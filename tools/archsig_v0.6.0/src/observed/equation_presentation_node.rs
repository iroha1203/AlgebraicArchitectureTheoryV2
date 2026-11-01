//! 既存の有限/多項式表示を結ぶ、全支持ContextとEquationPresentationのpayload。
use super::{
    construction_result as native,
    construction_result::{
        ArchitectureWitness, ConstructionData as D, ConstructionType as T, ConstructionValue,
        Witness,
    },
    result::*,
};
use crate::control::{Checkpoint, Control};
use crate::{canonical::Json, types::Type};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::EquationPresentation)?;
    Ok(())
}
fn refs(xs: &[NodeRef]) -> Json {
    Json::Arr(xs.iter().map(|r| r.wire()).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Coordinate {
    pub instance: NodeRef,
    pub component: Vec<usize>,
    pub lhs: NodeRef,
    pub rhs: NodeRef,
    pub nu: NodeRef,
    pub epsilon: Option<NodeRef>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Part {
    Context {
        base: NodeRef,
        carrier: Vec<Scalar>,
        dependencies: Vec<(NodeRef, String)>,
        laws: Vec<NodeRef>,
        quantifiers: Vec<Quantifier>,
    },
    Presentation {
        instances: Vec<NodeRef>,
        domain: NodeRef,
        ring: NodeRef,
        coordinates: Vec<Coordinate>,
        witnesses: Vec<NodeRef>,
        required: NodeRef,
        evaluation: Option<NodeRef>,
        context: NodeRef,
        quantifiers: Vec<Quantifier>,
        omissions: Vec<Reason>,
    },
}
impl Part {
    pub fn reasons(&self) -> Vec<Reason> {
        match self {
            Self::Presentation { omissions, .. } => omissions.clone(),
            Self::Context { .. } => vec![],
        }
    }
    pub fn ty(&self) -> NodeType {
        NodeType::Construction(match self {
            Self::Context { .. } => T::Context,
            Self::Presentation { .. } => T::EquationPresentation,
        })
    }
    pub fn construction(&self) -> &'static str {
        match self {
            Self::Context { .. } => "context",
            Self::Presentation { .. } => "equation_presentation",
        }
    }
    pub fn quantifiers(&self) -> &[Quantifier] {
        match self {
            Self::Context { quantifiers, .. } | Self::Presentation { quantifiers, .. } => {
                quantifiers
            }
        }
    }
    /// Context.baseはadapter Sourceの必須の第1引数と同じ参照である。
    pub fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Context {
                dependencies, laws, ..
            } => dependencies
                .iter()
                .map(|(r, _)| *r)
                .chain(laws.iter().copied())
                .collect(),
            Self::Presentation {
                instances,
                domain,
                ring,
                coordinates,
                witnesses,
                required,
                evaluation,
                context,
                ..
            } => {
                let mut xs = instances.clone();
                xs.extend([*domain, *ring]);
                for q in coordinates {
                    xs.extend([q.instance, q.lhs, q.rhs, q.nu]);
                    xs.extend(q.epsilon);
                }
                xs.extend(witnesses);
                xs.push(*required);
                xs.extend(evaluation);
                xs.push(*context);
                xs
            }
        }
    }
    pub fn wire(&self) -> Json {
        match self {
            Self::Context {
                base,
                carrier,
                dependencies,
                laws,
                ..
            } => Json::obj([
                ("base", base.wire()),
                ("locals", Json::Arr(vec![])),
                (
                    "carrier",
                    Json::Arr(
                        carrier
                            .iter()
                            .map(|v| Json::obj([("type", v.ty().wire()), ("value", v.wire())]))
                            .collect(),
                    ),
                ),
                (
                    "dependencies",
                    Json::Arr(
                        dependencies
                            .iter()
                            .map(|(subject, field)| {
                                Json::obj([
                                    ("subject", subject.wire()),
                                    ("field", Json::str(field)),
                                ])
                            })
                            .collect(),
                    ),
                ),
                ("readings", Json::Arr(vec![])),
                ("law_coordinates", refs(laws)),
            ]),
            Self::Presentation {
                instances,
                domain,
                ring,
                coordinates,
                witnesses,
                required,
                evaluation,
                context,
                ..
            } => {
                let mut fields = vec![
                    ("instances", refs(instances)),
                    ("domain", domain.wire()),
                    ("ring", ring.wire()),
                    (
                        "coordinates",
                        Json::Arr(
                            coordinates
                                .iter()
                                .map(|q| {
                                    let mut fs = vec![
                                        ("instance", q.instance.wire()),
                                        (
                                            "component",
                                            Json::Arr(
                                                q.component
                                                    .iter()
                                                    .map(|i| Json::Nat(*i as u64))
                                                    .collect(),
                                            ),
                                        ),
                                        ("lhs", q.lhs.wire()),
                                        ("rhs", q.rhs.wire()),
                                        ("nu", q.nu.wire()),
                                    ];
                                    if let Some(e) = q.epsilon {
                                        fs.push(("epsilon", e.wire()));
                                    }
                                    Json::Obj(
                                        fs.into_iter().map(|(k, v)| (k.to_owned(), v)).collect(),
                                    )
                                })
                                .collect(),
                        ),
                    ),
                    ("witness_ideals", refs(witnesses)),
                    ("required_ideal", required.wire()),
                    ("context", context.wire()),
                ];
                if let Some(e) = evaluation {
                    fields.push(("evaluation", e.wire()));
                }
                Json::Obj(fields.into_iter().map(|(k, v)| (k.to_owned(), v)).collect())
            }
        }
    }
}
/// 原始FactPointerの全欄を可逆に保持する。順序番号をAtomのidentityにしない。
pub(super) fn carrier(
    a: &ArchitectureWitness,
    c: &mut Control,
) -> Result<Vec<Scalar>, ValidationFailure> {
    let mut values = vec![];
    for f in a.construction().universe() {
        tick(c)?;
        let optional = |s: Option<&str>| Scalar::Option {
            element: Type::Text,
            value: s.map(|s| Box::new(Scalar::Text(s.to_owned()))),
        };
        values.push(Scalar::Tuple(vec![
            Scalar::Text(f.snapshot.clone()),
            Scalar::Text(f.subject.clone()),
            optional(f.field.as_deref()),
            optional(f.atom.as_deref()),
        ]));
    }
    values.sort_by_key(|v| v.wire().canonical());
    tick(c)?;
    Ok(values)
}
pub(super) fn global_metadata(
    a: &Arc<ArchitectureWitness>,
    support: &mut Vec<Fact>,
    scope: &mut Scope,
) -> Result<(), ValidationFailure> {
    let (facts, s) = native::metadata(&ConstructionValue {
        witness: Witness::Architecture(a.clone()),
        data: D::AtomUniverse(a.construction().universe().to_vec()),
    })?;
    support.extend(facts);
    support.sort_by_key(|f| f.wire().canonical());
    support.dedup();
    scope.merge(&s);
    Ok(())
}

pub(super) struct Dependencies {
    pub slots: Vec<(NodeRef, String)>,
}
impl Dependencies {
    /// 値として構成できる表示と、その表示で省略した実対象の評価を区別する。
    /// 理由は元LawのExpressionに結び、転記中の追加nodeで計画をずらさない。
    pub fn missing_reasons(
        &self,
        inputs: &crate::input::CheckedInputs,
        positions: &[Fact],
        expressions: &[NodeRef],
        request: &super::request::Request,
        c: &mut Control,
    ) -> Result<Vec<Reason>, ValidationFailure> {
        let env = super::environment::Environment::new(inputs, c)?;
        let mut missing = vec![];
        for f in positions {
            tick(c)?;
            let field = f.field.as_deref().ok_or("評価省略の元fieldがない")?;
            if matches!(
                env.field(&f.snapshot, &f.subject, field)?.slot,
                crate::archmap::Slot::Missing
            ) {
                missing.push(Fact {
                    atom: None,
                    ..f.clone()
                });
            }
        }
        if missing.is_empty() {
            return Ok(vec![]);
        }
        missing.sort_by_key(|f| f.wire().canonical());
        missing.dedup();
        let mut dependencies = expressions.to_vec();
        dependencies.sort_by_key(|r| r.0);
        dependencies.dedup();
        if dependencies.is_empty() {
            return Err("評価省略の元Expressionがない".into());
        }
        Ok(vec![Reason {
            kind: ReasonKind::Missing,
            request: request.id.clone(),
            dependencies,
            missing,
            location: None,
        }])
    }
}
pub(super) fn dependencies(
    inputs: &crate::input::CheckedInputs,
    positions: &[Fact],
    c: &mut Control,
    mut retain: impl FnMut(Scalar) -> Result<NodeRef, ValidationFailure>,
) -> Result<Dependencies, ValidationFailure> {
    let mut subjects = std::collections::BTreeMap::new();
    let mut slots = std::collections::BTreeMap::new();
    for f in positions {
        tick(c)?;
        let field = f
            .field
            .as_ref()
            .ok_or("global Contextの依存位置がfieldでない")?;
        let key = (f.snapshot.clone(), f.subject.clone());
        let reference = if let Some(r) = subjects.get(&key) {
            *r
        } else {
            let subject = inputs
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == f.snapshot)
                .and_then(|s| s.subjects.iter().find(|s| s.id == f.subject))
                .ok_or("global Contextの原始subjectがない")?;
            let r = retain(Scalar::Subject {
                snapshot: f.snapshot.clone(),
                subject: f.subject.clone(),
                entity: subject.ty.to_string(),
            })?;
            subjects.insert(key.clone(), r);
            r
        };
        slots.insert((key.0, key.1, field.clone()), (reference, field.clone()));
    }
    tick(c)?;
    Ok(Dependencies {
        slots: slots.into_values().map(|(node,name)| (node,name.to_string())).collect(),
    })
}
