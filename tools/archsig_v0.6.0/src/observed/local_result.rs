//! 固定観測状態の局所系。自由位置を補わず、恒等coverの有限matchingを計算する。
use super::{
    PreparedObserved,
    build_result::{Builder, Part},
    change_result,
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    control::Control,
    environment::{AnswerBinding, Environment, change_search},
    projection::{ProjectionStep, ProjectionType},
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::{
    canonical::Json,
    issue::Location,
    law::{
        ast::{BinOp, ExprKind},
        model::Signature,
    },
    types::Type,
};
use std::{collections::BTreeMap, sync::Arc};
#[derive(Debug)]
pub(super) struct Source {
    base: usize,
    parts: Vec<Part>,
    answer: Answer,
    request: Request,
    witness: Arc<ArchitectureWitness>,
    system: Option<System>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct System {
    expression: NodeRef,
    semantic: NodeRef,
    equation: NodeRef,
    domain: NodeRef,
    inhabited: bool,
}
#[derive(Clone, Debug)]
pub(crate) struct Data {
    source: Arc<Source>,
    index: usize,
}
impl PartialEq for Data {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.source, &other.source) && self.index == other.index
    }
}
impl Eq for Data {}
impl Data {
    fn part(&self) -> &Part {
        &self.source.parts[self.index]
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty.clone()
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        self.part().scalar.as_ref()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        self.part().arguments.clone()
    }
    pub(super) fn conditions(&self) -> Vec<NodeRef> {
        vec![]
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction
    }
    pub(super) fn wire(&self) -> Json {
        self.part().wire.clone()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.part().support.clone(), self.part().scope.clone())
    }
    pub(super) fn projection_type(&self) -> Option<ProjectionType> {
        match self.ty() {
            NodeType::Construction(T::LocalSystem) => Some(ProjectionType::LocalSystem),
            NodeType::Construction(T::Diagnostic) => Some(ProjectionType::Diagnostic),
            NodeType::Construction(T::Cover) => Some(ProjectionType::Cover),
            NodeType::Construction(T::Topology) => Some(ProjectionType::Topology),
            NodeType::Construction(T::StateMap) => Some(ProjectionType::StateMap),
            NodeType::Domain => Some(ProjectionType::Domain),
            NodeType::Construction(T::SolutionSet) => Some(ProjectionType::FixedSolutionSet),
            NodeType::Construction(T::EquationSolutionSet) => {
                Some(ProjectionType::EquationSolutionSet)
            }
            NodeType::Proposition => Some(ProjectionType::Proposition),
            _ => None,
        }
    }
    pub(super) fn project(&self, path: &[ProjectionStep]) -> Option<(NodeRef, usize)> {
        let ProjectionStep::Field(field) = path.first()? else {
            return None;
        };
        let allowed = match self.ty() {
            NodeType::Construction(T::LocalSystem) => {
                matches!(field.as_str(), "base" | "cover" | "topology")
            }
            NodeType::Construction(T::Diagnostic) => matches!(
                field.as_str(),
                "system" | "matching" | "global" | "restriction"
            ),
            NodeType::Construction(T::StateMap) => matches!(field.as_str(), "source" | "target"),
            _ => false,
        };
        if !allowed {
            return None;
        }
        let Json::Obj(wire) = &self.part().wire else {
            return None;
        };
        self.part()
            .arguments
            .iter()
            .find(|r| Some(&r.wire()) == wire.get(field))
            .map(|r| (*r, 1))
    }
}
fn refs(rs: &[NodeRef]) -> Json {
    Json::Arr(rs.iter().map(|r| r.wire()).collect())
}
fn unsupported(feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law { span: (0, 0) },
        feature: feature.into(),
    }
}
fn domain(b: &mut Builder<'_>, ty: &Type, items: &[NodeRef]) -> Result<NodeRef, ValidationFailure> {
    b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("finite")),
            ("type", ty.wire()),
            ("elements", refs(items)),
        ]),
        items.to_vec(),
        None,
        None,
    )
}
fn state_map(
    b: &mut Builder<'_>,
    from: NodeRef,
    to: NodeRef,
    pairs: &[(NodeRef, NodeRef)],
) -> Result<NodeRef, ValidationFailure> {
    b.push(
        NodeType::Construction(T::StateMap),
        "state_map",
        Json::obj([
            ("source", from.wire()),
            ("target", to.wire()),
            ("kind", Json::str("finite")),
            (
                "pairs",
                Json::Arr(
                    pairs
                        .iter()
                        .map(|(a, b)| Json::Arr(vec![a.wire(), b.wire()]))
                        .collect(),
                ),
            ),
        ]),
        std::iter::once(from)
            .chain([to])
            .chain(pairs.iter().flat_map(|(a, b)| [*a, *b]))
            .collect(),
        None,
        None,
    )
}
fn reference(
    env: &Environment<'_>,
    g: &Graph,
    selector: &Selector,
) -> Result<NodeRef, ValidationFailure> {
    match env.answer_binding(g, selector, (0, 0))? {
        AnswerBinding::Reference(r) => Ok(r),
        _ => Err(unsupported("局所系の対象Handleの射影は未実装")),
    }
}
fn compute(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    base: usize,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    c.checkpoint(super::control::Checkpoint::Localize)?;
    env.validation_graph_session(g, || {
        let target = reference(env, g, &request.head)?;
        let Some(Payload::Construction(original)) = &g.get(target)?.payload else {
            return Err("局所系の元構成がない".into());
        };
        let Witness::Architecture(witness) = &original.witness else {
            return Err("局所系の元Architectureがない".into());
        };
        if request.kind == QuestionKind::Diagnose {
            return diagnose(g, request, target, original, base, witness.clone());
        }
        if request.arguments.iter().any(|a| a.name == "using") {
            return Err(unsupported("自由位置を持つ局所系の公開構成は未実装"));
        }
        let reading = witness.construction().reading();
        if env
            .inputs
            .law()
            .declarations
            .values()
            .any(|d| d.reading == reading && matches!(d.signature, Signature::Local { .. }))
        {
            return Err(unsupported("明示local宣言の局所系は未実装"));
        }
        let selected = request
            .arguments
            .iter()
            .find(|a| a.name == "law")
            .map(|a| match &a.value {
                Selector::Declaration { name } => Ok(name.as_str()),
                _ => Err(ValidationFailure::from("局所Law名がない")),
            })
            .transpose()?;
        let names = if let Some(name) = selected {
            vec![name.to_owned()]
        } else {
            env.inputs
                .law()
                .declarations
                .values()
                .filter(|d| {
                    d.reading == reading
                        && matches!(
                            d.signature,
                            Signature::Law {
                                role: crate::law::ast::Role::Required,
                                ..
                            }
                        )
                })
                .map(|d| d.name.clone())
                .collect()
        };
        if names.len() != 1 {
            return Err(unsupported("複数または空のLaw族の局所系は未実装"));
        }
        let declaration = &env.inputs.law().declarations[&names[0]];
        if declaration.reading != reading {
            return Err(unsupported("対象Architectureと局所Lawのreadingが異なる"));
        }
        let Signature::Law {
            role,
            params,
            guard: None,
            body,
        } = &declaration.signature
        else {
            return Err(unsupported("条件付きLawの局所系は未実装"));
        };
        let ExprKind::Binary {
            op: BinOp::Eq,
            lhs,
            rhs,
        } = env.inputs.law().exprs[*body].kind
        else {
            return Err(unsupported("等式以外の局所Lawは未実装"));
        };
        let assignments = match &original.data {
            D::Change(d) => d.overrides(g)?,
            D::Quotient(d) => d.overrides(g)?,
            _ => vec![],
        }
        .into_iter()
        .map(|(f, _, v)| (f, v))
        .collect::<Vec<_>>();
        let mut fixed = Environment::try_primitive_valuation(env.inputs, &assignments, c)?
            .ok_or("固定Architectureの値が不適合")?;
        fixed.select_local_object(witness, c)?;
        let mut bindings = vec![];
        let mut universal = vec![];
        let mut missing = vec![];
        for p in params {
            let value = if let Some(a) = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
            {
                change_search::selector(env, g, &a.value)?
            } else {
                let Some(mut values) = change_search::domain(&fixed, &p.ty, p.span, &mut missing)?
                else {
                    return Err(unsupported("局所Lawのparameter域が未確定"));
                };
                if values.len() != 1 {
                    return Err(unsupported("複数instanceの局所系は未実装"));
                }
                universal.push(p);
                values.remove(0)
            };
            bindings.push((p.name.clone(), value));
        }
        let mut carrier = bindings
            .iter()
            .filter(|(_, v)| matches!(v, Scalar::Subject { .. }))
            .map(|(_, v)| Json::obj([("type", v.ty().wire()), ("value", v.wire())]))
            .collect::<Vec<_>>();
        let (row, read_missing, evaluated) = fixed.local_point(declaration, &bindings)?;
        for fact in &row.support {
            let subject = env.subject(&fact.snapshot, &fact.subject)?;
            let v = Scalar::Subject {
                snapshot: fact.snapshot.clone(),
                subject: fact.subject.clone(),
                entity: subject.ty.clone(),
            };
            carrier.push(Json::obj([("type", v.ty().wire()), ("value", v.wire())]));
        }
        for read in &evaluated {
            if let Some(value @ Scalar::Subject { .. }) = &read.value {
                carrier.push(Json::obj([
                    ("type", value.ty().wire()),
                    ("value", value.wire()),
                ]));
            }
        }
        carrier.sort_by_key(Json::canonical);
        carrier.dedup();
        let carrier_size = carrier.len();
        missing.extend(read_missing);
        let mut b = Builder {
            g,
            base,
            parts: vec![],
        };
        let bindings = bindings
            .iter()
            .map(|(n, v)| Ok((n.clone(), change_result::value(&mut b, v)?)))
            .collect::<Result<Vec<_>, ValidationFailure>>()?;
        let mut quantifiers = vec![];
        for p in universal {
            let value = bindings
                .iter()
                .find(|(n, _)| n == &p.name)
                .ok_or("局所量化の束縛がない")?
                .1;
            let domain = domain(&mut b, &p.ty.erase(), &[value])?;
            quantifiers.push(Quantifier {
                kind: crate::law::ast::QuantKind::Forall,
                name: p.name.clone(),
                ty: p.ty.clone(),
                domain: Some(domain),
                occurrence: p.span,
                context: Some(env.current_context(g)),
            });
        }
        let expression = change_result::source_expression(&mut b, env, *body, &bindings, &[])?;
        b.parts[expression.0 - base]
            .arguments
            .extend(quantifiers.iter().filter_map(|q| q.domain));
        b.parts[expression.0 - base]
            .scope
            .quantifiers
            .extend(quantifiers);
        b.parts[expression.0 - base].arguments.push(target);
        b.parts[expression.0 - base]
            .scope
            .merge(&g.get(target)?.scope);
        b.parts[expression.0 - base].scope.merge(&row.scope);
        let known = row.application == Some(true)
            && !row.condition_failed
            && !row.condition_pending
            && row.predicate.is_some();
        if !known {
            missing.extend(row.application_missing);
            missing.extend(
                row.support
                    .iter()
                    .filter(|f| f.field.is_some() && f.atom.is_none())
                    .cloned(),
            );
            missing.sort();
            missing.dedup();
            if missing.is_empty() {
                return Err(unsupported("局所Lawの適用条件または値が未確定"));
            }
            let reason = Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: vec![expression],
                missing,
                location: Some(Location::Law {
                    span: declaration.span,
                }),
            };
            b.parts[expression.0 - base].reasons.push(reason.clone());
            let scope = b.parts[expression.0 - base].scope.clone();
            return Ok(Source {
                base,
                parts: b.parts,
                answer: Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons: vec![reason],
                    scope,
                },
                request: request.clone(),
                witness: witness.clone(),
                system: None,
            });
        }
        let inhabited = row.predicate == Some(true);
        let law = b.push(
            NodeType::LawInstance,
            "law_instance",
            Json::obj([
                ("name", Json::str(&declaration.name)),
                (
                    "role",
                    Json::str(if *role == crate::law::ast::Role::Required {
                        "required"
                    } else {
                        "optional"
                    }),
                ),
                (
                    "occurrence",
                    crate::result::location_wire(&Location::Law {
                        span: declaration.span,
                    }),
                ),
                (
                    "bindings",
                    Json::Arr(
                        bindings
                            .iter()
                            .map(|(n, r)| Json::obj([("name", Json::str(n)), ("value", r.wire())]))
                            .collect(),
                    ),
                ),
                ("body", expression.wire()),
            ]),
            std::iter::once(expression)
                .chain(bindings.iter().map(|(_, r)| *r))
                .collect(),
            None,
            None,
        )?;
        let mut positions = row
            .support
            .iter()
            .filter(|f| f.field.is_some())
            .map(|f| Fact {
                atom: None,
                ..f.clone()
            })
            .collect::<Vec<_>>();
        positions.sort();
        positions.dedup();
        let slots = Json::Arr(positions.iter().map(Fact::wire).collect());
        let unit = change_result::value(&mut b, &Scalar::Unit)?;
        let point = domain(&mut b, &Type::Unit, &[unit])?;
        let elements = if inhabited { vec![unit] } else { vec![] };
        let states = domain(&mut b, &Type::Unit, &elements)?;
        let action = state_map(&mut b, point, point, &[(unit, unit)])?;
        let space = b.push(
            NodeType::Construction(T::StateSpace),
            "state_space",
            Json::obj([
                ("base", target.wire()),
                ("slots", Json::Arr(vec![])),
                ("state_type", Type::Unit.wire()),
            ]),
            vec![target],
            None,
            None,
        )?;
        let candidates = b.push(
            NodeType::Construction(T::CandidateSpace),
            "candidate_space",
            Json::obj([
                ("kind", Json::str("identity")),
                ("base", target.wire()),
                ("bindings", Json::Arr(vec![])),
                ("parameters", point.wire()),
                ("states", space.wire()),
                ("action", action.wire()),
                ("instances", Json::Arr(vec![])),
                ("guards", Json::Arr(vec![])),
                ("requirements", refs(&[law])),
            ]),
            vec![target, point, space, action, law],
            None,
            None,
        )?;
        let representation =
            Json::obj([("kind", Json::str("finite")), ("values", refs(&elements))]);
        let semantic = b.push(
            NodeType::Construction(T::SolutionSet),
            "solution_set",
            Json::obj([
                ("domain", candidates.wire()),
                ("requirements", refs(&[law])),
                ("representation", representation.clone()),
            ]),
            vec![candidates, law, states],
            None,
            None,
        )?;
        let equations = b.push(
            NodeType::Construction(T::EquationSpace),
            "equation_space",
            Json::obj([
                ("base", target.wire()),
                ("variables", Json::Arr(vec![])),
                ("fixed", slots.clone()),
                ("parameters", point.wire()),
                ("requirements", refs(&[law])),
            ]),
            vec![target, point, law],
            None,
            None,
        )?;
        let equation = b.push(
            NodeType::Construction(T::EquationSolutionSet),
            "equation_solution_set",
            Json::obj([
                ("domain", equations.wire()),
                ("representation", representation),
            ]),
            vec![equations, states],
            None,
            None,
        )?;
        let mut readings = vec![];
        let mut reading_refs = vec![];
        let mut retained = std::collections::BTreeSet::new();
        for read in evaluated.into_iter().filter(|n| {
            n.expression == lhs
                || n.expression == rhs
                || match &env.inputs.law().exprs[n.expression].kind {
                    ExprKind::Field { .. } => true,
                    ExprKind::Dotted(parts) => {
                        parts.len() > 1 && n.bindings.iter().any(|(name, _)| *name == parts[0].name)
                    }
                    _ => false,
                }
        }) {
            let Some(value) = read.value else {
                return Err("確定した局所読取りの値がない".into());
            };
            let key = (
                read.expression,
                read.bindings
                    .iter()
                    .map(|(n, v)| (n.clone(), v.wire().canonical()))
                    .collect::<Vec<_>>(),
            );
            if !retained.insert(key) {
                continue;
            }
            let bs = read
                .bindings
                .iter()
                .map(|(n, v)| Ok((n.clone(), change_result::value(&mut b, v)?)))
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            let expr = change_result::source_expression(&mut b, env, read.expression, &bs, &[])?;
            let actual = change_result::value(&mut b, &value)?;
            let image = domain(&mut b, &value.ty(), &[actual])?;
            readings.push(Json::obj([
                ("expression", expr.wire()),
                ("type", value.ty().wire()),
                ("domain", image.wire()),
            ]));
            reading_refs.extend([expr, image]);
        }
        let context = b.push(
            NodeType::Construction(T::Context),
            "context",
            Json::obj([
                ("base", target.wire()),
                ("locals", Json::Arr(vec![])),
                ("carrier", Json::Arr(carrier)),
                ("dependencies", slots),
                ("readings", Json::Arr(readings)),
                ("law_coordinates", refs(&[law])),
            ]),
            std::iter::once(target)
                .chain([law])
                .chain(reading_refs)
                .collect(),
            None,
            None,
        )?;
        let pairs = elements.iter().map(|r| (*r, *r)).collect::<Vec<_>>();
        let identity = state_map(&mut b, states, states, &pairs)?;
        let arrow = b.push(
            NodeType::Construction(T::ContextMap),
            "context_map",
            Json::obj([
                ("source", context.wire()),
                ("target", context.wire()),
                (
                    "images",
                    Json::Arr((0..carrier_size).map(|i| Json::Nat(i as u64)).collect()),
                ),
                ("restrictions", refs(&[identity])),
            ]),
            vec![context, identity],
            None,
            None,
        )?;
        let overlap = b.push(
            NodeType::Construction(T::Overlap),
            "overlap",
            Json::obj([
                ("left", context.wire()),
                ("right", context.wire()),
                ("context", context.wire()),
                ("left_projection", arrow.wire()),
                ("right_projection", arrow.wire()),
            ]),
            vec![context, arrow],
            None,
            None,
        )?;
        let adequacy = b.proposition(
            "cover_adequate",
            vec![context],
            vec![],
            Decision::Established,
        )?;
        let cover = b.push(
            NodeType::Construction(T::Cover),
            "cover",
            Json::obj([
                ("base", context.wire()),
                ("patches", refs(&[context])),
                ("overlaps", refs(&[overlap])),
                ("adequacy", adequacy.wire()),
            ]),
            vec![context, overlap, adequacy],
            None,
            None,
        )?;
        let topology = b.push(
            NodeType::Construction(T::Topology),
            "topology",
            Json::obj([
                ("contexts", refs(&[context])),
                ("maps", refs(&[arrow])),
                ("generators", refs(&[cover])),
                (
                    "covering_sieves",
                    Json::Arr(vec![Json::obj([
                        ("base", context.wire()),
                        ("arrows", refs(&[arrow])),
                    ])]),
                ),
            ]),
            vec![context, arrow, cover],
            None,
            None,
        )?;
        let mut checks = vec![];
        let mut restrictions = vec![];
        for side in ["equation", "semantic"] {
            restrictions.push(Json::obj([
                ("side", Json::str(side)),
                ("arrow", arrow.wire()),
                ("map", identity.wire()),
            ]));
            for (scope, object) in [("cover", cover), ("topology", topology)] {
                let proposition = b.proposition(
                    "sheaf_condition",
                    vec![object, identity],
                    vec![],
                    Decision::Established,
                )?;
                checks.push((
                    proposition,
                    Json::obj([
                        ("scope", Json::str(scope)),
                        ("side", Json::str(side)),
                        ("proposition", proposition.wire()),
                    ]),
                ));
            }
        }
        let mut fields = BTreeMap::from([
            ("base".into(), target.wire()),
            ("laws".into(), refs(&[law])),
            ("contexts".into(), refs(&[context])),
            ("maps".into(), refs(&[arrow])),
            ("cover".into(), cover.wire()),
            ("topology".into(), topology.wire()),
            (
                "semantic_states".into(),
                Json::Arr(vec![Json::obj([
                    ("context", context.wire()),
                    ("parameters", semantic.wire()),
                    ("state_image", states.wire()),
                    ("action", identity.wire()),
                ])]),
            ),
            (
                "equation_states".into(),
                Json::Arr(vec![Json::obj([
                    ("context", context.wire()),
                    ("space", equations.wire()),
                    ("solutions", equation.wire()),
                ])]),
            ),
            ("restrictions".into(), Json::Arr(restrictions)),
            (
                "state_comparisons".into(),
                Json::Arr(vec![Json::obj([
                    ("context", context.wire()),
                    ("map", identity.wire()),
                    ("conditions", Json::Arr(vec![])),
                ])]),
            ),
            (
                "sheaf_checks".into(),
                Json::Arr(checks.iter().map(|(_, v)| v.clone()).collect()),
            ),
        ]);
        for name in [
            "coefficients",
            "coefficient_restrictions",
            "actions",
            "presentations",
            "polynomial_inclusions",
            "residual_restrictions",
            "conditions",
        ] {
            fields.insert(name.into(), Json::Arr(vec![]));
        }
        let system = b.push(
            NodeType::Construction(T::LocalSystem),
            "local_system",
            Json::Obj(fields),
            [
                target, law, context, arrow, cover, topology, semantic, states, equations,
                equation, identity,
            ]
            .into_iter()
            .chain(checks.iter().map(|(r, _)| *r))
            .collect(),
            None,
            None,
        )?;
        let label = change_result::value(&mut b, &Scalar::Text("local_system".into()))?;
        let proposition = b.proposition(
            "constructible",
            std::iter::once(label)
                .chain(b.parts[system.0 - base].arguments.iter().copied())
                .collect(),
            vec![adequacy],
            Decision::Established,
        )?;
        let answer = Answer {
            id: request.id.clone(),
            status: Decision::Established,
            outputs: BTreeMap::from([
                ("system".into(), system),
                ("proposition".into(), proposition),
            ]),
            claim: Some(proposition),
            evidence: vec![],
            reasons: vec![],
            scope: b.parts[system.0 - base].scope.clone(),
        };
        Ok(Source {
            base,
            parts: b.parts,
            answer,
            request: request.clone(),
            witness: witness.clone(),
            system: Some(System {
                expression,
                semantic,
                equation,
                domain: states,
                inhabited,
            }),
        })
    })
}
fn diagnose(
    g: &Graph,
    request: &Request,
    target: NodeRef,
    original: &ConstructionValue,
    base: usize,
    witness: Arc<ArchitectureWitness>,
) -> Result<Source, ValidationFailure> {
    let D::Local(data) = &original.data else {
        return Err("診断対象がLocalSystemでない".into());
    };
    let system = data.source.system.as_ref().ok_or("局所系の状態がない")?;
    let degree = request
        .arguments
        .iter()
        .find_map(|a| {
            if a.name == "degree" {
                if let Selector::Degree { value } = a.value {
                    Some(value)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .ok_or("診断次数がない")?;
    if degree > 1 {
        let original = &data.source.parts[system.expression.0 - data.source.base];
        let mut b = Builder {
            g,
            base,
            parts: vec![],
        };
        let expression = b.push(
            original.ty.clone(),
            original.construction,
            original.wire.clone(),
            original.arguments.iter().copied().chain([target]).collect(),
            None,
            None,
        )?;
        let reason = Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: QuestionKind::Diagnose,
                operand_types: vec![Type::Bool],
                method: "finite_matching_degree".into(),
            },
            request: request.id.clone(),
            dependencies: vec![expression],
            missing: vec![],
            location: None,
        };
        b.parts[0].reasons.push(reason.clone());
        let answer = Answer {
            id: request.id.clone(),
            status: Decision::Undetermined,
            outputs: BTreeMap::new(),
            claim: None,
            evidence: vec![],
            reasons: vec![reason],
            scope: b.parts[0].scope.clone(),
        };
        return Ok(Source {
            base,
            parts: b.parts,
            answer,
            request: request.clone(),
            witness,
            system: None,
        });
    }
    let side = request
        .arguments
        .iter()
        .find_map(|a| {
            if a.name == "side" {
                if let Selector::Enum { value } = &a.value {
                    Some(value.as_str())
                } else {
                    None
                }
            } else {
                None
            }
        })
        .ok_or("診断sideがない")?;
    let global = if side == "equation" {
        system.equation
    } else {
        system.semantic
    };
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let unit = change_result::value(&mut b, &Scalar::Unit)?;
    let tuple = change_result::value(&mut b, &Scalar::Tuple(vec![Scalar::Unit]))?;
    let matching = domain(
        &mut b,
        &Type::Tuple(vec![Type::Unit]),
        &if system.inhabited {
            vec![tuple]
        } else {
            vec![]
        },
    )?;
    let pairs = if system.inhabited {
        vec![(unit, tuple)]
    } else {
        vec![]
    };
    let restriction = state_map(&mut b, system.domain, matching, &pairs)?;
    let fibers = if system.inhabited {
        vec![Json::obj([
            ("matching", tuple.wire()),
            ("preimage", global.wire()),
        ])]
    } else {
        vec![]
    };
    let diagnostic = b.push(
        NodeType::Construction(T::Diagnostic),
        "diagnostic",
        Json::obj([
            ("kind", Json::str("finite_matching")),
            ("side", Json::str(side)),
            ("system", target.wire()),
            ("degree", Json::Nat(degree)),
            ("matching", matching.wire()),
            ("global", global.wire()),
            ("restriction", restriction.wire()),
            ("fibers", Json::Arr(fibers)),
            ("conditions", Json::Arr(vec![])),
        ]),
        vec![target, matching, global, restriction],
        None,
        None,
    )?;
    let status = if degree == 0 || system.inhabited {
        Decision::Established
    } else {
        Decision::Refuted
    };
    let proposition = b.proposition(
        if degree == 0 {
            "sheaf_condition"
        } else {
            "inhabited"
        },
        vec![if degree == 0 { diagnostic } else { global }],
        vec![diagnostic],
        status,
    )?;
    let answer = Answer {
        id: request.id.clone(),
        status,
        outputs: BTreeMap::from([
            ("diagnostic".into(), diagnostic),
            ("proposition".into(), proposition),
        ]),
        claim: Some(proposition),
        evidence: vec![],
        reasons: vec![],
        scope: b.parts[diagnostic.0 - base].scope.clone(),
    };
    Ok(Source {
        base,
        parts: b.parts,
        answer,
        request: request.clone(),
        witness,
        system: None,
    })
}

pub(super) fn evaluate(
    _prepared: &PreparedObserved,
    env: &Environment<'_>,
    g: &mut Graph,
    request: &Request,
    c: &mut Control,
) -> Result<Answer, ValidationFailure> {
    env.commit_projection_conditions(g, request)?;
    if let Some(answer) = super::public_map::unavailable(env, g, request)? {
        return Ok(answer);
    }
    for argument in &request.arguments {
        if argument.name.starts_with("bind.") && matches!(argument.value, Selector::Answer { .. }) {
            if let AnswerBinding::Projection(node) =
                env.answer_binding(g, &argument.value, (0, 0))?
            {
                env.validate(g, &node)?;
                g.push(node)?;
            }
        }
    }
    let source = Arc::new(compute(env, g, request, g.nodes.len(), c)?);
    for (index, part) in source.parts.iter().enumerate() {
        native::retain(
            g,
            ConstructionValue {
                witness: Witness::Architecture(source.witness.clone()),
                data: D::Local(Data {
                    source: source.clone(),
                    index,
                }),
            },
            part.reasons.clone(),
            part.evidence.clone(),
            part.judgment.clone(),
        )?;
    }
    Ok(source.answer.clone())
}
pub(super) fn validate_node(
    g: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let Witness::Architecture(w) = &v.witness else {
        return Err("局所系の元Architectureがない".into());
    };
    let p = d.part();
    if !Arc::ptr_eq(w, &d.source.witness)
        || n.ty != p.ty
        || n.rule != Rule::Construction(p.construction)
        || n.arguments != p.arguments
        || n.support != p.support
        || n.scope != p.scope
        || n.reasons != p.reasons
        || n.evidence != p.evidence
        || n.judgment != p.judgment
    {
        return Err("局所系の元構成が違う".into());
    }
    for r in &p.arguments {
        g.get(*r)?;
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_local(
        &self,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        let D::Local(d) = &v.data else {
            return Ok(());
        };
        if d.index >= d.source.parts.len()
            || d.source.base + d.index != at
            || d.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("局所系の位置・既出参照が違う".into());
        }
        if self.local_source_checked(&d.source) {
            return Ok(());
        }
        let rebuilt = self.with_request_context(g, &d.source.request, || {
            compute(
                self,
                g,
                &d.source.request,
                d.source.base,
                &mut self.control.clone(),
            )
        })?;
        if rebuilt.parts != d.source.parts
            || rebuilt.answer != d.source.answer
            || rebuilt.system != d.source.system
        {
            return Err("局所系の再構成が違う".into());
        }
        self.remember_local_source(d.source.clone());
        Ok(())
    }
}
pub(super) fn validate_answer(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    answer: &Answer,
) -> Result<(), ValidationFailure> {
    if let Some(expected) = super::public_map::unavailable(env, g, request)? {
        return if *answer == expected {
            Ok(())
        } else {
            Err("局所系の依存停止が違う".into())
        };
    }
    let r = answer
        .outputs
        .get("system")
        .or_else(|| answer.outputs.get("diagnostic"))
        .or_else(|| {
            answer
                .reasons
                .iter()
                .find(|r| {
                    matches!(
                        r.kind,
                        ReasonKind::Missing | ReasonKind::UnsupportedAlgorithm { .. }
                    )
                })
                .and_then(|r| r.dependencies.first())
        })
        .ok_or("局所系の出力・不足の元式がない")?;
    let Some(Payload::Construction(v)) = &g.get(*r)?.payload else {
        return Err("局所系がnativeでない".into());
    };
    let D::Local(d) = &v.data else {
        return Err("局所系が別構成".into());
    };
    if &d.source.request != request || &d.source.answer != answer {
        return Err("局所系の元Request・回答が違う".into());
    }
    env.recheck_local(g, v, r.0)
}

pub(super) fn validate_origin(
    env: &Environment<'_>,
    request: &Request,
    v: &ConstructionValue,
) -> Result<(), ValidationFailure> {
    let D::Local(d) = &v.data else {
        return Err("局所系の構成が別種".into());
    };
    let Witness::Architecture(w) = &v.witness else {
        return Err("局所系の元Architectureがない".into());
    };
    if &d.source.request != request
        || !Arc::ptr_eq(w, &d.source.witness)
        || v.witness.inputs().sources() != env.inputs.sources()
    {
        return Err("局所系が現在の入力・Requestに属さない".into());
    }
    Ok(())
}
