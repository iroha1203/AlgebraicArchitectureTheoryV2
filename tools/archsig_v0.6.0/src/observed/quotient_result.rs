//! 候補集合そのものの有限view商を公開する。
use super::{
    PreparedObserved,
    build_result::{Builder, Part},
    change_result,
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    control::Control,
    environment::{AnswerBinding, Environment, quotient_evaluation},
    projection::{ProjectionStep, ProjectionType},
    request::Request,
    result::*,
};
use crate::{canonical::Json, issue::Location, law::model::Signature, types::Type};
use std::{collections::BTreeMap, sync::Arc};
#[derive(Debug)]
pub(super) struct Source {
    base: usize,
    parts: Vec<Part>,
    answer: Answer,
    request: Request,
    witness: Arc<ArchitectureWitness>,
    domain_type: ProjectionType,
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
            NodeType::Construction(T::Quotient) => Some(ProjectionType::Quotient(Box::new(
                self.source.domain_type.clone(),
            ))),
            NodeType::Construction(T::StateMap) => Some(ProjectionType::StateMap),
            NodeType::Domain => Some(ProjectionType::Domain),
            NodeType::Value(ty) => Some(ProjectionType::Law(ty)),
            _ => None,
        }
    }
    pub(super) fn project(&self, path: &[ProjectionStep]) -> Option<(NodeRef, usize)> {
        let ProjectionStep::Field(field) = path.first()? else {
            return None;
        };
        let allowed = match self.ty() {
            NodeType::Construction(T::Quotient) => matches!(
                field.as_str(),
                "domain" | "classes" | "projection" | "descent"
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
        let value = wire.get(field)?;
        self.part()
            .arguments
            .iter()
            .find(|r| r.wire() == *value)
            .map(|r| (*r, 1))
    }
}
fn refs(items: &[NodeRef]) -> Json {
    Json::Arr(items.iter().map(|r| r.wire()).collect())
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
fn compute(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    base: usize,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    env.validation_graph_session(g, || {
        let on = &request
            .arguments
            .iter()
            .find(|a| a.name == "on")
            .ok_or("商のonがない")?
            .value;
        let AnswerBinding::Reference(reference) = env.answer_binding(g, on, (0, 0))? else {
            return Err("商のonが既出参照でない".into());
        };
        let input = change_result::candidate_input(env, g, reference, c)?;
        let table = quotient_evaluation::compute(env, g, &input, request, c)?;
        let declaration =
            &env.inputs.law().declarations[request.declaration().ok_or("商のviewがない")?];
        let Signature::View { body, .. } = &declaration.signature else {
            return Err("商のviewが違う".into());
        };
        let mut b = Builder {
            g,
            base,
            parts: vec![],
        };
        let bindings = table
            .bindings
            .iter()
            .map(|(name, v)| Ok((name.clone(), change_result::value(&mut b, v)?)))
            .collect::<Result<Vec<_>, ValidationFailure>>()?;
        let expression = change_result::source_expression(&mut b, env, *body, &bindings, &[])?;
        b.parts[expression.0 - base]
            .scope
            .readings
            .insert(declaration.reading.clone());
        if !table.missing.is_empty() {
            let reason = Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: vec![expression],
                missing: table.missing,
                location: Some(Location::Law { span: declaration.span }),
            };
            b.parts[expression.0 - base].reasons.push(reason.clone());
            let scope = b.parts[expression.0 - base].scope.clone();
            return Ok(Source {
                base,
                parts: b.parts,
                answer: Answer {
                    id: request.id.clone(), status: Decision::Undetermined,
                    outputs: BTreeMap::new(), claim: None, evidence: vec![],
                    reasons: vec![reason], scope,
                },
                request: request.clone(), witness: input.witness,
                domain_type: input.domain_type,
            });
        }
        let mut fibers = BTreeMap::<String, Vec<Scalar>>::new();
        for row in table.rows {
            g.tick()?;
            fibers
                .entry(row.image.wire().canonical())
                .or_default()
                .push(row.parameters);
        }
        let mut classes = vec![];
        let mut fibers_wire = vec![];
        let mut projection_pairs = vec![];
        let mut arguments = vec![reference, expression];
        let class_type = Type::Set(Box::new(table.parameter_type.clone()));
        for mut members in fibers.into_values() {
            g.tick()?;
            members.sort_by_key(|v| v.wire().canonical());
            members.dedup();
            let points = members
                .iter()
                .map(|v| change_result::value(&mut b, v))
                .collect::<Result<Vec<_>, _>>()?;
            let class = change_result::value(
                &mut b,
                &Scalar::Set {
                    element: table.parameter_type.clone(),
                    items: members,
                },
            )?;
            let preimage = domain(&mut b, &table.parameter_type, &points)?;
            for point in &points {
                projection_pairs.push(Json::Arr(vec![point.wire(), class.wire()]));
            }
            arguments.extend(&points);
            arguments.extend([class, preimage]);
            classes.push(class);
            fibers_wire.push(Json::obj([
                ("image", class.wire()),
                ("preimage", preimage.wire()),
            ]));
        }
        let classes_domain = domain(&mut b, &class_type, &classes)?;
        let source_domain = b.push(
            NodeType::Domain,
            "domain",
            match &input.domain_type {
                ProjectionType::CandidateSpace(_) => Json::obj([
                    ("kind", Json::str("candidates")),
                    ("space", reference.wire()),
                ]),
                ProjectionType::SolutionSet(_) => Json::obj([
                    ("kind", Json::str("solutions")),
                    ("solutions", reference.wire()),
                ]),
                _ => return Err("商のdomain型が違う".into()),
            },
            vec![reference],
            None,
            None,
        )?;
        arguments.extend([source_domain, classes_domain]);
        let projection = b.push(
            NodeType::Construction(T::StateMap),
            "state_map",
            Json::obj([
                ("source", source_domain.wire()),
                ("target", classes_domain.wire()),
                ("kind", Json::str("finite")),
                ("pairs", Json::Arr(projection_pairs)),
            ]),
            arguments.clone(),
            None,
            None,
        )?;
        arguments.push(projection);
        let quotient = b.push(
            NodeType::Construction(T::Quotient),
            "quotient",
            Json::obj([
                ("domain", reference.wire()),
                (
                    "view",
                    Json::str(request.declaration().ok_or("商のviewがない")?),
                ),
                (
                    "bindings",
                    Json::Arr(
                        bindings
                            .iter()
                            .map(|(n, v)| Json::obj([("name", Json::str(n)), ("value", v.wire())]))
                            .collect(),
                    ),
                ),
                ("classes", classes_domain.wire()),
                ("projection", projection.wire()),
                (
                    "representation",
                    Json::obj([
                        ("kind", Json::str("finite")),
                        ("fibers", Json::Arr(fibers_wire)),
                    ]),
                ),
                ("evaluations", Json::Arr(vec![])),
            ]),
            arguments,
            None,
            None,
        )?;
        let scope = b.parts[quotient.0 - base].scope.clone();
        Ok(Source {
            base,
            parts: b.parts,
            answer: Answer {
                id: request.id.clone(),
                status: Decision::Established,
                outputs: BTreeMap::from([("quotient".into(), quotient)]),
                claim: None,
                evidence: vec![],
                reasons: vec![],
                scope,
            },
            request: request.clone(),
            witness: input.witness,
            domain_type: input.domain_type,
        })
    })
}
pub(super) fn evaluate(
    _prepared: &PreparedObserved,
    env: &Environment<'_>,
    g: &mut Graph,
    request: &Request,
    c: &mut Control,
) -> Result<Answer, ValidationFailure> {
    if let Some(answer) = super::public_map::unavailable(env, g, request)? {
        return Ok(answer);
    }
    let source = Arc::new(compute(env, g, request, g.nodes.len(), c)?);
    for (index, part) in source.parts.iter().enumerate() {
        native::retain(
            g,
            ConstructionValue {
                witness: Witness::Architecture(source.witness.clone()),
                data: D::Quotient(Data {
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
        return Err("商の元Architectureがない".into());
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
        return Err("商の元構成が違う".into());
    }
    for r in &p.arguments {
        g.get(*r)?;
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_quotient(
        &self,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        let D::Quotient(d) = &v.data else {
            return Ok(());
        };
        if d.index >= d.source.parts.len()
            || d.source.base + d.index != at
            || d.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("商の位置・既出参照が違う".into());
        }
        if self.quotient_source_checked(&d.source) {
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
            || rebuilt.domain_type != d.source.domain_type
        {
            return Err("商の再構成が違う".into());
        }
        self.remember_quotient_source(d.source.clone());
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
            Err("商の依存停止が違う".into())
        };
    }
    let r = answer.outputs.get("quotient").or_else(|| {
        answer.reasons.iter().find(|r| matches!(r.kind, ReasonKind::Missing))
            .and_then(|r| r.dependencies.first())
    }).ok_or("商の出力・不足の元式がない")?;
    let Some(Payload::Construction(v)) = &g.get(*r)?.payload else {
        return Err("商がnativeでない".into());
    };
    let D::Quotient(d) = &v.data else {
        return Err("商が別構成".into());
    };
    if &d.source.request != request || &d.source.answer != answer {
        return Err("商の元Request・回答が違う".into());
    }
    env.recheck_quotient(g, v, r.0)
}

pub(super) fn validate_origin(
    env: &Environment<'_>,
    request: &Request,
    v: &ConstructionValue,
) -> Result<(), ValidationFailure> {
    let D::Quotient(d) = &v.data else {
        return Err("商の構成が別種".into());
    };
    let Witness::Architecture(w) = &v.witness else {
        return Err("商の元Architectureがない".into());
    };
    if &d.source.request != request
        || !Arc::ptr_eq(w, &d.source.witness)
        || v.witness.inputs().sources() != env.inputs.sources()
    {
        return Err("商が現在の入力・Requestに属さない".into());
    }
    Ok(())
}
