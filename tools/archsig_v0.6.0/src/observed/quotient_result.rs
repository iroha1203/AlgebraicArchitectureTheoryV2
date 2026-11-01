//! 候補集合そのものの有限view商を公開する。
use super::{
    PreparedObserved,
    build_result::{Builder, Part},
    change_result, construction_result as native,
    construction_result::{
        ArchitectureWitness, ConstructionData as D, ConstructionType as T, ConstructionValue,
        Witness,
    },
    environment::{AnswerBinding, Environment, quotient_evaluation},
    projection::{ProjectionStep, ProjectionType},
    request::{Request, Selector},
    result::*,
};
use crate::control::Control;
use crate::{canonical::Json, issue::Location, law::model::Signature, types::Type};
use std::{collections::BTreeMap, sync::Arc};
mod affine_result;
mod law_result;
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
    pub(super) fn overrides(
        &self,
        g: &Graph,
    ) -> Result<Vec<(Fact, NodeRef, Scalar)>, ValidationFailure> {
        change_result::architecture_overrides(g, self.part())
    }
    pub(super) fn request(&self) -> &Request {
        &self.source.request
    }
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
            NodeType::Construction(T::Architecture) => Some(ProjectionType::Architecture),
            NodeType::Evaluation(ty) => Some(ProjectionType::Evaluation(ty)),
            NodeType::Proposition => Some(ProjectionType::Proposition),
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
            NodeType::Construction(T::Architecture) => field == "root",
            NodeType::Evaluation(_) => matches!(field.as_str(), "value" | "environment"),
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
fn domain(
    b: &mut Builder<'_>,
    ty: &Type,
    items: &[NodeRef],
    dependencies: &[NodeRef],
) -> Result<NodeRef, ValidationFailure> {
    b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("finite")),
            ("type", ty.wire()),
            ("elements", refs(items)),
        ]),
        items.iter().chain(dependencies).copied().collect(),
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
        if input.search.linear.is_some() || input.search.rational.is_some() {
            return affine_result::compute(env, g, input, reference, request, base, c);
        }
        let table = quotient_evaluation::compute(env, g, &input, request, c)?;
        let declaration = &env.indexes.inputs.law().declarations()
            [request.declaration().ok_or("商のviewがない")?];
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
            .map(|(name, v)| {
                let selector = &request
                    .arguments
                    .iter()
                    .find(|a| a.name == format!("bind.{name}"))
                    .ok_or("商の元束縛がない")?
                    .value;
                let reference = if matches!(selector, Selector::Answer { .. }) {
                    match env.answer_binding(g, selector, (0, 0))? {
                        AnswerBinding::Reference(r) => r,
                        AnswerBinding::Projection(node) => g
                            .nodes
                            .iter()
                            .position(|n| *n == node)
                            .map(NodeRef)
                            .ok_or("商の公開射影が保持されていない")?,
                        AnswerBinding::Inapplicable(_) => {
                            return Err(ValidationFailure::from("商の束縛射影が不適合"));
                        }
                    }
                } else {
                    change_result::value(&mut b, v)?
                };
                Ok((name.clone(), reference))
            })
            .collect::<Result<Vec<_>, ValidationFailure>>()?;
        let expression = change_result::source_expression(&mut b, env, *body, &bindings, &[])?;
        let expression_part = &mut b.parts[expression.0 - base];
        expression_part.arguments.push(reference);
        expression_part.arguments.sort_by_key(|r| r.0);
        expression_part.arguments.dedup();
        expression_part.scope.merge(&g.get(reference)?.scope);
        expression_part.scope.merge(&table.scope);
        expression_part
            .scope
            .readings
            .insert(declaration.reading.clone());
        let law_expression = if let Some((name, _)) = &table.law {
            let Signature::Law { params, body, .. } =
                &env.indexes.inputs.law().declarations()[name].signature
            else {
                unreachable!()
            };
            let selected = bindings
                .iter()
                .filter(|(name, _)| params.iter().any(|p| &p.name == name))
                .cloned()
                .collect::<Vec<_>>();
            let parameters = params
                .iter()
                .filter(|p| !selected.iter().any(|(n, _)| n == &p.name))
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect::<Vec<_>>();
            let law_expression =
                change_result::source_expression(&mut b, env, *body, &selected, &parameters)?;
            let part = &mut b.parts[law_expression.0 - base];
            part.arguments.push(reference);
            part.arguments.sort_by_key(|r| r.0);
            part.arguments.dedup();
            part.scope.merge(&table.scope);
            part.scope.merge(&g.get(reference)?.scope);
            Some(law_expression)
        } else {
            None
        };
        if !table.missing.is_empty() {
            let reason = Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: std::iter::once(expression).chain(law_expression).collect(),
                missing: table.missing,
                location: table
                    .law
                    .as_ref()
                    .map(|(name, _)| Location::Law {
                        span: env.indexes.inputs.law().declarations()[name].span,
                    })
                    .or(Some(Location::Law {
                        span: declaration.span,
                    })),
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
                witness: input.witness,
                domain_type: input.domain_type,
            });
        }
        let mut evaluations = vec![];
        let mut families = BTreeMap::new();
        let mut images = BTreeMap::new();
        if let Some((name, ty)) = &table.law {
            for row in &table.rows {
                let (family, rows) =
                    law_result::row(&mut b, env, &input, row, name, ty, expression)?;
                evaluations.extend(rows);
                families.insert(row.parameters.wire().canonical(), family);
                images.insert(row.parameters.wire().canonical(), row.image.clone());
            }
        }
        let mut descent_pairs = vec![];
        let mut family_values = vec![];
        let mut separating = None;
        // Setは列挙順が違っても等しい。表示キーでなく型付き等値で分ける。
        let mut fibers: Vec<(Scalar, Vec<Scalar>)> = vec![];
        for row in table.rows {
            g.tick()?;
            let mut existing = None;
            for (index, (image, _)) in fibers.iter().enumerate() {
                c.checkpoint(crate::control::Checkpoint::Quotient)?;
                if super::data::equal(image, &row.image, c)? {
                    existing = Some(index);
                    break;
                }
            }
            if let Some(index) = existing {
                fibers[index].1.push(row.parameters);
            } else {
                fibers.push((row.image, vec![row.parameters]));
            }
        }
        fibers.sort_by_cached_key(|(image, _)| image.wire().canonical());
        let mut classes = vec![];
        let mut fibers_wire = vec![];
        let mut projection_pairs = vec![];
        let mut arguments = vec![reference, expression];
        let class_type = Type::Set(Box::new(table.parameter_type.clone()));
        for (_, mut members) in fibers {
            g.tick()?;
            members.sort_by_key(|v| v.wire().canonical());
            members.dedup();
            let points = members
                .iter()
                .map(|v| change_result::value(&mut b, v))
                .collect::<Result<Vec<_>, _>>()?;
            if table.law.is_some() {
                let first = &members[0];
                let first_family = &families[&first.wire().canonical()];
                let first_ref = change_result::value(&mut b, first_family)?;
                family_values.push(first_ref);
                for (member, point) in members.iter().zip(&points) {
                    let family = &families[&member.wire().canonical()];
                    if separating.is_none() && !super::data::equal(family, first_family, c)? {
                        let other = change_result::value(&mut b, family)?;
                        let view =
                            change_result::value(&mut b, &images[&member.wire().canonical()])?;
                        separating = Some((points[0], *point, view, first_ref, other));
                    }
                }
            }
            let class = change_result::value(
                &mut b,
                &Scalar::Set {
                    element: table.parameter_type.clone(),
                    items: members,
                },
            )?;
            if let Some(family) = family_values.last().filter(|_| table.law.is_some()) {
                descent_pairs.push(Json::Arr(vec![class.wire(), family.wire()]));
            }
            let preimage = domain(
                &mut b,
                &table.parameter_type,
                &points,
                &[reference, expression],
            )?;
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
        let classes_domain = domain(&mut b, &class_type, &classes, &[reference, expression])?;
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
        arguments.extend(&evaluations);
        arguments.extend(law_expression);
        let descent = if let Some((name, ty)) = &table.law {
            if separating.is_none() {
                family_values.sort_by_key(|r| r.0);
                family_values.dedup();
                let mut dependencies = vec![reference, expression];
                dependencies.extend(law_expression);
                dependencies.extend(&evaluations);
                let target = domain(
                    &mut b,
                    &law_result::family_type(env, name, ty)?,
                    &family_values,
                    &dependencies,
                )?;
                let mut args = vec![classes_domain, target];
                args.extend(&family_values);
                let map = b.push(
                    NodeType::Construction(T::StateMap),
                    "state_map",
                    Json::obj([
                        ("source", classes_domain.wire()),
                        ("target", target.wire()),
                        ("kind", Json::str("finite")),
                        ("pairs", Json::Arr(descent_pairs)),
                    ]),
                    args,
                    None,
                    None,
                )?;
                arguments.push(map);
                Some(map)
            } else {
                None
            }
        } else {
            None
        };
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
                ("evaluations", refs(&evaluations)),
            ]),
            arguments,
            None,
            None,
        )?;
        let mut outputs = BTreeMap::from([("quotient".into(), quotient)]);
        let mut evidence = vec![];
        let mut claim = None;
        let mut status = Decision::Established;
        if let Some((name, _)) = &table.law {
            let Json::Obj(wire) = &mut b.parts[quotient.0 - base].wire else {
                unreachable!()
            };
            wire.insert("law".into(), Json::str(name));
            if let Some(descent) = descent {
                wire.insert("descent".into(), descent.wire());
            }
            if let Some((first, second, view, left, right)) = separating {
                status = Decision::Refuted;
                evidence.push(b.push(
                    NodeType::Evidence,
                    "evidence",
                    Json::obj([
                        ("kind", Json::str("separating_pair")),
                        (
                            "data",
                            Json::obj([
                                ("domain", reference.wire()),
                                ("first", first.wire()),
                                ("second", second.wire()),
                                ("view_values", refs(&[view, view])),
                                ("law_values", refs(&[left, right])),
                            ]),
                        ),
                    ]),
                    vec![reference, first, second, view, left, right],
                    None,
                    None,
                )?);
            }
            let proposition =
                b.proposition("sufficient", vec![quotient], evidence.clone(), status)?;
            let part = &mut b.parts[proposition.0 - base];
            part.evidence = evidence.clone();
            part.judgment.as_mut().ok_or("十分性判断がない")?.evidence = evidence.clone();
            outputs.insert("proposition".into(), proposition);
            claim = Some(proposition);
        }
        let scope = b.parts[quotient.0 - base].scope.clone();
        Ok(Source {
            base,
            parts: b.parts,
            answer: Answer {
                id: request.id.clone(),
                status,
                outputs,
                claim,
                evidence,
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
    <Data as super::result_kind::ResultKind>::compute_and_retain((_prepared, env, g, request, c))
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
    let r = answer
        .outputs
        .get("quotient")
        .or_else(|| {
            answer
                .reasons
                .iter()
                .find(|r| matches!(r.kind, ReasonKind::Missing))
                .and_then(|r| r.dependencies.first())
        })
        .ok_or("商の出力・不足の元式がない")?;
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
        || v.witness.inputs().sources() != env.indexes.inputs.sources()
    {
        return Err("商が現在の入力・Requestに属さない".into());
    }
    Ok(())
}

impl super::result_kind::ResultKind for Data {
    type Input<'a, 'input: 'a> = (
        &'a PreparedObserved,
        &'a Environment<'input>,
        &'a mut Graph,
        &'a Request,
        &'a mut Control,
    );
    type Output = Answer;
    fn compute_and_retain<'a, 'input: 'a>(
        input: Self::Input<'a, 'input>,
    ) -> Result<Self::Output, ValidationFailure> {
        let (_prepared, env, g, request, c) = input;
        env.commit_projection_conditions(g, request)?;
        if let Some(answer) = super::public_map::unavailable(env, g, request)? {
            return Ok(answer);
        }
        for argument in &request.arguments {
            if argument.name.starts_with("bind.")
                && matches!(argument.value, Selector::Answer { .. })
            {
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
    fn validate(
        &self,
        graph: &Graph,
        node: &Node,
        value: &super::construction_result::ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        validate_node(graph, node, value, self)
    }
    fn recheck(
        &self,
        env: &Environment<'_>,
        graph: &Graph,
        value: &super::construction_result::ConstructionValue,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        env.recheck_quotient(graph, value, limit)?;
        Ok(())
    }
}
