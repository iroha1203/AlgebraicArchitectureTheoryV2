//! 有限changeの元parameter座標を保った公開候補域と全解。
use super::{
    PreparedObserved,
    architecture_result::{self, Architecture},
    build_result::{Builder, Part},
    construction_result as native,
    construction_result::{
        ConstructionData as D, ConstructionType as T, ConstructionValue, Witness,
    },
    environment::{Environment, change_evaluation::State, change_search},
    native_source::Boundary,
    projection::{ProjectionStep, ProjectionType},
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::control::{Checkpoint, Control};
use crate::{canonical::Json, issue::Location, law::model::Signature, types::Type};
use std::{collections::BTreeMap, sync::Arc};
pub(super) mod field_linear_result;
pub(super) mod linear_result;

mod owner_completion;

#[derive(Debug)]
pub(super) struct Source {
    architecture: Architecture,
    boundary: Boundary,
    base: usize,
    parts: Vec<Part>,
    answer: Answer,
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
    pub(super) fn is_blocked(&self) -> bool {
        self.part().ty == NodeType::Construction(T::SolutionSet)
            && self.part().wire == Json::obj([])
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty.clone()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction
    }
    pub(super) fn wire(&self) -> Json {
        self.part().wire.clone()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        self.part().arguments.clone()
    }
    pub(super) fn completion_uniqueness(&self) -> Option<Decision> {
        if !self.source.parts.iter().any(|part| {
            part.ty == NodeType::Construction(T::SolutionSet) && part.wire == Json::obj([])
        }) {
            return None;
        }
        self.source.parts.iter().find_map(|part| {
            if matches!(&part.wire, Json::Obj(fields) if fields.get("predicate") == Some(&Json::str("unique_solution"))) {
                part.judgment.as_ref().map(|j| j.status)
            } else { None }
        })
    }
    pub(super) fn conditions(&self) -> Vec<NodeRef> {
        let completion_condition = self.part().ty == NodeType::Proposition
            && self.source.parts.iter().any(|part| {
                part.ty == NodeType::Construction(T::SolutionSet) && part.wire == Json::obj([])
            })
            && matches!(&self.part().wire, Json::Obj(fields) if fields.get("predicate") == Some(&Json::str("constructible")));
        if !completion_condition
            && !matches!(
                self.ty(),
                NodeType::Construction(T::Repair | T::Architecture)
            )
        {
            return vec![];
        }
        self.part()
            .arguments
            .iter()
            .copied()
            .filter(|r| {
                r.0 >= self.source.base
                    && self
                        .source
                        .parts
                        .get(r.0 - self.source.base)
                        .is_some_and(|p| p.ty == NodeType::Proposition)
            })
            .collect()
    }
    pub(super) fn overrides(
        &self,
        g: &Graph,
    ) -> Result<Vec<(Fact, NodeRef, Scalar)>, ValidationFailure> {
        architecture_overrides(g, self.part())
    }

    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.part().support.clone(), self.part().scope.clone())
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        self.part().scalar.as_ref()
    }
    pub(super) fn projection_type(&self) -> Option<ProjectionType> {
        let root = self.source.architecture.witness.construction().root();
        let origin = Witness::Architecture(self.source.architecture.witness.clone());
        let inputs = origin.inputs();
        let ty = inputs
            .archmap()
            .snapshots()
            .iter()
            .flat_map(|s| &s.subjects)
            .find(|s| s.snapshot == root.snapshot && s.id == root.subject)?
            .ty
            .clone();
        match self.ty() {
            NodeType::Construction(T::CandidateSpace) => {
                Some(ProjectionType::CandidateSpace(ty.into()))
            }
            NodeType::Construction(T::SolutionSet) => Some(ProjectionType::SolutionSet(ty.into())),
            NodeType::Construction(T::StateSpace) => Some(ProjectionType::StateSpace(ty.into())),
            NodeType::Construction(T::StateMap) => Some(ProjectionType::StateMap),
            NodeType::Construction(T::Architecture) => {
                Some(ProjectionType::ArchitectureRoot(ty.into()))
            }
            NodeType::Construction(T::Repair) => Some(ProjectionType::Repair(ty.into())),
            NodeType::Construction(T::Assignment) => Some(ProjectionType::Assignment(ty.into())),
            NodeType::Domain => Some(ProjectionType::Domain),
            _ => None,
        }
    }
    pub(super) fn project(&self, path: &[ProjectionStep]) -> Option<(NodeRef, usize)> {
        let ProjectionStep::Field(field) = path.first()? else {
            return None;
        };
        let allowed = match self.ty() {
            NodeType::Construction(T::CandidateSpace) => {
                matches!(field.as_str(), "base" | "parameters" | "states" | "action")
            }
            NodeType::Construction(T::SolutionSet) => field == "domain",
            NodeType::Construction(T::StateMap) => matches!(field.as_str(), "source" | "target"),
            NodeType::Construction(T::Architecture) => field == "root",
            NodeType::Construction(T::Repair) => matches!(
                field.as_str(),
                "domain" | "solutions" | "parameters" | "object"
            ),
            NodeType::Construction(T::Assignment) => field == "domain",
            _ => false,
        };
        if !allowed {
            return None;
        }
        let Json::Obj(wire) = &self.part().wire else {
            return None;
        };
        let selected = wire.get(field)?;
        self.part()
            .arguments
            .iter()
            .find(|r| &r.wire() == selected)
            .map(|r| (*r, 1))
    }
}
fn refs(values: &[NodeRef]) -> Json {
    Json::Arr(values.iter().map(|r| r.wire()).collect())
}
pub(super) fn value(b: &mut Builder<'_>, scalar: &Scalar) -> Result<NodeRef, ValidationFailure> {
    if let Some(reference) = b.g.retained_path_binding(scalar)? {
        return Ok(reference);
    }
    for (index, part) in b.parts.iter().enumerate() {
        b.g.tick()?;
        if part.scalar.as_ref() == Some(scalar) {
            return Ok(NodeRef(b.base + index));
        }
    }
    b.push(
        NodeType::Value(scalar.ty()),
        "binding",
        scalar.wire(),
        vec![],
        Some(scalar.clone()),
        None,
    )
}
pub(super) fn source_expression(
    b: &mut Builder<'_>,
    environment: &Environment<'_>,
    expression: usize,
    bindings: &[(String, NodeRef)],
    parameters: &[(String, Type)],
) -> Result<NodeRef, ValidationFailure> {
    let ast = environment
        .indexes
        .inputs
        .law()
        .exprs()
        .get(expression)
        .ok_or("changeの元式がない")?;
    let ty = environment
        .indexes
        .inputs
        .law()
        .expr_type(expression)
        .ok_or("changeの元式型がない")?
        .clone();
    b.push(
        NodeType::Expression(ty),
        "expression",
        Json::obj([
            ("kind", Json::str("source")),
            (
                "location",
                crate::result::location_wire(&Location::Law { span: ast.span }),
            ),
            (
                "parameters",
                Json::Arr(
                    parameters
                        .iter()
                        .map(|(name, ty)| {
                            Json::obj([("name", Json::str(name)), ("type", ty.wire())])
                        })
                        .collect(),
                ),
            ),
            (
                "bindings",
                Json::Arr(
                    bindings
                        .iter()
                        .map(|(name, r)| {
                            Json::obj([("name", Json::str(name)), ("value", r.wire())])
                        })
                        .collect(),
                ),
            ),
        ]),
        bindings.iter().map(|(_, r)| *r).collect(),
        None,
        None,
    )
}
fn compute(
    env: &Environment<'_>,
    g: &Graph,
    architecture: &Architecture,
    base: usize,
    request: &Request,
    c: &mut Control,
) -> Result<(Vec<Part>, Answer, Option<change_search::Search>), ValidationFailure> {
    env.validation_graph_session(g, || compute_inner(env, g, architecture, base, request, c))
}
fn compute_inner(
    env: &Environment<'_>,
    g: &Graph,
    architecture: &Architecture,
    base: usize,
    request: &Request,
    c: &mut Control,
) -> Result<(Vec<Part>, Answer, Option<change_search::Search>), ValidationFailure> {
    if !architecture.complete {
        if let Some(result) =
            owner_completion::compute(env, g, architecture, base, request, c, &[])?
        {
            return Ok(result);
        }
        return Err(ValidationFailure::UnsupportedExpression {
            location: Location::Law { span: (0, 0) },
            feature: "未完成Architecture上のchange候補の公開配送は未実装".into(),
        });
    }
    let search = match change_search::search(env, g, &architecture.witness, request, c) {
        Ok(search) => search,
        Err(failure) => {
            if let Some(pending) = &failure.partial.pending_integer {
                if let ValidationFailure::UnsupportedExpression { location, .. } = failure.cause {
                    let mut b = Builder {
                        g,
                        base,
                        parts: vec![],
                    };
                    let bindings = pending
                        .bindings
                        .iter()
                        .map(|(name, scalar)| Ok((name.clone(), value(&mut b, scalar)?)))
                        .collect::<Result<Vec<_>, ValidationFailure>>()?;
                    let expression = source_expression(
                        &mut b,
                        env,
                        pending.expression.ok_or("整数欠測の元式がない")?,
                        &bindings,
                        &pending.parameters,
                    )?;
                    let part = &mut b.parts[expression.0 - base];
                    part.arguments.push(architecture.reference);
                    part.scope.merge(&g.get(architecture.reference)?.scope);
                    let scope = part.scope.clone();
                    let mut reasons = vec![];
                    if !failure.partial.missing.is_empty() {
                        reasons.push(Reason {
                            kind: ReasonKind::Missing,
                            request: request.id.clone(),
                            dependencies: vec![expression],
                            missing: failure.partial.missing,
                            location: Some(location.clone()),
                        });
                    }
                    reasons.push(Reason {
                        kind: ReasonKind::UnsupportedAlgorithm {
                            question: request.kind,
                            operand_types: vec![
                                pending.coefficient_type.clone().unwrap_or(Type::Z),
                            ],
                            method: pending.unsupported.map(str::to_owned).unwrap_or_else(|| {
                                if pending.coefficient_type == Some(Type::Q) {
                                    "rational_change".into()
                                } else {
                                    "integer_change".into()
                                }
                            }),
                        },
                        request: request.id.clone(),
                        dependencies: vec![expression],
                        missing: vec![],
                        location: Some(location.clone()),
                    });
                    return Ok((
                        b.parts,
                        Answer {
                            id: request.id.clone(),
                            status: Decision::Undetermined,
                            outputs: BTreeMap::new(),
                            claim: None,
                            evidence: vec![],
                            reasons,
                            scope,
                        },
                        None,
                    ));
                }
            }
            return Err(failure.cause);
        }
    };
    let unsupported = || ValidationFailure::UnsupportedExpression {
        location: Location::Law { span: (0, 0) },
        feature: "有限changeの未確定候補・解の公開配送は未実装".into(),
    };
    let pending = !search.complete
        || search.solutions.iter().any(|r| r.member.is_none())
        || search.candidates.as_ref().is_none_or(|table| {
            !table.complete
                || table
                    .rows
                    .iter()
                    .any(|row| row.update.state == State::Undetermined)
        });
    if pending {
        let missing = search
            .missing
            .iter()
            .cloned()
            .chain(
                search
                    .candidates
                    .iter()
                    .flat_map(|table| &table.rows)
                    .flat_map(|row| row.update.missing.iter().cloned()),
            )
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if architecture.complete
            && !missing.is_empty()
            && let Some(result) =
                owner_completion::compute(env, g, architecture, base, request, c, &missing)?
        {
            return Ok(result);
        }
        return Err(unsupported());
    }
    render_search(env, g, architecture, base, request, c, search)
}

pub(super) fn render_search(
    env: &Environment<'_>,
    g: &Graph,
    architecture: &Architecture,
    base: usize,
    request: &Request,
    c: &mut Control,
    search: change_search::Search,
) -> Result<(Vec<Part>, Answer, Option<change_search::Search>), ValidationFailure> {
    let candidates = search.candidates.as_ref().ok_or("有限候補表がない")?;
    let change_name = request
        .arguments
        .iter()
        .find_map(|a| {
            if a.name == "using" {
                if let Selector::Declaration { name } = &a.value {
                    Some(name)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .ok_or("change名がない")?;
    let declaration = &env.indexes.inputs.law().declarations()[change_name];
    let Signature::Change { params, guard, .. } = &declaration.signature else {
        return Err("change署名がない".into());
    };
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let subjects = candidates
        .subjects
        .iter()
        .map(|s| value(&mut b, s))
        .collect::<Result<Vec<_>, _>>()?;
    let mut selected_bindings = vec![];
    let mut binding_refs = vec![];
    for (name, scalar) in &search.bindings {
        let r = value(&mut b, scalar)?;
        binding_refs.push(r);
        selected_bindings.push(Json::obj([("name", Json::str(name)), ("value", r.wire())]));
    }
    let mut requirements = vec![];
    for (name, bindings) in &search.requirements {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        let law = &env.indexes.inputs.law().declarations()[name];
        let Signature::Law {
            role,
            body,
            guard,
            params: law_params,
        } = &law.signature
        else {
            return Err("候補の元Lawがない".into());
        };
        let bindings = bindings
            .iter()
            .map(|(name, v)| Ok((name.clone(), value(&mut b, v)?)))
            .collect::<Result<Vec<_>, ValidationFailure>>()?;
        let unbound = law_params
            .iter()
            .filter(|p| !bindings.iter().any(|(name, _)| *name == p.name))
            .collect::<Vec<_>>();
        let parameters = unbound
            .iter()
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<Vec<_>>();
        let body = source_expression(&mut b, env, *body, &bindings, &parameters)?;
        for parameter in unbound {
            b.parts[body.0 - base].scope.quantifiers.push(Quantifier {
                kind: crate::law::ast::QuantKind::Forall,
                name: parameter.name.clone(),
                ty: parameter.ty.erase(),
                domain: None,
                occurrence: parameter.span,
                context: Some(env.current_context(g)),
            });
        }
        let guard = guard
            .map(|id| source_expression(&mut b, env, id, &bindings, &parameters))
            .transpose()?;
        let mut args = bindings.iter().map(|(_, r)| *r).collect::<Vec<_>>();
        args.push(body);
        args.extend(guard);
        let mut wire = vec![
            ("name", Json::str(name)),
            (
                "role",
                Json::str(match role {
                    crate::law::ast::Role::Required => "required",
                    crate::law::ast::Role::Optional => "optional",
                }),
            ),
            (
                "occurrence",
                crate::result::location_wire(&Location::Law { span: law.span }),
            ),
            (
                "bindings",
                Json::Arr(
                    bindings
                        .iter()
                        .map(|(name, r)| {
                            Json::obj([("name", Json::str(name)), ("value", r.wire())])
                        })
                        .collect(),
                ),
            ),
            ("body", body.wire()),
        ];
        if let Some(r) = guard {
            wire.push(("guard", r.wire()));
        }
        requirements.push(b.push(
            NodeType::LawInstance,
            "law_instance",
            Json::Obj(wire.into_iter().map(|(k, v)| (k.into(), v)).collect()),
            args,
            None,
            None,
        )?);
    }
    let mut guards = vec![];
    if let Some(expression) = guard {
        let residual = params[1..]
            .iter()
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<Vec<_>>();
        for &subject in &subjects {
            guards.push(source_expression(
                &mut b,
                env,
                *expression,
                &[(params[0].name.clone(), subject)],
                &residual,
            )?);
        }
    }
    let mut points = vec![];
    let mut states = vec![];
    let mut pairs = vec![];
    let mut solutions = vec![];
    let names = super::environment::change_evaluation::update_fields(env, declaration)?;
    let mut slots = vec![];
    for subject in &candidates.subjects {
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = subject
        else {
            return Err("変更対象がsubjectでない".into());
        };
        for name in &names {
            slots.push(Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: Some(env.input_name(&format!("{entity}.{name}"))?),
                atom: None,
            });
        }
    }
    slots.sort();
    if search
        .linear
        .as_ref()
        .is_some_and(|linear| linear.slots != slots)
        || search
            .rational
            .as_ref()
            .is_some_and(|linear| linear.slots != slots)
    {
        return Err(ValidationFailure::UnsupportedExpression {
            location: Location::Law {
                span: declaration.span,
            },
            feature: "整数changeの実更新先と公開slot集合が異なる".into(),
        });
    }
    for (index, row) in candidates.rows.iter().enumerate() {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        if matches!(row.update.state, State::Excluded | State::ConditionFailed) {
            continue;
        }
        let row_slots = row
            .update
            .values
            .iter()
            .map(|(f, _)| f.clone())
            .collect::<Vec<_>>();
        if slots != row_slots {
            return Err(ValidationFailure::UnsupportedExpression {
                location: Location::Law {
                    span: declaration.span,
                },
                feature: "分岐で更新slot集合が異なるchangeの状態表は未実装".into(),
            });
        }
        let point = value(&mut b, &Scalar::Tuple(row.parameters.clone()))?;
        let state = value(
            &mut b,
            &Scalar::Tuple(row.update.values.iter().map(|(_, v)| v.clone()).collect()),
        )?;
        points.push(point);
        states.push(state);
        pairs.push(Json::Arr(vec![point.wire(), state.wire()]));
        if search
            .solutions
            .get(index)
            .is_some_and(|r| r.member == Some(true))
        {
            solutions.push(point);
        }
    }
    let parameter_type = Type::Tuple(candidates.parameter_types.clone());
    let linear_parts = if let Some(linear) = &search.rational {
        Some(field_linear_result::build(
            &mut b,
            linear,
            &requirements,
            c,
        )?)
    } else {
        search
            .linear
            .as_ref()
            .map(|linear| linear_result::build(&mut b, linear, &requirements, c))
            .transpose()?
    };
    let parameters = if let Some(linear) = &linear_parts {
        linear.parameters
    } else {
        b.push(
            NodeType::Domain,
            "domain",
            Json::obj([
                ("kind", Json::str("finite")),
                ("type", parameter_type.wire()),
                ("elements", refs(&points)),
            ]),
            points.clone(),
            None,
            None,
        )?
    };
    let mut slot_values = vec![];
    let mut state_types = vec![];
    let mut state_args = vec![architecture.reference];
    for slot in slots {
        let subject = env.indexes.subject(&slot.snapshot, &slot.subject)?;
        let r = value(
            &mut b,
            &Scalar::Subject {
                snapshot: slot.snapshot.clone(),
                subject: slot.subject.clone(),
                entity: subject.ty.to_string(),
            },
        )?;
        state_args.push(r);
        let field = slot.field.as_ref().ok_or("更新slotのfieldがない")?;
        state_types.push(
            env.indexes
                .field(&env.state, &slot.snapshot, &slot.subject, field)?
                .ty
                .erase(),
        );
        slot_values.push(Json::obj([
            ("subject", r.wire()),
            ("field", Json::str(field)),
        ]));
    }
    let state_type = Type::Tuple(state_types);
    let state_space = b.push(
        NodeType::Construction(T::StateSpace),
        "state_space",
        Json::obj([
            ("base", architecture.reference.wire()),
            ("slots", Json::Arr(slot_values)),
            ("state_type", state_type.wire()),
        ]),
        state_args,
        None,
        None,
    )?;
    let mut state_order = BTreeMap::new();
    for state in states {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        state_order.insert(b.parts[state.0 - base].wire.canonical(), state);
    }
    let states = state_order.into_values().collect::<Vec<_>>();
    let state_domain = if let Some(linear) = &linear_parts {
        linear.states
    } else {
        b.push(
            NodeType::Domain,
            "domain",
            Json::obj([
                ("kind", Json::str("finite")),
                ("type", state_type.wire()),
                ("elements", refs(&states)),
            ]),
            states.clone(),
            None,
            None,
        )?
    };
    let mut action_args = vec![parameters, state_domain];
    action_args.extend(&points);
    action_args.extend(&states);
    let action = if let Some(linear) = &linear_parts {
        linear.action
    } else {
        b.push(
            NodeType::Construction(T::StateMap),
            "state_map",
            Json::obj([
                ("source", parameters.wire()),
                ("target", state_domain.wire()),
                ("kind", Json::str("finite")),
                ("pairs", Json::Arr(pairs)),
            ]),
            action_args,
            None,
            None,
        )?
    };
    let mut domain_args = vec![architecture.reference, parameters, state_space, action];
    domain_args.extend(&subjects);
    domain_args.extend(&requirements);
    domain_args.extend(&guards);
    domain_args.extend(binding_refs);
    let width = params.len() - 1;
    let instances = subjects
        .iter()
        .enumerate()
        .map(|(i, r)| {
            Json::obj([
                ("subject", r.wire()),
                (
                    "positions",
                    Json::Arr(
                        (i * width..(i + 1) * width)
                            .map(|n| Json::Nat(n as u64))
                            .collect(),
                    ),
                ),
            ])
        })
        .collect();
    let domain = b.push(
        NodeType::Construction(T::CandidateSpace),
        "candidate_space",
        Json::obj([
            ("kind", Json::str("change")),
            ("base", architecture.reference.wire()),
            ("bindings", Json::Arr(selected_bindings)),
            ("change", Json::str(change_name)),
            ("parameters", parameters.wire()),
            ("states", state_space.wire()),
            ("action", action.wire()),
            ("instances", Json::Arr(instances)),
            ("guards", refs(&guards)),
            ("requirements", refs(&requirements)),
        ]),
        domain_args,
        None,
        None,
    )?;
    // 検査済み全候補表の再計算が全域性を担う。出力に各試行のtraceを複製しない。
    let certificate = if let Some(linear) = &linear_parts {
        linear.certificate
    } else {
        b.push(
            NodeType::Evidence,
            "evidence",
            Json::obj([
                ("kind", Json::str("finite_exhaustion")),
                (
                    "data",
                    Json::obj([
                        ("domain", parameters.wire()),
                        ("checked", Json::Nat(points.len() as u64)),
                        ("instances", refs(&requirements)),
                    ]),
                ),
            ]),
            vec![domain, parameters],
            None,
            None,
        )?
    };
    let representation = if let Some(linear) = &linear_parts {
        linear.representation.clone()
    } else if solutions.is_empty() {
        Json::obj([
            ("kind", Json::str("empty")),
            ("certificate", certificate.wire()),
        ])
    } else {
        Json::obj([("kind", Json::str("finite")), ("values", refs(&solutions))])
    };
    let mut solution_args = vec![domain, certificate];
    if let Some(linear) = &linear_parts {
        solution_args.extend(&linear.representation_args);
    }
    solution_args.extend(&requirements);
    solution_args.extend(&solutions);
    let set = b.push(
        NodeType::Construction(T::SolutionSet),
        "solution_set",
        Json::obj([
            ("domain", domain.wire()),
            ("requirements", refs(&requirements)),
            ("representation", representation),
        ]),
        solution_args,
        None,
        None,
    )?;
    let mut status = if solutions.is_empty() {
        Decision::Refuted
    } else {
        Decision::Established
    };
    let mut claim = b.proposition("inhabited", vec![set], vec![certificate], status)?;
    b.parts[claim.0 - base]
        .judgment
        .as_mut()
        .ok_or("解存在の判断がない")?
        .evidence
        .push(certificate);
    let mut outputs = BTreeMap::from([
        ("domain".into(), domain),
        ("solutions".into(), set),
        ("proposition".into(), claim),
    ]);
    let mut reasons = vec![];
    if request.kind == QuestionKind::Repair {
        outputs.insert("existence".into(), claim);
        let unique_status = if solutions.len() == 1 {
            Decision::Established
        } else {
            Decision::Refuted
        };
        let mut unique_evidence = vec![certificate];
        let mut unique_arguments = vec![certificate];
        if solutions.len() > 1 {
            let mut witnesses = vec![];
            let mut membership = vec![];
            for solution in search
                .solutions
                .iter()
                .filter(|r| r.member == Some(true))
                .take(2)
            {
                let row = &candidates.rows[solution.candidate];
                let mut entries = vec![];
                let mut args = vec![domain];
                for (index, &subject) in subjects.iter().enumerate() {
                    let parameters = row.parameters[index * width..(index + 1) * width]
                        .iter()
                        .map(|v| value(&mut b, v))
                        .collect::<Result<Vec<_>, _>>()?;
                    args.push(subject);
                    args.extend(&parameters);
                    entries.push(Json::obj([
                        ("subject", subject.wire()),
                        ("parameters", refs(&parameters)),
                    ]));
                }
                let assignment = b.push(
                    NodeType::Construction(T::Assignment),
                    "assignment",
                    Json::obj([("domain", domain.wire()), ("entries", Json::Arr(entries))]),
                    args,
                    None,
                    None,
                )?;
                membership.push(b.proposition(
                    "solution_member",
                    vec![set, assignment],
                    vec![certificate],
                    Decision::Established,
                )?);
                witnesses.push(assignment);
            }
            let mut args = witnesses.clone();
            args.extend(&membership);
            let counter = b.push(
                NodeType::Evidence,
                "evidence",
                Json::obj([
                    ("kind", Json::str("counterexample")),
                    (
                        "data",
                        Json::obj([
                            ("bindings", Json::Arr(vec![])),
                            ("paths", Json::Arr(vec![])),
                            ("left", witnesses[0].wire()),
                            ("right", witnesses[1].wire()),
                            ("facts", Json::Arr(vec![])),
                        ]),
                    ),
                ]),
                args,
                None,
                None,
            )?;
            let unequal = b.proposition("equal", witnesses, vec![counter], Decision::Refuted)?;
            b.parts[unequal.0 - base]
                .judgment
                .as_mut()
                .ok_or("割当ての不等判断がない")?
                .evidence
                .push(counter);
            unique_arguments.extend([counter, unequal]);
            unique_arguments.extend(membership);
            unique_evidence.push(counter);
        }
        let unique = b.proposition(
            "unique_solution",
            vec![set],
            unique_arguments,
            unique_status,
        )?;
        b.parts[unique.0 - base]
            .judgment
            .as_mut()
            .ok_or("一意性判断がない")?
            .evidence = unique_evidence.clone();
        let mut conditions = vec![unique];
        let mut assignment = None;
        let mut updates = vec![];
        let mut steps = vec![];
        if solutions.len() == 1 {
            let row_index = search
                .solutions
                .iter()
                .find(|r| r.member == Some(true))
                .ok_or("唯一の解の元割当てがない")?
                .candidate;
            let row = &candidates.rows[row_index];
            let mut entries = vec![];
            let mut args = vec![domain];
            for (index, &subject) in subjects.iter().enumerate() {
                let parameters = row.parameters[index * width..(index + 1) * width]
                    .iter()
                    .map(|v| value(&mut b, v))
                    .collect::<Result<Vec<_>, _>>()?;
                args.push(subject);
                args.extend(&parameters);
                entries.push(Json::obj([
                    ("subject", subject.wire()),
                    ("parameters", refs(&parameters)),
                ]));
                steps.push(Json::obj([
                    ("subject", subject.wire()),
                    ("change", Json::str(change_name)),
                    ("parameters", refs(&parameters)),
                ]));
            }
            let parameters = b.push(
                NodeType::Construction(T::Assignment),
                "assignment",
                Json::obj([("domain", domain.wire()), ("entries", Json::Arr(entries))]),
                args,
                None,
                None,
            )?;
            let member = b.proposition(
                "solution_member",
                vec![set, parameters],
                vec![certificate],
                Decision::Established,
            )?;
            conditions.push(member);
            assignment = Some(parameters);
            for (fact, scalar) in &row.update.values {
                let subject = env.indexes.subject(&fact.snapshot, &fact.subject)?;
                let subject = value(
                    &mut b,
                    &Scalar::Subject {
                        snapshot: fact.snapshot.clone(),
                        subject: fact.subject.clone(),
                        entity: subject.ty.to_string(),
                    },
                )?;
                let updated = value(&mut b, scalar)?;
                updates.push((
                    subject,
                    fact.field.clone().ok_or("更新fieldがない")?,
                    updated,
                ));
            }
        }
        if let Some(parameters) = assignment {
            for &law in &requirements {
                conditions.push(b.proposition(
                    "law_holds",
                    vec![law],
                    vec![parameters, set, certificate],
                    Decision::Established,
                )?);
            }
        }
        let label = value(&mut b, &Scalar::Text("repair".into()))?;
        claim = b.proposition(
            "constructible",
            vec![label, domain, set],
            conditions.clone(),
            unique_status,
        )?;
        status = unique_status;
        b.parts[claim.0 - base]
            .judgment
            .as_mut()
            .ok_or("修復構成判断がない")?
            .evidence = unique_evidence;
        outputs.insert("proposition".into(), claim);
        if let Some(parameters) = assignment {
            let Some(Payload::Construction(original)) = &g.get(architecture.reference)?.payload
            else {
                return Err("修復元Architectureがnativeでない".into());
            };
            let mut original_wire = original.wire();
            let Json::Obj(wire) = &mut original_wire else {
                return Err("修復元Architecture recordがない".into());
            };
            let Some(Json::Arr(previous)) = wire.get_mut("overrides") else {
                return Err("修復元の更新表がない".into());
            };
            let mut overrides = BTreeMap::new();
            for row in std::mem::take(previous) {
                let Json::Obj(fields) = &row else {
                    return Err("修復元slotがrecordでない".into());
                };
                overrides.insert(
                    fields.get("slot").ok_or("修復元slotがない")?.canonical(),
                    row,
                );
            }
            let mut args = original.arguments();
            args.extend([architecture.reference, claim]);
            for (subject, field, updated) in &updates {
                args.extend([*subject, *updated]);
                let slot = Json::obj([("subject", subject.wire()), ("field", Json::str(field))]);
                // subjectのRef nodeが違っても同じslotの更新は置換する。
                let current = if subject.0 < base {
                    g.scalar(*subject)?
                } else {
                    b.parts[subject.0 - base]
                        .scalar
                        .as_ref()
                        .ok_or("更新subject値がない")?
                };
                overrides.retain(|_, row| {
                    let Json::Obj(row) = row else {
                        return true;
                    };
                    let Some(Json::Obj(old_slot)) = row.get("slot") else {
                        return true;
                    };
                    if old_slot.get("field") != Some(&Json::str(field)) {
                        return true;
                    }
                    let Some(old_subject) = old_slot.get("subject") else {
                        return true;
                    };
                    !original
                        .arguments()
                        .iter()
                        .any(|r| r.wire() == *old_subject && g.scalar(*r).ok() == Some(current))
                });
                overrides.insert(
                    slot.canonical(),
                    Json::obj([("slot", slot), ("value", updated.wire())]),
                );
            }
            wire.insert(
                "overrides".into(),
                Json::Arr(overrides.into_values().collect()),
            );
            let object = b.push(
                NodeType::Construction(T::Architecture),
                "architecture",
                original_wire,
                args,
                None,
                None,
            )?;
            let mut args = vec![domain, set, parameters, object, claim];
            args.extend(&conditions);
            let repair = b.push(
                NodeType::Construction(T::Repair),
                "repair",
                Json::obj([
                    ("domain", domain.wire()),
                    ("solutions", set.wire()),
                    ("parameters", parameters.wire()),
                    ("steps", Json::Arr(steps)),
                    ("object", object.wire()),
                    ("rechecks", refs(&conditions)),
                ]),
                args,
                None,
                None,
            )?;
            outputs.insert("repair".into(), repair);
            outputs.insert("object".into(), object);
        } else {
            let reason = Reason {
                location: Some(Location::Law {
                    span: declaration.span,
                }),
                request: request.id.clone(),
                kind: ReasonKind::ConditionFailed {
                    condition: unique,
                    construction: "repair",
                },
                dependencies: vec![unique],
                missing: vec![],
            };
            reasons.push(reason.clone());
            b.parts[claim.0 - base].reasons.push(reason.clone());
            b.parts[claim.0 - base]
                .judgment
                .as_mut()
                .ok_or("repair判断がない")?
                .reasons
                .push(reason);
        }
    }
    let scope = b.parts[claim.0 - base].scope.clone();
    Ok((
        b.parts,
        Answer {
            id: request.id.clone(),
            status,
            outputs,
            claim: Some(claim),
            evidence: vec![certificate],
            reasons,
            scope,
        },
        (search.linear.is_some() || search.rational.is_some()).then_some(search),
    ))
}
pub(super) fn evaluate(
    prepared: &PreparedObserved,
    env: &Environment<'_>,
    g: &mut Graph,
    request: &Request,
    c: &mut Control,
) -> Result<Answer, ValidationFailure> {
    <Data as super::result_kind::ResultKind>::compute_and_retain((prepared, env, g, request, c))
}
pub(super) fn validate_node(
    g: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let Witness::Architecture(w) = &v.witness else {
        return Err("changeの元Architectureがない".into());
    };
    let p = d.part();
    if !Arc::ptr_eq(w, &d.source.architecture.witness)
        || n.ty != p.ty
        || n.rule != Rule::Construction(p.construction)
        || n.arguments != p.arguments
        || n.support != p.support
        || n.scope != p.scope
        || n.reasons != p.reasons
        || n.evidence != p.evidence
        || n.judgment != p.judgment
    {
        return Err("changeの元構成・辺・判断が違う".into());
    }
    for r in &p.arguments {
        g.get(*r)?;
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_change(
        &self,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        let D::Change(d) = &v.data else {
            return Ok(());
        };
        if d.index >= d.source.parts.len()
            || at != d.source.base + d.index
            || d.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("changeの位置・既出参照が違う".into());
        }
        let mut c = self.control.clone();
        d.source.boundary.recheck(self, g, at, &mut c)?;
        if self.change_source_checked(&d.source) {
            return Ok(());
        }
        let origin = Witness::Architecture(d.source.architecture.witness.clone());
        let request = origin.request();
        let (parts, answer, verification) = compute(
            self,
            g,
            &d.source.architecture,
            d.source.base,
            request,
            &mut c,
        )?;
        if let Some(search) = verification {
            for point in 0..search
                .candidates
                .as_ref()
                .map_or(0, |table| table.rows.len())
            {
                change_search::verify_point(
                    self,
                    &d.source.architecture.witness,
                    &search,
                    point,
                    &mut c,
                )?;
            }
        }
        if parts != d.source.parts || answer != d.source.answer {
            return Err("changeの再構成が違う".into());
        }
        self.remember_change_source(d.source.clone());
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
        return if answer == &expected {
            Ok(())
        } else {
            Err("change依存停止が違う".into())
        };
    }
    let r = answer
        .claim
        .or_else(|| {
            answer
                .reasons
                .iter()
                .find_map(|r| r.dependencies.first().copied())
        })
        .ok_or("solveの存在命題・未決の元式がない")?;
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("solveの存在命題がnativeでない".into());
    };
    let D::Change(d) = &v.data else {
        return Err("solveの存在命題が別種".into());
    };
    architecture_result::validate_build_origin(env, g, request, v)?;
    env.recheck_change(g, v, r.0)?;
    if answer != &d.source.answer {
        return Err("solve回答が元全解と違う".into());
    }
    Ok(())
}

pub(super) fn validate_failure(g: &Graph, reason: &Reason) -> Result<(), ValidationFailure> {
    let ReasonKind::ConditionFailed {
        condition,
        construction: "repair",
    } = reason.kind
    else {
        return Err("修復反証が別種".into());
    };
    let n = g.get(condition)?;
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("修復反証がnativeでない".into());
    };
    let D::Change(d) = &v.data else {
        return Err("修復反証が別構成".into());
    };
    if n.judgment.as_ref().map(|j| j.status) != Some(Decision::Refuted)
        || !d.source.answer.reasons.contains(reason)
        || reason.dependencies != [condition]
        || !reason.missing.is_empty()
    {
        return Err("修復反証の元全解が違う".into());
    }
    validate_node(g, n, v, d)
}

pub(super) struct CandidateInput {
    pub architecture: NodeRef,
    pub witness: Arc<native::ArchitectureWitness>,
    pub assignments: Vec<(Fact, Scalar)>,
    pub search: change_search::Search,
    pub domain_type: ProjectionType,
}
pub(super) fn candidate_input(
    env: &Environment<'_>,
    g: &Graph,
    reference: NodeRef,
    c: &mut Control,
) -> Result<CandidateInput, ValidationFailure> {
    let node = g.get(reference)?;
    let Some(Payload::Construction(v)) = &node.payload else {
        return Err("商の候補域がnativeでない".into());
    };
    let D::Change(d) = &v.data else {
        return Err("商の候補域がchange由来でない".into());
    };
    if !matches!(
        d.ty(),
        NodeType::Construction(T::CandidateSpace | T::SolutionSet)
    ) {
        return Err("商の候補域の型が違う".into());
    }
    env.recheck_node(g, node, reference.0)?;
    let origin = Witness::Architecture(d.source.architecture.witness.clone());
    let request = origin.request();
    env.with_request_context(g, request, || {
        let _selected = env.enter_architecture(g)?;
        let assignments = env.state.architecture_values();
        let search = change_search::search(env, g, &d.source.architecture.witness, request, c)
            .map_err(|f| f.cause)?;
        Ok(CandidateInput {
            architecture: d.source.architecture.reference,
            witness: d.source.architecture.witness.clone(),
            assignments,
            search,
            domain_type: d.projection_type().ok_or("商の候補域の公開型がない")?,
        })
    })
}

pub(super) fn architecture_overrides(
    g: &Graph,
    part: &Part,
) -> Result<Vec<(Fact, NodeRef, Scalar)>, ValidationFailure> {
    if part.ty != NodeType::Construction(T::Architecture) {
        return Err("修復対象がArchitectureでない".into());
    }
    let Json::Obj(wire) = &part.wire else {
        return Err("修復対象のrecordがない".into());
    };
    let Some(Json::Arr(rows)) = wire.get("overrides") else {
        return Err("修復対象の更新表がない".into());
    };
    let reference = |wire: &Json| {
        part.arguments
            .iter()
            .copied()
            .find(|r| r.wire() == *wire)
            .ok_or_else(|| ValidationFailure::Internal("更新の型付き辺がない".into()))
    };
    let mut result = vec![];
    for row in rows {
        let Json::Obj(row) = row else {
            return Err("更新recordがない".into());
        };
        let Some(Json::Obj(slot)) = row.get("slot") else {
            return Err("更新slotがない".into());
        };
        let subject = reference(slot.get("subject").ok_or("更新subjectがない")?)?;
        let Some(Json::Str(field)) = slot.get("field") else {
            return Err("更新fieldがない".into());
        };
        let Scalar::Subject {
            snapshot, subject, ..
        } = g.scalar(subject)?
        else {
            return Err("更新subjectが参照でない".into());
        };
        let updated = reference(row.get("value").ok_or("更新値がない")?)?;
        result.push((
            Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: Some(field.clone().into()),
                atom: None,
            },
            updated,
            g.scalar(updated)?.clone(),
        ));
    }
    Ok(result)
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
        let (prepared, env, g, request, c) = input;
        if let Some(answer) = super::public_map::unavailable(env, g, request)? {
            return Ok(answer);
        }
        let _selected = env.enter_architecture(g)?;
        let mut architecture =
            architecture_result::build(prepared.shared_inputs(), env, g, request, c)?;
        let producer = architecture.reference;
        if let Some(reference) = env.state.architecture_ref() {
            architecture.reference = reference;
        }
        let boundary = Boundary::capture(env, g, producer, vec![architecture.reference], c)?;
        let base = g.nodes.len();
        let (parts, answer, verification) = compute(env, g, &architecture, base, request, c)?;
        let source = Arc::new(Source {
            architecture,
            boundary,
            base,
            parts,
            answer,
        });
        let points = verification
            .as_ref()
            .and_then(|s| s.candidates.as_ref())
            .map_or(0, |table| table.rows.len());
        if points > 0 {
            change_search::verify_point(
                env,
                &source.architecture.witness,
                verification.as_ref().unwrap(),
                0,
                c,
            )?;
        }
        let existence = source
            .answer
            .outputs
            .get("existence")
            .or_else(|| source.answer.outputs.get("proposition"))
            .copied()
            .or_else(|| {
                source
                    .answer
                    .reasons
                    .iter()
                    .find_map(|r| r.dependencies.first().copied())
            })
            .ok_or("changeの存在命題・未決の元式がない")?;
        for index in 0..source.parts.len() {
            // 完了済みnative構成の転送だけを行う。停止後に新しい導出はしない。

            let part = &source.parts[index];
            native::retain(
                g,
                ConstructionValue {
                    witness: Witness::Architecture(source.architecture.witness.clone()),
                    data: D::Change(Data {
                        source: source.clone(),
                        index,
                    }),
                },
                part.reasons.clone(),
                part.evidence.clone(),
                part.judgment.clone(),
            )?;
            if base + index == existence.0 && points > 1 {
                for point in 1..points {
                    if let Err(failure) = change_search::verify_point(
                        env,
                        &source.architecture.witness,
                        verification.as_ref().unwrap(),
                        point,
                        c,
                    ) {
                        let ValidationFailure::Stop(reason) = failure else {
                            return Err(failure);
                        };
                        let mut answer = source.answer.clone();
                        if request.kind == QuestionKind::Repair {
                            answer.status = Decision::Undetermined;
                            answer.claim = None;
                            answer.outputs.retain(|key, _| {
                                matches!(key.as_str(), "domain" | "solutions" | "existence")
                            });
                            answer.reasons.clear();
                            answer.scope = source.parts[existence.0 - base].scope.clone();
                        }
                        answer.reasons.push(Reason::stopped(&request.id, reason));
                        return Ok(answer);
                    }
                }
            }
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
        env.recheck_change(graph, value, limit)?;
        Ok(())
    }
}
