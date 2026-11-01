//! 固定観測状態の局所系。支持coverの有限matchingを計算する。
use super::{
    PreparedObserved,
    build_result::{Builder, Part},
    change_result, construction_result as native,
    construction_result::{
        ArchitectureWitness, ConstructionData as D, ConstructionType as T, ConstructionValue,
        Witness,
    },
    environment::{AnswerBinding, Environment, change_search},
    projection::{ProjectionStep, ProjectionType},
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::control::Control;
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
mod comparison;
mod finite;
mod finite_model;
pub(super) mod geometry;
mod integer;
mod rational;
mod rational_finite;
mod rational_geometry;
#[derive(Debug)]
pub(super) struct Source {
    base: usize,
    parts: Vec<Part>,
    scope_domains: Vec<(NodeRef, Type)>,
    answer: Answer,
    request: Request,
    witness: Arc<ArchitectureWitness>,
    system: Option<System>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct System {
    parameters: NodeRef,
    laws: Vec<NodeRef>,
    expression: Option<NodeRef>,
    semantic: NodeRef,
    equation: NodeRef,
    domain: NodeRef,
    inhabited: bool,
    patch_count: usize,
    finite: Option<geometry::Finite>,
    integer: Option<integer::Diagram>,
    rational: Option<rational::Diagram>,
    fixed_positions: Vec<Fact>,
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
    pub(super) fn scope_domain_type(&self) -> Option<&Type> {
        let reference = NodeRef(self.source.base + self.index);
        self.source
            .scope_domains
            .iter()
            .find(|(r, _)| *r == reference)
            .map(|(_, ty)| ty)
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
            NodeType::Construction(T::Cohomology) => Some(ProjectionType::Cohomology),
            NodeType::Construction(T::Class) => Some(ProjectionType::Class),
            NodeType::Construction(T::Module) => Some(ProjectionType::Module),
            NodeType::Construction(T::Ring) => Some(ProjectionType::Ring),
            NodeType::Vector(_) => Some(ProjectionType::Vector),
            NodeType::ModuleMap(_, _) => Some(ProjectionType::ModuleMap),
            NodeType::Construction(T::Comparison) => Some(ProjectionType::Comparison),
            NodeType::Construction(T::Cover) => Some(ProjectionType::Cover),
            NodeType::Construction(T::Topology) => Some(ProjectionType::Topology),
            NodeType::Construction(T::StateMap) => Some(ProjectionType::StateMap),
            NodeType::Construction(T::CandidateSpace) => Some(ProjectionType::FixedCandidateSpace),
            NodeType::Construction(T::StateSpace) => Some(ProjectionType::FixedStateSpace),
            NodeType::Construction(T::EquationSpace) => Some(ProjectionType::EquationSpace),
            NodeType::Domain => Some(ProjectionType::Domain),
            NodeType::Construction(T::SolutionSet) => Some(ProjectionType::FixedSolutionSet),
            NodeType::Construction(T::EquationSolutionSet) => {
                Some(ProjectionType::EquationSolutionSet)
            }
            NodeType::Proposition => Some(ProjectionType::Proposition),
            _ => None,
        }
    }
    pub(super) fn scalar_projection(&self, path: &[ProjectionStep]) -> Option<Scalar> {
        if self.ty() != NodeType::Construction(T::Module) {
            return None;
        }
        let Json::Obj(fields) = &self.part().wire else {
            return None;
        };
        match path {
            [ProjectionStep::Field(field)] if field == "free_rank" => {
                let Json::Nat(rank) = fields.get(field)? else {
                    return None;
                };
                Some(Scalar::Z((*rank).into()))
            }
            [ProjectionStep::Field(field), rest @ ..] if field == "torsion" => {
                let Json::Arr(values) = fields.get(field)? else {
                    return None;
                };
                let values = values
                    .iter()
                    .map(|v| {
                        let Json::Str(value) = v else {
                            return None;
                        };
                        Some(Scalar::Z(value.parse().ok()?))
                    })
                    .collect::<Option<Vec<_>>>()?;
                match rest {
                    [] => Some(Scalar::List {
                        element: Type::Z,
                        items: values,
                    }),
                    [ProjectionStep::Index(i)] => values.get(usize::try_from(*i).ok()?).cloned(),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    pub(super) fn project(&self, path: &[ProjectionStep]) -> Option<(NodeRef, usize)> {
        let ProjectionStep::Field(field) = path.first()? else {
            return None;
        };
        let allowed = match self.ty() {
            NodeType::Construction(T::SolutionSet | T::EquationSolutionSet) => field == "domain",
            NodeType::Construction(T::CandidateSpace) => {
                matches!(field.as_str(), "base" | "parameters" | "states" | "action")
            }
            NodeType::Construction(T::EquationSpace) => {
                matches!(field.as_str(), "base" | "parameters")
            }
            NodeType::Construction(T::LocalSystem) => {
                matches!(field.as_str(), "base" | "cover" | "topology")
            }
            NodeType::Construction(T::Diagnostic) => matches!(
                field.as_str(),
                "system" | "matching" | "global" | "restriction" | "space" | "class"
            ),
            NodeType::Construction(T::Module) => field == "ring",
            NodeType::Vector(_) => field == "module",
            NodeType::Construction(T::Cohomology) => field == "module",
            NodeType::Construction(T::Class) => {
                matches!(field.as_str(), "cohomology" | "coordinates")
            }
            NodeType::Construction(T::Comparison) => matches!(
                field.as_str(),
                "finite_map" | "cohomology_map" | "kernel" | "cokernel" | "class_transport"
            ),
            NodeType::ModuleMap(_, _) => matches!(field.as_str(), "source" | "target"),
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
pub(super) fn domain(
    b: &mut Builder<'_>,
    ty: &Type,
    items: &[NodeRef],
) -> Result<NodeRef, ValidationFailure> {
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
    c: &Control,
) -> Result<Source, ValidationFailure> {
    c.checkpoint(crate::control::Checkpoint::Localize)?;
    env.validation_graph_session(g, || {
        let target = reference(env, g, &request.head)?;
        let Some(Payload::Construction(original)) = &g.get(target)?.payload else {
            return Err("局所系の元構成がない".into());
        };
        let Witness::Architecture(witness) = &original.witness else {
            return Err("局所系の元Architectureがない".into());
        };
        if request.kind == QuestionKind::Compare {
            return comparison::compute(env,g,request,target,base,witness.clone(),c);
        }
        if request.kind == QuestionKind::Diagnose {
            return diagnose(env, g, request, target, original, base, witness.clone(), c);
        }
        if let Some(name) = request.arguments.iter().find_map(|a| match (&*a.name, &a.value) {
            ("using", Selector::Declaration { name }) => Some(name), _ => None,
        }) {
            if matches!(&env.indexes.inputs.law().declarations()[name].signature, Signature::Change { params, .. } if params.iter().skip(1).any(|p| p.ty == Type::Z)) {
                return integer::compute(env, g, request, target, original, base, witness.clone(), c);
            }
            if matches!(&env.indexes.inputs.law().declarations()[name].signature, Signature::Change { params, .. } if params.iter().skip(1).any(|p| p.ty == Type::Q)) {
                return rational::compute(env, g, request, target, original, base, witness.clone(), c);
            }
            return finite::compute(env, g, request, target, original, base, witness.clone(), c);
        }
        let reading = witness.construction().reading();
        let locals = env
            .indexes.inputs
            .law()
            .declarations()
            .values()
            .filter(|d| d.reading == reading && matches!(d.signature, Signature::Local { .. }))
            .collect::<Vec<_>>();
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
            env.indexes.inputs
                .law()
                .declarations()
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
        let assignments = match &original.data {
            D::Change(d) => d.overrides(g)?,
            D::Quotient(d) => d.overrides(g)?,
            _ => vec![],
        }
        .into_iter()
        .map(|(f, _, v)| (f, v))
        .collect::<Vec<_>>();
        let mut fixed = Environment::try_primitive_valuation(env.indexes.inputs, &assignments, c)?
            .ok_or("固定Architectureの値が不適合")?;
        fixed.select_local_object(witness, c)?;
        let mut evaluations = vec![];
        for name in &names {
            let declaration = &env.indexes.inputs.law().declarations()[name];
            if declaration.reading != reading {
                return Err(unsupported("対象Architectureと局所Lawのreadingが異なる"));
            }
            let Signature::Law {
                params,
                guard,
                body,
                ..
            } = &declaration.signature
            else {
                return Err("局所系の指定宣言がLawでない".into());
            };
            let mut reading_roots = match env.indexes.inputs.law().exprs()[*body].kind {
                ExprKind::Binary {
                    op: BinOp::Eq,
                    lhs,
                    rhs,
                } => vec![lhs, rhs],
                _ => vec![*body],
            };
            reading_roots.extend(*guard);
            let mut assignments = vec![vec![]];
            let mut universal = vec![];
            let mut domain_missing = vec![];
            for p in params {
                let values = if let Some(a) = request
                    .arguments
                    .iter()
                    .find(|a| a.name == format!("bind.{}", p.name))
                {
                    vec![change_search::selector(env, g, &a.value)?]
                } else {
                    if matches!(p.ty.erase(), Type::Z | Type::Q) {
                        universal.push((p, None));
                        continue;
                    }
                    let Some(values) =
                        change_search::domain(&fixed, &p.ty, p.span, &mut domain_missing)?
                    else {
                        return Err(unsupported("局所Lawのparameter域が未確定"));
                    };
                    universal.push((p, Some(values.clone())));
                    values
                };
                let mut next = vec![];
                for bindings in assignments {
                    for value in &values {
                        c.checkpoint(crate::control::Checkpoint::Localize)?;
                        let mut row = bindings.clone();
                        row.push((p.name.clone(), value.clone()));
                        next.push(row);
                    }
                }
                assignments = next;
            }
            for bindings in assignments {
                let mut missing = domain_missing.clone();
                let mut carrier = bindings
                    .iter()
                    .filter(|(_, v)| matches!(v, Scalar::Subject { .. }))
                    .map(|(_, v)| Json::obj([("type", v.ty().wire()), ("value", v.wire())]))
                    .collect::<Vec<_>>();
                let (row, read_missing, evaluated) = fixed.local_point(declaration, &bindings)?;
                for fact in &row.support {
                    let subject = env.indexes.subject(&fact.snapshot, &fact.subject)?;
                    let v = Scalar::Subject {
                        snapshot: fact.snapshot.clone(),
                        subject: fact.subject.clone(),
                        entity: subject.ty.to_string(),
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

                missing.extend(read_missing);
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
                evaluations.push((
                    declaration,
                    bindings,
                    universal.clone(),
                    row,
                    missing,
                    evaluated,
                    carrier,
                    positions,
                    reading_roots.clone(),
                ));
            }
        }
        let mut b = Builder {
            g,
            base,
            parts: vec![],
        };
        let mut scope_domains = vec![];
        let mut parameter_domains = BTreeMap::new();
        let mut laws = vec![];
        let mut expressions = vec![];
        let mut reasons = vec![];
        let mut inhabited = true;
        let mut common: (Vec<Json>, Vec<Fact>) = (vec![], vec![]);
        let mut readings = vec![];
        let mut reading_refs = vec![];
        let mut projections = vec![];
        let mut patches = vec![];
        let mut read_supports = vec![];
        let mut truth = vec![];
        let mut retained = std::collections::BTreeSet::new();
        for (
            declaration,
            bindings,
            universal,
            row,
            mut missing,
            evaluated,
            carrier,
            positions,
            reading_roots,
        ) in evaluations
        {
            let Signature::Law {
                role, body, guard, params, ..
            } = &declaration.signature
            else {
                return Err("局所系の指定宣言がLawでない".into());
            };
            let parameters = params.iter().filter(|p| !bindings.iter().any(|(n, _)| *n == p.name)).cloned().collect::<Vec<_>>();
            let typed_parameters = parameters.iter().map(|p| (p.name.clone(), p.ty.erase())).collect::<Vec<_>>();
            let mut law_support = geometry::Support {
                carrier: carrier.clone(), positions: positions.clone(), visible: positions.clone(),
            };
            if !locals.is_empty() && missing.is_empty() {
                let roots = std::iter::once(*body).chain(guard.iter().copied()).collect::<Vec<_>>();
                if let Some((carrier, visible)) = super::environment::local_read::fixed_chain_visibility(
                    &fixed, &roots, &bindings, &parameters, reading, c,
                )? {
                    law_support.carrier = carrier;
                    law_support.visible = visible;
                }
            }
            patches.push(law_support);
            common.0.extend(carrier);
            common.0.sort_by_key(Json::canonical);
            common.0.dedup();
            common.1.extend(positions);
            common.1.sort();
            common.1.dedup();
            let bindings = bindings
                .iter()
                .map(|(n, v)| Ok((n.clone(), change_result::value(&mut b, v)?)))
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            let mut quantifiers = vec![];
            for (p, values) in universal {
                let domain = if let Some(values) = values {
                    let key = (declaration.name.clone(), p.name.clone());
                    let domain = if let Some(reference) = parameter_domains.get(&key) {
                        *reference
                    } else {
                        let items = values
                            .iter()
                            .map(|v| change_result::value(&mut b, v))
                            .collect::<Result<Vec<_>, _>>()?;
                        let reference = domain(&mut b, &p.ty.erase(), &items)?;
                        scope_domains.push((reference, p.ty.erase()));
                        parameter_domains.insert(key, reference);
                        reference
                    };
                    Some(domain)
                } else {
                    None
                };
                quantifiers.push(Quantifier {
                    kind: crate::law::ast::QuantKind::Forall,
                    name: p.name.clone(),
                    ty: p.ty.erase(),
                    domain,
                    occurrence: p.span,
                    context: Some(env.current_context(g)),
                });
            }
            let guard_expression = guard
                .map(|id| change_result::source_expression(&mut b, env, id, &bindings, &typed_parameters))
                .transpose()?;
            let expression = change_result::source_expression(&mut b, env, *body, &bindings, &typed_parameters)?;
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
            if let Some(reference) = guard_expression {
                b.parts[expression.0 - base].arguments.push(reference);
            }
            let known = row.application == Some(true)
                && !row.condition_failed
                && !row.condition_pending
                && (row.guard == Some(false)
                    || (row.guard == Some(true) && row.predicate.is_some()))
                && missing.is_empty();
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
                reasons.push(reason);
                expressions.push(expression);
                continue;
            }
            truth.push(row.guard == Some(false) || row.predicate == Some(true));
            inhabited &= row.guard == Some(false) || row.predicate == Some(true);
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
                                .map(|(n, r)| {
                                    Json::obj([("name", Json::str(n)), ("value", r.wire())])
                                })
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
            if let Some(guard) = guard_expression {
                let part = &mut b.parts[law.0 - base];
                if let Json::Obj(wire) = &mut part.wire {
                    wire.insert("guard".into(), guard.wire());
                }
                part.arguments.push(guard);
            }
            laws.push(law);
            expressions.push(expression);
            for read in evaluated
                .into_iter()
                .filter(|_| locals.is_empty())
                .filter(|n| {
                    reading_roots.contains(&n.expression)
                        || match &env.indexes.inputs.law().exprs()[n.expression].kind {
                            ExprKind::Field { .. } => true,
                            ExprKind::Dotted(parts) => {
                                parts.len() > 1
                                    && n.bindings.iter().any(|(name, _)| *name == parts[0].name)
                            }
                            _ => false,
                        }
                })
            {
                let Some(value) = read.value else {
                    if parameters.is_empty() {
                        return Err("確定した局所読取りの値がない".into());
                    }
                    continue;
                };
                let bs = read
                    .bindings
                    .iter()
                    .map(|(n, v)| Ok((n.clone(), change_result::value(&mut b, v)?)))
                    .collect::<Result<Vec<_>, ValidationFailure>>()?;
                let key = (read.expression, bs.iter().map(|(name, reference)| (name.clone(), reference.0)).collect::<Vec<_>>());
                if !retained.insert(key) {
                    continue;
                }
                let (read_carrier, read_positions) =
                    super::environment::local_read::implicit_support_with_parameters(
                        &fixed,
                        read.expression,
                        &read.bindings,
                        &parameters,
                        reading,
                        c,
                    )?;
                read_supports.push(geometry::Support {
                    carrier: read_carrier,
                    positions: read_positions.clone(),
                    visible: read_positions,
                });
                let expr =
                    change_result::source_expression(&mut b, env, read.expression, &bs, &typed_parameters)?;
                let actual = change_result::value(&mut b, &value)?;
                let image = domain(&mut b, &value.ty(), &[actual])?;
                readings.push(Json::obj([
                    ("expression", expr.wire()),
                    ("type", value.ty().wire()),
                    ("domain", image.wire()),
                ]));
                reading_refs.extend([expr, image]);
            }
        }
        let (mut carrier, mut positions) = common;
        let law_supports = patches.clone();
        let mut visible = positions.clone();
        let mut local_instances = vec![];
        let mut local_scope = Scope::default();
        if !locals.is_empty() {
            carrier.clear();
            positions.clear();
            visible.clear();
            patches.clear();
            readings.clear();
            read_supports.clear();
            reading_refs.clear();
            'local_instances: for declaration in &locals {
                for explicit in super::environment::local_read::materialize(
                    &fixed,
                    &mut b,
                    declaration,
                    request,
                    &expressions,
                    &[],
                    c,
                )? {
                    local_scope.merge(&explicit.scope);
                    let stopped = explicit.reasons.iter().any(|r| matches!(r.kind, ReasonKind::Stop(_)));
                    reasons.extend(explicit.reasons);
                    if stopped { break 'local_instances; }
                    if explicit.locals.is_empty() {
                        continue;
                    }
                    let support = geometry::Support {
                        carrier: explicit.carrier,
                        positions: explicit.positions,
                        visible: explicit.visible,
                    };
                    carrier.extend(support.carrier.iter().cloned());
                    positions.extend(support.positions.iter().cloned());
                    visible.extend(support.visible.iter().cloned());
                    projections.extend(explicit.projections.into_iter().map(|mut p| {
                        p.read += readings.len();
                        p
                    }));
                    readings.extend(explicit.readings);
                    read_supports.extend(explicit.read_supports);
                    reading_refs.extend(explicit.read_refs);
                    patches.push(support.clone());
                    local_instances.push(geometry::Local {
                        support,
                        instances: explicit.locals,
                        arguments: explicit.arguments,
                    });
                }
            }
            carrier.sort_by_key(Json::canonical);
            carrier.dedup();
            positions.sort();
            positions.dedup();
            visible.sort();
            visible.dedup();
            if reasons.is_empty()
                && law_supports
                    .iter()
                    .any(|law| !patches.iter().any(|patch| patch.contains(law)))
            {
                reasons.push(Reason {
                    kind: ReasonKind::VisibilityInsufficient {
                        locals: locals.iter().map(|d| d.name.clone()).collect(),
                        coordinates: expressions.clone(),
                    },
                    request: request.id.clone(),
                    dependencies: expressions.clone(),
                    missing: vec![],
                    location: None,
                });
            }
        }
        if !reasons.is_empty() {
            let mut scope = local_scope;
            for expression in &expressions {
                scope.merge(&b.parts[expression.0 - base].scope);
            }
            return Ok(Source {
                base,
                parts: b.parts,
                scope_domains,
                answer: Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons,
                    scope,
                },
                request: request.clone(),
                witness: witness.clone(),
                system: None,
            });
        }
        let mut fixed_positions = positions.clone();
        for reference in &carrier {
            let Json::Obj(reference) = reference else {
                return Err("局所carrierが参照でない".into());
            };
            let Some(Json::Arr(value)) = reference.get("value") else {
                return Err("局所carrierの値がない".into());
            };
            let [Json::Str(snapshot), Json::Str(subject)] = value.as_slice() else {
                return Err("局所carrierが原始参照でない".into());
            };
            fixed_positions.push(Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: None,
                atom: None,
            });
        }
        let expression = expressions.first().copied();
        let built = match geometry::build(
            env,
            &mut b,
            target,
            &laws,
            &truth,
            &patches,
            &law_supports,
            geometry::Support {
                carrier,
                positions,
                visible,
            },
            &readings,
            &read_supports,
            &reading_refs,
            &projections,
            &local_instances,
            None,
            None,
            &local_scope,
            c,
        ) {
            Ok(built) => built,
            Err(ValidationFailure::Stop(stop)) => {
                // 完成済みの型付き断片だけを転送し、未完成のLocalSystemを公開しない。
                let mut reason = Reason::stopped(&request.id, stop);
                let mut scope = Scope::default();
                for (index, part) in b.parts.iter().enumerate() {
                    scope.merge(&part.scope);
                    if matches!(
                        part.ty,
                        NodeType::Construction(
                            T::Context | T::ContextMap | T::Overlap | T::Cover | T::Topology
                        )
                    ) {
                        reason.dependencies.push(NodeRef(base + index));
                    }
                }
                return Ok(Source {
                    base,
                    parts: b.parts,
                    scope_domains,
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
            Err(failure) => return Err(failure),
        };
        let geometry::Built {
            integer,
            finite,
            system,
            adequacy,
            point,
            semantic,
            equation,
            states,
            patch_count,
        } = built;
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
            scope_domains,
            answer,
            request: request.clone(),
            witness: witness.clone(),
            system: Some(System {
                parameters: point,
                laws,
                expression,
                semantic,
                equation,
                domain: states,
                inhabited,
                patch_count,
                finite,
                integer,
                rational: None,
                fixed_positions,
            }),
        })
    })
}
fn diagnose(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    target: NodeRef,
    original: &ConstructionValue,
    base: usize,
    witness: Arc<ArchitectureWitness>,
    c: &Control,
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
    if let Some(diagram) = &system.integer {
        let semantic = request.arguments.iter().any(|a| {
            a.name == "side" && matches!(&a.value,Selector::Enum{value} if value=="semantic")
        });
        if !diagram.equation_only || !semantic {
            return integer::diagnose(env, g, request, target, base, witness, diagram, degree, c);
        }
    }
    if let Some(diagram) = &system.rational {
        let semantic = request.arguments.iter().any(|a| {
            a.name == "side" && matches!(&a.value,Selector::Enum{value} if value=="semantic")
        });
        if !diagram.equation_only || !semantic {
            return rational::diagnose(env, g, request, target, base, witness, diagram, degree, c);
        }
    }
    if degree > 1 {
        let mut b = Builder {
            g,
            base,
            parts: vec![],
        };
        let (dependencies, scope) = if let Some(expression) = system.expression {
            let original = &data.source.parts[expression.0 - data.source.base];
            let expression = b.push(
                original.ty.clone(),
                original.construction,
                original.wire.clone(),
                original.arguments.iter().copied().chain([target]).collect(),
                None,
                None,
            )?;
            (vec![expression], b.parts[0].scope.clone())
        } else {
            (vec![target], g.get(target)?.scope.clone())
        };
        let reason = Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: QuestionKind::Diagnose,
                operand_types: vec![Type::Bool],
                method: "finite_matching_degree".into(),
            },
            request: request.id.clone(),
            dependencies,
            missing: vec![],
            location: None,
        };
        if let Some(part) = b.parts.first_mut() {
            part.reasons.push(reason.clone());
        }
        let answer = Answer {
            id: request.id.clone(),
            status: Decision::Undetermined,
            outputs: BTreeMap::new(),
            claim: None,
            evidence: vec![],
            reasons: vec![reason],
            scope,
        };
        return Ok(Source {
            base,
            parts: b.parts,
            scope_domains: vec![],
            answer,
            request: request.clone(),
            witness,
            system: None,
        });
    }
    if let Some(finite) = &system.finite {
        return finite::diagnose(
            g,
            request,
            target,
            base,
            witness,
            finite,
            &system.laws,
            degree,
            c,
        );
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
    let tuple = change_result::value(
        &mut b,
        &Scalar::Tuple(vec![Scalar::Unit; system.patch_count]),
    )?;
    let matching = domain(
        &mut b,
        &Type::Tuple(vec![Type::Unit; system.patch_count]),
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
    let mut evidence = vec![];
    if degree == 1 && !system.inhabited {
        evidence.push(
            b.push(
                NodeType::Evidence,
                "evidence",
                Json::obj([
                    ("kind", Json::str("finite_exhaustion")),
                    (
                        "data",
                        Json::obj([
                            ("domain", system.parameters.wire()),
                            ("checked", Json::Nat(1)),
                            ("instances", refs(&system.laws)),
                        ]),
                    ),
                ]),
                [system.parameters, global]
                    .into_iter()
                    .chain(system.laws.iter().copied())
                    .collect(),
                None,
                None,
            )?,
        );
    }
    let status = if degree == 0 || system.inhabited {
        Decision::Established
    } else {
        Decision::Refuted
    };
    let mut outputs = BTreeMap::from([("diagnostic".into(), diagnostic)]);
    let claim = if degree == 1 {
        let proposition = b.proposition(
            "inhabited",
            vec![global],
            std::iter::once(diagnostic)
                .chain(evidence.iter().copied())
                .collect(),
            status,
        )?;
        b.parts[proposition.0 - base]
            .judgment
            .as_mut()
            .ok_or("診断の判断がない")?
            .evidence = evidence.clone();
        outputs.insert("proposition".into(), proposition);
        Some(proposition)
    } else {
        None
    };
    let answer = Answer {
        id: request.id.clone(),
        status,
        outputs,
        claim,
        evidence,
        reasons: vec![],
        scope: b.parts[diagnostic.0 - base].scope.clone(),
    };
    Ok(Source {
        base,
        parts: b.parts,
        scope_domains: vec![],
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
    c: &Control,
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
                &self.control.clone(),
            )
        })?;
        if let Some(stop) = rebuilt.answer.reasons.iter().find_map(|r| {
            if let ReasonKind::Stop(stop) = &r.kind {
                Some(*stop)
            } else {
                None
            }
        }) {
            return Err(ValidationFailure::Stop(stop));
        }
        if d.source
            .answer
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Stop(_)))
        {
            if rebuilt.scope_domains != d.source.scope_domains
                || !rebuilt.parts.starts_with(&d.source.parts)
                || d.source.system.is_some()
                || d.source.answer.status != Decision::Undetermined
                || !d.source.answer.outputs.is_empty()
                || d.source.answer.claim.is_some()
            {
                return Err("局所系の停止断片の再構成が違う".into());
            }
            self.remember_local_source(d.source.clone());
            return Ok(());
        }
        if rebuilt.scope_domains != d.source.scope_domains
            || rebuilt.parts != d.source.parts
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
        .or_else(|| answer.outputs.get("comparison"))
        .or_else(|| {
            answer
                .reasons
                .iter()
                .find(|r| {
                    matches!(
                        r.kind,
                        ReasonKind::Missing
                            | ReasonKind::UnsupportedAlgorithm { .. }
                            | ReasonKind::VisibilityInsufficient { .. }
                            | ReasonKind::Stop(_)
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
    if &d.source.request != request {
        let rebuilt = env.with_request_context(g, request, || {
            compute(env, g, request, g.nodes.len(), &env.control.clone())
        })?;
        if let Some(stop) = rebuilt.answer.reasons.iter().find_map(|r| {
            if let ReasonKind::Stop(stop) = &r.kind {
                Some(*stop)
            } else {
                None
            }
        }) {
            return Err(ValidationFailure::Stop(stop));
        }
        return if rebuilt.parts.is_empty() && rebuilt.answer == *answer {
            Ok(())
        } else {
            Err("局所系のノードを生成しない回答の再計算が違う".into())
        };
    }
    if &d.source.answer != answer {
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
        || v.witness.inputs().sources() != env.indexes.inputs.sources()
    {
        return Err("局所系が現在の入力・Requestに属さない".into());
    }
    Ok(())
}

impl super::result_kind::ResultKind for Data {
    type Input<'a, 'input: 'a> = (
        &'a PreparedObserved,
        &'a Environment<'input>,
        &'a mut Graph,
        &'a Request,
        &'a Control,
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
        env.recheck_local(graph, value, limit)?;
        Ok(())
    }
}
