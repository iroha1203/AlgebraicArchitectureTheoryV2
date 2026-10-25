//! 整数アフィン局所状態。可視Lawだけを各局所の自由状態へ課す。
use super::*;
use crate::observed::environment::{change_affine, local_read};
use crate::observed::integer_fiber::{self, Matrix};
use num_bigint::BigInt as Z;
use num_traits::Zero;
#[path = "local_integer_cech.rs"]
mod cech;
#[path = "local_integer_linear.rs"]
mod linear;
#[path = "local_integer_state.rs"]
mod state;
pub(super) use cech::diagnose;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Diagram {
    pub slots: Vec<Fact>,
    pub free: Vec<Vec<usize>>,
    pub patches: Vec<usize>,
    pub intersections: Vec<Vec<usize>>,
    pub equation: Vec<linear::Fiber>,
    pub semantic: Vec<linear::Fiber>,
    pub restrictions: BTreeMap<(usize, usize), (Matrix, Matrix)>,
    pub contexts: Vec<NodeRef>,
    pub cover: NodeRef,
    pub solutions: Vec<[NodeRef; 2]>,
    pub missing: Vec<Fact>,
    pub requirements: Vec<(String, Vec<(String, Scalar)>)>,
    pub law_refs: Vec<NodeRef>,
    pub assignments: Vec<(Fact, Scalar)>,
    pub sheaf_conditions: Vec<NodeRef>,
}
struct Model {
    change: String,
    bindings: Vec<(String, Scalar)>,
    instances: Vec<(Scalar, Vec<usize>)>,
    action: change_affine::Linear,
    requirements: Vec<(String, Vec<(String, Scalar)>)>,
    laws: Vec<(Matrix, Vec<Option<Z>>)>,
    supports: Vec<geometry::Support>,
    scope: Scope,
    missing: Vec<Fact>,
}
fn analyze(
    env: &Environment<'_>,
    g: &Graph,
    witness: &ArchitectureWitness,
    request: &Request,
    c: &mut Control,
    pending: &mut change_affine::Pending,
) -> Result<Model, ValidationFailure> {
    let name = request
        .arguments
        .iter()
        .find_map(|a| match (&*a.name, &a.value) {
            ("using", Selector::Declaration { name }) => Some(name),
            _ => None,
        })
        .ok_or("整数局所changeがない")?;
    let change = &env.inputs.law().declarations[name];
    let Signature::Change { params, body, .. } = &change.signature else {
        return Err("整数局所changeの署名がない".into());
    };
    let reading = witness.construction().reading();
    if change.reading != reading {
        return Err(unsupported("整数局所changeのreadingが異なる"));
    }
    let first = params.first().ok_or("整数changeの対象引数がない")?;
    let mut missing = vec![];
    let mut subjects = change_search::domain(env, &first.ty, first.span, &mut missing)?
        .ok_or_else(|| {
            pending.facts.extend(missing.iter().cloned());
            pending.expression = Some(*body);
            pending.parameters = params
                .iter()
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect();
            unsupported("整数局所changeの対象域が未確定")
        })?;
    let construction = witness.construction();
    subjects.retain(|v| match v {
        Scalar::Subject {
            snapshot, subject, ..
        } => std::iter::once(construction.root())
            .chain(construction.local_domain().known())
            .any(|f| f.snapshot == *snapshot && f.subject == *subject),
        _ => false,
    });
    let action = change_affine::compute(env, change, &subjects, &[], pending)?;
    let mut requirements = vec![];
    for law in env.inputs.law().declarations.values().filter(|d| {
        d.reading == reading
            && request.declaration().map_or(
                matches!(
                    d.signature,
                    Signature::Law {
                        role: crate::law::ast::Role::Required,
                        ..
                    }
                ),
                |name| d.name == name,
            )
    }) {
        let Signature::Law { params, body, .. } = &law.signature else {
            return Err("整数局所Lawの署名がない".into());
        };
        let mut rows = vec![vec![]];
        for p in params {
            let values = if let Some(a) = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
            {
                vec![change_search::selector(env, g, &a.value)?]
            } else {
                change_search::domain(env, &p.ty, p.span, &mut missing)?.ok_or_else(|| {
                    pending.facts.extend(missing.iter().cloned());
                    pending.expression = Some(*body);
                    pending.parameters = params
                        .iter()
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect();
                    pending.bindings.clear();
                    unsupported("整数局所Lawの対象域が未確定")
                })?
            };
            let mut next = vec![];
            for row in rows {
                for value in &values {
                    c.checkpoint(super::super::control::Checkpoint::Localize)?;
                    let mut r = row.clone();
                    r.push((p.name.clone(), value.clone()));
                    next.push(r);
                }
            }
            rows = next;
        }
        requirements.extend(rows.into_iter().map(|row| (law.name.clone(), row)));
    }
    let mut laws = vec![];
    let mut supports = vec![];
    let mut scope = Scope::default();
    for (name, bindings) in &requirements {
        let declaration = &env.inputs.law().declarations[name];
        let Signature::Law { body, guard, .. } = &declaration.signature else {
            return Err("整数局所Lawでない".into());
        };
        pending.expression = Some(*body);
        pending.bindings = bindings.clone();
        pending.parameters.clear();
        let (row, absent, _) = env.local_point(declaration, bindings)?;
        missing.extend(absent);
        pending.facts.extend(missing.iter().cloned());
        scope.merge(&row.scope);
        let roots = std::iter::once(*body)
            .chain(guard.iter().copied())
            .collect::<Vec<_>>();
        let (carrier, visible) =
            local_read::state_visibility(env, &roots, bindings, reading, c)?
                .ok_or_else(|| unsupported("整数局所Lawの読取り座標の因子分解は未実装"))?;
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
        supports.push(geometry::Support {
            carrier,
            positions,
            visible,
        });
        laws.push(change_affine::state_equations(
            env,
            &action.slots,
            &[(name.clone(), bindings.clone())],
            pending,
        )?);
    }
    missing.extend(pending.facts.iter().cloned());
    missing.sort();
    missing.dedup();
    let instances = subjects
        .into_iter()
        .enumerate()
        .map(|(i, subject)| {
            (
                subject,
                (i * (params.len() - 1)..(i + 1) * (params.len() - 1)).collect(),
            )
        })
        .collect();
    let bindings = request
        .arguments
        .iter()
        .filter_map(|a| a.name.strip_prefix("bind.").map(|n| (n, a)))
        .map(|(n, a)| Ok((n.to_owned(), change_search::selector(env, g, &a.value)?)))
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    Ok(Model {
        change: change.name.clone(),
        bindings,
        instances,
        action,
        requirements,
        laws,
        supports,
        scope,
        missing,
    })
}

fn fibers(
    model: &Model,
    supports: &[geometry::Support],
    c: &Control,
) -> Result<(Vec<Vec<usize>>, Vec<linear::Fiber>, Vec<linear::Fiber>), ValidationFailure> {
    let mut free = vec![];
    let mut equation = vec![];
    let mut semantic = vec![];
    for support in supports {
        c.clone()
            .checkpoint(super::super::control::Checkpoint::Localize)?;
        let positions = model
            .action
            .slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| support.visible.contains(slot))
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        let mut d = vec![];
        let mut rhs = vec![];
        for (i, law_support) in model.supports.iter().enumerate() {
            if !support.contains(law_support) {
                continue;
            }
            for row in &model.laws[i].0 {
                if row
                    .iter()
                    .enumerate()
                    .any(|(j, x)| !x.is_zero() && !positions.contains(&j))
                {
                    return Err("局所Lawが可視座標を通じて因子分解しない".into());
                }
                d.push(positions.iter().map(|j| row[*j].clone()).collect());
            }
            rhs.extend(model.laws[i].1.iter().cloned());
        }
        let eq = linear::solve_partial(&d, positions.len(), &rhs, c)?;
        let action = linear::project(&model.action.action, &positions);
        let offset = positions
            .iter()
            .map(|i| model.action.offset[*i].clone())
            .collect::<Vec<_>>();
        let mut da = integer_fiber::multiply(&d, &action, model.action.parameter_count, c)?;
        let shift = linear::apply(&d, &offset, c)?;
        let mut shifted = rhs
            .iter()
            .zip(shift)
            .map(|(x, y)| x.as_ref().map(|x| x - y))
            .collect::<Vec<_>>();
        parameter_guards(model, &mut da, &mut shifted);
        let parameters = linear::solve_partial(&da, model.action.parameter_count, &shifted, c)?;
        let sem = linear::affine_image(&parameters, &action, &offset, c)?;
        free.push(positions);
        equation.push(eq);
        semantic.push(sem);
    }
    Ok((free, equation, semantic))
}

fn parameter_guards(model: &Model, matrix: &mut Matrix, rhs: &mut Vec<Option<Z>>) {
    if let Some(guard) = &model.action.guard {
        matrix.extend(guard.equations.iter().cloned());
        rhs.extend(guard.rhs.iter().cloned().map(Some));
    } else if model.action.candidates_empty {
        matrix.extend(model.action.equations.iter().cloned());
        rhs.extend(model.action.rhs.iter().cloned().map(Some));
    }
}

pub(super) fn compute(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    target: NodeRef,
    original: &ConstructionValue,
    base: usize,
    witness: Arc<ArchitectureWitness>,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    let assignments = match &original.data {
        D::Change(d) => d.overrides(g)?,
        D::Quotient(d) => d.overrides(g)?,
        _ => vec![],
    }
    .into_iter()
    .map(|(f, _, v)| (f, v))
    .collect::<Vec<_>>();
    let mut fixed = Environment::try_primitive_valuation(env.inputs, &assignments, c)?
        .ok_or("整数局所系の元代入が不適合")?;
    fixed.select_local_object(&witness, c)?;
    let mut pending = change_affine::Pending::default();
    let result = analyze(&fixed, g, &witness, request, c, &mut pending);
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let mut model = match result {
        Ok(model) => model,
        Err(ValidationFailure::UnsupportedExpression { location, .. })
            if !pending.facts.is_empty() =>
        {
            let id = pending.expression.ok_or("整数局所欠測の原式がない")?;
            let bindings = pending
                .bindings
                .iter()
                .map(|(n, v)| Ok((n.clone(), change_result::value(&mut b, v)?)))
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            let expression =
                change_result::source_expression(&mut b, env, id, &bindings, &pending.parameters)?;
            b.parts[expression.0 - base].arguments.push(target);
            pending.facts.sort();
            pending.facts.dedup();
            let reason = Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: vec![expression],
                missing: pending.facts,
                location: Some(location),
            };
            b.parts[expression.0 - base].reasons.push(reason.clone());
            let scope = b.parts[expression.0 - base].scope.clone();
            return Ok(Source {
                base,
                parts: b.parts,
                scope_domains: vec![],
                request: request.clone(),
                witness,
                system: None,
                answer: Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons: vec![reason],
                    scope,
                },
            });
        }
        Err(error) => return Err(error),
    };
    model.scope.merge(&g.get(target)?.scope);
    let saved_witness = witness.clone();
    let result = (|| -> Result<Source, ValidationFailure> {
        let mut laws = vec![];
        let mut expressions = vec![];
        for (name, bindings) in &model.requirements {
            let declaration = &env.inputs.law().declarations[name];
            let Signature::Law {
                body, guard, role, ..
            } = declaration.signature
            else {
                return Err("整数局所Lawの署名がない".into());
            };
            let bindings = bindings
                .iter()
                .map(|(n, v)| Ok((n.clone(), change_result::value(&mut b, v)?)))
                .collect::<Result<Vec<_>, ValidationFailure>>()?;
            let expression = change_result::source_expression(&mut b, env, body, &bindings, &[])?;
            b.parts[expression.0 - base].scope.merge(&model.scope);
            expressions.push(expression);
            let guard = guard
                .map(|id| change_result::source_expression(&mut b, env, id, &bindings, &[]))
                .transpose()?;
            let mut fields = BTreeMap::from([
                ("name".into(), Json::str(name)),
                (
                    "role".into(),
                    Json::str(if role == crate::law::ast::Role::Required {
                        "required"
                    } else {
                        "optional"
                    }),
                ),
                (
                    "occurrence".into(),
                    crate::result::location_wire(&Location::Law {
                        span: declaration.span,
                    }),
                ),
                (
                    "bindings".into(),
                    Json::Arr(
                        bindings
                            .iter()
                            .map(|(n, r)| Json::obj([("name", Json::str(n)), ("value", r.wire())]))
                            .collect(),
                    ),
                ),
                ("body".into(), expression.wire()),
            ]);
            if let Some(guard) = guard {
                fields.insert("guard".into(), guard.wire());
            }
            laws.push(
                b.push(
                    NodeType::LawInstance,
                    "law_instance",
                    Json::Obj(fields),
                    std::iter::once(expression)
                        .chain(guard)
                        .chain(bindings.iter().map(|(_, r)| *r))
                        .collect(),
                    None,
                    None,
                )?,
            );
        }
        if expressions.is_empty() {
            let declaration = &env.inputs.law().declarations[&model.change];
            let Signature::Change { body, params, .. } = &declaration.signature else {
                return Err("change署名がない".into());
            };
            expressions.push(change_result::source_expression(
                &mut b,
                env,
                *body,
                &[],
                &params
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.clone()))
                    .collect::<Vec<_>>(),
            )?);
        }
        let locals = env
            .inputs
            .law()
            .declarations
            .values()
            .filter(|d| {
                d.reading == witness.construction().reading()
                    && matches!(d.signature, Signature::Local { .. })
            })
            .collect::<Vec<_>>();
        let implicit = locals.is_empty();
        let local_names = locals.iter().map(|d| d.name.clone()).collect::<Vec<_>>();
        let mut explicit = vec![];
        if implicit {
            let mut supports = model.supports.clone();
            for support in &mut supports {
                support.visible = support.positions.clone();
                for slot in &support.positions {
                    let subject = fixed.subject(&slot.snapshot, &slot.subject)?;
                    let value = Scalar::Subject {
                        snapshot: slot.snapshot.clone(),
                        subject: slot.subject.clone(),
                        entity: subject.ty.clone(),
                    };
                    support.carrier.push(Json::obj([
                        ("type", value.ty().wire()),
                        ("value", value.wire()),
                    ]));
                }
                support.carrier.sort_by_key(Json::canonical);
                support.carrier.dedup();
            }
            for slot in &model.action.slots {
                if supports.iter().any(|s| s.positions.contains(slot)) {
                    continue;
                }
                let subject = fixed.subject(&slot.snapshot, &slot.subject)?;
                let value = Scalar::Subject {
                    snapshot: slot.snapshot.clone(),
                    subject: slot.subject.clone(),
                    entity: subject.ty.clone(),
                };
                supports.push(geometry::Support {
                    carrier: vec![Json::obj([
                        ("type", value.ty().wire()),
                        ("value", value.wire()),
                    ])],
                    positions: vec![slot.clone()],
                    visible: vec![slot.clone()],
                });
            }
            for support in supports {
                explicit.push(local_read::materialize_positions(
                    &fixed,
                    &mut b,
                    request,
                    &support,
                    &model.action.slots,
                    witness.construction().reading(),
                    c,
                )?);
            }
        }
        for declaration in locals {
            explicit.extend(local_read::materialize_with_free(
                &fixed,
                &mut b,
                declaration,
                request,
                &expressions,
                &[],
                &model.action.slots,
                Some(target),
                c,
            )?);
        }
        let reasons = explicit
            .iter()
            .flat_map(|x| x.reasons.iter().cloned())
            .collect::<Vec<_>>();
        if reasons.iter().any(|r| {
            !matches!(r.kind, ReasonKind::Missing)
                || r.missing.iter().any(|f| !model.missing.contains(f))
        }) {
            return Ok(Source {
                base,
                parts: std::mem::take(&mut b.parts),
                scope_domains: vec![],
                request: request.clone(),
                witness,
                system: None,
                answer: Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons,
                    scope: model.scope,
                },
            });
        }
        let mut global = geometry::Support {
            carrier: vec![],
            positions: vec![],
            visible: vec![],
        };
        let patches = explicit
            .iter()
            .filter(|x| implicit || !x.locals.is_empty())
            .map(|x| geometry::Support {
                carrier: x.carrier.clone(),
                positions: x.positions.clone(),
                visible: x.visible.clone(),
            })
            .collect::<Vec<_>>();
        if model
            .supports
            .iter()
            .any(|s| !patches.iter().any(|p| p.contains(s)))
            || model
                .action
                .slots
                .iter()
                .any(|s| !patches.iter().any(|p| p.visible.contains(s)))
        {
            let reason = Reason {
                kind: ReasonKind::VisibilityInsufficient {
                    locals: local_names,
                    coordinates: expressions.clone(),
                },
                request: request.id.clone(),
                dependencies: expressions.clone(),
                missing: vec![],
                location: None,
            };
            for expression in &expressions {
                b.parts[expression.0 - base].reasons.push(reason.clone());
            }
            return Ok(Source {
                base,
                parts: std::mem::take(&mut b.parts),
                scope_domains: vec![],
                request: request.clone(),
                witness,
                system: None,
                answer: Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons: vec![reason],
                    scope: model.scope,
                },
            });
        }
        for p in &patches {
            global.carrier.extend(p.carrier.iter().cloned());
            global.positions.extend(p.positions.iter().cloned());
            global.visible.extend(p.visible.iter().cloned());
        }
        global.carrier.sort_by_key(Json::canonical);
        global.carrier.dedup();
        global.positions.sort();
        global.positions.dedup();
        global.visible.sort();
        global.visible.dedup();
        let fixed_positions = global.positions.clone();
        let mut supports = vec![global];
        let mut patch_indices = vec![];
        for patch in &patches {
            let i = if let Some(i) = supports.iter().position(|p| p == patch) {
                i
            } else {
                supports.push(patch.clone());
                supports.len() - 1
            };
            if !patch_indices.contains(&i) {
                patch_indices.push(i);
            }
        }
        let mut i = 0;
        while i < supports.len() {
            for j in 0..i {
                c.checkpoint(super::super::control::Checkpoint::Localize)?;
                let support = supports[i].intersect(&supports[j]);
                if !supports.contains(&support) {
                    supports.push(support);
                }
            }
            i += 1;
        }
        let (free, equation, semantic) = fibers(&model, &supports, c)?;
        let ring = b.push(
            NodeType::Construction(T::Ring),
            "ring",
            Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Z"))]),
            vec![],
            None,
            None,
        )?;
        let mut states = vec![];
        let mut contexts = vec![];
        for (i, support) in supports.iter().enumerate() {
            let st = state::build(
                &fixed,
                &mut b,
                ring,
                target,
                &model,
                support,
                &free[i],
                &laws,
                &semantic[i],
                c,
            )?;
            let mut readings = vec![];
            let mut instances = vec![];
            let mut arguments = vec![target];
            let mut included = vec![];
            for e in &explicit {
                let es = geometry::Support {
                    carrier: e.carrier.clone(),
                    positions: e.positions.clone(),
                    visible: e.visible.clone(),
                };
                if support.contains(&es) {
                    instances.extend(e.locals.iter().cloned());
                    arguments.extend(e.arguments.iter().copied());
                }
                for (j, rs) in e.read_supports.iter().enumerate() {
                    if support.contains(rs) {
                        readings.push(e.readings[j].clone());
                        arguments.extend(e.read_refs[2 * j..2 * j + 2].iter().copied());
                        included.push(rs.clone());
                    }
                }
            }
            let mut projected = vec![];
            for e in &explicit {
                for p in &e.projections {
                    if !support.contains(&p.support)
                        || included.iter().any(|s| s.contains(&p.support))
                        || projected.contains(&p.support)
                    {
                        continue;
                    }
                    let (expression, image) =
                        geometry::project(&mut b, e.read_refs[2 * p.read], p, &model.action.slots)?;
                    readings.push(Json::obj([
                        ("expression", expression.wire()),
                        ("type", p.values[0].ty().wire()),
                        ("domain", image.wire()),
                    ]));
                    arguments.extend([expression, image]);
                    projected.push(p.support.clone());
                }
            }
            let mut dependencies = vec![];
            for slot in &support.positions {
                let (v, r) = state::position(&fixed, &mut b, slot)?;
                dependencies.push(v);
                arguments.push(r);
            }
            let selected = model
                .supports
                .iter()
                .enumerate()
                .filter(|(_, s)| support.contains(s))
                .map(|(i, _)| laws[i])
                .collect::<Vec<_>>();
            arguments.extend(selected.iter().copied());
            let context = b.push(
                NodeType::Construction(T::Context),
                "context",
                Json::obj([
                    ("base", target.wire()),
                    ("locals", Json::Arr(instances)),
                    ("carrier", Json::Arr(support.carrier.clone())),
                    ("dependencies", Json::Arr(dependencies)),
                    ("readings", Json::Arr(readings)),
                    ("law_coordinates", refs(&selected)),
                ]),
                arguments,
                None,
                None,
            )?;
            contexts.push(context);
            states.push(st);
        }
        let mut intersections = vec![vec![0; supports.len()]; supports.len()];
        for i in 0..supports.len() {
            for j in 0..supports.len() {
                intersections[i][j] = supports
                    .iter()
                    .position(|s| *s == supports[i].intersect(&supports[j]))
                    .ok_or("整数局所の交わりがない")?;
            }
        }
        let mut arrows = BTreeMap::new();
        let mut restrictions = BTreeMap::new();
        let mut maps = vec![];
        let mut restriction_refs = vec![];
        let mut restriction_values = vec![];
        let mut coefficient_values = vec![];
        for v in 0..supports.len() {
            for w in 0..supports.len() {
                c.checkpoint(super::super::control::Checkpoint::Localize)?;
                if !supports[w].contains(&supports[v]) {
                    continue;
                }
                let indices = free[v]
                    .iter()
                    .map(|i| {
                        free[w]
                            .iter()
                            .position(|j| i == j)
                            .ok_or("制限先の自由位置が元にない")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let eq = linear::restrict(&equation[w], &equation[v], &indices, c)?;
                let sem = linear::restrict(&semantic[w], &semantic[v], &indices, c)?;
                let projection = linear::project(&linear::identity(free[w].len()), &indices);
                let mut rr = vec![];
                let mut cr = vec![];
                for side in 0..2 {
                    let (source, dest, coefficients) = if side == 0 {
                        (states[w].equation_domain, states[v].equation_domain, &eq)
                    } else {
                        (states[w].semantic_domain, states[v].semantic_domain, &sem)
                    };
                    rr.push(state::affine_map(
                        &mut b,
                        source,
                        dest,
                        states[w].ambient,
                        states[v].ambient,
                        &projection,
                        free[w].len(),
                        &vec![Z::zero(); free[v].len()],
                        c,
                    )?);
                    cr.push(change_result::linear_result::map(
                        &mut b,
                        states[w].coefficients[side],
                        states[v].coefficients[side],
                        coefficients,
                        if side == 0 {
                            equation[w].rank
                        } else {
                            semantic[w].rank
                        },
                        c,
                    )?);
                }
                let images = supports[v]
                    .carrier
                    .iter()
                    .map(|x| {
                        supports[w]
                            .carrier
                            .iter()
                            .position(|y| x == y)
                            .map(|i| Json::Nat(i as u64))
                            .ok_or("contextの包含像がない")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let arrow = b.push(
                    NodeType::Construction(T::ContextMap),
                    "context_map",
                    Json::obj([
                        ("source", contexts[v].wire()),
                        ("target", contexts[w].wire()),
                        ("images", Json::Arr(images)),
                        ("restrictions", refs(&rr)),
                    ]),
                    vec![contexts[v], contexts[w], rr[0], rr[1]],
                    None,
                    None,
                )?;
                for side in 0..2 {
                    restriction_values.push(Json::obj([
                        (
                            "side",
                            Json::str(if side == 0 { "equation" } else { "semantic" }),
                        ),
                        ("arrow", arrow.wire()),
                        ("map", rr[side].wire()),
                    ]));
                    coefficient_values.push(Json::obj([
                        (
                            "side",
                            Json::str(if side == 0 { "equation" } else { "semantic" }),
                        ),
                        ("arrow", arrow.wire()),
                        ("map", cr[side].wire()),
                    ]));
                }
                restriction_refs.extend(rr);
                restriction_refs.extend(cr);
                maps.push(arrow);
                arrows.insert((v, w), arrow);
                restrictions.insert((v, w), (eq, sem));
            }
        }
        let mut overlaps = vec![];
        for &left in &patch_indices {
            for &right in &patch_indices {
                let i = intersections[left][right];
                let lp = arrows[&(i, left)];
                let rp = arrows[&(i, right)];
                overlaps.push(b.push(
                    NodeType::Construction(T::Overlap),
                    "context",
                    Json::obj([
                        ("left", contexts[left].wire()),
                        ("right", contexts[right].wire()),
                        ("context", contexts[i].wire()),
                        ("left_projection", lp.wire()),
                        ("right_projection", rp.wire()),
                    ]),
                    vec![contexts[left], contexts[right], contexts[i], lp, rp],
                    None,
                    None,
                )?);
            }
        }
        let adequacy = b.proposition(
            "cover_adequate",
            contexts.clone(),
            vec![],
            Decision::Established,
        )?;
        let patch_refs = patch_indices
            .iter()
            .map(|i| contexts[*i])
            .collect::<Vec<_>>();
        let cover = b.push(
            NodeType::Construction(T::Cover),
            "cover",
            Json::obj([
                ("base", contexts[0].wire()),
                ("patches", refs(&patch_refs)),
                ("overlaps", refs(&overlaps)),
                ("adequacy", adequacy.wire()),
            ]),
            std::iter::once(contexts[0])
                .chain(patch_refs)
                .chain(overlaps)
                .chain([adequacy])
                .collect(),
            None,
            None,
        )?;
        let (topology, checks) = geometry::topology(
            &mut b,
            &supports,
            &contexts,
            &maps,
            cover,
            &arrows,
            &patch_indices,
        )?;
        let solutions = states.iter().map(|s| [s.equation, s.semantic]).collect();
        let diagram = Diagram {
            missing: model.missing.clone(),
            requirements: model.requirements.clone(),
            law_refs: laws.clone(),
            assignments: assignments.clone(),
            sheaf_conditions: vec![],
            solutions,
            slots: model.action.slots.clone(),
            free,
            patches: patch_indices,
            intersections,
            equation,
            semantic,
            restrictions,
            contexts: contexts.clone(),
            cover,
        };
        emit_system(
            &mut b,
            request,
            target,
            witness,
            base,
            model,
            laws,
            expressions,
            fixed_positions,
            states,
            maps,
            topology,
            checks,
            restriction_values,
            coefficient_values,
            restriction_refs,
            adequacy,
            diagram,
            c,
        )
    })();
    retain_partial(result, b, request, saved_witness)
}

#[allow(clippy::too_many_arguments)]
fn emit_system(
    b: &mut Builder<'_>,
    request: &Request,
    target: NodeRef,
    witness: Arc<ArchitectureWitness>,
    base: usize,
    model: Model,
    laws: Vec<NodeRef>,
    expressions: Vec<NodeRef>,
    fixed_positions: Vec<Fact>,
    states: Vec<state::State>,
    maps: Vec<NodeRef>,
    topology: NodeRef,
    checks: Vec<(usize, Vec<usize>)>,
    restrictions: Vec<Json>,
    coefficient_restrictions: Vec<Json>,
    restriction_refs: Vec<NodeRef>,
    adequacy: NodeRef,
    mut diagram: Diagram,
    c: &mut Control,
) -> Result<Source, ValidationFailure> {
    let contexts = &diagram.contexts;
    let mut conditions = vec![];
    let mut sheaf_checks = vec![];
    for (side, semantic) in [("equation", false), ("semantic", true)] {
        let known = model.missing.is_empty();
        let cover_holds = if known {
            linear::glues(&diagram, &diagram.patches, 0, semantic, c)?
        } else {
            false
        };
        let mut topology_holds = known;
        if known {
            for (target, sources) in &checks {
                topology_holds &= linear::glues(&diagram, sources, *target, semantic, c)?;
            }
        }
        for (scope, object, holds) in [
            ("cover", diagram.cover, cover_holds),
            ("topology", topology, topology_holds),
        ] {
            let proposition = b.proposition(
                "sheaf_condition",
                std::iter::once(object)
                    .chain(restriction_refs.iter().copied())
                    .collect(),
                vec![],
                if !known {
                    Decision::Undetermined
                } else if holds {
                    Decision::Established
                } else {
                    Decision::Refuted
                },
            )?;
            conditions.push(proposition);
            sheaf_checks.push(Json::obj([
                ("scope", Json::str(scope)),
                ("side", Json::str(side)),
                ("proposition", proposition.wire()),
            ]));
        }
    }
    diagram.sheaf_conditions = conditions.clone();
    let mut fields = BTreeMap::from([
        ("base".into(), target.wire()),
        ("change".into(), Json::str(&model.change)),
        ("laws".into(), refs(&laws)),
        ("contexts".into(), refs(contexts)),
        ("maps".into(), refs(&maps)),
        ("cover".into(), diagram.cover.wire()),
        ("topology".into(), topology.wire()),
        (
            "semantic_states".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .map(|(context, s)| {
                        Json::obj([
                            ("context", context.wire()),
                            ("parameters", s.semantic.wire()),
                            ("state_image", s.semantic_domain.wire()),
                            ("action", s.action.wire()),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "equation_states".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .map(|(context, s)| {
                        Json::obj([
                            ("context", context.wire()),
                            ("space", s.equations.wire()),
                            ("solutions", s.equation.wire()),
                        ])
                    })
                    .collect(),
            ),
        ),
        ("restrictions".into(), Json::Arr(restrictions)),
        (
            "coefficient_restrictions".into(),
            Json::Arr(coefficient_restrictions),
        ),
        (
            "coefficients".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .flat_map(|(context, s)| {
                        [0, 1].map(|i| {
                            Json::obj([
                                (
                                    "side",
                                    Json::str(if i == 0 { "equation" } else { "semantic" }),
                                ),
                                ("context", context.wire()),
                                ("module", s.coefficients[i].wire()),
                            ])
                        })
                    })
                    .collect(),
            ),
        ),
        (
            "state_comparisons".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .map(|(context, s)| {
                        Json::obj([
                            ("context", context.wire()),
                            ("map", s.comparison.wire()),
                            ("conditions", Json::Arr(vec![])),
                        ])
                    })
                    .collect(),
            ),
        ),
        ("sheaf_checks".into(), Json::Arr(sheaf_checks)),
    ]);
    for name in [
        "actions",
        "presentations",
        "polynomial_inclusions",
        "residual_restrictions",
        "conditions",
    ] {
        fields.insert(name.into(), Json::Arr(vec![]));
    }
    let args = [target, diagram.cover, topology]
        .into_iter()
        .chain(contexts.iter().copied())
        .chain(maps)
        .chain(laws.iter().copied())
        .chain(restriction_refs)
        .chain(conditions)
        .chain(states.iter().flat_map(|s| {
            [
                s.semantic,
                s.semantic_domain,
                s.action,
                s.equations,
                s.equation,
                s.comparison,
                s.coefficients[0],
                s.coefficients[1],
            ]
        }))
        .collect();
    let system = b.push(
        NodeType::Construction(T::LocalSystem),
        "local_system",
        Json::Obj(fields),
        args,
        None,
        None,
    )?;
    let label = change_result::value(b, &Scalar::Text("local_system".into()))?;
    let proposition = b.proposition(
        "constructible",
        vec![label, system],
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
        reasons: if model.missing.is_empty() {
            vec![]
        } else {
            vec![Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: expressions.clone(),
                missing: model.missing.clone(),
                location: None,
            }]
        },
        scope: model.scope,
    };
    b.parts[system.0 - base].reasons = answer.reasons.clone();
    let saved = System {
        parameters: states[0].parameters,
        laws,
        expression: *expressions.first().ok_or("整数局所Lawがない")?,
        semantic: states[0].semantic,
        equation: states[0].equation,
        domain: states[0].semantic_domain,
        inhabited: diagram.semantic[0].origin.is_some(),
        patch_count: diagram.patches.len(),
        finite: None,
        integer: Some(diagram),
        fixed_positions,
    };
    Ok(Source {
        base,
        parts: std::mem::take(&mut b.parts),
        scope_domains: vec![],
        answer,
        request: request.clone(),
        witness,
        system: Some(saved),
    })
}

fn retain_partial(
    result: Result<Source, ValidationFailure>,
    b: Builder<'_>,
    request: &Request,
    witness: Arc<ArchitectureWitness>,
) -> Result<Source, ValidationFailure> {
    match result {
        Err(ValidationFailure::Stop(stop)) if !b.parts.is_empty() => {
            let dependencies = b
                .parts
                .iter()
                .enumerate()
                .filter(|(i, p)| {
                    *i == 0
                        || matches!(
                            p.ty,
                            NodeType::Construction(
                                T::Context | T::Cover | T::Topology | T::Complex | T::Cohomology
                            )
                        )
                })
                .map(|(i, _)| NodeRef(b.base + i))
                .collect();
            let reason = Reason {
                kind: ReasonKind::Stop(stop),
                request: request.id.clone(),
                dependencies,
                missing: vec![],
                location: None,
            };
            let scope = b.parts.iter().fold(Scope::default(), |mut s, p| {
                s.merge(&p.scope);
                s
            });
            Ok(Source {
                base: b.base,
                parts: b.parts,
                scope_domains: vec![],
                request: request.clone(),
                witness,
                system: None,
                answer: Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons: vec![reason],
                    scope,
                },
            })
        }
        result => result,
    }
}
