//! 固定整数系の入力方向を、正確な像と共通の元Assignmentで区別する。
use super::*;
use crate::observed::environment::repair_problem::family;
use num_traits::{One, Zero};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Goal {
    Decision,
    Assignment,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Effect {
    Zero,
    Image,
    Outside,
}
#[derive(Debug)]
pub(super) struct Math {
    joint: Arc<Joint>,
    fixed: Vec<usize>,
    seed: Option<Vec<Z>>,
    effects: Vec<Effect>,
}
#[derive(Debug)]
pub(super) struct Observation {
    reader: String,
    bindings: Vec<(String, Scalar)>,
    readings: Vec<usize>,
    enabled: Vec<bool>,
    math: Arc<Math>,
    affine: Arc<Affine>,
}
#[derive(Debug)]
struct Affine {
    input_module: NodeRef,
    total: NodeRef,
    rows: NodeRef,
    equations: NodeRef,
    rhs: NodeRef,
}
/// 同じ入力族・内部集合の全同時fiberと共有像。範囲ごとに元の系を再分解しない。
#[derive(Debug)]
struct Joint {
    fiber: integer_fiber::Fiber,
    projection: Option<Arc<Projection>>,
    slots: Vec<usize>,
}
impl Joint {
    fn new(env: &Environment<'_>, shared: &Shared, c: &Control) -> Result<Self, ValidationFailure> {
        let family = shared
            .compiled
            .family
            .as_ref()
            .ok_or(internal!("整数入力族がない"))?;
        let system = &family.system;
        let n = shared.compiled.linear.parameter_count;
        let m = family.fields.len();
        let mut matrix = Vec::with_capacity(system.rhs.len());
        for (a, b) in system.equations.iter().zip(&system.inputs) {
            tick(c)?;
            matrix.push(a.iter().chain(b).cloned().collect());
        }
        let fiber = integer_fiber::reuse::solve(
            &env.results.integer_factors,
            &matrix,
            n + m,
            &system.rhs,
            c,
        )?;
        let mut selected = BTreeSet::new();
        for (i, writes) in shared.compiled.linear.unit_writes.iter().enumerate() {
            tick(c)?;
            if !shared.internal[i] {
                for fact in writes {
                    selected.insert(
                        find(&shared.compiled.linear.slots, fact, c)?
                            .ok_or(internal!("整数共有更新先がない"))?,
                    );
                }
            }
        }
        let slots = selected.into_iter().collect::<Vec<_>>();
        let projection = if let Some(origin) = &fiber.particular {
            let mut action = Vec::with_capacity(slots.len());
            let mut offset = Vec::with_capacity(slots.len());
            for slot in &slots {
                tick(c)?;
                let mut row = shared.compiled.linear.action[*slot].clone();
                row.resize(n + m, Z::zero());
                // 基準値が入力座標なら、更新後値−その入力値を共有側に保持する。
                if let Some(j) = find(&family.fields, &shared.compiled.linear.slots[*slot], c)? {
                    row[n + j] = -Z::one();
                }
                action.push(row);
                offset.push(shared.compiled.linear.offset[*slot].clone());
            }
            Some(Arc::new(Projection::new(
                &env.results.integer_factors,
                origin,
                &fiber.decomposition.kernel,
                &action,
                &offset,
                (0..slots.len()).collect(),
                c,
            )?))
        } else {
            None
        };
        Ok(Self {
            fiber,
            projection,
            slots,
        })
    }
}
impl Math {
    fn new(
        env: &Environment<'_>,
        shared: &Shared,
        enabled: &[bool],
        prior: Option<Arc<Joint>>,
        c: &Control,
    ) -> Result<Result<Self, Vec<Fact>>, ValidationFailure> {
        let family = shared
            .compiled
            .family
            .as_ref()
            .ok_or(internal!("整数入力族がない"))?;
        let n = shared.compiled.linear.parameter_count;
        let m = family.fields.len();
        let joint = if let Some(prior) = prior {
            prior
        } else {
            Arc::new(Joint::new(env, shared, c)?)
        };
        let mut selected = BTreeSet::new();
        for (i, writes) in shared.compiled.linear.unit_writes.iter().enumerate() {
            tick(c)?;
            if !enabled[i] && !shared.internal[i] {
                for fact in writes {
                    selected.insert(
                        find(&shared.compiled.linear.slots, fact, c)?
                            .ok_or(internal!("整数観測の固定先がない"))?,
                    );
                }
            }
        }
        let mut fixed = vec![];
        let mut constraints = vec![];
        let mut missing = vec![];
        for slot in selected {
            tick(c)?;
            let fact = &shared.compiled.linear.slots[slot];
            let value = if let Some(value) = &shared.compiled.baselines[slot] {
                Some(value.clone())
            } else if find(&family.fields, fact, c)?.is_some() {
                Some(Z::zero())
            } else {
                None
            };
            if let Some(value) = value {
                fixed.push(slot);
                constraints.push((
                    find(&joint.slots, &slot, c)?.ok_or(internal!("整数共有側の固定行がない"))?,
                    value,
                ));
            } else {
                missing.push(fact.clone());
            }
        }
        if !missing.is_empty() && joint.fiber.particular.is_some() {
            return Ok(Err(missing));
        }
        let mut effects = vec![Effect::Zero; m];
        let seed = if let (Some(projection), Some(origin)) =
            (&joint.projection, &joint.fiber.particular)
        {
            let (matrix, rhs) = projection.constraints(&constraints, c)?;
            let range = integer_fiber::reuse::solve(
                &env.results.integer_factors,
                &matrix,
                projection.visible(),
                &rhs,
                c,
            )?;
            let seed = projection
                .candidate(
                    origin,
                    &joint.fiber.decomposition.kernel,
                    &range,
                    &0u32.into(),
                    c,
                )?
                .map(|mut point| point.split_off(n));
            let mut varying = vec![false; m];
            for j in 0..m {
                for row in &family.system.inputs {
                    tick(c)?;
                    varying[j] |= !row[j].is_zero();
                }
                for slot in &fixed {
                    tick(c)?;
                    varying[j] |= family.fields[j] == shared.compiled.linear.slots[*slot];
                }
            }
            if seed.is_some() && varying.iter().any(|v| *v) {
                let free = projection.free(&range)?;
                // 入力像だけが必要。pだけを動かす零列を除き、全元核はjointに保持する。
                let mut input_image = vec![Vec::new(); m];
                let mut columns = 0;
                for j in 0..free {
                    tick(c)?;
                    let column = projection.kernel_column(
                        &joint.fiber.decomposition.kernel,
                        &range,
                        j,
                        c,
                    )?;
                    if column[n..].iter().any(|v| !v.is_zero()) {
                        for (row, value) in input_image.iter_mut().zip(column.into_iter().skip(n)) {
                            row.push(value);
                        }
                        columns += 1;
                    }
                }
                let image = integer_fiber::reuse::factor(
                    &env.results.integer_factors,
                    input_image,
                    columns,
                    c,
                )?;
                for j in 0..m {
                    tick(c)?;
                    if varying[j] {
                        let mut direction = vec![Z::zero(); m];
                        direction[j] = Z::one();
                        effects[j] = if integer_fiber::restore(
                            image.decomposition().clone(),
                            &direction,
                            c,
                        )?
                        .particular
                        .is_some()
                        {
                            Effect::Image
                        } else {
                            Effect::Outside
                        };
                    }
                }
            }
            seed
        } else {
            None
        };
        Ok(Ok(Self {
            joint,
            fixed,
            seed,
            effects,
        }))
    }
    fn needed(&self, goal: Goal, c: &Control) -> Result<Vec<usize>, ValidationFailure> {
        let mut needed = vec![];
        if self.seed.is_some() {
            for (i, effect) in self.effects.iter().enumerate() {
                tick(c)?;
                if !matches!(
                    (goal, effect),
                    (_, Effect::Zero) | (Goal::Decision, Effect::Image)
                ) {
                    needed.push(i);
                }
            }
        }
        Ok(needed)
    }
    fn example(&self, j: usize) -> Result<(&[Z], Vec<Z>, &'static str), ValidationFailure> {
        let first = self
            .seed
            .as_deref()
            .ok_or(internal!("全入力不能の系に不足反例はない"))?;
        let mut second = first.to_vec();
        second[j] += Z::one();
        Ok((
            first,
            second,
            if self.effects[j] == Effect::Outside {
                "decision_difference"
            } else {
                "no_common_assignment"
            },
        ))
    }
}

fn reject(
    g: &mut Graph,
    r: &Request,
    shared: Arc<Shared>,
    inputs: Vec<NodeRef>,
) -> Result<Source, ValidationFailure> {
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let claim = condition(&mut b, r, inputs.clone(), Decision::Refuted)?;
    let mut a = answer(r, claim, Decision::Refuted, BTreeMap::new(), &b);
    fail(&mut a, "observe");
    Ok(wrap(b, a, r, shared.witness.clone(), Some(shared), inputs))
}
fn pending(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    shared: &Shared,
    inputs: Vec<NodeRef>,
    reading: (&str, &[(String, Scalar)]),
    missing: Vec<Fact>,
) -> Result<Source, ValidationFailure> {
    let (reader, bindings) = reading;
    let unsupported = missing.is_empty();
    let Signature::View { body, returns, .. } =
        &env.indexes.inputs.law().declarations()[reader].signature
    else {
        unreachable!("読取りview")
    };
    prepare::pending(
        env,
        g,
        r,
        shared.witness.clone(),
        inputs,
        crate::observed::environment::change_affine::Pending {
            expression: Some(*body),
            coefficient_type: Some(returns.clone()),
            unsupported: Some("integer_affine_repair_observation"),
            bindings: bindings.to_vec(),
            facts: missing,
            ..Default::default()
        },
        unsupported,
    )
}
fn tuple(b: &mut Builder<'_>, domain: NodeRef, point: &[Z]) -> Result<NodeRef, ValidationFailure> {
    let at = change_result::value(
        b,
        &Scalar::Tuple(point.iter().cloned().map(Scalar::Z).collect()),
    )?;
    b.parts[at.0 - b.base].arguments.push(domain);
    b.parts[at.0 - b.base].scope.completions = true;
    Ok(at)
}
fn witness(
    b: &mut Builder<'_>,
    shared: &Shared,
    math: &Math,
    range: NodeRef,
    readings: &[usize],
    j: usize,
    origin: &mut Option<NodeRef>,
) -> Result<(Json, NodeRef), ValidationFailure> {
    let family = shared
        .compiled
        .family
        .as_ref()
        .ok_or(internal!("整数反例の入力族がない"))?;
    let domain = shared
        .input_domain
        .ok_or(internal!("整数入力域がない"))?
        .domain;
    let (first, second, kind) = math.example(j)?;
    let mut values = vec![];
    let mut arguments = vec![domain];
    let mut fields = vec![];
    for i in readings.iter().copied().filter(|i| *i != j) {
        let at = change_result::value(b, &Scalar::Z(first[i].clone()))?;
        values.push(at);
        arguments.push(at);
        fields.push(family.fields[i].wire());
    }
    let group = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("observation_fiber")),
            ("domain", domain.wire()),
            ("fields", Json::Arr(fields)),
            ("values", refs(&values)),
            (
                "value_type",
                Type::Tuple(vec![Type::Z; family.fields.len()]).wire(),
            ),
        ]),
        arguments,
        None,
    )?;
    let first = if let Some(first) = *origin {
        first
    } else {
        let at = tuple(b, domain, first)?;
        *origin = Some(at);
        at
    };
    let second = tuple(b, domain, &second)?;
    let proof = super::super::observation::named(
        b,
        kind,
        vec![
            shared.problem.ok_or(internal!("整数問題がない"))?,
            range,
            group,
            first,
            second,
        ],
        true,
    )?;
    Ok((
        Json::obj([
            ("kind", Json::str(kind)),
            ("inputs", refs(&[first, second])),
        ]),
        proof,
    ))
}
pub(super) fn compute(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
    problem: NodeRef,
    shared: Arc<Shared>,
) -> Result<Source, ValidationFailure> {
    let family = shared
        .compiled
        .family
        .as_ref()
        .ok_or(internal!("整数観測の入力族がない"))?;
    let mut inputs = vec![problem];
    let selector = &r
        .arguments
        .iter()
        .find(|a| a.name == "within")
        .ok_or(internal!("整数観測の範囲がない"))?
        .value;
    let (within, enabled) = mask(env, g, &shared, selector)?;
    inputs.push(within);
    let Some(enabled) = enabled else {
        return reject(g, r, shared, inputs);
    };
    let mut support = vec![];
    let mut scope = Scope::default();
    let (reader, bindings, allowed, old_plan) =
        match &r.head {
            Selector::Declaration { name } => {
                let Signature::View { params, .. } =
                    &env.indexes.inputs.law().declarations()[name].signature
                else {
                    unreachable!("観測view")
                };
                let mut bindings = vec![];
                for p in params {
                    let a = r
                        .arguments
                        .iter()
                        .find(|a| a.name == format!("bind.{}", p.name))
                        .ok_or(internal!("整数観測の束縛がない"))?;
                    if matches!(a.value, Selector::Answer { .. }) {
                        inputs.push(reference(env, g, &a.value)?);
                    }
                    bindings.push((p.name.clone(), change_search::selector(env, g, &a.value)?));
                }
                let current = shared.compiled.environment(env, c)?;
                let read = match family::read(&current, name, &bindings) {
                    Ok(read) => read,
                    Err(ValidationFailure::UnsupportedExpression { .. }) => {
                        return pending(env, g, r, &shared, inputs, (name, &bindings), vec![]);
                    }
                    Err(e) => return Err(e),
                };
                if read.failed {
                    return reject(g, r, shared, inputs);
                }
                if read.blocked {
                    return pending(env, g, r, &shared, inputs, (name, &bindings), read.missing);
                }
                let mut allowed = BTreeSet::new();
                for fact in read.support.iter().chain(&read.missing) {
                    tick(c)?;
                    if let Some(j) = family.fields.iter().position(|f| {
                        crate::observed::environment::repair_problem::same_slot(f, fact)
                    }) {
                        allowed.insert(j);
                    }
                }
                support = read.support;
                scope = read.scope;
                (
                    name.clone(),
                    bindings,
                    allowed.into_iter().collect::<Vec<_>>(),
                    None,
                )
            }
            Selector::Answer { .. } => {
                let at = reference(env, g, &r.head)?;
                inputs.push(at);
                let old = data(g, at)?;
                let Some(state) = old.source.integer() else {
                    return reject(g, r, shared, inputs);
                };
                if !Arc::ptr_eq(&state.shared, &shared) {
                    return reject(g, r, shared, inputs);
                }
                let plan = state
                    .observation
                    .as_ref()
                    .ok_or(internal!("整数planの元観測がない"))?;
                (
                    plan.reader.clone(),
                    plan.bindings.clone(),
                    plan.readings.clone(),
                    Some(at),
                )
            }
            _ => return Err(internal!("整数観測の指定が不正").into()),
        };
    let goal = match &r
        .arguments
        .iter()
        .find(|a| a.name == "output")
        .ok_or(internal!("整数観測の目的がない"))?
        .value
    {
        Selector::Enum { value } if value == "decision" => Goal::Decision,
        Selector::Enum { value } if value == "assignment" => Goal::Assignment,
        _ => return Err(internal!("整数観測の目的が不正").into()),
    };
    let mut reused = None;
    let mut joint = None;
    let mut presentation = None;
    for node in g.nodes.iter().rev() {
        tick(c)?;
        let Some(Payload::Construction(v)) = &node.payload else {
            continue;
        };
        let D::SharedRepair(d) = &v.data else {
            continue;
        };
        if d.index + 1 != d.source.parts.len() {
            continue;
        }
        if let Some(state) = d.source.integer()
            && Arc::ptr_eq(&state.shared, &shared)
            && let Some(plan) = &state.observation
        {
            if joint.is_none() {
                joint = Some(plan.math.joint.clone());
            }
            if plan.enabled == enabled {
                reused = Some(plan.math.clone());
                presentation = Some(plan.affine.clone());
                break;
            }
        }
    }
    let math = if let Some(math) = reused {
        math
    } else {
        match Math::new(env, &shared, &enabled, joint, c)? {
            Ok(math) => Arc::new(math),
            Err(missing) => {
                return pending(env, g, r, &shared, inputs, (&reader, &bindings), missing);
            }
        }
    };
    let needed = math.needed(goal, c)?;
    let sufficient = needed.iter().all(|j| allowed.contains(j));
    let readings = if sufficient { needed.clone() } else { allowed };
    let common = if sufficient && goal == Goal::Assignment && readings.is_empty() {
        Some(match resolve_range(env, &shared, &enabled, c)? {
            Ok(math) => math,
            Err(missing) => {
                return pending(env, g, r, &shared, inputs, (&reader, &bindings), missing);
            }
        })
    } else {
        None
    };
    let public = if common.is_some() {
        known_public(g, &shared, c)?
    } else {
        None
    };
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let range = range_value(&mut b, &shared, &enabled, &inputs)?;
    let input_domain = shared
        .input_domain
        .ok_or(internal!("整数観測の入力域がない"))?;
    let mut arguments = vec![problem, range, input_domain.domain];
    let reading = if let Some(at) = old_plan {
        arguments.push(at);
        Json::obj([("plan", at.wire())])
    } else {
        let mut fields = vec![];
        for (name, value) in &bindings {
            let at = change_result::value(&mut b, value)?;
            arguments.push(at);
            fields.push(Json::obj([("name", Json::str(name)), ("value", at.wire())]));
        }
        Json::obj([
            ("view", Json::str(&reader)),
            ("bindings", Json::Arr(fields)),
        ])
    };
    let affine = if let Some(affine) = presentation {
        affine
    } else {
        use crate::observed::change_result::linear_result as display;
        let input_module = input_domain.coordinates;
        let total = display::module(
            &mut b,
            shared.ring,
            shared.compiled.linear.parameter_count + family.fields.len(),
            "direct_sum",
            vec![shared.parameter_module, input_module],
        )?;
        let system = &family.system;
        let rows = display::module(
            &mut b,
            shared.ring,
            system.rhs.len() + math.fixed.len(),
            "free",
            vec![problem, range],
        )?;
        let equations = display::map_generated(
            &mut b,
            total,
            rows,
            shared.compiled.linear.parameter_count + family.fields.len(),
            c,
            |j| {
                let n = shared.compiled.linear.parameter_count;
                let mut column = if j < n {
                    system
                        .equations
                        .iter()
                        .map(|r| r[j].clone())
                        .collect::<Vec<_>>()
                } else {
                    system
                        .inputs
                        .iter()
                        .map(|r| r[j - n].clone())
                        .collect::<Vec<_>>()
                };
                for slot in &math.fixed {
                    tick(c)?;
                    column.push(if j < n {
                        shared.compiled.linear.action[*slot][j].clone()
                    } else if family.fields[j - n] == shared.compiled.linear.slots[*slot] {
                        -Z::one()
                    } else {
                        Z::zero()
                    });
                }
                Ok(column)
            },
        )?;
        let mut values = system.rhs.clone();
        for slot in &math.fixed {
            tick(c)?;
            let baseline = if let Some(value) = &shared.compiled.baselines[*slot] {
                value.clone()
            } else if family.fields.contains(&shared.compiled.linear.slots[*slot]) {
                Z::zero()
            } else {
                return Err(internal!("確認済みの整数観測基準値がない").into());
            };
            values.push(baseline - &shared.compiled.linear.offset[*slot]);
        }
        let rhs = display::vector(&mut b, rows, &values, c)?;
        Arc::new(Affine {
            input_module,
            total,
            rows,
            equations,
            rhs,
        })
    };
    let Affine {
        input_module,
        total,
        rows,
        equations,
        rhs,
    } = *affine;
    arguments.extend([input_module, total, rows, equations, rhs]);
    let mut proofs = BTreeMap::new();
    let mut examples = vec![];
    let mut origin = None;
    for j in &needed {
        tick(c)?;
        let (example, proof) = witness(&mut b, &shared, &math, range, &readings, *j, &mut origin)?;
        examples.push(example);
        arguments.push(proof);
        proofs.insert(*j, proof);
    }
    let status = if sufficient {
        Decision::Established
    } else {
        Decision::Refuted
    };
    let claim = condition(&mut b, r, arguments.clone(), status)?;
    arguments.push(claim);
    let mut outputs = BTreeMap::new();
    let mut public_model = None;
    let mut solutions = None;
    if let Some(common) = &common {
        let public = if let Some(public) = public {
            public
        } else {
            publish_model(&mut b, &shared, c)?
        };
        let set = render_solutions(&mut b, &shared, &public, common, range, c)?;
        outputs.insert("solutions".into(), set);
        arguments.push(set);
        solutions = Some(set);
        public_model = Some(public);
    }
    let location = archsig_input::result::location_wire(&archsig_common::issue::Location::Law {
        span: env.indexes.inputs.law().declarations()[&reader].span,
    });
    let requirements = readings
        .iter()
        .map(|j| {
            Json::obj([
                ("field", family.fields[*j].wire()),
                (
                    "dependents",
                    refs(&proofs.get(j).copied().into_iter().collect::<Vec<_>>()),
                ),
                ("locations", Json::Arr(vec![location.clone()])),
            ])
        })
        .collect();
    let mut fields = vec![
        ("problem".to_owned(), problem.wire()),
        ("range".into(), range.wire()),
        (
            "goal".into(),
            Json::str(if goal == Goal::Decision {
                "decision"
            } else {
                "assignment"
            }),
        ),
        ("reading".into(), reading),
        ("requirements".into(), Json::Arr(requirements)),
        ("sufficient".into(), claim.wire()),
        ("cases".into(), Json::Arr(vec![])),
        ("counterexamples".into(), Json::Arr(examples)),
        (
            "affine".into(),
            Json::obj([
                ("parameters", shared.parameter_module.wire()),
                ("inputs", input_module.wire()),
                ("equations", equations.wire()),
                ("rhs", rhs.wire()),
            ]),
        ),
    ];
    if let Some(set) = solutions {
        fields.push(("solutions".into(), set.wire()));
    }
    let plan = b.push(
        NodeType::Construction(T::RepairObservation),
        "repair_observation",
        Json::Obj(fields.into_iter().collect()),
        arguments,
        None,
    )?;
    b.parts[plan.0 - base].support.extend(support);
    b.parts[plan.0 - base].support.sort();
    b.parts[plan.0 - base].support.dedup();
    b.parts[plan.0 - base].scope.merge(&scope);
    outputs.insert("plan".into(), plan);
    let mut a = answer(r, claim, status, outputs, &b);
    if !sufficient {
        fail(&mut a, "observe");
    }
    let mut source = wrap(
        b,
        a,
        r,
        shared.witness.clone(),
        Some(shared.clone()),
        inputs,
    );
    source.range = Some(enabled.clone());
    if let Some(Backend::Integer(state)) = &mut source.shared {
        state.observation = Some(Arc::new(Observation {
            reader,
            bindings,
            readings,
            enabled,
            math,
            affine,
        }));
        state.range_result = common;
        state.solutions = solutions;
        state.public_model = public_model;
    }
    Ok(source)
}

#[cfg(test)]
mod tests;
