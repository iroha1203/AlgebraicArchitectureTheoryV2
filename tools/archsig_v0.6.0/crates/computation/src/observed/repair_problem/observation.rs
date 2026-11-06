//! 同じ入力族の観測群で、可否と共通の元Assignmentを区別する。
use super::*;
use crate::observed::environment::repair_problem::family::{self, Family, Variant};
use std::collections::BTreeSet;
#[derive(Debug)]
pub(super) struct State {
    reader: String,
    bindings: Vec<(String, Scalar)>,
    readings: Vec<usize>,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Goal {
    Decision,
    Assignment,
}
struct Group {
    indices: Vec<usize>,
    possible: Option<bool>,
    common: Option<bool>,
}
#[derive(Clone)]
struct Counterexample {
    kind: &'static str,
    indices: Vec<usize>,
}
struct Analysis {
    groups: Vec<Group>,
    witnesses: Vec<Counterexample>,
}
impl Analysis {
    fn sufficient(&self) -> bool {
        self.witnesses.is_empty()
    }
}
fn variant_pins(shared: &Shared, variant: &Variant, enabled: &[bool]) -> Vec<Option<usize>> {
    let mut pins = vec![None; variant.relations.variables()];
    for output in &variant.outputs {
        if !shared.internal[output.subject] && !enabled[output.subject] {
            pins[output.column] = output.baseline;
        }
    }
    pins
}
fn common(
    shared: &Shared,
    indices: &[usize],
    enabled: &[bool],
    c: &Control,
) -> Result<(Arc<finite::Problem>, Vec<Option<usize>>), ValidationFailure> {
    let (family, _) = shared
        .family
        .as_ref()
        .ok_or(internal!("共通修復の入力族がない"))?;
    if indices.len() == family.variants.len()
        && indices.iter().copied().eq(0..family.variants.len())
    {
        return Ok((shared.compiled.relations.clone(), pins(shared, enabled)));
    }
    if let [index] = indices {
        let variant = &family.variants[*index];
        return Ok((
            variant.relations.clone(),
            variant_pins(shared, variant, enabled),
        ));
    }
    let selected = indices
        .iter()
        .map(|i| family.variants[*i].relations.as_ref())
        .collect::<Vec<_>>();
    let (joined, maps) = finite::Problem::join(&selected, shared.compiled.parameter_count, c)?;
    let mut fixed = vec![None; joined.variables()];
    for (index, map) in indices.iter().zip(maps) {
        for output in &family.variants[*index].outputs {
            if !shared.internal[output.subject] && !enabled[output.subject] {
                fixed[map[output.column]] = output.baseline;
            }
        }
    }
    Ok((Arc::new(joined), fixed))
}
fn common_exists(
    shared: &Shared,
    indices: &[usize],
    enabled: &[bool],
    c: &Control,
) -> Result<bool, ValidationFailure> {
    let (problem, pins) = common(shared, indices, enabled, c)?;
    problem.exists(&pins, c)
}
fn analyze(
    shared: &Shared,
    readings: &[usize],
    enabled: &[bool],
    goal: Goal,
    c: &Control,
) -> Result<Analysis, ValidationFailure> {
    let (family, _) = shared
        .family
        .as_ref()
        .ok_or(internal!("観測の入力族がない"))?;
    let mut groups = BTreeMap::<Vec<usize>, Vec<usize>>::new();
    for (index, point) in family.points.iter().enumerate() {
        tick(c)?;
        groups
            .entry(readings.iter().map(|i| point[*i]).collect())
            .or_default()
            .push(index);
    }
    let mut result = Analysis {
        groups: vec![],
        witnesses: vec![],
    };
    for (_, indices) in groups {
        tick(c)?;
        let mut first_yes = None;
        let mut first_no = None;
        for index in &indices {
            let variant = &family.variants[*index];
            if variant
                .relations
                .exists(&variant_pins(shared, variant, enabled), c)?
            {
                first_yes.get_or_insert(*index);
            } else {
                first_no.get_or_insert(*index);
            }
        }
        let possible = match (first_yes, first_no) {
            (Some(_), None) => Some(true),
            (None, Some(_)) => Some(false),
            (Some(_), Some(_)) => None,
            _ => return Err(internal!("観測群が空").into()),
        };
        let common = if goal == Goal::Assignment {
            Some(if possible == Some(true) {
                common_exists(shared, &indices, enabled, c)?
            } else {
                false
            })
        } else {
            None
        };
        if let (Some(yes), Some(no)) = (first_yes, first_no) {
            result.witnesses.push(Counterexample {
                kind: "decision_difference",
                indices: vec![yes, no],
            });
        } else if goal == Goal::Assignment && possible == Some(true) && common == Some(false) {
            let mut witness = indices.clone();
            for index in &indices {
                tick(c)?;
                if witness.len() > 1 {
                    let trial = witness
                        .iter()
                        .copied()
                        .filter(|i| i != index)
                        .collect::<Vec<_>>();
                    if !common_exists(shared, &trial, enabled, c)? {
                        witness = trial;
                    }
                }
            }
            result.witnesses.push(Counterexample {
                kind: "no_common_assignment",
                indices: witness,
            });
        }
        result.groups.push(Group {
            indices,
            possible,
            common,
        });
    }
    Ok(result)
}
struct Reduced {
    readings: Vec<usize>,
    analysis: Analysis,
    necessary: Vec<(usize, Counterexample)>,
}
fn reduce(
    shared: &Shared,
    allowed: &[usize],
    enabled: &[bool],
    goal: Goal,
    c: &Control,
) -> Result<Reduced, ValidationFailure> {
    let mut readings = allowed.to_vec();
    let mut analysis = analyze(shared, &readings, enabled, goal, c)?;
    let mut necessary = vec![];
    if analysis.sufficient() {
        for field in allowed {
            tick(c)?;
            let trial = readings
                .iter()
                .copied()
                .filter(|f| f != field)
                .collect::<Vec<_>>();
            let checked = analyze(shared, &trial, enabled, goal, c)?;
            if checked.sufficient() {
                readings = trial;
                analysis = checked;
            } else {
                necessary.push((
                    *field,
                    checked
                        .witnesses
                        .into_iter()
                        .next()
                        .ok_or(internal!("不足の反例がない"))?,
                ));
            }
        }
    }
    Ok(Reduced {
        readings,
        analysis,
        necessary,
    })
}
fn named(
    b: &mut Builder<'_>,
    name: &str,
    arguments: Vec<NodeRef>,
    value: bool,
) -> Result<NodeRef, ValidationFailure> {
    let label = change_result::value(b, &Scalar::Text(name.into()))?;
    b.proposition(
        "constructible",
        std::iter::once(label).chain(arguments).collect(),
        vec![],
        if value {
            Decision::Established
        } else {
            Decision::Refuted
        },
    )
}
fn input_type(family: &Family) -> Type {
    Type::Tuple(family.domains.iter().map(|d| d[0].ty()).collect())
}
fn fiber(
    b: &mut Builder<'_>,
    family: &Family,
    domain: NodeRef,
    readings: &[usize],
    index: usize,
) -> Result<(NodeRef, Vec<NodeRef>), ValidationFailure> {
    if readings.is_empty() {
        return Ok((domain, vec![]));
    }
    let mut values = vec![];
    for field in readings {
        values.push(change_result::value(
            b,
            &family.domains[*field][family.points[index][*field]],
        )?);
    }
    let fields = Json::Arr(readings.iter().map(|i| family.fields[*i].wire()).collect());
    let at = b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("observation_fiber")),
            ("domain", domain.wire()),
            ("fields", fields),
            ("values", refs(&values)),
            ("value_type", input_type(family).wire()),
        ]),
        std::iter::once(domain)
            .chain(values.iter().copied())
            .collect(),
        None,
    )?;
    Ok((at, values))
}
fn witness(
    b: &mut Builder<'_>,
    shared: &Shared,
    range: NodeRef,
    readings: &[usize],
    example: &Counterexample,
    point_refs: &mut BTreeMap<usize, NodeRef>,
) -> Result<(Json, NodeRef), ValidationFailure> {
    let (family, domain) = shared
        .family
        .as_ref()
        .ok_or(internal!("反例の入力族がない"))?;
    let mut values = vec![];
    for index in &example.indices {
        let value = if let Some(value) = point_refs.get(index) {
            *value
        } else {
            let value = Scalar::Tuple(
                family.points[*index]
                    .iter()
                    .enumerate()
                    .map(|(i, p)| family.domains[i][*p].clone())
                    .collect(),
            );
            let at = change_result::value(b, &value)?;
            point_refs.insert(*index, at);
            at
        };
        values.push(value);
    }
    let (group, _) = fiber(b, family, *domain, readings, example.indices[0])?;
    let proof = named(
        b,
        example.kind,
        [
            vec![
                shared.problem.ok_or(internal!("反例の修復問題がない"))?,
                range,
                group,
            ],
            values.clone(),
        ]
        .concat(),
        true,
    )?;
    Ok((
        Json::obj([("kind", Json::str(example.kind)), ("inputs", refs(&values))]),
        proof,
    ))
}
fn rejected(
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
    Ok(Source {
        base,
        parts: b.parts,
        answer: a,
        request: r.clone(),
        witness: shared.witness.clone(),
        shared: Some(shared),
        range: None,
        ranges: BTreeMap::new(),
        chosen: None,
        inputs,
        context: g.active,
        observation: None,
    })
}
fn compute_inner(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
) -> Result<Source, ValidationFailure> {
    let problem = reference(
        env,
        g,
        &r.arguments
            .iter()
            .find(|a| a.name == "on")
            .ok_or(internal!("観測の修復問題がない"))?
            .value,
    )?;
    let shared = data(g, problem)?
        .source
        .shared
        .as_ref()
        .ok_or(internal!("観測の共有構成がない"))?
        .clone();
    let (family, input_domain) = shared
        .family
        .as_ref()
        .ok_or(internal!("観測の有限入力族がない"))?;
    let family = family.clone();
    let input_domain = *input_domain;
    let mut inputs = vec![problem];
    let within = reference(
        env,
        g,
        &r.arguments
            .iter()
            .find(|a| a.name == "within")
            .ok_or(internal!("観測の変更範囲がない"))?
            .value,
    )?;
    inputs.push(within);
    let mut valid = true;
    let enabled = if g.get(within)?.ty == NodeType::Construction(T::ChangeRange) {
        let old = data(g, within)?;
        let origin = old
            .source
            .shared
            .as_ref()
            .ok_or(internal!("観測範囲の問題がない"))?;
        valid &= same_problem(&shared, origin);
        old.source
            .range
            .as_ref()
            .cloned()
            .or_else(|| old.source.ranges.get(&old.index).cloned())
            .ok_or(internal!("観測範囲の解禁単位がない"))?
    } else {
        let Scalar::Set { items, .. } = g.scalar(within)? else {
            return Err(internal!("観測範囲がSetでない").into());
        };
        valid &= items.iter().all(|v| {
            shared
                .compiled
                .subjects
                .iter()
                .position(|s| s == v)
                .is_some_and(|i| !shared.internal[i])
        });
        shared
            .compiled
            .subjects
            .iter()
            .map(|v| items.contains(v))
            .collect()
    };
    if !valid {
        return rejected(g, r, shared, inputs);
    }
    let mut fixed = env
        .try_primitive_valuation_from(&shared.compiled.fixed, c)?
        .ok_or(internal!("観測問題の基準が不適合"))?;
    fixed.select_local_object(&shared.witness, c)?;
    let mut support = BTreeSet::new();
    let mut scope = Scope::default();
    let (reader, bindings, allowed, reading) = match &r.head {
        Selector::Declaration { name } => {
            let mut bindings = vec![];
            for argument in &r.arguments {
                if let Some(name) = argument.name.strip_prefix("bind.") {
                    let value = change_search::selector(env, g, &argument.value)?;
                    if matches!(argument.value, Selector::Answer { .. }) {
                        inputs.push(reference(env, g, &argument.value)?);
                    }
                    bindings.push((name.to_owned(), value));
                }
            }
            let mut allowed = BTreeSet::new();
            for index in 0..family.points.len() {
                tick(c)?;
                let updated = family.environment(&fixed, index)?;
                let probe = family::read(&updated, name, &bindings)?;
                if probe.failed {
                    return rejected(g, r, shared, inputs);
                }
                if probe.blocked {
                    return unready(
                        env,
                        g,
                        r,
                        shared,
                        inputs,
                        (name.clone(), bindings),
                        probe.missing,
                    );
                }
                for fact in probe.support.iter().chain(&probe.missing) {
                    if let Some(i) = family.fields.iter().position(|f| {
                        crate::observed::environment::repair_problem::same_slot(f, fact)
                    }) {
                        allowed.insert(i);
                    }
                }
                support.extend(probe.support);
                scope.merge(&probe.scope);
            }
            (
                name.clone(),
                bindings,
                allowed.into_iter().collect::<Vec<_>>(),
                None,
            )
        }
        Selector::Answer { .. } => {
            let old = reference(env, g, &r.head)?;
            inputs.push(old);
            let old = data(g, old)?;
            let origin = old
                .source
                .shared
                .as_ref()
                .ok_or(internal!("読取りplanの元問題がない"))?;
            valid &= same_problem(&shared, origin);
            let state = old
                .source
                .observation
                .as_ref()
                .ok_or(internal!("読取りplanの生成情報がない"))?;
            (
                state.reader.clone(),
                state.bindings.clone(),
                state.readings.clone(),
                Some(inputs[inputs.len() - 1]),
            )
        }
        _ => return Err(internal!("観測の読取り指定が不正").into()),
    };
    if !valid {
        return rejected(g, r, shared, inputs);
    }
    let goal = match &r
        .arguments
        .iter()
        .find(|a| a.name == "output")
        .ok_or(internal!("観測の目的がない"))?
        .value
    {
        Selector::Enum { value } if value == "decision" => Goal::Decision,
        Selector::Enum { value } if value == "assignment" => Goal::Assignment,
        _ => return Err(internal!("観測の目的が不正").into()),
    };
    let reduced = reduce(&shared, &allowed, &enabled, goal, c)?;
    let sufficient = reduced.analysis.sufficient();
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let range = range(&mut b, &shared, &enabled)?;
    let mut arguments = vec![problem, range, input_domain];
    let reading = if let Some(old) = reading {
        arguments.push(old);
        Json::obj([("plan", old.wire())])
    } else {
        let mut wire = vec![];
        for (name, value) in &bindings {
            let at = change_result::value(&mut b, value)?;
            arguments.push(at);
            wire.push(Json::obj([("name", Json::str(name)), ("value", at.wire())]));
        }
        Json::obj([("view", Json::str(&reader)), ("bindings", Json::Arr(wire))])
    };
    let mut cases = vec![];
    for group in &reduced.analysis.groups {
        let (domain, values) = fiber(
            &mut b,
            &family,
            input_domain,
            &reduced.readings,
            group.indices[0],
        )?;
        arguments.push(domain);
        arguments.extend(values.iter().copied());
        let mut fields = vec![
            ("values".to_owned(), refs(&values)),
            ("inputs".into(), domain.wire()),
        ];
        if let Some(possible) = group.possible {
            let prop = named(
                &mut b,
                "repair_possible",
                vec![problem, range, domain],
                possible,
            )?;
            fields.push(("possible".into(), prop.wire()));
            arguments.push(prop);
        }
        if let Some(common) = group.common {
            let prop = named(
                &mut b,
                "common_repair",
                vec![problem, range, domain],
                common,
            )?;
            fields.push(("common".into(), prop.wire()));
            arguments.push(prop);
        }
        cases.push(Json::Obj(fields.into_iter().collect()));
    }
    let mut counterexamples = vec![];
    let mut point_refs = BTreeMap::new();
    let mut proofs = BTreeMap::new();
    for example in &reduced.analysis.witnesses {
        let (wire, proof) = witness(
            &mut b,
            &shared,
            range,
            &reduced.readings,
            example,
            &mut point_refs,
        )?;
        counterexamples.push(wire);
        arguments.push(proof);
    }
    for (field, example) in &reduced.necessary {
        let readings = reduced
            .readings
            .iter()
            .copied()
            .filter(|i| i != field)
            .collect::<Vec<_>>();
        let (wire, proof) = witness(&mut b, &shared, range, &readings, example, &mut point_refs)?;
        counterexamples.push(wire);
        arguments.push(proof);
        proofs.insert(*field, proof);
    }
    let status = if sufficient {
        Decision::Established
    } else {
        Decision::Refuted
    };
    let claim = condition(&mut b, r, arguments.clone(), status)?;
    arguments.push(claim);
    let mut outputs = BTreeMap::new();
    let mut solution = None;
    if sufficient && goal == Goal::Assignment && reduced.readings.is_empty() {
        let at = b.push(
            NodeType::Construction(T::SolutionSet),
            "solution_set",
            Json::obj([
                ("domain", shared.domain.wire()),
                ("requirements", refs(&shared.requirements)),
                (
                    "representation",
                    Json::obj([
                        ("kind", Json::str("factored")),
                        ("problem", problem.wire()),
                        ("range", range.wire()),
                    ]),
                ),
            ]),
            [
                vec![shared.domain, problem, range],
                shared.requirements.clone(),
            ]
            .concat(),
            None,
        )?;
        outputs.insert("solutions".into(), at);
        solution = Some(at);
        arguments.push(at);
    }
    let declaration = &env.indexes.inputs.law().declarations()[&reader];
    let locations = Json::Arr(vec![archsig_input::result::location_wire(
        &archsig_common::issue::Location::Law {
            span: declaration.span,
        },
    )]);
    let requirements = reduced
        .readings
        .iter()
        .map(|i| {
            Json::obj([
                ("field", family.fields[*i].wire()),
                (
                    "dependents",
                    refs(&proofs.get(i).copied().into_iter().collect::<Vec<_>>()),
                ),
                ("locations", locations.clone()),
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
        ("cases".into(), Json::Arr(cases)),
        ("counterexamples".into(), Json::Arr(counterexamples)),
    ];
    if let Some(solution) = solution {
        fields.push(("solutions".into(), solution.wire()));
    }
    let plan = b.push(
        NodeType::Construction(T::RepairObservation),
        "repair_observation",
        Json::Obj(fields.into_iter().collect()),
        arguments,
        None,
    )?;
    b.parts[plan.0 - base].support.extend(support);
    b.parts[plan.0 - base].scope.merge(&scope);
    b.parts[plan.0 - base].support.sort();
    b.parts[plan.0 - base].support.dedup();
    outputs.insert("plan".into(), plan);
    let mut a = answer(r, claim, status, outputs, &b);
    if !sufficient {
        fail(&mut a, "observe");
    }
    Ok(Source {
        base,
        parts: b.parts,
        answer: a,
        request: r.clone(),
        witness: shared.witness.clone(),
        shared: Some(shared),
        range: Some(enabled),
        ranges: BTreeMap::new(),
        chosen: None,
        inputs,
        context: g.active,
        observation: Some(Arc::new(State {
            reader,
            bindings,
            readings: reduced.readings,
        })),
    })
}

fn unready(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    shared: Arc<Shared>,
    inputs: Vec<NodeRef>,
    reading: (String, Vec<(String, Scalar)>),
    missing: Vec<Fact>,
) -> Result<Source, ValidationFailure> {
    let (reader, bindings) = reading;
    let declaration = &env.indexes.inputs.law().declarations()[&reader];
    let Signature::View { returns, body, .. } = &declaration.signature else {
        unreachable!()
    };
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let mut values = vec![];
    for (name, value) in &bindings {
        values.push((name.clone(), change_result::value(&mut b, value)?));
    }
    let expression = change_result::source_expression(&mut b, env, *body, &values, &[])?;
    b.parts[expression.0 - base]
        .arguments
        .extend(inputs.iter().copied());
    let claim = condition(&mut b, r, inputs.clone(), Decision::Undetermined)?;
    let mut a = answer(r, claim, Decision::Undetermined, BTreeMap::new(), &b);
    a.reasons.push(Reason {
        kind: if missing.is_empty() {
            ReasonKind::UnsupportedAlgorithm {
                question: r.kind,
                operand_types: vec![returns.clone()],
                method: "finite_repair_observation".into(),
            }
        } else {
            ReasonKind::Missing
        },
        request: r.id.clone(),
        dependencies: vec![expression],
        missing,
        location: Some(archsig_common::issue::Location::Law {
            span: declaration.span,
        }),
    });
    Ok(Source {
        base,
        parts: b.parts,
        answer: a,
        request: r.clone(),
        witness: shared.witness.clone(),
        shared: Some(shared),
        range: None,
        ranges: BTreeMap::new(),
        chosen: None,
        inputs,
        context: g.active,
        observation: None,
    })
}
pub(super) fn compute(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
) -> Result<Source, ValidationFailure> {
    match compute_inner(env, g, r, c) {
        Err(ValidationFailure::UnsupportedExpression { .. }) => {
            let problem = reference(
                env,
                g,
                &r.arguments
                    .iter()
                    .find(|a| a.name == "on")
                    .ok_or(internal!("未対応観測の問題がない"))?
                    .value,
            )?;
            let shared = data(g, problem)?
                .source
                .shared
                .as_ref()
                .ok_or(internal!("未対応観測の共有構成がない"))?
                .clone();
            let mut inputs = vec![problem];
            for argument in &r.arguments {
                if matches!(argument.value, Selector::Answer { .. }) {
                    inputs.push(reference(env, g, &argument.value)?);
                }
            }
            let (reader, bindings) = match &r.head {
                Selector::Declaration { name } => {
                    let mut bindings = vec![];
                    for a in &r.arguments {
                        if let Some(name) = a.name.strip_prefix("bind.") {
                            bindings.push((
                                name.to_owned(),
                                change_search::selector(env, g, &a.value)?,
                            ));
                        }
                    }
                    (name.clone(), bindings)
                }
                Selector::Answer { .. } => {
                    let old = reference(env, g, &r.head)?;
                    inputs.push(old);
                    let state = data(g, old)?
                        .source
                        .observation
                        .as_ref()
                        .ok_or(internal!("未対応観測の元planがない"))?;
                    (state.reader.clone(), state.bindings.clone())
                }
                _ => return Err(internal!("未対応観測の読取りがない").into()),
            };
            unready(env, g, r, shared, inputs, (reader, bindings), vec![])
        }
        result => result,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(dead_code)]
    mod repair_problem_data {
        include!("../../../../../tests/common/repair_problem_data.rs");
    }
    #[allow(dead_code)]
    mod observation_fixture {
        include!("../../../../../tests/common/repair_observation_data.rs");
    }
    use observation_fixture::input;
    fn shared(result: &crate::observed::ObservedEvaluation) -> Arc<Shared> {
        let Some(Payload::Construction(v)) = &result.nodes[result
            .answers
            .iter()
            .find_map(|a| a.outputs.get("problem"))
            .copied()
            .unwrap()
            .0]
            .payload
        else {
            panic!("問題")
        };
        let D::SharedRepair(d) = &v.data else {
            panic!("共有問題")
        };
        d.source.shared.as_ref().unwrap().clone()
    }
    #[test]
    fn decision_and_assignment_readings_differ_and_known_information_removes_the_requirement() {
        for known in [false, true] {
            let input = input(
                "view input(r:Root):Bool=r.h;change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):forall c in Part[r]. c.flag=r.h;",
                "\"Bool\"",
                known.then_some("false"),
            );
            let c = archsig_common::control::quiet();
            let result=super::super::super::evaluate_observed_bytes(input,&["p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)"],&c).unwrap();
            let shared = shared(&result);
            let enabled = vec![true; shared.subjects.len()];
            let (family, _) = shared.family.as_ref().unwrap();
            let allowed = (0..family.fields.len()).collect::<Vec<_>>();
            let decision = reduce(&shared, &allowed, &enabled, Goal::Decision, &c).unwrap();
            assert!(decision.analysis.sufficient());
            assert!(decision.readings.is_empty());
            assert_eq!(decision.analysis.groups[0].possible, Some(true));
            let assignment = reduce(&shared, &allowed, &enabled, Goal::Assignment, &c).unwrap();
            assert!(assignment.analysis.sufficient());
            assert_eq!(assignment.readings.len(), usize::from(!known));
            let without = analyze(&shared, &[], &enabled, Goal::Assignment, &c).unwrap();
            assert_eq!(without.sufficient(), known);
            if !known {
                assert_eq!(without.witnesses[0].kind, "no_common_assignment");
                assert_eq!(without.witnesses[0].indices.len(), 2);
            }
        }
    }
    #[test]
    fn pairwise_repairs_do_not_replace_the_intersection_of_the_whole_input_group() {
        let inputs = input(
            "view input(r:Root):Fp(3)=r.h;change choose(c:Part,p:Fp(3))=c with {label=if p=0 then \"a\" else if p=1 then \"b\" else \"c\"};law required valid(r:Root):forall c in Part[r]. if r.h=0 then (c.label=\"a\" or c.label=\"b\") else if r.h=1 then (c.label=\"b\" or c.label=\"c\") else (c.label=\"a\" or c.label=\"c\");",
            r#"["Fp","3"]"#,
            None,
        );
        let c = archsig_common::control::quiet();
        let result=super::super::super::evaluate_observed_bytes(inputs,&["p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)"],&c).unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        let shared = shared(&result);
        let enabled = vec![true; shared.subjects.len()];
        for pair in [&[0, 1][..], &[0, 2], &[1, 2]] {
            assert!(common_exists(&shared, pair, &enabled, &c).unwrap());
        }
        let insufficient = analyze(&shared, &[], &enabled, Goal::Assignment, &c).unwrap();
        assert!(!insufficient.sufficient());
        assert_eq!(insufficient.witnesses[0].indices.len(), 3);
        assert!(
            reduce(&shared, &[], &enabled, Goal::Decision, &c)
                .unwrap()
                .analysis
                .sufficient()
        );
        let enough = reduce(&shared, &[0], &enabled, Goal::Assignment, &c).unwrap();
        assert_eq!(enough.readings, vec![0]);
        assert!(enough.analysis.sufficient());
    }
    #[test]
    fn public_observe_reuses_the_problem_and_constructs_after_the_input_is_observed() {
        for known in [false, true] {
            let input = input(
                "view input(r:Root):Bool=r.h;view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):forall c in Part[r]. c.flag=r.h;",
                "\"Bool\"",
                known.then_some("false"),
            );
            let mut asks = vec![
                "u=evaluate(Selected.all,r=@v/root)",
                "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)",
                "d=observe(Selected.input,on=$p.problem,within=$u.value,output=decision,r=@v/root)",
                "a=observe(Selected.input,on=$p.problem,within=$u.value,output=assignment,r=@v/root)",
                "again=observe($a.plan,on=$a.plan.problem,within=$u.value,output=decision)",
            ];
            if known {
                asks.extend([
                    "c=candidate($a.solutions,index=0)",
                    "ap=apply($c.assignment,in=$a.solutions)",
                    "ok=check(Selected.valid,on=$ap.object,r=@v/root)",
                ]);
            }
            let result = super::super::super::evaluate_observed_bytes(
                input,
                &asks,
                &archsig_common::control::quiet(),
            )
            .unwrap();
            assert_eq!(result.status(), "complete", "{:?}", result.issues);
            for answer in &result.answers {
                assert_eq!(
                    answer.status,
                    Decision::Established,
                    "{} {:?}",
                    answer.id,
                    answer.reasons
                );
            }
            let plans = [(2, 0), (3, usize::from(!known)), (4, 0)];
            for (at, count) in plans {
                let Some(Payload::Construction(v)) =
                    &result.nodes[result.answers[at].outputs["plan"].0].payload
                else {
                    panic!()
                };
                let D::SharedRepair(data) = &v.data else {
                    panic!()
                };
                assert_eq!(
                    data.source.observation.as_ref().unwrap().readings.len(),
                    count
                );
            }
            assert_eq!(result.answers[3].outputs.contains_key("solutions"), known);
            assert!(!result.answers[2].outputs.contains_key("solutions"));
        }
    }

    #[test]
    fn common_assignment_does_not_turn_input_dependent_target_values_into_observations() {
        let input = input(
            "view input(r:Root):Bool=r.h;view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=if p then c.owner.h else false};law required valid(r:Root):true;",
            "\"Bool\"",
            None,
        );
        let asks = [
            "u=evaluate(Selected.all,r=@v/root)",
            "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)",
            "a=observe(Selected.input,on=$p.problem,within=$u.value,output=assignment,r=@v/root)",
            "first=candidate($a.solutions,index=0)",
            "good=apply($first.assignment,in=$a.solutions)",
            "second=candidate($a.solutions,index=1)",
            "pending=apply($second.assignment,in=$a.solutions)",
            "blocked=check(Selected.valid,on=$pending.object,r=@v/root)",
            "later=check(Selected.valid,r=@v/root)",
            "still=evaluate(Selected.input,on=$good.object,r=@v/root)",
        ];
        let result = super::super::super::evaluate_observed_bytes(
            input,
            &asks,
            &archsig_common::control::quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "partial", "{:?}", result.issues);
        assert_eq!(result.answers[4].status, Decision::Established);
        assert_eq!(result.answers[6].status, Decision::Undetermined);
        assert!(!result.answers[6].outputs.contains_key("object"));
        assert!(result.answers[6].reasons.iter().any(|r| {
            matches!(r.kind, ReasonKind::Missing)
                && r.missing
                    .iter()
                    .any(|f| f.field.as_deref() == Some("Pattern.Root.h"))
        }));
        assert_eq!(result.answers[7].status, Decision::Undetermined);
        assert_eq!(result.answers[8].status, Decision::Established);
        assert_eq!(result.answers[9].status, Decision::Undetermined);
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
            "{:?}",
            result.issues
        );
    }

    #[test]
    fn assignments_rebind_original_parameters_across_input_families() {
        let input = input(
            "view input(r:Root):Bool=r.h;view wider(r:Root):(Bool,Bool)=(r.h,r.z);view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):forall c in Part[r]. r.h or c.flag;",
            "\"Bool\"",
            None,
        );
        let asks = [
            "u=evaluate(Selected.all,r=@v/root)",
            "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)",
            "a=observe(Selected.input,on=$p.problem,within=$u.value,output=assignment,r=@v/root)",
            "c=candidate($a.solutions,index=0)",
            "q=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.wider,r=@v/root)",
            "b=observe(Selected.wider,on=$q.problem,within=$u.value,output=assignment,r=@v/root)",
            "ap=apply($c.assignment,in=$b.solutions)",
            "ok=check(Selected.valid,on=$ap.object,r=@v/root)",
        ];
        let result = super::super::super::evaluate_observed_bytes(
            input,
            &asks,
            &archsig_common::control::quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(result.answers[6].status, Decision::Established);
        assert_eq!(result.answers[7].status, Decision::Established);
    }

    #[test]
    fn decision_difference_and_impossible_groups_have_distinct_witnesses() {
        for law in ["r.h", "false"] {
            let input = input(
                &format!(
                    "view input(r:Root):Bool=r.h;view uninformative(r:Root):Bool=true;view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {{flag=p}};law required valid(r:Root):{law};"
                ),
                "\"Bool\"",
                None,
            );
            let asks = [
                "u=evaluate(Selected.all,r=@v/root)",
                "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)",
                "a=observe(Selected.uninformative,on=$p.problem,within=$u.value,output=assignment,r=@v/root)",
            ];
            let result = super::super::super::evaluate_observed_bytes(
                input,
                &asks,
                &archsig_common::control::quiet(),
            )
            .unwrap();
            assert_eq!(
                result.answers[2].status,
                if law == "false" {
                    Decision::Established
                } else {
                    Decision::Refuted
                }
            );
            let shared = shared(&result);
            let analyzed = analyze(
                &shared,
                &[],
                &vec![true; shared.subjects.len()],
                Goal::Assignment,
                &archsig_common::control::quiet(),
            )
            .unwrap();
            if law == "false" {
                assert!(analyzed.witnesses.is_empty());
                assert_eq!(analyzed.groups[0].possible, Some(false));
            } else {
                assert_eq!(analyzed.witnesses[0].kind, "decision_difference");
                assert_eq!(analyzed.witnesses[0].indices.len(), 2);
            }
        }
    }
    #[test]
    fn nonfinite_input_is_pending_and_dependent_requests_do_not_become_internal_errors() {
        let input = input(
            "view input(r:Root):Text=r.h;view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):true;",
            "\"Text\"",
            None,
        );
        let asks = [
            "u=evaluate(Selected.all,r=@v/root)",
            "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)",
            "a=observe(Selected.input,on=$p.problem,within=$u.value,output=decision,r=@v/root)",
            "later=check(Selected.valid,r=@v/root)",
        ];
        let result = super::super::super::evaluate_observed_bytes(
            input,
            &asks,
            &archsig_common::control::quiet(),
        )
        .unwrap();
        assert_eq!(result.answers[1].status, Decision::Undetermined);
        assert!(!result.answers[1].outputs.contains_key("problem"));
        assert_eq!(result.answers[2].status, Decision::Undetermined);
        assert_eq!(
            result.answers[3].status,
            Decision::Established,
            "{:?}",
            result.issues
        );
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
            "{:?}",
            result.issues
        );
    }
    #[test]
    fn observation_plan_keeps_problem_identity_and_closed_argument_types() {
        let body = "view input(r:Root):Bool=r.h;view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):forall c in Part[r]. c.flag=r.h;law required other(r:Root):true;";
        let asks = [
            "u=evaluate(Selected.all,r=@v/root)",
            "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)",
            "a=observe(Selected.input,on=$p.problem,within=$u.value,output=assignment,r=@v/root)",
            "q=prepare(Selected.other,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)",
            "bad=observe($a.plan,on=$q.problem,within=$u.value,output=assignment)",
            "later=check(Selected.other,r=@v/root)",
        ];
        let result = super::super::super::evaluate_observed_bytes(
            input(body, "\"Bool\"", None),
            &asks,
            &archsig_common::control::quiet(),
        )
        .unwrap();
        assert_eq!(result.answers[4].status, Decision::Refuted);
        assert!(!result.answers[4].outputs.contains_key("plan"));
        assert_eq!(result.answers[5].status, Decision::Established);
        for invalid in [
            "bad=observe(Selected.input,on=$p.problem,within=$u.value,output=other,r=@v/root)",
            "bad=observe(Selected.input,on=$p.problem,within=$u.value,output=decision)",
            "bad=observe(Selected.input,on=$p.problem,within=$u.value,output=decision,r=@v/v)",
            "bad=observe($a.plan,on=$p.problem,within=$u.value,output=decision,r=@v/root)",
        ] {
            let mut requests = asks[..3].to_vec();
            requests.push(invalid);
            assert!(
                super::super::super::evaluate_observed_bytes(
                    input(body, "\"Bool\"", None),
                    &requests,
                    &archsig_common::control::quiet()
                )
                .is_err(),
                "{invalid}"
            );
        }
    }
    #[test]
    fn observation_reduction_preserves_cooperative_interruption() {
        use std::{cell::Cell, rc::Rc};
        let input = input(
            "view input(r:Root):Bool=r.h;change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):forall c in Part[r]. c.flag=r.h;",
            "\"Bool\"",
            None,
        );
        let result=super::super::super::evaluate_observed_bytes(input,&["p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)"],&archsig_common::control::quiet()).unwrap();
        let shared = shared(&result);
        let run = |stop: Option<usize>| {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let c = Control::new(move |_| {
                seen.set(seen.get() + 1);
                stop.filter(|n| *n == seen.get())
                    .map(|_| archsig_common::control::Signal::Term)
            });
            let result = reduce(
                &shared,
                &[0],
                &vec![true; shared.subjects.len()],
                Goal::Assignment,
                &c,
            );
            (result, count.get())
        };
        let (result, count) = run(None);
        assert!(result.unwrap().analysis.sufficient());
        for at in 1..=count {
            assert!(
                matches!(run(Some(at)).0, Err(ValidationFailure::Stop(_))),
                "checkpoint {at}"
            );
        }
    }
}
