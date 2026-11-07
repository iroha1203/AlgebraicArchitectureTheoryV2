//! 同じRepairProblemの整数fiber・範囲・元Assignmentを通常の構成へ渡す。
use super::*;
use crate::observed::{
    environment::repair_problem::integer::Compiled,
    integer_fiber::{self, projection::Projection},
};
use num_bigint::BigInt as Z;
mod legacy;
mod output;
use output::{
    PublicModel, apply_object, assignment_value, known_public, publish_model, render_solutions,
};
mod prepare;
use legacy::legacy;
pub(super) use prepare::{is_prepare, prepare};
#[derive(Debug)]
pub(super) struct Shared {
    pub compiled: Arc<Compiled>,
    pub projection: Option<Arc<Projection>>,
    pub witness: Arc<ArchitectureWitness>,
    pub base: NodeRef,
    pub domain: NodeRef,
    pub problem: Option<NodeRef>,
    pub subjects: Vec<NodeRef>,
    pub requirements: Vec<NodeRef>,
    pub internal: Vec<bool>,
    pub unit_rows: Vec<Vec<usize>>,
    pub ring: NodeRef,
    pub parameter_module: NodeRef,
    pub action: NodeRef,
    pub root_type: String,
}
#[derive(Debug)]
pub(super) struct State {
    pub shared: Arc<Shared>,
    pub parameters: Option<Vec<Z>>,
    pub range_result: Option<Arc<RangeMath>>,
    pub solutions: Option<NodeRef>,
    pub public_model: Option<Arc<PublicModel>>,
    pub input_key: Vec<NodeRef>,
}

/// 商から明示的に求められた元parameterの全fiber。公開JSONでなく検査済みownerを保持する。
pub(in crate::observed) struct Family {
    shared: Arc<Shared>,
    range: Arc<RangeMath>,
}
impl Family {
    pub(in crate::observed) fn particular(
        &self,
        c: &Control,
    ) -> Result<Option<Vec<Z>>, ValidationFailure> {
        match (
            self.range.as_ref(),
            &self.shared.projection,
            &self.shared.compiled.linear.particular,
        ) {
            (RangeMath::Constrained { fiber, .. }, Some(projection), Some(origin)) => projection
                .candidate(
                    origin,
                    &self.shared.compiled.linear.kernel,
                    fiber,
                    &0u32.into(),
                    c,
                ),
            (RangeMath::Empty, _, _) => Ok(None),
            _ => Err(internal!("商へ渡す整数全fiberが対応しない").into()),
        }
    }
    pub(in crate::observed) fn dimensions(&self) -> Result<usize, ValidationFailure> {
        match (self.range.as_ref(), &self.shared.projection) {
            (RangeMath::Constrained { fiber, .. }, Some(projection)) => projection.free(fiber),
            (RangeMath::Empty, _) => Ok(0),
            _ => Err(internal!("商へ渡す整数全fiberが対応しない").into()),
        }
    }
    pub(in crate::observed) fn column(
        &self,
        j: usize,
        c: &Control,
    ) -> Result<Vec<Z>, ValidationFailure> {
        match (self.range.as_ref(), &self.shared.projection) {
            (RangeMath::Constrained { fiber, .. }, Some(projection)) => {
                projection.kernel_column(&self.shared.compiled.linear.kernel, fiber, j, c)
            }
            _ => Err(internal!("空の整数全fiberには核列がない").into()),
        }
    }
}
pub(super) fn candidate_input(
    state: &State,
    ty: NodeType,
) -> Result<change_result::CandidateInput, ValidationFailure> {
    let shared = &state.shared;
    let domain_type = match ty {
        NodeType::Construction(T::SolutionSet) => {
            ProjectionType::SolutionSet(shared.root_type.clone())
        }
        NodeType::Construction(T::CandidateSpace) => {
            ProjectionType::CandidateSpace(shared.root_type.clone())
        }
        _ => return Err(internal!("整数商の定義域の型が違う").into()),
    };
    let integer_family = if matches!(domain_type, ProjectionType::SolutionSet(_)) {
        Some(Family {
            shared: shared.clone(),
            range: state
                .range_result
                .clone()
                .ok_or(internal!("整数商の解集合に全fiberがない"))?,
        })
    } else {
        None
    };
    Ok(change_result::CandidateInput {
        architecture: shared.base,
        witness: shared.witness.clone(),
        domain_type,
        integer_family,
        search: change_search::Search {
            linear: Some(shared.compiled.linear.clone()),
            rational: None,
            pending_integer: None,
            candidates: None,
            solutions: vec![],
            requirements: shared.compiled.requirements.clone(),
            bindings: shared.compiled.bindings.clone(),
            missing: vec![],
            complete: true,
            valuation: shared.compiled.fixed.clone(),
        },
    })
}
pub(super) fn assignment_input(
    state: &State,
) -> Result<change_result::AssignmentInput, ValidationFailure> {
    let s = &state.shared;
    let parameters = state
        .parameters
        .as_ref()
        .ok_or(internal!("整数の元Assignmentがない"))?;
    let width = if s.compiled.subjects.is_empty() {
        0
    } else {
        s.compiled.linear.parameter_count / s.compiled.subjects.len()
    };
    let entries = s
        .compiled
        .subjects
        .iter()
        .enumerate()
        .map(|(i, subject)| {
            (
                subject.clone(),
                parameters[i * width..(i + 1) * width]
                    .iter()
                    .cloned()
                    .map(Scalar::Z)
                    .collect(),
            )
        })
        .collect();
    Ok(change_result::AssignmentInput {
        domain: s.domain,
        entries,
    })
}

fn find<T: PartialEq>(
    values: &[T],
    value: &T,
    c: &Control,
) -> Result<Option<usize>, ValidationFailure> {
    for (i, other) in values.iter().enumerate() {
        tick(c)?;
        if other == value {
            return Ok(Some(i));
        }
    }
    Ok(None)
}
fn entity_mask(
    subjects: &[Scalar],
    values: &[Scalar],
    c: &Control,
) -> Result<Option<Vec<bool>>, ValidationFailure> {
    let mut mask = vec![false; subjects.len()];
    for value in values {
        let Some(i) = find(subjects, value, c)? else {
            return Ok(None);
        };
        mask[i] = true;
    }
    Ok(Some(mask))
}
fn fixed_equal(
    a: &[(Fact, Scalar)],
    b: &[(Fact, Scalar)],
    c: &Control,
) -> Result<bool, ValidationFailure> {
    if a.len() != b.len() {
        return Ok(false);
    };
    for ((af, av), (bf, bv)) in a.iter().zip(b) {
        tick(c)?;
        if af != bf || !crate::observed::data::equal(av, bv, c)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn bindings_equal(
    a: &[(String, Scalar)],
    b: &BTreeMap<String, Scalar>,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    if a.len() != b.len() {
        return Ok(false);
    };
    for (name, value) in a {
        tick(c)?;
        let Some(other) = b.get(name) else {
            return Ok(false);
        };
        if !crate::observed::data::equal(value, other, c)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn wrap(
    b: Builder<'_>,
    answer: Answer,
    r: &Request,
    witness: Arc<ArchitectureWitness>,
    shared: Option<Arc<Shared>>,
    inputs: Vec<NodeRef>,
) -> Source {
    let context = b.g.active;
    Source {
        base: b.base,
        parts: b.parts,
        answer,
        request: r.clone(),
        witness,
        shared: shared.map(|shared| {
            Backend::Integer(State {
                shared,
                parameters: None,
                range_result: None,
                solutions: None,
                public_model: None,
                input_key: vec![],
            })
        }),
        range: None,
        ranges: BTreeMap::new(),
        chosen: None,
        inputs,
        context,
        observation: None,
    }
}

#[derive(Debug)]
pub(super) enum RangeMath {
    Empty,
    Constrained {
        coefficients: Arc<integer_fiber::reuse::Entry>,
        rhs: Vec<Z>,
        fiber: integer_fiber::Fiber,
    },
}
impl RangeMath {
    fn exists(&self) -> bool {
        matches!(self,Self::Constrained{fiber,..}if fiber.particular.is_some())
    }
}
type FixedRows = Result<Vec<(usize, Z)>, Vec<Fact>>;
fn fixed(shared: &Shared, enabled: &[bool], c: &Control) -> Result<FixedRows, ValidationFailure> {
    if enabled.len() != shared.internal.len() {
        return Err(internal!("整数範囲の単位数が違う").into());
    }
    let Some(projection) = &shared.projection else {
        return Ok(Ok(vec![]));
    };
    let mut rows = vec![false; projection.shared_rows.len()];
    for (i, unit) in shared.unit_rows.iter().enumerate() {
        tick(c)?;
        if !shared.internal[i] && !enabled[i] {
            for row in unit {
                tick(c)?;
                rows[*row] = true;
            }
        }
    }
    let mut fixed = vec![];
    let mut missing = vec![];
    for (row, on) in rows.iter().enumerate() {
        tick(c)?;
        if *on {
            let at = projection.shared_rows[row];
            if let Some(value) = &shared.compiled.baselines[at] {
                fixed.push((row, value.clone()));
            } else {
                missing.push(shared.compiled.linear.slots[at].clone());
            }
        }
    }
    Ok(if missing.is_empty() {
        Ok(fixed)
    } else {
        Err(missing)
    })
}
fn resolve_range(
    env: &Environment<'_>,
    shared: &Shared,
    enabled: &[bool],
    c: &Control,
) -> Result<Result<Arc<RangeMath>, Vec<Fact>>, ValidationFailure> {
    let Some(projection) = &shared.projection else {
        return Ok(Ok(Arc::new(RangeMath::Empty)));
    };
    let fixed = match fixed(shared, enabled, c)? {
        Ok(v) => v,
        Err(v) => return Ok(Err(v)),
    };
    let (matrix, rhs) = projection.constraints(&fixed, c)?;
    let coefficients = integer_fiber::reuse::factor(
        &env.results.integer_factors,
        matrix,
        projection.visible(),
        c,
    )?;
    let fiber = integer_fiber::restore(coefficients.decomposition().clone(), &rhs, c)?;
    Ok(Ok(Arc::new(RangeMath::Constrained {
        coefficients,
        rhs,
        fiber,
    })))
}
fn range_value(
    b: &mut Builder<'_>,
    s: &Shared,
    enabled: &[bool],
    inputs: &[NodeRef],
) -> Result<NodeRef, ValidationFailure> {
    let origin = Witness::Architecture(s.witness.clone());
    let declaration = &origin.inputs().law().declarations()[&s.compiled.change];
    let Signature::Change { params, .. } = &declaration.signature else {
        unreachable!()
    };
    let values = s
        .subjects
        .iter()
        .zip(enabled)
        .filter_map(|(r, on)| on.then_some(*r))
        .collect::<Vec<_>>();
    let enabled = super::domain(b, &params[0].ty.erase(), &values)?;
    let problem = s.problem.ok_or(internal!("整数修復問題の参照がない"))?;
    b.push(
        NodeType::Construction(T::ChangeRange),
        "change_range",
        Json::obj([("problem", problem.wire()), ("enabled", enabled.wire())]),
        [vec![problem, enabled], inputs.to_vec()].concat(),
        None,
    )
}
fn same_domain(a: &Shared, b: &Shared, c: &Control) -> Result<bool, ValidationFailure> {
    if a.witness.construction().root() != b.witness.construction().root()
        || a.witness.construction().reading() != b.witness.construction().reading()
        || a.compiled.change != b.compiled.change
        || a.compiled.subjects.len() != b.compiled.subjects.len()
        || a.compiled.bindings.len() != b.compiled.bindings.len()
    {
        return Ok(false);
    };
    if !fixed_equal(&a.compiled.fixed, &b.compiled.fixed, c)? {
        return Ok(false);
    };
    for (a, b) in a.compiled.subjects.iter().zip(&b.compiled.subjects) {
        tick(c)?;
        if a != b {
            return Ok(false);
        }
    }
    for (name, value) in &a.compiled.bindings {
        let mut other = None;
        for (key, scalar) in &b.compiled.bindings {
            tick(c)?;
            if key == name {
                other = Some(scalar);
                break;
            }
        }
        let Some(other) = other else { return Ok(false) };
        if !crate::observed::data::equal(value, other, c)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn mask(
    env: &Environment<'_>,
    g: &mut Graph,
    s: &Shared,
    selector: &Selector,
) -> Result<(NodeRef, Option<Vec<bool>>), ValidationFailure> {
    let at = reference(env, g, selector)?;
    if g.get(at)?.ty == NodeType::Construction(T::ChangeRange) {
        let d = data(g, at)?;
        let Some(other) = d.source.integer() else {
            return Ok((at, None));
        };
        if s.problem != other.shared.problem || !same_domain(s, &other.shared, &env.control)? {
            return Ok((at, None));
        }
        return Ok((
            at,
            d.source
                .range
                .clone()
                .or_else(|| d.source.ranges.get(&d.index).cloned()),
        ));
    }
    let Scalar::Set { items, .. } = g.scalar(at)? else {
        return Err(internal!("整数変更範囲がSetでない").into());
    };
    let Some(mask) = entity_mask(&s.compiled.subjects, items, &env.control)? else {
        return Ok((at, None));
    };
    for (on, internal) in mask.iter().zip(&s.internal) {
        tick(&env.control)?;
        if *on && *internal {
            return Ok((at, None));
        }
    }
    Ok((at, Some(mask)))
}
type KnownRange = (Arc<RangeMath>, Option<NodeRef>);
fn known_range(
    g: &Graph,
    shared: &Arc<Shared>,
    enabled: &[bool],
    inputs: &[NodeRef],
    need_display: bool,
    c: &Control,
) -> Result<Option<KnownRange>, ValidationFailure> {
    let mut known = None;
    for node in &g.nodes {
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
        let Some(state) = d.source.integer() else {
            continue;
        };
        if Arc::ptr_eq(&state.shared, shared)
            && d.source.range.as_deref() == Some(enabled)
            && let Some(math) = &state.range_result
        {
            let display = (state.input_key == inputs)
                .then_some(state.solutions)
                .flatten();
            known = Some((math.clone(), display));
            if !need_display || display.is_some() {
                return Ok(known);
            }
        }
    }
    Ok(known)
}

struct Checked {
    candidate: change_evaluation::Candidate,
    member: Option<bool>,
    missing: Vec<Fact>,
}
fn check_candidate(
    env: &Environment<'_>,
    shared: &Shared,
    enabled: &[bool],
    parameters: &[Z],
    c: &Control,
) -> Result<Checked, ValidationFailure> {
    let mut current = env
        .try_primitive_valuation_from(&shared.compiled.fixed, c)?
        .ok_or(internal!("整数候補の基準代入が不適合"))?;
    current.select_local_object(&shared.witness, c)?;
    let origin = Witness::Architecture(shared.witness.clone());
    let change = &origin.inputs().law().declarations()[&shared.compiled.change];
    let values = parameters
        .iter()
        .cloned()
        .map(Scalar::Z)
        .collect::<Vec<_>>();
    let candidate =
        change_evaluation::candidate(&current, change, &shared.compiled.subjects, &values)?;
    let row =
        change_evaluation::solution_row(&current, &candidate, 0, &shared.compiled.requirements)?;
    let mut missing = candidate.update.missing.clone();
    missing.extend(row.missing);
    if row.member != Some(true) {
        return Ok(Checked {
            candidate,
            member: row.member,
            missing,
        });
    }
    let mut predicted = integer_fiber::apply(&shared.compiled.linear.action, parameters, c)?;
    for (v, k) in predicted.iter_mut().zip(&shared.compiled.linear.offset) {
        tick(c)?;
        *v += k;
    }
    if candidate.update.values.len() != shared.compiled.linear.slots.len() {
        return Err(internal!("整数候補の更新先族が元式と違う").into());
    }
    for (slot, value) in shared.compiled.linear.slots.iter().zip(&predicted) {
        tick(c)?;
        let actual = candidate
            .update
            .values
            .iter()
            .find(|(fact, _)| crate::observed::environment::repair_problem::same_slot(fact, slot))
            .ok_or(internal!("整数候補の更新先がない"))?;
        if !matches!(&actual.1,Scalar::Z(z)if z==value) {
            return Err(internal!("整数候補の復元値が元更新式と違う").into());
        }
    }
    let member = if let Some(projection) = &shared.projection {
        match fixed(shared, enabled, c)? {
            Ok(fixed) => Some(
                fixed
                    .iter()
                    .all(|(row, value)| predicted[projection.shared_rows[*row]] == *value),
            ),
            Err(facts) => {
                missing.extend(facts);
                None
            }
        }
    } else {
        Some(false)
    };
    Ok(Checked {
        candidate,
        member,
        missing,
    })
}

pub(super) fn consume_at(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
    head: NodeRef,
) -> Result<Option<Source>, ValidationFailure> {
    let d = match data(g, head) {
        Ok(d) => d,
        Err(_) if r.kind == QuestionKind::Candidate => {
            let Some(shared) = legacy(env, g, head, c)? else {
                return Ok(None);
            };
            let enabled = vec![true; shared.subjects.len()];
            return consume(
                env,
                g,
                r,
                c,
                Operand {
                    head,
                    shared,
                    range: Some(enabled),
                    parameters: None,
                },
            )
            .map(Some);
        }
        Err(_) if r.kind == QuestionKind::Apply => {
            let input = change_result::assignment_input(env, g, head)?;
            let Some(shared) = legacy(env, g, input.domain, c)? else {
                return Ok(None);
            };
            let mut parameters = vec![];
            for subject in &shared.compiled.subjects {
                tick(c)?;
                let Some((_, values)) = input.entries.iter().find(|(s, _)| s == subject) else {
                    return Err(internal!("整数元割当てのinstanceがない").into());
                };
                for value in values {
                    tick(c)?;
                    let Scalar::Z(value) = value else {
                        return Err(internal!("整数元割当ての値がZでない").into());
                    };
                    parameters.push(value.clone());
                }
            }
            return consume(
                env,
                g,
                r,
                c,
                Operand {
                    head,
                    shared,
                    range: None,
                    parameters: Some(parameters),
                },
            )
            .map(Some);
        }
        Err(_) => return Ok(None),
    };
    let Some(state) = d.source.integer() else {
        return Ok(None);
    };
    let shared = state.shared.clone();
    let parameters = if r.kind == QuestionKind::Apply {
        state.parameters.clone()
    } else {
        None
    };
    let inherited = d
        .source
        .range
        .clone()
        .or_else(|| d.source.ranges.get(&d.index).cloned());
    consume(
        env,
        g,
        r,
        c,
        Operand {
            head,
            shared,
            range: inherited,
            parameters,
        },
    )
    .map(Some)
}
struct Operand {
    head: NodeRef,
    shared: Arc<Shared>,
    range: Option<Vec<bool>>,
    parameters: Option<Vec<Z>>,
}
fn consume(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
    operand: Operand,
) -> Result<Source, ValidationFailure> {
    let Operand {
        head,
        mut shared,
        range: mut enabled,
        parameters: previous_parameters,
    } = operand;
    let mut inputs = vec![head];
    let mut invalid = false;
    let mut chosen = None;
    let mut math = None;
    let mut published = None;
    let mut missing = vec![];
    let mut checked = None;
    let mut target_set = None;
    let mut selected_ranges = vec![];
    let mut public_model = None;
    if r.kind == QuestionKind::Observe {
        let base = g.nodes.len();
        let mut b = Builder {
            g,
            base,
            parts: vec![],
        };
        let claim = condition(&mut b, r, inputs.clone(), Decision::Undetermined)?;
        let mut a = answer(r, claim, Decision::Undetermined, BTreeMap::new(), &b);
        a.reasons.push(Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: r.kind,
                operand_types: vec![match r
                    .declaration()
                    .and_then(|name| env.indexes.inputs.law().declarations().get(name))
                    .map(|d| &d.signature)
                {
                    Some(Signature::View { returns, .. }) => returns.clone(),
                    _ => Type::Bool,
                }],
                method: "integer_affine_repair_observation".into(),
            },
            request: r.id.clone(),
            dependencies: inputs.clone(),
            missing: vec![],
            location: None,
        });
        let mut source = wrap(b, a, r, shared.witness.clone(), Some(shared), inputs);
        source.range = enabled;
        return Ok(source);
    }
    if r.kind == QuestionKind::Solve {
        let selector = &r
            .arguments
            .iter()
            .find(|a| a.name == "within")
            .ok_or(internal!("整数変更範囲がない"))?
            .value;
        let (at, mask) = mask(env, g, &shared, selector)?;
        inputs.push(at);
        invalid = mask.is_none();
        enabled = mask;
        if !invalid {
            let mask = enabled.as_ref().ok_or(internal!("整数範囲がない"))?;
            let display = !r.arguments.iter().any(|a| {
                a.name == "mode" && matches!(&a.value,Selector::Enum{value}if value=="existence")
            });
            if let Some((known, at)) = known_range(g, &shared, mask, &inputs, display, c)? {
                math = Some(known);
                published = at;
            } else {
                match resolve_range(env, &shared, mask, c)? {
                    Ok(value) => math = Some(value),
                    Err(facts) => missing = facts,
                }
            }
        }
    } else if r.kind == QuestionKind::Scopes {
        if let Some(projection) = &shared.projection {
            missing = projection
                .shared_rows
                .iter()
                .filter(|i| shared.compiled.baselines[**i].is_none())
                .map(|i| shared.compiled.linear.slots[*i].clone())
                .collect();
            if missing.is_empty() {
                selected_ranges = super::minimal_masks(
                    &shared.internal,
                    |mask| {
                        let fixed = fixed(&shared, mask, c)?.map_err(|_| {
                            ValidationFailure::from(internal!("確認済みの整数基準値がない"))
                        })?;
                        let (matrix, rhs) = projection.constraints(&fixed, c)?;
                        // 探索だけの分解を実行履歴としてpoolへ蓄積しない。
                        Ok(
                            integer_fiber::solve(&matrix, projection.visible(), &rhs, c)?
                                .particular
                                .is_some(),
                        )
                    },
                    c,
                )?;
            }
        }
    } else if r.kind == QuestionKind::Candidate {
        let mask = enabled
            .as_ref()
            .ok_or(internal!("整数解集合の範囲がない"))?;
        math = if shared.problem.is_none() {
            match resolve_range(env, &shared, mask, c)? {
                Ok(value) => Some(value),
                Err(_) => return Err(internal!("整数元全解の固定条件が未確定").into()),
            }
        } else {
            data(g, head)?
                .source
                .integer()
                .ok_or(internal!("整数解集合のownerがない"))?
                .range_result
                .clone()
        };
        let solved = math.as_ref().ok_or(internal!("完成した整数全解がない"))?;
        let index = &r
            .arguments
            .iter()
            .find(|a| a.name == "index")
            .ok_or(internal!("整数候補番号がない"))?
            .value;
        let Selector::Ordinal { value } = index else {
            return Err(internal!("整数候補番号がOrdinalでない").into());
        };
        let index =
            BigUint::parse_bytes(value.as_bytes(), 10).ok_or(internal!("整数候補番号が不正"))?;
        chosen = match (
            solved.as_ref(),
            shared.projection.as_ref(),
            shared.compiled.linear.particular.as_ref(),
        ) {
            (RangeMath::Constrained { fiber, .. }, Some(projection), Some(origin)) => {
                projection.candidate(origin, &shared.compiled.linear.kernel, fiber, &index, c)?
            }
            (RangeMath::Empty, _, _) => None,
            _ => return Err(internal!("整数全解の部品が対応しない").into()),
        };
        invalid = chosen.is_none();
        if let Some(parameters) = &chosen {
            let result = check_candidate(env, &shared, mask, parameters, c)?;
            if result.member != Some(true) {
                return Err(internal!("整数候補が元guard・範囲・Lawを満たさない").into());
            }
        }
    } else if r.kind == QuestionKind::Apply {
        let at = reference(
            env,
            g,
            &r.arguments
                .iter()
                .find(|a| a.name == "in")
                .ok_or(internal!("整数選択の解集合がない"))?
                .value,
        )?;
        inputs.push(at);
        target_set = Some(at);
        let target = if let Ok(d) = data(g, at) {
            d.source.integer().map(|state| {
                (
                    state.shared.clone(),
                    d.source.range.clone(),
                    state.range_result.clone(),
                )
            })
        } else {
            legacy(env, g, at, c)?.map(|s| {
                let enabled = vec![true; s.subjects.len()];
                (s, Some(enabled), None)
            })
        };
        if let Some((target, range, known)) = target {
            invalid = !same_domain(&shared, &target, c)?;
            enabled = range;
            math = known;
            shared = target;
            if !invalid {
                let parameters = previous_parameters.ok_or(internal!("整数の元割当てがない"))?;
                let mask = enabled
                    .as_ref()
                    .ok_or(internal!("整数の適用先範囲がない"))?;
                let result = check_candidate(env, &shared, mask, &parameters, c)?;
                match result.member {
                    Some(true) => {
                        chosen = Some(parameters);
                        checked = Some(result.candidate);
                    }
                    Some(false) => invalid = true,
                    None => missing = result.missing,
                }
            }
        } else {
            invalid = true;
        }
    } else {
        return Err(internal!("整数修復の消費操作が違う").into());
    }
    let input_key = inputs.clone();
    if r.kind == QuestionKind::Solve && math.is_some() && missing.is_empty() && !invalid {
        let display = !r.arguments.iter().any(|a| {
            a.name == "mode" && matches!(&a.value,Selector::Enum{value}if value=="existence")
        });
        if display {
            if let Some(set) = published {
                inputs.push(set);
            } else if let Some(model) = known_public(g, &shared, c)? {
                inputs.extend(model.inputs());
                public_model = Some(model);
            }
        }
    }
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let mut outputs = BTreeMap::new();
    let mut ranges = BTreeMap::new();
    let (claim, status) = if invalid {
        (
            condition(&mut b, r, inputs.clone(), Decision::Refuted)?,
            Decision::Refuted,
        )
    } else if !missing.is_empty() {
        if r.kind == QuestionKind::Solve
            && let Some(mask) = &enabled
        {
            let at = range_value(&mut b, &shared, mask, &inputs)?;
            ranges.insert(at.0 - base, mask.clone());
            outputs.insert("range".into(), at);
        }
        (
            condition(&mut b, r, inputs.clone(), Decision::Undetermined)?,
            Decision::Undetermined,
        )
    } else if r.kind == QuestionKind::Solve {
        let mask = enabled.as_ref().ok_or(internal!("整数範囲がない"))?;
        let range = range_value(&mut b, &shared, mask, &inputs)?;
        ranges.insert(range.0 - base, mask.clone());
        outputs.insert("range".into(), range);
        let solved = math.as_ref().ok_or(internal!("整数範囲の計算結果がない"))?;
        let status = if solved.exists() {
            Decision::Established
        } else {
            Decision::Refuted
        };
        let display = !r.arguments.iter().any(|a| {
            a.name == "mode" && matches!(&a.value,Selector::Enum{value}if value=="existence")
        });
        if display {
            let set = if let Some(at) = published {
                at
            } else {
                let model = if let Some(model) = &public_model {
                    model.clone()
                } else {
                    let model = publish_model(&mut b, &shared, c)?;
                    public_model = Some(model.clone());
                    model
                };
                render_solutions(&mut b, &shared, &model, solved, range, c)?
            };
            published = Some(set);
            outputs.insert("solutions".into(), set);
            (
                b.proposition("inhabited", vec![set], vec![], status)?,
                status,
            )
        } else {
            (
                condition(
                    &mut b,
                    r,
                    vec![shared.problem.ok_or(internal!("整数問題がない"))?, range],
                    status,
                )?,
                status,
            )
        }
    } else if r.kind == QuestionKind::Scopes {
        let mut entries = vec![];
        for mask in selected_ranges {
            let at = range_value(&mut b, &shared, &mask, &inputs)?;
            ranges.insert(at.0 - base, mask);
            entries.push(at);
        }
        let list = b.push(
            NodeType::ChangeRanges,
            "domain",
            refs(&entries),
            entries,
            None,
        )?;
        outputs.insert("ranges".into(), list);
        (
            condition(&mut b, r, vec![head, list], Decision::Established)?,
            Decision::Established,
        )
    } else if r.kind == QuestionKind::Candidate {
        let parameters = chosen.as_ref().ok_or(internal!("整数候補がない"))?;
        let assignment = assignment_value(&mut b, &shared, parameters, head)?;
        outputs.insert("assignment".into(), assignment);
        (
            b.proposition(
                "solution_member",
                vec![head, assignment],
                vec![],
                Decision::Established,
            )?,
            Decision::Established,
        )
    } else {
        let set = target_set.ok_or(internal!("整数適用の解集合がない"))?;
        let claim = condition(&mut b, r, vec![head, set], Decision::Established)?;
        let (object, checks) = apply_object(
            env,
            &mut b,
            &shared,
            head,
            set,
            claim,
            checked
                .as_ref()
                .ok_or(internal!("検査済み整数候補がない"))?,
        )?;
        let selection = b.push(
            NodeType::Construction(T::Selection),
            "selection",
            Json::obj([
                ("domain", shared.domain.wire()),
                ("solutions", set.wire()),
                ("parameters", head.wire()),
                ("object", object.wire()),
                ("rechecks", refs(&checks)),
            ]),
            [vec![shared.domain, set, head, object, claim], checks].concat(),
            None,
        )?;
        outputs.insert("selection".into(), selection);
        outputs.insert("object".into(), object);
        (claim, Decision::Established)
    };
    let mut a = answer(r, claim, status, outputs, &b);
    if invalid {
        fail(&mut a, r.kind.wire());
    }
    if !missing.is_empty() {
        a.reasons.push(Reason {
            kind: ReasonKind::Missing,
            request: r.id.clone(),
            dependencies: inputs.clone(),
            missing,
            location: None,
        });
    }
    let witness = shared.witness.clone();
    let mut source = wrap(b, a, r, witness, Some(shared), inputs);
    source.range = enabled;
    source.ranges = ranges;
    if let Some(Backend::Integer(state)) = &mut source.shared {
        state.parameters = chosen;
        state.range_result = math;
        state.solutions = published;
        state.public_model = public_model;
        state.input_key = input_key;
    }
    Ok(source)
}

#[cfg(test)]
mod tests;
