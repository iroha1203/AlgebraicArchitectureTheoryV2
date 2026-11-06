//! 同じ有限修復問題から範囲・元割当て・対象を構成する。
pub(super) mod finite;
mod prepare;
use prepare::{legacy, prepare};
#[cfg(test)]
mod tests;
use super::{
    PreparedObserved, architecture_result,
    build_result::{Builder, Part},
    change_result,
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    environment::{
        AnswerBinding, Environment, change_evaluation, change_search,
        repair_problem::{Compilation, Compiled},
    },
    projection::{ProjectionStep, ProjectionType},
    request::{QuestionKind, Request, Selector},
    result::*,
};
use archsig_common::{
    canonical::Json,
    control::{Checkpoint, Control},
    types::Type,
};
use archsig_input::law::model::Signature;
use num_bigint::BigUint;
use std::{collections::BTreeMap, sync::Arc};

#[derive(Debug)]
struct Shared {
    compiled: Arc<Compiled>,
    witness: Arc<ArchitectureWitness>,
    base: NodeRef,
    domain: NodeRef,
    problem: Option<NodeRef>,
    legacy_set: Option<NodeRef>,
    subjects: Vec<NodeRef>,
    requirements: Vec<NodeRef>,
    internal: Vec<bool>,
    change: String,
    root_type: String,
}
#[derive(Debug)]
pub(super) struct Source {
    base: usize,
    parts: Vec<Part>,
    answer: Answer,
    request: Request,
    witness: Arc<ArchitectureWitness>,
    shared: Option<Arc<Shared>>,
    range: Option<Vec<bool>>,
    ranges: BTreeMap<usize, Vec<bool>>,
    chosen: Option<Vec<usize>>,
    inputs: Vec<NodeRef>,
    context: super::call::Context,
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
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::PrimitiveValuation)?;
    Ok(())
}
fn refs(xs: &[NodeRef]) -> Json {
    Json::Arr(xs.iter().map(|r| r.wire()).collect())
}
fn fields(wire: &Json) -> Option<&archsig_common::canonical::JsonObject> {
    if let Json::Obj(xs) = wire {
        Some(xs)
    } else {
        None
    }
}
impl Data {
    fn part(&self) -> &Part {
        &self.source.parts[self.index]
    }
    pub(super) fn request(&self) -> &Request {
        &self.source.request
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty.clone()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction
    }
    pub(super) fn wire(&self) -> Json {
        self.part().wire()
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        self.part().scalar.as_ref()
    }
    pub(super) fn evidence_kind(&self) -> Option<EvidenceKind> {
        self.part().evidence_kind()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        self.part().arguments.clone()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.part().support.clone(), self.part().scope.clone())
    }
    pub(super) fn overrides(
        &self,
        g: &Graph,
    ) -> Result<Vec<(Fact, NodeRef, Scalar)>, ValidationFailure> {
        change_result::architecture_overrides(g, self.part())
    }
    pub(super) fn conditions(&self) -> Vec<NodeRef> {
        if !matches!(
            self.ty(),
            NodeType::Construction(T::Architecture | T::Selection)
        ) {
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
    pub(super) fn projection_type(&self) -> Option<ProjectionType> {
        let root = self.source.shared.as_ref().map(|s| s.root_type.clone())?;
        Some(match self.ty() {
            NodeType::Construction(T::RepairProblem) => ProjectionType::RepairProblem(root),
            NodeType::Construction(T::ChangeRange) => ProjectionType::ChangeRange(root),
            NodeType::Construction(T::Selection) => ProjectionType::Selection(root),
            NodeType::Construction(T::CandidateSpace) => ProjectionType::CandidateSpace(root),
            NodeType::Construction(T::SolutionSet) => ProjectionType::SolutionSet(root),
            NodeType::Construction(T::Assignment) => ProjectionType::Assignment(root),
            NodeType::Construction(T::Architecture) => ProjectionType::ArchitectureRoot(root),
            NodeType::Construction(T::StateSpace) => ProjectionType::StateSpace(root),
            NodeType::Construction(T::StateMap) => ProjectionType::StateMap,
            NodeType::ChangeRanges => ProjectionType::RangeList(root),
            NodeType::Domain => ProjectionType::Domain,
            _ => return None,
        })
    }
    pub(super) fn project(&self, path: &[ProjectionStep]) -> Option<(NodeRef, usize)> {
        let ty = self.projection_type()?;
        let allowed = if let Some(plan) = super::request::repair_projection(&ty, path) {
            plan.is_ok()
        } else {
            match (self.ty(), path.first()?) {
                (NodeType::Construction(T::CandidateSpace), ProjectionStep::Field(f)) => {
                    matches!(f.as_str(), "base" | "parameters" | "states" | "action")
                }
                (
                    NodeType::Construction(T::SolutionSet | T::Assignment),
                    ProjectionStep::Field(f),
                ) => f == "domain",
                (NodeType::Construction(T::Architecture), ProjectionStep::Field(f)) => f == "root",
                (NodeType::Construction(T::StateMap), ProjectionStep::Field(f)) => {
                    matches!(f.as_str(), "source" | "target")
                }
                _ => false,
            }
        };
        if !allowed {
            return None;
        }
        let value = match (path.first()?, self.part().wire_ref()?) {
            (ProjectionStep::Field(f), Json::Obj(xs)) => xs.get(f)?,
            (ProjectionStep::Index(i), Json::Arr(xs)) => xs.get(usize::try_from(*i).ok()?)?,
            _ => return None,
        };
        self.part()
            .arguments
            .iter()
            .find(|r| r.wire() == *value)
            .map(|r| (*r, 1))
    }
}
fn data(g: &Graph, r: NodeRef) -> Result<&Data, ValidationFailure> {
    match &g.get(r)?.payload {
        Some(Payload::Construction(v)) => match &v.data {
            D::SharedRepair(d) => Ok(d),
            _ => Err(internal!("共通修復問題の由来が違う").into()),
        },
        _ => Err(internal!("共通修復問題がnativeでない").into()),
    }
}
fn reference(
    env: &Environment<'_>,
    g: &mut Graph,
    s: &Selector,
) -> Result<NodeRef, ValidationFailure> {
    match env.answer_binding(g, s, (0, 0))? {
        AnswerBinding::Reference(r) => {
            env.recheck_node(g, g.get(r)?, r.0)?;
            Ok(r)
        }
        AnswerBinding::Projection(n) => {
            env.validate(g, &n)?;
            g.push(n)
        }
        AnswerBinding::Inapplicable(_) => Err(ValidationFailure::UnsupportedExpression {
            location: archsig_common::issue::Location::Law { span: (0, 0) },
            feature: "repair result projection is not available".into(),
        }),
    }
}
fn scalar_set(
    env: &Environment<'_>,
    g: &mut Graph,
    s: &Selector,
) -> Result<(NodeRef, Vec<Scalar>), ValidationFailure> {
    let r = reference(env, g, s)?;
    let Scalar::Set { items, .. } = g.scalar(r)? else {
        return Err(internal!("変更範囲がSetでない").into());
    };
    Ok((r, items.clone()))
}
fn domain(
    b: &mut Builder<'_>,
    ty: &Type,
    values: &[NodeRef],
) -> Result<NodeRef, ValidationFailure> {
    b.push(
        NodeType::Domain,
        "domain",
        Json::obj([
            ("kind", Json::str("finite")),
            ("type", ty.wire()),
            ("elements", refs(values)),
        ]),
        values.to_vec(),
        None,
    )
}
fn condition(
    b: &mut Builder<'_>,
    r: &Request,
    inputs: Vec<NodeRef>,
    status: Decision,
) -> Result<NodeRef, ValidationFailure> {
    let label = change_result::value(b, &Scalar::Text(r.kind.wire().into()))?;
    let mut operands = vec![label];
    operands.extend(inputs);
    b.proposition("constructible", operands, vec![], status)
}
fn answer(
    r: &Request,
    claim: NodeRef,
    status: Decision,
    mut outputs: BTreeMap<String, NodeRef>,
    b: &Builder<'_>,
) -> Answer {
    outputs.insert("proposition".into(), claim);
    Answer {
        id: r.id.clone(),
        status,
        outputs,
        claim: Some(claim),
        evidence: vec![],
        reasons: vec![],
        scope: b.parts[claim.0 - b.base].scope.clone(),
    }
}
fn fail(a: &mut Answer, construction: &'static str) {
    let claim = a.claim.expect("構成条件を生成済み");
    a.reasons.push(Reason {
        kind: ReasonKind::ConditionFailed {
            condition: claim,
            construction,
        },
        request: a.id.clone(),
        dependencies: vec![claim],
        missing: vec![],
        location: None,
    });
}
fn pins(shared: &Shared, enabled: &[bool]) -> Vec<Option<usize>> {
    let mut pins = vec![None; shared.compiled.relations.variables()];
    for o in &shared.compiled.outputs {
        if !shared.internal[o.subject] && !enabled[o.subject] {
            pins[o.column] = Some(o.baseline);
        }
    }
    pins
}
fn range(b: &mut Builder<'_>, s: &Shared, enabled: &[bool]) -> Result<NodeRef, ValidationFailure> {
    let ty = s
        .compiled
        .subjects
        .first()
        .map(Scalar::ty)
        .unwrap_or_else(|| {
            let inputs = Witness::Architecture(s.witness.clone());
            let Signature::Change { params, .. } =
                &inputs.inputs().law().declarations()[&s.change].signature
            else {
                unreachable!()
            };
            params[0].ty.erase()
        });
    let problem = s
        .problem
        .ok_or(internal!("旧解集合には修復問題の範囲がない"))?;
    let elements = s
        .subjects
        .iter()
        .zip(enabled)
        .filter_map(|(r, on)| on.then_some(*r))
        .collect::<Vec<_>>();
    let d = domain(b, &ty, &elements)?;
    b.push(
        NodeType::Construction(T::ChangeRange),
        "change_range",
        Json::obj([("problem", problem.wire()), ("enabled", d.wire())]),
        vec![problem, d],
        None,
    )
}
fn same_problem(a: &Shared, b: &Shared) -> bool {
    a.problem.is_some() && a.problem == b.problem
}
fn same_domain(a: &Shared, b: &Shared) -> bool {
    a.domain == b.domain
}
fn minimal(shared: &Shared, c: &Control) -> Result<Vec<Vec<bool>>, ValidationFailure> {
    let units = shared
        .internal
        .iter()
        .enumerate()
        .filter_map(|(i, on)| (!on).then_some(i))
        .collect::<Vec<_>>();
    let mut found: Vec<Vec<bool>> = vec![];
    for size in 0..=units.len() {
        let mut selected = (0..size).collect::<Vec<_>>();
        loop {
            tick(c)?;
            let mut enabled = vec![false; shared.subjects.len()];
            for i in &selected {
                enabled[units[*i]] = true;
            }
            if !found
                .iter()
                .any(|old| old.iter().zip(&enabled).all(|(a, b)| !a || *b))
                && shared
                    .compiled
                    .relations
                    .exists(&pins(shared, &enabled), c)?
            {
                found.push(enabled);
            }
            let Some(at) = (0..size)
                .rev()
                .find(|i| selected[*i] < units.len() - size + *i)
            else {
                break;
            };
            selected[at] += 1;
            for i in at + 1..size {
                selected[i] = selected[i - 1] + 1;
            }
        }
    }
    found.sort_by_key(|enabled| {
        enabled
            .iter()
            .enumerate()
            .filter_map(|(i, on)| on.then_some(i))
            .collect::<Vec<_>>()
    });
    Ok(found)
}
fn assignment(
    b: &mut Builder<'_>,
    s: &Shared,
    point: &[usize],
    solutions: NodeRef,
) -> Result<NodeRef, ValidationFailure> {
    let origin = Witness::Architecture(s.witness.clone());
    let Signature::Change { params, .. } =
        &origin.inputs().law().declarations()[&s.change].signature
    else {
        unreachable!()
    };
    let width = params.len() - 1;
    let mut entries = vec![];
    let mut args = vec![s.domain, solutions];
    for (i, subject) in s.subjects.iter().enumerate() {
        let mut values = vec![];
        for (column, value) in point.iter().enumerate().skip(i * width).take(width) {
            let at = change_result::value(b, &s.compiled.domains[column][*value])?;
            values.push(at);
            args.push(at);
        }
        args.push(*subject);
        entries.push(Json::obj([
            ("subject", subject.wire()),
            ("parameters", refs(&values)),
        ]));
    }
    b.push(
        NodeType::Construction(T::Assignment),
        "assignment",
        Json::obj([("domain", s.domain.wire()), ("entries", Json::Arr(entries))]),
        args,
        None,
    )
}
fn apply_object(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    s: &Shared,
    point: &[usize],
    selected: NodeRef,
    solutions: NodeRef,
    claim: NodeRef,
) -> Result<(NodeRef, Vec<NodeRef>), ValidationFailure> {
    let g = b.g;
    let c = &env.control;
    let mut fixed = env
        .try_primitive_valuation_from(&s.compiled.fixed, c)?
        .ok_or(internal!("選択候補の基準が不適合"))?;
    fixed.select_local_object(&s.witness, c)?;
    let origin = Witness::Architecture(s.witness.clone());
    let change = &origin.inputs().law().declarations()[&s.change];
    let values = (0..s.compiled.parameter_count)
        .map(|i| s.compiled.domains[i][point[i]].clone())
        .collect::<Vec<_>>();
    let candidate = change_evaluation::candidate(&fixed, change, &s.compiled.subjects, &values)?;
    let row = change_evaluation::solution_row(&fixed, &candidate, 0, &s.compiled.requirements)?;
    if row.member != Some(true) || candidate.update.state != change_evaluation::State::Ready {
        return Err(internal!("選択候補が元更新・Lawへの再代入を満たさない").into());
    }
    for output in &s.compiled.outputs {
        tick(c)?;
        if !candidate.update.values.iter().any(|(fact, value)| {
            fact.snapshot == output.fact.snapshot
                && fact.subject == output.fact.subject
                && fact.field == output.fact.field
                && *value == s.compiled.domains[output.column][point[output.column]]
        }) {
            return Err(internal!("復元した更新先が元式と違う").into());
        }
    }
    let mut checks = vec![b.proposition(
        "solution_member",
        vec![solutions, selected],
        vec![claim],
        Decision::Established,
    )?];
    for law in &s.requirements {
        checks.push(b.proposition(
            "law_holds",
            vec![*law],
            vec![selected, claim],
            Decision::Established,
        )?);
    }
    let Some(Payload::Construction(original)) = &g.get(s.base)?.payload else {
        return Err(internal!("選択対象の元Architectureがない").into());
    };
    let mut wire = original.wire();
    let Json::Obj(fields) = &mut wire else {
        return Err(internal!("元Architectureがrecordでない").into());
    };
    let Some(Json::Arr(previous)) = fields.get_mut("overrides") else {
        return Err(internal!("元Architectureのoverrideがない").into());
    };
    let mut args = original.arguments();
    args.push(s.base);
    args.extend(&checks);
    for (fact, value) in &candidate.update.values {
        tick(c)?;
        let subject_index=s.compiled.subjects.iter().position(|v|matches!(v,Scalar::Subject {snapshot,subject,..} if *snapshot==fact.snapshot&&*subject==fact.subject)).ok_or(internal!("更新先が元instanceにない"))?;
        let subject = s.subjects[subject_index];
        let updated = change_result::value(b, value)?;
        args.extend([subject, updated]);
        previous.retain(|row| {
            let Some(row) = self::fields(row) else {
                return true;
            };
            let Some(slot) = row.get("slot").and_then(self::fields) else {
                return true;
            };
            if slot.get("field") != fact.field.as_ref().map(Json::str).as_ref() {
                return true;
            }
            !original.arguments().iter().any(|r| {
                Some(&r.wire()) == slot.get("subject")
                    && g.scalar(*r).ok() == Some(&s.compiled.subjects[subject_index])
            })
        });
        previous.push(Json::obj([
            (
                "slot",
                Json::obj([
                    ("subject", subject.wire()),
                    (
                        "field",
                        Json::str(fact.field.as_deref().ok_or(internal!("更新fieldがない"))?),
                    ),
                ]),
            ),
            ("value", updated.wire()),
        ]));
    }
    let object = b.push(
        NodeType::Construction(T::Architecture),
        "architecture",
        wire,
        args,
        None,
    )?;
    Ok((object, checks))
}
fn consume(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
) -> Result<Source, ValidationFailure> {
    let head = reference(env, g, &r.head)?;
    let (shared, mut enabled, previous_chosen) = if let Ok(d) = data(g, head) {
        (
            d.source
                .shared
                .as_ref()
                .ok_or(internal!("未構成の修復問題を消費した"))?
                .clone(),
            d.source.range.clone(),
            d.source.chosen.clone(),
        )
    } else if r.kind == QuestionKind::Candidate {
        let shared = legacy(env, g, head, c)?;
        let enabled = vec![true; shared.subjects.len()];
        (shared, Some(enabled), None)
    } else {
        return Err(internal!("共通修復問題の元結果がない").into());
    };
    let mut inputs = vec![head];
    let mut chosen = None;
    let mut selected_ranges = vec![];
    let mut target_set = None;
    let mut invalid = false;
    if r.kind == QuestionKind::Solve {
        let a = r
            .arguments
            .iter()
            .find(|a| a.name == "within")
            .ok_or(internal!("変更範囲がない"))?;
        let at = reference(env, g, &a.value)?;
        inputs.push(at);
        if g.get(at)?.ty == NodeType::Construction(T::ChangeRange) {
            let d = data(g, at)?;
            let other = d
                .source
                .shared
                .as_ref()
                .ok_or(internal!("変更範囲の問題がない"))?;
            invalid = !same_problem(&shared, other);
            enabled = d.source.ranges.get(&d.index).cloned();
        } else {
            let Scalar::Set { items, .. } = g.scalar(at)? else {
                return Err(internal!("変更範囲がSetでない").into());
            };
            invalid = items.iter().any(|v| {
                shared
                    .compiled
                    .subjects
                    .iter()
                    .position(|s| s == v)
                    .is_none_or(|i| shared.internal[i])
            });
            enabled = Some(
                shared
                    .compiled
                    .subjects
                    .iter()
                    .map(|v| items.contains(v))
                    .collect(),
            );
        }
    } else if r.kind == QuestionKind::Scopes {
        selected_ranges = minimal(&shared, c)?;
    } else if r.kind == QuestionKind::Candidate {
        let Selector::Ordinal { value } = &r
            .arguments
            .iter()
            .find(|a| a.name == "index")
            .ok_or(internal!("候補番号がない"))?
            .value
        else {
            return Err(internal!("候補番号がOrdinalでない").into());
        };
        let index = BigUint::parse_bytes(value.as_bytes(), 10)
            .ok_or(internal!("検査済み候補番号が不正"))?;
        chosen = shared.compiled.relations.candidate(
            &pins(
                &shared,
                enabled.as_ref().ok_or(internal!("解集合の範囲がない"))?,
            ),
            index,
            c,
        )?;
        invalid = chosen.is_none();
    } else if r.kind == QuestionKind::Apply {
        let at = reference(
            env,
            g,
            &r.arguments
                .iter()
                .find(|a| a.name == "in")
                .ok_or(internal!("選択の解集合がない"))?
                .value,
        )?;
        inputs.push(at);
        target_set = Some(at);
        let (other, target_range) = if let Ok(d) = data(g, at) {
            (
                d.source
                    .shared
                    .as_ref()
                    .ok_or(internal!("解集合の問題がない"))?
                    .clone(),
                d.source.range.clone(),
            )
        } else if shared.legacy_set == Some(at) {
            (shared.clone(), Some(vec![true; shared.subjects.len()]))
        } else {
            let old = legacy(env, g, at, c)?;
            let range = Some(vec![true; old.subjects.len()]);
            (old, range)
        };
        chosen = previous_chosen;
        enabled = target_range;
        invalid = !same_domain(&shared, &other)
            || !shared.compiled.relations.member(
                &pins(
                    &other,
                    enabled.as_ref().ok_or(internal!("解集合の範囲がない"))?,
                ),
                chosen
                    .as_deref()
                    .ok_or(internal!("選択した元割当てがない"))?,
                c,
            )?;
    }
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let mut ranges = BTreeMap::new();
    let mut outputs = BTreeMap::new();
    let (claim, status) = if invalid {
        (
            condition(&mut b, r, inputs.clone(), Decision::Refuted)?,
            Decision::Refuted,
        )
    } else if r.kind == QuestionKind::Solve {
        let problem = shared.problem.ok_or(internal!("修復問題がない"))?;
        let enabled = enabled.as_ref().ok_or(internal!("範囲がない"))?;
        let at = range(&mut b, &shared, enabled)?;
        ranges.insert(at.0 - base, enabled.clone());
        outputs.insert("range".into(), at);
        let exists = shared
            .compiled
            .relations
            .exists(&pins(&shared, enabled), c)?;
        let status = if exists {
            Decision::Established
        } else {
            Decision::Refuted
        };
        let solutions_mode = !r.arguments.iter().any(|a| {
            a.name == "mode" && matches!(&a.value,Selector::Enum {value}if value=="existence")
        });
        if solutions_mode {
            let set = b.push(
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
                            ("range", at.wire()),
                        ]),
                    ),
                ]),
                [
                    vec![shared.domain, problem, at],
                    shared.requirements.clone(),
                ]
                .concat(),
                None,
            )?;
            outputs.insert("solutions".into(), set);
            (
                b.proposition("inhabited", vec![set], vec![], status)?,
                status,
            )
        } else {
            (condition(&mut b, r, vec![problem, at], status)?, status)
        }
    } else if r.kind == QuestionKind::Scopes {
        let mut entries = vec![];
        for enabled in selected_ranges {
            let at = range(&mut b, &shared, &enabled)?;
            ranges.insert(at.0 - base, enabled);
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
        let assignment = assignment(
            &mut b,
            &shared,
            chosen.as_deref().ok_or(internal!("復元候補がない"))?,
            head,
        )?;
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
        let set = target_set.ok_or(internal!("選択先がない"))?;
        let claim = condition(&mut b, r, vec![head, set], Decision::Established)?;
        let (object, checks) = apply_object(
            env,
            &mut b,
            &shared,
            chosen.as_deref().ok_or(internal!("割当てがない"))?,
            head,
            set,
            claim,
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
        outputs.insert("object".into(), object);
        outputs.insert("selection".into(), selection);
        (claim, Decision::Established)
    };
    let mut a = answer(r, claim, status, outputs, &b);
    if invalid {
        fail(&mut a, r.kind.wire());
    }
    Ok(Source {
        base,
        parts: b.parts,
        answer: a,
        request: r.clone(),
        witness: shared.witness.clone(),
        shared: Some(shared),
        range: enabled,
        ranges,
        chosen,
        inputs,
        context: g.active,
    })
}
impl super::result_kind::ResultKind for Data {
    type Stored = Arc<Source>;
    type Input<'a, 'input: 'a> = (
        &'a PreparedObserved,
        &'a Environment<'input>,
        &'a mut Graph,
        &'a Request,
        &'a Control,
    );
    type Output = Answer;
    fn compute_and_retain<'a, 'input: 'a>(
        (prepared, env, g, r, c): Self::Input<'a, 'input>,
    ) -> Result<Answer, ValidationFailure> {
        env.commit_projection_conditions(g, r)?;
        if let Some(a) = super::public_map::unavailable(env, g, r)? {
            return Ok(a);
        }
        let source = Arc::new(if r.kind == QuestionKind::Prepare {
            prepare(prepared, env, g, r, c)?
        } else {
            consume(env, g, r, c)?
        });
        for (index, part) in source.parts.iter().enumerate() {
            native::retain(
                g,
                ConstructionValue {
                    witness: Witness::Architecture(source.witness.clone()),
                    data: D::SharedRepair(Data {
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
        g: &Graph,
        n: &Node,
        v: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let Witness::Architecture(w) = &v.witness else {
            return Err(internal!("修復問題の由来が違う").into());
        };
        let p = self.part();
        if !Arc::ptr_eq(w, &self.source.witness)
            || n.ty != p.ty
            || n.rule != Rule::Construction(p.construction)
            || n.arguments != p.arguments
            || n.support != p.support
            || n.scope != p.scope
            || n.reasons != p.reasons
            || n.evidence != p.evidence
            || n.judgment != p.judgment
        {
            return Err(internal!("共通修復問題の元構成・型・判断が違う").into());
        }
        for at in &p.arguments {
            g.get(*at)?;
        }
        Ok(())
    }
    fn recheck(
        &self,
        env: &Environment<'_>,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        if self.index >= self.source.parts.len()
            || at != self.source.base + self.index
            || g.context_at(at) != self.source.context
            || g.requests.get(self.source.context.request) != Some(&self.source.request)
            || (!std::ptr::eq(v.witness.inputs(), env.indexes.inputs)
                && v.witness.inputs().sources() != env.indexes.inputs.sources())
            || self.part().arguments.iter().any(|r| r.0 >= at)
        {
            return Err(internal!("共通修復問題の入力・位置・producerが違う").into());
        }
        if env.results.source_checked(&self.source) {
            return Ok(());
        }
        for input in &self.source.inputs {
            if input.0 >= self.source.base {
                return Err(internal!("共通修復問題の元入力が既出でない").into());
            }
            env.recheck_node(g, g.get(*input)?, input.0)?;
        }
        // Source は通常評価・関係生成・所属再検査を終えた不変値だけを保持する。
        // 同じownerを検査sessionで引き継ぎ、範囲ごとに部品生成を反復しない。
        env.results.remember(self.source.clone());
        Ok(())
    }
}
pub(super) fn evaluate(
    p: &PreparedObserved,
    e: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    c: &Control,
) -> Result<Answer, ValidationFailure> {
    <Data as super::result_kind::ResultKind>::compute_and_retain((p, e, g, r, c))
}
pub(super) fn validate_answer(
    e: &Environment<'_>,
    g: &Graph,
    r: &Request,
    a: &Answer,
) -> Result<(), ValidationFailure> {
    if let Some(expected) = super::public_map::unavailable(e, g, r)? {
        return if *a == expected {
            Ok(())
        } else {
            Err(internal!("修復問題の依存停止が違う").into())
        };
    }
    let at = a.claim.ok_or(internal!("修復問題の構成条件がない"))?;
    let d = data(g, at)?;
    if d.source.request != *r || d.source.answer != *a {
        return Err(internal!("修復問題の元回答が違う").into());
    }
    let Some(Payload::Construction(v)) = &g.get(at)?.payload else {
        unreachable!()
    };
    <Data as super::result_kind::ResultKind>::recheck(d, e, g, v, at.0)
}
pub(super) fn validate_failure(g: &Graph, r: &Reason) -> Result<(), ValidationFailure> {
    let ReasonKind::ConditionFailed {
        condition,
        construction,
    } = r.kind
    else {
        return Err(internal!("修復問題の失敗種別が違う").into());
    };
    let d = data(g, condition)?;
    if d.source.request.kind.wire() != construction
        || !d.source.answer.reasons.contains(r)
        || r.dependencies != [condition]
        || g.get(condition)?.judgment.as_ref().map(|j| j.status) != Some(Decision::Refuted)
    {
        return Err(internal!("修復問題の反証条件が違う").into());
    }
    Ok(())
}

pub(super) fn validate_origin(
    e: &Environment<'_>,
    r: &Request,
    v: &ConstructionValue,
) -> Result<(), ValidationFailure> {
    let D::SharedRepair(d) = &v.data else {
        return Err(internal!("共通修復問題の由来が別種").into());
    };
    let Witness::Architecture(w) = &v.witness else {
        return Err(internal!("共通修復問題の元対象がない").into());
    };
    if d.source.request != *r
        || !Arc::ptr_eq(w, &d.source.witness)
        || (!std::ptr::eq(v.witness.inputs(), e.indexes.inputs)
            && v.witness.inputs().sources() != e.indexes.inputs.sources())
    {
        return Err(internal!("共通修復問題が現在の入力・要求に属さない").into());
    }
    Ok(())
}
