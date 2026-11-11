//! 同じ有限修復問題から範囲・元割当て・対象を構成する。
pub(super) mod finite;
pub(super) mod integer;
mod observation;
mod prepare;
use prepare::{legacy, prepare};
#[cfg(test)]
mod reobservation_tests;
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
    family: Option<(
        Arc<crate::observed::environment::repair_problem::family::Family>,
        NodeRef,
    )>,
    witness: Arc<ArchitectureWitness>,
    base: NodeRef,
    domain: NodeRef,
    problem: Option<NodeRef>,
    subjects: Vec<NodeRef>,
    requirements: Vec<NodeRef>,
    internal: Vec<bool>,
    change: String,
    root_type: String,
}
#[derive(Debug)]
enum Backend {
    Finite(Arc<Shared>),
    Integer(integer::State),
}
#[derive(Debug)]
pub(super) struct Source {
    base: usize,
    parts: Vec<Part>,
    answer: Answer,
    request: Request,
    witness: Arc<ArchitectureWitness>,
    shared: Option<Backend>,
    range: Option<Vec<bool>>,
    ranges: BTreeMap<usize, Vec<bool>>,
    chosen: Option<Vec<usize>>,
    inputs: Vec<NodeRef>,
    context: super::call::Context,
    observation: Option<Arc<observation::State>>,
}
impl Source {
    fn finite(&self) -> Option<&Arc<Shared>> {
        match self.shared.as_ref()? {
            Backend::Finite(s) => Some(s),
            Backend::Integer(_) => None,
        }
    }
    fn integer(&self) -> Option<&integer::State> {
        match self.shared.as_ref()? {
            Backend::Integer(s) => Some(s),
            Backend::Finite(_) => None,
        }
    }
    fn root_type(&self) -> Option<&str> {
        match self.shared.as_ref()? {
            Backend::Finite(s) => Some(&s.root_type),
            Backend::Integer(s) => Some(&s.shared.root_type),
        }
    }
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
    /// 保持済み表示のmetadataだけを読む。動的な作用表は生成しない。
    pub(super) fn wire_ref(&self) -> Option<&Json> {
        self.part().wire_ref()
    }
    pub(super) fn wire(&self) -> Json {
        #[cfg(test)]
        super::data::observe_actual(
            (0, 0),
            self.source.context,
            "shared_repair_wire",
            self.source.base + self.index,
        );
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
    pub(super) fn retained_metadata(&self) -> (Support, Scope) {
        (self.part().support.clone(), self.part().scope.clone())
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.part().support.to_vec(), self.part().scope.clone())
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
        let root = self.source.root_type()?.to_owned();
        Some(match self.ty() {
            NodeType::Construction(T::RepairProblem) => ProjectionType::RepairProblem(root),
            NodeType::Construction(T::RepairObservation) => ProjectionType::RepairObservation(root),
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
fn domain_index(
    domain: &[Scalar],
    value: &Scalar,
    c: &Control,
) -> Result<Option<usize>, ValidationFailure> {
    for (position, member) in domain.iter().enumerate() {
        tick(c)?;
        if super::data::equal(member, value, c)? {
            return Ok(Some(position));
        }
    }
    Ok(None)
}

fn pins(shared: &Shared, enabled: &[bool]) -> Vec<Option<usize>> {
    let mut pins = vec![None; shared.compiled.relations.variables()];
    for o in &shared.compiled.outputs {
        if !shared.internal[o.subject] && !enabled[o.subject] {
            pins[o.column] = Some(o.baseline.expect("範囲を固定する問題には基準値がある"));
        }
    }
    if let Some((family, _)) = &shared.family {
        for (variant, map) in family.variants.iter().zip(&family.maps) {
            for o in &variant.outputs {
                if !shared.internal[o.subject] && !enabled[o.subject] {
                    pins[map[o.column]] = o.baseline;
                }
            }
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
/// 全点を要求する既存の商計算へ、生成済み有限関係の元座標を渡す。
pub(super) fn candidate_input(
    env: &Environment<'_>,
    g: &Graph,
    at: NodeRef,
    c: &Control,
) -> Result<change_result::CandidateInput, ValidationFailure> {
    env.recheck_node(g, g.get(at)?, at.0)?;
    let d = data(g, at)?;
    if let Some(state) = d.source.integer() {
        return integer::candidate_input(state, g.get(at)?.ty.clone());
    }
    let shared = d.source.finite().ok_or(internal!("商の共有候補域がない"))?;
    let solutions = g.get(at)?.ty == NodeType::Construction(T::SolutionSet);
    if !solutions && g.get(at)?.ty != NodeType::Construction(T::CandidateSpace) {
        return Err(internal!("商の共有候補域の型が違う").into());
    }
    let mut fixed = env
        .try_primitive_valuation_from(&shared.compiled.fixed, c)?
        .ok_or(internal!("商の基準値が不適合"))?;
    fixed.select_local_object(&shared.witness, c)?;
    let origin = Witness::Architecture(shared.witness.clone());
    let declaration = &origin.inputs().law().declarations()[&shared.change];
    let mut rows = vec![];
    let mut members = vec![];
    let mut append = |point: &[usize]| -> Result<(), ValidationFailure> {
        tick(c)?;
        let parameters = point
            .iter()
            .take(shared.compiled.parameter_count)
            .enumerate()
            .map(|(i, v)| shared.compiled.domains[i][*v].clone())
            .collect::<Vec<_>>();
        let candidate = change_evaluation::candidate(
            &fixed,
            declaration,
            &shared.compiled.subjects,
            &parameters,
        )?;
        // 除外されたguard/未定義の更新は、従来の商も定義域へ含めない。
        if matches!(
            candidate.update.state,
            change_evaluation::State::Excluded | change_evaluation::State::ConditionFailed
        ) {
            return Ok(());
        }
        let member = if solutions {
            true
        } else {
            let mut fixed = vec![None; shared.compiled.relations.variables()];
            for (i, value) in point
                .iter()
                .take(shared.compiled.parameter_count)
                .enumerate()
            {
                fixed[i] = Some(*value);
            }
            shared.compiled.relations.exists(&fixed, c)?
        };
        members.push(change_evaluation::SolutionRow {
            candidate: rows.len(),
            member: Some(member),
            missing: vec![],
        });
        rows.push(candidate);
        Ok(())
    };
    if solutions {
        let enabled = d
            .source
            .range
            .as_ref()
            .ok_or(internal!("商の解集合の範囲がない"))?;
        shared
            .compiled
            .relations
            .visit_solutions(&pins(shared, enabled), c, &mut append)?;
    } else if !shared.compiled.domains[..shared.compiled.parameter_count]
        .iter()
        .any(|domain| domain.is_empty())
    {
        let mut point = vec![0; shared.compiled.parameter_count];
        loop {
            append(&point)?;
            let mut cursor = point.len();
            loop {
                if cursor == 0 {
                    break;
                }
                cursor -= 1;
                point[cursor] += 1;
                if point[cursor] < shared.compiled.domains[cursor].len() {
                    break;
                }
                point[cursor] = 0;
            }
            if point.iter().all(|v| *v == 0) {
                break;
            }
        }
    }
    Ok(change_result::CandidateInput {
        integer_family: None,
        architecture: shared.base,
        witness: shared.witness.clone(),
        domain_type: if solutions {
            ProjectionType::SolutionSet(shared.root_type.clone())
        } else {
            ProjectionType::CandidateSpace(shared.root_type.clone())
        },
        search: change_search::Search {
            linear: None,
            rational: None,
            pending_integer: None,
            candidates: Some(change_evaluation::Candidates {
                subjects: shared.compiled.subjects.clone(),
                parameter_types: shared.compiled.parameter_types.clone(),
                rows,
                complete: true,
            }),
            solutions: members,
            requirements: shared.compiled.requirements.clone(),
            bindings: shared.compiled.bindings.clone(),
            missing: vec![],
            complete: true,
            valuation: shared.compiled.fixed.clone(),
        },
    })
}
pub(super) fn assignment_input(
    env: &Environment<'_>,
    g: &Graph,
    at: NodeRef,
) -> Result<change_result::AssignmentInput, ValidationFailure> {
    if let Ok(d) = data(g, at) {
        if let Some(state) = d.source.integer() {
            return integer::assignment_input(state);
        }
        let s = d
            .source
            .finite()
            .ok_or(internal!("元割当ての候補域がない"))?;
        let point = d
            .source
            .chosen
            .as_ref()
            .ok_or(internal!("元割当ての座標がない"))?;
        let width = if s.subjects.is_empty() {
            0
        } else {
            s.compiled.parameter_count / s.subjects.len()
        };
        let entries = s
            .compiled
            .subjects
            .iter()
            .enumerate()
            .map(|(i, subject)| {
                (
                    subject.clone(),
                    (i * width..(i + 1) * width)
                        .map(|column| s.compiled.domains[column][point[column]].clone())
                        .collect(),
                )
            })
            .collect();
        Ok(change_result::AssignmentInput {
            domain: s.domain,
            entries,
        })
    } else {
        change_result::assignment_input(env, g, at)
    }
}
fn same_problem(a: &Shared, b: &Shared) -> bool {
    a.problem.is_some()
        && b.problem.is_some()
        && same_domain(a, b)
        && a.internal == b.internal
        && a.compiled.requirements == b.compiled.requirements
        && match (&a.family, &b.family) {
            (None, None) => true,
            (Some((a, _)), Some((b, _))) => {
                a.view == b.view
                    && a.bindings == b.bindings
                    && a.fields == b.fields
                    && a.domains == b.domains
                    && a.points == b.points
            }
            _ => false,
        }
}
fn same_domain(a: &Shared, b: &Shared) -> bool {
    a.witness.construction().root() == b.witness.construction().root()
        && a.witness.construction().reading() == b.witness.construction().reading()
        && a.compiled.fixed == b.compiled.fixed
        && a.change == b.change
        && a.compiled.bindings == b.compiled.bindings
        && a.compiled.subjects == b.compiled.subjects
        && a.compiled.parameter_types == b.compiled.parameter_types
}
fn minimal(shared: &Shared, c: &Control) -> Result<Vec<Vec<bool>>, ValidationFailure> {
    minimal_masks(
        &shared.internal,
        |enabled| shared.compiled.relations.exists(&pins(shared, enabled), c),
        c,
    )
}
fn minimal_masks(
    internal: &[bool],
    mut exists: impl FnMut(&[bool]) -> Result<bool, ValidationFailure>,
    c: &Control,
) -> Result<Vec<Vec<bool>>, ValidationFailure> {
    let units = internal
        .iter()
        .enumerate()
        .filter_map(|(i, on)| (!on).then_some(i))
        .collect::<Vec<_>>();
    fn subset(a: &[bool], b: &[bool]) -> bool {
        a.iter().zip(b).all(|(a, b)| !a || *b)
    }
    // 未探索の上限だけを持つ。別の上限に含まれるものは重複しない。
    fn add(
        bounds: &mut Vec<Vec<bool>>,
        bound: Vec<bool>,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        for old in bounds.iter() {
            tick(c)?;
            if subset(&bound, old) {
                return Ok(());
            }
        }
        let mut at = 0;
        while at < bounds.len() {
            tick(c)?;
            if subset(&bounds[at], &bound) {
                bounds.swap_remove(at);
            } else {
                at += 1;
            }
        }
        bounds.push(bound);
        Ok(())
    }
    let empty = vec![false; internal.len()];
    if exists(&empty)? {
        return Ok(vec![empty]);
    }
    let mut all = empty;
    for i in &units {
        all[*i] = true;
    }
    let mut bounds = vec![all];
    let mut found = vec![];
    while let Some(upper) = bounds.pop() {
        tick(c)?;
        if !exists(&upper)? {
            continue;
        }
        let mut enabled = upper.clone();
        for unit in &units {
            tick(c)?;
            if !enabled[*unit] {
                continue;
            }
            enabled[*unit] = false;
            if !exists(&enabled)? {
                enabled[*unit] = true;
            }
        }
        // 他の極小範囲は、この範囲の少なくとも一単位を含まない。
        // 既知の極小範囲を含む上位集合を、生成する前に探索域から除く。
        let previous = std::mem::take(&mut bounds);
        for bound in std::iter::once(upper).chain(previous) {
            tick(c)?;
            if subset(&enabled, &bound) {
                for unit in &units {
                    if enabled[*unit] {
                        let mut next = bound.clone();
                        next[*unit] = false;
                        add(&mut bounds, next, c)?;
                    }
                }
            } else {
                add(&mut bounds, bound, c)?;
            }
        }
        found.push(enabled);
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
enum Application {
    Ready(change_evaluation::Candidate),
    Missing(Vec<Fact>),
}
fn family_application(
    env: &Environment<'_>,
    shared: &Shared,
    point: &[usize],
    c: &Control,
) -> Result<Application, ValidationFailure> {
    let (family, _) = shared
        .family
        .as_ref()
        .ok_or(internal!("適用する入力族がない"))?;
    let mut fixed = env
        .try_primitive_valuation_from(&shared.compiled.fixed, c)?
        .ok_or(internal!("適用する基準が不適合"))?;
    fixed.select_local_object(&shared.witness, c)?;
    let origin = Witness::Architecture(shared.witness.clone());
    let change = &origin.inputs().law().declarations()[&shared.change];
    let values = (0..shared.compiled.parameter_count)
        .map(|i| shared.compiled.domains[i][point[i]].clone())
        .collect::<Vec<_>>();
    let mut candidate =
        change_evaluation::candidate(&fixed, change, &shared.compiled.subjects, &values)?;
    let row =
        change_evaluation::solution_row(&fixed, &candidate, 0, &shared.compiled.requirements)?;
    if candidate.update.state == change_evaluation::State::Ready && row.member == Some(true) {
        return Ok(Application::Ready(candidate));
    }
    if row.member == Some(false)
        || matches!(
            candidate.update.state,
            change_evaluation::State::Excluded | change_evaluation::State::ConditionFailed
        )
    {
        return Err(internal!("共通候補が現在の原式で反証された").into());
    }
    let need_values = candidate.update.state != change_evaluation::State::Ready;
    let mut first = None::<Vec<(Fact, Scalar)>>;
    let mut constant = true;
    let mut support = candidate
        .update
        .support
        .iter()
        .cloned()
        .collect::<std::collections::BTreeSet<_>>();
    let mut scope = candidate.update.scope.clone();
    for index in 0..family.points.len() {
        tick(c)?;
        let updated = family.environment(&fixed, index)?;
        let at =
            change_evaluation::candidate(&updated, change, &shared.compiled.subjects, &values)?;
        let row =
            change_evaluation::solution_row(&updated, &at, index, &shared.compiled.requirements)?;
        if row.member != Some(true) || at.update.state != change_evaluation::State::Ready {
            return Err(internal!("共通候補の元式への再代入が入力族で成立しない").into());
        }
        if need_values {
            if let Some(first) = &first {
                if first.len() != at.update.values.len() {
                    return Err(internal!("共通候補の更新先が入力ごとに異なる").into());
                }
                for (fact, value) in first {
                    let other = &at
                        .update
                        .values
                        .iter()
                        .find(|(f, _)| {
                            crate::observed::environment::repair_problem::same_slot(f, fact)
                        })
                        .ok_or(internal!("共通更新先がない"))?
                        .1;
                    constant &= crate::observed::data::equal(value, other, c)?;
                }
            } else {
                first = Some(at.update.values.clone());
            }
        }
        support.extend(at.update.support);
        scope.merge(&at.update.scope);
    }
    if candidate.update.state != change_evaluation::State::Ready {
        if !constant {
            let mut missing = candidate.update.missing;
            missing.extend(row.missing);
            missing.sort();
            missing.dedup();
            return Ok(Application::Missing(missing));
        }
        candidate.update.values = first.ok_or(internal!("共通候補の入力族が空"))?;
        candidate.update.state = change_evaluation::State::Ready;
    }
    candidate.update.missing.clear();
    candidate.update.support = support.into_iter().collect();
    candidate.update.scope = scope;
    candidate.update.scope.completions |= !family.fields.is_empty();
    Ok(Application::Ready(candidate))
}
fn pending_application(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
    shared: Arc<Shared>,
    inputs: Vec<NodeRef>,
    missing: Vec<Fact>,
) -> Result<Source, ValidationFailure> {
    if missing.is_empty() {
        return unsupported(env, g, r);
    }
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let origin = Witness::Architecture(shared.witness.clone());
    let Signature::Change { params, body, .. } =
        &origin.inputs().law().declarations()[&shared.change].signature
    else {
        unreachable!()
    };
    let parameters = params
        .iter()
        .map(|p| (p.name.clone(), p.ty.clone()))
        .collect::<Vec<_>>();
    let expression = change_result::source_expression(&mut b, env, *body, &[], &parameters)?;
    b.parts[expression.0 - base]
        .arguments
        .extend(inputs.iter().copied());
    let claim = condition(&mut b, r, inputs.clone(), Decision::Undetermined)?;
    let mut a = answer(r, claim, Decision::Undetermined, BTreeMap::new(), &b);
    a.reasons.push(Reason {
        kind: ReasonKind::Missing,
        request: r.id.clone(),
        dependencies: vec![expression],
        missing,
        location: None,
    });
    Ok(Source {
        base,
        parts: b.parts,
        answer: a,
        request: r.clone(),
        witness: shared.witness.clone(),
        shared: Some(Backend::Finite(shared)),
        range: None,
        ranges: BTreeMap::new(),
        chosen: None,
        inputs,
        context: g.active,
        observation: None,
    })
}
fn apply_object(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    s: &Shared,
    point: &[usize],
    selection: (NodeRef, NodeRef),
    claim: NodeRef,
    checked: Option<change_evaluation::Candidate>,
) -> Result<(NodeRef, Vec<NodeRef>), ValidationFailure> {
    let (selected, solutions) = selection;
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
    let candidate = if let Some(candidate) = checked {
        candidate
    } else {
        let candidate =
            change_evaluation::candidate(&fixed, change, &s.compiled.subjects, &values)?;
        let row = change_evaluation::solution_row(&fixed, &candidate, 0, &s.compiled.requirements)?;
        if row.member != Some(true) || candidate.update.state != change_evaluation::State::Ready {
            return Err(internal!("選択候補が元更新・Lawへの再代入を満たさない").into());
        }
        candidate
    };
    for output in &s.compiled.outputs {
        tick(c)?;
        if s.family
            .as_ref()
            .is_some_and(|(family, _)| !family.fields.is_empty())
        {
            continue;
        }
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
    if let Some(source) = integer::consume_at(env, g, r, c, head)? {
        return Ok(source);
    }
    let (mut shared, mut enabled, previous_chosen) = if let Ok(d) = data(g, head) {
        (
            d.source
                .finite()
                .ok_or(internal!("未構成の修復問題を消費した"))?
                .clone(),
            d.source.range.clone(),
            d.source.chosen.clone(),
        )
    } else if r.kind == QuestionKind::Candidate {
        let shared = legacy(env, g, head, c)?;
        let enabled = vec![true; shared.subjects.len()];
        (shared, Some(enabled), None)
    } else if r.kind == QuestionKind::Apply {
        let (shared, point) = prepare::original_assignment(env, g, head, c)?;
        (shared, None, Some(point))
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
            if let Some(other) = d.source.finite() {
                invalid = !same_problem(&shared, other);
                enabled = d
                    .source
                    .range
                    .clone()
                    .or_else(|| d.source.ranges.get(&d.index).cloned());
            } else {
                invalid = true;
            }
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
            if let Some(other) = d.source.finite() {
                (other.clone(), d.source.range.clone())
            } else {
                invalid = true;
                (shared.clone(), None)
            }
        } else if shared.problem.is_none()
            && matches!(&g.get(at)?.payload,Some(Payload::Construction(v)) if v.project(&[ProjectionStep::Field("domain".into())]).map(|(r,_)|r)==Some(shared.domain))
        {
            (shared.clone(), Some(vec![true; shared.subjects.len()]))
        } else {
            let old = legacy(env, g, at, c)?;
            let range = Some(vec![true; old.subjects.len()]);
            (old, range)
        };
        enabled = target_range;
        invalid |= !same_domain(&shared, &other);
        chosen = None;
        if !invalid {
            let original = previous_chosen
                .as_deref()
                .ok_or(internal!("選択した元割当てがない"))?;
            let mut target_pins = pins(
                &other,
                enabled.as_ref().ok_or(internal!("解集合の範囲がない"))?,
            );
            for i in 0..shared.compiled.parameter_count {
                let value = &shared.compiled.domains[i][original[i]];
                let index = domain_index(&other.compiled.domains[i], value, c)?;
                if index.is_none() {
                    invalid = true;
                    break;
                }
                target_pins[i] = index;
            }
            if !invalid {
                chosen = other.compiled.relations.witness(&target_pins, c)?;
                invalid = chosen.is_none();
            }
        }
        shared = other;
    }
    let mut checked_application = None;
    if r.kind == QuestionKind::Apply && !invalid && shared.family.is_some() {
        match family_application(
            env,
            &shared,
            chosen.as_deref().ok_or(internal!("共通割当てがない"))?,
            c,
        )? {
            Application::Ready(candidate) => checked_application = Some(candidate),
            Application::Missing(missing) => {
                return pending_application(env, g, r, shared, inputs, missing);
            }
        }
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
            (head, set),
            claim,
            checked_application.take(),
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
        shared: Some(Backend::Finite(shared)),
        range: enabled,
        ranges,
        chosen,
        inputs,
        context: g.active,
        observation: None,
    })
}
/// 対応範囲外は通常の未決として残し、独立した後続要求を止めない。
fn unsupported(
    env: &Environment<'_>,
    g: &mut Graph,
    r: &Request,
) -> Result<Source, ValidationFailure> {
    let head = reference(env, g, &r.head)?;
    let Some(Payload::Construction(value)) = &g.get(head)?.payload else {
        return Err(internal!("未対応の修復入力がnativeでない").into());
    };
    let Witness::Architecture(witness) = &value.witness else {
        return Err(internal!("未対応の修復入力の元対象がない").into());
    };
    let witness = witness.clone();
    let mut inputs = vec![head];
    for argument in &r.arguments {
        if matches!(argument.value, Selector::Answer { .. }) {
            inputs.push(reference(env, g, &argument.value)?);
        }
    }
    let base = g.nodes.len();
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let origin = Witness::Architecture(witness.clone());
    let change = origin
        .request()
        .arguments
        .iter()
        .find_map(|a| match (&*a.name, &a.value) {
            ("using", Selector::Declaration { name }) => {
                env.indexes.inputs.law().declarations().get(name)
            }
            _ => None,
        })
        .ok_or(internal!("未対応の候補の元changeがない"))?;
    let Signature::Change { params, body, .. } = &change.signature else {
        return Err(internal!("未対応の候補の元操作がchangeでない").into());
    };
    let parameters = params
        .iter()
        .map(|p| (p.name.clone(), p.ty.clone()))
        .collect::<Vec<_>>();
    let expression = change_result::source_expression(&mut b, env, *body, &[], &parameters)?;
    let claim = condition(&mut b, r, inputs.clone(), Decision::Undetermined)?;
    let mut a = answer(r, claim, Decision::Undetermined, BTreeMap::new(), &b);
    a.reasons.push(Reason {
        kind: ReasonKind::UnsupportedAlgorithm {
            question: r.kind,
            operand_types: params.iter().map(|p| p.ty.clone()).collect(),
            method: "finite_repair_relation".into(),
        },
        request: r.id.clone(),
        dependencies: vec![expression],
        missing: vec![],
        location: None,
    });
    Ok(Source {
        base,
        parts: b.parts,
        answer: a,
        request: r.clone(),
        witness,
        shared: None,
        range: None,
        ranges: BTreeMap::new(),
        chosen: None,
        inputs,
        context: g.active,
        observation: None,
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
        let result = if r.kind == QuestionKind::Prepare && integer::is_prepare(env, r) {
            integer::prepare(prepared, env, g, r, c)
        } else if r.kind == QuestionKind::Prepare {
            prepare(prepared, env, g, r, c)
        } else if r.kind == QuestionKind::Observe {
            observation::compute(env, g, r, c)
        } else {
            consume(env, g, r, c)
        };
        let source = Arc::new(match result {
            Err(ValidationFailure::UnsupportedExpression { .. })
                if !matches!(r.kind, QuestionKind::Prepare | QuestionKind::Observe) =>
            {
                unsupported(env, g, r)?
            }
            result => result?,
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
        #[cfg(test)]
        super::data::observe_actual(
            (0, 0),
            self.source.context,
            "shared_repair_recheck",
            self.source.base,
        );
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

/// 同じ finite change の元個体・parameter 値を現在の解集合で照合する。
pub(super) fn reobserved_membership(
    previous: &Node,
    current: &Node,
    subject_image: impl Fn(&Scalar) -> Option<Scalar>,
    c: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    let (Some(Payload::Construction(old)), Some(Payload::Construction(new))) =
        (&previous.payload, &current.payload)
    else {
        return Ok(None);
    };
    let (D::SharedRepair(old), D::SharedRepair(new)) = (&old.data, &new.data) else {
        return Ok(None);
    };
    let (Some(a), Some(b), Some(chosen), Some(enabled)) = (
        old.source.finite(),
        new.source.finite(),
        &old.source.chosen,
        &new.source.range,
    ) else {
        return Ok(None);
    };
    if old.ty() != NodeType::Construction(T::Assignment)
        || new.ty() != NodeType::Construction(T::SolutionSet)
        || a.change != b.change
        || subject_image(&Scalar::Subject {
            snapshot: a.witness.construction().root().snapshot.clone(),
            subject: a.witness.construction().root().subject.clone(),
            entity: a.root_type.clone(),
        }) != Some(Scalar::Subject {
            snapshot: b.witness.construction().root().snapshot.clone(),
            subject: b.witness.construction().root().subject.clone(),
            entity: b.root_type.clone(),
        })
        || a.compiled.subjects.len() != b.compiled.subjects.len()
        || a.compiled.parameter_count != b.compiled.parameter_count
    {
        return Ok(None);
    }
    let width = a
        .compiled
        .parameter_count
        .checked_div(a.compiled.subjects.len())
        .unwrap_or(0);
    let mut target_subjects = BTreeMap::new();
    for (i, subject) in b.compiled.subjects.iter().enumerate() {
        tick(c)?;
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = subject
        else {
            return Ok(None);
        };
        target_subjects.insert((snapshot.as_str(), subject.as_str(), entity.as_str()), i);
    }
    let mut target_pins = pins(b, enabled);
    for (i, subject) in a.compiled.subjects.iter().enumerate() {
        tick(c)?;
        let image = subject_image(subject);

        let Some(Scalar::Subject {
            snapshot,
            subject,
            entity,
        }) = image.as_ref()
        else {
            return Ok(None);
        };
        let Some(&j) = target_subjects.get(&(snapshot.as_str(), subject.as_str(), entity.as_str()))
        else {
            return Ok(None);
        };
        for k in 0..width {
            tick(c)?;
            let index = i * width + k;
            let target = j * width + k;
            let original = &a.compiled.domains[index][chosen[index]];
            let found = domain_index(&b.compiled.domains[target], original, c)?;
            let Some(found) = found else {
                return Ok(Some(false));
            };
            target_pins[target] = Some(found);
        }
    }
    Ok(Some(b.compiled.relations.exists(&target_pins, c)?))
}
