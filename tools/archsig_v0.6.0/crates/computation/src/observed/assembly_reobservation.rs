//! 明示した同一性の下で、局所組立ての不足位置と有限候補を現在の入力へ照合する。
use super::{
    EvaluationFailure, ObservedEvaluation, PreparedObserved, assembly_plan,
    construction_result::ConstructionData,
    environment::Environment,
    model_assembly,
    projection::ProjectionStep,
    reevaluate_observed,
    request::{QuestionKind, Request, Selector},
    result::{Decision, Fact, Node, Payload, ReasonKind, Scalar, ValidationFailure},
};
use crate::construction::{ConstructionFailure, is_owner_fact, owner_slot_for};
use archsig_common::{
    canonical::{Json, JsonObject},
    control::{Checkpoint, Control, Signal},
};
use archsig_input::{
    archmap::{FactData, Slot, Subject, Value},
    law::model::Signature,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

/// 明示的な同一性の仮定。表の各行は before と after の subject ID。
#[derive(Debug)]
pub struct AssemblyAlignment<'a> {
    pub before_snapshot: &'a str,
    pub after_snapshot: &'a str,
    pub reading: &'a str,
    pub subjects: &'a [(&'a str, &'a str)],
    pub assembly: &'a str,
    pub previous_candidate: &'a str,
    pub current_solve: &'a str,
}

/// 同じ組立て要求の局所選択に対する担当ごとの対応。
#[derive(Clone, Copy, Debug)]
pub struct AssemblyCandidateAlignment<'a> {
    /// `local.<participant>` の引数名。
    pub participant: &'a str,
    pub previous_candidate: &'a str,
    pub current_solve: &'a str,
}

#[derive(Debug)]
pub struct MultiAssemblyAlignment<'a> {
    pub before_snapshot: &'a str,
    pub after_snapshot: &'a str,
    pub reading: &'a str,
    pub subjects: &'a [(&'a str, &'a str)],
    pub assembly: &'a str,
    pub candidates: &'a [AssemblyCandidateAlignment<'a>],
}

#[derive(Debug)]
pub enum ReobservationFailure {
    InvalidCorrespondence(String),
    Unsupported(String),
    Evaluation(Box<EvaluationFailure>),
    Stopped(Signal),
}

impl From<Signal> for ReobservationFailure {
    fn from(signal: Signal) -> Self {
        Self::Stopped(signal)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidateContinuity {
    Retained,
    Excluded,
    Undetermined,
}

#[derive(Debug)]
pub struct ObservationMatch {
    needed: Fact,
    observed: Option<Fact>,
}

#[derive(Debug)]
pub struct ReobservedAssembly {
    evaluation: ObservedEvaluation,
    observations: Vec<ObservationMatch>,
    layout_missing: Vec<Fact>,
    candidates: Vec<ReobservedCandidate>,
    assembly_status: Option<Decision>,
    continuity_stop: Option<Signal>,
}

/// 現在の solve 上で確認した局所候補と、組立てで消費した候補の対応。
#[derive(Debug)]
pub struct ReobservedCandidate {
    participant: String,
    previous_candidate: String,
    current_solve: String,
    continuity: CandidateContinuity,
    undecided: Option<ContinuityPending>,
    current_assignment: Option<CurrentAssignment>,
    missing: Vec<Fact>,
    selected_candidate: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContinuityPending {
    LayoutMissing,
    Missing,
    PreviousAssignmentUnavailable,
    CurrentSolveUnavailable,
    IncompatibleDomain,
    Interrupted,
}

impl ContinuityPending {
    fn wire(self) -> &'static str {
        match self {
            Self::LayoutMissing => "layout_missing",
            Self::Missing => "missing",
            Self::PreviousAssignmentUnavailable => "previous_assignment_unavailable",
            Self::CurrentSolveUnavailable => "current_solve_unavailable",
            Self::IncompatibleDomain => "incompatible_domain",
            Self::Interrupted => "interrupted",
        }
    }
}

#[derive(Debug)]
pub struct CurrentAssignment {
    entries: Vec<(Scalar, Vec<Scalar>)>,
}

impl CurrentAssignment {
    /// 現在の主体・宣言順へ戻した元 parameter 値。
    pub fn entries_wire(&self) -> Json {
        let typed =
            |value: &Scalar| Json::obj([("type", value.ty().wire()), ("value", value.wire())]);
        Json::Arr(
            self.entries
                .iter()
                .map(|(subject, parameters)| {
                    Json::obj([
                        ("subject", typed(subject)),
                        (
                            "parameters",
                            Json::Arr(parameters.iter().map(typed).collect()),
                        ),
                    ])
                })
                .collect(),
        )
    }
}

impl ReobservedCandidate {
    pub fn participant(&self) -> &str {
        &self.participant
    }
    pub fn previous_candidate(&self) -> &str {
        &self.previous_candidate
    }
    pub fn current_solve(&self) -> &str {
        &self.current_solve
    }
    pub fn pending_reason(&self) -> Option<ContinuityPending> {
        self.undecided
    }
    pub fn continuity(&self) -> CandidateContinuity {
        self.continuity
    }
    pub fn current_assignment(&self) -> Option<&CurrentAssignment> {
        self.current_assignment.as_ref()
    }
    pub fn missing(&self) -> &[Fact] {
        &self.missing
    }
    pub fn selected_candidate(&self) -> Option<&str> {
        self.selected_candidate.as_deref()
    }
}

impl ObservationMatch {
    pub fn needed(&self) -> &Fact {
        &self.needed
    }
    pub fn observed(&self) -> Option<&Fact> {
        self.observed.as_ref()
    }
}

impl ReobservedAssembly {
    pub fn evaluation(&self) -> &ObservedEvaluation {
        &self.evaluation
    }
    pub fn observations(&self) -> &[ObservationMatch] {
        &self.observations
    }
    /// Slots that prevented comparing the two evaluated layouts.
    pub fn layout_missing(&self) -> &[Fact] {
        &self.layout_missing
    }
    pub fn candidates(&self) -> &[ReobservedCandidate] {
        &self.candidates
    }
    pub fn assembly_status(&self) -> Option<&'static str> {
        self.assembly_status.map(Decision::wire)
    }
    /// 従来の一担当の継続結果。
    pub fn candidate(&self) -> CandidateContinuity {
        match self.candidates.as_slice() {
            [candidate] => candidate.continuity(),
            _ => CandidateContinuity::Undetermined,
        }
    }
    /// 従来の一担当で、現在の成立した組立てに使った候補。
    pub fn selected_candidate(&self) -> Option<&str> {
        match self.candidates.as_slice() {
            [candidate] if self.assembly_status == Some(Decision::Established) => {
                candidate.selected_candidate()
            }
            _ => None,
        }
    }
    pub fn continuity_wire(&self) -> Json {
        let observations = self
            .observations
            .iter()
            .map(|m| {
                let mut row = JsonObject::from([("needed".into(), m.needed.wire())]);
                if let Some(fact) = &m.observed {
                    row.insert("observed".into(), fact.wire());
                }
                Json::Obj(row)
            })
            .collect();
        let candidates = self
            .candidates
            .iter()
            .map(|candidate| {
                let mut row = JsonObject::from([
                    ("participant".into(), Json::str(&candidate.participant)),
                    (
                        "previous_candidate".into(),
                        Json::str(&candidate.previous_candidate),
                    ),
                    ("current_solve".into(), Json::str(&candidate.current_solve)),
                    (
                        "status".into(),
                        Json::str(match candidate.continuity {
                            CandidateContinuity::Retained => "retained",
                            CandidateContinuity::Excluded => "excluded",
                            CandidateContinuity::Undetermined => "undetermined",
                        }),
                    ),
                    (
                        "missing".into(),
                        Json::Arr(candidate.missing.iter().map(Fact::wire).collect()),
                    ),
                ]);
                if let Some(reason) = candidate.pending_reason() {
                    row.insert("reason".into(), Json::str(reason.wire()));
                }
                if let Some(assignment) = candidate.current_assignment() {
                    row.insert(
                        "current_assignment".into(),
                        Json::obj([("entries", assignment.entries_wire())]),
                    );
                }
                if let Some(selected) = candidate.selected_candidate() {
                    row.insert("selected_candidate".into(), Json::str(selected));
                }
                Json::Obj(row)
            })
            .collect();
        let mut result = JsonObject::from([
            ("observations".into(), Json::Arr(observations)),
            (
                "layout_missing".into(),
                Json::Arr(self.layout_missing.iter().map(Fact::wire).collect()),
            ),
            ("candidates".into(), Json::Arr(candidates)),
        ]);
        if let Some(status) = self.assembly_status() {
            result.insert("assembly_status".into(), Json::str(status));
        }
        Json::Obj(result)
    }
    pub fn into_evaluation(self) -> ObservedEvaluation {
        self.evaluation
    }
    pub fn continuity_stop(&self) -> Option<Signal> {
        self.continuity_stop
    }
}

fn owner_failure(failure: ConstructionFailure) -> ReobservationFailure {
    match failure {
        ConstructionFailure::Stopped(signal) => ReobservationFailure::Stopped(signal),
        _ => ReobservationFailure::Unsupported("定義上の owner を確認できない".into()),
    }
}

fn invalid(message: &str) -> ReobservationFailure {
    ReobservationFailure::InvalidCorrespondence(message.into())
}

fn fact(subject: &Subject, field: &archsig_input::archmap::Field, atom: Option<String>) -> Fact {
    Fact::from(FactData {
        snapshot: subject.snapshot.clone(),
        subject: subject.id.clone(),
        field: Some(field.name.clone()),
        atom,
    })
}

fn question<'a>(
    prepared: &'a PreparedObserved,
    id: &str,
    kind: QuestionKind,
) -> Result<&'a Request, ReobservationFailure> {
    prepared
        .requests()
        .requests()
        .iter()
        .find(|r| r.id == id && r.kind == kind)
        .ok_or_else(|| invalid("対応する種類・ID の元要求がない"))
}

fn output<'a>(evaluation: &'a ObservedEvaluation, id: &str, field: &str) -> Option<&'a Node> {
    let reference = evaluation
        .answers
        .iter()
        .find(|a| a.id == id)?
        .outputs
        .get(field)?;
    evaluation.nodes.get(reference.0)
}

fn selected_reading(prepared: &PreparedObserved, question: &Request, reading: &str) -> bool {
    question
        .declaration()
        .is_some_and(|name| prepared.inputs().law().declarations()[name].reading == reading)
}

fn subject_index<'a>(
    subjects: &'a [Subject],
    control: &Control,
) -> Result<BTreeMap<&'a str, &'a Subject>, ReobservationFailure> {
    let mut roster = BTreeMap::new();
    for subject in subjects {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        roster.insert(subject.id.as_str(), subject);
    }
    Ok(roster)
}

fn answer_field<'a>(selector: &'a Selector, field: &str) -> Option<&'a str> {
    match selector {
        Selector::Answer { id, path } if matches!(path.as_slice(), [ProjectionStep::Field(name)] if name == field) => {
            Some(id)
        }
        _ => None,
    }
}

fn repair_selection<'a>(
    prepared: &'a PreparedObserved,
    selector: &Selector,
    solve: &Request,
) -> Result<(&'a Request, &'a Request), ReobservationFailure> {
    let apply = answer_field(selector, "object")
        .ok_or_else(|| invalid("局所選択が apply.object を指さない"))?;
    let apply = question(prepared, apply, QuestionKind::Apply)?;
    let selected = answer_field(&apply.head, "assignment")
        .ok_or_else(|| invalid("局所 apply に選択 Assignment がない"))?;
    let selected = question(prepared, selected, QuestionKind::Candidate)?;
    let in_solutions = apply
        .arguments
        .iter()
        .find(|a| a.name == "in")
        .and_then(|a| answer_field(&a.value, "solutions"));
    if in_solutions != Some(solve.id.as_str())
        || answer_field(&selected.head, "solutions") != Some(solve.id.as_str())
    {
        return Err(invalid(
            "局所 apply と選択候補が照合対象の solve を消費しない",
        ));
    }
    Ok((apply, selected))
}

struct Layout {
    roots: Option<Vec<Fact>>,
    shared: Option<SharedLayout>,
    missing: Vec<Fact>,
}
enum SharedLayout {
    Reads(Vec<(Fact, Fact)>),
    Checked(Arc<model_assembly::Model>),
}
type SharedPartition = BTreeSet<BTreeSet<Fact>>;

fn retained_layout<'a>(
    evaluation: &'a ObservedEvaluation,
    id: &str,
) -> Option<(
    &'a assembly_plan::Assembly,
    &'a super::architecture_result::Architecture,
)> {
    let answer = evaluation.answers.iter().find(|answer| answer.id == id)?;
    let node = evaluation.nodes.get(answer.claim?.0)?;
    let Some(Payload::Construction(value)) = &node.payload else {
        return None;
    };
    let ConstructionData::Build(data) = &value.data else {
        return None;
    };
    let plan = data.plan();
    Some((plan.assembly.as_deref()?, &plan.architecture))
}

fn checked_layout(
    evaluation: &ObservedEvaluation,
    request: &Request,
    control: &Control,
) -> Result<Layout, ReobservationFailure> {
    if let Some((assembly, architecture)) = retained_layout(evaluation, &request.id) {
        match &assembly.failure {
            Some(assembly_plan::Failure::Unsupported(detail)) if detail.affects_layout => {
                return Err(ReobservationFailure::Unsupported(detail.detail.clone()));
            }
            Some(assembly_plan::Failure::Rejected(detail)) if detail.affects_layout => {
                return Err(invalid(&detail.detail));
            }
            _ => {}
        }
        if let Some(model) = &assembly.model {
            return Ok(Layout {
                roots: Some(
                    model
                        .fragments
                        .iter()
                        .map(|fragment| fragment.root().clone())
                        .collect(),
                ),
                shared: Some(SharedLayout::Checked(model.clone())),
                missing: vec![],
            });
        }
        let mut layout =
            layout_from_reads(&assembly.fragments, &assembly.interfaces, control, |_| {
                Ok(())
            })?;
        if assembly.checked_ownership {
            if let Some(assembly_plan::Failure::Missing(positions)) = &assembly.failure {
                layout.missing.extend(
                    positions
                        .iter()
                        .filter(|fact| is_owner_fact(evaluation.prepared().inputs(), fact))
                        .cloned(),
                );
            }
        } else {
            let domain = architecture.witness.construction().local_domain();
            if domain.known().len() != 1 {
                return Err(invalid("組立て先rootに既存の所属個体がある"));
            }
            layout.missing.extend(
                domain
                    .conditional()
                    .iter()
                    .map(|member| member.owner_slot().clone()),
            );
        }
        return Ok(layout);
    }
    read_layout(evaluation.prepared(), request, control)
}

fn read_layout(
    prepared: &PreparedObserved,
    request: &Request,
    control: &Control,
) -> Result<Layout, ReobservationFailure> {
    let unsupported = |message: &str| ReobservationFailure::Unsupported(message.into());
    let classify = |failure| match failure {
        ValidationFailure::Stop(signal) => ReobservationFailure::Stopped(signal),
        _ => unsupported("組立ての View を現在の原始観測で読めない"),
    };
    let env = Environment::with_prepared(prepared, control)?;
    let mut bindings = Vec::new();
    for arg in &request.arguments {
        if let Some(name) = arg.name.strip_prefix("bind.") {
            control.checkpoint(Checkpoint::ConfigurationMap)?;
            let Selector::Subject { snapshot, subject } = &arg.value else {
                return Err(unsupported(
                    "組立て View の束縛には明示した原始参照を要求する",
                ));
            };
            let entity = env
                .indexes
                .subject(snapshot, subject)
                .map_err(|_| invalid("組立て View の参照先がない"))?
                .ty
                .to_string();
            bindings.push((
                name.to_owned(),
                Scalar::Subject {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    entity,
                },
            ));
        }
    }
    let along = request
        .arguments
        .iter()
        .find(|a| a.name == "along")
        .and_then(|a| match &a.value {
            Selector::Declaration { name } => Some(name.as_str()),
            _ => None,
        })
        .ok_or_else(|| unsupported("共有 View 宣言がない"))?;
    let head = request
        .declaration()
        .ok_or_else(|| unsupported("担当 View 宣言がない"))?;
    let fragments = assembly_plan::read(&env, head, &bindings, false, false).map_err(classify)?;
    let interfaces = assembly_plan::read(&env, along, &bindings, false, false).map_err(classify)?;
    let target = layout_target(request)?;
    let reading = prepared.inputs().law().declarations()[head]
        .reading
        .as_str();
    let mut layout = layout_from_reads(&fragments, &interfaces, control, |layout| {
        if let Some(problem) = super::model_assembly::layout_snapshot(
            &env.indexes,
            reading,
            &target,
            layout.roots.as_deref().unwrap_or_default(),
            match &layout.shared {
                Some(SharedLayout::Reads(pairs)) => pairs.as_slice(),
                _ => &[],
            },
            control,
        )
        .map_err(classify)?
        {
            return Err(ReobservationFailure::Unsupported(problem.detail));
        }
        Ok(())
    })?;
    if let Some(roots) = &layout.roots
        && let Some(problem) =
            super::model_assembly::layout_root_condition(&env.indexes, &target, roots, control)
                .map_err(classify)?
    {
        return Err(invalid(&problem.detail));
    }
    check_target_ownership(prepared, request, &mut layout, control)?;
    Ok(layout)
}

fn layout_target(request: &Request) -> Result<Fact, ReobservationFailure> {
    let target = request.arguments.iter().find(|arg| arg.name == "on");
    let Some(Selector::Subject { snapshot, subject }) = target.map(|arg| &arg.value) else {
        return Err(invalid("組立て先の明示rootがない"));
    };
    Ok(Fact::from(FactData {
        snapshot: snapshot.clone(),
        subject: subject.clone(),
        field: None,
        atom: None,
    }))
}

fn check_target_ownership(
    prepared: &PreparedObserved,
    request: &Request,
    layout: &mut Layout,
    control: &Control,
) -> Result<(), ReobservationFailure> {
    let target = layout_target(request)?;
    let root = model_assembly::subject(prepared.inputs(), &target)
        .map_err(|_| invalid("組立て先の root がない"))?;
    let head = request
        .declaration()
        .ok_or_else(|| invalid("担当 View 宣言がない"))?;
    let reading = &prepared.inputs().law().declarations()[head].reading;
    let (occupied, missing) = crate::construction::layout_ownership(
        prepared.inputs(),
        reading,
        root.ty.as_str(),
        &target,
        control,
    )
    .map_err(|failure| match failure {
        crate::construction::ConstructionFailure::Stopped(signal) => {
            ReobservationFailure::Stopped(signal)
        }
        _ => ReobservationFailure::Unsupported("組立ての所属域を現在の原始観測で読めない".into()),
    })?;
    if let Some(occupied) = occupied {
        if occupied.snapshot != target.snapshot {
            return Err(ReobservationFailure::Unsupported(
                "組立て先の所属個体が別 snapshot に属する".into(),
            ));
        }
        return Err(invalid("組立て先rootに既存の所属個体がある"));
    }
    layout.missing.extend(missing);
    Ok(())
}

fn layout_from_reads(
    fragments: &assembly_plan::Read,
    interfaces: &assembly_plan::Read,
    control: &Control,
    validate_snapshot: impl FnOnce(&Layout) -> Result<(), ReobservationFailure>,
) -> Result<Layout, ReobservationFailure> {
    let classify = |failure| match failure {
        ValidationFailure::Stop(signal) => ReobservationFailure::Stopped(signal),
        _ => ReobservationFailure::Unsupported("組立ての View を現在の原始観測で読めない".into()),
    };
    let roots = assembly_plan::fragment_roots(fragments, control).map_err(classify)?;
    let shared = interfaces
        .value
        .as_ref()
        .map(|value| assembly_plan::interfaces(value, control))
        .transpose()
        .map_err(classify)?;
    let mut missing = fragments.metadata.missing.clone();
    missing.extend(interfaces.metadata.missing.iter().cloned());
    missing.sort();
    missing.dedup();
    let layout = Layout {
        roots,
        shared: shared.map(SharedLayout::Reads),
        missing,
    };
    validate_snapshot(&layout)?;
    if fragments.metadata.failed || interfaces.metadata.failed {
        return Err(invalid("組立て View の適用条件が成立しない"));
    }
    if let Some(problem) = fragments
        .unsupported
        .as_ref()
        .or(interfaces.unsupported.as_ref())
    {
        return Err(ReobservationFailure::Unsupported(problem.detail.clone()));
    }
    if layout.roots.is_none() && fragments.metadata.missing.is_empty() {
        return Err(ReobservationFailure::Unsupported(
            "担当集合を確定できない".into(),
        ));
    }
    if layout.shared.is_none() && interfaces.metadata.missing.is_empty() {
        return Err(ReobservationFailure::Unsupported(
            "共有対を確定できない".into(),
        ));
    }
    Ok(layout)
}

fn checked_shared_partition(
    layout: &Layout,
    roster: &BTreeMap<&str, &Subject>,
    snapshot: &str,
    image: impl Fn(&Fact) -> Result<Fact, ReobservationFailure>,
    check: (&PreparedObserved, &Request),
    missing: &mut Vec<Fact>,
    control: &Control,
) -> Result<SharedPartition, ReobservationFailure> {
    let mut classes = BTreeMap::<&Fact, BTreeSet<Fact>>::new();
    let shared = match layout
        .shared
        .as_ref()
        .ok_or_else(|| invalid("共有対が未確定"))?
    {
        SharedLayout::Checked(model) => {
            let construction = &model.construction;
            let transport = construction
                .transport()
                .ok_or_else(|| invalid("検査済み組立ての参照輸送がない"))?;
            for (member, representative) in transport {
                control.checkpoint(Checkpoint::ConfigurationMap)?;
                // The transport also contains identities and maps fragment roots to the target.
                if member == representative || representative == construction.root() {
                    continue;
                }
                let class = classes.entry(representative).or_default();
                if class.is_empty() {
                    class.insert(image(representative)?);
                }
                class.insert(image(member)?);
            }
            return Ok(classes.into_values().collect());
        }
        SharedLayout::Reads(pairs) => pairs,
    };
    let roots = layout.roots.as_ref().map(|roots| {
        roots
            .iter()
            .map(|root| root.subject.as_str())
            .collect::<BTreeSet<_>>()
    });
    let mut owner_root = |fact: &Fact| -> Result<Option<&str>, ReobservationFailure> {
        if fact.snapshot != snapshot {
            return Err(ReobservationFailure::Unsupported(
                "共有対が別 snapshot の参照を含む".into(),
            ));
        }
        let member = roster
            .get(fact.subject.as_str())
            .copied()
            .ok_or_else(|| invalid("共有対の主体がない"))?;
        let (field, _) = owner_slot_for(check.0.inputs(), member, None, control)
            .map_err(owner_failure)?
            .ok_or_else(|| invalid("共有対の個体が担当 root に所属しない"))?;
        match &field.slot {
            Slot::Known {
                value:
                    Value::Ref {
                        snapshot: owner_snapshot,
                        subject,
                    },
                ..
            } => {
                if owner_snapshot != snapshot {
                    return Err(ReobservationFailure::Unsupported(
                        "共有個体の owner が別 snapshot を参照する".into(),
                    ));
                }
                if roots
                    .as_ref()
                    .is_some_and(|roots| !roots.contains(subject.as_str()))
                {
                    return Err(invalid("共有対の個体が担当 root に所属しない"));
                }
                Ok(Some(subject.as_str()))
            }
            Slot::Missing => {
                missing.push(self::fact(member, field, None));
                Ok(None)
            }
            _ => Err(invalid("共有個体の owner が参照でない")),
        }
    };
    let classify = |failure| match failure {
        ValidationFailure::Stop(signal) => ReobservationFailure::Stopped(signal),
        _ => ReobservationFailure::Unsupported("共有対の同値閉包を確認できない".into()),
    };
    let mut parent = BTreeMap::new();
    let mut members = BTreeMap::new();
    for (left, right) in shared {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        for endpoint in [left, right] {
            if !members.contains_key(endpoint) {
                let root = owner_root(endpoint)?;
                members.insert(endpoint.clone(), root);
            }
        }
        let left_owner = members[left];
        let right_owner = members[right];
        if left == right
            || (left_owner.is_some() && left_owner == right_owner)
            || roster[left.subject.as_str()].ty != roster[right.subject.as_str()].ty
        {
            return Err(invalid("共有対は別担当の同じ型の個体を要求する"));
        }
        parent.entry(left.clone()).or_insert_with(|| left.clone());
        parent.entry(right.clone()).or_insert_with(|| right.clone());
        model_assembly::link_shared(&mut parent, left, right, control).map_err(classify)?;
    }
    let keys = parent.keys().cloned().collect::<Vec<_>>();
    for item in keys {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        model_assembly::representative(&mut parent, &item, control).map_err(classify)?;
    }
    let mut local_images = BTreeSet::new();
    for (member, owner) in &members {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        if let Some(owner) = owner
            && !local_images.insert((owner, &parent[member]))
        {
            return Err(invalid("共有対の閉包が同じ担当の異なる個体を同一視する"));
        }
    }
    for (member, representative) in &parent {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        classes
            .entry(representative)
            .or_default()
            .insert(image(member)?);
    }
    let partition = classes.into_values().collect();
    check_inclusions(parent, layout, roster, check, missing, control)?;
    Ok(partition)
}

fn check_inclusions(
    mut transport: BTreeMap<Fact, Fact>,
    layout: &Layout,
    roster: &BTreeMap<&str, &Subject>,
    check: (&PreparedObserved, &Request),
    missing: &mut Vec<Fact>,
    control: &Control,
) -> Result<(), ReobservationFailure> {
    let (prepared, request) = check;
    let Some(roots) = &layout.roots else {
        return Ok(());
    };
    let target = layout_target(request)?;
    let root = model_assembly::subject(prepared.inputs(), &target)
        .map_err(|_| invalid("組立て先の root がない"))?;
    let head = request
        .declaration()
        .ok_or_else(|| invalid("担当 View 宣言がない"))?;
    let reading = &prepared.inputs().law().declarations()[head].reading;
    transport.insert(target.clone(), target.clone());
    for fragment in roots {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        transport.insert(fragment.clone(), target.clone());
    }
    let mut relevant_types = BTreeSet::new();
    for endpoint in transport.keys() {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        let subject = roster
            .get(endpoint.subject.as_str())
            .ok_or_else(|| invalid("共有端点の主体がない"))?;
        relevant_types.insert(subject.ty.as_str());
    }
    let (collapsed, positions) = crate::construction::check_layout_inclusions(
        prepared.inputs(),
        reading,
        &target,
        root.ty.as_str(),
        roots,
        &transport,
        &relevant_types,
        control,
    )
    .map_err(|failure| match failure {
        crate::construction::ConstructionFailure::Stopped(signal) => {
            ReobservationFailure::Stopped(signal)
        }
        _ => ReobservationFailure::Unsupported("局所構成の参照を確認できない".into()),
    })?;
    if collapsed {
        return Err(invalid("共有対応の推移閉包が局所の異なる個体を同一視する"));
    }
    missing.extend(positions);
    Ok(())
}

fn selected_change(request: &Request) -> Result<&str, ReobservationFailure> {
    request
        .arguments
        .iter()
        .find_map(|argument| {
            if argument.name == "using"
                && let Selector::Declaration { name } = &argument.value
            {
                Some(name.as_str())
            } else {
                None
            }
        })
        .ok_or_else(|| invalid("prepare の change がない"))
}

/// Law改訂時も更新式と、それが読む補助宣言の意味を固定する。
/// 式同値を推論する代わりに、解決済み参照と検査済みソース片を照合する。
fn check_change(
    before: &PreparedObserved,
    current: &PreparedObserved,
    name: &str,
    c: &Control,
) -> Result<(), ReobservationFailure> {
    let old = before.inputs();
    let new = current.inputs();
    if old.sources().law().bytes() == new.sources().law().bytes() {
        return Ok(());
    }
    let mut remaining = vec![name];
    let mut seen = BTreeSet::new();
    while let Some(name) = remaining.pop() {
        c.checkpoint(Checkpoint::ConfigurationMap)?;
        if !seen.insert(name) {
            continue;
        }
        let [Some(a), Some(b)] =
            [old, new].map(|inputs| inputs.law().infos().iter().find(|info| info.name == name))
        else {
            return Err(invalid("change の参照宣言が現在入力にない"));
        };
        if a.kind != b.kind || a.parameters != b.parameters || a.returns != b.returns {
            return Err(invalid("change または参照宣言の型付き署名が対応しない"));
        }
        let tokens = |info: &archsig_input::law::model::DeclarationInfo,
                      inputs: &archsig_input::input::CheckedInputs| {
            let bytes = inputs
                .sources()
                .law()
                .bytes()
                .get(info.span.0..info.span.1)
                .ok_or_else(|| invalid("検査済みの change 宣言位置がない"))?;
            archsig_input::law::lexer::lex_controlled(bytes, c).map_err(|cause| match cause {
                archsig_common::control::CheckFailure::Stopped(signal) => {
                    ReobservationFailure::Stopped(signal)
                }
                archsig_common::control::CheckFailure::Input(_) => {
                    invalid("検査済みの change 宣言を読めない")
                }
            })
        };
        let prior_tokens = tokens(a, old)?;
        let current_tokens = tokens(b, new)?;
        let same_tokens = prior_tokens
            .iter()
            .map(|token| (token.kind, &token.text))
            .eq(current_tokens.iter().map(|token| (token.kind, &token.text)));
        if !same_tokens
            || a.references
                .iter()
                .map(|(_, name)| name)
                .ne(b.references.iter().map(|(_, name)| name))
        {
            return Err(invalid("change の更新式・条件・参照が対応しない"));
        }
        for dependency in &a.dependencies {
            if old
                .law()
                .infos()
                .iter()
                .any(|info| info.name == *dependency)
            {
                remaining.push(dependency);
            }
        }
    }
    Ok(())
}

fn matching_arguments<'a>(
    prior: &'a Request,
    new: &'a Request,
) -> Result<
    impl Iterator<
        Item = (
            &'a super::request::RequestArgument,
            &'a super::request::RequestArgument,
        ),
    >,
    ReobservationFailure,
> {
    if prior.arguments.len() != new.arguments.len() {
        return Err(invalid("明示引数の件数が対応しない"));
    }
    Ok(prior.arguments.iter().zip(&new.arguments))
}

fn repair_requests<'a>(
    before: &'a PreparedObserved,
    current: &'a PreparedObserved,
    previous_candidate: &str,
    current_solve: &str,
    reading: &str,
    control: &Control,
) -> Result<([&'a Request; 2], [&'a Request; 2]), ReobservationFailure> {
    let before_candidate = question(before, previous_candidate, QuestionKind::Candidate)?;
    let Some(prior_solve_id) = answer_field(&before_candidate.head, "solutions") else {
        return Err(invalid("前候補に元 solve がない"));
    };
    let prior_solve = question(before, prior_solve_id, QuestionKind::Solve)?;
    let new_solve = question(current, current_solve, QuestionKind::Solve)?;
    if [prior_solve, new_solve].iter().any(|request| {
        request.arguments.iter().any(|argument| {
            argument.name == "mode"
                && matches!(&argument.value, Selector::Enum { value } if value == "existence")
        })
    }) {
        return Err(ReobservationFailure::Unsupported(
            "前後の solve は全解を要求する".into(),
        ));
    }
    let Some(prior_prepare_id) = answer_field(&prior_solve.head, "problem") else {
        return Err(ReobservationFailure::Unsupported(
            "finite prepare の前回 solve を要求する".into(),
        ));
    };
    let Some(new_prepare_id) = answer_field(&new_solve.head, "problem") else {
        return Err(ReobservationFailure::Unsupported(
            "finite prepare の現在 solve を要求する".into(),
        ));
    };
    let prior_prepare = question(before, prior_prepare_id, QuestionKind::Prepare)?;
    let new_prepare = question(current, new_prepare_id, QuestionKind::Prepare)?;
    let using = selected_change(prior_prepare)?;
    if using != selected_change(new_prepare)? {
        return Err(invalid("前回と現在の change が対応しない"));
    }
    check_change(before, current, using, control)?;
    let law = before.inputs().law();
    let Signature::Change { params, .. } = &law.declarations()[using].signature else {
        return Err(invalid("前回 prepare の using が change でない"));
    };
    for parameter in params.iter().skip(1) {
        let supported =
            super::finite::completion_supported(&parameter.ty, law, control).map_err(|error| {
                match error {
                    ValidationFailure::Stop(signal) => ReobservationFailure::Stopped(signal),
                    _ => {
                        ReobservationFailure::Unsupported("change の有限値域を確認できない".into())
                    }
                }
            })?;
        if !supported {
            return Err(ReobservationFailure::Unsupported(
                "change の parameter は有限値域を要求する".into(),
            ));
        }
    }
    if prior_prepare.head != new_prepare.head
        || !selected_reading(before, prior_prepare, reading)
        || !selected_reading(current, new_prepare, reading)
    {
        return Err(invalid(
            "finite repair の要求 Law または reading が対応しない",
        ));
    }
    Ok(([prior_solve, new_solve], [prior_prepare, new_prepare]))
}

struct SelectedLocal<'a> {
    alignment: AssemblyCandidateAlignment<'a>,
    roots: [(String, String); 2],
    selection: Option<(String, String)>,
    prepare: String,
}

/// 同じ定義・Law を使用し、主体対応を検査してから現在の要求を通常評価する。
/// 過去の組立てや割当てを現在の証拠として移植しない。
pub fn reevaluate_assembly(
    previous: &ObservedEvaluation,
    current: PreparedObserved,
    alignment: &AssemblyAlignment<'_>,
    control: &Control,
) -> Result<ReobservedAssembly, ReobservationFailure> {
    let before = previous.prepared();
    let request = question(before, alignment.assembly, QuestionKind::Assemble)?;
    let mut locals = request
        .arguments
        .iter()
        .filter_map(|argument| argument.name.strip_prefix("local."));
    let candidate = AssemblyCandidateAlignment {
        participant: locals.next().unwrap_or(""),
        previous_candidate: alignment.previous_candidate,
        current_solve: alignment.current_solve,
    };
    if locals.next().is_some() {
        return Err(invalid("各担当の候補対応を指定する"));
    }
    let standalone = (candidate.participant.is_empty()).then_some(candidate);
    let candidates = [candidate];
    if before.inputs().sources().law().bytes() != current.inputs().sources().law().bytes() {
        return Err(ReobservationFailure::Unsupported(
            "一担当 API は同一 Law を要求する".into(),
        ));
    }
    reevaluate_assembly_aligned(
        previous,
        current,
        &MultiAssemblyAlignment {
            before_snapshot: alignment.before_snapshot,
            after_snapshot: alignment.after_snapshot,
            reading: alignment.reading,
            subjects: alignment.subjects,
            assembly: alignment.assembly,
            candidates: if standalone.is_some() {
                &[]
            } else {
                &candidates
            },
        },
        standalone,
        control,
    )
}

/// 担当ごとの現在の候補所属と、現在の組立て結果を返す。
pub fn reevaluate_assembly_many(
    previous: &ObservedEvaluation,
    current: PreparedObserved,
    alignment: &MultiAssemblyAlignment<'_>,
    control: &Control,
) -> Result<ReobservedAssembly, ReobservationFailure> {
    reevaluate_assembly_aligned(previous, current, alignment, None, control)
}

fn reevaluate_assembly_aligned(
    previous: &ObservedEvaluation,
    current: PreparedObserved,
    alignment: &MultiAssemblyAlignment<'_>,
    standalone: Option<AssemblyCandidateAlignment<'_>>,
    control: &Control,
) -> Result<ReobservedAssembly, ReobservationFailure> {
    let before = previous.prepared();
    let old = before.inputs().sources();
    let new = current.inputs().sources();
    if old.definitions().len() != new.definitions().len()
        || !old
            .definitions()
            .iter()
            .zip(new.definitions())
            .all(|(a, b)| a.bytes() == b.bytes())
    {
        return Err(ReobservationFailure::Unsupported(
            "定義が同一の読みを要求する".into(),
        ));
    }
    let before_request = question(before, alignment.assembly, QuestionKind::Assemble)?;
    let after_request = question(&current, alignment.assembly, QuestionKind::Assemble)?;
    if before_request.head != after_request.head
        || !selected_reading(before, before_request, alignment.reading)
        || !selected_reading(&current, after_request, alignment.reading)
    {
        return Err(invalid("組立ての View または reading が対応しない"));
    }
    let snapshot = |prepared: &PreparedObserved, id: &str| {
        prepared
            .inputs()
            .archmap()
            .snapshots()
            .iter()
            .position(|s| s.id == id)
            .ok_or_else(|| invalid("明示された snapshot がない"))
    };
    let a = &before.inputs().archmap().snapshots()[snapshot(before, alignment.before_snapshot)?];
    let current_inputs = current.shared_inputs();
    let b = &current_inputs.archmap().snapshots()[snapshot(&current, alignment.after_snapshot)?];
    let a = subject_index(&a.subjects, control)?;
    let b = subject_index(&b.subjects, control)?;
    let mut pairs = BTreeMap::new();
    let mut used = BTreeSet::new();
    for &(left, right) in alignment.subjects {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        let old = a
            .get(left)
            .copied()
            .ok_or_else(|| invalid("before subject がない"))?;
        let new = b
            .get(right)
            .copied()
            .ok_or_else(|| invalid("after subject がない"))?;
        if old.ty != new.ty || pairs.insert(left, (old, new)).is_some() || !used.insert(right) {
            return Err(invalid("subject 対応は同型の一対一を要求する"));
        }
    }
    let matches_subject = |left: &str, right: &str| {
        pairs
            .get(left)
            .is_some_and(|(_, target)| target.id == right)
    };
    let mut before_missing = Vec::new();
    let mut layout_missing = Vec::new();
    for (old, new) in pairs.values() {
        if let Some((old_field, _)) =
            owner_slot_for(before.inputs(), old, None, control).map_err(owner_failure)?
        {
            control.checkpoint(Checkpoint::ConfigurationMap)?;
            let (new_field, _) = owner_slot_for(current.inputs(), new, None, control)
                .map_err(owner_failure)?
                .filter(|(f, _)| f.name == old_field.name && f.ty == old_field.ty)
                .ok_or_else(|| invalid("owner field の型が対応しない"))?;
            for (slot, snapshot) in [
                (&old_field.slot, alignment.before_snapshot),
                (&new_field.slot, alignment.after_snapshot),
            ] {
                if matches!(slot, Slot::Known { value: Value::Ref { snapshot: owner_snapshot, .. }, .. }
                    if owner_snapshot != snapshot)
                {
                    return Err(ReobservationFailure::Unsupported(
                        "owner が別 snapshot を参照する".into(),
                    ));
                }
            }
            match (&old_field.slot, &new_field.slot) {
                (Slot::Missing, Slot::Missing) => {
                    before_missing.push(fact(old, old_field, None));
                    layout_missing.push(fact(new, new_field, None));
                }
                (Slot::Missing, _) => before_missing.push(fact(old, old_field, None)),
                (_, Slot::Missing) => layout_missing.push(fact(new, new_field, None)),
                (
                    Slot::Known {
                        value:
                            Value::Ref {
                                snapshot: a,
                                subject: x,
                            },
                        ..
                    },
                    Slot::Known {
                        value:
                            Value::Ref {
                                snapshot: b,
                                subject: y,
                            },
                        ..
                    },
                ) if a == alignment.before_snapshot
                    && b == alignment.after_snapshot
                    && matches_subject(x, y) => {}
                _ => return Err(invalid("owner が明示した同一性に沿わない")),
            }
        }
    }
    let same_argument = |a: &Selector, b: &Selector| match (a, b) {
        (
            Selector::Subject {
                snapshot: s,
                subject: x,
            },
            Selector::Subject {
                snapshot: t,
                subject: y,
            },
        ) => {
            if s != alignment.before_snapshot || t != alignment.after_snapshot {
                return Err(ReobservationFailure::Unsupported(
                    "一つの組立て要求に別 snapshot を混在できない".into(),
                ));
            }
            Ok(matches_subject(x, y))
        }
        (Selector::Declaration { .. }, Selector::Declaration { .. }) => Ok(a == b),
        _ => Err(ReobservationFailure::Unsupported(
            "root、共有位置と修復束縛を明示する".into(),
        )),
    };
    let mut candidate_alignments = BTreeMap::new();
    let mut prior_candidates = BTreeSet::new();
    let mut current_solves = BTreeSet::new();
    for candidate in alignment.candidates {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        if candidate_alignments
            .insert(candidate.participant, *candidate)
            .is_some()
            || !prior_candidates.insert(candidate.previous_candidate)
            || !current_solves.insert(candidate.current_solve)
        {
            return Err(invalid("担当・前回候補・現在 solve の対応が重複する"));
        }
    }
    let compare_prepare = |prior: &Request, new: &Request| {
        for (prior, new) in matching_arguments(prior, new)? {
            control.checkpoint(Checkpoint::ConfigurationMap)?;
            if prior.name != new.name || !same_argument(&prior.value, &new.value)? {
                return Err(invalid("担当の修復束縛が対応しない"));
            }
        }
        Ok(())
    };
    let mut selected_locals = Vec::new();
    for (a, b) in matching_arguments(before_request, after_request)? {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        if a.name != b.name {
            return Err(invalid("組立ての明示引数名が対応しない"));
        }
        let Some(participant) = a.name.strip_prefix("local.") else {
            if !same_argument(&a.value, &b.value)? {
                return Err(invalid("root・共有個体・宣言・明示束縛の対応が違う"));
            }
            continue;
        };
        let candidate = candidate_alignments
            .remove(participant)
            .ok_or_else(|| invalid("局所 apply に担当の候補対応がない"))?;
        let ([prior_solve, new_solve], [prior_prepare, new_prepare]) = repair_requests(
            before,
            &current,
            candidate.previous_candidate,
            candidate.current_solve,
            alignment.reading,
            control,
        )?;
        compare_prepare(prior_prepare, new_prepare)?;
        let binding = format!("bind.{participant}");
        let root = |assemble: &Request, prepare: &Request| {
            let selected = assemble
                .arguments
                .iter()
                .find(|a| a.name == binding)
                .map(|a| &a.value);
            let source = prepare
                .arguments
                .iter()
                .find(|a| a.name == "on")
                .map(|a| &a.value);
            let Some(Selector::Subject { snapshot, subject }) = source else {
                return Err(invalid("局所 apply の元rootが明示されていない"));
            };
            if selected != source {
                return Err(invalid("局所 apply の元rootが担当の明示束縛と異なる"));
            }
            Ok((snapshot.clone(), subject.clone()))
        };
        let (_, old_candidate) = repair_selection(before, &a.value, prior_solve)?;
        let (new_apply, new_candidate) = repair_selection(&current, &b.value, new_solve)?;
        if old_candidate.id != candidate.previous_candidate {
            return Err(invalid(
                "前回の局所 apply が照合対象の前回候補を使用していない",
            ));
        }
        selected_locals.push(SelectedLocal {
            alignment: candidate,
            roots: [
                root(before_request, prior_prepare)?,
                root(after_request, new_prepare)?,
            ],
            selection: Some((new_apply.id.clone(), new_candidate.id.clone())),
            prepare: new_prepare.id.clone(),
        });
    }
    if let Some(candidate) = standalone {
        let (_, [prior_prepare, new_prepare]) = repair_requests(
            before,
            &current,
            candidate.previous_candidate,
            candidate.current_solve,
            alignment.reading,
            control,
        )?;
        compare_prepare(prior_prepare, new_prepare)?;
        selected_locals.push(SelectedLocal {
            alignment: candidate,
            roots: [("".into(), "".into()), ("".into(), "".into())],
            selection: None,
            prepare: new_prepare.id.clone(),
        });
    }
    if !candidate_alignments.is_empty() || selected_locals.is_empty() {
        return Err(invalid("担当の候補対応と局所 apply が一致しない"));
    }

    let before_answer = previous
        .answers
        .iter()
        .find(|a| a.id == alignment.assembly)
        .ok_or_else(|| invalid("before の組立て回答がない"))?;
    let mut observations = Vec::new();
    let mut external_missing = Vec::new();
    let mut seen = BTreeSet::new();
    let mut record_needed = |needed: &Fact| -> Result<(), ReobservationFailure> {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        if !seen.insert(needed.clone()) {
            return Ok(());
        }
        if needed.snapshot != alignment.before_snapshot {
            external_missing.push(needed.clone());
            return Ok(());
        }
        let Some((old, new)) = pairs.get(needed.subject.as_str()) else {
            if is_owner_fact(before.inputs(), needed) {
                return Ok(());
            }
            return Err(invalid("組立ての不足位置に subject 対応がない"));
        };
        let name = needed
            .field
            .as_ref()
            .ok_or_else(|| invalid("不足位置に field がない"))?;
        let old_field = old
            .fields
            .iter()
            .find(|f| &f.name == name && matches!(f.slot, Slot::Missing))
            .ok_or_else(|| invalid("before の不足位置が原始 slot と一致しない"))?;
        let field = new
            .fields
            .iter()
            .find(|f| &f.name == name && f.ty == old_field.ty)
            .ok_or_else(|| invalid("after の field と型が一致しない"))?;
        let observed = match &field.slot {
            Slot::Missing => None,
            Slot::Known { atom, .. } => Some(fact(new, field, Some(atom.clone()))),
        };
        observations.push(ObservationMatch {
            needed: needed.clone(),
            observed,
        });
        Ok(())
    };
    for needed in before_answer
        .reasons
        .iter()
        .filter(|r| r.kind == ReasonKind::Missing)
        .flat_map(|reason| &reason.missing)
    {
        if is_owner_fact(before.inputs(), needed) {
            before_missing.push(needed.clone());
        }
        record_needed(needed)?;
    }
    let translate = |value: &Scalar| match value {
        Scalar::Subject {
            snapshot,
            subject,
            entity,
        } if snapshot == alignment.before_snapshot => {
            pairs
                .get(subject.as_str())
                .map(|(_, target)| Scalar::Subject {
                    snapshot: target.snapshot.clone(),
                    subject: target.id.clone(),
                    entity: entity.clone(),
                })
        }
        _ => None,
    };
    let evaluation = reevaluate_observed(previous, current, control)
        .map_err(|failure| ReobservationFailure::Evaluation(Box::new(failure)))?;
    if let Some(current_answer) = evaluation
        .answers
        .iter()
        .find(|a| a.id == alignment.assembly)
    {
        layout_missing.extend(
            current_answer
                .reasons
                .iter()
                .filter(|reason| reason.kind == ReasonKind::Missing)
                .flat_map(|reason| &reason.missing)
                .filter(|fact| is_owner_fact(evaluation.prepared().inputs(), fact))
                .cloned(),
        );
    }
    let mut continuity_stop = control.stop_reason();
    if continuity_stop.is_none() {
        let mut compare_layout = || -> Result<(), ReobservationFailure> {
            let before_layout = checked_layout(previous, before_request, control)?;
            let after_request_for_layout = question(
                evaluation.prepared(),
                alignment.assembly,
                QuestionKind::Assemble,
            )?;
            let after_layout = checked_layout(&evaluation, after_request_for_layout, control)?;
            for local in selected_locals
                .iter()
                .filter(|local| local.selection.is_some())
            {
                for (layout, (snapshot, subject)) in [&before_layout, &after_layout]
                    .into_iter()
                    .zip(&local.roots)
                {
                    if layout.roots.as_ref().is_some_and(|roots| {
                        !roots
                            .iter()
                            .any(|root| root.snapshot == *snapshot && root.subject == *subject)
                    }) {
                        return Err(invalid("局所 apply の元rootが評価済みの担当集合にない"));
                    }
                }
            }
            before_missing.extend(before_layout.missing.iter().cloned());
            layout_missing.extend(after_layout.missing.iter().cloned());
            let after_subject = |fact: &Fact| {
                control.checkpoint(Checkpoint::ConfigurationMap)?;
                if fact.snapshot != alignment.after_snapshot {
                    return Err(ReobservationFailure::Unsupported(
                        "組立て View が別 snapshot の参照を返した".into(),
                    ));
                }
                Ok(fact.clone())
            };
            let before_image = |fact: &Fact| {
                control.checkpoint(Checkpoint::ConfigurationMap)?;
                if fact.snapshot != alignment.before_snapshot {
                    return Err(ReobservationFailure::Unsupported(
                        "組立て View が別 snapshot の参照を返した".into(),
                    ));
                }
                pairs
                    .get(fact.subject.as_str())
                    .map(|(_, new)| {
                        Fact::from(FactData {
                            snapshot: new.snapshot.clone(),
                            subject: new.id.clone(),
                            field: None,
                            atom: None,
                        })
                    })
                    .ok_or_else(|| invalid("組立て View の参照先に明示対応がない"))
            };
            let old_roots = before_layout
                .roots
                .as_ref()
                .map(|roots| {
                    roots
                        .iter()
                        .map(before_image)
                        .collect::<Result<BTreeSet<_>, _>>()
                })
                .transpose()?;
            let new_roots = after_layout
                .roots
                .as_ref()
                .map(|roots| {
                    roots
                        .iter()
                        .map(after_subject)
                        .collect::<Result<BTreeSet<_>, _>>()
                })
                .transpose()?;
            if let (Some(old), Some(new)) = (&old_roots, &new_roots)
                && old != new
            {
                return Err(invalid("評価済みの担当集合が明示対応と異なる"));
            }
            let old_shared = if before_layout.shared.is_some() {
                Some(checked_shared_partition(
                    &before_layout,
                    &a,
                    alignment.before_snapshot,
                    before_image,
                    (before, before_request),
                    &mut before_missing,
                    control,
                )?)
            } else {
                check_inclusions(
                    BTreeMap::new(),
                    &before_layout,
                    &a,
                    (before, before_request),
                    &mut before_missing,
                    control,
                )?;
                None
            };
            let new_shared = if after_layout.shared.is_some() {
                Some(checked_shared_partition(
                    &after_layout,
                    &b,
                    alignment.after_snapshot,
                    after_subject,
                    (evaluation.prepared(), after_request_for_layout),
                    &mut layout_missing,
                    control,
                )?)
            } else {
                check_inclusions(
                    BTreeMap::new(),
                    &after_layout,
                    &b,
                    (evaluation.prepared(), after_request_for_layout),
                    &mut layout_missing,
                    control,
                )?;
                None
            };
            for needed in &before_missing {
                record_needed(needed)?;
            }
            if let (Some(old), Some(new)) = (old_shared, new_shared)
                && old != new
            {
                return Err(invalid("評価済みの共有対が明示対応と異なる"));
            }
            Ok(())
        };
        if let Err(error) = compare_layout() {
            match error {
                ReobservationFailure::Stopped(signal) => continuity_stop = Some(signal),
                other => return Err(other),
            }
        }
    }
    layout_missing.extend(before_missing);
    layout_missing.extend(external_missing);
    layout_missing.sort();
    layout_missing.dedup();
    let mut candidates = Vec::new();
    let mut membership_environment = None;
    for local in selected_locals {
        let previous_candidate = local.alignment.previous_candidate;
        let current_solve = local.alignment.current_solve;
        let mut missing = evaluation
            .answers
            .iter()
            .filter(|answer| {
                answer.id == current_solve
                    || answer.id == local.prepare
                    || local
                        .selection
                        .as_ref()
                        .is_some_and(|(apply, _)| answer.id == *apply)
            })
            .flat_map(|answer| &answer.reasons)
            .filter(|reason| reason.kind == ReasonKind::Missing)
            .flat_map(|reason| reason.missing.iter().cloned())
            .collect::<Vec<_>>();
        missing.sort();
        missing.dedup();
        let solutions = evaluation
            .answers
            .iter()
            .find(|answer| answer.id == current_solve)
            .and_then(|answer| answer.outputs.get("solutions"))
            .copied();
        let mut current_assignment = None;
        let mut continuity = CandidateContinuity::Undetermined;
        let mut undecided = Some(if continuity_stop.is_some() {
            ContinuityPending::Interrupted
        } else if !layout_missing.is_empty() {
            ContinuityPending::LayoutMissing
        } else if solutions.is_none() {
            ContinuityPending::CurrentSolveUnavailable
        } else {
            ContinuityPending::PreviousAssignmentUnavailable
        });
        if let (Some(old), Some(solutions)) = (
            output(previous, previous_candidate, "assignment"),
            solutions,
        ) && continuity_stop.is_none()
            && layout_missing.is_empty()
        {
            use super::repair_problem::ReobservedMembership as Membership;
            let membership = (|| {
                if membership_environment.is_none() {
                    membership_environment =
                        Some(Environment::with_prepared(evaluation.prepared(), control)?);
                }
                let environment = membership_environment
                    .as_ref()
                    .ok_or(internal!("候補照合の現在環境がない"))?;
                super::repair_problem::reobserved_membership(
                    old,
                    &evaluation.nodes[solutions.0],
                    translate,
                    environment,
                    control,
                )
            })();
            match membership {
                Ok(Membership::Retained(entries)) => {
                    continuity = CandidateContinuity::Retained;
                    current_assignment = Some(CurrentAssignment { entries });
                    undecided = None;
                }
                Ok(Membership::Excluded) => {
                    continuity = CandidateContinuity::Excluded;
                    undecided = None;
                }
                Ok(Membership::Missing(facts)) => {
                    missing.extend(facts);
                    missing.sort();
                    missing.dedup();
                    undecided = Some(ContinuityPending::Missing);
                }
                Ok(Membership::Incompatible) => {
                    undecided = Some(ContinuityPending::IncompatibleDomain);
                }
                Err(ValidationFailure::Stop(signal)) => {
                    continuity_stop = Some(signal);
                    undecided = Some(ContinuityPending::Interrupted);
                }
                Err(_) => {
                    return Err(ReobservationFailure::Unsupported(
                        "有限割当ての対応を照合できない".into(),
                    ));
                }
            }
        }
        candidates.push(ReobservedCandidate {
            participant: local.alignment.participant.into(),
            previous_candidate: previous_candidate.into(),
            current_solve: current_solve.into(),
            continuity,
            undecided,
            current_assignment,
            missing,
            selected_candidate: local.selection.and_then(|(apply, candidate)| {
                output(&evaluation, &apply, "object")
                    .is_some()
                    .then_some(candidate)
            }),
        });
    }
    let assembly_status = evaluation
        .answers
        .iter()
        .find(|answer| answer.id == alignment.assembly)
        .map(|answer| answer.status);
    Ok(ReobservedAssembly {
        evaluation,
        observations,
        layout_missing,
        candidates,
        assembly_status,
        continuity_stop,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::{evaluate_observed, prepare_observed, result::Decision};
    use archsig_input::input::InputSources;

    const DEFINITIONS: &[u8] =
        include_bytes!("../../../../tests/fixtures/r2-assembly-reobservation/definitions.json");
    const LAW: &[u8] =
        include_bytes!("../../../../tests/fixtures/r2-assembly-reobservation/laws.law");
    const BEFORE: &str =
        include_str!("../../../../tests/fixtures/r2-assembly-reobservation/before.json");
    const AFTER: &str =
        include_str!("../../../../tests/fixtures/r2-assembly-reobservation/after.json");
    const QUERIES: &str =
        include_str!("../../../../tests/fixtures/r2-assembly-reobservation/queries.txt");

    fn prepared(snapshot: &str, map: &str, c: &Control) -> PreparedObserved {
        prepared_with(snapshot, map, LAW, QUERIES, c)
    }

    fn prepared_with(
        snapshot: &str,
        map: &str,
        law: &[u8],
        queries: &str,
        c: &Control,
    ) -> PreparedObserved {
        let asks = queries.replace("SNAP", snapshot);
        let asks = asks.lines().collect::<Vec<_>>();
        prepare_observed(
            InputSources::from_bytes(
                vec![DEFINITIONS.to_vec()],
                law.to_vec(),
                map.as_bytes().to_vec(),
            ),
            &asks,
            c,
        )
        .unwrap()
    }

    fn status(result: &ObservedEvaluation, id: &str) -> Decision {
        result.answers.iter().find(|a| a.id == id).unwrap().status
    }

    fn quantity(map: &str, subject: &str, old: u32, new: u32) -> String {
        let prefix = format!(
            "\"id\": \"{subject}-quantity\",\n          \"subject\": \"{subject}\",\n          \"field\": \"Assemble.Part.quantity\",\n          \"value\": "
        );
        let updated = map.replacen(
            &format!("{prefix}\"{old}\""),
            &format!("{prefix}\"{new}\""),
            1,
        );
        assert_ne!(updated, map);
        updated
    }

    #[test]
    fn multiple_candidates_follow_current_inputs_and_revised_law() {
        let c = Control::unlimited();
        let queries = r#"aWithin=evaluate(Assembly.singleton,p=@SNAP/ma)
bWithin=evaluate(Assembly.singleton,p=@SNAP/mb)
aProblem=prepare(Assembly.boundary,using=Assembly.choose,on=@SNAP/A,p=@SNAP/ma)
bProblem=prepare(Assembly.flexible,using=Assembly.choose,on=@SNAP/B,p=@SNAP/mb,b=@SNAP/b)
aSolve=solve($aProblem.problem,within=$aWithin.value)
bSolve=solve($bProblem.problem,within=$bWithin.value)
aPick=candidate($aSolve.solutions,index=0)
bPick=candidate($bSolve.solutions,index=0)
aApply=apply($aPick.assignment,in=$aSolve.solutions)
bApply=apply($bPick.assignment,in=$bSolve.solutions)
joined=assemble(Assembly.fragments,on=@SNAP/G,along=Assembly.interfaces,a=@SNAP/A,b=@SNAP/B,ma=@SNAP/ma,mb=@SNAP/mb,local.a=$aApply.object,local.b=$bApply.object)"#;
        let law = std::str::from_utf8(LAW).unwrap().replace(
            "law optional boundary(p:Part)", "law optional flexible(p:Part,b:Part):p.quantity+b.quantity=p.quantity+b.quantity; law optional boundary(p:Part)",
        );
        let strong = law.replace(
            "p.quantity+b.quantity=p.quantity+b.quantity",
            "p.quantity=1",
        );
        let previous_map = AFTER.replace("\"after\"", "\"before\"");
        let before = |law: &str| {
            evaluate_observed(
                prepared_with("before", &previous_map, law.as_bytes(), queries, &c),
                &c,
            )
            .unwrap()
        };
        let pairs = [
            ("A", "A"),
            ("B", "B"),
            ("G", "G"),
            ("a", "a"),
            ("b", "b"),
            ("ma", "ma"),
            ("mb", "mb"),
        ];
        let candidates = [
            AssemblyCandidateAlignment {
                participant: "a",
                previous_candidate: "aPick",
                current_solve: "aSolve",
            },
            AssemblyCandidateAlignment {
                participant: "b",
                previous_candidate: "bPick",
                current_solve: "bSolve",
            },
        ];
        let alignment = MultiAssemblyAlignment {
            before_snapshot: "before",
            after_snapshot: "after",
            reading: "Assembly",
            subjects: &pairs,
            assembly: "joined",
            candidates: &candidates,
        };
        let different_choice = queries.replace(
            "bPick=candidate($bSolve.solutions,index=0)",
            "bPick=candidate($bSolve.solutions,index=1)",
        );
        let corrected = quantity(AFTER, "b", 0, 1);
        let unrelated = law.replace(
            "law optional boundary(p:Part)",
            "law optional unrelated():true; law optional boundary(p:Part)",
        );
        let reformatted = unrelated.replace("quantity=if q", "quantity = if q");
        for (old, new, map, asks, expected, assembly) in [
            (
                &law,
                &law,
                AFTER,
                queries,
                CandidateContinuity::Retained,
                "established",
            ),
            (
                &law,
                &law,
                AFTER,
                different_choice.as_str(),
                CandidateContinuity::Retained,
                "refuted",
            ),
            (
                &law,
                &law,
                corrected.as_str(),
                queries,
                CandidateContinuity::Excluded,
                "established",
            ),
            (
                &law,
                &strong,
                AFTER,
                queries,
                CandidateContinuity::Excluded,
                "refuted",
            ),
            (
                &strong,
                &law,
                AFTER,
                different_choice.as_str(),
                CandidateContinuity::Retained,
                "refuted",
            ),
            (
                &law,
                &unrelated,
                AFTER,
                queries,
                CandidateContinuity::Retained,
                "established",
            ),
            (
                &law,
                &reformatted,
                AFTER,
                queries,
                CandidateContinuity::Retained,
                "established",
            ),
        ] {
            let previous = before(old);
            let prepare = || prepared_with("after", map, new.as_bytes(), asks, &c);
            let cold = evaluate_observed(prepare(), &c).unwrap();
            let result = reevaluate_assembly_many(&previous, prepare(), &alignment, &c).unwrap();
            assert_eq!(result.evaluation().result_wire(), cold.result_wire());
            assert_eq!(
                result.assembly_status(),
                Some(assembly),
                "{:?}",
                result
                    .evaluation()
                    .answers
                    .iter()
                    .map(|a| (&a.id, a.status, &a.reasons))
                    .collect::<Vec<_>>()
            );
            let [a, b] = result.candidates() else {
                panic!("two candidate rows")
            };
            assert_eq!(a.continuity(), CandidateContinuity::Retained);
            assert_eq!(b.continuity(), expected);
            assert!(a.current_assignment().is_some());
            if let Some(assignment) = b.current_assignment() {
                let (_, values) = assignment.entries.iter().find(|(subject, _)| matches!(subject, Scalar::Subject { subject, .. } if subject == "mb")).unwrap();
                assert_eq!(values, &[Scalar::Bool(old == &strong)]);
            } else {
                assert_eq!(expected, CandidateContinuity::Excluded);
            }
        }
        // The same original assignments still satisfy both current solves,
        // but the newly observed baseline changes one selected shared value.
        let preserving = law.replace(
            "quantity=if q then 1 else 0",
            "quantity=if q then 1 else p.quantity",
        );
        let changed_shared = quantity(
            &AFTER.replace("observed-shared-quantity", "mb-quantity"),
            "mb",
            0,
            1,
        );
        let transported = reevaluate_assembly_many(
            &before(&preserving),
            prepared_with("after", &changed_shared, preserving.as_bytes(), queries, &c),
            &alignment,
            &c,
        )
        .unwrap();
        assert_eq!(transported.assembly_status(), Some("refuted"));
        assert!(
            transported
                .candidates()
                .iter()
                .all(|candidate| candidate.continuity() == CandidateContinuity::Retained)
        );
        for local in transported.candidates() {
            let subject = if local.participant() == "a" {
                "ma"
            } else {
                "mb"
            };
            let (_, values) = local.current_assignment().unwrap().entries.iter().find(|(root, _)| matches!(root, Scalar::Subject { subject: name, .. } if name == subject)).unwrap();
            assert_eq!(values, &[Scalar::Bool(false)]);
        }
        let prior = before(&law);
        for candidates in [
            &candidates[..1],
            &[candidates[0], candidates[0]],
            &[
                candidates[0],
                AssemblyCandidateAlignment {
                    current_solve: "aSolve",
                    ..candidates[1]
                },
            ],
        ] {
            assert!(matches!(
                reevaluate_assembly_many(
                    &prior,
                    prepared_with("after", AFTER, law.as_bytes(), queries, &c),
                    &MultiAssemblyAlignment {
                        candidates,
                        ..alignment
                    },
                    &c
                ),
                Err(ReobservationFailure::InvalidCorrespondence(_))
            ));
        }
        let changed = law.replace("quantity=if q then 1 else 0", "quantity=if q then 0 else 1");
        assert!(
            matches!(reevaluate_assembly_many(&prior, prepared_with("after", AFTER, changed.as_bytes(), queries, &c), &alignment, &c), Err(ReobservationFailure::InvalidCorrespondence(message)) if message.contains("更新式"))
        );
    }

    #[test]
    fn saved_reobservation_matches_the_expected_evidence() {
        use archsig_common::{canonical::Json, json::parse};
        let c = Control::unlimited();
        let pairs = [
            ("A", "A"),
            ("B", "B"),
            ("G", "G"),
            ("a", "a"),
            ("b", "b"),
            ("ma", "ma"),
            ("mb", "mb"),
        ];
        let alignment = AssemblyAlignment {
            before_snapshot: "before",
            after_snapshot: "after",
            reading: "Assembly",
            subjects: &pairs,
            assembly: "joined",
            previous_candidate: "pick",
            current_solve: "solveIt",
        };
        let before = evaluate_observed(prepared("before", BEFORE, &c), &c).unwrap();
        let visits = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let recorded = visits.clone();
        let trace = Control::new(move |point| {
            recorded.borrow_mut().push(point);
            None
        });
        let after =
            reevaluate_assembly(&before, prepared("after", AFTER, &c), &alignment, &trace).unwrap();
        let visits = visits.borrow();
        let last_result = visits
            .iter()
            .rposition(|point| *point == Checkpoint::NativeResultNode)
            .unwrap();
        let stop_at = visits
            .iter()
            .enumerate()
            .skip(last_result + 1)
            .find_map(|(i, point)| (*point == Checkpoint::ConfigurationMap).then_some(i))
            .unwrap();
        let mut visit = 0;
        let stop = Control::new(move |_| {
            let signal = (visit == stop_at).then_some(Signal::Int);
            visit += 1;
            signal
        });
        let stopped =
            reevaluate_assembly(&before, prepared("after", AFTER, &c), &alignment, &stop).unwrap();
        assert_eq!(stopped.continuity_stop(), Some(Signal::Int));
        assert_eq!(stopped.candidate(), CandidateContinuity::Undetermined);
        assert_eq!(stopped.selected_candidate(), Some("pick"));
        assert_eq!(
            stopped.evaluation().result_wire().canonical(),
            after.evaluation().result_wire().canonical()
        );
        let asks = QUERIES
            .replace("pick=", "replacement=")
            .replace("$pick.assignment", "$replacement.assignment");
        let corrected_map = quantity(&quantity(AFTER, "a", 1, 2), "b", 0, 1);
        let corrected = reevaluate_assembly(
            &before,
            prepared_with("after", &corrected_map, LAW, &asks, &c),
            &alignment,
            &c,
        )
        .unwrap();
        let [observation] = after.observations() else {
            panic!("one observed shared slot")
        };
        let slot = |fact: &Fact| {
            let mut members = vec![
                Json::str(fact.snapshot.as_str()),
                Json::str(fact.subject.as_str()),
                Json::str(fact.field.as_ref().unwrap().as_str()),
            ];
            members.extend(fact.atom.as_ref().map(|atom| Json::str(atom.as_str())));
            Json::Arr(members)
        };
        assert_eq!(after.candidate(), CandidateContinuity::Retained);
        assert_eq!(corrected.candidate(), CandidateContinuity::Excluded);
        let corrected_result = corrected.evaluation();
        assert_eq!(status(corrected_result, "selected"), Decision::Established);
        let mut swapped = pairs;
        swapped[5].1 = "mb";
        swapped[6].1 = "ma";
        let swapped = AssemblyAlignment {
            subjects: &swapped,
            ..alignment
        };
        assert!(matches!(
            reevaluate_assembly(&before, prepared("after", AFTER, &c), &swapped, &c,),
            Err(ReobservationFailure::InvalidCorrespondence(_))
        ));
        let actual = Json::obj([
            (
                "before",
                Json::obj([
                    ("assembly", Json::str(status(&before, "joined").wire())),
                    ("global", Json::str(status(&before, "global").wire())),
                    ("missing", slot(observation.needed())),
                ]),
            ),
            (
                "after",
                Json::obj([
                    (
                        "assembly",
                        Json::str(status(after.evaluation(), "joined").wire()),
                    ),
                    (
                        "global",
                        Json::str(status(after.evaluation(), "global").wire()),
                    ),
                    ("observed", slot(observation.observed().unwrap())),
                    ("previous_assignment", Json::str("retained")),
                    (
                        "selected_candidate",
                        Json::str(after.selected_candidate().unwrap()),
                    ),
                ]),
            ),
            (
                "after_with_corrected_private_quantities",
                Json::obj([
                    (
                        "assembly",
                        Json::str(status(corrected_result, "joined").wire()),
                    ),
                    (
                        "global",
                        Json::str(status(corrected_result, "global").wire()),
                    ),
                    ("previous_assignment", Json::str("excluded")),
                    (
                        "selected_candidate",
                        Json::str(corrected.selected_candidate().unwrap()),
                    ),
                    (
                        "current_candidate_and_apply",
                        Json::str(status(corrected_result, "replacement").wire()),
                    ),
                ]),
            ),
            (
                "swapped_owner_correspondence",
                Json::str("invalid_correspondence"),
            ),
        ]);
        let expected =
            include_bytes!("../../../../tests/fixtures/r2-assembly-reobservation/expected.json");
        assert_eq!(
            parse(actual.canonical().as_bytes()).unwrap(),
            parse(expected).unwrap()
        );
    }

    #[test]
    fn explicit_reobservation_matches_a_shared_slot_and_rechecks_an_actual_assignment() {
        let c = Control::unlimited();
        let before_map = quantity(BEFORE, "b", 0, 1);
        let before = evaluate_observed(prepared("before", &before_map, &c), &c).unwrap();
        assert_eq!(status(&before, "pick"), Decision::Established);
        assert_eq!(status(&before, "joined"), Decision::Undetermined);
        assert_eq!(status(&before, "global"), Decision::Undetermined);
        let pairs = [
            ("A", "A"),
            ("B", "B"),
            ("G", "G"),
            ("a", "a"),
            ("b", "b"),
            ("ma", "ma"),
            ("mb", "mb"),
        ];
        let alignment = AssemblyAlignment {
            before_snapshot: "before",
            after_snapshot: "after",
            reading: "Assembly",
            subjects: &pairs,
            assembly: "joined",
            previous_candidate: "pick",
            current_solve: "solveIt",
        };
        let before_input = before.prepared();
        let before_request = question(before_input, "joined", QuestionKind::Assemble).unwrap();
        let layout = checked_layout(&before, before_request, &c).unwrap();
        let Some(SharedLayout::Reads(shared)) = &layout.shared else {
            panic!("prior shared view");
        };
        let (left, right) = &shared[0];
        let old_snapshot = before_input
            .inputs()
            .archmap()
            .snapshots()
            .iter()
            .find(|snapshot| snapshot.id == "before")
            .unwrap();
        let roster = subject_index(&old_snapshot.subjects, &c).unwrap();
        let mut private = left.clone();
        private.subject = "a".into();
        for (edge, detail) in [
            ((left.clone(), left.clone()), "別担当"),
            ((private, right.clone()), "閉包"),
        ] {
            let invalid_layout = Layout {
                roots: layout.roots.clone(),
                shared: Some(SharedLayout::Reads(vec![
                    (left.clone(), right.clone()),
                    edge,
                ])),
                missing: vec![],
            };
            assert!(matches!(
                checked_shared_partition(&invalid_layout, &roster, "before", |fact| Ok(fact.clone()), (before_input, before_request), &mut Vec::new(), &c),
                Err(ReobservationFailure::InvalidCorrespondence(message)) if message.contains(detail)
            ));
        }

        let new_queries = QUERIES
            .replace("pick=", "replacement=")
            .replace("$pick.assignment", "$replacement.assignment")
            .replace("ma=@SNAP/ma,mb=@SNAP/mb", "mb=@SNAP/mb,ma=@SNAP/ma");
        let revised = quantity(AFTER, "b", 0, 1);
        let mut renamed = revised.clone();
        let mut renamed_queries = new_queries.clone();
        let mut renamed_pairs = pairs;
        for (old, new) in [("a", "zeta"), ("ma", "sharedA"), ("mb", "sharedB")] {
            renamed = renamed.replace(&format!("\"{old}\""), &format!("\"{new}\""));
            renamed_queries =
                renamed_queries.replace(&format!("@SNAP/{old}"), &format!("@SNAP/{new}"));
            renamed_pairs
                .iter_mut()
                .find(|pair| pair.0 == old)
                .unwrap()
                .1 = new;
        }
        let renamed_alignment = AssemblyAlignment {
            subjects: &renamed_pairs,
            ..alignment
        };
        let current = || prepared_with("after", &renamed, LAW, &renamed_queries, &c);
        let next = reevaluate_assembly(&before, current(), &renamed_alignment, &c).unwrap();
        assert_eq!(next.candidate(), CandidateContinuity::Retained);
        assert_eq!(next.selected_candidate(), Some("replacement"));
        let [matched] = next.observations.as_slice() else {
            panic!("one shared observation")
        };
        assert_eq!(matched.needed.snapshot, "before");
        assert_eq!(matched.needed.subject, "mb");
        assert!(matched.needed.atom.is_none());
        let observed = matched.observed.as_ref().unwrap();
        assert_eq!(observed.snapshot, "after");
        assert_eq!(observed.subject, "sharedB");
        assert_eq!(observed.field, matched.needed.field);
        assert_eq!(observed.atom.as_deref(), Some("observed-shared-quantity"));
        assert_eq!(status(&next.evaluation, "joined"), Decision::Established);
        assert_eq!(status(&next.evaluation, "global"), Decision::Established);

        let corrected = quantity(AFTER, "a", 1, 2);
        let next = reevaluate_assembly(
            &before,
            prepared_with("after", &corrected, LAW, &new_queries, &c),
            &alignment,
            &c,
        )
        .unwrap();
        assert_eq!(next.candidate(), CandidateContinuity::Excluded);
        assert_eq!(next.selected_candidate(), Some("replacement"));
        assert_eq!(
            status(&next.evaluation, "replacement"),
            Decision::Established
        );
        assert_eq!(status(&next.evaluation, "selected"), Decision::Established);
        assert_eq!(status(&next.evaluation, "joined"), Decision::Established);
        assert_eq!(status(&next.evaluation, "global"), Decision::Established);

        let unknown = AFTER.replace(
            r#""subjects": ["#,
            r#""subjects": [{"id":"unknown","type":"Assemble.Step","origin":"model"},"#,
        ).replace(
            r#""atoms": ["#,
            r#""atoms": [
                {"id":"unknown-from","subject":"unknown","field":"Assemble.Step.from","value":["after","mb"],"origin":"model"},
                {"id":"unknown-to","subject":"unknown","field":"Assemble.Step.to","value":["after","mb"],"origin":"model"},"#,
        );
        let unavailable = QUERIES.replace("index=0", "index=100");
        let pending = reevaluate_assembly(
            &before,
            prepared_with("after", &unknown, LAW, &unavailable, &c),
            &alignment,
            &c,
        )
        .unwrap();
        assert_eq!(
            status(pending.evaluation(), "solveIt"),
            Decision::Established
        );
        assert_eq!(pending.candidate(), CandidateContinuity::Undetermined);
        assert!(pending.layout_missing().iter().any(|slot| {
            slot.subject == "unknown" && slot.field.as_ref().is_some_and(|name| name.is_owner())
        }));

        let mut wrong = pairs;
        wrong[5].1 = "mb";
        wrong[6].1 = "ma";
        let wrong_alignment = AssemblyAlignment {
            subjects: &wrong,
            ..alignment
        };
        assert!(matches!(
            reevaluate_assembly(&before, prepared("after", AFTER, &c), &wrong_alignment, &c),
            Err(ReobservationFailure::InvalidCorrespondence(message)) if message.contains("owner")
        ));

        let wrong_queries = QUERIES
            .replace("selected=apply", "other=apply")
            .replace("local.a=$selected.object", "local.a=$other.object");
        let wrong_queries = wrong_queries
            .replace("other=apply($pick.assignment,in=$solveIt.solutions)",
                "unrelated=solve($prepareIt.problem,within=$within.value)\nother=apply($pick.assignment,in=$unrelated.solutions)");
        assert!(matches!(
            reevaluate_assembly(&before, prepared_with("after", AFTER, LAW, &wrong_queries, &c), &alignment, &c),
            Err(ReobservationFailure::InvalidCorrespondence(message)) if message.contains("solve")
        ));

        let incomplete = BEFORE.replace("\"before\"", "\"after\"");
        let next = reevaluate_assembly(&before, prepared("after", &incomplete, &c), &alignment, &c)
            .unwrap();
        assert_eq!(next.observations().len(), 1);
        assert!(next.observations()[0].observed().is_none());
        assert!(next.selected_candidate().is_none());
        assert_eq!(status(next.evaluation(), "joined"), Decision::Undetermined);

        let pending_law = std::str::from_utf8(LAW).unwrap().replace(
            "list<(Part,Part)>[(ma,mb)];",
            "if mb.quantity=0 then list<(Part,Part)>[(ma,mb)] else list<(Part,Part)>[(mb,ma)];",
        );
        let missing_private = BEFORE.replace(
            concat!(
                "        {\n          \"id\": \"b-quantity\",\n          \"subject\": \"b\",\n",
                "          \"field\": \"Assemble.Part.quantity\",\n          \"value\": \"0\",\n",
                "          \"origin\": \"model\"\n        },\n"
            ),
            "",
        );
        let pending = evaluate_observed(
            prepared_with(
                "before",
                &missing_private,
                pending_law.as_bytes(),
                QUERIES,
                &c,
            ),
            &c,
        )
        .unwrap();
        let completed = reevaluate_assembly(
            &pending,
            prepared_with("after", AFTER, pending_law.as_bytes(), QUERIES, &c),
            &alignment,
            &c,
        )
        .unwrap();
        assert!(completed.layout_missing().iter().any(|slot| {
            slot.snapshot == "before"
                && slot.subject == "mb"
                && slot
                    .field
                    .as_ref()
                    .is_some_and(|name| name == "Assemble.Part.quantity")
        }));
        assert_eq!(status(&pending, "selected"), Decision::Undetermined);
        assert!(completed.observations().iter().any(|matched| {
            matched.needed().subject == "b"
                && matched
                    .observed()
                    .is_some_and(|atom| atom.atom.as_deref() == Some("b-quantity"))
        }));
        assert_eq!(completed.candidate(), CandidateContinuity::Undetermined);
        assert_eq!(completed.selected_candidate(), Some("pick"));
        assert!(completed.observations().iter().any(|matched| {
            matched.needed().subject == "mb"
                && matched
                    .observed()
                    .is_some_and(|atom| atom.atom.as_deref() == Some("observed-shared-quantity"))
        }));
        assert_eq!(
            status(completed.evaluation(), "global"),
            Decision::Established
        );

        let root_law = std::str::from_utf8(LAW)
            .unwrap()
            .replace(
                "set<Root>{a,b}",
                "if ma.quantity=0 then set<Root>{a,b} else set<Root>{a}",
            )
            .replace("list<(Part,Part)>[(ma,mb)]", "list<(Part,Part)>[]");
        let previous = evaluate_observed(
            prepared_with("before", BEFORE, root_law.as_bytes(), QUERIES, &c),
            &c,
        )
        .unwrap();
        let changed_root = AFTER.replacen(
            concat!(
                "\"id\": \"ma-quantity\",\n          \"subject\": \"ma\",\n",
                "          \"field\": \"Assemble.Part.quantity\",\n          \"value\": \"0\"",
            ),
            concat!(
                "\"id\": \"ma-quantity\",\n          \"subject\": \"ma\",\n",
                "          \"field\": \"Assemble.Part.quantity\",\n          \"value\": \"1\"",
            ),
            1,
        );
        assert_ne!(changed_root, AFTER);
        assert!(matches!(reevaluate_assembly(
            &previous,
            prepared_with("after", &changed_root, root_law.as_bytes(), QUERIES, &c),
            &alignment, &c,
        ), Err(ReobservationFailure::InvalidCorrespondence(message)) if message.contains("担当集合")));

        let invalid_shared = std::str::from_utf8(LAW)
            .unwrap()
            .replace(
                "set<Root>{a,b}",
                "if mb.quantity=0 then set<Root>{a,b} else set<Root>{a,b}",
            )
            .replace("list<(Part,Part)>[(ma,mb)];", "list<(Part,Part)>[(ma,ma)];");
        let raw = QUERIES.replace(",local.a=$selected.object", "");
        let previous = evaluate_observed(
            prepared_with("before", BEFORE, invalid_shared.as_bytes(), &raw, &c),
            &c,
        )
        .unwrap();
        assert!(matches!(reevaluate_assembly(
            &previous, prepared_with("after", &incomplete, invalid_shared.as_bytes(), &raw, &c),
            &alignment, &c,
        ), Err(ReobservationFailure::InvalidCorrespondence(message)) if message.contains("共有対")));
    }

    #[test]
    fn a_checked_repair_in_a_foreign_snapshot_leaves_assembly_undetermined() {
        let (prefix, snapshots) = AFTER.split_once("\"snapshots\": [").unwrap();
        let (body, suffix) = snapshots.rsplit_once("\n  ]").unwrap();
        let foreign = body.replace("\"after\"", "\"foreign\"");
        let map = format!("{prefix}\"snapshots\": [{body},{foreign}\n  ]{suffix}");
        let c = Control::unlimited();
        let foreign_repair = QUERIES
            .lines()
            .map(|line| {
                if line.starts_with("within=") || line.starts_with("prepareIt=") {
                    line.replace("@SNAP/", "@foreign/")
                } else {
                    line.to_owned()
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        let mixed_locals = foreign_repair
            .replace("joined=", "wrong=build(Assembly,on=@SNAP/A)\njoined=")
            .replace(
                "local.a=$selected.object",
                "local.a=$wrong.object,local.b=$selected.object",
            );
        let foreign_build = QUERIES
            .replace("joined=", "wrong=build(Assembly,on=@foreign/A)\njoined=")
            .replace("local.a=$selected.object", "local.a=$wrong.object");
        let foreign_binding = QUERIES.replace("a=@SNAP/A,b=@SNAP/B", "a=@foreign/A,b=@SNAP/B");
        let outside = QUERIES.replace("b=@SNAP/B", "b=@foreign/B");
        let only_foreign = std::str::from_utf8(LAW)
            .unwrap()
            .replace("set<Root>{a,b}", "set<Root>{b}")
            .replace("list<(Part,Part)>[(ma,mb)]", "list<(Part,Part)>[]");
        let empty = std::str::from_utf8(LAW)
            .unwrap()
            .replace("set<Root>{a,b}", "set<Root>{}")
            .replace("list<(Part,Part)>[(ma,mb)]", "list<(Part,Part)>[]");
        for (law, queries) in [
            (LAW, &foreign_repair),
            (empty.as_bytes(), &foreign_repair),
            (LAW, &mixed_locals),
            (LAW, &foreign_build),
            (LAW, &foreign_binding),
            (only_foreign.as_bytes(), &outside),
        ] {
            let result =
                evaluate_observed(prepared_with("after", &map, law, queries, &c), &c).unwrap();
            assert_eq!(status(&result, "selected"), Decision::Established);
            assert_eq!(status(&result, "joined"), Decision::Undetermined);
            let joined = result
                .answers
                .iter()
                .find(|answer| answer.id == "joined")
                .unwrap();
            assert!(matches!(joined.reasons.as_slice(), [reason]
                if matches!(&reason.kind, ReasonKind::UnsupportedAlgorithm { .. })));
            assert!(!joined.outputs.contains_key("assembly"));
            let global = result
                .answers
                .iter()
                .find(|answer| answer.id == "global")
                .unwrap();
            assert_eq!(global.status, Decision::Undetermined);
            assert!(
                global
                    .reasons
                    .iter()
                    .any(|reason| matches!(&reason.kind, ReasonKind::DependencyBlocked { .. }))
            );
            assert!(
                result
                    .issues
                    .iter()
                    .all(|reason| !matches!(&reason.kind, ReasonKind::Internal(_)))
            );
        }

        let foreign_member = r#"{
          "id":"foreign", "origin":"model",
          "subjects":[{"id":"b","type":"Assemble.Part","origin":"model"}],
          "atoms":[
            {"id":"b-owner","subject":"b","field":"Assemble.Part.owner","value":["after","B"],"origin":"model"},
            {"id":"b-quantity","subject":"b","field":"Assemble.Part.quantity","value":"0","origin":"model"},
            {"id":"b-links","subject":"b","field":"Assemble.Part.links","value":[],"origin":"model"}
          ]
        }"#;
        let map = format!("{prefix}\"snapshots\": [{body},{foreign_member}\n  ]{suffix}");
        let blocked = QUERIES.replace("index=0", "index=100");
        let pairs = [
            ("A", "A"),
            ("B", "B"),
            ("G", "G"),
            ("a", "a"),
            ("b", "b"),
            ("ma", "ma"),
            ("mb", "mb"),
        ];
        let alignment = AssemblyAlignment {
            before_snapshot: "before",
            after_snapshot: "after",
            reading: "Assembly",
            subjects: &pairs,
            assembly: "joined",
            previous_candidate: "pick",
            current_solve: "solveIt",
        };
        let previous = evaluate_observed(prepared("before", BEFORE, &c), &c).unwrap();
        assert!(matches!(reevaluate_assembly(
            &previous, prepared_with("after", &map, LAW, &blocked, &c), &alignment, &c,
        ), Err(ReobservationFailure::Unsupported(message)) if message.contains("所属個体")));

        // The known foreign member still matters when another observation
        // blocks the interface View independently of the local selection.
        let (_, snapshots) = BEFORE.split_once("\"snapshots\": [").unwrap();
        let (before_body, _) = snapshots.rsplit_once("\n  ]").unwrap();
        let pending_body = before_body.replace("\"before\"", "\"after\"");
        let pending_map =
            format!("{prefix}\"snapshots\": [{pending_body},{foreign_member}\n  ]{suffix}");
        let law = std::str::from_utf8(LAW).unwrap().replace(
            "list<(Part,Part)>[(ma,mb)];",
            "if mb.quantity=0 then list<(Part,Part)>[(ma,mb)] else list<(Part,Part)>[(mb,ma)];",
        );
        let raw = QUERIES.replace(",local.a=$selected.object", "");
        let result = evaluate_observed(
            prepared_with("after", &pending_map, law.as_bytes(), &raw, &c),
            &c,
        )
        .unwrap();
        let joined = result
            .answers
            .iter()
            .find(|answer| answer.id == "joined")
            .unwrap();
        assert!(matches!(joined.reasons.as_slice(), [reason]
            if matches!(&reason.kind, ReasonKind::UnsupportedAlgorithm { .. })));
    }

    #[test]
    fn layout_alignment_checks_both_target_and_fragment_structure() {
        let c = Control::unlimited();
        let alignment = AssemblyAlignment {
            before_snapshot: "before",
            after_snapshot: "after",
            reading: "Assembly",
            subjects: &[
                ("A", "A"),
                ("B", "B"),
                ("G", "G"),
                ("a", "a"),
                ("b", "b"),
                ("ma", "ma"),
                ("mb", "mb"),
            ],
            assembly: "joined",
            previous_candidate: "pick",
            current_solve: "solveIt",
        };
        let law = std::str::from_utf8(LAW).unwrap();
        let occupied = AFTER.replacen(
            r#""subjects": ["#,
            r#""subjects": [{"id":"occupied","type":"Assemble.Part","origin":"model"},"#,
            1,
        ).replacen(
            r#""atoms": ["#,
            r#""atoms": [{"id":"occupied-owner","subject":"occupied","field":"Assemble.Part.owner","value":["after","G"],"origin":"model"},"#,
            1,
        );
        let with_target = law.replace("list<(Part,Part)>[(ma,mb)]", "list<(Part,Part)>[]");
        let target_in_roster = QUERIES.replace("a=@SNAP/A,b=@SNAP/B", "a=@SNAP/A,b=@SNAP/G");
        for (law, asks, after, detail) in [
            (
                law.replace("set<Root>{a,b}", "set<Root>{}"),
                QUERIES.replace(",local.a=$selected.object", ""),
                AFTER,
                "担当集合が空",
            ),
            (
                law.to_owned(),
                QUERIES.replace("local.a=", "local.b="),
                AFTER,
                "担当の明示束縛",
            ),
            (
                law.replace("set<Root>{a,b}", "set<Root>{b}")
                    .replace("list<(Part,Part)>[(ma,mb)]", "list<(Part,Part)>[]"),
                QUERIES.to_owned(),
                AFTER,
                "評価済みの担当集合",
            ),
            (with_target, target_in_roster, AFTER, "異なるroot"),
            (
                law.to_owned(),
                QUERIES.to_owned(),
                &occupied,
                "既存の所属個体",
            ),
        ] {
            let previous = evaluate_observed(
                prepared_with("before", BEFORE, law.as_bytes(), &asks, &c),
                &c,
            )
            .unwrap();
            assert!(matches!(reevaluate_assembly(
                &previous, prepared_with("after", after, law.as_bytes(), &asks, &c),
                &alignment, &c,
            ), Err(ReobservationFailure::InvalidCorrespondence(message)) if message.contains(detail)));
        }
        let position = concat!(
            "\"id\": \"a-links\",\n          \"subject\": \"a\",\n",
            "          \"field\": \"Assemble.Part.links\",\n          \"value\": []",
        );
        let after = AFTER.replacen(position, &position.replace("[]", r#"[["after","mb"]]"#), 1);
        assert_ne!(after, AFTER);
        let previous = evaluate_observed(prepared("before", BEFORE, &c), &c).unwrap();
        for asks in [QUERIES.to_owned(), QUERIES.replace("index=0", "index=100")] {
            assert!(matches!(reevaluate_assembly(
                &previous, prepared_with("after", &after, LAW, &asks, &c),
                &alignment, &c,
            ), Err(ReobservationFailure::InvalidCorrespondence(message)) if message.contains("同一視")));
        }
        let bounded_owned = AFTER.replacen(
            r#""subjects": ["#,
            r#""subjects": [{"id":"step","type":"Assemble.Step","origin":"model"},"#,
            1,
        ).replacen(
            r#""atoms": ["#,
            concat!(
                r#""atoms": [{"id":"step-owner","subject":"step","field":"Assemble.Step.owner","value":["after","B"],"origin":"model"},"#,
                r#"{"id":"step-to","subject":"step","field":"Assemble.Step.to","value":["after","mb"],"origin":"model"},"#,
            ),
            1,
        );
        let raw = QUERIES.replace(",local.a=$selected.object", "");
        let previous =
            evaluate_observed(prepared_with("before", BEFORE, LAW, &raw, &c), &c).unwrap();
        let reobserved = reevaluate_assembly(
            &previous,
            prepared_with("after", &bounded_owned, LAW, &raw, &c),
            &alignment,
            &c,
        )
        .unwrap();
        assert_eq!(reobserved.candidate(), CandidateContinuity::Retained);
        assert!(reobserved.layout_missing().is_empty());
        let joined = reobserved
            .evaluation()
            .answers
            .iter()
            .find(|answer| answer.id == "joined")
            .unwrap();
        assert_eq!(joined.status, Decision::Undetermined);
        assert!(
            joined
                .reasons
                .iter()
                .any(|reason| reason.missing.iter().any(|fact| {
                    fact.subject == "step"
                        && fact
                            .field
                            .as_ref()
                            .is_some_and(|field| field == "Assemble.Step.from")
                }))
        );

        let unrelated = concat!(
            ",\n        {\n          \"id\": \"b-links\",\n          \"subject\": \"b\",\n",
            "          \"field\": \"Assemble.Part.links\",\n          \"value\": [],\n",
            "          \"origin\": \"model\"\n        }",
        );
        let incomplete = AFTER.replacen(unrelated, "", 1);
        assert_ne!(AFTER, incomplete);
        let no_alias = law.replace("list<(Part,Part)>[(ma,mb)]", "list<(Part,Part)>[]");
        let previous = evaluate_observed(
            prepared_with("before", BEFORE, no_alias.as_bytes(), QUERIES, &c),
            &c,
        )
        .unwrap();
        for asks in [QUERIES.to_owned(), QUERIES.replace("index=0", "index=100")] {
            let reobserved = reevaluate_assembly(
                &previous,
                prepared_with("after", &incomplete, no_alias.as_bytes(), &asks, &c),
                &alignment,
                &c,
            )
            .unwrap();
            assert_eq!(reobserved.candidate(), CandidateContinuity::Retained);
            assert!(reobserved.layout_missing().is_empty());
            assert_eq!(
                status(reobserved.evaluation(), "joined"),
                Decision::Undetermined
            );
        }
    }

    #[test]
    fn an_empty_change_roster_has_the_single_empty_assignment() {
        let c = Control::unlimited();
        let asks = QUERIES
            .replace(",local.a=$selected.object", "")
            .replace("Assembly.singleton,p=@SNAP/a", "Assembly.within,r=@SNAP/G")
            .replace(
                "Assembly.desired,using=Assembly.choose,on=@SNAP/A,p=@SNAP/a,b=@SNAP/b",
                "Assembly.boundary,using=Assembly.choose,on=@SNAP/G,p=@SNAP/ma",
            );
        let before =
            evaluate_observed(prepared_with("before", BEFORE, LAW, &asks, &c), &c).unwrap();
        let pairs = [
            ("A", "A"),
            ("B", "B"),
            ("G", "G"),
            ("ma", "ma"),
            ("mb", "mb"),
        ];
        let alignment = AssemblyAlignment {
            before_snapshot: "before",
            after_snapshot: "after",
            reading: "Assembly",
            subjects: &pairs,
            assembly: "joined",
            previous_candidate: "pick",
            current_solve: "solveIt",
        };
        let result = reevaluate_assembly(
            &before,
            prepared_with("after", AFTER, LAW, &asks, &c),
            &alignment,
            &c,
        )
        .unwrap();
        assert_eq!(
            status(result.evaluation(), "solveIt"),
            Decision::Established
        );
        assert_eq!(result.candidate(), CandidateContinuity::Retained);
    }
}
