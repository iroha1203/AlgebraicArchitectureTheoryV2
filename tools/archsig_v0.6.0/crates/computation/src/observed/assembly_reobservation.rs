//! 明示した同一性の下で、局所組立ての不足位置と有限候補を現在の入力へ照合する。
use super::{
    EvaluationFailure, ObservedEvaluation, PreparedObserved, assembly_plan,
    construction_result::ConstructionData,
    environment::Environment,
    model_assembly,
    projection::ProjectionStep,
    reevaluate_observed,
    request::{QuestionKind, Request, Selector},
    result::{Fact, Node, Payload, ReasonKind, Scalar, ValidationFailure},
};
use archsig_common::control::{Checkpoint, Control, Signal};
use archsig_input::archmap::{FactData, Slot, Subject, Value};
use std::collections::{BTreeMap, BTreeSet};

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
    candidate: CandidateContinuity,
    selected_candidate: Option<String>,
    continuity_stop: Option<Signal>,
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
    pub fn candidate(&self) -> CandidateContinuity {
        self.candidate
    }
    /// Candidate consumed by the current local apply when the current assembly established.
    pub fn selected_candidate(&self) -> Option<&str> {
        self.selected_candidate.as_deref()
    }
    pub fn continuity_stop(&self) -> Option<Signal> {
        self.continuity_stop
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
    shared: Option<Vec<(Fact, Fact)>>,
    missing: Vec<Fact>,
}

fn retained_layout<'a>(
    evaluation: &'a ObservedEvaluation,
    id: &str,
) -> Option<&'a assembly_plan::Assembly> {
    let answer = evaluation.answers.iter().find(|answer| answer.id == id)?;
    let node = evaluation.nodes.get(answer.claim?.0)?;
    let Some(Payload::Construction(value)) = &node.payload else {
        return None;
    };
    let ConstructionData::Build(data) = &value.data else {
        return None;
    };
    data.plan().assembly.as_deref()
}

fn checked_layout(
    evaluation: &ObservedEvaluation,
    request: &Request,
    control: &Control,
) -> Result<Layout, ReobservationFailure> {
    if let Some(assembly) = retained_layout(evaluation, &request.id) {
        if let Some(assembly_plan::Failure::Unsupported(detail)) = &assembly.failure
            && detail.affects_layout
        {
            return Err(ReobservationFailure::Unsupported(detail.detail.clone()));
        }
        return layout_from_reads(&assembly.fragments, &assembly.interfaces, control);
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
    let fragments = assembly_plan::read(&env, head, &bindings).map_err(classify)?;
    let interfaces = assembly_plan::read(&env, along, &bindings).map_err(classify)?;
    let target = request.arguments.iter().find(|arg| arg.name == "on");
    let Some(Selector::Subject { snapshot, subject }) = target.map(|arg| &arg.value) else {
        return Err(unsupported("組立て先の明示rootがない"));
    };
    let target = Fact::from(FactData {
        snapshot: snapshot.clone(),
        subject: subject.clone(),
        field: None,
        atom: None,
    });
    let reading = prepared.inputs().law().declarations()[head]
        .reading
        .as_str();
    if let Some(problem) =
        assembly_plan::layout_snapshot(&env, reading, &target, &fragments, &interfaces, control)
            .map_err(classify)?
    {
        return Err(ReobservationFailure::Unsupported(problem.detail));
    }
    layout_from_reads(&fragments, &interfaces, control)
}

fn layout_from_reads(
    fragments: &assembly_plan::Read,
    interfaces: &assembly_plan::Read,
    control: &Control,
) -> Result<Layout, ReobservationFailure> {
    let classify = |failure| match failure {
        ValidationFailure::Stop(signal) => ReobservationFailure::Stopped(signal),
        _ => ReobservationFailure::Unsupported("組立ての View を現在の原始観測で読めない".into()),
    };
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
    let mut missing = fragments.metadata.missing.clone();
    missing.extend(interfaces.metadata.missing.iter().cloned());
    missing.sort();
    missing.dedup();
    let roots = match &fragments.value {
        Some(Scalar::Set { items, .. }) => Some(
            items
                .iter()
                .map(|item| {
                    control.checkpoint(Checkpoint::ConfigurationMap)?;
                    assembly_plan::fact(item)
                })
                .collect::<Result<Vec<_>, _>>()
                .map_err(classify)?,
        ),
        None if !fragments.metadata.missing.is_empty() => None,
        _ => {
            return Err(ReobservationFailure::Unsupported(
                "担当集合を確定できない".into(),
            ));
        }
    };
    let shared = match &interfaces.value {
        Some(value) => Some(assembly_plan::interfaces(value, control).map_err(classify)?),
        None if !interfaces.metadata.missing.is_empty() => None,
        _ => {
            return Err(ReobservationFailure::Unsupported(
                "共有対を確定できない".into(),
            ));
        }
    };
    Ok(Layout {
        roots,
        shared,
        missing,
    })
}

fn checked_shared_partition(
    layout: &Layout,
    roster: &BTreeMap<&str, &Subject>,
    snapshot: &str,
    image: impl Fn(&Fact) -> Result<Fact, ReobservationFailure>,
    missing: &mut Vec<Fact>,
    control: &Control,
) -> Result<BTreeMap<Fact, Fact>, ReobservationFailure> {
    let shared = layout
        .shared
        .as_ref()
        .ok_or_else(|| invalid("共有対が未確定"))?;
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
        let field = member
            .fields
            .iter()
            .find(|field| field.name.is_owner())
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
                members.insert(endpoint.clone(), (root, image(endpoint)?));
            }
        }
        let (left_owner, a) = &members[left];
        let (right_owner, b) = &members[right];
        if left == right
            || (left_owner.is_some() && left_owner == right_owner)
            || roster[left.subject.as_str()].ty != roster[right.subject.as_str()].ty
        {
            return Err(invalid("共有対は別担当の同じ型の個体を要求する"));
        }
        parent.entry(a.clone()).or_insert_with(|| a.clone());
        parent.entry(b.clone()).or_insert_with(|| b.clone());
        model_assembly::link_shared(&mut parent, a, b, control).map_err(classify)?;
    }
    let keys = parent.keys().cloned().collect::<Vec<_>>();
    for item in keys {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        model_assembly::representative(&mut parent, &item, control).map_err(classify)?;
    }
    let mut local_images = BTreeSet::new();
    for (owner, member) in members.values() {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        if let Some(owner) = owner
            && !local_images.insert((owner, &parent[member]))
        {
            return Err(invalid("共有対の閉包が同じ担当の異なる個体を同一視する"));
        }
    }
    Ok(parent)
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
    let old = before.inputs().sources();
    let new = current.inputs().sources();
    if old.law().bytes() != new.law().bytes()
        || old.definitions().len() != new.definitions().len()
        || !old
            .definitions()
            .iter()
            .zip(new.definitions())
            .all(|(a, b)| a.bytes() == b.bytes())
    {
        return Err(ReobservationFailure::Unsupported(
            "定義と Law が同一の読みを要求する".into(),
        ));
    }
    let before_request = question(before, alignment.assembly, QuestionKind::Assemble)?;
    let after_request = question(&current, alignment.assembly, QuestionKind::Assemble)?;
    let before_candidate = question(
        before,
        alignment.previous_candidate,
        QuestionKind::Candidate,
    )?;
    let Selector::Answer {
        id: prior_solve_id, ..
    } = &before_candidate.head
    else {
        return Err(invalid("前候補に元 solve がない"));
    };
    let prior_solve = question(before, prior_solve_id, QuestionKind::Solve)?;
    let new_solve = question(&current, alignment.current_solve, QuestionKind::Solve)?;
    let Selector::Answer {
        id: prior_prepare_id,
        ..
    } = &prior_solve.head
    else {
        return Err(ReobservationFailure::Unsupported(
            "finite prepare の前回 solve を要求する".into(),
        ));
    };
    let Selector::Answer {
        id: new_prepare_id, ..
    } = &new_solve.head
    else {
        return Err(ReobservationFailure::Unsupported(
            "finite prepare の現在 solve を要求する".into(),
        ));
    };
    let prior_prepare = question(before, prior_prepare_id, QuestionKind::Prepare)?;
    let new_prepare = question(&current, new_prepare_id, QuestionKind::Prepare)?;
    if prior_prepare.head != new_prepare.head
        || !selected_reading(before, prior_prepare, alignment.reading)
        || !selected_reading(&current, new_prepare, alignment.reading)
    {
        return Err(invalid(
            "finite repair の要求 Law または reading が対応しない",
        ));
    }
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
    let mut layout_missing = Vec::new();
    for (old, new) in pairs.values() {
        for old_field in old.fields.iter().filter(|f| f.name.is_owner()) {
            control.checkpoint(Checkpoint::ConfigurationMap)?;
            let new_field = new
                .fields
                .iter()
                .find(|f| f.name == old_field.name && f.ty == old_field.ty)
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
                    layout_missing.extend([fact(old, old_field, None), fact(new, new_field, None)]);
                }
                (Slot::Missing, _) => layout_missing.push(fact(old, old_field, None)),
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
    let mut current_selection = None;
    for (prior, new) in [
        (before_request, after_request),
        (prior_prepare, new_prepare),
    ] {
        if prior.arguments.len() != new.arguments.len() {
            return Err(invalid("明示引数の件数が対応しない"));
        }
        // Both request resolvers normalize named arguments to name order.
        for (a, b) in prior.arguments.iter().zip(&new.arguments) {
            control.checkpoint(Checkpoint::ConfigurationMap)?;
            if a.name != b.name {
                return Err(invalid("明示引数名が対応しない"));
            }
            let matching = match (&a.value, &b.value) {
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
                    matches_subject(x, y)
                }
                (Selector::Declaration { .. }, Selector::Declaration { .. }) => a.value == b.value,
                (Selector::Answer { .. }, Selector::Answer { .. })
                    if a.name.starts_with("local.") =>
                {
                    if current_selection.is_some() {
                        return Err(ReobservationFailure::Unsupported(
                            "再照合する局所 apply は一つまで".into(),
                        ));
                    }
                    let (_, old_candidate) = repair_selection(before, &a.value, prior_solve)?;
                    let (new_apply, new_candidate) =
                        repair_selection(&current, &b.value, new_solve)?;
                    if old_candidate.id != alignment.previous_candidate {
                        return Err(invalid(
                            "前回の局所 apply が照合対象の前回候補を使用していない",
                        ));
                    }
                    current_selection = Some((new_apply.id.clone(), new_candidate.id.clone()));
                    true
                }
                _ => {
                    return Err(ReobservationFailure::Unsupported(
                        "root、共有位置と修復束縛を明示する".into(),
                    ));
                }
            };
            if !matching {
                return Err(invalid("root・共有個体・宣言・明示束縛の対応が違う"));
            }
        }
    }

    let before_answer = previous
        .answers
        .iter()
        .find(|a| a.id == alignment.assembly)
        .ok_or_else(|| invalid("before の組立て回答がない"))?;
    let mut observations = Vec::new();
    let mut seen = BTreeSet::new();
    for reason in before_answer
        .reasons
        .iter()
        .filter(|r| r.kind == ReasonKind::Missing)
    {
        for needed in &reason.missing {
            control.checkpoint(Checkpoint::ConfigurationMap)?;
            if !seen.insert(needed) {
                continue;
            }
            if needed.snapshot != alignment.before_snapshot {
                return Err(ReobservationFailure::Unsupported(
                    "前回の欠測が対応対象外の snapshot に属する".into(),
                ));
            }
            let Some((old, new)) = pairs.get(needed.subject.as_str()) else {
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
        }
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
    let mut continuity_stop = control.stop_reason();
    if continuity_stop.is_none() {
        let mut compare_layout = || -> Result<(), ReobservationFailure> {
            let before_layout = checked_layout(previous, before_request, control)?;
            let after_layout = checked_layout(
                &evaluation,
                question(
                    evaluation.prepared(),
                    alignment.assembly,
                    QuestionKind::Assemble,
                )?,
                control,
            )?;
            layout_missing.extend(before_layout.missing.iter().cloned());
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
                    &mut layout_missing,
                    control,
                )?)
            } else {
                None
            };
            let new_shared = if after_layout.shared.is_some() {
                Some(checked_shared_partition(
                    &after_layout,
                    &b,
                    alignment.after_snapshot,
                    after_subject,
                    &mut layout_missing,
                    control,
                )?)
            } else {
                None
            };
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
    layout_missing.sort();
    layout_missing.dedup();
    let candidate = match (
        output(previous, alignment.previous_candidate, "assignment"),
        output(&evaluation, alignment.current_solve, "solutions"),
    ) {
        (Some(old), Some(new)) if continuity_stop.is_none() && layout_missing.is_empty() => {
            match super::repair_problem::reobserved_membership(old, new, translate, control) {
                Ok(Some(true)) => CandidateContinuity::Retained,
                Ok(Some(false)) => CandidateContinuity::Excluded,
                Ok(None) => CandidateContinuity::Undetermined,
                Err(ValidationFailure::Stop(signal)) => {
                    continuity_stop = Some(signal);
                    CandidateContinuity::Undetermined
                }
                Err(_) => {
                    return Err(ReobservationFailure::Unsupported(
                        "有限割当ての対応を照合できない".into(),
                    ));
                }
            }
        }
        _ => CandidateContinuity::Undetermined,
    };
    let selected_candidate = current_selection.and_then(|(apply, candidate)| {
        (output(&evaluation, alignment.assembly, "assembly").is_some()
            && output(&evaluation, &apply, "object").is_some())
        .then_some(candidate)
    });
    Ok(ReobservedAssembly {
        evaluation,
        observations,
        layout_missing,
        candidate,
        selected_candidate,
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

    #[test]
    fn explicit_reobservation_matches_a_shared_slot_and_rechecks_an_actual_assignment() {
        let c = Control::unlimited();
        let quantity = |map: &str, subject: &str, old: u32, new: u32| {
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
        };
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
        let (left, right) = &layout.shared.as_ref().unwrap()[0];
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
                shared: Some(vec![(left.clone(), right.clone()), edge]),
                missing: vec![],
            };
            assert!(matches!(
                checked_shared_partition(&invalid_layout, &roster, "before", |fact| Ok(fact.clone()), &mut Vec::new(), &c),
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
        let owner_law = pending_law.replace("if mb.quantity=0", "if mb.owner=b and mb.quantity=0");
        let missing_owner = BEFORE.replace(
            concat!(
                "        {\n          \"id\": \"mb-owner\",\n          \"subject\": \"mb\",\n",
                "          \"field\": \"Assemble.Part.owner\",\n          \"value\": [\n",
                "            \"before\",\n            \"B\"\n          ],\n          \"origin\": \"model\"\n        },\n"
            ),
            "",
        );
        assert_ne!(missing_owner, BEFORE);
        let pending = evaluate_observed(
            prepared_with("before", &missing_owner, owner_law.as_bytes(), QUERIES, &c),
            &c,
        )
        .unwrap();
        let completed = reevaluate_assembly(
            &pending,
            prepared_with("after", AFTER, owner_law.as_bytes(), QUERIES, &c),
            &alignment,
            &c,
        )
        .unwrap();
        assert!(completed.layout_missing().iter().any(|slot| {
            slot.snapshot == "before"
                && slot.subject == "mb"
                && slot.field.as_ref().is_some_and(|name| name.is_owner())
        }));
        assert_eq!(completed.candidate(), CandidateContinuity::Undetermined);
        assert_eq!(completed.selected_candidate(), Some("pick"));
        assert!(completed.observations().iter().any(|matched| {
            matched.needed().subject == "mb"
                && matched
                    .observed()
                    .is_some_and(|atom| atom.atom.as_deref() == Some("mb-owner"))
        }));
        assert_eq!(
            status(completed.evaluation(), "global"),
            Decision::Established
        );

        let root_law = pending_law.replace(
            "set<Root>{a,b}",
            "if ma.quantity=0 then set<Root>{a,b} else set<Root>{a}",
        );
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
        let foreign_binding = QUERIES.replace("a=@SNAP/A,b=@SNAP/B", "a=@foreign/A,b=@SNAP/B");
        let outside = QUERIES.replace("b=@SNAP/B", "b=@foreign/B");
        let only_foreign = std::str::from_utf8(LAW)
            .unwrap()
            .replace("set<Root>{a,b}", "set<Root>{b}")
            .replace("list<(Part,Part)>[(ma,mb)]", "list<(Part,Part)>[]");
        for (law, queries) in [
            (LAW, &foreign_repair),
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
    fn an_empty_change_roster_has_the_single_empty_assignment() {
        let c = Control::unlimited();
        let asks = QUERIES
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
