//! 明示した同一性の下で、局所組立ての不足位置と有限候補を現在の入力へ照合する。
use super::{
    EvaluationFailure, ObservedEvaluation, PreparedObserved, reevaluate_observed,
    request::{QuestionKind, Request, Selector},
    result::{Fact, Node, ReasonKind, Scalar, ValidationFailure},
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
    MissingOwner(Fact),
    Unsupported(String),
    Evaluation(Box<EvaluationFailure>),
    Stopped(Signal),
}

impl From<Signal> for ReobservationFailure {
    fn from(signal: Signal) -> Self {
        Self::Stopped(signal)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum CandidateContinuity {
    Retained,
    Excluded,
    Undetermined,
}

#[derive(Debug)]
pub struct ObservationMatch {
    pub needed: Fact,
    pub observed: Option<Fact>,
}

#[derive(Debug)]
pub struct ReobservedAssembly {
    pub evaluation: ObservedEvaluation,
    pub observations: Vec<ObservationMatch>,
    pub candidate: CandidateContinuity,
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
    prepared.requests().requests().iter().find(|r| r.id == id && r.kind == kind)
        .ok_or_else(|| invalid("対応する種類・ID の元要求がない"))
}

fn output<'a>(evaluation: &'a ObservedEvaluation, id: &str, field: &str) -> Option<&'a Node> {
    let reference = evaluation.answers.iter().find(|a| a.id == id)?.outputs.get(field)?;
    evaluation.nodes.get(reference.0)
}

fn selected_reading(prepared: &PreparedObserved, question: &Request, reading: &str) -> bool {
    question.declaration().is_some_and(|name|
        prepared.inputs().law().declarations()[name].reading == reading)
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
        || !old.definitions().iter().zip(new.definitions()).all(|(a,b)| a.bytes() == b.bytes())
    {
        return Err(ReobservationFailure::Unsupported("定義と Law が同一の読みを要求する".into()));
    }
    let before_request = question(before, alignment.assembly, QuestionKind::Assemble)?;
    let after_request = question(&current, alignment.assembly, QuestionKind::Assemble)?;
    let before_candidate = question(before, alignment.previous_candidate, QuestionKind::Candidate)?;
    let Selector::Answer { id: prior_solve_id, .. } = &before_candidate.head else {
        return Err(invalid("前候補に元 solve がない"));
    };
    let prior_solve = question(before, prior_solve_id, QuestionKind::Solve)?;
    let new_solve = question(&current, alignment.current_solve, QuestionKind::Solve)?;
    let Selector::Answer { id: prior_prepare_id, .. } = &prior_solve.head else {
        return Err(ReobservationFailure::Unsupported("finite prepare の前回 solve を要求する".into()));
    };
    let Selector::Answer { id: new_prepare_id, .. } = &new_solve.head else {
        return Err(ReobservationFailure::Unsupported("finite prepare の現在 solve を要求する".into()));
    };
    let prior_prepare = question(before, prior_prepare_id, QuestionKind::Prepare)?;
    let new_prepare = question(&current, new_prepare_id, QuestionKind::Prepare)?;
    if prior_prepare.head != new_prepare.head
        || !selected_reading(before, prior_prepare, alignment.reading)
        || !selected_reading(&current, new_prepare, alignment.reading)
    {
        return Err(invalid("finite repair の要求 Law または reading が対応しない"));
    }
    if before_request.head != after_request.head
        || !selected_reading(before, before_request, alignment.reading)
        || !selected_reading(&current, after_request, alignment.reading)
    {
        return Err(invalid("組立ての View または reading が対応しない"));
    }
    let snapshot = |prepared: &PreparedObserved, id: &str| {
        prepared.inputs().archmap().snapshots().iter().position(|s| s.id == id)
            .ok_or_else(|| invalid("明示された snapshot がない"))
    };
    let a = &before.inputs().archmap().snapshots()[snapshot(before, alignment.before_snapshot)?];
    let current_inputs = current.shared_inputs();
    let b = &current_inputs.archmap().snapshots()[snapshot(&current, alignment.after_snapshot)?];
    let mut pairs = BTreeMap::new();
    let mut used = BTreeSet::new();
    for &(left, right) in alignment.subjects {
        control.checkpoint(Checkpoint::ConfigurationMap)?;
        let old = a.subjects.iter().find(|s| s.id == left).ok_or_else(|| invalid("before subject がない"))?;
        let new = b.subjects.iter().find(|s| s.id == right).ok_or_else(|| invalid("after subject がない"))?;
        if old.ty != new.ty || pairs.insert(left, (old, new)).is_some() || !used.insert(right) {
            return Err(invalid("subject 対応は同型の一対一を要求する"));
        }
    }
    let matches_subject = |left: &str, right: &str| pairs.get(left).is_some_and(|(_, target)| target.id == right);
    for (old, new) in pairs.values() {
        for old_field in old.fields.iter().filter(|f| f.name.is_owner()) {
            control.checkpoint(Checkpoint::ConfigurationMap)?;
            let new_field = new.fields.iter().find(|f| f.name == old_field.name && f.ty == old_field.ty)
                .ok_or_else(|| invalid("owner field の型が対応しない"))?;
            match (&old_field.slot, &new_field.slot) {
                (Slot::Missing, _) => return Err(ReobservationFailure::MissingOwner(fact(old, old_field, None))),
                (_, Slot::Missing) => return Err(ReobservationFailure::MissingOwner(fact(new, new_field, None))),
                (Slot::Known { value: Value::Ref {snapshot: a, subject: x}, .. },
                 Slot::Known { value: Value::Ref {snapshot: b, subject: y}, .. })
                    if a == alignment.before_snapshot && b == alignment.after_snapshot && matches_subject(x, y) => {}
                _ => return Err(invalid("owner が明示した同一性に沿わない")),
            }
        }
    }
    for (prior, new) in [(before_request, after_request), (prior_prepare, new_prepare)] {
        if prior.arguments.len() != new.arguments.len() {
            return Err(invalid("明示引数の件数が対応しない"));
        }
        for (a, b) in prior.arguments.iter().zip(&new.arguments) {
            control.checkpoint(Checkpoint::ConfigurationMap)?;
            if a.name != b.name {
                return Err(invalid("明示引数名が対応しない"));
            }
            let matching = match (&a.value, &b.value) {
                (Selector::Subject {snapshot: s, subject: x}, Selector::Subject {snapshot: t, subject: y}) =>
                    s == alignment.before_snapshot && t == alignment.after_snapshot && matches_subject(x, y),
                (Selector::Declaration { .. }, Selector::Declaration { .. }) => a.value == b.value,
                (Selector::Answer { .. }, Selector::Answer { .. }) if a.name.starts_with("local.") =>
                    a.value == b.value,
                _ => return Err(ReobservationFailure::Unsupported("root、共有位置と修復束縛を明示する".into())),
            };
            if !matching {
                return Err(invalid("root・共有個体・宣言・明示束縛の対応が違う"));
            }
        }
    }

    let before_answer = previous.answers.iter().find(|a| a.id == alignment.assembly)
        .ok_or_else(|| invalid("before の組立て回答がない"))?;
    let mut observations = Vec::new();
    let mut seen = BTreeSet::new();
    for reason in before_answer.reasons.iter().filter(|r| r.kind == ReasonKind::Missing) {
        for needed in &reason.missing {
            control.checkpoint(Checkpoint::ConfigurationMap)?;
            if !seen.insert(needed) { continue; }
            let Some((old, new)) = pairs.get(needed.subject.as_str())
                .filter(|(old, _)| old.snapshot == needed.snapshot)
            else {
                return Err(invalid("組立ての不足位置に subject 対応がない"));
            };
            let name = needed.field.as_ref().ok_or_else(|| invalid("不足位置に field がない"))?;
            let old_field = old.fields.iter().find(|f| &f.name == name && matches!(f.slot, Slot::Missing))
                .ok_or_else(|| invalid("before の不足位置が原始 slot と一致しない"))?;
            let field = new.fields.iter().find(|f| &f.name == name && f.ty == old_field.ty)
                .ok_or_else(|| invalid("after の field と型が一致しない"))?;
            let observed = match &field.slot {
                Slot::Missing => None,
                Slot::Known { atom, .. } => Some(fact(new, field, Some(atom.clone()))),
            };
            observations.push(ObservationMatch { needed: needed.clone(), observed });
        }
    }
    let translate = |value: &Scalar| match value {
        Scalar::Subject { snapshot, subject, entity } if snapshot == alignment.before_snapshot =>
            pairs.get(subject.as_str()).map(|(_, target)| Scalar::Subject {
                snapshot: target.snapshot.clone(), subject: target.id.clone(), entity: entity.clone(),
            }),
        _ => None,
    };
    let evaluation = reevaluate_observed(previous, current, control)
        .map_err(|failure| ReobservationFailure::Evaluation(Box::new(failure)))?;
    let candidate = match (
        output(previous, alignment.previous_candidate, "assignment"),
        output(&evaluation, alignment.current_solve, "solutions"),
    ) {
        (Some(old), Some(new)) => match super::repair_problem::reobserved_membership(old, new, translate, control) {
            Ok(Some(true)) => CandidateContinuity::Retained,
            Ok(Some(false)) => CandidateContinuity::Excluded,
            Ok(None) => CandidateContinuity::Undetermined,
            Err(ValidationFailure::Stop(signal)) => return Err(ReobservationFailure::Stopped(signal)),
            Err(_) => return Err(ReobservationFailure::Unsupported("有限割当ての対応を照合できない".into())),
        },
        _ => CandidateContinuity::Undetermined,
    };
    Ok(ReobservedAssembly { evaluation, observations, candidate })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::{evaluate_observed, prepare_observed, result::Decision};
    use archsig_input::input::InputSources;

    const DEFINITIONS: &[u8] = include_bytes!("../../../../tests/fixtures/r2-assembly-reobservation/definitions.json");
    const LAW: &[u8] = include_bytes!("../../../../tests/fixtures/r2-assembly-reobservation/laws.law");
    const BEFORE: &str = include_str!("../../../../tests/fixtures/r2-assembly-reobservation/before.json");
    const AFTER: &str = include_str!("../../../../tests/fixtures/r2-assembly-reobservation/after.json");
    const QUERIES: &str = include_str!("../../../../tests/fixtures/r2-assembly-reobservation/queries.txt");

    fn prepared(snapshot: &str, map: &str, c: &Control) -> PreparedObserved {
        let asks = QUERIES.replace("SNAP", snapshot);
        let asks = asks.lines().collect::<Vec<_>>();
        prepare_observed(InputSources::from_bytes(vec![DEFINITIONS.to_vec()], LAW.to_vec(), map.as_bytes().to_vec()), &asks, c).unwrap()
    }

    fn status(result: &ObservedEvaluation, id: &str) -> Decision {
        result.answers.iter().find(|a| a.id == id).unwrap().status
    }

    #[test]
    fn explicit_reobservation_matches_a_shared_slot_and_rechecks_an_actual_assignment() {
        let c = Control::unlimited();
        let before = evaluate_observed(prepared("before", BEFORE, &c), &c).unwrap();
        assert_eq!(status(&before, "pick"), Decision::Established);
        assert_eq!(status(&before, "joined"), Decision::Undetermined);
        assert_eq!(status(&before, "global"), Decision::Undetermined);
        let pairs = [("A", "A"), ("B", "B"), ("G", "G"), ("a", "a"), ("b", "b"), ("ma", "ma"), ("mb", "mb")];
        let mut alignment = AssemblyAlignment {
            before_snapshot: "before",
            after_snapshot: "after",
            reading: "Assembly",
            subjects: &pairs,
            assembly: "joined",
            previous_candidate: "pick",
            current_solve: "solveIt",
        };
        let next = reevaluate_assembly(&before, prepared("after", AFTER, &c), &alignment, &c).unwrap();
        assert_eq!(next.candidate, CandidateContinuity::Retained);
        let [matched] = next.observations.as_slice() else { panic!("one shared observation") };
        assert_eq!(matched.needed.snapshot, "before");
        assert_eq!(matched.needed.subject, "mb");
        assert!(matched.needed.atom.is_none());
        let observed = matched.observed.as_ref().unwrap();
        assert_eq!(observed.snapshot, "after");
        assert_eq!(observed.subject, "mb");
        assert_eq!(observed.field, matched.needed.field);
        assert_eq!(observed.atom.as_deref(), Some("observed-shared-quantity"));
        assert_eq!(status(&next.evaluation, "joined"), Decision::Established);
        assert_eq!(status(&next.evaluation, "global"), Decision::Established);

        let revised = AFTER.replacen(
            concat!("\"id\": \"b-quantity\",\n          \"subject\": \"b\",\n",
                "          \"field\": \"Assemble.Part.quantity\",\n          \"value\": \"0\""),
            concat!("\"id\": \"b-quantity\",\n          \"subject\": \"b\",\n",
                "          \"field\": \"Assemble.Part.quantity\",\n          \"value\": \"1\""),
            1,
        );
        assert_ne!(revised, AFTER);
        let next = reevaluate_assembly(&before, prepared("after", &revised, &c), &alignment, &c).unwrap();
        assert_eq!(next.candidate, CandidateContinuity::Excluded);
        assert_eq!(status(&next.evaluation, "pick"), Decision::Established);
        assert_eq!(status(&next.evaluation, "selected"), Decision::Established);
        assert_eq!(status(&next.evaluation, "joined"), Decision::Established);
        assert_eq!(status(&next.evaluation, "global"), Decision::Established);

        let mut wrong = pairs;
        wrong.swap(0, 1);
        wrong[0].1 = "A";
        wrong[1].1 = "B";
        alignment.subjects = &wrong;
        assert!(matches!(
            reevaluate_assembly(&before, prepared("after", AFTER, &c), &alignment, &c),
            Err(ReobservationFailure::InvalidCorrespondence(_))
        ));
    }
}
