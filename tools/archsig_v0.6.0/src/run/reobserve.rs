//! 旧評価をメモリ上で生成し、現在の検査済み入力を native 再観測へ渡す。
use super::{Io, Outcome, ReobserveArgs, Signals, evaluate, output, read};
use archsig_common::{
    canonical::{Json, JsonObject},
    control::Control,
    json::{JNode, JValue},
};
use archsig_computation::observed::{
    DeliveryEvaluation, EvaluationFailure, ObservedEvaluation,
    assembly_reobservation::{
        AssemblyCandidateAlignment, CandidateContinuity, MultiAssemblyAlignment,
        ReobservationFailure, reevaluate_assembly_many,
    },
    evaluate_observed, reevaluate_observed,
};
use archsig_input::result::{ResultIssue, Status, exit_code};

fn object<'a>(node: &'a JNode, keys: &[&str]) -> Result<Vec<&'a JNode>, String> {
    let JValue::Obj(fields) = &node.value else {
        return Err("expected an alignment object".into());
    };
    if fields.len() != keys.len() {
        return Err(format!("expected exactly {}", keys.join(", ")));
    }
    keys.iter()
        .map(|key| {
            fields
                .iter()
                .find(|(name, _)| name == key)
                .map(|(_, node)| node)
                .ok_or_else(|| format!("missing alignment field {key}"))
        })
        .collect()
}

fn string(node: &JNode) -> Result<&str, String> {
    match &node.value {
        JValue::Str(value) if !value.is_empty() => Ok(value),
        _ => Err("alignment identifiers must be non-empty strings".into()),
    }
}

fn array(node: &JNode) -> Result<&[JNode], String> {
    match &node.value {
        JValue::Arr(values) => Ok(values),
        _ => Err("expected an alignment array".into()),
    }
}

struct Alignment<'a> {
    before_snapshot: &'a str,
    after_snapshot: &'a str,
    reading: &'a str,
    assembly: &'a str,
    subjects: Vec<(&'a str, &'a str)>,
    candidates: Vec<AssemblyCandidateAlignment<'a>>,
}

impl<'a> Alignment<'a> {
    fn parse(node: &'a JNode) -> Result<Self, String> {
        let fields = object(
            node,
            &[
                "before_snapshot",
                "after_snapshot",
                "reading",
                "assembly",
                "subjects",
                "candidates",
            ],
        )?;
        let subjects = array(fields[4])?
            .iter()
            .map(|row| {
                let [old, new] = array(row)? else {
                    return Err("each subject row must contain before and after IDs".into());
                };
                Ok((string(old)?, string(new)?))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let candidates = array(fields[5])?
            .iter()
            .map(|row| {
                let fields = object(row, &["participant", "previous_candidate", "current_solve"])?;
                Ok(AssemblyCandidateAlignment {
                    participant: string(fields[0])?,
                    previous_candidate: string(fields[1])?,
                    current_solve: string(fields[2])?,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(Self {
            before_snapshot: string(fields[0])?,
            after_snapshot: string(fields[1])?,
            reading: string(fields[2])?,
            assembly: string(fields[3])?,
            subjects,
            candidates,
        })
    }

    fn as_alignment(&self) -> MultiAssemblyAlignment<'_> {
        MultiAssemblyAlignment {
            before_snapshot: self.before_snapshot,
            after_snapshot: self.after_snapshot,
            reading: self.reading,
            assembly: self.assembly,
            subjects: &self.subjects,
            candidates: &self.candidates,
        }
    }
}

fn invalid(signals: &mut dyn Signals, message: String) -> Outcome {
    output::without_result(
        signals,
        Status::Invalid,
        vec![ResultIssue::Usage {
            message,
            argument: "--alignment".into(),
        }],
    )
}

fn result(value: Result<ObservedEvaluation, EvaluationFailure>) -> Option<ObservedEvaluation> {
    match value {
        Ok(evaluation) => Some(evaluation),
        Err(EvaluationFailure::NotImplemented { partial, .. }) => Some(*partial),
        Err(EvaluationFailure::Prepare(_)) => None,
    }
}

pub(super) fn execute(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &ReobserveArgs,
    c: &Control,
) -> Outcome {
    let alignment_bytes = if let Some(path) = &args.alignment {
        let mut issues = Vec::new();
        let Some(bytes) = read(path, &mut issues) else {
            return output::without_result(signals, Status::Error, issues);
        };
        Some(bytes)
    } else {
        None
    };
    let node = match alignment_bytes
        .as_deref()
        .map(archsig_common::json::parse)
        .transpose()
    {
        Ok(node) => node,
        Err(issue) => return invalid(signals, issue.message.clone()),
    };
    let alignment = match node.as_ref().map(Alignment::parse).transpose() {
        Ok(alignment) => alignment,
        Err(message) => return invalid(signals, message),
    };
    let previous = match evaluate::load_requests(signals, &args.previous, c) {
        Ok(prepared) => prepared,
        Err(outcome) => return outcome,
    };
    let current = match evaluate::load_requests(signals, &args.current, c) {
        Ok(prepared) => prepared,
        Err(outcome) => return outcome,
    };
    let Some(previous) = result(evaluate_observed(previous, c)) else {
        return evaluate::run_internal_outcome(signals);
    };
    let mut continuity = None;
    let mut pending = false;
    let current = if c.stop_reason().is_some() || previous.has_internal_issue() {
        None
    } else if let Some(alignment) = alignment {
        match reevaluate_assembly_many(&previous, current, &alignment.as_alignment(), c) {
            Ok(reobserved) => {
                pending = reobserved
                    .candidates()
                    .iter()
                    .any(|candidate| candidate.continuity() == CandidateContinuity::Undetermined);
                continuity = Some(reobserved.continuity_wire());
                Some(reobserved.into_evaluation())
            }
            Err(ReobservationFailure::Stopped(_)) => None,
            Err(ReobservationFailure::InvalidCorrespondence(message)) => {
                return invalid(signals, message);
            }
            Err(ReobservationFailure::Unsupported(message)) => {
                return output::notify(
                    signals,
                    Status::Unsupported,
                    69,
                    c.stop_reason(),
                    vec![Json::obj([
                        ("code", Json::str("unsupported_alignment")),
                        ("message", Json::str(message)),
                    ])],
                );
            }
            Err(ReobservationFailure::Evaluation(failure)) => result(Err(*failure)),
        }
    } else {
        result(reevaluate_observed(&previous, current, c))
    };
    if current.is_none() && !previous.has_internal_issue() && c.stop_reason().is_none() {
        return evaluate::run_internal_outcome(signals);
    }
    let previous: DeliveryEvaluation = previous.into();
    let current = current.map(DeliveryEvaluation::from);
    let stage = current.as_ref().unwrap_or(&previous);
    let mut state = status(stage);
    if state.0 == Status::Complete && pending {
        state = (Status::Partial, 2);
    }
    let frozen = signals.freeze();
    let signal = c.stop_reason().or(frozen);
    let mut issues = stage.failure_notifications();
    if let Some(signal) = signal {
        state = (
            Status::Interrupted,
            exit_code(Status::Interrupted, Some(signal), &[]),
        );
        if !issues.contains(&signal.issue()) {
            issues.push(signal.issue());
        }
    }
    if !previous.has_nodes()
        && !current.as_ref().is_some_and(DeliveryEvaluation::has_nodes)
        && matches!(state.0, Status::Error | Status::Interrupted)
    {
        return Outcome {
            status: state.0,
            exit_code: state.1,
            result: None,
            summary: None,
            issues,
        };
    }
    let mut summary = envelope("archsig.reobservation.summary/1", state, &issues);
    summary.insert("previous".into(), summary_stage(&previous));
    if let Some(current) = &current {
        summary.insert("current".into(), summary_stage(current));
    }
    if let Some(report) = &continuity {
        summary.insert("assembly".into(), report.clone());
    }
    let out = args.current.inputs.out.as_deref();
    let outcome = Outcome {
        status: state.0,
        exit_code: state.1,
        result: out.map(|path| path.join("result.json")),
        summary: Some(Json::Obj(summary)),
        issues,
    };
    let Some(out) = out else {
        return outcome;
    };
    let mut document = envelope("archsig.reobservation/1", state, &outcome.issues);
    let mut files = Vec::new();
    document.insert(
        "previous".into(),
        saved_stage(&previous, "previous", &mut files),
    );
    if let Some(current) = &current {
        document.insert(
            "current".into(),
            saved_stage(current, "current", &mut files),
        );
    }
    if let Some(report) = continuity {
        document.insert("assembly".into(), report);
    }
    if let Some(bytes) = &alignment_bytes {
        document.insert("alignment".into(), Json::str("inputs/alignment.json"));
        files.push(("inputs/alignment.json".into(), bytes));
    }
    let copies = files
        .iter()
        .map(|(name, bytes)| (name.as_str(), *bytes))
        .collect::<Vec<_>>();
    output::publish(io, out, Json::Obj(document), &copies, outcome)
}

fn status(evaluation: &DeliveryEvaluation) -> (Status, u8) {
    match evaluation.status() {
        "complete" => (Status::Complete, u8::from(evaluation.has_refuted_answer())),
        "partial" => (Status::Partial, 2),
        "interrupted" => (Status::Interrupted, 75),
        _ => (Status::Error, 70),
    }
}

fn envelope(format: &str, state: (Status, u8), issues: &[Json]) -> JsonObject {
    JsonObject::from([
        ("format".into(), Json::str(format)),
        ("semantics".into(), Json::str(archsig_input::law::SEMANTICS)),
        ("status".into(), Json::str(state.0.wire())),
        ("exit_code".into(), Json::Nat(u64::from(state.1))),
        ("issues".into(), Json::Arr(issues.to_vec())),
    ])
}

fn summary_stage(evaluation: &DeliveryEvaluation) -> Json {
    let (status, code) = status(evaluation);
    evaluation.summary_wire(status.wire(), code, &evaluation.issues_wire())
}

fn saved_stage<'a>(
    evaluation: &'a DeliveryEvaluation,
    name: &str,
    files: &mut Vec<(String, &'a [u8])>,
) -> Json {
    let inputs = evaluation.prepared().inputs();
    let sources = inputs.sources();
    let mut identities = inputs.inputs().to_vec();
    for identity in &mut identities {
        let (path, bytes) = match identity.id.as_str() {
            "law" => (format!("inputs/{name}.law"), sources.law().bytes()),
            "archmap" => (
                format!("inputs/{name}.archmap.json"),
                sources.archmap().bytes(),
            ),
            id => {
                let index = id
                    .trim_start_matches("definition")
                    .parse::<usize>()
                    .expect("checked definition ID");
                (
                    format!("inputs/definitions/{name}-{index}.json"),
                    sources.definitions()[index].bytes(),
                )
            }
        };
        identity.path = Some(path.clone());
        files.push((path, bytes));
    }
    let mut result = evaluation.result_wire();
    let Json::Obj(wire) = &mut result else {
        unreachable!("evaluation result object")
    };
    wire.insert(
        "inputs".into(),
        Json::Arr(identities.iter().map(|identity| identity.wire()).collect()),
    );
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_common::control::{Checkpoint, Signal};
    use archsig_computation::observed::prepare_observed;
    use archsig_input::input::InputSources;
    use std::{cell::Cell, ffi::OsString, rc::Rc};

    const DEFINITION: &[u8] = include_bytes!("../../tests/fixtures/counter.atoms.json");
    const LAW: &[u8] = include_bytes!("../../tests/fixtures/counter.law");
    const MAP: &[u8] = include_bytes!("../../tests/fixtures/counter.archmap.json");
    const QUESTIONS: [&str; 2] = [
        "stable=evaluate(CountCheck.amount,s=@v/s)",
        "later=evaluate(CountCheck.amount,s=@v/s)",
    ];

    struct Captured;
    impl Signals for Captured {
        fn freeze(&mut self) -> Option<Signal> {
            None
        }
    }

    fn count(asks: &[&str]) -> usize {
        let source =
            InputSources::from_bytes(vec![DEFINITION.to_vec()], LAW.to_vec(), MAP.to_vec());
        let prepared = prepare_observed(source, asks, &Control::unlimited()).unwrap();
        let visits = Rc::new(Cell::new(0));
        let count = visits.clone();
        let c = Control::new(move |point| {
            if point == Checkpoint::Expression {
                count.set(count.get() + 1);
            }
            None
        });
        evaluate_observed(prepared, &c).unwrap();
        visits.get()
    }

    fn stage_status<'a>(summary: &'a Json, stage: &str, index: usize) -> Option<&'a str> {
        let Json::Obj(report) = summary else {
            panic!("summary")
        };
        let Json::Obj(stage) = report.get(stage)? else {
            panic!("stage")
        };
        let Json::Arr(answers) = &stage["answers"] else {
            panic!("answers")
        };
        let Json::Obj(answer) = &answers[index] else {
            panic!("answer")
        };
        let Json::Str(status) = &answer["status"] else {
            panic!("status")
        };
        Some(status)
    }

    #[test]
    fn signals_during_either_evaluation_keep_the_verified_prefix() {
        let dir =
            std::env::temp_dir().join(format!("archsig-reobserve-stages-{}", std::process::id()));
        std::fs::create_dir(&dir).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(dir.clone());
        for (name, bytes) in [("d", DEFINITION), ("l", LAW), ("a", MAP)] {
            std::fs::write(dir.join(name), bytes).unwrap();
        }
        let mut args = vec![OsString::from("reobserve")];
        for (flag, file) in [
            ("--before-atom-definition", "d"),
            ("--before-law", "l"),
            ("--before-archmap", "a"),
            ("--atom-definition", "d"),
            ("--law", "l"),
            ("--archmap", "a"),
        ] {
            args.extend([flag.into(), dir.join(file).into_os_string()]);
        }
        for question in QUESTIONS {
            args.extend([
                "--before-ask".into(),
                question.into(),
                "--ask".into(),
                question.into(),
            ]);
        }
        let first = count(&QUESTIONS[..1]);
        let total = count(&QUESTIONS);
        assert!(0 < first && first < total);
        for (stage, stop) in [("previous", first + 1), ("current", total + first + 1)] {
            for save in [false, true] {
                let mut flags = args.clone();
                if save {
                    flags.extend(["--out".into(), dir.join(stage).into_os_string()]);
                }
                let command = super::super::parse_args(&flags).unwrap();
                let mut visits = 0;
                let control = Control::new(move |point| {
                    if point == Checkpoint::Expression {
                        visits += 1;
                    }
                    (visits == stop).then_some(Signal::Term)
                });
                let result = super::super::execute_command(
                    &command,
                    &mut super::super::FileIo,
                    &mut Captured,
                    &control,
                )
                .unwrap();
                assert_eq!(result.status, Status::Interrupted);
                assert_eq!(result.exit_code, 143);
                assert_eq!(result.result.is_some(), save);
                let summary = result.summary.as_ref().expect("verified prefix");
                assert_eq!(stage_status(summary, "previous", 0), Some("established"));
                assert_eq!(stage_status(summary, stage, 1), Some("undetermined"));
                if stage == "previous" {
                    assert!(stage_status(summary, "current", 0).is_none());
                } else {
                    assert_eq!(stage_status(summary, "previous", 1), Some("established"));
                    assert_eq!(stage_status(summary, "current", 0), Some("established"));
                }
                if let Some(path) = result.result {
                    let document = std::fs::read(path).unwrap();
                    assert!(
                        std::str::from_utf8(&document)
                            .unwrap()
                            .contains("\"status\":\"interrupted\"")
                    );
                }
            }
        }
    }
}
