use super::*;
use crate::run::CheckArgs;
use archsig_common::json::{JNode, JValue};
use archsig_input::result::Signal;
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};
#[derive(Default)]
struct MemoryIo(BTreeMap<PathBuf, Vec<u8>>);
impl Io for MemoryIo {
    fn create_dir(&mut self, _: &Path) -> std::io::Result<()> {
        Ok(())
    }
    fn write(&mut self, p: &Path, b: &[u8]) -> std::io::Result<()> {
        self.0.insert(p.to_owned(), b.to_vec());
        Ok(())
    }
    fn flush(&mut self, _: &Path) -> std::io::Result<()> {
        Ok(())
    }
    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> std::io::Result<()> {
        let old = std::mem::take(&mut self.0);
        for (p, b) in old {
            self.0.insert(to.join(p.strip_prefix(from).unwrap()), b);
        }
        Ok(())
    }
    fn remove_dir_all(&mut self, p: &Path) -> std::io::Result<()> {
        self.0.retain(|k, _| !k.starts_with(p));
        Ok(())
    }
}
struct FinalSignal(Option<Signal>, usize);
impl Signals for FinalSignal {
    fn freeze(&mut self) -> Option<Signal> {
        self.1 += 1;
        self.0.take()
    }
}
fn field<'a>(n: &'a JNode, key: &str) -> &'a JNode {
    let JValue::Obj(fields) = &n.value else {
        panic!("object")
    };
    &fields.iter().find(|(k, _)| k == key).unwrap().1
}
fn array(n: &JNode) -> &[JNode] {
    let JValue::Arr(a) = &n.value else {
        panic!("array")
    };
    a
}
fn text(n: &JNode) -> &str {
    let JValue::Str(s) = &n.value else {
        panic!("string")
    };
    s
}
#[test]
fn later_internal_failure_delivers_only_the_validated_prefix_and_no_empty_error_files() {
    let directory =
        std::env::temp_dir().join(format!("archsig-prefix-delivery-{}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    for prefix in [false, true] {
        for save in [false, true] {
            for signal in [None, Some(Signal::Int)] {
                let sources = InputSources::from_bytes(
                    vec![include_bytes!("../../../tests/fixtures/counter.atoms.json").to_vec()],
                    include_bytes!("../../../tests/fixtures/counter.law").to_vec(),
                    include_bytes!("../../../tests/fixtures/counter.archmap.json").to_vec(),
                );
                let mut asks = vec![];
                if prefix {
                    asks.push("n=evaluate(CountCheck.amount,s=@v/s)");
                }
                asks.extend([
                    "fail=evaluate(CountCheck.amount,s=@v/s)",
                    "later=evaluate(CountCheck.amount,s=@v/s)",
                ]);
                let control = Control::unlimited();
                let prepared = prepare_observed(sources, &asks, &control).unwrap();
                let evaluation =
                    archsig_computation::observed::evaluate_observed_with_rejected_answer(
                        prepared, &control, "fail",
                    )
                    .unwrap();
                assert_eq!(evaluation.status(), "error");
                assert_eq!(!evaluation.has_nodes(), !prefix);
                let output = directory.join(format!("out-{prefix}-{save}"));
                let args = RunArgs {
                    inputs: CheckArgs {
                        atom_definitions: vec![],
                        law: PathBuf::new(),
                        archmap: None,
                        out: save.then_some(output.clone()),
                    },
                    asks: asks.iter().map(|s| (*s).to_owned()).collect(),
                    reuse: None,
                };
                let mut io = MemoryIo::default();
                let mut signals = FinalSignal(signal, 0);
                let outcome = deliver(
                    &mut io,
                    &mut signals,
                    &args,
                    evaluation.into(),
                    super::super::reuse::Verification::default(),
                    &control,
                );
                assert_eq!(
                    (outcome.status, outcome.exit_code),
                    if signal.is_some() {
                        (Status::Interrupted, 130)
                    } else {
                        (Status::Error, 70)
                    }
                );
                assert_eq!(signals.1, 1);
                if !prefix {
                    assert!(outcome.result.is_none());
                    assert!(outcome.summary.is_none());
                    assert!(io.0.is_empty());
                    continue;
                }
                let document = if save {
                    assert_eq!(io.0.len(), 4);
                    assert_eq!(
                        io.0[&output.join("inputs/definitions/0.json")],
                        include_bytes!("../../../tests/fixtures/counter.atoms.json")
                    );
                    archsig_common::json::parse(&io.0[&output.join("result.json")]).unwrap()
                } else {
                    assert!(io.0.is_empty());
                    archsig_common::json::parse(outcome.receipt().as_bytes()).unwrap()
                };
                let answers = array(field(&document, "answers"));
                assert_eq!(text(field(&answers[0], "status")), "established");
                let value = field(field(&answers[0], "outputs"), "value");
                if save {
                    let id = text(field(value, "node"));
                    let n = array(field(&document, "nodes"))
                        .iter()
                        .find(|n| text(field(n, "id")) == id)
                        .unwrap();
                    assert_eq!(text(field(n, "value")), "2");
                } else {
                    assert_eq!(text(field(value, "value")), "2");
                }
                for a in &answers[1..] {
                    let JValue::Obj(outputs) = &field(a, "outputs").value else {
                        panic!()
                    };
                    assert!(outputs.is_empty());
                    assert!(
                        array(field(a, "reasons"))
                            .iter()
                            .all(|r| text(field(r, "code")) == "internal")
                    );
                }
            }
        }
    }
    std::fs::remove_dir(&directory).unwrap();
}

#[test]
fn generated_replay_and_fresh_rendering_deliver_identical_bytes() {
    use super::super::reuse::Verification;
    let directory =
        std::env::temp_dir().join(format!("archsig-replay-delivery-{}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    for save in [false, true] {
        for signal in [None, Some(Signal::Int)] {
            for reuse_stop in [None, Some(Signal::Term)] {
                let args = RunArgs {
                    inputs: CheckArgs {
                        atom_definitions: vec![],
                        law: PathBuf::new(),
                        archmap: None,
                        out: save.then(|| directory.join("out")),
                    },
                    asks: vec!["n=evaluate(CountCheck.amount,s=@v/s)".into()],
                    reuse: None,
                };
                let mut results = Vec::new();
                for keep_replay in [false, true] {
                    let control = Control::unlimited();
                    let prepared = prepare_observed(
                        InputSources::from_bytes(
                            vec![
                                include_bytes!("../../../tests/fixtures/counter.atoms.json")
                                    .to_vec(),
                            ],
                            include_bytes!("../../../tests/fixtures/counter.law").to_vec(),
                            include_bytes!("../../../tests/fixtures/counter.archmap.json").to_vec(),
                        ),
                        &[args.asks[0].as_str()],
                        &control,
                    )
                    .unwrap();
                    let evaluation = evaluate_for_delivery(prepared, &control).unwrap();
                    let replay = keep_replay.then(|| evaluation.result_wire());
                    let verification = Verification {
                        rejected: vec![
                            ResultIssue::Usage {
                                argument: "--reuse".into(),
                                message: "rejected candidate".into(),
                            }
                            .wire(),
                        ],
                        stop: reuse_stop,
                        replay,
                    };
                    let mut io = MemoryIo::default();
                    let mut signals = FinalSignal(signal, 0);
                    let outcome = deliver(
                        &mut io,
                        &mut signals,
                        &args,
                        evaluation,
                        verification,
                        &control,
                    );
                    assert_eq!(signals.1, 1);
                    assert_eq!(
                        outcome.exit_code,
                        if signal.is_some() {
                            130
                        } else if reuse_stop.is_some() {
                            75
                        } else {
                            0
                        }
                    );
                    assert_eq!(io.0.len(), if save { 4 } else { 0 });
                    results.push((outcome.receipt(), io.0));
                }
                assert_eq!(
                    results[0], results[1],
                    "save={save}, signal={signal:?}, reuse_stop={reuse_stop:?}"
                );
            }
        }
    }
    std::fs::remove_dir(&directory).unwrap();
}

#[test]
fn quantified_delivery_keeps_raw_summary_save_reuse_and_final_signal_contracts() {
    let directory =
        std::env::temp_dir().join(format!("archsig-quant-delivery-{}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let atom = r#"{"id": "count", "subject": "s", "field": "Counter.State.count", "value": "2", "origin": "model"}"#;
    let ask = "q=check(CountCheck.quantified,s=@v/s)";
    for (case, (domain, body, missing, expected_code)) in [
        ("set<Z>{0,1,2}", "n <= s.count", false, 0),
        ("set<Z>{0,1,2}", "n >= s.count", false, 1),
        ("set<Z>{0,1,2}", "n <= s.count", true, 2),
        ("set<Z>{0,1,2}", "n >= s.count", true, 2),
        ("set<Bool>{false,true}", "n = n", false, 0),
        ("set<Bool>{false,true}", "n = false", false, 1),
        ("set<Bool>{false,true}", "n = n", true, 0),
        ("set<Bool>{false,true}", "n = false", true, 1),
    ]
    .into_iter()
    .enumerate()
    {
        let law = include_str!("../../../tests/fixtures/counter.law").replace(
            "law required nonnegative", &format!("law required quantified(s: State): forall n in {domain} . {body};\n  law required nonnegative"));
        let original_map = include_str!("../../../tests/fixtures/counter.archmap.json");
        assert_eq!(original_map.matches(atom).count(), 1);
        let map = if missing {
            original_map.replace(atom, "")
        } else {
            original_map.to_owned()
        };
        let sources = || {
            InputSources::from_bytes(
                vec![include_bytes!("../../../tests/fixtures/counter.atoms.json").to_vec()],
                law.as_bytes().to_vec(),
                map.as_bytes().to_vec(),
            )
        };
        let baseline = directory.join(format!("baseline-{case}"));
        let args = |out| RunArgs {
            inputs: CheckArgs {
                atom_definitions: vec![],
                law: PathBuf::new(),
                archmap: None,
                out,
            },
            asks: vec![ask.to_owned()],
            reuse: None,
        };
        let control = Control::unlimited();
        let prepared = prepare_observed(sources(), &[ask], &control).unwrap();
        let raw = archsig_computation::observed::evaluate_observed(prepared, &control).unwrap();
        let mut baseline_io = MemoryIo::default();
        let baseline_outcome = deliver(
            &mut baseline_io,
            &mut FinalSignal(None, 0),
            &args(Some(baseline.clone())),
            raw.into(),
            super::super::reuse::Verification::default(),
            &control,
        );
        assert_eq!(baseline_outcome.exit_code, expected_code);
        std::fs::create_dir(&baseline).unwrap();
        std::fs::write(
            baseline.join("result.json"),
            &baseline_io.0[&baseline.join("result.json")],
        )
        .unwrap();
        for save in [false, true] {
            for signal in [None, Some(Signal::Int)] {
                for reuse in [false, true] {
                    let out = directory.join(format!("out-{case}"));
                    let arguments = args(save.then_some(out.clone()));
                    let mut results = Vec::new();
                    for normal_delivery in [false, true] {
                        let control = Control::unlimited();
                        let prepared = prepare_observed(sources(), &[ask], &control).unwrap();
                        let evaluation = if normal_delivery {
                            evaluate_for_delivery(prepared, &control).unwrap()
                        } else {
                            archsig_computation::observed::evaluate_observed(prepared, &control)
                                .unwrap()
                                .into()
                        };
                        // Compare the current checked semantic projection to a raw
                        // artifact through the existing canonical reuse verifier.
                        // Internal node numbering/sharing is not a public identity.
                        let verification = if reuse {
                            let checked = super::super::reuse::inspect(Some(&baseline), &control)
                                .unwrap()
                                .verify(&evaluation, &control);
                            assert!(
                                checked.rejected.is_empty(),
                                "{body}, missing={missing}, normal={normal_delivery}: {:?}",
                                checked.rejected
                            );
                            assert!(checked.stop.is_none());
                            checked
                        } else {
                            super::super::reuse::Verification::default()
                        };
                        let mut io = MemoryIo::default();
                        let mut signals = FinalSignal(signal, 0);
                        let outcome = deliver(
                            &mut io,
                            &mut signals,
                            &arguments,
                            evaluation,
                            verification,
                            &control,
                        );
                        assert_eq!(signals.1, 1);
                        let result_path = out.join("result.json");
                        let copies: BTreeMap<_, _> =
                            io.0.into_iter()
                                .filter(|(path, _)| path != &result_path)
                                .collect();
                        results.push((
                            outcome.status,
                            outcome.exit_code,
                            outcome.result,
                            outcome.issues,
                            outcome.summary,
                            copies,
                        ));
                    }
                    assert_eq!(
                        results[0], results[1],
                        "{body}, missing={missing}, save={save}, signal={signal:?}, reuse={reuse}"
                    );
                }
            }
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
