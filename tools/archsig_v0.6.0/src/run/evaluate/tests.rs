use super::*;
use crate::json::{JNode, JValue};
use crate::run::CheckArgs;
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
                let mut control = Control::new(Default::default(), |_| Default::default());
                let prepared = prepare_observed(sources, &asks, &mut control).unwrap();
                let evaluation = crate::observed::evaluate_observed_with_rejected_answer(
                    prepared,
                    &mut control,
                    "fail",
                )
                .unwrap();
                assert_eq!(evaluation.status(), "error");
                assert_eq!(evaluation.nodes.is_empty(), !prefix);
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
                    time_ms: None,
                    memory_mib: None,
                };
                let mut io = MemoryIo::default();
                let mut signals = FinalSignal(signal, 0);
                let outcome = deliver(
                    &mut io,
                    &mut signals,
                    &args,
                    evaluation,
                    vec![],
                    None,
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
                    crate::json::parse(&io.0[&output.join("result.json")]).unwrap()
                } else {
                    assert!(io.0.is_empty());
                    crate::json::parse(outcome.receipt().as_bytes()).unwrap()
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
