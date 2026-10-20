//! 観測計画の独立したslot・依存・理由の期待値。
mod common;
use archsig::json::{JNode, JValue};
use common::cli::*;
use std::path::{Path, PathBuf};
const D: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const L: &str = include_str!("fixtures/counter.law");
const A: &str = include_str!("fixtures/counter.archmap.json");
fn setup(name: &str, missing: bool) -> PathBuf {
    let dir = workdir(name);
    let law = L.replace("view amount(s: State): Z = s.count;", "view amount(s: State): Z = s.count;\n view echo(z: Z): Z = z;\n view no(): Bool = false;\n law optional inactive(s: State) when false: s.count >= 0;");
    let map = if missing {
        A.replace("{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}", "")
    } else {
        A.into()
    };
    for (name, bytes) in [
        ("d.json", D),
        ("l.law", law.as_bytes()),
        ("a.json", map.as_bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
fn execute(dir: &Path, out: &str, reuse: Option<&str>, asks: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        out,
    ];
    if let Some(reuse) = reuse {
        args.extend(["--reuse", reuse]);
    }
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    run(dir, &args)
}
fn answer<'a>(result: &'a JNode, id: &str) -> &'a JNode {
    arr(get(result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn node<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn plan<'a>(result: &'a JNode, id: &str) -> &'a JNode {
    let answer = answer(result, id);
    assert_eq!(s(get(answer, "status")), "established");
    assert!(arr(get(answer, "reasons")).is_empty());
    let node = node(result, get(get(answer, "outputs"), "plan"));
    assert_eq!(s(get(node, "type")), "ObservationPlan");
    assert_eq!(s(get(get(node, "rule"), "name")), "observation_plan");
    get(node, "value")
}
#[test]
fn missing_slot_survives_backward_and_nested_needed_without_duplicate_requirements() {
    let dir = setup("needed-missing", true);
    let asks = [
        "p=needed($x)",
        "nested=needed($p)",
        "x=evaluate(CountCheck.echo,z=$n.value)",
        "n=evaluate(CountCheck.amount,s=@v/s)",
    ];
    let run = execute(&dir, "out", None, &asks);
    assert_eq!(run.code, 2, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(
        arr(get(&result, "answers"))
            .iter()
            .map(|a| s(get(a, "id")))
            .collect::<Vec<_>>(),
        ["p", "nested", "x", "n"]
    );
    for id in ["p", "nested"] {
        let p = plan(&result, id);
        let requirements = arr(get(p, "requirements"));
        assert_eq!(requirements.len(), 1);
        let field = get(&requirements[0], "field");
        assert_eq!(s(get(field, "snapshot")), "v");
        assert_eq!(s(get(field, "subject")), "s");
        assert_eq!(s(get(field, "field")), "Counter.State.count");
        assert!(!has(field, "atom"));
        assert!(!arr(get(&requirements[0], "dependents")).is_empty());
        for reference in arr(get(&requirements[0], "dependents")) {
            node(&result, reference);
        }
        assert!(
            arr(get(&requirements[0], "locations"))
                .iter()
                .any(|l| s(get(l, "input")) == "law")
        );
        assert!(
            arr(get(p, "blockers"))
                .iter()
                .any(|r| s(get(r, "code")) == "dependency_blocked"
                    && s(get(get(r, "details"), "request")) == "n")
        );
    }
    let old = std::fs::read(dir.join("out/result.json")).unwrap();
    let reused = execute(&dir, "reused", Some("out"), &asks);
    assert_eq!(reused.code, 2, "{}", reused.stdout);
    let replay = result_json(&dir, &reused);
    assert_eq!(get(&result, "nodes"), get(&replay, "nodes"));
    assert!(arr(get(get(&replay, "reuse"), "rejected")).is_empty());
    assert_eq!(std::fs::read(dir.join("out/result.json")).unwrap(), old);
}
#[test]
fn established_false_refuted_and_inapplicable_results_need_no_invented_slots() {
    let dir = setup("needed-complete", false);
    let map = A.replace("\"value\": \"2\"", "\"value\": \"12\"");
    std::fs::write(dir.join("a.json"), map).unwrap();
    let asks = [
        "n=evaluate(CountCheck.amount,s=@v/s)",
        "f=evaluate(CountCheck.no)",
        "c=check(CountAudit.bounded,s=@v/s)",
        "i=check(CountCheck.inactive,s=@v/s)",
        "pn=needed($n)",
        "pf=needed($f)",
        "pc=needed($c)",
        "pi=needed($i)",
    ];
    let run = execute(&dir, "out", None, &asks);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(answer(&result, "c"), "status")), "refuted");
    for id in ["pn", "pf", "pc", "pi"] {
        let p = plan(&result, id);
        assert!(arr(get(p, "requirements")).is_empty());
        assert!(arr(get(p, "blockers")).is_empty());
    }
}

#[test]
fn needed_preserves_algorithm_blockers_and_excludes_unrelated_missing_requests() {
    let dir = setup("needed-blockers", false);
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap().replace(
        "view no()",
        "view unknown(): Bool = forall text: Text. text=text;\n view no()",
    );
    std::fs::write(dir.join("l.law"), law).unwrap();
    let map = A.replace(
        "\"subjects\": [",
        "\"subjects\": [{\"id\":\"other\",\"type\":\"Counter.State\",\"origin\":\"model\"},",
    );
    std::fs::write(dir.join("a.json"), map).unwrap();
    let asks = [
        "u=evaluate(CountCheck.unknown)",
        "missing=evaluate(CountCheck.amount,s=@v/other)",
        "p=needed($u)",
        "n=evaluate(CountCheck.amount,s=@v/s)",
        "pn=needed($n)",
    ];
    let run = execute(&dir, "out", None, &asks);
    assert_eq!(run.code, 2, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let p = plan(&result, "p");
    assert!(arr(get(p, "requirements")).is_empty());
    let blockers = arr(get(p, "blockers"));
    assert!(
        blockers
            .iter()
            .any(|r| s(get(r, "code")) == "unsupported_algorithm")
    );
    for original in arr(get(answer(&result, "u"), "reasons")) {
        assert!(
            blockers.contains(original),
            "元の未決理由をdetails/位置/依存ごと保持する"
        );
    }
    assert!(arr(get(plan(&result, "pn"), "requirements")).is_empty());
    assert!(arr(get(plan(&result, "pn"), "blockers")).is_empty());
}

#[test]
fn invalid_needed_references_arguments_cycles_and_plan_projections_are_usage_without_files() {
    let cases: &[&[&str]] = &[
        &["p=needed($missing)"],
        &["p=needed(@v/s)"],
        &["p=needed(CountCheck.amount)"],
        &["n=evaluate(CountCheck.amount,s=@v/s)", "p=needed($n.value)"],
        &[
            "n=evaluate(CountCheck.amount,s=@v/s)",
            "p=needed($n,on=@v/s)",
        ],
        &["p=needed($p)"],
        &["p=needed($q)", "q=needed($p)"],
        &[
            "n=evaluate(CountCheck.amount,s=@v/s)",
            "p=needed($n)",
            "p=needed($n)",
        ],
        &[
            "n=evaluate(CountCheck.amount,s=@v/s)",
            "p=needed($n)",
            "x=evaluate(CountCheck.echo,z=$p.plan)",
        ],
    ];
    for (index, asks) in cases.iter().enumerate() {
        let dir = setup(&format!("needed-usage-{index}"), false);
        let run = execute(&dir, "out", None, asks);
        let receipt = notified(&dir, &run, "invalid", 64);
        assert!(
            arr(get(&receipt, "issues"))
                .iter()
                .all(|r| !s(get(r, "message")).is_empty())
        );
        if index == 6 {
            assert!(run.stdout.contains("p -> q") && run.stdout.contains("q -> p"));
        }
    }
}

#[test]
fn reuse_recomputes_current_missing_subject_and_preserves_existing_output() {
    let dir = setup("needed-current-reuse", true);
    let oldasks = ["n=evaluate(CountCheck.amount,s=@v/s)", "p=needed($n)"];
    let old = execute(&dir, "previous", None, &oldasks);
    assert_eq!(old.code, 2, "{}", old.stdout);
    let bytes = std::fs::read(dir.join("previous/result.json")).unwrap();
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace("\"s\"", "\"t\"")
        .replace("\"model\"", "\"current-source\"");
    std::fs::write(dir.join("a.json"), &map).unwrap();
    let asks = ["n=evaluate(CountCheck.amount,s=@v/t)", "p=needed($n)"];
    let plain = execute(&dir, "plain", None, &asks);
    let reused = execute(&dir, "reused", Some("previous"), &asks);
    assert_eq!(plain.code, 2);
    assert_eq!(reused.code, 2, "{}", reused.stdout);
    let plain = result_json(&dir, &plain);
    let result = result_json(&dir, &reused);
    for name in ["inputs", "requests", "answers", "nodes", "issues"] {
        assert_eq!(get(&plain, name), get(&result, name));
    }
    let requirements = arr(get(plan(&result, "p"), "requirements"));
    assert_eq!(requirements.len(), 1);
    assert_eq!(s(get(get(&requirements[0], "field"), "subject")), "t");
    assert_eq!(
        std::fs::read(dir.join("reused/inputs/archmap.json")).unwrap(),
        map.as_bytes()
    );
    assert_eq!(
        std::fs::read(dir.join("previous/result.json")).unwrap(),
        bytes
    );
    assert!(!arr(get(get(&result, "reuse"), "rejected")).is_empty());
    let rejected = execute(&dir, "previous", Some("previous"), &asks);
    assert_eq!(rejected.code, 64);
    assert_eq!(
        std::fs::read(dir.join("previous/result.json")).unwrap(),
        bytes
    );
}

struct TestIo;
impl archsig::run::Io for TestIo {
    fn create_dir(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::create_dir(p)
    }
    fn write(&mut self, p: &Path, b: &[u8]) -> std::io::Result<()> {
        std::fs::write(p, b)
    }
    fn flush(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::File::open(p)?.sync_all()
    }
    fn rename_noreplace(&mut self, a: &Path, b: &Path) -> std::io::Result<()> {
        rustix::fs::renameat_with(
            rustix::fs::CWD,
            a,
            rustix::fs::CWD,
            b,
            rustix::fs::RenameFlags::NOREPLACE,
        )
        .map_err(std::io::Error::from)
    }
    fn remove_dir_all(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::remove_dir_all(p)
    }
}
#[derive(Default)]
struct NoSignal(usize);
impl archsig::run::Signals for NoSignal {
    fn freeze(&mut self) -> Option<archsig::result::Signal> {
        self.0 += 1;
        None
    }
}
fn args(dir: &Path) -> archsig::run::RunArgs {
    archsig::run::RunArgs {
        inputs: archsig::run::CheckArgs {
            atom_definitions: vec![dir.join("d.json")],
            law: dir.join("l.law"),
            archmap: Some(dir.join("a.json")),
            out: dir.join("out"),
        },
        asks: vec![
            "n=evaluate(CountCheck.amount,s=@v/s)".into(),
            "p=needed($n)".into(),
        ],
        reuse: None,
        time_ms: None,
        memory_mib: None,
    }
}
#[test]
fn plan_checkpoint_stops_retain_values_and_publish_only_completed_plans() {
    use archsig::observed::control::{Checkpoint, Control, Limits, Usage};
    use archsig::result::Signal;
    use std::{cell::Cell, rc::Rc, time::Instant};
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut probe = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::ObservationPlan {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let dir = setup("needed-probe", false);
    let result = archsig::run::run_requests(
        &mut TestIo,
        &mut NoSignal::default(),
        &args(&dir),
        Instant::now(),
        &mut probe,
    );
    assert_eq!(result.exit_code, 0);
    let total = count.get();
    assert!(total > 5);
    for at in [1, total / 2, total] {
        for mode in 0..4 {
            let dir = setup(&format!("needed-stop-{at}-{mode}"), false);
            let count = Rc::new(Cell::new(0usize));
            let seen = count.clone();
            let mut control = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |point| {
                    if point == Checkpoint::ObservationPlan {
                        seen.set(seen.get() + 1);
                    }
                    let stopped = seen.get() >= at;
                    Usage {
                        elapsed_ms: if stopped && mode == 0 { 1 } else { 0 },
                        memory_mib: if stopped && mode == 1 { 1 } else { 0 },
                        signal: if stopped {
                            match mode {
                                2 => Some(Signal::Int),
                                3 => Some(Signal::Term),
                                _ => None,
                            }
                        } else {
                            None
                        },
                    }
                },
            );
            let mut options = args(&dir);
            options.time_ms = (mode == 0).then(|| "1".into());
            options.memory_mib = (mode == 1).then(|| "1".into());
            let mut signals = NoSignal::default();
            let outcome = archsig::run::run_requests(
                &mut TestIo,
                &mut signals,
                &options,
                Instant::now(),
                &mut control,
            );
            let code = match mode {
                2 => 130,
                3 => 143,
                _ => 75,
            };
            assert_eq!(outcome.exit_code, code, "{at}/{mode}");
            assert_eq!(signals.0, 1);
            assert_eq!(count.get(), at, "停止後probeなし");
            let result =
                archsig::json::parse(&std::fs::read(dir.join("out/result.json")).unwrap()).unwrap();
            assert_eq!(num(get(&result, "exit_code")), code as u64);
            assert_eq!(s(get(&result, "status")), "interrupted");
            assert_eq!(
                s(get(
                    node(&result, get(get(answer(&result, "n"), "outputs"), "value")),
                    "value"
                )),
                "2"
            );
            if at == total {
                assert!(arr(get(plan(&result, "p"), "requirements")).is_empty());
            } else {
                assert!(!has(get(answer(&result, "p"), "outputs"), "plan"));
                assert!(
                    arr(get(&result, "nodes"))
                        .iter()
                        .all(|n| get(n, "type").value != JValue::Str("ObservationPlan".into()))
                );
            }
            assert!(std::fs::read_dir(&dir).unwrap().all(|e| {
                !e.unwrap()
                    .file_name()
                    .to_string_lossy()
                    .contains(".archsig-")
            }));
        }
    }
}
