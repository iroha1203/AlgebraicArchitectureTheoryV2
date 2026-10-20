//! run の実バイナリと、本文から独立したCounter入力・期待値。
mod common;
use archsig::json::{JNode, JValue};
use common::cli::*;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
const D: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const L: &str = include_str!("fixtures/counter.law");
const A: &str = include_str!("fixtures/counter.archmap.json");
const ASKS: [&str; 3] = [
    "n=evaluate(CountCheck.amount,s=@v/s)",
    "ok=check(CountCheck.nonnegative,s=@v/s)",
    "audit=check(CountAudit.bounded,s=@v/s)",
];

fn inputs(name: &str, count: Option<&str>, law: &str) -> PathBuf {
    let dir = workdir(name);
    std::fs::write(dir.join("d.json"), D).unwrap();
    std::fs::write(dir.join("l.law"), law).unwrap();
    let map = match count {
        Some(n) => A.replace("\"value\": \"2\"", &format!("\"value\": \"{n}\"")),
        None => A.replace("{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}", ""),
    };
    std::fs::write(dir.join("a.json"), map).unwrap();
    dir
}
fn requests(dir: &Path, asks: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "out",
    ];
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    run(dir, &args)
}
fn answer<'a>(res: &'a JNode, id: &str) -> &'a JNode {
    arr(get(res, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn node<'a>(res: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(res, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn result(dir: &Path, run: &Run, status: &str, code: i32) -> JNode {
    assert_eq!(run.code, code, "{}", run.stdout);
    assert_eq!(s(get(&run.receipt, "status")), status);
    assert_eq!(num(get(&run.receipt, "exit_code")), code as u64);
    let res = result_json(dir, run);
    assert_eq!(s(get(&res, "format")), "archsig.result/2");
    assert_eq!(s(get(&res, "semantics")), "archsig/0.6.0");
    assert_eq!(s(get(&res, "command")), "run");
    assert_eq!(s(get(&res, "status")), status);
    assert_eq!(num(get(&res, "exit_code")), code as u64);
    let JValue::Obj(fields) = &res.value else {
        panic!("object")
    };
    let names: BTreeSet<_> = fields.iter().map(|(k, _)| k.as_str()).collect();
    assert_eq!(
        names,
        [
            "format",
            "semantics",
            "producer",
            "command",
            "status",
            "exit_code",
            "inputs",
            "declarations",
            "vocabularies",
            "requests",
            "answers",
            "nodes",
            "issues",
            "reuse",
            "usage",
            "limits"
        ]
        .into_iter()
        .collect()
    );
    assert_eq!(
        std::fs::read(dir.join("out/inputs/definitions/0.json")).unwrap(),
        D
    );
    for (src, dst) in [
        ("l.law", "inputs/law.law"),
        ("a.json", "inputs/archmap.json"),
    ] {
        assert_eq!(
            std::fs::read(dir.join(src)).unwrap(),
            std::fs::read(dir.join("out").join(dst)).unwrap()
        );
    }
    for i in arr(get(&res, "inputs")) {
        let bytes = std::fs::read(dir.join("out").join(s(get(i, "path")))).unwrap();
        assert_eq!(
            s(get(i, "bytes_digest")),
            archsig::canonical::sha256_digest(&bytes)
        );
    }
    let mut prior = BTreeSet::new();
    for n in arr(get(&res, "nodes")) {
        for refs in ["arguments", "conditions", "evidence"] {
            for r in arr(get(n, refs)) {
                assert!(prior.contains(s(get(r, "node"))), "DAGの先行node: {refs}");
            }
        }
        assert!(prior.insert(s(get(n, "id"))));
        for key in ["rule", "scope", "support", "reasons", "type", "state"] {
            get(n, key);
        }
    }
    res
}

#[test]
fn counter_value_refutation_and_missing_are_results() {
    for (name, count, status, code, decisions) in [
        (
            "two",
            Some("2"),
            "complete",
            0,
            ["established", "established", "established"],
        ),
        (
            "twelve",
            Some("12"),
            "complete",
            1,
            ["established", "established", "refuted"],
        ),
        (
            "absent",
            None,
            "partial",
            2,
            ["undetermined", "undetermined", "undetermined"],
        ),
    ] {
        let dir = inputs(name, count, L);
        let r = requests(&dir, &ASKS);
        let res = result(&dir, &r, status, code);
        assert_eq!(arr(get(&res, "requests")).len(), 3);
        assert_eq!(
            arr(get(&res, "answers"))
                .iter()
                .map(|a| s(get(a, "id")))
                .collect::<Vec<_>>(),
            ["n", "ok", "audit"]
        );
        for (id, decision) in ["n", "ok", "audit"].into_iter().zip(decisions) {
            assert_eq!(s(get(answer(&res, id), "status")), decision);
        }
        if let Some(count) = count {
            let n = node(&res, get(get(answer(&res, "n"), "outputs"), "value"));
            assert_eq!(s(get(n, "type")), "Z");
            assert_eq!(s(get(n, "value")), count);
            assert!(!arr(get(n, "support")).is_empty());
            assert!(!has(&r.receipt, "issues"));
        } else {
            for a in arr(get(&res, "answers")) {
                let missing: Vec<_> = arr(get(a, "reasons"))
                    .iter()
                    .filter(|i| s(get(i, "code")) == "missing_observation")
                    .collect();
                assert!(!missing.is_empty());
                assert!(
                    missing
                        .iter()
                        .flat_map(|i| arr(get(i, "missing")))
                        .any(|p| s(get(p, "snapshot")) == "v"
                            && s(get(p, "subject")) == "s"
                            && s(get(p, "field")) == "Counter.State.count")
                );
            }
        }
    }
}

#[test]
fn false_value_and_guarded_inapplicability_are_distinct() {
    let law=L.replace("view amount", "view negative(s: State): Bool = s.count < 0;\n  law required negativeLaw(s: State): s.count < 0;\n  law required guarded(s: State) when false: s.count < 0;\n  view amount");
    let dir = inputs("bool-guard", Some("2"), &law);
    let r = requests(
        &dir,
        &[
            "v=evaluate(CountCheck.negative,s=@v/s)",
            "f=check(CountCheck.negativeLaw,s=@v/s)",
            "g=check(CountCheck.guarded,s=@v/s)",
        ],
    );
    let res = result(&dir, &r, "complete", 1);
    assert_eq!(s(get(answer(&res, "f"), "status")), "refuted");
    let value = node(&res, get(get(answer(&res, "v"), "outputs"), "value"));
    assert_eq!(s(get(value, "type")), "Bool");
    assert!(matches!(get(value, "value").value, JValue::Bool(false)));
    assert_eq!(s(get(answer(&res, "v"), "status")), "established");
    let guard = node(&res, get(get(answer(&res, "g"), "outputs"), "evaluation"));
    assert_eq!(
        s(get(get(guard, "value"), "applicability")),
        "not_applicable"
    );
    assert_eq!(s(get(answer(&res, "g"), "status")), "established");
}

#[test]
fn backward_references_keep_answer_order_and_cycles_explain_edges() {
    let law = L.replace("view amount", "view relay(x: Z): Z = x;\n  view amount");
    let dir = inputs("backward", Some("2"), &law);
    let r = requests(
        &dir,
        &["later=evaluate(CountCheck.relay,x=$n.value)", ASKS[0]],
    );
    let res = result(&dir, &r, "complete", 0);
    assert_eq!(
        arr(get(&res, "answers"))
            .iter()
            .map(|a| s(get(a, "id")))
            .collect::<Vec<_>>(),
        ["later", "n"]
    );
    assert_eq!(
        s(get(
            node(&res, get(get(answer(&res, "later"), "outputs"), "value")),
            "value"
        )),
        "2"
    );
    let dir = inputs("cycle", Some("2"), &law);
    let r = requests(
        &dir,
        &[
            "a=evaluate(CountCheck.relay,x=$b.value)",
            "b=evaluate(CountCheck.relay,x=$a.value)",
        ],
    );
    let res = notified(&dir, &r, "invalid", 64);
    let issues = arr(get(&res, "issues"));
    assert_eq!(issues.len(), 2);
    for issue in issues {
        assert_eq!(s(get(issue, "code")), "cycle");
        let id = s(get(issue, "request"));
        assert!(matches!(id, "a" | "b"));
        let message = s(get(issue, "message"));
        assert!(message.contains("a") && message.contains("b") && message.contains(" -> "));
        assert!(!has(issue, "location"));
    }
}

#[test]
fn invalid_run_requests_report_usage_without_files() {
    for (name, asks) in [
        ("duplicate", vec![ASKS[0], ASKS[0]]),
        ("unknown", vec!["n=evaluate(CountCheck.unknown,s=@v/s)"]),
        (
            "projection",
            vec![ASKS[0], "x=evaluate(CountCheck.amount,s=$n.value.witness)"],
        ),
        (
            "unknownid",
            vec!["x=evaluate(CountCheck.amount,s=$unknown.value)"],
        ),
    ] {
        let dir = inputs(name, Some("2"), L);
        let r = requests(&dir, &asks);
        let receipt = notified(&dir, &r, "invalid", 64);
        assert!(
            arr(get(&receipt, "issues"))
                .iter()
                .all(|i| s(get(i, "code")) == "usage")
        );
    }
}

#[test]
fn run_flags_validate_budgets_and_preserve_unbounded_decimal_limits() {
    for (index, n) in ["0", "01", "+1", "-1", "1.0", "1e2", "", " 1"]
        .into_iter()
        .enumerate()
    {
        let dir = inputs(&format!("budget-grammar-{index}"), Some("2"), L);
        let r = run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--ask",
                ASKS[0],
                "--out",
                "out",
                "--time-ms",
                n,
            ],
        );
        let receipt = notified(&dir, &r, "invalid", 64);
        assert_eq!(
            s(get(
                get(&arr(get(&receipt, "issues"))[0], "details"),
                "argument"
            )),
            "--time-ms"
        );
    }
    let dir = inputs("large-budget", Some("2"), L);
    let n = "9999999999999999999999999999999999999999999999999999999999999999999";
    let r = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            ASKS[0],
            "--out",
            "out",
            "--time-ms",
            n,
            "--memory-mib",
            n,
        ],
    );
    let res = result(&dir, &r, "complete", 0);
    assert_eq!(s(get(get(&res, "limits"), "time_ms")), n);
    assert_eq!(s(get(get(&res, "limits"), "memory_mib")), n);
}

#[test]
fn run_argument_and_input_failures_never_create_failure_files() {
    for (name, extra, expected) in [
        ("duplicate-out", vec!["--out", "other"], "--out"),
        ("duplicate-law", vec!["--law", "other"], "--law"),
        ("unknown-flag", vec!["--bogus"], "--bogus"),
        ("positional", vec!["extra"], "extra"),
        ("missing-value", vec!["--memory-mib"], "--memory-mib"),
    ] {
        let dir = inputs(name, Some("2"), L);
        let mut args = vec![
            "run",
            "--atom-definition",
            "missing.json",
            "--law",
            "missing.law",
            "--archmap",
            "missing-map.json",
            "--ask",
            ASKS[0],
            "--out",
            "out",
        ];
        args.extend(extra);
        let r = run(&dir, &args);
        let receipt = notified(&dir, &r, "invalid", 64);
        assert_eq!(
            s(get(
                get(&arr(get(&receipt, "issues"))[0], "details"),
                "argument"
            )),
            expected
        );
    }
    for (name, definition, law, map, code, status, issue) in [
        (
            "bad-definition",
            b"invalid".as_slice(),
            L.as_bytes(),
            A.as_bytes(),
            65,
            "invalid",
            "syntax",
        ),
        (
            "bad-law",
            D,
            b"invalid law".as_slice(),
            A.as_bytes(),
            65,
            "invalid",
            "syntax",
        ),
        (
            "future-map",
            D,
            L.as_bytes(),
            b"{\"format\":\"archsig.future/9\",\"semantics\":\"archsig/0.6.0\"}".as_slice(),
            69,
            "unsupported",
            "unsupported_version",
        ),
    ] {
        let dir = inputs(name, Some("2"), L);
        for (file, bytes) in [("d.json", definition), ("l.law", law), ("a.json", map)] {
            std::fs::write(dir.join(file), bytes).unwrap();
        }
        let r = requests(&dir, &ASKS);
        let receipt = notified(&dir, &r, status, code);
        assert_eq!(s(get(&arr(get(&receipt, "issues"))[0], "code")), issue);
    }
    let dir = inputs("run-read-error", Some("2"), L);
    std::fs::remove_file(dir.join("l.law")).unwrap();
    let r = requests(&dir, &ASKS);
    let receipt = notified(&dir, &r, "error", 74);
    assert_eq!(
        s(get(
            get(&arr(get(&receipt, "issues"))[0], "details"),
            "path"
        )),
        "l.law"
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
struct NoSignal {
    freezes: usize,
}
impl archsig::run::Signals for NoSignal {
    fn freeze(&mut self) -> Option<archsig::result::Signal> {
        self.freezes += 1;
        None
    }
}
fn run_args(dir: &Path) -> archsig::run::RunArgs {
    archsig::run::RunArgs {
        inputs: archsig::run::CheckArgs {
            atom_definitions: vec![dir.join("d.json")],
            law: dir.join("l.law"),
            archmap: Some(dir.join("a.json")),
            out: dir.join("out"),
        },
        asks: ASKS.iter().map(|s| s.to_string()).collect(),
        reuse: None,
        time_ms: Some("1".into()),
        memory_mib: None,
    }
}

#[test]
fn run_stops_preserve_verified_values_and_refutations_and_skip_empty_artifacts() {
    use archsig::observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    };
    use std::{cell::Cell, rc::Rc, time::Instant};
    let map = A.replace("\"value\": \"2\"", "\"value\": \"12\"");
    let count = Rc::new(Cell::new(0usize));
    let seen = Rc::clone(&count);
    let mut probe = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let first = [ASKS[0], ASKS[2]];
    evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![D.to_vec()],
            L.as_bytes().to_vec(),
            map.as_bytes().to_vec(),
        ),
        &first,
        &mut probe,
    )
    .unwrap();
    let before = count.get();
    assert!(before > 0);
    let seen = Rc::new(Cell::new(0usize));
    let observed = Rc::clone(&seen);
    let mut control = Control::new(
        Limits {
            time_ms: Some(1),
            memory_mib: None,
        },
        move |point| {
            if point == Checkpoint::Expression {
                observed.set(observed.get() + 1);
            }
            Usage {
                elapsed_ms: u128::from(observed.get() > before),
                ..Usage::default()
            }
        },
    );
    let dir = inputs("partial-run", Some("12"), L);
    let mut args = run_args(&dir);
    args.asks = [ASKS[0], ASKS[2], ASKS[1]]
        .iter()
        .map(|s| s.to_string())
        .collect();
    let mut signals = NoSignal::default();
    let outcome = archsig::run::run_requests(
        &mut TestIo,
        &mut signals,
        &args,
        Instant::now(),
        &mut control,
    );
    assert_eq!(outcome.exit_code, 75);
    assert_eq!(signals.freezes, 1);
    let res = archsig::json::parse(&std::fs::read(dir.join("out/result.json")).unwrap()).unwrap();
    assert_eq!(s(get(answer(&res, "n"), "status")), "established");
    assert_eq!(
        s(get(
            node(&res, get(get(answer(&res, "n"), "outputs"), "value")),
            "value"
        )),
        "12"
    );
    assert_eq!(s(get(answer(&res, "audit"), "status")), "refuted");
    assert_eq!(s(get(answer(&res, "ok"), "status")), "undetermined");
    assert!(
        arr(get(&res, "issues"))
            .iter()
            .any(|i| s(get(i, "code")) == "budget_exhausted")
    );
    let dir = inputs("empty-run-stop", Some("2"), L);
    let args = run_args(&dir);
    let mut control = Control::new(
        Limits {
            time_ms: Some(1),
            memory_mib: None,
        },
        |point| Usage {
            elapsed_ms: u128::from(point == Checkpoint::BeforeDefinitions),
            ..Usage::default()
        },
    );
    let outcome = archsig::run::run_requests(
        &mut TestIo,
        &mut NoSignal::default(),
        &args,
        Instant::now(),
        &mut control,
    );
    assert_eq!(outcome.exit_code, 75);
    assert!(outcome.result.is_none());
    assert!(!dir.join("out").exists());
    let receipt = archsig::json::parse(outcome.receipt().as_bytes()).unwrap();
    assert!(!arr(get(&receipt, "issues")).is_empty());
}

#[test]
fn repeated_definitions_and_required_run_flags_are_checked() {
    let dir = inputs("run-multiple-definitions", Some("2"), L);
    std::fs::write(
        dir.join("extras.json"),
        include_bytes!("fixtures/extras.atoms.json"),
    )
    .unwrap();
    let r = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--atom-definition",
            "extras.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            "out",
            "--ask",
            ASKS[0],
        ],
    );
    let res = result(&dir, &r, "complete", 0);
    assert_eq!(arr(get(&res, "inputs")).len(), 4);
    assert_eq!(
        std::fs::read(dir.join("out/inputs/definitions/1.json")).unwrap(),
        include_bytes!("fixtures/extras.atoms.json")
    );
    for (missing, argument) in [
        ("definition", "--atom-definition"),
        ("law", "--law"),
        ("archmap", "--archmap"),
        ("ask", "--ask"),
        ("out", "--out"),
    ] {
        let dir = inputs(&format!("run-missing-{missing}"), Some("2"), L);
        let mut args = vec!["run"];
        for (kind, flag, value) in [
            ("definition", "--atom-definition", "d.json"),
            ("law", "--law", "l.law"),
            ("archmap", "--archmap", "a.json"),
            ("ask", "--ask", ASKS[0]),
            ("out", "--out", "out"),
        ] {
            if missing != kind {
                args.extend([flag, value]);
            }
        }
        let r = run(&dir, &args);
        let receipt = notified(&dir, &r, "invalid", 64);
        assert_eq!(
            s(get(
                get(&arr(get(&receipt, "issues"))[0], "details"),
                "argument"
            )),
            argument
        );
    }
}

struct WriteFailure;
impl archsig::run::Io for WriteFailure {
    fn create_dir(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::create_dir(p)
    }
    fn write(&mut self, p: &Path, b: &[u8]) -> std::io::Result<()> {
        if p.ends_with("result.json") {
            Err(std::io::ErrorKind::PermissionDenied.into())
        } else {
            std::fs::write(p, b)
        }
    }
    fn flush(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::File::open(p)?.sync_all()
    }
    fn rename_noreplace(&mut self, a: &Path, b: &Path) -> std::io::Result<()> {
        TestIo.rename_noreplace(a, b)
    }
    fn remove_dir_all(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::remove_dir_all(p)
    }
}

#[test]
fn run_delivery_failure_cleans_only_its_temp_and_existing_out_is_protected() {
    let dir = inputs("run-write-failure", Some("2"), L);
    std::fs::create_dir(dir.join("existing")).unwrap();
    std::fs::write(dir.join("existing/keep"), b"keep").unwrap();
    let mut args = run_args(&dir);
    args.time_ms = None;
    let outcome = archsig::run::run_requests(
        &mut WriteFailure,
        &mut NoSignal::default(),
        &args,
        std::time::Instant::now(),
        &mut archsig::observed::control::Control::unlimited(),
    );
    assert_eq!(outcome.exit_code, 74);
    assert!(!dir.join("out").exists());
    assert_eq!(std::fs::read(dir.join("existing/keep")).unwrap(), b"keep");
    assert!(std::fs::read_dir(&dir).unwrap().all(|e| {
        !e.unwrap()
            .file_name()
            .to_string_lossy()
            .contains(".archsig-")
    }));
    let receipt = archsig::json::parse(outcome.receipt().as_bytes()).unwrap();
    assert!(!has(&receipt, "result"));
    assert_eq!(s(get(&arr(get(&receipt, "issues"))[0], "code")), "io");
    assert_eq!(
        s(get(
            get(&arr(get(&receipt, "issues"))[0], "details"),
            "operation"
        )),
        "write"
    );
    std::fs::create_dir(dir.join("out")).unwrap();
    std::fs::write(dir.join("out/keep"), b"keep").unwrap();
    let r = requests(&dir, &ASKS);
    notified(&dir, &r, "invalid", 64);
    assert_eq!(std::fs::read(dir.join("out/keep")).unwrap(), b"keep");
}
