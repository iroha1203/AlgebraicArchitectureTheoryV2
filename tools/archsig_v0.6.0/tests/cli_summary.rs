//! 日常の短い回答と、明示保存・後続計算・再利用の同値性。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
use cli::*;
use std::path::{Path, PathBuf};
fn counter(name: &str, count: Option<&str>) -> PathBuf {
    let dir = workdir(name);
    std::fs::write(
        dir.join("d.json"),
        include_bytes!("fixtures/counter.atoms.json"),
    )
    .unwrap();
    std::fs::write(dir.join("l.law"), include_str!("fixtures/counter.law")).unwrap();
    let original = include_str!("fixtures/counter.archmap.json");
    let map = match count {
        Some(n) => original.replace("\"value\": \"2\"", &format!("\"value\": \"{n}\"")),
        None => original.replace("{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}", ""),
    };
    std::fs::write(dir.join("a.json"), map).unwrap();
    dir
}
fn execute(dir: &Path, asks: &[&str], extra: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
    ];
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    args.extend(extra);
    run(dir, &args)
}
fn no_saved_proofs(result: &archsig::json::JNode) {
    for node in arr(get(result, "nodes")) {
        if let archsig::json::JValue::Str(ty) = &get(node, "type").value {
            assert!(!matches!(ty.as_str(), "Evidence" | "Evaluation"));
            if ty == "Counterexample" {
                assert!(matches!(
                    s(get(get(node, "value"), "kind")),
                    "counterexample" | "completion_pair" | "separating_pair"
                ));
            }
        }
    }
}
#[test]
fn empty_integer_solutions_are_saved_without_smith_certificates() {
    let dir = counter("summary-empty-integer", Some("2"));
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap().replace("view amount", "change choose(s:State,a:Z)=s with{count=2*a}; law optional one(s:State):s.count=1; view amount");
    std::fs::write(path, law).unwrap();
    let asks = ["x=solve(CountCheck.one,on=@v/s,using=CountCheck.choose,s=@v/s)"];
    let brief = execute(&dir, &asks, &[]);
    assert_eq!(brief.code, 1, "{}", brief.stdout);
    assert!(brief.stdout.len() < 1500);
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    let saved = execute(&dir, &asks, &["--out", "saved"]);
    assert_eq!(saved.code, 1);
    let result = result_json(&dir, &saved);
    no_saved_proofs(&result);
    let id = s(get(
        get(
            get(&arr(get(&result, "answers"))[0], "outputs"),
            "solutions",
        ),
        "node",
    ));
    let solution = arr(get(&result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == id)
        .unwrap();
    let representation = get(get(solution, "value"), "representation");
    assert_eq!(s(get(representation, "kind")), "empty");
    assert!(!has(representation, "certificate"));
    let reused = execute(&dir, &asks, &["--reuse", "saved"]);
    assert_eq!(brief.receipt.value, reused.receipt.value);
}
#[test]
fn daily_answers_return_values_refutations_and_missing_without_files() {
    for (label, count, code) in [
        ("value", Some("2"), 0),
        ("refuted", Some("12"), 1),
        ("missing", None, 2),
    ] {
        let dir = counter(&format!("summary-{label}"), count);
        let asks = [
            "n=evaluate(CountCheck.amount,s=@v/s)",
            "c=check(CountAudit.bounded,s=@v/s)",
        ];
        let brief = execute(&dir, &asks, &[]);
        assert_eq!(brief.code, code, "{}", brief.stdout);
        assert_eq!(s(get(&brief.receipt, "format")), "archsig.summary/1");
        assert!(brief.stderr.is_empty());
        assert!(!has(&brief.receipt, "nodes"));
        assert!(!brief.stdout.contains("\"node\":"));
        assert!(brief.stdout.len() < 2000);
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        let answers = arr(get(&brief.receipt, "answers"));
        if let Some(count) = count {
            assert_eq!(
                s(get(get(get(&answers[0], "outputs"), "value"), "value")),
                count
            );
        } else {
            assert!(!arr(get(&answers[0], "reasons")).is_empty());
            assert!(!arr(get(&arr(get(&answers[0], "reasons"))[0], "missing")).is_empty());
        }
        let full = execute(&dir, &asks, &["--out", "saved"]);
        assert_eq!(full.code, brief.code);
        let result = result_json(&dir, &full);
        for answer in arr(get(&result, "answers")) {
            assert!(!has(answer, "claim"));
            for key in ["evaluation", "proposition"] {
                assert!(!has(get(answer, "outputs"), key));
            }
        }
        for node in arr(get(&result, "nodes")) {
            assert!(
                !matches!(&get(node,"type").value, archsig::json::JValue::Str(t) if matches!(t.as_str(), "Evaluation" | "Expression" | "LawInstance" | "Proposition"))
            );
            assert!(!has(node, "evidence"));
            if matches!(&get(node,"type").value, archsig::json::JValue::Str(t) if t == "Counterexample")
            {
                assert!(matches!(
                    s(get(get(node, "value"), "kind")),
                    "counterexample" | "completion_pair" | "separating_pair"
                ));
            }
        }
        for (brief, full) in answers.iter().zip(arr(get(&result, "answers"))) {
            assert_eq!(get(brief, "status").value, get(full, "status").value);
        }
        let reused = execute(&dir, &asks, &["--reuse", "saved"]);
        assert_eq!(reused.receipt.value, brief.receipt.value);
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 4);
    }
}
#[test]
fn daily_check_distinguishes_inapplicable_from_applicable_laws() {
    let dir = counter("summary-guard", Some("2"));
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap().replace(
        "view amount",
        "law required guarded(s: State) when false: s.count < 0; view amount",
    );
    std::fs::write(path, law).unwrap();
    let asks = [
        "g=check(CountCheck.guarded,s=@v/s)",
        "c=check(CountAudit.bounded,s=@v/s)",
    ];
    let brief = execute(&dir, &asks, &[]);
    assert_eq!(brief.code, 0, "{}", brief.stdout);
    let answers = arr(get(&brief.receipt, "answers"));
    assert_eq!(s(get(&answers[0], "applicability")), "not_applicable");
    assert_eq!(s(get(&answers[1], "applicability")), "applicable");
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    let saved = execute(&dir, &asks, &["--out", "saved"]);
    let result = result_json(&dir, &saved);
    let full = arr(get(&result, "answers"));
    for (a, b) in answers.iter().zip(full) {
        assert_eq!(get(a, "applicability").value, get(b, "applicability").value);
    }
}
#[test]
fn large_requested_values_are_available_in_explicit_saved_results() {
    let value = "1".repeat(1000);
    let dir = counter("summary-large-value", Some(&value));
    let asks = ["n=evaluate(CountCheck.amount,s=@v/s)"];
    let brief = execute(&dir, &asks, &[]);
    assert_eq!(brief.code, 0);
    assert!(brief.stdout.len() < 600);
    let output = get(
        get(&arr(get(&brief.receipt, "answers"))[0], "outputs"),
        "value",
    );
    assert_eq!(num(get(output, "value_bytes")), 1002);
    assert!(!has(output, "value"));
    let full = execute(&dir, &asks, &["--out", "saved"]);
    let result = result_json(&dir, &full);
    let reference = s(get(
        get(get(&arr(get(&result, "answers"))[0], "outputs"), "value"),
        "node",
    ));
    let node = arr(get(&result, "nodes"))
        .iter()
        .find(|node| s(get(node, "id")) == reference)
        .unwrap();
    assert_eq!(s(get(node, "value")), value);
}

#[test]
fn daily_local_diagnostics_keep_the_pipeline_without_exporting_its_calculation() {
    #[allow(dead_code)]
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    use archsig::{canonical::Json, definition};
    let dir = workdir("summary-diagnostics");
    let original = include_str!("fixtures/reservations.atoms.json");
    let definition = original.replace("\"type\": \"Z\"", "\"type\": \"Q\"");
    let before = definition::check_definitions(&[("d", original.as_bytes())]).unwrap();
    let after = definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
    let old = &before.vocabularies["Reservations"].digest;
    let digest = &after.vocabularies["Reservations"].digest;
    let law = include_str!("fixtures/public-compose.law").replace("view holdings", "law optional localValid(s:State):s.free=2; local Sum(s:State) reads s.free+s.held; local Left(s:State) reads s.free; local Delta(s:State) reads s.free-s.held; change choose(s:State,b:Bool)=s with{free=if b then 2 else 3,held=if b then 0 else -1}; view holdings")
        .replace(old, digest).replace("(Z, Z)", "(Q, Q)");
    let text = include_str!("fixtures/configuration-operation.archmap.json").replace(old, digest)
        .replace("\"id\":\"r-free\",\"subject\":\"r\",\"field\":\"Reservations.State.free\",\"value\":\"4\"", "\"id\":\"r-free\",\"subject\":\"r\",\"field\":\"Reservations.State.free\",\"value\":\"2\"")
        .replace("\"id\":\"s-free\",\"subject\":\"s\",\"field\":\"Reservations.State.free\",\"value\":\"3\"", "\"id\":\"s-free\",\"subject\":\"s\",\"field\":\"Reservations.State.free\",\"value\":\"1\"");
    let mut map = fixture::owned(&archsig::json::parse(text.as_bytes()).unwrap());
    for atom in fixture::atoms(&mut map) {
        let Json::Obj(atom) = atom else {
            panic!("atom")
        };
        if matches!(atom.get("field"), Some(Json::Str(field)) if field == "Reservations.State.free" || field == "Reservations.State.held")
        {
            atom.insert(
                "value".into(),
                Json::Arr(vec![atom["value"].clone(), Json::str("1")]),
            );
        }
    }
    for (name, content) in [
        ("d.json", definition),
        ("l.law", law),
        ("a.json", map.canonical()),
    ] {
        std::fs::write(dir.join(name), content).unwrap();
    }
    let asks = [
        "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
        "r=localize($m.candidate.target,law=Reservations.localValid,s=@v/r,using=Reservations.choose)",
        "d=diagnose($l.system,side=semantic,degree=1)",
        "e=diagnose($r.system,side=semantic,degree=1)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
    ];
    let brief = execute(&dir, &asks, &[]);
    assert_eq!(brief.code, 0, "{}", brief.stdout);
    assert!(brief.stderr.is_empty());
    assert!(brief.stdout.len() < 5000, "{} bytes", brief.stdout.len());
    for internal in ["\"nodes\":", "\"evidence\":", "\"rule\":", "\"scope\":"] {
        assert!(!brief.stdout.contains(internal));
    }
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    let answers = arr(get(&brief.receipt, "answers"));
    assert_eq!(answers.len(), 6);
    assert!(
        answers
            .iter()
            .all(|answer| s(get(answer, "status")) == "established")
    );
    let diagnostic = get(get(&answers[3], "outputs"), "diagnostic");
    assert_eq!(s(get(diagnostic, "side")), "semantic");
    assert_eq!(num(get(diagnostic, "degree")), 1);
    assert!(num(get(get(diagnostic, "matching"), "elements_count")) > 0);
    let full = execute(&dir, &asks, &["--out", "saved"]);
    assert_eq!(full.code, 0, "{}", full.stdout);
    let result = result_json(&dir, &full);
    no_saved_proofs(&result);
    let mut coordinates = std::collections::BTreeSet::new();
    for node in arr(get(&result, "nodes")) {
        if matches!(&get(node,"type").value, archsig::json::JValue::Str(t) if matches!(t.as_str(), "Ring" | "Module")) {
            let mut value = fixture::owned(node);
            let Json::Obj(fields) = &mut value else { unreachable!() };
            fields.remove("id");
            assert!(coordinates.insert(value.canonical()), "同じ座標表示を重複保存しない");
        }
    }
    for internal in ["producer", "reuse", "usage", "limits"] {
        assert!(!has(&result, internal));
    }
    assert!(
        std::fs::metadata(dir.join("saved/result.json"))
            .unwrap()
            .len()
            < 400_000
    );
    for node in arr(get(&result, "nodes")) {
        for internal in ["rule", "arguments", "evidence", "scope", "support"] {
            assert!(!has(node, internal), "{internal}");
        }
        if matches!(&get(node,"type").value, archsig::json::JValue::Str(t) if t == "EvaluationResult")
        {
            for internal in ["parts", "expression"] {
                assert!(!has(get(node, "value"), internal));
            }
        }
        if matches!(&get(node,"type").value, archsig::json::JValue::Str(t) if t == "LawInstance")
            && has(node, "value")
        {
            for internal in ["body", "guard", "occurrence"] {
                assert!(!has(get(node, "value"), internal));
            }
        }
    }
    let reused = execute(&dir, &asks, &["--reuse", "saved"]);
    assert_eq!(reused.receipt.value, brief.receipt.value);
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 4);
    println!(
        "daily={} saved={} bytes",
        brief.stdout.len(),
        std::fs::metadata(dir.join("saved/result.json"))
            .unwrap()
            .len()
    );
}
