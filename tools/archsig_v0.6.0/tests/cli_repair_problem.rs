//! 共通の有限修復問題をCLIで保存し、現在入力に戻して再観測する。
use crate::common::{cli::*, repair_problem_data as fixture};
use std::path::Path;
const ASKS: [&str; 8] = [
    "u=evaluate(Selected.all,r=@v/root)",
    "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
    "r=scopes($p.problem)",
    "s=solve($p.problem,within=$r.ranges[0])",
    "c=candidate($s.solutions,index=1)",
    "a=apply($c.assignment,in=$s.solutions)",
    "ok=check(Selected.valid,on=$a.object)",
    "v=evaluate(Selected.flag,c=@v/q,on=$a.object)",
];
fn execute(dir: &Path, out: &str, reuse: Option<&str>) -> BinaryRun {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--archmap",
        "a.json",
        "--law",
        "l.law",
        "--out",
        out,
    ];
    if let Some(path) = reuse {
        args.extend(["--reuse", path]);
    }
    for ask in ASKS {
        args.extend(["--ask", ask]);
    }
    run_binary(dir, &args)
}
#[test]
fn saved_shared_problem_and_ordinal_return_to_current_observation() {
    let input = fixture::input("");
    let dir = workdir("shared-repair-problem");
    for (name, data) in [
        ("d.json", input.definitions()[0].bytes()),
        ("a.json", input.archmap().bytes()),
        ("l.law", input.law().bytes()),
    ] {
        std::fs::write(dir.join(name), data).unwrap();
    }
    let first = execute(&dir, "first", None);
    assert_eq!(first.code, 0, "{}", first.stdout);
    let saved = "first";
    let second = execute(&dir, "second", Some(saved));
    assert_eq!(second.code, 0, "{}", second.stdout);
    assert!(warnings(&result_json(&dir, &second)).is_empty());
    for run in [&first, &second] {
        let result = result_json(&dir, &run.run);
        let answers = arr(get(&result, "answers"));
        assert_eq!(answers.len(), 8);
        for answer in answers {
            assert_eq!(s(get(answer, "status")), "established");
        }
        let output = get(get(&answers[7], "outputs"), "value");
        let value = arr(get(&result, "nodes"))
            .iter()
            .find(|n| s(get(n, "id")) == s(get(output, "node")))
            .unwrap();
        assert!(matches!(
            get(value, "value").value,
            archsig_common::json::JValue::Bool(true)
        ));
        let requests = arr(get(&result, "requests"));
        let index = arr(get(&requests[4], "arguments"))
            .iter()
            .find(|a| s(get(a, "name")) == "index")
            .unwrap();
        let selector = get(index, "value");
        assert_eq!(s(get(selector, "kind")), "ordinal");
        assert_eq!(s(get(selector, "value")), "1");
    }
    // 保存結果の古い対象を採用せず、現在のLawで選択後の再観測を変える。
    let law = String::from_utf8(input.law().bytes().to_vec())
        .unwrap()
        .replace(
            "view flag(c:Part):Bool=c.flag",
            "view flag(c:Part):Bool=not c.flag",
        );
    std::fs::write(dir.join("l.law"), law).unwrap();
    let changed = execute(&dir, "changed", Some(saved));
    assert_eq!(changed.code, 0, "{}", changed.stdout);
    let result = result_json(&dir, &changed);
    let rejected = warnings(&result);
    assert!(
        rejected
            .iter()
            .any(|w| s(get(w, "message")).contains("current input identity does not match"))
    );
    let answers = arr(get(&result, "answers"));
    let output = get(get(&answers[7], "outputs"), "value");
    let value = arr(get(&result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(output, "node")))
        .unwrap();
    assert!(matches!(
        get(value, "value").value,
        archsig_common::json::JValue::Bool(false)
    ));
}

#[test]
fn fixed_range_comparison_keeps_original_assignments_in_both_routes() {
    let dir = workdir("shared-repair-ranges");
    for (name, data) in [
        (
            "d.json",
            include_bytes!("fixtures/shared-repair-saleor/definition.json").as_slice(),
        ),
        (
            "a.json",
            include_bytes!("fixtures/shared-repair-saleor/input.archmap.json").as_slice(),
        ),
        (
            "l.law",
            include_bytes!("fixtures/shared-repair-saleor/input.law").as_slice(),
        ),
    ] {
        std::fs::write(dir.join(name), data).unwrap();
    }
    for (route, asks) in [
        (
            "independent",
            include_str!("fixtures/shared-repair-saleor/independent.asks"),
        ),
        (
            "shared",
            include_str!("fixtures/shared-repair-saleor/shared.asks"),
        ),
    ] {
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
            "--out",
            route,
        ];
        for ask in asks.lines() {
            args.extend(["--ask", ask]);
        }
        let executed = run(&dir, &args);
        assert_eq!(executed.code, 1, "{}", executed.stdout);
        let result = result_json(&dir, &executed);
        let answers = arr(get(&result, "answers"));
        for (id, status) in [
            ("task", "refuted"),
            ("payment", "refuted"),
            ("shared", "established"),
            ("ok", "established"),
        ] {
            let answer = answers.iter().find(|a| s(get(a, "id")) == id).unwrap();
            assert_eq!(s(get(answer, "status")), status);
        }
        let candidate = answers.iter().find(|a| s(get(a, "id")) == "c").unwrap();
        let reference = get(get(candidate, "outputs"), "assignment");
        let nodes = arr(get(&result, "nodes"));
        let resolve = |r: &archsig_common::json::JNode| {
            get(
                nodes
                    .iter()
                    .find(|n| s(get(n, "id")) == s(get(r, "node")))
                    .unwrap(),
                "value",
            )
        };
        let assignment = resolve(reference);
        let entries = arr(get(assignment, "entries"));
        assert_eq!(entries.len(), 6);
        for entry in entries {
            let subject = resolve(get(entry, "subject"));
            let label = s(&arr(subject)[1]);
            let value = resolve(&arr(get(entry, "parameters"))[0]);
            assert!(
                matches!(value.value,archsig_common::json::JValue::Bool(v) if v==matches!(label,"x"|"y"|"z"))
            );
        }
    }
}

#[test]
fn saved_observation_plan_is_rechecked_after_primitive_observation() {
    use crate::common::repair_observation_data;
    let body = "view input(r:Root):Bool=r.h;view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):forall c in Part[r]. c.flag=r.h;";
    let dir = workdir("repair-observation");
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)",
        "a=observe(Selected.input,on=$p.problem,within=$u.value,output=assignment,r=@v/root)",
    ];
    let execute = |out: &str, reuse: Option<&str>, observed: bool| {
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
            "--out",
            out,
        ];
        if let Some(reuse) = reuse {
            args.extend(["--reuse", reuse]);
        }
        for ask in asks {
            args.extend(["--ask", ask]);
        }
        if observed {
            for ask in [
                "c=candidate($a.solutions,index=0)",
                "ap=apply($c.assignment,in=$a.solutions)",
                "ok=check(Selected.valid,on=$ap.object,r=@v/root)",
            ] {
                args.extend(["--ask", ask]);
            }
        }
        run_binary(&dir, &args)
    };
    for known in [false, true] {
        let input = repair_observation_data::input(body, "\"Bool\"", known.then_some("true"));
        for (name, bytes) in [
            ("d.json", input.definitions()[0].bytes()),
            ("a.json", input.archmap().bytes()),
            ("l.law", input.law().bytes()),
        ] {
            std::fs::write(dir.join(name), bytes).unwrap();
        }
        if !known {
            for (out, reuse) in [("first", None), ("same", Some("first"))] {
                let executed = execute(out, reuse, false);
                assert_eq!(executed.code, 0, "{}", executed.stdout);
                let result = result_json(&dir, &executed);
                assert!(warnings(&result).is_empty());
                let answers = arr(get(&result, "answers"));
                assert_eq!(s(get(&answers[2], "status")), "established");
                assert!(!has(get(&answers[2], "outputs"), "solutions"));
            }
        } else {
            let executed = execute("observed", Some("first"), true);
            assert_eq!(executed.code, 0, "{}", executed.stdout);
            let result = result_json(&dir, &executed);
            assert!(warnings(&result).iter().any(|w|s(get(w,"message")).contains("current input identity does not match")));
            for answer in arr(get(&result, "answers")) {
                assert_eq!(s(get(answer, "status")), "established");
            }
        }
    }
}

#[allow(dead_code)]
#[path = "common/integer_reobservation_data.rs"]
mod integer_fixture;
#[test]
fn saved_integer_problem_preserves_exact_ordinal_and_rechecks_forged_original_assignment() {
    let body = "view all(s:State):Set<State> =set<State>{s};view first(s:State):Z=s.h;change choose(s:State,p:Z,q:Z)=s with{h=p};law required valid(s:State):s.a*s.h=s.b;";
    let input = integer_fixture::input(body, "2", "2");
    let dir = workdir("integer-common-repair-save");
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("a.json", input.archmap().bytes()),
        ("l.law", input.law().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let asks = [
        "u=evaluate(Pair.all,s=@v/s)",
        "p=prepare(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "ranges=scopes($p.problem)",
        "s=solve($p.problem,within=$ranges.ranges[0])",
        "c=candidate($s.solutions,index=18446744073709551617)",
        "a=apply($c.assignment,in=$s.solutions)",
        "ok=check(Pair.valid,on=$a.object,s=@v/s)",
        "h=evaluate(Pair.first,on=$a.object,s=@v/s)",
    ];
    let run = |out: &str, reuse: Option<&str>| {
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
            "--out",
            out,
        ];
        if let Some(path) = reuse {
            args.extend(["--reuse", path]);
        }
        for ask in asks {
            args.extend(["--ask", ask]);
        }
        run_binary(&dir, &args)
    };
    let first = run("first", None);
    assert_eq!(first.code, 0, "{}", first.stdout);
    let same = run("same", Some("first"));
    assert_eq!(same.code, 0, "{}", same.stdout);
    let cold = result_json(&dir, &first);
    let warm = result_json(&dir, &same);
    assert!(warnings(&warm).is_empty());
    for key in ["requests", "answers", "nodes"] {
        assert_eq!(get(&cold, key), get(&warm, key), "{key}");
    }
    for answer in arr(get(&warm, "answers")) {
        assert_eq!(s(get(answer, "status")), "established");
    }
    let requests = arr(get(&warm, "requests"));
    let index = arr(get(&requests[4], "arguments"))
        .iter()
        .find(|a| s(get(a, "name")) == "index")
        .unwrap();
    assert_eq!(s(get(get(index, "value"), "value")), "18446744073709551617");
    let raw = std::fs::read_to_string(dir.join(s(get(&first.receipt, "result")))).unwrap();
    let forged = raw.replace("\"9223372036854775809\"", "\"9223372036854775810\"");
    assert_ne!(raw, forged);
    std::fs::create_dir(dir.join("forged")).unwrap();
    std::fs::write(dir.join("forged/result.json"), forged).unwrap();
    let rejected = run("rejected", Some("forged"));
    assert_eq!(rejected.code, 0, "{}", rejected.stdout);
    let checked = result_json(&dir, &rejected);
    assert!(!warnings(&checked).is_empty());
    for key in ["requests", "answers", "nodes"] {
        assert_eq!(get(&cold, key), get(&checked, key), "{key}");
    }
    let changed = integer_fixture::input(body, "2", "4");
    std::fs::write(dir.join("a.json"), changed.archmap().bytes()).unwrap();
    let current = run("current", Some("first"));
    assert_eq!(current.code, 0, "{}", current.stdout);
    let result = result_json(&dir, &current);
    assert!(!warnings(&result).is_empty());
    let value = get(get(&arr(get(&result, "answers"))[7], "outputs"), "value");
    let node = arr(get(&result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(value, "node")))
        .unwrap();
    assert_eq!(s(get(node, "value")), "2");
}

#[test]
fn saved_integer_observation_uses_current_raw_values_before_candidate_and_apply() {
    let body = "view all(s:State):Set<State> =set<State>{s};view input(s:State):Z=s.b;change choose(s:State,p:Z)=s with{h=p};law required valid(s:State):2*s.h=s.b;";
    let dir = workdir("integer-repair-observation");
    let run = |out: &str, reuse: Option<&str>, observed: bool| {
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
            "--out",
            out,
        ];
        if let Some(path) = reuse {
            args.extend(["--reuse", path]);
        }
        for ask in [
            "u=evaluate(Pair.all,s=@v/s)",
            "p=prepare(Pair.valid,using=Pair.choose,on=@v/s,inputs=Pair.input,s=@v/s)",
            "a=observe(Pair.input,on=$p.problem,within=$u.value,output=assignment,s=@v/s)",
        ] {
            args.extend(["--ask", ask]);
        }
        if observed {
            for ask in [
                "c=candidate($a.solutions,index=0)",
                "ap=apply($c.assignment,in=$a.solutions)",
                "ok=check(Pair.valid,on=$ap.object,s=@v/s)",
            ] {
                args.extend(["--ask", ask]);
            }
        }
        run_binary(&dir, &args)
    };
    let input = integer_fixture::input(body, "2", "2");
    std::fs::write(dir.join("d.json"), input.definitions()[0].bytes()).unwrap();
    std::fs::write(dir.join("l.law"), input.law().bytes()).unwrap();
    let mut map = String::from_utf8(input.archmap().bytes().to_vec()).unwrap();
    let start = map.find(r#"{"id":"b","#).unwrap();
    let end = start + map[start..].find('}').unwrap() + 1;
    assert_eq!(map.as_bytes()[start - 1], b',');
    map.replace_range(start - 1..end, "");
    std::fs::write(dir.join("a.json"), map).unwrap();
    for (out, reuse) in [("missing", None), ("same", Some("missing"))] {
        let executed = run(out, reuse, false);
        assert_eq!(executed.code, 0, "{}", executed.stdout);
        let result = result_json(&dir, &executed);
        assert!(warnings(&result).is_empty());
        let answers = arr(get(&result, "answers"));
        assert!(!has(get(&answers[2], "outputs"), "solutions"));
        let plan = get(get(&answers[2], "outputs"), "plan");
        let plan = arr(get(&result, "nodes"))
            .iter()
            .find(|n| s(get(n, "id")) == s(get(plan, "node")))
            .unwrap();
        let value = get(plan, "value");
        assert_eq!(arr(get(value, "requirements")).len(), 1);
        assert!(has(value, "affine"));
    }
    std::fs::write(dir.join("a.json"), input.archmap().bytes()).unwrap();
    let executed = run("observed", Some("missing"), true);
    assert_eq!(executed.code, 0, "{}", executed.stdout);
    let result = result_json(&dir, &executed);
    assert!(
        warnings(&result)
            .iter()
            .any(|w| s(get(w, "message")).contains("current input identity does not match"))
    );
    let answers = arr(get(&result, "answers"));
    for a in answers {
        assert_eq!(s(get(a, "status")), "established");
    }
    let plan = get(get(&answers[2], "outputs"), "plan");
    let plan = arr(get(&result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(plan, "node")))
        .unwrap();
    assert!(arr(get(get(plan, "value"), "requirements")).is_empty());
}
