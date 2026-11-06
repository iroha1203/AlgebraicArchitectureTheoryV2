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
    let saved = s(get(&first.receipt, "result")).to_owned();
    let second = execute(&dir, "second", Some(&saved));
    assert_eq!(second.code, 0, "{}", second.stdout);
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
    let changed = execute(&dir, "changed", Some(&saved));
    assert_eq!(changed.code, 0, "{}", changed.stdout);
    let result = result_json(&dir, &changed);
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
