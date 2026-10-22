#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
#[allow(dead_code)]
#[path = "common/public_relation.rs"]
mod fixture;
use archsig::json::JNode;
use cli::*;
use std::path::{Path, PathBuf};
fn files(name: &str, script: &str, missing: bool) -> PathBuf {
    let dir = workdir(name);
    let input = fixture::input(script, missing);
    std::fs::write(dir.join("d.json"), input.definitions()[0].bytes()).unwrap();
    std::fs::write(dir.join("l.law"), input.law().bytes()).unwrap();
    std::fs::write(dir.join("a.json"), input.archmap().bytes()).unwrap();
    dir
}
fn asks(dir: &Path, texts: &[&str]) -> Run {
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
    for text in texts {
        args.extend(["--ask", *text]);
    }
    run(dir, &args)
}
fn answer<'a>(result: &'a JNode, id: &str) -> &'a JNode {
    arr(get(result, "answers"))
        .iter()
        .find(|answer| s(get(answer, "id")) == id)
        .unwrap()
}
fn node<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|node| s(get(node, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn saved(dir: &Path, run: &Run, status: &str, code: i32) -> JNode {
    assert_eq!(run.code, code, "{}", run.stdout);
    assert!(run.stderr.is_empty(), "{}", run.stderr);
    assert_eq!(s(get(&run.receipt, "status")), status);
    assert_eq!(num(get(&run.receipt, "exit_code")), code as u64);
    let result = result_json(dir, run);
    assert_eq!(s(get(&result, "command")), "run");
    assert_eq!(s(get(&result, "status")), status);
    assert_eq!(num(get(&result, "exit_code")), code as u64);
    result
}
#[test]
fn relation_membership_and_free_word_nonmembership_have_distinct_checked_evidence() {
    let texts = [
        fixture::E,
        fixture::ALIAS,
        "compared=compare($e.value,to=$alias.value,kind=relation)",
    ];
    for (name, script, expected) in [
        ("relation-names-free", "", "refuted"),
        (
            "relation-names-rule",
            fixture::ALIAS_RELATION,
            "established",
        ),
    ] {
        let dir = files(name, script, false);
        let run = asks(&dir, &texts);
        let result = saved(
            &dir,
            &run,
            "complete",
            if expected == "refuted" { 1 } else { 0 },
        );
        let compared = answer(&result, "compared");
        assert_eq!(s(get(compared, "status")), expected);
        assert!(has(get(compared, "outputs"), "comparison"));
        let claim = node(&result, get(get(compared, "outputs"), "proposition"));
        assert_eq!(s(get(get(claim, "value"), "predicate")), "relation_equal");
        assert_eq!(arr(get(compared, "evidence")).len(), 2);
        let proof = node(&result, &arr(get(compared, "evidence"))[1]);
        assert_eq!(
            s(get(get(proof, "value"), "kind")),
            if expected == "established" {
                "normalization"
            } else {
                "counterexample"
            }
        );
        assert!(arr(get(&result, "issues")).is_empty());
    }
}
#[test]
fn a_composed_path_uses_the_original_relation_inside_its_query_context() {
    let dir = files("relation-context", fixture::ALIAS_RELATION, false);
    let run = asks(
        &dir,
        &[
            fixture::E,
            fixture::ALIAS,
            fixture::F,
            fixture::C,
            "other=compose($alias.value,then=$f.value)",
            "compared=compare($c.operation,to=$other.operation,kind=relation)",
        ],
    );
    let result = saved(&dir, &run, "complete", 0);
    assert_eq!(s(get(answer(&result, "compared"), "status")), "established");
    let proof = node(
        &result,
        &arr(get(answer(&result, "compared"), "evidence"))[1],
    );
    assert!(!arr(get(get(get(proof, "value"), "data"), "steps")).is_empty());
}
#[test]
fn missing_relation_guard_is_a_partial_result_with_a_plan_for_the_original_field() {
    let dir = files("relation-needed", fixture::PENDING_RELATION, true);
    let run = asks(
        &dir,
        &[
            fixture::E,
            fixture::ALIAS,
            "compared=compare($e.value,to=$alias.value,kind=relation)",
            "observe=needed($compared)",
        ],
    );
    let result = saved(&dir, &run, "partial", 2);
    assert_eq!(s(get(answer(&result, "e"), "status")), "established");
    assert_eq!(s(get(answer(&result, "alias"), "status")), "established");
    assert_eq!(
        s(get(answer(&result, "compared"), "status")),
        "undetermined"
    );
    let plan = node(
        &result,
        get(get(answer(&result, "observe"), "outputs"), "plan"),
    );
    let requirements = arr(get(get(plan, "value"), "requirements"));
    assert_eq!(requirements.len(), 1);
    let field = get(&requirements[0], "field");
    assert_eq!(s(get(field, "snapshot")), "v");
    assert_eq!(s(get(field, "subject")), "guard");
    assert_eq!(s(get(field, "field")), "Paths.Guard.flag");
    assert!(!arr(get(&requirements[0], "dependents")).is_empty());
}
#[test]
fn malformed_relation_comparison_notifies_stdout_and_preserves_existing_files() {
    let dir = files("relation-invalid-selector", "", false);
    std::fs::create_dir(dir.join("out")).unwrap();
    std::fs::write(dir.join("out/keep"), b"existing").unwrap();
    let run = asks(
        &dir,
        &[
            fixture::E,
            "compared=compare($e.value,to=$e.value,kind=relation,along=$e.value)",
        ],
    );
    assert_eq!(run.code, 64);
    assert!(!has(&run.receipt, "result"));
    assert!(!arr(get(&run.receipt, "issues")).is_empty());
    assert!(
        arr(get(&run.receipt, "issues"))
            .iter()
            .all(|issue| !s(get(issue, "message")).is_empty())
    );
    assert_eq!(std::fs::read(dir.join("out/keep")).unwrap(), b"existing");
    assert!(std::fs::read_dir(&dir).unwrap().all(|entry| {
        !entry
            .unwrap()
            .file_name()
            .to_string_lossy()
            .contains(".archsig-")
    }));
}
