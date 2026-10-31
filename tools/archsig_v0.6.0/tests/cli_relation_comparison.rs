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
    input_files(name, fixture::input(script, missing))
}
fn input_files(name: &str, input: archsig::input::InputSources) -> PathBuf {
    let dir = workdir(name);
    std::fs::write(dir.join("d.json"), input.definitions()[0].bytes()).unwrap();
    std::fs::write(dir.join("l.law"), input.law().bytes()).unwrap();
    std::fs::write(dir.join("a.json"), input.archmap().bytes()).unwrap();
    dir
}

fn partial_domain_case(outside: bool) {
    let dir = input_files(
        if outside {
            "relation-prefix-nonfinite"
        } else {
            "relation-prefix-missing"
        },
        fixture::partial_domain_input(outside, "path(e)=identity(source(path(e)))"),
    );
    let snapshot = if outside { "v" } else { "w" };
    let one = format!("one=evaluate(Reservations.route,e=@{snapshot}/e)");
    let two = format!("two=evaluate(Reservations.route,e=@{snapshot}/k)");
    let run = asks(
        &dir,
        &[
            &one,
            &two,
            "compared=compare($one.value,to=$two.value,kind=relation)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = saved(&dir, &run, "complete", 1);
    assert_eq!(s(get(answer(&result, "one"), "status")), "established");
    assert_eq!(s(get(answer(&result, "two"), "status")), "established");
    let compared = answer(&result, "compared");
    assert_eq!(s(get(compared, "status")), "refuted");
    assert!(!has(get(compared, "outputs"), "comparison"));
    assert!(!arr(get(compared, "counterexamples")).is_empty());
    assert!(
        arr(get(compared, "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "condition_failed")
    );
    assert!(arr(get(&result, "issues")).iter().all(|r| matches!(
        s(get(r, "code")),
        "condition_failed" | "missing_observation"
    )));
    let claim = node(&result, get(compared, "claim"));
    assert_eq!(s(get(get(claim, "value"), "predicate")), "constructible");
    if !outside {
        assert!(
            arr(get(compared, "reasons"))
                .iter()
                .any(|r| s(get(r, "code")) == "missing_observation")
        );
    }
}

#[test]
fn a_known_relation_refutation_survives_nonfinite_prefixes_of_the_same_declaration() {
    partial_domain_case(true);
}

#[test]
fn a_known_relation_refutation_survives_missing_owned_prefixes_of_the_same_declaration() {
    partial_domain_case(false);
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
        if expected == "established" { assert!(!has(compared,"counterexamples")); }
        else {
            assert_eq!(arr(get(compared,"counterexamples")).len(),1);
            let example=node(&result,&arr(get(compared,"counterexamples"))[0]);
            assert_eq!(s(get(get(example,"value"),"kind")),"counterexample");
        }
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
    assert!(!has(answer(&result,"compared"),"counterexamples"));
    let result=internal_graph(&dir,&result);
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
    let texts = [
        fixture::E,
        "compared=compare($e.value,to=$e.value,kind=relation,along=$e.value)",
    ];
    let invalid = asks(&dir, &texts);
    assert_eq!(invalid.code, 64);
    assert!(invalid.stderr.is_empty());
    assert!(!has(&invalid.receipt, "result"));
    assert!(
        arr(get(&invalid.receipt, "issues"))
            .iter()
            .any(|issue| { s(get(issue, "message")).contains("along") })
    );
    assert!(!dir.join("out").exists());
    std::fs::create_dir(dir.join("out")).unwrap();
    std::fs::write(dir.join("out/keep"), b"existing").unwrap();
    let run = asks(&dir, &texts);
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
