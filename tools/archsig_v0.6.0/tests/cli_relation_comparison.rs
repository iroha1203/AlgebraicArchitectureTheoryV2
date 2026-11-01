use crate::common::cli;
#[allow(dead_code)]
use crate::common::public_relation as fixture;
use archsig::json::JNode;
use cli::*;
use std::path::{Path, PathBuf};
fn files(name: &str, script: &str, missing: bool) -> PathBuf {
    input_files(name, without_unused_hops(fixture::input(script, missing)))
}
// relationの族は Hop の組で展開されるので、試験が使わない Hop(self・different)を外して族を小さくする。
fn without_unused_hops(sources: archsig::input::InputSources) -> archsig::input::InputSources {
    use archsig::canonical::Json;
    use archsig::json::JValue;
    fn convert(node: &JNode) -> Json {
        match &node.value {
            JValue::Bool(value) => Json::Bool(*value),
            JValue::Str(value) => Json::str(value),
            JValue::Num(value) => Json::Nat(value.parse().unwrap()),
            JValue::Arr(values) => Json::Arr(values.iter().map(convert).collect()),
            JValue::Obj(fields) => Json::Obj(
                fields
                    .iter()
                    .map(|(name, value)| (name.clone(), convert(value)))
                    .collect(),
            ),
            JValue::Null => panic!("この原始fixtureにnullはない"),
        }
    }
    fn unused(json: &Json, key: &str) -> bool {
        let Json::Obj(fields) = json else { panic!() };
        fields[key] == Json::str("self") || fields[key] == Json::str("different")
    }
    let mut map = convert(&archsig::json::parse(sources.archmap().bytes()).unwrap());
    let Json::Obj(root) = &mut map else { panic!() };
    let Json::Arr(snapshots) = root.get_mut("snapshots").unwrap() else {
        panic!()
    };
    let Json::Obj(v) = &mut snapshots[0] else {
        panic!()
    };
    let Json::Arr(subjects) = v.get_mut("subjects").unwrap() else {
        panic!()
    };
    let before = subjects.len();
    subjects.retain(|subject| !unused(subject, "id"));
    assert!(subjects.len() < before);
    let Json::Arr(atoms) = v.get_mut("atoms").unwrap() else {
        panic!()
    };
    atoms.retain(|atom| !unused(atom, "subject"));
    archsig::input::InputSources::from_bytes(
        sources
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        sources.law().bytes().to_vec(),
        map.canonical().into_bytes(),
    )
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
// 宣言relationでの成立(閉じた語の証拠)と合成Pathでの成立は、同じ入力の実評価を
// src/observed/public_relation_sources_tests.rs が確かめる。ここでは公開結果の反証の形を見る。
#[test]
fn free_word_nonmembership_has_a_checked_counterexample() {
    let dir = files("relation-names-free", "", false);
    let run = asks(
        &dir,
        &[
            fixture::E,
            fixture::ALIAS,
            "compared=compare($e.value,to=$alias.value,kind=relation)",
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    let compared = answer(&result, "compared");
    assert_eq!(s(get(compared, "status")), "refuted");
    assert!(has(get(compared, "outputs"), "comparison"));
    let claim = node(&result, get(get(compared, "outputs"), "proposition"));
    assert_eq!(s(get(get(claim, "value"), "predicate")), "relation_equal");
    assert_eq!(arr(get(compared, "counterexamples")).len(), 1);
    let example = node(&result, &arr(get(compared, "counterexamples"))[0]);
    assert_eq!(s(get(get(example, "value"), "kind")), "counterexample");
    assert!(arr(get(&result, "issues")).is_empty());
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
