//! 原始三入力からの公開Operation合成。期待値は文書本文から取得しない。
mod common;
use archsig::json::JNode;
use common::cli::*;
use std::path::{Path, PathBuf};
const D: &[u8] = include_bytes!("fixtures/reservations.atoms.json");
const L: &[u8] = include_bytes!("fixtures/public-compose.law");
const A: &str = include_str!("fixtures/configuration-operation.archmap.json");
const M: &str = "m=map(Reservations.Migration,on=@v/m,reading=Reservations)";
const N: &str = "n=map(Reservations.Migration,on=@v/n,reading=Reservations)";
const C: &str = "c=compose($m.operation,then=$n.operation)";
fn inputs(name: &str, map: &str) -> PathBuf {
    let dir = workdir(name);
    for (n, b) in [("d.json", D), ("l.law", L), ("a.json", map.as_bytes())] {
        std::fs::write(dir.join(n), b).unwrap();
    }
    dir
}
fn asks(dir: &Path, qs: &[&str]) -> Run {
    let mut a = vec![
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
    for q in qs {
        a.extend(["--ask", q]);
    }
    run(dir, &a)
}
fn node<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    arr(get(j, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(r, "node")))
        .unwrap()
}
fn value<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    get(node(j, r), "value")
}
fn answer<'a>(j: &'a JNode, id: &str) -> &'a JNode {
    arr(get(j, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn saved(dir: &Path, r: &Run, status: &str, code: i32) -> JNode {
    assert_eq!(r.code, code, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), status);
    let j = result_json(dir, r);
    assert_eq!(s(get(&j, "status")), status);
    assert_eq!(num(get(&j, "exit_code")), code as u64);
    j
}
#[test]
fn composed_operations_keep_total_action_typed_words_and_original_operation_refs() {
    let dir = inputs("compose-success", A);
    let r = asks(
        &dir,
        &[
            "cc=compose($c.operation,then=$m.operation)",
            C,
            N,
            M,
            "read=evaluate(Reservations.sourceOf,m=$cc.operation.word[2])",
        ],
    );
    let j = saved(&dir, &r, "complete", 0);
    assert_eq!(
        arr(get(&j, "answers"))
            .iter()
            .map(|a| s(get(a, "id")))
            .collect::<Vec<_>>(),
        ["cc", "c", "n", "m", "read"]
    );
    for (id, word, end) in [("c", vec!["m", "n"], "A"), ("cc", vec!["m", "n", "m"], "B")] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), "established");
        let outputs = get(a, "outputs");
        let op = value(&j, get(outputs, "operation"));
        let map = value(&j, get(outputs, "map"));
        assert_eq!(get(op, "configuration_map"), get(outputs, "map"));
        assert_eq!(get(op, "candidate"), get(map, "candidate"));
        let candidate = value(&j, get(map, "candidate"));
        assert!(!has(candidate, "subject") && !has(candidate, "declaration"));
        assert_eq!(get(candidate, "source"), get(op, "source"));
        assert_eq!(get(candidate, "target"), get(op, "target"));
        assert_eq!(get(candidate, "action"), get(op, "action"));
        assert_eq!(s(get(get(op, "name"), "kind")), "word");
        let names = arr(get(op, "word"))
            .iter()
            .map(|r| s(&arr(value(&j, r))[1]))
            .collect::<Vec<_>>();
        assert_eq!(names, word);
        for r in arr(get(op, "word")) {
            assert_eq!(
                s(&arr(get(node(&j, r), "type"))[1]),
                "Reservations.Migration"
            );
        }
        assert_eq!(
            s(&arr(value(&j, get(value(&j, get(op, "target")), "root")))[1]),
            end
        );
        let action = value(&j, get(op, "action"));
        let universe = arr(get(value(&j, get(action, "universe")), "atoms"));
        let images = arr(get(action, "images"));
        assert_eq!(universe.len(), 62);
        assert_eq!(images.len(), 62);
        for (atom, image) in universe.iter().zip(images) {
            let owner = s(get(atom, "subject"));
            let in_family = ["A", "p", "q", "e", "h", "k"].contains(&owner);
            let expected = if id == "c" {
                if in_family { owner } else { "A" }
            } else {
                match owner {
                    "A" => "B",
                    "p" => "r",
                    "q" => "s",
                    "e" => "f",
                    "h" => "l",
                    "k" => "t",
                    _ => "B",
                }
            };
            assert_eq!(s(get(image, "subject")), expected);
            if id == "c" && in_family {
                assert_eq!(image, atom);
            }
            if !in_family {
                assert!(!has(image, "field"));
            }
        }
        let original = if id == "c" { ["m", "n"] } else { ["c", "m"] };
        for (r, original) in arr(get(get(op, "name"), "generators")).iter().zip(original) {
            assert_eq!(r, get(get(answer(&j, original), "outputs"), "operation"));
        }
        assert_eq!(
            arr(get(node(&j, get(outputs, "operation")), "conditions")).len(),
            1
        );
        assert_eq!(
            get(node(&j, get(outputs, "operation")), "conditions"),
            get(node(&j, get(outputs, "map")), "conditions")
        );
    }
    let read = answer(&j, "read");
    assert_eq!(
        s(&arr(value(&j, get(get(read, "outputs"), "value")))[1]),
        "A"
    );
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn incompatible_actual_intermediate_objects_are_refutations_and_block_dependents() {
    let dir = inputs("compose-refuted", A);
    let r = asks(
        &dir,
        &[
            M,
            "bad=compose($m.operation,then=$m.operation)",
            "blocked=compose($bad.operation,then=$m.operation)",
            "plan=needed($blocked)",
        ],
    );
    let j = saved(&dir, &r, "partial", 2);
    let bad = answer(&j, "bad");
    assert_eq!(s(get(bad, "status")), "refuted");
    assert!(!has(get(bad, "outputs"), "operation"));
    assert!(!has(get(bad, "outputs"), "map"));
    assert_eq!(arr(get(bad, "evidence")).len(), 1);
    let evidence = value(&j, &arr(get(bad, "evidence"))[0]);
    assert_eq!(s(get(evidence, "kind")), "counterexample");
    assert_eq!(s(get(answer(&j, "blocked"), "status")), "undetermined");
    assert_eq!(s(get(answer(&j, "plan"), "status")), "established");
    std::fs::remove_dir_all(dir).unwrap();
    let dir = inputs("compose-refuted-alone", A);
    let r = asks(&dir, &[M, "bad=compose($m.operation,then=$m.operation)"]);
    saved(&dir, &r, "complete", 1);
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn static_compose_errors_are_usage_without_artifacts() {
    for (i, qs) in [
        vec![M, "c=compose($m.operation)"],
        vec![M, "c=compose($m.operation,then=$m.operation,extra=@v/m)"],
        vec![M, "c=compose($m.candidate,then=$m.operation)"],
        vec![M, "c=compose($unknown.operation,then=$m.operation)"],
        vec![
            M,
            "c=compose($m.operation,then=$m.operation,then=$m.operation)",
        ],
        vec![M, "c=compose($m.operation.word[1],then=$m.operation)"],
        vec![M, "c=compose($m.operation.name,then=$m.operation)"],
        vec![
            M,
            "p=evaluate(Reservations.emptyPath,s=@v/p)",
            "c=compose($m.operation,then=$p.value)",
        ],
        vec![
            M,
            "c=compose($m.operation,then=$alt.operation)",
            "alt=map(Reservations.Migration,on=@v/n,reading=Alternative)",
        ],
    ]
    .into_iter()
    .enumerate()
    {
        let dir = inputs(&format!("compose-static-{i}"), A);
        let r = asks(&dir, &qs);
        notified(&dir, &r, "invalid", 64);
        assert!(!dir.join("out").exists());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn valid_paths_are_distinguished_from_unimplemented_execution_and_cycles_keep_edges() {
    let dir = inputs("compose-path", A);
    let r = asks(
        &dir,
        &[
            "p=evaluate(Reservations.emptyPath,s=@v/p)",
            "c=compose($p.value,then=$p.value)",
        ],
    );
    notified(&dir, &r, "error", 70);
    std::fs::remove_dir_all(dir).unwrap();
    let dir = inputs("compose-cycle", A);
    let r = asks(
        &dir,
        &[
            M,
            "a=compose($b.operation,then=$m.operation)",
            "b=compose($a.operation,then=$m.operation)",
        ],
    );
    notified(&dir, &r, "invalid", 64);
    assert!(r.stdout.contains("cycle") && r.stdout.contains("a") && r.stdout.contains("b"));
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn aliases_and_reverse_order_keep_distinct_words_and_full_universe_actions() {
    let dir = inputs("compose-aliases", A);
    let r = asks(
        &dir,
        &[
            M,
            N,
            "mm=map(Reservations.Migration,on=@v/mm,reading=Reservations)",
            C,
            "alias=compose($mm.operation,then=$n.operation)",
            "reverse=compose($n.operation,then=$m.operation)",
        ],
    );
    let j = saved(&dir, &r, "complete", 0);
    let op = |id| value(&j, get(get(answer(&j, id), "outputs"), "operation"));
    let images = |id| get(value(&j, get(op(id), "action")), "images");
    assert_eq!(images("c"), images("alias"));
    for (id, expected) in [
        ("c", ["m", "n"]),
        ("alias", ["mm", "n"]),
        ("reverse", ["n", "m"]),
    ] {
        let word = arr(get(op(id), "word"))
            .iter()
            .map(|r| s(&arr(value(&j, r))[1]))
            .collect::<Vec<_>>();
        assert_eq!(word, expected);
    }
    let action = value(&j, get(op("reverse"), "action"));
    let universe = arr(get(value(&j, get(action, "universe")), "atoms"));
    for (atom, image) in universe.iter().zip(arr(get(action, "images"))) {
        if ["B", "r", "s", "f", "l", "t"].contains(&s(get(atom, "subject"))) {
            assert_eq!(atom, image);
        } else {
            assert_eq!(s(get(image, "subject")), "B");
            assert!(!has(image, "field"));
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn missing_producer_operations_keep_original_slots_and_needed_plan() {
    let map = A
        .lines()
        .filter(|l| !l.contains("\"id\":\"m-states\""))
        .collect::<Vec<_>>()
        .join("\n");
    let dir = inputs("compose-missing", &map);
    let r = asks(&dir, &[C, N, M, "plan=needed($c)"]);
    let j = saved(&dir, &r, "partial", 2);
    let a = answer(&j, "c");
    assert_eq!(s(get(a, "status")), "undetermined");
    assert!(!has(get(a, "outputs"), "operation"));
    let reasons = arr(get(a, "reasons"));
    assert!(
        reasons
            .iter()
            .any(|r| s(get(r, "code")) == "dependency_blocked")
    );
    assert!(reasons.iter().any(|r| {
        arr(get(r, "missing")).iter().any(|f| {
            s(get(f, "subject")) == "m" && s(get(f, "field")) == "Reservations.Migration.states"
        })
    }));
    let plan = value(&j, get(get(answer(&j, "plan"), "outputs"), "plan"));
    assert!(
        arr(get(plan, "requirements"))
            .iter()
            .any(|r| s(get(get(r, "field"), "subject")) == "m"
                && s(get(get(r, "field"), "field")) == "Reservations.Migration.states")
    );
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn dynamic_producer_projection_failure_survives_composition_and_needed() {
    let dir = inputs("compose-dynamic", A);
    let r = asks(
        &dir,
        &[
            "absentValue=evaluate(Reservations.absent,m=@v/m)",
            "m=map(Reservations.Migration,on=$absentValue.value.some,reading=Reservations)",
            N,
            C,
            "plan=needed($c)",
        ],
    );
    let j = saved(&dir, &r, "partial", 2);
    let c = answer(&j, "c");
    assert_eq!(s(get(c, "status")), "undetermined");
    assert!(
        arr(get(c, "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "condition_failed")
    );
    assert!(
        arr(get(c, "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "dependency_blocked")
    );
    let plan = value(&j, get(get(answer(&j, "plan"), "outputs"), "plan"));
    assert!(
        arr(get(plan, "blockers"))
            .iter()
            .any(|r| s(get(r, "code")) == "condition_failed")
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn omitted_composed_candidate_subject_is_a_dynamic_projection_failure() {
    for (i, path) in ["operation.candidate.subject", "map.candidate.subject"]
        .into_iter()
        .enumerate()
    {
        let dir = inputs(&format!("compose-omitted-subject-{i}"), A);
        let read = format!("read=evaluate(Reservations.sourceOf,m=$c.{path})");
        let mapped =
            format!("mapped=map(Reservations.Migration,on=$c.{path},reading=Reservations)");
        let r = asks(
            &dir,
            &[
                M,
                N,
                C,
                &read,
                &mapped,
                "readPlan=needed($read)",
                "mapPlan=needed($mapped)",
            ],
        );
        let j = saved(&dir, &r, "partial", 2);
        for id in ["m", "n", "c"] {
            let a = answer(&j, id);
            assert_eq!(s(get(a, "status")), "established");
            assert!(has(get(a, "outputs"), "operation"));
        }
        for (id, plan_id) in [("read", "readPlan"), ("mapped", "mapPlan")] {
            let a = answer(&j, id);
            assert_eq!(s(get(a, "status")), "undetermined");
            let reasons = arr(get(a, "reasons"));
            let condition = reasons
                .iter()
                .find(|r| s(get(r, "code")) == "condition_failed")
                .unwrap();
            let details = get(condition, "details");
            assert_eq!(s(get(details, "construction")), "projection");
            let proposition = node(&j, get(details, "condition"));
            assert_eq!(s(get(get(proposition, "judgment"), "status")), "refuted");
            assert!(reasons
                .iter()
                .any(|r| s(get(r, "code")) == "dependency_blocked"));
            let plan_answer = answer(&j, plan_id);
            assert_eq!(s(get(plan_answer, "status")), "established");
            let plan = value(&j, get(get(plan_answer, "outputs"), "plan"));
            assert!(arr(get(plan, "blockers"))
                .iter()
                .any(|r| s(get(r, "code")) == "condition_failed"));
            assert!(!has(get(a, "outputs"), "operation"));
        }
        let op = value(&j, get(get(answer(&j, "c"), "outputs"), "operation"));
        assert!(!has(value(&j, get(op, "candidate")), "subject"));
        std::fs::remove_dir_all(dir).unwrap();
    }
}
