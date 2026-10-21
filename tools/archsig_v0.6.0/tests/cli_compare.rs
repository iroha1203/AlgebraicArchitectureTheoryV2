//! 公開word/action比較を独立した原始入力と明示期待値で検査する。
mod common;
#[path = "common/public_path_compose.rs"]
mod fixture;
use archsig::json::JNode;
use common::cli::*;
use std::path::{Path, PathBuf};
fn inputs(name: &str) -> PathBuf {
    let dir = workdir(name);
    let input = fixture::input(false, "public-compare");
    std::fs::write(dir.join("d.json"), input.definitions()[0].bytes()).unwrap();
    std::fs::write(dir.join("l.law"), input.law().bytes()).unwrap();
    std::fs::write(dir.join("a.json"), input.archmap().bytes()).unwrap();
    dir
}
fn asks(dir: &Path, qs: &[&str]) -> Run {
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
    for q in qs {
        args.extend(["--ask", q]);
    }
    run(dir, &args)
}
fn answer<'a>(j: &'a JNode, id: &str) -> &'a JNode {
    arr(get(j, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn node<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    arr(get(j, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(r, "node")))
        .unwrap()
}
#[test]
fn path_aliases_have_different_words_and_equal_actions() {
    let dir = inputs("compare-path-alias");
    let r = asks(
        &dir,
        &[
            "e=evaluate(Walk.step,e=@v/e)",
            "alias=evaluate(Walk.step,e=@v/alias)",
            "word=compare($e.value,to=$alias.value,kind=word)",
            "action=compare($e.value,to=$alias.value,kind=action)",
            "plan=needed($word)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), "complete");
    let j = result_json(&dir, &r);
    for (id, status, predicate) in [
        ("word", "refuted", "word_equal"),
        ("action", "established", "action_equal"),
    ] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), status);
        let comparison = node(&j, get(get(a, "outputs"), "comparison"));
        assert_eq!(s(get(comparison, "type")), "Comparison");
        assert_eq!(s(get(get(comparison, "value"), "kind")), id);
        let p = node(&j, get(get(a, "outputs"), "proposition"));
        assert_eq!(s(get(get(p, "value"), "predicate")), predicate);
    }
    assert_eq!(s(get(answer(&j, "plan"), "status")), "established");
    std::fs::remove_dir_all(dir).unwrap();
}
fn saved(dir: &Path, r: &Run, status: &str, code: i32) -> JNode {
    assert_eq!(r.code, code, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), status);
    let j = result_json(dir, r);
    assert_eq!(s(get(&j, "status")), status);
    assert_eq!(num(get(&j, "exit_code")), code as u64);
    j
}
fn value<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    get(node(j, r), "value")
}
const M: &str = "m=map(Reservations.Migration,on=@v/m,reading=Reservations)";
const N: &str = "n=map(Reservations.Migration,on=@v/n,reading=Reservations)";
fn operation_inputs(name: &str) -> PathBuf {
    let dir = workdir(name);
    for (name, bytes) in [
        (
            "d.json",
            include_bytes!("fixtures/reservations.atoms.json").as_slice(),
        ),
        (
            "l.law",
            include_bytes!("fixtures/public-compose.law").as_slice(),
        ),
        (
            "a.json",
            include_bytes!("fixtures/configuration-operation.archmap.json").as_slice(),
        ),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
#[test]
fn operation_aliases_keep_named_words_and_equal_full_actions() {
    let dir = operation_inputs("compare-operation-alias");
    let r = asks(
        &dir,
        &[
            M,
            "alias=map(Reservations.Migration,on=@v/mm,reading=Reservations)",
            "word=compare($m.operation,to=$alias.operation,kind=word)",
            "action=compare($m.operation,to=$alias.operation,kind=action)",
            "plan=needed($word)",
        ],
    );
    let j = saved(&dir, &r, "complete", 1);
    for (id, status) in [("word", "refuted"), ("action", "established")] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), status);
        let c = value(&j, get(get(a, "outputs"), "comparison"));
        assert_eq!(
            get(c, "left"),
            get(get(answer(&j, "m"), "outputs"), "operation")
        );
        assert_eq!(
            get(c, "right"),
            get(get(answer(&j, "alias"), "outputs"), "operation")
        );
    }
    let a = answer(&j, "word");
    let e = value(&j, &arr(get(a, "evidence"))[0]);
    let data = get(e, "data");
    for field in ["bindings", "paths", "facts"] {
        assert!(arr(get(data, field)).is_empty());
    }
    assert_eq!(
        get(data, "left"),
        get(get(answer(&j, "m"), "outputs"), "operation")
    );
    assert_eq!(s(get(answer(&j, "plan"), "status")), "established");
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn path_action_compares_the_whole_universe_and_keeps_a_concrete_counterexample() {
    let dir = inputs("compare-path-whole-u");
    let r = asks(
        &dir,
        &[
            fixture::E,
            fixture::F,
            fixture::C,
            "direct=evaluate(Walk.step,e=@v/different)",
            "a=compare($c.operation,to=$direct.value,kind=action)",
        ],
    );
    let j = saved(&dir, &r, "complete", 1);
    let a = answer(&j, "a");
    assert_eq!(s(get(a, "status")), "refuted");
    let data = get(value(&j, &arr(get(a, "evidence"))[0]), "data");
    // p↦r agrees at the selected source; q↦r versus q↦q distinguishes total maps.
    let facts = arr(get(data, "facts"));
    assert_eq!(facts.len(), 3);
    for (fact, subject) in facts.iter().zip(["q", "r", "q"]) {
        assert_eq!(s(get(fact, "snapshot")), "v");
        assert_eq!(s(get(fact, "subject")), subject);
        assert!(!has(fact, "field"));
    }
    assert_eq!(
        get(data, "left"),
        get(get(answer(&j, "c"), "outputs"), "operation")
    );
    assert_eq!(
        get(data, "right"),
        get(get(answer(&j, "direct"), "outputs"), "value")
    );
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn flattened_path_words_remove_identities_but_keep_named_self_steps() {
    let dir = inputs("compare-path-words");
    let r = asks(
        &dir,
        &[
            fixture::E,
            fixture::F,
            fixture::C,
            "ident=evaluate(Walk.identityAt,x=@v/p)",
            "same=compose($ident.value,then=$c.operation)",
            "nested=evaluate(Walk.join,e=@v/e,f=@v/next)",
            "flat=compare($same.operation,to=$nested.value,kind=word)",
            "looped=evaluate(Walk.step,e=@v/self)",
            "identity_action=compare($looped.value,to=$ident.value,kind=action)",
            "identity_word=compare($looped.value,to=$ident.value,kind=word)",
        ],
    );
    let j = saved(&dir, &r, "complete", 1);
    for (id, status) in [
        ("flat", "established"),
        ("identity_action", "established"),
        ("identity_word", "refuted"),
    ] {
        assert_eq!(s(get(answer(&j, id), "status")), status);
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn flattened_operation_words_are_independent_of_association() {
    let dir = operation_inputs("compare-operation-flat");
    let r = asks(
        &dir,
        &[
            M,
            N,
            "a=compose($m.operation,then=$n.operation)",
            "left=compose($a.operation,then=$m.operation)",
            "b=compose($n.operation,then=$m.operation)",
            "right=compose($m.operation,then=$b.operation)",
            "word=compare($left.operation,to=$right.operation,kind=word)",
            "action=compare($left.operation,to=$right.operation,kind=action)",
        ],
    );
    let j = saved(&dir, &r, "complete", 0);
    for id in ["word", "action"] {
        assert_eq!(s(get(answer(&j, id), "status")), "established");
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn actual_action_endpoint_mismatch_is_a_checked_construction_refutation() {
    for operation in [false, true] {
        let dir = if operation {
            operation_inputs("compare-operation-endpoints")
        } else {
            inputs("compare-path-endpoints")
        };
        let qs = if operation {
            vec![
                M,
                N,
                "bad=compare($m.operation,to=$n.operation,kind=action)",
                "plan=needed($bad)",
            ]
        } else {
            vec![
                fixture::E,
                fixture::F,
                "bad=compare($e.value,to=$f.value,kind=action)",
                "plan=needed($bad)",
            ]
        };
        let r = asks(&dir, &qs);
        let j = saved(&dir, &r, "complete", 1);
        let a = answer(&j, "bad");
        assert_eq!(s(get(a, "status")), "refuted");
        assert!(!has(get(a, "outputs"), "comparison"));
        let claim = node(&j, get(get(a, "outputs"), "proposition"));
        assert_eq!(s(get(get(claim, "value"), "predicate")), "constructible");
        assert_eq!(arr(get(get(claim, "value"), "operands")).len(), 3);
        let data = get(value(&j, &arr(get(a, "evidence"))[0]), "data");
        for field in ["bindings", "paths", "facts"] {
            assert!(arr(get(data, field)).is_empty());
        }
        assert_ne!(get(data, "left"), get(data, "right"));
        assert_eq!(s(get(answer(&j, "plan"), "status")), "established");
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn static_compare_errors_notify_usage_without_artifacts() {
    for (i, q) in [
        "bad=compare($e.value,kind=word)",
        "bad=compare($e.value,to=$e.value)",
        "bad=compare($e.value,to=$e.value,kind=unknown)",
        "bad=compare($e.value,to=$e.value,kind=word,along=$e.value)",
        "bad=compare($e.value,to=$e.value,kind=diagnostics)",
        "bad=compare($e.value,to=$e.value,kind=word,extra=$e.value)",
        "bad=compare(@v/e,to=$e.value,kind=word)",
        "bad=compare($e,to=$e.value,kind=word)",
        "bad=compare($e.value,to=$unknown.value,kind=word)",
        "bad=compare($bad.comparison,to=$e.value,kind=word)",
        "bad=compare($e.value,to=$e.value,kind=word,kind=action)",
        "bad=compare($e.evaluation,to=$e.value,kind=word)",
        "bad=compare($e.value,to=$e.value,kind=$e.value)",
    ]
    .iter()
    .enumerate()
    {
        let dir = inputs(&format!("compare-usage-{i}"));
        let r = asks(&dir, &[fixture::E, q]);
        notified(&dir, &r, "invalid", 64);
        assert!(!dir.join("out").exists());
        std::fs::remove_dir_all(dir).unwrap();
    }
    let dir = operation_inputs("compare-mixed-usage");
    let r = asks(
        &dir,
        &[
            M,
            "p=evaluate(Reservations.route,e=@v/e)",
            "bad=compare($m.operation,to=$p.value,kind=word)",
        ],
    );
    notified(&dir, &r, "invalid", 64);
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn comparison_records_have_no_public_subfields() {
    for field in ["left", "right", "kind", "word", "images"] {
        let dir = inputs(&format!("compare-private-{field}"));
        let q = format!("bad=compare($a.comparison.{field},to=$e.value,kind=word)");
        let r = asks(
            &dir,
            &[fixture::E, "a=compare($e.value,to=$e.value,kind=word)", &q],
        );
        notified(&dir, &r, "invalid", 64);
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn forward_and_conditional_path_handles_keep_dependencies_and_missing_reasons() {
    let dir = inputs("compare-forward");
    let r = asks(
        &dir,
        &[
            "a=compare($wrapped.value.some[0],to=$e.value,kind=word)",
            "wrapped=evaluate(Walk.wrapped,p=$e.value)",
            fixture::E,
        ],
    );
    let j = saved(&dir, &r, "complete", 0);
    assert_eq!(s(get(answer(&j, "a"), "status")), "established");
    std::fs::remove_dir_all(dir).unwrap();
    for missing in [false, true] {
        let dir = inputs(&format!("compare-unavailable-{missing}"));
        if missing {
            let input = fixture::input(true, "public-compare");
            std::fs::write(dir.join("a.json"), input.archmap().bytes()).unwrap();
        }
        let qs = if missing {
            vec![
                fixture::E,
                "a=compare($e.value,to=$e.value,kind=action)",
                "plan=needed($a)",
            ]
        } else {
            vec![
                "e=evaluate(Walk.absentPath,e=@v/e)",
                "a=compare($e.value.some,to=$e.value.some,kind=word)",
                "plan=needed($a)",
            ]
        };
        let r = asks(&dir, &qs);
        let j = saved(&dir, &r, "partial", 2);
        let a = answer(&j, "a");
        assert_eq!(s(get(a, "status")), "undetermined");
        assert!(!has(get(a, "outputs"), "comparison"));
        assert!(!arr(get(a, "reasons")).is_empty());
        assert_eq!(s(get(answer(&j, "plan"), "status")), "established");
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn reused_comparison_is_recomputed_after_forged_kind_or_input_changes() {
    let dir = inputs("compare-reuse");
    let qs = [
        fixture::E,
        "alias=evaluate(Walk.step,e=@v/alias)",
        "a=compare($e.value,to=$alias.value,kind=word)",
    ];
    let first = asks(&dir, &qs);
    let original = saved(&dir, &first, "complete", 1);
    let path = dir.join(s(get(&first.receipt, "result")));
    let raw = std::fs::read_to_string(&path).unwrap();
    let changed = raw.replace("\"kind\":\"word\"", "\"kind\":\"action\"");
    assert_ne!(raw, changed);
    std::fs::write(&path, changed).unwrap();
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "again",
        "--reuse",
        "out",
    ];
    for q in qs {
        args.extend(["--ask", q]);
    }
    let r = run(&dir, &args);
    let j = saved(&dir, &r, "complete", 1);
    assert_eq!(num(get(get(&j, "reuse"), "accepted_nodes")), 0);
    assert!(!arr(get(get(&j, "reuse"), "rejected")).is_empty());
    assert_eq!(get(&j, "nodes"), get(&original, "nodes"));
    assert_eq!(get(&j, "answers"), get(&original, "answers"));
    // A provenance revision invalidates the hint; current primitives are rechecked.
    let input = fixture::input(false, "new-revision");
    std::fs::write(dir.join("a.json"), input.archmap().bytes()).unwrap();
    args[8] = "fresh";
    let r = run(&dir, &args);
    let j = saved(&dir, &r, "complete", 1);
    assert_eq!(num(get(get(&j, "reuse"), "accepted_nodes")), 0);
    assert_eq!(s(get(answer(&j, "a"), "status")), "refuted");
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn empty_words_across_snapshots_match_but_action_requires_actual_endpoints() {
    let dir = inputs("compare-snapshot-identities");
    let r = asks(
        &dir,
        &[
            "p=evaluate(Walk.identityAt,x=@v/p)",
            "q=evaluate(Walk.identityAt,x=@w/p)",
            "word=compare($p.value,to=$q.value,kind=word)",
            "action=compare($p.value,to=$q.value,kind=action)",
        ],
    );
    let j = saved(&dir, &r, "complete", 1);
    assert_eq!(s(get(answer(&j, "word"), "status")), "established");
    assert_eq!(s(get(answer(&j, "action"), "status")), "refuted");
    assert!(!has(get(answer(&j, "action"), "outputs"), "comparison"));
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn comparison_rejects_static_tuple_bounds_and_action_reading_mismatches() {
    let dir = inputs("compare-static-tuple");
    let r = asks(
        &dir,
        &[
            "e=evaluate(Walk.nested,e=@v/e)",
            "a=compare($e.value.some[0][9],to=$e.value.some[0][1],kind=word)",
        ],
    );
    notified(&dir, &r, "invalid", 64);
    std::fs::remove_dir_all(dir).unwrap();
    let dir = operation_inputs("compare-reading");
    let r = asks(
        &dir,
        &[
            M,
            "alt=map(Reservations.Migration,on=@v/m,reading=Alternative)",
            "a=compare($m.operation,to=$alt.operation,kind=action)",
        ],
    );
    notified(&dir, &r, "invalid", 64);
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn comparison_dynamic_index_failure_keeps_original_condition_and_needed() {
    let dir = inputs("compare-dynamic-index");
    let r = asks(
        &dir,
        &[
            fixture::E,
            "wrapped=evaluate(Walk.wrapped,p=$e.value)",
            "a=compare($wrapped.value.some[99],to=$e.value,kind=word)",
            "plan=needed($a)",
        ],
    );
    let j = saved(&dir, &r, "partial", 2);
    assert_eq!(s(get(answer(&j, "a"), "status")), "undetermined");
    let reasons = arr(get(answer(&j, "a"), "reasons"));
    assert!(reasons
        .iter()
        .any(|r| s(get(r, "code")) == "condition_failed"));
    assert!(reasons
        .iter()
        .any(|r| s(get(r, "code")) == "dependency_blocked"));
    assert_eq!(s(get(answer(&j, "plan"), "status")), "established");
    std::fs::remove_dir_all(dir).unwrap();
}
