//! 公開Path合成を独立の原始fixtureと明示期待値で検査する。
mod common;
#[path = "common/public_path_compose.rs"]
mod fixture;
use archsig::json::JNode;
use common::cli::*;
use fixture::{C, E, F};
use std::path::{Path, PathBuf};
fn inputs(name: &str, missing: bool) -> PathBuf {
    let d = workdir(name);
    let i = fixture::input(missing, "public-path");
    std::fs::write(d.join("d.json"), i.definitions()[0].bytes()).unwrap();
    std::fs::write(d.join("l.law"), i.law().bytes()).unwrap();
    std::fs::write(d.join("a.json"), i.archmap().bytes()).unwrap();
    d
}
fn asks(d: &Path, qs: &[&str]) -> Run {
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
    run(d, &args)
}
fn saved(d: &Path, r: &Run, status: &str, code: i32) -> JNode {
    assert_eq!(r.code, code, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), status);
    let j = result_json(d, r);
    assert_eq!(s(get(&j, "status")), status);
    assert_eq!(num(get(&j, "exit_code")), code as u64);
    j
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
fn value<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    get(node(j, r), "value")
}
#[test]
fn public_path_composition_preserves_words_refs_endpoints_and_following_bindings() {
    let d = inputs("path-compose", false);
    let r = asks(
        &d,
        &[
            C,
            F,
            E,
            "s=evaluate(Walk.step,e=@v/self)",
            "cc=compose($s.value,then=$c.operation)",
            "read=evaluate(Walk.first,e=$cc.operation.generators[1])",
            "echo=evaluate(Walk.keep,p=$cc.operation)",
        ],
    );
    let j = saved(&d, &r, "complete", 0);
    assert_eq!(
        arr(get(&j, "answers"))
            .iter()
            .map(|a| s(get(a, "id")))
            .collect::<Vec<_>>(),
        ["c", "f", "e", "s", "cc", "read", "echo"]
    );
    for (id, names) in [("c", vec!["e", "next"]), ("cc", vec!["self", "e", "next"])] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), "established");
        let outputs = get(a, "outputs");
        assert!(!has(outputs, "map"));
        let op = get(outputs, "operation");
        let path = value(&j, op);
        assert_eq!(s(&arr(get(node(&j, op), "type"))[0]), "Path");
        assert_eq!(s(get(path, "reading")), "Walk");
        assert_eq!(s(&arr(value(&j, get(path, "source")))[1]), "p");
        assert_eq!(s(&arr(value(&j, get(path, "target")))[1]), "r");
        assert_eq!(
            arr(get(path, "generators"))
                .iter()
                .map(|r| s(&arr(value(&j, r))[1]))
                .collect::<Vec<_>>(),
            names
        );
        assert_eq!(arr(get(node(&j, op), "conditions")).len(), 1);
        assert_eq!(
            &arr(get(node(&j, op), "conditions"))[0],
            get(outputs, "proposition")
        );
        let claim = value(&j, get(outputs, "proposition"));
        assert_eq!(s(value(&j, &arr(get(claim, "operands"))[0])), "composition");
    }
    assert_eq!(
        s(&arr(value(&j, get(get(answer(&j, "read"), "outputs"), "value")))[1]),
        "p"
    );
    std::fs::remove_dir_all(d).unwrap();
}
#[test]
fn path_endpoint_refutations_block_dependents_and_needed_keeps_the_condition() {
    let d = inputs("path-refuted", false);
    let r = asks(
        &d,
        &[
            E,
            "bad=compose($e.value,then=$e.value)",
            "blocked=compose($bad.operation,then=$e.value)",
            "plan=needed($blocked)",
        ],
    );
    let j = saved(&d, &r, "partial", 2);
    let bad = answer(&j, "bad");
    assert_eq!(s(get(bad, "status")), "refuted");
    assert!(!has(get(bad, "outputs"), "operation"));
    let proof = value(&j, &arr(get(bad, "evidence"))[0]);
    let data = get(proof, "data");
    assert!(arr(get(data, "facts")).is_empty());
    let archsig::json::JValue::Obj(fields) = &data.value else {
        panic!()
    };
    let mut keys = fields
        .iter()
        .map(|(key, _)| key.as_str())
        .collect::<Vec<_>>();
    keys.sort();
    assert_eq!(keys, ["bindings", "facts", "left", "paths", "right"]);

    assert_eq!(s(&arr(value(&j, get(data, "left")))[1]), "q");
    assert_eq!(s(&arr(value(&j, get(data, "right")))[1]), "p");
    for id in ["bad", "blocked"] {
        let reasons = arr(get(answer(&j, id), "reasons"));
        let failed = reasons
            .iter()
            .find(|r| s(get(r, "code")) == "condition_failed")
            .unwrap();
        assert_eq!(
            s(get(get(failed, "details"), "construction")),
            "composition"
        );
    }
    assert_eq!(s(get(answer(&j, "plan"), "status")), "established");
    std::fs::remove_dir_all(d).unwrap();
    let d = inputs("path-refuted-alone", false);
    let r = asks(&d, &[E, "bad=compose($e.value,then=$e.value)"]);
    saved(&d, &r, "complete", 1);
    std::fs::remove_dir_all(d).unwrap();
}
#[test]
fn optional_path_projections_compose_and_absent_paths_keep_dynamic_reasons() {
    for absent in [false, true] {
        let d = inputs("path-option", false);
        let q = if absent {
            "p=evaluate(Walk.absentPath,e=@v/e)"
        } else {
            "p=evaluate(Walk.maybe,e=@v/e)"
        };
        let r = asks(
            &d,
            &[
                q,
                F,
                "c=compose($p.value.some,then=$f.value)",
                "plan=needed($c)",
            ],
        );
        let j = saved(
            &d,
            &r,
            if absent { "partial" } else { "complete" },
            if absent { 2 } else { 0 },
        );
        let c = answer(&j, "c");
        assert_eq!(
            s(get(c, "status")),
            if absent {
                "undetermined"
            } else {
                "established"
            }
        );
        if absent {
            let reasons = arr(get(c, "reasons"));
            assert!(reasons
                .iter()
                .any(|r| s(get(r, "code")) == "condition_failed"));
            assert!(reasons
                .iter()
                .any(|r| s(get(r, "code")) == "dependency_blocked"));
        }
        std::fs::remove_dir_all(d).unwrap();
    }
}
#[test]
fn path_identities_flatten_without_erasing_named_self_or_alias_generators() {
    let d = inputs("path-identities", false);
    let r = asks(
        &d,
        &[
            E,
            F,
            "i=evaluate(Walk.identityAt,x=@v/p)",
            "j=evaluate(Walk.identityAt,x=@v/q)",
            "left=compose($i.value,then=$e.value)",
            "right=compose($e.value,then=$j.value)",
            "empty=compose($i.value,then=$i.value)",
            "s=evaluate(Walk.step,e=@v/self)",
            "selfWord=compose($s.value,then=$e.value)",
            "alias=evaluate(Walk.step,e=@v/alias)",
            "aliasWord=compose($alias.value,then=$f.value)",
        ],
    );
    let j = saved(&d, &r, "complete", 0);
    for (id, names) in [
        ("left", vec!["e"]),
        ("right", vec!["e"]),
        ("empty", vec![]),
        ("selfWord", vec!["self", "e"]),
        ("aliasWord", vec!["alias", "next"]),
    ] {
        let path = value(&j, get(get(answer(&j, id), "outputs"), "operation"));
        assert_eq!(
            arr(get(path, "generators"))
                .iter()
                .map(|r| s(&arr(value(&j, r))[1]))
                .collect::<Vec<_>>(),
            names
        );
    }
    std::fs::remove_dir_all(d).unwrap();
}
#[test]
fn path_missing_producers_preserve_original_slots_through_needed() {
    let d = inputs("path-missing", true);
    let r = asks(&d, &[E, F, C, "plan=needed($c)"]);
    let j = saved(&d, &r, "partial", 2);
    let c = answer(&j, "c");
    assert_eq!(s(get(c, "status")), "undetermined");
    assert!(!has(get(c, "outputs"), "operation"));
    assert!(arr(get(c, "reasons"))
        .iter()
        .any(|r| s(get(r, "code")) == "dependency_blocked"));
    let plan = value(&j, get(get(answer(&j, "plan"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).iter().any(|r| {
        let f = get(r, "field");
        s(get(f, "snapshot")) == "v"
            && s(get(f, "subject")) == "e"
            && s(get(f, "field")) == "Paths.Hop.to"
    }));
    std::fs::remove_dir_all(d).unwrap();
}
#[test]
fn path_private_fields_static_types_and_cycles_fail_without_artifacts() {
    for (i, qs) in [
        vec![E, F, "c=compose($e.value,then=$f.value.source)"],
        vec![E, F, C, "q=evaluate(Walk.keep,p=$c.operation.name)"],
        vec![
            E,
            "a=compose($b.operation,then=$e.value)",
            "b=compose($a.operation,then=$e.value)",
        ],
    ]
    .into_iter()
    .enumerate()
    {
        let d = inputs(&format!("path-usage-{i}"), false);
        let r = asks(&d, &qs);
        notified(&d, &r, "invalid", 64);
        assert!(!d.join("out").exists());
        if i == 2 {
            assert!(r.stdout.contains("cycle") && r.stdout.contains("a") && r.stdout.contains("b"));
        }
        std::fs::remove_dir_all(d).unwrap();
    }
}
#[test]
fn path_reuse_rejects_changed_reading_and_recomputes_current_nodes() {
    let d = inputs("path-reuse", false);
    let first = asks(&d, &[E, F, C]);
    let original = saved(&d, &first, "complete", 0);
    let path = d.join(s(get(&first.receipt, "result")));
    let raw = std::fs::read_to_string(&path).unwrap();
    let changed = raw.replace("\"reading\":\"Walk\"", "\"reading\":\"Forged\"");
    assert_ne!(raw, changed);
    std::fs::write(&path, changed).unwrap();
    let r = run(
        &d,
        &[
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
            "--ask",
            E,
            "--ask",
            F,
            "--ask",
            C,
        ],
    );
    let j = saved(&d, &r, "complete", 0);
    assert!(!arr(get(get(&j, "reuse"), "rejected")).is_empty());
    assert_eq!(num(get(get(&j, "reuse"), "accepted_nodes")), 0);
    assert_eq!(get(&j, "nodes"), get(&original, "nodes"));
    assert_eq!(get(&j, "answers"), get(&original, "answers"));
    std::fs::remove_dir_all(d).unwrap();
}

#[test]
fn composed_paths_inside_containers_keep_the_original_typed_ref() {
    let d = inputs("path-container", false);
    let r = asks(
        &d,
        &[
            E,
            F,
            C,
            "wrapped=evaluate(Walk.wrapped,p=$c.operation)",
            "i=evaluate(Walk.identityAt,x=@v/r)",
            "again=compose($wrapped.value.some[0],then=$i.value)",
        ],
    );
    let j = saved(&d, &r, "complete", 0);
    let original = get(get(answer(&j, "c"), "outputs"), "operation");
    let wrapped = value(&j, get(get(answer(&j, "wrapped"), "outputs"), "value"));
    let list = value(&j, get(wrapped, "some"));
    assert_eq!(&arr(list)[0], original);
    let again = value(&j, get(get(answer(&j, "again"), "outputs"), "operation"));
    assert_eq!(
        arr(get(again, "generators"))
            .iter()
            .map(|r| s(&arr(value(&j, r))[1]))
            .collect::<Vec<_>>(),
        ["e", "next"]
    );
    std::fs::remove_dir_all(d).unwrap();
}

#[test]
fn reservations_path_and_identity_compose_from_shared_primitive_inputs() {
    let d = workdir("path-reservations");
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
        std::fs::write(d.join(name), bytes).unwrap();
    }
    let r = asks(
        &d,
        &[
            "p=evaluate(Reservations.route,e=@v/e)",
            "i=evaluate(Reservations.emptyPath,s=@v/q)",
            "c=compose($p.value,then=$i.value)",
        ],
    );
    let j = saved(&d, &r, "complete", 0);
    let path = value(&j, get(get(answer(&j, "c"), "outputs"), "operation"));
    assert_eq!(s(&arr(value(&j, get(path, "source")))[1]), "p");
    assert_eq!(s(&arr(value(&j, get(path, "target")))[1]), "q");
    assert_eq!(arr(get(path, "generators")).len(), 1);
    assert_eq!(s(&arr(value(&j, &arr(get(path, "generators"))[0]))[1]), "e");
    std::fs::remove_dir_all(d).unwrap();
}
fn visibility_inputs(name: &str) -> PathBuf {
    let dir = workdir(name);
    let input = fixture::visibility_input();
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("l.law", input.law().bytes()),
        ("a.json", input.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
#[test]
fn composition_rejects_generators_outside_its_reading_and_preserves_the_reason() {
    let dir = visibility_inputs("path-invisible");
    let r = asks(
        &dir,
        &[
            "p=evaluate(Reservations.route,e=@v/e)",
            "q=evaluate(Alternative.route,e=@v/h)",
            "bad=compose($p.value,then=$q.value)",
            "blocked=compose($bad.operation,then=$p.value)",
            "plan=needed($blocked)",
        ],
    );
    let j = saved(&dir, &r, "partial", 2);
    for id in ["p", "q"] {
        assert_eq!(s(get(answer(&j, id), "status")), "established");
    }
    let bad = answer(&j, "bad");
    assert_eq!(s(get(bad, "status")), "refuted");
    assert!(!has(get(bad, "outputs"), "operation"));
    let proof = value(&j, &arr(get(bad, "evidence"))[0]);
    let data = get(proof, "data");
    assert!(arr(get(data, "facts")).is_empty());
    assert_eq!(
        s(&arr(get(node(&j, get(data, "left")), "type"))[1]),
        "Hidden.Hop"
    );
    assert_eq!(s(value(&j, get(data, "right"))), "Reservations");
    assert_eq!(s(get(answer(&j, "blocked"), "status")), "undetermined");
    let plan = value(&j, get(get(answer(&j, "plan"), "outputs"), "plan"));
    assert!(arr(get(plan, "blockers"))
        .iter()
        .any(|r| s(get(r, "code")) == "condition_failed"));
    std::fs::remove_dir_all(dir).unwrap();
    let dir = visibility_inputs("path-invisible-alone");
    let r = asks(
        &dir,
        &[
            "p=evaluate(Reservations.route,e=@v/e)",
            "q=evaluate(Alternative.route,e=@v/h)",
            "bad=compose($p.value,then=$q.value)",
        ],
    );
    saved(&dir, &r, "complete", 1);
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn different_readings_with_visible_words_keep_the_selected_reading() {
    for (i, p, q, reading) in [
        (
            0,
            "p=evaluate(Reservations.route,e=@v/e)",
            "q=evaluate(Alternative.stay,s=@v/q)",
            "Reservations",
        ),
        (
            1,
            "p=evaluate(Alternative.common,e=@v/e)",
            "q=evaluate(Reservations.stay,s=@v/q)",
            "Alternative",
        ),
    ] {
        let dir = visibility_inputs(&format!("path-shared-reading-{i}"));
        let r = asks(&dir, &[p, q, "c=compose($p.value,then=$q.value)"]);
        let j = saved(&dir, &r, "complete", 0);
        let path = value(&j, get(get(answer(&j, "c"), "outputs"), "operation"));
        assert_eq!(s(get(path, "reading")), reading);
        assert_eq!(arr(get(path, "generators")).len(), 1);
        assert_eq!(s(&arr(value(&j, &arr(get(path, "generators"))[0]))[1]), "e");
        std::fs::remove_dir_all(dir).unwrap();
    }
}
