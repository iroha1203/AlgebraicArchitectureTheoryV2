//! 原始構造値の公開比較を独立入力と明示期待値で検査する。
mod common;
use archsig::json::JNode;
use common::cli::*;
use std::path::{Path, PathBuf};
const D: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const L: &str = include_str!("fixtures/counter.law");
const A: &str = include_str!("fixtures/counter.archmap.json");
fn inputs(name: &str) -> PathBuf {
    let dir = workdir(name);
    let law=L.replace("view amount(s: State): Z = s.count;","view amount(s: State): Z = s.count;\nview next(s:State):Z=s.count+1;\nview no(s:State):Bool=false;");
    for (name, bytes) in [
        ("d.json", D),
        ("l.law", law.as_bytes()),
        ("a.json", A.as_bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
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
        .find(|n| get(n, "id") == get(r, "node"))
        .unwrap()
}
#[test]
fn value_comparison_distinguishes_equal_values_refutations_and_false_bool_values() {
    let dir = inputs("compare-values-numbers");
    let r = asks(
        &dir,
        &[
            "n=evaluate(CountCheck.amount,s=@v/s)",
            "next=evaluate(CountCheck.next,s=@v/s)",
            "no=evaluate(CountCheck.no,s=@v/s)",
            "same=compare($n.value,to=$n.value,kind=value)",
            "different=compare($n.value,to=$next.value,kind=value)",
            "false_value=compare($no.value,to=$no.value,kind=value)",
            "plan=needed($different)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), "complete");
    let j = result_json(&dir, &r);
    for (id, status) in [
        ("same", "established"),
        ("different", "refuted"),
        ("false_value", "established"),
        ("plan", "established"),
    ] {
        assert_eq!(s(get(answer(&j, id), "status")), status);
    }
    for id in ["same", "different", "false_value"] {
        let a = answer(&j, id);
        let c = node(&j, get(get(a, "outputs"), "comparison"));
        assert_eq!(s(get(c, "type")), "Comparison");
        assert_eq!(s(get(get(c, "value"), "kind")), "value");
        let p = node(&j, get(get(a, "outputs"), "proposition"));
        assert_eq!(s(get(get(p, "value"), "predicate")), "equal");
    }
    let a = answer(&j, "different");
    let e = node(&j, &arr(get(a, "evidence"))[0]);
    let data = get(get(e, "value"), "data");
    assert_eq!(
        get(data, "left"),
        get(get(answer(&j, "n"), "outputs"), "value")
    );
    assert_eq!(
        get(data, "right"),
        get(get(answer(&j, "next"), "outputs"), "value")
    );
    std::fs::remove_dir_all(dir).unwrap();
}
#[path = "common/compare_values.rs"]
mod primitive;
fn structured_inputs(name: &str, missing: bool, extra: &str) -> PathBuf {
    let dir = workdir(name);
    let src = primitive::input(missing, extra);
    for (name, bytes) in [
        ("d.json", src.definitions()[0].bytes()),
        ("l.law", src.law().bytes()),
        ("a.json", src.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
#[test]
fn all_ground_primitive_types_follow_value_semantics_and_keep_original_refs() {
    let dir = structured_inputs("compare-values-structure", false, "");
    let mut qs = vec![];
    for (name, _, _, _) in primitive::FIELDS {
        qs.push(format!("a_{name}=evaluate(Values.{name},s=@v/a)"));
        qs.push(format!("b_{name}=evaluate(Values.{name},s=@v/b)"));
        qs.push(format!(
            "c_{name}=compare($a_{name}.value,to=$b_{name}.value,kind=value)"
        ));
    }
    qs.extend(
        [
            "same_ref=compare(@v/a,to=@v/a,kind=value)",
            "different_ref=compare(@v/a,to=@v/b,kind=value)",
            "snapshot_ref=compare(@v/a,to=@w/a,kind=value)",
            "component=compare($a_vpair.value[0],to=$b_vpair.value[0],kind=value)",
        ]
        .map(str::to_owned),
    );
    let r = asks(&dir, &qs.iter().map(String::as_str).collect::<Vec<_>>());
    let j = saved(&dir, &r, "complete", 1);
    for (name, _, _, _) in primitive::FIELDS {
        let a = answer(&j, &format!("c_{name}"));
        assert_eq!(
            s(get(a, "status")),
            if *name == "vlist" {
                "refuted"
            } else {
                "established"
            },
            "{name}"
        );
        let c = node(&j, get(get(a, "outputs"), "comparison"));
        let v = get(c, "value");
        assert_eq!(
            get(v, "left"),
            get(get(answer(&j, &format!("a_{name}")), "outputs"), "value")
        );
        assert_eq!(
            get(v, "right"),
            get(get(answer(&j, &format!("b_{name}")), "outputs"), "value")
        );
        assert!(!arr(get(c, "support")).is_empty());
    }
    for (id, status) in [
        ("same_ref", "established"),
        ("different_ref", "refuted"),
        ("snapshot_ref", "refuted"),
        ("component", "established"),
    ] {
        assert_eq!(s(get(answer(&j, id), "status")), status);
    }
    assert!(arr(get(get(answer(&j, "same_ref"), "scope"), "readings")).is_empty());
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn value_comparison_rejects_invalid_handles_types_and_arguments_without_artifacts() {
    for q in [
        "x=compare(@v/no,to=@v/a,kind=value)",
        "x=compare($missing.value,to=@v/a,kind=value)",
        "n=evaluate(Values.vinteger,s=@v/a);x=compare($n.value,to=@v/a,kind=value)",
        "n=evaluate(Values.vinteger,s=@v/a);x=compare($n.value,to=$n.value,kind=value,along=@v/a)",
        "x=compare(@v/a,to=@v/a,kind=value,to=@v/b)",
        "x=compare(@v/a,to=@v/a,kind=value,foo=bar)",
        "n=evaluate(Values.vpair,s=@v/a);x=compare($n.value[3],to=$n.value[0],kind=value)",
        "x=compare($y.comparison,to=$y.comparison,kind=value);y=compare($x.comparison,to=$x.comparison,kind=value)",
        "x=compare(@v/a,to=@v/b,kind=value);y=compare($x.comparison.left,to=@v/a,kind=value)",
    ] {
        let dir=structured_inputs("compare-values-reject",false,"");
        let r=asks(&dir,&q.split(';').collect::<Vec<_>>());
        assert_eq!(r.code,64,"{q}: {}",r.stdout);
        assert_eq!(s(get(&r.receipt,"status")),"invalid");
        assert!(!dir.join("out").exists());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn value_comparison_missing_and_dynamic_projection_keep_needed_and_independent_results() {
    let dir = structured_inputs(
        "compare-values-missing",
        true,
        "view short():List<Z> = list<Z>[]; view no():Option<Z> = none<Z>;",
    );
    let r = asks(
        &dir,
        &[
            "c=compare($a.value,to=$b.value,kind=value)",
            "a=evaluate(Values.vinteger,s=@v/a)",
            "b=evaluate(Values.vinteger,s=@v/b)",
            "known=compare(@v/a,to=@v/a,kind=value)",
            "short=evaluate(Values.short)",
            "index=compare($short.value[0],to=$a.value,kind=value)",
            "absent=evaluate(Values.no)",
            "projected=compare($absent.value.some,to=$a.value,kind=value)",
            "plan=needed($c)",
            "index_plan=needed($index)",
            "some_plan=needed($projected)",
        ],
    );
    let j = saved(&dir, &r, "partial", 2);
    assert_eq!(s(get(answer(&j, "known"), "status")), "established");
    for id in ["c", "index", "projected"] {
        assert_eq!(s(get(answer(&j, id), "status")), "undetermined");
        assert!(!has(get(answer(&j, id), "outputs"), "comparison"));
        assert!(!arr(get(answer(&j, id), "reasons")).is_empty());
    }
    for id in ["plan", "index_plan", "some_plan"] {
        assert_eq!(s(get(answer(&j, id), "status")), "established");
    }
    let text = std::fs::read_to_string(dir.join(s(get(&r.receipt, "result")))).unwrap();
    assert!(text.contains("dependency_blocked") && text.contains("Values.Sample.vinteger"));
    assert!(text.contains("condition_failed"));
    std::fs::remove_dir_all(dir).unwrap();
}

fn saved(dir: &Path, r: &Run, status: &str, code: i32) -> JNode {
    assert_eq!(r.code, code, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), status);
    assert_eq!(num(get(&r.receipt, "exit_code")), code as u64);
    let j = result_json(dir, r);
    assert_eq!(s(get(&j, "command")), "run");
    assert_eq!(s(get(&j, "status")), status);
    assert_eq!(num(get(&j, "exit_code")), code as u64);
    j
}
#[test]
fn different_ground_values_keep_constructor_arguments_empty_values_and_exact_types() {
    let dir = structured_inputs(
        "compare-values-differences",
        false,
        r#"
view zero():Z=0;
view yes():Bool=true;
view otherq():Q=-rat(1,3);
view otherf():Fp(5)=0;
view othert():Text="日本語";
view otherpair():(Z,Bool)=(1,false);
view emptylist():List<Z> = list<Z>[];
view emptyset():Set<Z> = set<Z>{};
view present():Option<Z> = some(0);
view emptydata():Packet=Empty;
view otherdata():Packet=Full(8);
view copied(s:Sample):Sample=s;
"#,
    );
    let mut qs = vec![];
    for (field, other) in [
        ("vinteger", "zero"),
        ("vflag", "yes"),
        ("vrational", "otherq"),
        ("vresidue", "otherf"),
        ("vtext", "othert"),
        ("vpair", "otherpair"),
        ("vlist", "emptylist"),
        ("vset", "emptyset"),
        ("voption", "present"),
        ("vpacket", "emptydata"),
    ] {
        qs.push(format!("a_{field}=evaluate(Values.{field},s=@v/a)"));
        qs.push(format!("b_{field}=evaluate(Values.{other})"));
        qs.push(format!(
            "c_{field}=compare($a_{field}.value,to=$b_{field}.value,kind=value)"
        ));
    }
    qs.extend(
        [
            "ctor=evaluate(Values.otherdata)",
            "ctor_difference=compare($a_vpacket.value,to=$ctor.value,kind=value)",
            "copy=evaluate(Values.copied,s=@v/a)",
            "copy_comparison=compare(@v/a,to=$copy.value,kind=value)",
        ]
        .map(str::to_owned),
    );
    let r = asks(&dir, &qs.iter().map(String::as_str).collect::<Vec<_>>());
    let j = saved(&dir, &r, "complete", 1);
    for (id, _) in qs
        .iter()
        .filter_map(|q| q.split_once('='))
        .filter(|(id, _)| id.starts_with("c_") || *id == "ctor_difference")
    {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), "refuted", "{id}");
        assert_eq!(arr(get(a, "evidence")).len(), 1);
        let e = node(&j, &arr(get(a, "evidence"))[0]);
        let data = get(get(e, "value"), "data");
        for key in ["bindings", "paths", "left", "right", "facts"] {
            assert!(has(data, key));
        }
    }
    assert_eq!(
        s(get(answer(&j, "copy_comparison"), "status")),
        "established"
    );
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn reused_value_comparison_rejects_forgery_and_recomputes_current_observations() {
    let dir = inputs("compare-values-reuse");
    let qs = [
        "n=evaluate(CountCheck.amount,s=@v/s)",
        "m=evaluate(CountCheck.next,s=@v/s)",
        "c=compare($n.value,to=$m.value,kind=value)",
    ];
    let first = asks(&dir, &qs);
    let original = saved(&dir, &first, "complete", 1);
    let path = dir.join(s(get(&first.receipt, "result")));
    let raw = std::fs::read_to_string(&path).unwrap();
    let forged = raw.replace("\"kind\":\"value\"", "\"kind\":\"word\"");
    assert_ne!(raw, forged);
    std::fs::write(&path, forged).unwrap();
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
    std::fs::write(
        dir.join("a.json"),
        A.replace("\"value\": \"2\"", "\"value\": \"3\""),
    )
    .unwrap();
    args[8] = "fresh";
    let r = run(&dir, &args);
    let j = saved(&dir, &r, "complete", 1);
    assert_eq!(num(get(get(&j, "reuse"), "accepted_nodes")), 0);
    assert_eq!(s(get(answer(&j, "c"), "status")), "refuted");
    assert_ne!(get(&j, "nodes"), get(&original, "nodes"));
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn false_bool_value_comparison_alone_is_successful_and_argument_order_is_canonical() {
    let mut prior: Option<JNode> = None;
    for q in [
        "c=compare($no.value,to=$no.value,kind=value)",
        "c=compare($no.value,kind=value,to=$no.value)",
    ] {
        let dir = inputs("compare-values-false-only");
        let r = asks(&dir, &["no=evaluate(CountCheck.no,s=@v/s)", q]);
        let j = saved(&dir, &r, "complete", 0);
        assert_eq!(s(get(answer(&j, "c"), "status")), "established");
        let req = &arr(get(&j, "requests"))[1];
        assert_eq!(s(get(req, "text")), q);
        assert_eq!(
            arr(get(req, "arguments"))
                .iter()
                .map(|a| s(get(a, "name")))
                .collect::<Vec<_>>(),
            ["kind", "to"]
        );
        if let Some(p) = &prior {
            assert_eq!(get(p, "nodes"), get(&j, "nodes"));
            assert_eq!(get(p, "answers"), get(&j, "answers"));
        } else {
            prior = Some(j);
        }
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[path = "common/public_path_compose.rs"]
mod paths;
#[test]
fn value_comparison_rejects_paths_instead_of_equating_their_display_or_action() {
    let dir = workdir("compare-value-path-rejection");
    let input = paths::input(false, "value-static");
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("l.law", input.law().bytes()),
        ("a.json", input.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let r = asks(
        &dir,
        &[paths::E, "bad=compare($e.value,to=$e.value,kind=value)"],
    );
    assert_eq!(r.code, 64, "{}", r.stdout);
    assert!(!dir.join("out").exists());
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn dynamic_primitive_projection_types_are_checked_after_selecting_constructor_values() {
    let dir=structured_inputs("compare-values-dynamic-types",false,"view flagged():Packet=Flag(false); view empty():Packet=Empty; view seven():Z=7; view no():Bool=false;");
    let r = asks(
        &dir,
        &[
            "full=evaluate(Values.vpacket,s=@v/a)",
            "flagged=evaluate(Values.flagged)",
            "empty=evaluate(Values.empty)",
            "z=evaluate(Values.seven)",
            "b=evaluate(Values.no)",
            "left=compare($full.value[0],to=$z.value,kind=value)",
            "right=compare($z.value,to=$full.value[0],kind=value)",
            "both=compare($full.value[0],to=$full.value[0],kind=value)",
            "false_value=compare($flagged.value[0],to=$b.value,kind=value)",
            "false_pair=compare($flagged.value[0],to=$flagged.value[0],kind=value)",
            "mismatch=compare($full.value[0],to=$flagged.value[0],kind=value)",
            "wrong_branch=compare($full.value[0],to=$b.value,kind=value)",
            "no_argument=compare($empty.value[0],to=$z.value,kind=value)",
            "plan=needed($mismatch)",
            "branch_plan=needed($wrong_branch)",
            "empty_plan=needed($no_argument)",
        ],
    );
    let j = saved(&dir, &r, "partial", 2);
    for id in [
        "left",
        "right",
        "both",
        "false_value",
        "false_pair",
        "plan",
        "branch_plan",
        "empty_plan",
    ] {
        assert_eq!(s(get(answer(&j, id), "status")), "established", "{id}");
    }
    for id in ["mismatch", "wrong_branch", "no_argument"] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), "undetermined", "{id}");
        assert!(!has(get(a, "outputs"), "comparison"));
        let reasons = arr(get(a, "reasons"));
        assert!(reasons
            .iter()
            .any(|x| s(get(x, "code")) == "condition_failed"));
        assert!(reasons
            .iter()
            .any(|x| s(get(x, "code")) == "dependency_blocked"));
    }
    let p = node(&j, get(get(answer(&j, "left"), "outputs"), "comparison"));
    let selected = node(&j, get(get(p, "value"), "left"));
    assert_eq!(s(get(selected, "type")), "Z");
    assert_eq!(s(get(selected, "value")), "7");
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn head_only_inapplicable_projection_keeps_partial_reasons_needed_and_known_results() {
    for (view, head) in [("absent", "$x.value.some"), ("emptyrefs", "$x.value[0]")] {
        for reverse in [false, true] {
            let dir=structured_inputs("compare-values-head-projection",false,"view absent():Option<Sample> = none<Sample>; view emptyrefs():List<Sample> = list<Sample>[];");
            let x = format!("x=evaluate(Values.{view})");
            let q = if reverse {
                format!("c=compare(@v/a,to={head},kind=value)")
            } else {
                format!("c=compare({head},to=@v/a,kind=value)")
            };
            let r = asks(
                &dir,
                &[
                    &x,
                    &q,
                    "known=compare(@v/a,to=@v/a,kind=value)",
                    "plan=needed($c)",
                ],
            );
            let j = saved(&dir, &r, "partial", 2);
            let a = answer(&j, "c");
            assert_eq!(s(get(a, "status")), "undetermined");
            assert!(!has(get(a, "outputs"), "comparison"));
            for kind in ["condition_failed", "dependency_blocked"] {
                assert!(arr(get(a, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == kind));
            }
            for id in ["known", "plan"] {
                assert_eq!(s(get(answer(&j, id), "status")), "established");
            }
            std::fs::remove_dir_all(dir).unwrap();
        }
    }
}
#[test]
fn dynamic_path_generator_projection_is_a_primitive_reference_value() {
    let dir = workdir("compare-values-path-generator");
    let i = paths::input(false, "value-generator");
    for (name, bytes) in [
        ("d.json", i.definitions()[0].bytes()),
        ("l.law", i.law().bytes()),
        ("a.json", i.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let r = asks(
        &dir,
        &[
            paths::E,
            "a=compare($e.value.generators[0],to=@v/e,kind=value)",
            "b=compare(@v/e,to=$e.value.generators[0],kind=value)",
            "c=compare($e.value.generators[0],to=$e.value.generators[0],kind=value)",
        ],
    );
    let j = saved(&dir, &r, "complete", 0);
    for id in ["a", "b", "c"] {
        assert_eq!(s(get(answer(&j, id), "status")), "established");
    }
    std::fs::remove_dir_all(dir).unwrap();
}
