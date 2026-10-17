//! 三入力から有限木の変換と全Z域の保存を追う。
#[path = "common/engine.rs"]
mod engine;
use archsig::observed::ObservedEvaluation;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{InputSources, check_inputs},
    },
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn inputs(wrappers: bool, missing: bool, revision: Option<&str>) -> InputSources {
    InputSources::from_bytes(
        vec![engine::DEFINITIONS.to_vec()],
        engine::law(wrappers),
        engine::map(missing, revision),
    )
}
fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(x) = j else {
        panic!("object {j:?}")
    };
    x
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(x) = j else {
        panic!("array {j:?}")
    };
    x
}
fn text(j: &Json) -> &str {
    let Json::Str(x) = j else {
        panic!("text {j:?}")
    };
    x
}
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    &obj(j)[k]
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn original_status(subject: &str, wanted: &str) -> ObservedEvaluation {
    let sources = inputs(false, false, None);
    let before = check_inputs(sources.clone(), &mut quiet()).unwrap();
    let query = format!("a=check(Engine.preserves,c=@engine/{subject})");
    let r = evaluate_observed_bytes(sources, &[&query], &mut quiet()).unwrap();
    assert_eq!(
        r.prepared().inputs().metadata_wire(),
        before.metadata_wire()
    );
    unchanged(&before, r.prepared().inputs());
    let w = r.wire();
    assert_eq!(
        f(answer(&w, "a"), "status"),
        &Json::str(wanted),
        "answer {:?}",
        answer(&w, "a")
    );
    assert_eq!(f(&w, "status"), &Json::str("complete"));
    audit(&r, None);
    assert_universal(&r, subject);
    r
}
#[test]
fn engine_original_bytes_preserves_add_over_all_z() {
    let _ = original_status("add", "established");
}
#[test]
fn engine_original_bytes_refutes_subtract_over_all_z() {
    let r = original_status("subtract", "refuted");
    check_counterexample(&r);
}

fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    let id = text(f(r, "node"));
    arr(f(w, "nodes"))
        .iter()
        .find(|n| text(f(n, "id")) == id)
        .unwrap()
}
fn val(n: &Json) -> &Json {
    assert_eq!(f(n, "state"), &Json::str("value"));
    f(n, "value")
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(text(&m["node"]).into()),
        Json::Obj(m) => {
            for v in m.values() {
                refs(v, out)
            }
        }
        Json::Arr(xs) => {
            for x in xs {
                refs(x, out)
            }
        }
        _ => {}
    }
}
fn nodes<'a>(w: &'a Json, a: &Json) -> Vec<&'a Json> {
    let ns: BTreeMap<_, _> = arr(f(w, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect();
    let mut todo = vec![];
    refs(a, &mut todo);
    let mut seen = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if seen.insert(id.clone()) {
            refs(ns[id.as_str()], &mut todo)
        }
    }
    arr(f(w, "nodes"))
        .iter()
        .filter(|n| seen.contains(text(f(n, "id"))))
        .collect()
}
fn audit(r: &ObservedEvaluation, revision: Option<&str>) {
    let w = r.wire();
    let ns: BTreeMap<_, _> = arr(f(&w, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect();
    let mut seen = BTreeSet::new();
    for n in arr(f(&w, "nodes")) {
        let mut rs = vec![];
        refs(n, &mut rs);
        assert!(rs.iter().all(|r| seen.contains(r.as_str())), "{n:?}");
        assert!(seen.insert(text(f(n, "id"))));
        if f(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if let Some(v) = obj(n).get("value") {
            let mut rs = vec![];
            refs(v, &mut rs);
            for r in rs {
                assert_eq!(f(ns[r.as_str()], "state"), &Json::str("value"));
                assert!(!obj(ns[r.as_str()]).contains_key("partial"));
            }
        }
        if f(n, "type") == &Json::str("Expression") && f(val(n), "kind") == &Json::str("source") {
            let l = f(val(n), "location");
            assert_eq!(f(l, "input"), &Json::str("law"));
            let sp = arr(f(l, "span"));
            let [Json::Nat(a), Json::Nat(b)] = sp else {
                panic!("span")
            };
            let raw = r.prepared().inputs().sources().law().bytes();
            assert!(*a < *b && (*b as usize) <= raw.len());
        }
        for fact in arr(f(n, "support")) {
            let m = r.prepared().inputs().archmap();
            let snap = m
                .snapshots
                .iter()
                .find(|s| s.id == text(f(fact, "snapshot")))
                .unwrap();
            let subject = snap
                .subjects
                .iter()
                .find(|s| s.id == text(f(fact, "subject")))
                .unwrap();
            let origin = if let Some(field) = obj(fact).get("field") {
                let slot = &subject
                    .fields
                    .iter()
                    .find(|x| x.name == text(field))
                    .unwrap()
                    .slot;
                let archsig::archmap::Slot::Known {
                    atom,
                    origin,
                    pointer,
                    ..
                } = slot
                else {
                    panic!("missing is not support")
                };
                assert_eq!(f(fact, "atom"), &Json::str(atom));
                assert!(pointer.starts_with("/snapshots/0/atoms/"));
                origin
            } else {
                &subject.origin
            };
            let origin = m.origins.iter().find(|o| &o.id == origin).unwrap();
            assert_eq!(origin.mode, archsig::archmap::Mode::Specification);
            if let Some(rev) = revision {
                assert!(!origin.locations.is_empty());
                for l in &origin.locations {
                    let source = m.sources.iter().find(|s| s.id == l.source).unwrap();
                    assert_eq!(source.uri, "urn:fixture:engine");
                    assert_eq!(source.revision, rev);
                }
            }
        }
    }
    for a in arr(f(&w, "answers")) {
        let mut rs = vec![];
        refs(a, &mut rs);
        assert!(rs.iter().all(|r| ns.contains_key(r.as_str())));
        if let Some(claim) = obj(a).get("claim") {
            let claim = node(&w, claim);
            assert_eq!(f(a, "status"), f(f(claim, "judgment"), "status"));
        }
    }
}
fn assert_universal(r: &ObservedEvaluation, subject: &str) {
    let w = r.wire();
    let a = answer(&w, "a");
    let scope = f(a, "scope");
    assert_eq!(f(scope, "domain"), &Json::str("all_assignments"));
    let qs = arr(f(scope, "quantifiers"));
    let x = qs.iter().find(|q| f(q, "name") == &Json::str("x")).unwrap();
    assert_eq!(f(x, "type"), &Json::str("Z"));
    assert_eq!(f(x, "kind"), &Json::str("forall"));
    let d = node(&w, f(x, "domain"));
    assert_eq!(
        val(d),
        &Json::obj([("kind", Json::str("type")), ("type", Json::str("Z"))])
    );
    let reachable = nodes(&w, a);
    let norms: Vec<_> = reachable
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("normalization")
        })
        .collect();
    assert!(!norms.is_empty());
    let residuals: Vec<_> = reachable
        .iter()
        .filter(|n| f(n, "type") == &Json::str("Evaluation"))
        .filter(|n| {
            let e = node(&w, f(val(n), "expression"));
            obj(val(e)).get("operation") == Some(&Json::str("difference"))
        })
        .collect();
    assert!(!residuals.is_empty());
    assert!(
        residuals
            .iter()
            .any(|n| obj(val(n)).get("value").is_some_and(
                |v| val(node(&w, v)) == &Json::str(if subject == "add" { "0" } else { "-2" })
            ))
    );
    for field in ["Engine.Compiler.source", "Engine.Compiler.operator"] {
        assert!(reachable.iter().any(|n| {
            arr(f(n, "support")).iter().any(|s| {
                obj(s).get("field") == Some(&Json::str(field))
                    && f(s, "subject") == &Json::str(subject)
            })
        }));
    }
}
fn tree(tag: &str, args: Vec<Json>) -> Json {
    Json::obj([("tag", Json::str(tag)), ("args", Json::Arr(args))])
}
fn ir(add: bool) -> Json {
    let op = if add { "Plus" } else { "Minus" };
    tree(
        op,
        vec![
            tree("Load", vec![]),
            tree(
                op,
                vec![
                    tree("Const", vec![Json::str("1")]),
                    tree("Const", vec![Json::str("2")]),
                ],
            ),
        ],
    )
}
fn value<'a>(w: &'a Json, id: &str, ty: Json) -> &'a Json {
    let a = answer(w, id);
    assert_eq!(f(a, "status"), &Json::str("established"));
    let n = node(w, f(f(a, "outputs"), "value"));
    assert_eq!(f(n, "type"), &ty);
    val(n)
}
fn interp(t: &Json, x: &BigInt) -> BigInt {
    let args = arr(f(t, "args"));
    match text(f(t, "tag")) {
        "Var" | "Load" => x.clone(),
        "Lit" | "Const" => text(&args[0]).parse().unwrap(),
        "Add" | "Plus" => interp(&args[0], x) + interp(&args[1], x),
        "Minus" => interp(&args[0], x) - interp(&args[1], x),
        other => panic!("unknown constructor {other}"),
    }
}
fn check_counterexample(r: &ObservedEvaluation) {
    let w = r.wire();
    let all = nodes(&w, answer(&w, "a"));
    let es: Vec<_> = all
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("counterexample")
        })
        .collect();
    assert_eq!(es.len(), 1);
    let e = es[0];
    let d = f(val(e), "data");
    let b = arr(f(d, "bindings"))
        .iter()
        .find(|b| f(b, "name") == &Json::str("x"))
        .unwrap();
    let assigned = node(&w, f(b, "value"));
    assert_eq!(f(assigned, "type"), &Json::str("Z"));
    let x: BigInt = text(val(assigned)).parse().unwrap();
    let map = r.prepared().inputs().archmap();
    let source = &map.snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == "subtract")
        .unwrap()
        .fields
        .iter()
        .find(|f| f.name == "Engine.Compiler.source")
        .unwrap()
        .slot;
    let archsig::archmap::Slot::Known {
        value: original, ..
    } = source
    else {
        panic!("source")
    };
    let expected = [
        ("left", interp(&ir(false), &x)),
        ("right", interp(&original.canonical_json(), &x)),
    ];
    assert_ne!(expected[0].1, expected[1].1);
    for (key, n) in expected {
        let evaluation = node(&w, f(d, key));
        assert_eq!(f(evaluation, "type"), &Json::str("Evaluation"));
        let v = node(&w, f(val(evaluation), "value"));
        assert_eq!(f(v, "type"), &Json::str("Z"));
        assert_eq!(val(v), &Json::str(n.to_string()));
        let expr = node(&w, f(val(evaluation), "expression"));
        assert_eq!(f(val(expr), "operation"), &Json::str("substitute"));
        assert!(arr(f(val(expr), "bindings")).contains(b));
    }
}
#[test]
fn engine_generated_ir_and_recursive_views_keep_original_parts_and_facts() {
    let asks = [
        "ir=evaluate(Engine.generated,c=@engine/subtract)",
        "source=evaluate(Engine.sourceAt,c=@engine/subtract)",
        "target=evaluate(Engine.irAt,c=@engine/subtract)",
    ];
    let r = evaluate_observed_bytes(inputs(true, false, Some("r1")), &asks, &mut quiet()).unwrap();
    assert_eq!(r.status(), "complete");
    audit(&r, Some("r1"));
    let w = r.wire();
    assert_eq!(
        value(
            &w,
            "ir",
            Json::Arr(vec![Json::str("Data"), Json::str("Engine.IR")])
        ),
        &ir(false)
    );
    assert_eq!(value(&w, "source", Json::str("Z")), &Json::str("8"));
    assert_eq!(value(&w, "target", Json::str("Z")), &Json::str("6"));
    let law = r.prepared().inputs().law();
    for name in ["Engine.evalSource", "Engine.translate", "Engine.evalIR"] {
        let archsig::law::model::Signature::View { body, .. } = &law.declarations[name].signature
        else {
            panic!("view")
        };
        let span = law.exprs[*body].span;
        assert!(
            arr(f(&w, "nodes"))
                .iter()
                .filter(|n| f(n, "type") == &Json::str("Evaluation"))
                .any(|n| {
                    arr(f(val(n), "parts")).iter().any(|p| {
                        f(f(p, "location"), "span")
                            == &Json::Arr(vec![Json::Nat(span.0 as u64), Json::Nat(span.1 as u64)])
                    })
                })
        );
    }
}
#[test]
fn engine_operator_missing_keeps_subject_source_and_differing_completions_undetermined() {
    let src = inputs(false, true, None);
    let before = check_inputs(src.clone(), &mut quiet()).unwrap();
    let r = evaluate_observed_bytes(
        src,
        &["a=check(Engine.preserves,c=@engine/add)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    audit(&r, None);
    assert_eq!(
        r.prepared().inputs().metadata_wire(),
        before.metadata_wire()
    );
    unchanged(&before, r.prepared().inputs());
    let w = r.wire();
    let a = answer(&w, "a");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
    let reasons = arr(f(a, "reasons"));
    assert!(reasons.iter().any(|r| {
        f(r, "code") == &Json::str("missing_observation")
            && arr(f(r, "missing")).iter().any(|m| {
                f(m, "snapshot") == &Json::str("engine")
                    && f(m, "subject") == &Json::str("add")
                    && f(m, "field") == &Json::str("Engine.Compiler.operator")
            })
    }));
    let pairs: Vec<_> = nodes(&w, a)
        .into_iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("completion_pair")
        })
        .collect();
    assert_eq!(pairs.len(), 1);
    let d = f(val(pairs[0]), "data");
    assert_ne!(
        val(node(&w, f(d, "first_result"))),
        val(node(&w, f(d, "second_result")))
    );
}

fn unchanged(
    before: &archsig::observed::input::CheckedInputs,
    after: &archsig::observed::input::CheckedInputs,
) {
    assert_eq!(
        format!("{:?}", before.definitions()),
        format!("{:?}", after.definitions())
    );
    assert_eq!(format!("{:?}", before.law()), format!("{:?}", after.law()));
    assert_eq!(
        format!("{:?}", before.archmap()),
        format!("{:?}", after.archmap())
    );
    assert_eq!(
        format!("{:?}", before.sources()),
        format!("{:?}", after.sources())
    );
}
#[test]
fn engine_generated_add_ir_preserves_input_bytes_and_all_three_checked_tables() {
    let src = inputs(true, false, Some("r1"));
    let before = check_inputs(src.clone(), &mut quiet()).unwrap();
    let r = evaluate_observed_bytes(
        src,
        &["ir=evaluate(Engine.generated,c=@engine/add)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    unchanged(&before, r.prepared().inputs());
    audit(&r, Some("r1"));
    assert_eq!(
        value(
            &r.wire(),
            "ir",
            Json::Arr(vec![Json::str("Data"), Json::str("Engine.IR")])
        ),
        &ir(true)
    );
}
#[test]
fn engine_provenance_pair_keeps_the_same_universal_judgment_and_current_source() {
    let run = |revision| {
        evaluate_observed_bytes(
            inputs(false, false, Some(revision)),
            &["a=check(Engine.preserves,c=@engine/subtract)"],
            &mut quiet(),
        )
        .unwrap()
    };
    let first = run("r1");
    let second = run("r2");
    audit(&first, Some("r1"));
    audit(&second, Some("r2"));
    assert_eq!(f(&first.wire(), "answers"), f(&second.wire(), "answers"));
    assert_ne!(
        first.prepared().inputs().metadata_wire(),
        second.prepared().inputs().metadata_wire()
    );
    check_counterexample(&first);
    check_counterexample(&second);
}
#[test]
fn engine_unknown_source_tree_keeps_missing_and_is_never_a_finite_type_sample() {
    let original = String::from_utf8(engine::map(false, None)).unwrap();
    let line = original
        .lines()
        .find(|l| l.contains("\"add-source\""))
        .unwrap();
    let map = original
        .replace(&(line.to_string() + "\n"), "")
        .into_bytes();
    let src = InputSources::from_bytes(
        vec![engine::DEFINITIONS.to_vec()],
        engine::LAW.to_vec(),
        map,
    );
    let before = check_inputs(src.clone(), &mut quiet()).unwrap();
    let r = evaluate_observed_bytes(
        src,
        &["a=check(Engine.preserves,c=@engine/add)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    unchanged(&before, r.prepared().inputs());
    audit(&r, None);
    let w = r.wire();
    let a = answer(&w, "a");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(arr(f(a, "reasons")).iter().any(|r| {
        f(r, "code") == &Json::str("missing_observation")
            && arr(f(r, "missing"))
                .iter()
                .any(|m| f(m, "field") == &Json::str("Engine.Compiler.source"))
    }));
    assert!(
        !arr(f(&w, "nodes"))
            .iter()
            .any(|n| f(n, "type") == &Json::str("Domain")
                && obj(val(n)).get("type")
                    == Some(&Json::Arr(vec![
                        Json::str("Data"),
                        Json::str("Engine.Expr")
                    ])))
    );
}
#[test]
fn engine_universal_match_tracks_selected_comparison_and_qualified_zero_constructor() {
    let r = evaluate_observed_bytes(
        inputs(true, false, None),
        &[
            "add=check(Engine.matched,c=@engine/add)",
            "subtract=check(Engine.matched,c=@engine/subtract)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    audit(&r, None);
    let w = r.wire();
    assert_eq!(f(answer(&w, "add"), "status"), &Json::str("established"));
    assert_eq!(f(answer(&w, "subtract"), "status"), &Json::str("refuted"));
    assert!(arr(f(&w, "nodes")).iter().any(|n| f(n, "type")
        == &Json::Arr(vec![Json::str("Data"), Json::str("Engine.IR")])
        && val(n) == &tree("Load", vec![])));
}
