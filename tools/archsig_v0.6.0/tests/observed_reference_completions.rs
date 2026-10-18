mod common;
#[path = "common/reference_completions.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{InputSources, check_inputs},
    },
};
use std::collections::{BTreeMap, BTreeSet};
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(v) = j else {
        panic!("object {j:?}")
    };
    v
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(v) = j else {
        panic!("array {j:?}")
    };
    v
}
fn text(j: &Json) -> &str {
    let Json::Str(v) = j else {
        panic!("text {j:?}")
    };
    v
}
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    obj(j).get(k).unwrap_or_else(|| panic!("missing key {k}"))
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(v) if v.len() == 1 && v.contains_key("node") => out.push(text(&v["node"]).into()),
        Json::Obj(v) => {
            for j in v.values() {
                refs(j, out)
            }
        }
        Json::Arr(v) => {
            for j in v {
                refs(j, out)
            }
        }
        _ => {}
    }
}
fn nodes(j: &Json) -> BTreeMap<&str, &Json> {
    arr(f(j, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect()
}
fn answer<'a>(j: &'a Json, id: &str) -> &'a Json {
    arr(f(j, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn value<'a>(j: &'a Json, id: &str) -> &'a Json {
    let ns = nodes(j);
    f(
        ns[text(f(f(f(answer(j, id), "outputs"), "value"), "node"))],
        "value",
    )
}
fn run(i: InputSources, asks: &[&str]) -> Json {
    let checked =
        check_inputs(i.clone(), &mut quiet()).unwrap_or_else(|e| panic!("input {:?}", e.issues()));
    let r = evaluate_observed_bytes(i.clone(), asks, &mut quiet())
        .unwrap_or_else(|e| panic!("evaluate {e:?}"));
    assert_ne!(r.status(), "error", "{:?}", r.wire());
    assert_eq!(r.prepared().inputs().sources(), &i);
    assert_eq!(
        r.prepared().inputs().archmap().snapshots,
        checked.archmap().snapshots
    );
    assert_eq!(
        r.prepared().inputs().archmap().origins,
        checked.archmap().origins
    );
    assert_eq!(
        r.prepared().inputs().archmap().sources,
        checked.archmap().sources
    );
    let j = r.wire();
    let ns = nodes(&j);
    for a in arr(f(&j, "answers")) {
        if let Some(claim) = obj(a).get("claim") {
            let claim = ns[text(f(claim, "node"))];
            assert_eq!(f(claim, "type"), &Json::str("Proposition"));
            assert_eq!(f(f(claim, "judgment"), "status"), f(a, "status"));
            assert_eq!(f(claim, "scope"), f(a, "scope"));
        }
    }
    let mut earlier = BTreeSet::new();
    for n in arr(f(&j, "nodes")) {
        let mut links = vec![];
        refs(n, &mut links);
        assert!(
            links.iter().all(|s| earlier.contains(s)),
            "earlier {links:?}"
        );
        earlier.insert(text(f(n, "id")).to_string());
        if let Some(v) = obj(n).get("value") {
            let mut links = vec![];
            refs(v, &mut links);
            for l in links {
                assert_ne!(f(ns[l.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[l.as_str()]).contains_key("partial"));
            }
        }
        for fact in arr(f(n, "support")) {
            let snapshot = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == text(f(fact, "snapshot")))
                .unwrap();
            let subject = snapshot
                .subjects
                .iter()
                .find(|s| s.id == text(f(fact, "subject")))
                .unwrap();
            assert!(arr(f(f(n, "scope"), "snapshots")).contains(f(fact, "snapshot")));
            let origin = if let Some(field) = obj(fact).get("field") {
                let field = subject
                    .fields
                    .iter()
                    .find(|s| s.name == text(field))
                    .unwrap();
                match &field.slot {
                    archsig::archmap::Slot::Known { atom, origin, .. } => {
                        assert_eq!(f(fact, "atom"), &Json::str(atom));
                        origin
                    }
                    archsig::archmap::Slot::Missing => {
                        assert!(!obj(fact).contains_key("atom"));
                        &subject.origin
                    }
                }
            } else {
                &subject.origin
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            assert!(arr(f(f(n, "scope"), "modes")).contains(&Json::str(origin.mode.wire())));
            for location in &origin.locations {
                let source = checked
                    .archmap()
                    .sources
                    .iter()
                    .find(|s| s.id == location.source)
                    .unwrap();
                assert!(source.uri.starts_with("urn:fixture:"));
                assert!(!location.path.starts_with('/'));
                if source.revision == "r2" {
                    assert_eq!(location.span, Some((10, 11)));
                    assert!(source.uri.ends_with(":relocated"));
                }
            }
        }
    }
    j
}
fn completion_domains(j: &Json) -> Vec<&Json> {
    arr(f(j,"nodes")).iter().filter(|n|f(n,"type")==&Json::str("Domain")&&arr(f(n,"arguments")).first().is_some_and(|r|{let ns=nodes(j);let s=ns[text(f(r,"node"))];obj(s).get("value").is_some_and(|v|if let Json::Obj(m)=v {m.get("kind")} else {None}==Some(&Json::str("source")))})).collect()
}
#[test]
fn missing_reference_same_slot_is_shared_and_changed_values_keep_a_typed_pair() {
    let j = run(
        fixture::input(fixture::SCRIPT, false, false),
        &[
            "a=check(RefCalc.equal,s=@v/item)",
            "b=evaluate(RefCalc.choose,s=@v/item)",
            "c=evaluate(RefCalc.same_pair,s=@v/item)",
            "d=evaluate(RefCalc.ignore,s=@v/item)",
        ],
    );
    assert_eq!(f(answer(&j, "a"), "status"), &Json::str("established"));
    assert_eq!(f(answer(&j, "b"), "status"), &Json::str("undetermined"));
    assert_eq!(f(answer(&j, "c"), "status"), &Json::str("undetermined"));
    assert_eq!(value(&j, "d"), &Json::str("7"));
    let ns = nodes(&j);
    let pairs:Vec<_>=ns.values().filter(|n|obj(n).get("value").is_some_and(|v|if let Json::Obj(m)=v {m.get("kind")} else {None}==Some(&Json::str("completion_pair")))).collect();
    assert!(!pairs.is_empty());
    for pair in pairs {
        let data = f(f(pair, "value"), "data");
        let fields = arr(f(data, "fields"));
        assert_eq!(fields.len(), 1);
        assert_eq!(f(&fields[0], "snapshot"), &Json::str("v"));
        assert_eq!(f(&fields[0], "subject"), &Json::str("item"));
        assert_eq!(f(&fields[0], "field"), &Json::str("Refs.Sample.left"));
        let values: Vec<_> = ["first", "second"]
            .iter()
            .map(|k| {
                let rs = arr(f(data, k));
                assert_eq!(rs.len(), 1);
                let n = ns[text(f(&rs[0], "node"))];
                assert_eq!(
                    f(n, "type"),
                    &Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Root")])
                );
                f(n, "value")
            })
            .collect();
        assert_ne!(values[0], values[1]);
        for v in values {
            assert!([fixture::ref_value("v", "A"), fixture::ref_value("v", "B")].contains(v));
        }
        assert_eq!(f(f(pair, "scope"), "domain"), &Json::str("all_completions"));
    }

    let choices: BTreeSet<_> = ns
        .values()
        .filter(|n| f(n, "type") == &Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Root")]))
        .filter_map(|n| obj(n).get("value"))
        .filter(|v| matches!(v, Json::Arr(_)))
        .map(Json::canonical)
        .collect();
    assert!(
        choices.contains(&fixture::ref_value("v", "A").canonical())
            && choices.contains(&fixture::ref_value("v", "B").canonical())
    );
    let ds = completion_domains(&j);
    assert!(!ds.is_empty());
    for d in ds {
        assert_eq!(arr(f(f(d, "value"), "elements")).len(), 2);
    }
}
#[test]
fn missing_reference_independent_slots_and_cross_snapshot_candidates_keep_current_origin() {
    let asks = [
        "a=evaluate(RefCalc.compare,s=@v/item)",
        "b=check(RefCalc.differs,s=@v/item)",
    ];
    let a = run(fixture::input(fixture::SCRIPT, true, false), &asks);
    let b = run(fixture::input(fixture::SCRIPT, true, true), &asks);
    for j in [&a, &b] {
        assert_eq!(f(answer(j, "a"), "status"), &Json::str("undetermined"));
        assert_eq!(f(answer(j, "b"), "status"), &Json::str("refuted"));
        assert!(
            arr(f(j, "nodes"))
                .iter()
                .any(|n| obj(n).get("value") == Some(&fixture::ref_value("w", "C")))
        )
    }
    assert_eq!(f(answer(&a, "a"), "status"), f(answer(&b, "a"), "status"));
    assert_ne!(
        fixture::input(fixture::SCRIPT, true, false)
            .archmap()
            .bytes(),
        fixture::input(fixture::SCRIPT, true, true)
            .archmap()
            .bytes()
    );
    let ds = completion_domains(&a);
    assert!(
        ds.iter()
            .any(|d| arr(f(f(d, "value"), "elements")).len() == 9)
    );
    assert!(
        ds.iter()
            .any(|d| arr(f(f(d, "value"), "elements")).len() == 3)
    );
}
#[test]
fn missing_reference_known_map_constraints_force_only_consistent_owner_and_source() {
    for owner in [false, true] {
        let (ask, expected) = if owner {
            (
                "a=evaluate(Applications.owner,p=@v/p)",
                fixture::ref_value("v", "A"),
            )
        } else {
            (
                "a=evaluate(Applications.origin_ref,m=@v/m)",
                fixture::ref_value("v", "A"),
            )
        };
        let j = run(fixture::constrained(owner), &[ask]);
        assert_eq!(f(answer(&j, "a"), "status"), &Json::str("established"));
        assert_eq!(value(&j, "a"), &expected);
        let ds = completion_domains(&j);
        assert!(!ds.is_empty());
        for d in ds {
            assert_eq!(arr(f(f(d, "value"), "elements")).len(), 1);
        }
    }
}
#[test]
fn missing_reference_mixed_bool_completion_keeps_slot_types_and_known_counterexample() {
    let script = r#"view mixed(s:Sample):Bool=(s.left=s.owner) and s.flag;law required all(s:Sample):false and s.left=s.left;"#;
    let j = run(
        fixture::input(script, false, false),
        &[
            "a=evaluate(RefCalc.mixed,s=@v/item)",
            "b=check(RefCalc.all)",
        ],
    );
    assert_eq!(f(answer(&j, "a"), "status"), &Json::str("undetermined"));
    assert_eq!(f(answer(&j, "b"), "status"), &Json::str("refuted"));
    let ns = nodes(&j);
    let d = completion_domains(&j)
        .into_iter()
        .find(|n| {
            f(f(n, "value"), "type")
                == &Json::Arr(vec![
                    Json::str("Tuple"),
                    Json::str("Bool"),
                    Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Root")]),
                ])
        })
        .unwrap();
    assert_eq!(arr(f(f(d, "value"), "elements")).len(), 4);
    for r in arr(f(f(d, "value"), "elements")) {
        let n = ns[text(f(r, "node"))];
        let vs = arr(f(n, "value"));
        assert_eq!(vs.len(), 2);
        assert!(matches!(&vs[0], Json::Bool(_)));
        assert!([fixture::ref_value("v", "A"), fixture::ref_value("v", "B")].contains(&vs[1]));
    }
    assert!(ns.values().any(|n| obj(n).get("value").is_some_and(
        |v| matches!(v,Json::Obj(m)if m.get("kind")==Some(&Json::str("counterexample")))
    )));
}
#[test]
fn missing_reference_no_consistent_extension_is_rejected_at_original_map_location() {
    let i = fixture::constrained(false);
    let before = check_inputs(i.clone(), &mut quiet()).unwrap();
    let map = String::from_utf8(i.archmap().bytes().to_vec()).unwrap();
    let old = "[[[\"v\", \"p\"], [\"v\", \"r\"]], [[\"v\", \"q\"], [\"v\", \"s\"]]]";
    assert_eq!(map.matches(old).count(), 1);
    let map = map.replace(old, "[[[\"v\", \"p\"], [\"v\", \"r\"]]]");
    let invalid = InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        i.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let err = check_inputs(invalid, &mut quiet()).unwrap_err();
    assert_eq!(err.status().wire(), "invalid");
    let issues = err.issues();
    assert!(
        issues
            .iter()
            .any(|j| f(j, "code") == &Json::str("inconsistent_observation"))
    );
    let expected = before.archmap().snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == "m")
        .unwrap()
        .fields
        .iter()
        .find_map(|f| match &f.slot {
            archsig::archmap::Slot::Known { atom, pointer, .. } if atom == "m-states" => {
                Some(pointer)
            }
            _ => None,
        })
        .unwrap();
    for issue in issues {
        if f(issue, "code") == &Json::str("inconsistent_observation") {
            assert_eq!(f(f(issue, "location"), "pointer"), &Json::str(expected));
        }
    }
}
#[test]
fn missing_reference_joint_assignments_keep_known_map_source_and_target_constraints() {
    let j = run(
        fixture::constrained_joint(),
        &["a=evaluate(Applications.endpoints,m=@v/m)"],
    );
    assert_eq!(f(answer(&j, "a"), "status"), &Json::str("established"));
    assert_eq!(
        value(&j, "a"),
        &Json::Arr(vec![
            fixture::ref_value("v", "A"),
            fixture::ref_value("v", "B")
        ])
    );
    let ds = completion_domains(&j);
    assert_eq!(ds.len(), 1);
    assert_eq!(arr(f(f(ds[0], "value"), "elements")).len(), 1);
    let support = arr(f(ds[0], "support"));
    assert!(
        support
            .iter()
            .any(|s| obj(s).get("atom") == Some(&Json::str("m-states")))
    );
    assert!(
        support
            .iter()
            .any(|s| obj(s).get("atom") == Some(&Json::str("m-reserves")))
    );
}
#[test]
fn missing_reference_owner_expression_returns_the_known_actual_fiber_under_map_constraints() {
    let j = run(
        fixture::constrained(false),
        &["a=evaluate(Applications.members,m=@v/m)"],
    );
    assert_eq!(f(answer(&j, "a"), "status"), &Json::str("established"));
    assert_eq!(
        value(&j, "a"),
        &Json::Arr(vec![
            fixture::ref_value("v", "p"),
            fixture::ref_value("v", "q")
        ])
    );
    assert_eq!(
        f(f(answer(&j, "a"), "scope"), "domain"),
        &Json::str("all_completions")
    );
    let ds = completion_domains(&j);
    assert_eq!(ds.len(), 1);
    assert_eq!(arr(f(f(ds[0], "value"), "elements")).len(), 1);
}
