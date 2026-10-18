mod common;
#[path = "common/dependent_owner_completions.rs"]
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
        assert!(
            !arr(f(a, "reasons"))
                .iter()
                .any(
                    |reason| obj(reason).get("code") == Some(&Json::str("unsupported_algorithm"))
                        && obj(f(reason, "details")).get("method")
                            == Some(&Json::str("unresolved_owned_expression_family"))
                        || obj(reason).get("code") == Some(&Json::str("unsupported_algorithm"))
                            && obj(f(reason, "details")).get("method")
                                == Some(&Json::str("unresolved_dependent_owner"))
                )
        );
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
    let ns = nodes(j);
    arr(f(j,"nodes")).iter().filter(|n| f(n,"type")==&Json::str("Domain")
        && f(f(n,"rule"),"kind")==&Json::str("construction")
        && f(f(n,"rule"),"name")==&Json::str("domain")
        && arr(f(n,"arguments")).first().is_some_and(|r| {
            let source=ns[text(f(r,"node"))];
            obj(source).get("value").is_some_and(|v| if let Json::Obj(m)=v {m.get("kind")}else{None}==Some(&Json::str("source")))
        })).collect()
}

fn original_missing(j: &Json, id: &str, subject: &str, field: &str) {
    let wanted = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str(subject)),
        ("field", Json::str(field)),
    ]);
    assert!(
        arr(f(answer(j, id), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation")
                && arr(f(r, "missing")).contains(&wanted)
                && !arr(f(r, "dependencies")).is_empty()),
        "{id} {wanted:?}"
    );
}
fn assert_boolean_completion_pairs(j: &Json, expected: &[Json]) {
    let ns = nodes(j);
    let pairs:Vec<_>=ns.values().filter(|n|obj(n).get("value").is_some_and(|v|if let Json::Obj(m)=v{m.get("kind")}else{None}==Some(&Json::str("completion_pair")))).collect();
    assert!(!pairs.is_empty());
    for pair in pairs {
        assert_eq!(f(pair, "type"), &Json::str("Evidence"));
        let data = f(f(pair, "value"), "data");
        let fields = arr(f(data, "fields"));
        assert_eq!(fields.len(), expected.len());
        for field in fields {
            assert_eq!(f(field, "snapshot"), &Json::str("v"));
            assert_eq!(f(field, "subject"), &Json::str("item"));
            assert!(!obj(field).contains_key("atom"));
        }
        for key in ["first", "second"] {
            let values = arr(f(data, key));
            assert_eq!(values.len(), expected.len());
            for (value, ty) in values.iter().zip(expected) {
                assert_eq!(f(ns[text(f(value, "node"))], "type"), ty);
            }
        }
        let results: BTreeSet<_> = ["first_result", "second_result"]
            .iter()
            .map(|key| {
                let evaluation = ns[text(f(f(data, key), "node"))];
                assert_eq!(f(evaluation, "type"), &Json::str("Evaluation"));
                let scalar = ns[text(f(f(f(evaluation, "value"), "value"), "node"))];
                assert_eq!(f(scalar, "type"), &Json::str("Bool"));
                f(scalar, "value").canonical()
            })
            .collect();
        assert_eq!(
            results,
            [Json::Bool(false), Json::Bool(true)]
                .iter()
                .map(Json::canonical)
                .collect()
        );
    }
}

#[test]
fn dependent_owner_assignments_prove_invariant_wholes_and_keep_varying_fixed_fibers() {
    let input = fixture::input(1, false, false, Some(true));
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let all = run(
        input,
        &[
            "each=check(RefCalc.each)",
            "owned=check(RefCalc.owner_is_a)",
            "numeric=check(RefCalc.numeric)",
        ],
    );
    for id in ["each", "owned", "numeric"] {
        assert_eq!(
            f(answer(&all, id), "status"),
            &Json::str("established"),
            "{all:?}"
        );
        assert_eq!(
            f(f(answer(&all, id), "scope"), "domain"),
            &Json::str("all_completions")
        );
        original_missing(&all, id, "item", "Refs.Sample.owner");
        let declaration = if id == "owned" {
            "RefCalc.owner_is_a"
        } else if id == "numeric" {
            "RefCalc.numeric"
        } else {
            "RefCalc.each"
        };
        let archsig::law::model::Signature::Law { params, body, .. } =
            &checked.law().declarations[declaration].signature
        else {
            panic!()
        };
        let parameter = params.iter().find(|p| p.name == "s").unwrap();
        let wanted = Json::Arr(vec![
            Json::Nat(parameter.span.0 as u64),
            Json::Nat(parameter.span.1 as u64),
        ]);
        let reason = arr(f(answer(&all, id), "reasons"))
            .iter()
            .find(|r| {
                f(r, "code") == &Json::str("missing_observation")
                    && f(f(r, "location"), "span") == &wanted
            })
            .unwrap();
        let ns = nodes(&all);
        let deps = arr(f(reason, "dependencies"));
        assert_eq!(deps.len(), 1);
        let source = ns[text(f(&deps[0], "node"))];
        assert_eq!(f(source, "type"), &Json::str("Expression"));
        let span = checked.law().exprs[*body].span;
        assert_eq!(
            f(f(f(source, "value"), "location"), "span"),
            &Json::Arr(vec![Json::Nat(span.0 as u64), Json::Nat(span.1 as u64)])
        );
        assert!(
            arr(f(f(source, "value"), "parameters"))
                .iter()
                .any(|p| f(p, "name") == &Json::str("s")
                    && f(p, "type")
                        == &Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Sample")]))
        );
    }
    let varying = run(
        fixture::input(1, false, false, Some(false)),
        &[
            "fixed=check(RefCalc.each,a=@v/A)",
            "whole=check(RefCalc.each)",
        ],
    );
    assert_eq!(
        f(answer(&varying, "fixed"), "status"),
        &Json::str("undetermined"),
        "{varying:?}"
    );
    assert_eq!(
        f(answer(&varying, "whole"), "status"),
        &Json::str("refuted")
    );
    for id in ["fixed", "whole"] {
        original_missing(&varying, id, "item", "Refs.Sample.owner");
    }
    let ns = nodes(&varying);
    assert!(ns.values().any(|n| {
        obj(n)
            .get("value")
            .is_some_and(|v| if let Json::Obj(m) = v {
                m.get("kind")
            } else {
                None
            } == Some(&Json::str("completion_pair")))
    }));
    assert_boolean_completion_pairs(
        &varying,
        &[Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Root")])],
    );
    let domains = completion_domains(&varying);
    assert!(!domains.is_empty());
    for d in domains {
        assert_eq!(arr(f(f(d, "value"), "elements")).len(), 2);
    }
}

#[test]
fn dependent_owner_independent_slots_keep_exact_assignments_and_shared_body_reads() {
    let j = run(
        fixture::input(2, false, false, Some(true)),
        &[
            "each=check(RefCalc.each)",
            "pair=check(RefCalc.pair)",
            "owner=check(RefCalc.owner_is_a)",
        ],
    );
    for id in ["each", "pair", "owner"] {
        assert_eq!(f(answer(&j, id), "status"), &Json::str("established"));
        for subject in ["item", "other"] {
            original_missing(&j, id, subject, "Refs.Sample.owner");
        }
    }
    let ns = nodes(&j);
    let ds = completion_domains(&j);
    assert!(!ds.is_empty());
    for d in ds {
        let data = f(d, "value");
        let es = arr(f(data, "elements"));
        assert_eq!(es.len(), 4);
        assert_eq!(
            f(data, "type"),
            &Json::Arr(vec![
                Json::str("Tuple"),
                Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Root")]),
                Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Root")])
            ])
        );
        let actual: BTreeSet<_> = es
            .iter()
            .map(|r| f(ns[text(f(r, "node"))], "value").canonical())
            .collect();
        let wanted: BTreeSet<_> = ["A", "B"]
            .iter()
            .flat_map(|a| {
                ["A", "B"].iter().map(move |b| {
                    Json::Arr(vec![fixture::ref_value("v", a), fixture::ref_value("v", b)])
                        .canonical()
                })
            })
            .collect();
        assert_eq!(actual, wanted);
    }
}

#[test]
fn dependent_owner_mixed_bool_and_known_counterexamples_keep_whole_semantics() {
    let mixed = run(
        fixture::input(1, false, false, None),
        &["all=check(RefCalc.each)"],
    );
    assert_eq!(
        f(answer(&mixed, "all"), "status"),
        &Json::str("undetermined")
    );
    for field in ["Refs.Sample.owner", "Refs.Sample.flag"] {
        original_missing(&mixed, "all", "item", field);
    }
    assert!(
        completion_domains(&mixed)
            .iter()
            .any(|d| arr(f(f(d, "value"), "elements")).len() == 4)
    );
    assert_boolean_completion_pairs(
        &mixed,
        &[
            Json::str("Bool"),
            Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Root")]),
        ],
    );
    let ns = nodes(&mixed);
    let pairs:Vec<_>=ns.values().filter(|n|obj(n).get("value").is_some_and(|v|if let Json::Obj(m)=v{m.get("kind")}else{None}==Some(&Json::str("completion_pair")))).collect();
    assert!(!pairs.is_empty());
    for p in pairs {
        let data = f(f(p, "value"), "data");
        let fields = arr(f(data, "fields"));
        assert_eq!(fields.len(), 2);
        assert_eq!(f(&fields[0], "field"), &Json::str("Refs.Sample.flag"));
        assert_eq!(f(&fields[1], "field"), &Json::str("Refs.Sample.owner"));
    }
    for reverse in [false, true] {
        let j = run(
            fixture::counterexample(reverse, false),
            &["all=check(RefCalc.each)", "later=evaluate(RefCalc.seed)"],
        );
        assert_eq!(f(answer(&j, "all"), "status"), &Json::str("refuted"));
        assert_eq!(value(&j, "later"), &Json::str("1"));
        original_missing(&j, "all", "item", "Refs.Sample.owner");
        let ns = nodes(&j);
        let fact = Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str("other")),
            ("field", Json::str("Refs.Sample.flag")),
            ("atom", Json::str("other-flag")),
        ]);
        let actual: Vec<_> = ns
            .values()
            .filter(|n| {
                let Some(Json::Obj(v)) = obj(n).get("value") else {
                    return false;
                };
                if v.get("kind") != Some(&Json::str("counterexample")) {
                    return false;
                }
                let data = &v["data"];
                arr(f(data, "facts")).contains(&fact)
                    && arr(f(data, "bindings"))
                        .iter()
                        .any(|b| f(b, "name") == &Json::str("s"))
            })
            .collect();
        assert!(!actual.is_empty());
        for p in actual {
            let data = f(f(p, "value"), "data");
            assert_eq!(
                f(ns[text(f(f(data, "left"), "node"))], "value"),
                &Json::Bool(false)
            );
            assert_eq!(
                f(ns[text(f(f(data, "right"), "node"))], "value"),
                &Json::Bool(true)
            );
            assert!(
                arr(f(data, "bindings"))
                    .iter()
                    .any(|b| f(b, "name") == &Json::str("s")
                        && f(ns[text(f(f(b, "value"), "node"))], "value")
                            == &fixture::ref_value("v", "other"))
            );
        }
    }
}

#[test]
fn dependent_owner_cross_snapshot_and_current_provenance_keep_actual_fibers() {
    let mut judgments = vec![];
    for moved in [false, true] {
        let j = run(
            fixture::input(1, true, moved, Some(false)),
            &["all=check(RefCalc.each)", "peer=check(RefCalc.each,a=@w/C)"],
        );
        assert_eq!(f(answer(&j, "all"), "status"), &Json::str("undetermined"));
        assert_eq!(f(answer(&j, "peer"), "status"), &Json::str("established"));
        original_missing(&j, "all", "item", "Refs.Sample.owner");
        let ns = nodes(&j);
        let ds = completion_domains(&j);
        assert!(!ds.is_empty());
        for d in ds {
            let es = arr(f(f(d, "value"), "elements"));
            assert_eq!(es.len(), 3);
            let actual: BTreeSet<_> = es
                .iter()
                .map(|r| f(ns[text(f(r, "node"))], "value").canonical())
                .collect();
            let wanted: BTreeSet<_> = [
                fixture::ref_value("v", "A"),
                fixture::ref_value("v", "B"),
                fixture::ref_value("w", "C"),
            ]
            .iter()
            .map(Json::canonical)
            .collect();
            assert_eq!(actual, wanted);
        }
        judgments.push(["all", "peer"].map(|id| f(answer(&j, id), "status").canonical()));
    }
    assert_eq!(judgments[0], judgments[1]);
}

#[test]
fn dependent_owner_map_and_arrow_constraints_keep_original_missing_and_known_support() {
    for (input, field, subject, atom) in [
        (
            fixture::constrained(),
            "Reservations.State.owner",
            "p",
            "m-states",
        ),
        (fixture::arrow(), "Reservations.Reserve.owner", "e", "e-to"),
    ] {
        let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
        assert_eq!(
            checked.archmap().snapshots[0]
                .subjects
                .iter()
                .find(|s| s.id == subject)
                .unwrap()
                .fields
                .iter()
                .find(|f| f.name == field)
                .unwrap()
                .slot,
            archsig::archmap::Slot::Missing
        );
        let j = run(input, &["all=check(Applications.each)"]);
        assert_eq!(
            f(answer(&j, "all"), "status"),
            &Json::str("established"),
            "{j:?}"
        );
        original_missing(&j, "all", subject, field);
        let ds = completion_domains(&j);
        assert!(!ds.is_empty());
        for d in ds {
            assert_eq!(arr(f(f(d, "value"), "elements")).len(), 1);
            assert!(
                arr(f(d, "support"))
                    .iter()
                    .any(|f| obj(f).get("atom") == Some(&Json::str(atom)))
            );
        }
    }
}

#[test]
fn dependent_owner_later_parameter_discovery_keeps_each_original_slot_and_whole() {
    for missing_flag in [false, true] {
        let j = run(fixture::nested(missing_flag), &["all=check(Inspect.each)"]);
        assert_eq!(
            f(answer(&j, "all"), "status"),
            &Json::str(if missing_flag {
                "refuted"
            } else {
                "established"
            }),
            "{j:?}"
        );
        original_missing(&j, "all", "p", "Dep.Child.owner");
        original_missing(&j, "all", "l", "Dep.Leaf.owner");
        let ds = completion_domains(&j);
        assert!(
            ds.iter()
                .any(|d| arr(f(f(d, "value"), "elements")).len()
                    == if missing_flag { 18 } else { 9 })
        );
        if missing_flag {
            original_missing(&j, "all", "l", "Dep.Leaf.ok");
        }
    }
}

#[test]
fn dependent_owner_finite_compound_parameters_keep_typed_conditional_domains() {
    let j = run(
        fixture::input(1, false, false, Some(true)),
        &[
            "sets=check(RefCalc.sets,a=@v/A)",
            "options=check(RefCalc.options,a=@v/A)",
            "tuples=check(RefCalc.tuples,a=@v/A)",
        ],
    );
    let ns = nodes(&j);
    let reference = Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Sample")]);
    for (id, ty) in [
        ("sets", Json::Arr(vec![Json::str("Set"), reference.clone()])),
        (
            "options",
            Json::Arr(vec![Json::str("Option"), reference.clone()]),
        ),
        (
            "tuples",
            Json::Arr(vec![Json::str("Tuple"), reference, Json::str("Bool")]),
        ),
    ] {
        assert_eq!(
            f(answer(&j, id), "status"),
            &Json::str("established"),
            "{j:?}"
        );
        original_missing(&j, id, "item", "Refs.Sample.owner");
        assert!(ns.values().any(|n| f(n, "type") == &Json::str("Domain")
            && f(f(n, "rule"), "kind") == &Json::str("law")
            && f(f(n, "value"), "type") == &ty));
    }
    let ds = completion_domains(&j);
    assert!(!ds.is_empty());
    for d in ds {
        assert_eq!(arr(f(f(d, "value"), "elements")).len(), 2);
    }
}
