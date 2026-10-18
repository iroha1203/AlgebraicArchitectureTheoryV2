mod common;
#[path = "common/owner_completions.rs"]
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
    arr(f(j,"nodes")).iter().filter(|n|f(n,"type")==&Json::str("Domain")&&arr(f(n,"arguments")).first().is_some_and(|r|{let ns=nodes(j);let s=ns[text(f(r,"node"))];obj(s).get("value").is_some_and(|v|if let Json::Obj(m)=v {m.get("kind")} else {None}==Some(&Json::str("source")))})).collect()
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
#[test]
fn unknown_owner_family_counts_vary_and_shared_complements_stay_constant() {
    let j = run(
        fixture::input(1, false, false, false),
        &[
            "members=evaluate(RefCalc.members,a=@v/A)",
            "size=evaluate(RefCalc.size,a=@v/A)",
            "total=evaluate(RefCalc.total,a=@v/A,b=@v/B)",
            "stable=check(RefCalc.nonnegative,a=@v/A)",
            "varies=check(RefCalc.nonempty,a=@v/A)",
        ],
    );
    for id in ["members", "size", "varies"] {
        assert_eq!(
            f(answer(&j, id), "status"),
            &Json::str("undetermined"),
            "{j:?}"
        );
        assert_eq!(
            f(f(answer(&j, id), "scope"), "domain"),
            &Json::str("all_completions")
        );
    }
    assert_eq!(value(&j, "total"), &Json::str("1"));
    assert_eq!(f(answer(&j, "stable"), "status"), &Json::str("established"));
    for id in ["members", "size", "total", "stable", "varies"] {
        original_missing(&j, id, "item", "Refs.Sample.owner");
    }
    let domains = completion_domains(&j);
    assert!(!domains.is_empty(), "{j:?}");
    for d in domains {
        assert_eq!(arr(f(f(d, "value"), "elements")).len(), 2);
    }
    let ns = nodes(&j);
    let pairs:Vec<_>=ns.values().filter(|n|obj(n).get("value").is_some_and(|v|if let Json::Obj(m)=v{m.get("kind")}else{None}==Some(&Json::str("completion_pair")))).collect();
    assert!(!pairs.is_empty());
    for pair in pairs {
        let data = f(f(pair, "value"), "data");
        let fields = arr(f(data, "fields"));
        assert_eq!(fields.len(), 1);
        assert_eq!(f(&fields[0], "subject"), &Json::str("item"));
        assert_eq!(f(&fields[0], "field"), &Json::str("Refs.Sample.owner"));
        let values: Vec<_> = ["first", "second"]
            .iter()
            .map(|k| {
                let refs = arr(f(data, k));
                assert_eq!(refs.len(), 1);
                let n = ns[text(f(&refs[0], "node"))];
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
    }
}

#[test]
fn unknown_owner_families_keep_independent_slots_and_one_shared_assignment() {
    let j = run(
        fixture::input(2, false, false, false),
        &[
            "size=evaluate(RefCalc.size,a=@v/A)",
            "total=evaluate(RefCalc.total,a=@v/A,b=@v/B)",
            "pair=evaluate(RefCalc.pair,a=@v/A,b=@v/B)",
        ],
    );
    assert_eq!(value(&j, "total"), &Json::str("2"));
    for id in ["size", "total", "pair"] {
        for subject in ["item", "other"] {
            original_missing(&j, id, subject, "Refs.Sample.owner");
        }
    }
    for id in ["size", "pair"] {
        assert_eq!(f(answer(&j, id), "status"), &Json::str("undetermined"));
    }
    let ns = nodes(&j);
    for domain in completion_domains(&j) {
        let data = f(domain, "value");
        let elements = arr(f(data, "elements"));
        assert_eq!(elements.len(), 4);
        assert_eq!(
            f(data, "type"),
            &Json::Arr(vec![
                Json::str("Tuple"),
                Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Root")]),
                Json::Arr(vec![Json::str("Ref"), Json::str("Refs.Root")]),
            ])
        );
        let actual: BTreeSet<_> = elements
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
fn unknown_owner_cross_snapshot_membership_and_current_provenance_are_preserved() {
    let mut statuses = Vec::new();
    for moved in [false, true] {
        let j = run(
            fixture::input(1, true, moved, false),
            &[
                "size=evaluate(RefCalc.size,a=@v/A)",
                "peer=evaluate(RefCalc.size,a=@w/C)",
                "total=evaluate(RefCalc.total,a=@v/A,b=@v/B)",
            ],
        );
        assert_eq!(value(&j, "peer"), &Json::str("0"));
        assert_eq!(f(answer(&j, "size"), "status"), &Json::str("undetermined"));
        assert_eq!(f(answer(&j, "total"), "status"), &Json::str("undetermined"));
        let ns = nodes(&j);
        for d in completion_domains(&j) {
            let elements = arr(f(f(d, "value"), "elements"));
            assert_eq!(elements.len(), 3);
            let actual: BTreeSet<_> = elements
                .iter()
                .map(|r| f(ns[text(f(r, "node"))], "value").canonical())
                .collect();
            assert_eq!(
                actual,
                [
                    fixture::ref_value("v", "A"),
                    fixture::ref_value("v", "B"),
                    fixture::ref_value("w", "C")
                ]
                .iter()
                .map(Json::canonical)
                .collect()
            );
        }
        statuses.push(["size", "peer", "total"].map(|id| f(answer(&j, id), "status").canonical()));
    }
    assert_eq!(statuses[0], statuses[1]);
}

#[test]
fn unknown_owner_family_uses_known_map_constraints_and_keeps_the_raw_missing_slot() {
    let i = fixture::constrained();
    let checked = check_inputs(i.clone(), &mut quiet()).unwrap();
    let p = checked.archmap().snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == "p")
        .unwrap();
    assert_eq!(
        p.fields
            .iter()
            .find(|f| f.name == "Reservations.State.owner")
            .unwrap()
            .slot,
        archsig::archmap::Slot::Missing
    );
    let j = run(
        i,
        &[
            "members=evaluate(Applications.members,a=@v/A)",
            "size=evaluate(Applications.size,a=@v/A)",
        ],
    );
    assert_eq!(
        value(&j, "members"),
        &Json::Arr(vec![
            fixture::ref_value("v", "p"),
            fixture::ref_value("v", "q")
        ])
    );
    assert_eq!(value(&j, "size"), &Json::str("2"));
    for id in ["members", "size"] {
        original_missing(&j, id, "p", "Reservations.State.owner");
    }
    let domains = completion_domains(&j);
    assert!(!domains.is_empty());
    for d in domains {
        assert_eq!(arr(f(f(d, "value"), "elements")).len(), 1);
        assert!(
            arr(f(d, "support"))
                .iter()
                .any(|fact| obj(fact).get("atom") == Some(&Json::str("m-states")))
        );
    }
    for id in ["members", "size"] {
        assert_eq!(
            f(f(answer(&j, id), "scope"), "domain"),
            &Json::str("all_completions")
        );
    }
}

#[test]
fn unknown_owner_in_quantifier_keeps_known_counterexample_with_missing_first_or_last() {
    for reverse in [false, true] {
        let j = run(
            fixture::counterexample(reverse, false),
            &[
                "all=check(RefCalc.every,a=@v/A)",
                "later=evaluate(RefCalc.seed)",
            ],
        );
        assert_eq!(f(answer(&j, "all"), "status"), &Json::str("refuted"));
        assert_eq!(value(&j, "later"), &Json::str("1"));
        let ns = nodes(&j);
        let known = Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str("other")),
            ("field", Json::str("Refs.Sample.flag")),
            ("atom", Json::str("other-flag")),
        ]);
        assert!(ns.values().any(|n| obj(n).get("value").is_some_and(
            |v| if let Json::Obj(m) = v {
                m.get("kind")
            } else {
                None
            } == Some(&Json::str("counterexample"))
        ) && arr(f(n, "support")).contains(&known)));
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
                arr(f(data, "facts")).contains(&known)
                    && arr(f(data, "bindings"))
                        .iter()
                        .any(|b| f(b, "name") == &Json::str("s"))
            })
            .collect();
        assert!(!actual.is_empty());
        for proof in actual {
            let data = f(f(proof, "value"), "data");
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
        assert!(arr(f(answer(&j, "all"), "reasons")).iter().any(|reason| {
            obj(reason).get("missing").is_some_and(|missing| {
                arr(missing)
                    .iter()
                    .any(|fact| obj(fact).get("field") == Some(&Json::str("Refs.Sample.owner")))
            })
        }));
        if !reverse {
            assert!(arr(f(answer(&j, "all"), "reasons")).iter().any(|reason| {
                obj(reason).get("missing").is_some_and(|missing| {
                    arr(missing)
                        .iter()
                        .any(|fact| obj(fact).get("field") == Some(&Json::str("Refs.Sample.flag")))
                })
            }));
        }
    }
}

#[test]
fn unknown_owner_quantifier_truth_changes_keep_typed_mixed_completions() {
    let j = run(
        fixture::input(1, false, false, false),
        &["all=check(RefCalc.every,a=@v/A)"],
    );
    assert_eq!(f(answer(&j, "all"), "status"), &Json::str("undetermined"));
    original_missing(&j, "all", "item", "Refs.Sample.owner");
    original_missing(&j, "all", "item", "Refs.Sample.flag");
    let ns = nodes(&j);
    let domains = completion_domains(&j);
    assert!(
        domains
            .iter()
            .any(|d| arr(f(f(d, "value"), "elements")).len() == 4)
    );
    let pairs:Vec<_>=ns.values().filter(|n|obj(n).get("value").is_some_and(|v|if let Json::Obj(m)=v{m.get("kind")}else{None}==Some(&Json::str("completion_pair")))).collect();
    assert!(!pairs.is_empty());
    for pair in pairs {
        let fields = arr(f(f(f(pair, "value"), "data"), "fields"));
        assert_eq!(fields.len(), 2);
        assert_eq!(f(&fields[0], "field"), &Json::str("Refs.Sample.flag"));
        assert_eq!(f(&fields[1], "field"), &Json::str("Refs.Sample.owner"));
    }
}
