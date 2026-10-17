//! 元参照族から生成した有限Map型全域の三入力接続。
#[path = "common/finite_map.rs"]
mod maps;
use archsig::{
    canonical::Json,
    definition::check_definitions,
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
fn sources(revision: &str) -> InputSources {
    let d = check_definitions(&[("definition0", maps::DEFINITIONS.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Maps"].digest;
    InputSources::from_bytes(
        vec![maps::DEFINITIONS.as_bytes().to_vec()],
        maps::law(digest).into_bytes(),
        maps::archmap(digest, revision).into_bytes(),
    )
}
fn object(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(x) = j else {
        panic!("object: {j:?}")
    };
    x
}
fn array(j: &Json) -> &[Json] {
    let Json::Arr(x) = j else {
        panic!("array: {j:?}")
    };
    x
}
fn text(j: &Json) -> &str {
    let Json::Str(x) = j else {
        panic!("string: {j:?}")
    };
    x
}
fn get<'a>(j: &'a Json, name: &str) -> &'a Json {
    &object(j)[name]
}
fn answer<'a>(wire: &'a Json, id: &str) -> &'a Json {
    array(get(wire, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str(id))
        .unwrap()
}
fn value<'a>(wire: &'a Json, id: &str, ty: Json) -> &'a Json {
    let a = answer(wire, id);
    assert_eq!(get(a, "status"), &Json::str("established"), "{a:?}");
    let r = get(get(get(a, "outputs"), "value"), "node");
    let node = array(get(wire, "nodes"))
        .iter()
        .find(|n| get(n, "id") == r)
        .unwrap();
    assert_eq!(get(node, "type"), &ty);
    assert_eq!(get(node, "state"), &Json::str("value"));
    get(node, "value")
}

fn ref_ty(name: &str) -> Json {
    Json::Arr(vec![Json::str("Ref"), Json::str(format!("Maps.{name}"))])
}
fn map_ty(from: &str, to: &str) -> Json {
    Json::Arr(vec![Json::str("Map"), ref_ty(from), ref_ty(to)])
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    array(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == get(r, "node"))
        .unwrap()
}
fn domain<'a>(w: &'a Json, ty: &Json) -> &'a Json {
    let ds: Vec<_> = array(get(w, "nodes"))
        .iter()
        .filter(|n| {
            get(n, "type") == &Json::str("Domain")
                && object(n)
                    .get("value")
                    .is_some_and(|v| object(v).get("type") == Some(ty))
        })
        .collect();
    assert_eq!(ds.len(), 1);
    ds[0]
}
fn members(w: &Json, d: &Json) -> Vec<Json> {
    array(get(get(d, "value"), "elements"))
        .iter()
        .map(|r| get(node(w, r), "value").clone())
        .collect()
}
fn maps_oracle() -> BTreeSet<String> {
    let mut all = BTreeSet::new();
    for x in [("v", "x"), ("w", "y")] {
        for y in [("v", "x"), ("w", "y")] {
            let rows = [(("v", "a"), x), (("w", "b"), y)];
            let v = Json::Arr(
                rows.iter()
                    .map(|(a, b)| {
                        Json::Arr(vec![
                            Json::Arr(vec![Json::str(a.0), Json::str(a.1)]),
                            Json::Arr(vec![Json::str(b.0), Json::str(b.1)]),
                        ])
                    })
                    .collect(),
            );
            all.insert(v.canonical());
        }
    }
    all
}
#[test]
fn finite_map_type_domain_enumerates_all_four_functions_across_snapshots() {
    let input = sources("r1");
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let before = format!("{:?}", checked.archmap());
    let result = evaluate_observed_bytes(input, &["a=evaluate(Maps.every)"], &mut quiet()).unwrap();
    assert_eq!(result.status(), "complete");
    let wire = result.wire();
    assert_eq!(value(&wire, "a", Json::str("Bool")), &Json::Bool(true));
    let d = domain(&wire, &map_ty("Key", "Image"));
    audit(&result);
    assert_eq!(
        checked.metadata_wire(),
        result.prepared().inputs().metadata_wire()
    );
    assert_eq!(
        format!("{:?}", checked.definitions()),
        format!("{:?}", result.prepared().inputs().definitions())
    );
    assert_eq!(
        format!("{:?}", checked.law()),
        format!("{:?}", result.prepared().inputs().law())
    );
    assert_eq!(
        format!("{:?}", checked.sources()),
        format!("{:?}", result.prepared().inputs().sources())
    );
    let ms = members(&wire, d);
    assert_eq!(ms.len(), 4);
    assert_eq!(
        ms.iter().map(Json::canonical).collect::<BTreeSet<_>>(),
        maps_oracle()
    );
    assert_eq!(
        format!("{:?}", result.prepared().inputs().archmap()),
        before
    );
    for s in ["v", "w", "z"] {
        assert!(
            get(d, "scope")
                .canonical()
                .contains(&Json::str(s).canonical())
        );
    }
    assert_eq!(
        checked
            .archmap()
            .snapshots
            .iter()
            .flat_map(|s| &s.subjects)
            .filter(|s| s.ty == "Maps.Key")
            .count(),
        2
    );
    assert!(
        checked
            .archmap()
            .snapshots
            .iter()
            .flat_map(|s| &s.subjects)
            .flat_map(|s| &s.fields)
            .all(|f| matches!(f.slot, archsig::archmap::Slot::Missing))
    );
}

fn refs(j: &Json, rs: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => rs.push(text(&m["node"]).into()),
        Json::Obj(m) => {
            for v in m.values() {
                refs(v, rs);
            }
        }
        Json::Arr(a) => {
            for v in a {
                refs(v, rs);
            }
        }
        _ => {}
    }
}
fn audit(result: &archsig::observed::ObservedEvaluation) {
    let w = result.wire();
    let mut seen = BTreeSet::new();
    let checked = result.prepared().inputs();
    for n in array(get(&w, "nodes")) {
        let mut rs = vec![];
        refs(n, &mut rs);
        assert!(rs.iter().all(|r| seen.contains(r)));
        assert!(seen.insert(text(get(n, "id")).to_string()));
        if get(n, "type") != &Json::str("Proposition") {
            assert!(!object(n).contains_key("judgment"));
        }
        if let Some(v) = object(n).get("value") {
            let mut rs = vec![];
            refs(v, &mut rs);
            for r in rs {
                let target = array(get(&w, "nodes"))
                    .iter()
                    .find(|n| get(n, "id") == &Json::str(r.clone()))
                    .unwrap();
                assert_eq!(get(target, "state"), &Json::str("value"));
                assert!(!object(target).contains_key("partial"));
            }
        }
        for fact in array(get(n, "support")) {
            let subject = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == text(get(fact, "snapshot")))
                .unwrap()
                .subjects
                .iter()
                .find(|s| s.id == text(get(fact, "subject")))
                .unwrap();
            let origin = if let Some(field) = object(fact).get("field") {
                let f = subject
                    .fields
                    .iter()
                    .find(|f| f.name == text(field))
                    .unwrap();
                let archsig::archmap::Slot::Known { atom, origin, .. } = &f.slot else {
                    panic!("support is known")
                };
                assert_eq!(get(fact, "atom"), &Json::str(atom));
                origin
            } else {
                &subject.origin
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            for loc in &origin.locations {
                assert!(checked.archmap().sources.iter().any(|s| s.id == loc.source));
            }
        }
        if get(n, "type") == &Json::str("Domain")
            && object(n)
                .get("value")
                .is_some_and(|v| object(v).get("kind") == Some(&Json::str("finite")))
        {
            let payload = get(n, "value");
            for member in array(get(payload, "elements")) {
                let target = node(&w, member);
                assert_eq!(get(target, "type"), get(payload, "type"));
                assert_eq!(get(target, "state"), &Json::str("value"));
            }
        }
        if get(n, "type") == &Json::str("Evidence")
            && object(n)
                .get("value")
                .is_some_and(|v| object(v).get("kind") == Some(&Json::str("finite_exhaustion")))
        {
            let data = get(get(n, "value"), "data");
            let instances = array(get(data, "instances"));
            assert_eq!(get(data, "checked"), &Json::Nat(instances.len() as u64));
            for r in instances {
                assert_eq!(get(node(&w, r), "type"), &Json::str("Evaluation"));
            }
        }
    }
    for a in array(get(&w, "answers")) {
        if let Some(claim) = object(a).get("claim") {
            let claim = node(&w, claim);
            assert_eq!(get(claim, "type"), &Json::str("Proposition"));
            assert_eq!(get(get(claim, "judgment"), "status"), get(a, "status"));
        }
    }
}
#[test]
fn finite_map_empty_source_and_empty_target_keep_different_function_domains() {
    for (name, from, to, count, result) in [
        ("empty_source", "Void", "Image", 1, true),
        ("empty_target", "Key", "Void", 0, false),
        ("no_map_all", "Key", "Void", 0, true),
        ("both_empty", "Void", "Void", 1, true),
    ] {
        let ask = format!("a=evaluate(Maps.{name})");
        let evaluated = evaluate_observed_bytes(sources("r1"), &[&ask], &mut quiet()).unwrap();
        assert_eq!(evaluated.status(), "complete");
        let wire = evaluated.wire();
        assert_eq!(value(&wire, "a", Json::str("Bool")), &Json::Bool(result));
        let ms = members(&wire, domain(&wire, &map_ty(from, to)));
        assert_eq!(ms.len(), count);
        if count == 1 {
            assert_eq!(ms, vec![Json::Arr(vec![])]);
        }
        audit(&evaluated);
    }
}
#[test]
fn finite_map_option_tuple_and_set_domains_keep_every_concrete_member() {
    let oracle = maps_oracle();
    let map = map_ty("Key", "Image");
    for (name, ty, count) in [
        (
            "option_domain",
            Json::Arr(vec![Json::str("Option"), map.clone()]),
            5,
        ),
        (
            "tuple_domain",
            Json::Arr(vec![Json::str("Tuple"), Json::str("Unit"), map.clone()]),
            4,
        ),
        (
            "set_domain",
            Json::Arr(vec![Json::str("Set"), map.clone()]),
            16,
        ),
    ] {
        let ask = format!("a=evaluate(Maps.{name})");
        let result = evaluate_observed_bytes(sources("r1"), &[&ask], &mut quiet()).unwrap();
        assert_eq!(result.status(), "complete");
        let w = result.wire();
        let ms = members(&w, domain(&w, &ty));
        assert_eq!(ms.len(), count);
        let mut signatures = BTreeSet::new();
        for m in &ms {
            let signature = if name == "option_domain" {
                if let Some(value) = object(m).get("some") {
                    assert!(oracle.contains(&value.canonical()));
                    format!("some:{}", value.canonical())
                } else {
                    assert_eq!(m, &Json::obj([("none", Json::Bool(true))]));
                    "none".into()
                }
            } else if name == "tuple_domain" {
                let row = array(m);
                assert_eq!(row[0], Json::Arr(vec![]));
                assert!(oracle.contains(&row[1].canonical()));
                row[1].canonical()
            } else {
                let values = array(m)
                    .iter()
                    .map(Json::canonical)
                    .collect::<BTreeSet<_>>();
                assert_eq!(values.len(), array(m).len());
                assert!(values.iter().all(|v| oracle.contains(v)));
                format!("{values:?}")
            };
            assert!(signatures.insert(signature));
        }
        assert_eq!(value(&w, "a", Json::str("Bool")), &Json::Bool(true));
        audit(&result);
    }
}
#[test]
fn finite_map_unbound_law_parameter_has_all_rows_and_real_counterexample() {
    for (name, status) in [("whole", "established"), ("impossible", "refuted")] {
        let ask = format!("a=check(Maps.{name})");
        let result = evaluate_observed_bytes(sources("r1"), &[&ask], &mut quiet()).unwrap();
        assert_eq!(result.status(), "complete");
        let w = result.wire();
        let a = answer(&w, "a");
        assert_eq!(get(a, "status"), &Json::str(status));
        let ms = members(&w, domain(&w, &map_ty("Key", "Image")));
        assert_eq!(
            ms.iter().map(Json::canonical).collect::<BTreeSet<_>>(),
            maps_oracle()
        );
        let instances: Vec<_> = array(get(&w, "nodes"))
            .iter()
            .filter(|n| {
                get(n, "type") == &Json::str("LawInstance")
                    && object(n).get("value").is_some_and(|v| {
                        object(v).get("name") == Some(&Json::str(format!("Maps.{name}")))
                            && !array(get(v, "bindings")).is_empty()
                    })
            })
            .collect();
        assert_eq!(instances.len(), 4);
        let mut rows = BTreeSet::new();
        for i in instances {
            let b = &array(get(get(i, "value"), "bindings"))[0];
            assert_eq!(get(b, "name"), &Json::str("f"));
            assert_eq!(
                get(node(&w, get(b, "value")), "type"),
                &map_ty("Key", "Image")
            );
            rows.insert(get(node(&w, get(b, "value")), "value").canonical());
        }
        assert_eq!(rows, maps_oracle());
        if status == "refuted" {
            assert!(!array(get(a, "evidence")).is_empty());
        }
        audit(&result);
    }
}
fn owned_sources(unknown: bool) -> InputSources {
    let definitions = maps::OWNED_DEFINITIONS.as_bytes();
    let d = check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies["Reservations"].digest;
    InputSources::from_bytes(
        vec![definitions.to_vec()],
        maps::owned_law(digest).into_bytes(),
        maps::owned_archmap(unknown).into_bytes(),
    )
}
#[test]
fn finite_owned_map_domains_use_each_actual_endpoint_owner_and_empty_fibers() {
    let state = Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")]);
    let ty = Json::Arr(vec![Json::str("Map"), state.clone(), state]);
    for (a, b, name, count, wanted) in [
        ("A", "B", "every", 4, true),
        ("A", "B", "any", 4, true),
        ("Z", "A", "any", 1, true),
        ("A", "Z", "any", 0, false),
    ] {
        let ask = format!("a=evaluate(Reservations.{name},a=@v/{a},b=@v/{b})");
        let input = owned_sources(false);
        let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
        let before = format!("{:?}", checked.archmap());
        let result = evaluate_observed_bytes(input, &[&ask], &mut quiet()).unwrap();
        assert_eq!(result.status(), "complete");
        let w = result.wire();
        assert_eq!(value(&w, "a", Json::str("Bool")), &Json::Bool(wanted));
        let d = domain(&w, &ty);
        let ms = members(&w, d);
        assert_eq!(ms.len(), count);
        if a == "Z" {
            assert_eq!(ms, vec![Json::Arr(vec![])]);
        } else if b != "Z" {
            let keys: BTreeSet<_> = ["p", "q"]
                .iter()
                .map(|s| Json::Arr(vec![Json::str("v"), Json::str(*s)]).canonical())
                .collect();
            let mut signatures = BTreeSet::new();
            for m in ms {
                let rows = array(&m);
                assert_eq!(rows.len(), 2);
                assert_eq!(
                    rows.iter()
                        .map(|p| array(p)[0].canonical())
                        .collect::<BTreeSet<_>>(),
                    keys
                );
                let images: Vec<_> = rows
                    .iter()
                    .map(|p| array(&array(p)[1])[1].clone())
                    .collect();
                assert!(
                    images
                        .iter()
                        .all(|i| [Json::str("r"), Json::str("s")].contains(i))
                );
                assert!(signatures.insert(format!("{images:?}")));
            }
            assert_eq!(signatures.len(), 4);
        }
        assert!(
            get(d, "support")
                .canonical()
                .contains("Reservations.State.owner")
        );
        assert_eq!(
            format!("{:?}", result.prepared().inputs().archmap()),
            before
        );
        audit(&result);
    }
    let result = evaluate_observed_bytes(
        owned_sources(false),
        &["a=evaluate(Reservations.lexical,m=@v/m)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete");
    assert_eq!(
        members(&result.wire(), domain(&result.wire(), &ty)).len(),
        4
    );
    audit(&result);
}
#[test]
fn finite_owned_map_unknown_membership_keeps_missing_and_no_complete_domain() {
    let result = evaluate_observed_bytes(
        owned_sources(true),
        &["a=evaluate(Reservations.every,a=@v/A,b=@v/B)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "partial");
    let w = result.wire();
    let a = answer(&w, "a");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    assert!(!object(get(a, "outputs")).contains_key("value"));
    assert!(a.canonical().contains("Reservations.State.owner"));
    assert!(a.canonical().contains("all_completions"));
    assert!(
        array(get(&w, "nodes"))
            .iter()
            .all(|n| get(n, "type") != &Json::str("Domain"))
    );
    audit(&result);
}
#[test]
fn finite_map_provenance_move_keeps_answers_and_current_roster_sources() {
    let a =
        evaluate_observed_bytes(sources("r1"), &["a=evaluate(Maps.every)"], &mut quiet()).unwrap();
    let b =
        evaluate_observed_bytes(sources("r2"), &["a=evaluate(Maps.every)"], &mut quiet()).unwrap();
    assert_eq!(get(&a.wire(), "answers"), get(&b.wire(), "answers"));
    assert_ne!(
        a.prepared().inputs().sources().archmap().bytes(),
        b.prepared().inputs().sources().archmap().bytes()
    );
    for (r, rev) in [(&a, "r1"), (&b, "r2")] {
        assert_eq!(r.prepared().inputs().archmap().sources[0].revision, rev);
        audit(r);
    }
}
#[test]
fn finite_map_empty_domain_still_rejects_an_ill_typed_body() {
    let input = sources("r1");
    let mut law = String::from_utf8(input.law().bytes().to_vec()).unwrap();
    let pos = law.rfind('}').unwrap();
    law.insert_str(pos, "view invalid():Bool=forall f:Map<Key,Void> . f+f=f;");
    let input = InputSources::from_bytes(
        vec![maps::DEFINITIONS.as_bytes().to_vec()],
        law.into_bytes(),
        input.archmap().bytes().to_vec(),
    );
    assert!(check_inputs(input, &mut quiet()).is_err());
}

#[test]
fn finite_owned_map_unbound_parameters_have_concrete_finite_domains() {
    for (ty, count) in [
        ("Map<State[a],State[b]>", 4),
        ("Option<Map<State[a],State[b]>>", 5),
        ("(Unit,Map<State[a],State[b]>)", 4),
        ("Set<Map<State[a],State[b]>>", 16),
    ] {
        let original = owned_sources(false);
        let mut law = String::from_utf8(original.law().bytes().to_vec()).unwrap();
        let pos = law.rfind('}').unwrap();
        law.insert_str(
            pos,
            &format!("law required nested(a:System,b:System,f:{ty}):f=f;"),
        );
        let input = InputSources::from_bytes(
            vec![maps::OWNED_DEFINITIONS.as_bytes().to_vec()],
            law.into_bytes(),
            original.archmap().bytes().to_vec(),
        );
        let result = evaluate_observed_bytes(
            input,
            &["c=check(Reservations.nested,a=@v/A,b=@v/B)"],
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete");
        let w = result.wire();
        assert_eq!(get(answer(&w, "c"), "status"), &Json::str("established"));
        let ds: Vec<_> = array(get(&w, "nodes"))
            .iter()
            .filter(|n| {
                get(n, "type") == &Json::str("Domain")
                    && array(get(get(n, "value"), "elements")).len() == count
            })
            .collect();
        assert_eq!(ds.len(), 2);
        audit(&result);
    }
}

#[test]
fn nonfinite_owned_map_unbound_parameters_keep_dedicated_unimplemented_failure() {
    for ty in [
        "List<Map<State[a],State[b]>>",
        "Option<List<Map<State[a],State[b]>>>",
        "(Unit,List<Map<State[a],State[b]>>)",
        "Set<List<Map<State[a],State[b]>>>",
    ] {
        let original = owned_sources(false);
        let mut law = String::from_utf8(original.law().bytes().to_vec()).unwrap();
        let pos = law.rfind('}').unwrap();
        law.insert_str(
            pos,
            &format!("law required nested(a:System,b:System,f:{ty}):true;"),
        );
        let input = InputSources::from_bytes(
            vec![maps::OWNED_DEFINITIONS.as_bytes().to_vec()],
            law.into_bytes(),
            original.archmap().bytes().to_vec(),
        );
        let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
        let archsig::law::model::Signature::Law { params, .. } =
            &checked.law().declarations["Reservations.nested"].signature
        else {
            panic!("Law signature");
        };
        let expected = archsig::issue::Location::Law {
            span: params[2].span,
        };
        let outcome = evaluate_observed_bytes(
            input,
            &["c=check(Reservations.nested,a=@v/A,b=@v/B)"],
            &mut quiet(),
        );
        let Err(failure) = outcome else {
            panic!("{ty}: unsupported parameter produced a result instead of dedicated failure");
        };
        assert!(failure.wire().is_none());
        let archsig::observed::EvaluationFailure::NotImplemented {
            declaration,
            location,
            feature,
        } = failure
        else {
            panic!("{ty}: wrong failure");
        };
        assert_eq!(declaration, "Reservations.nested");
        assert_eq!(location, expected);
        assert!(feature.contains("parameter `f`"), "{feature}");
    }
}
