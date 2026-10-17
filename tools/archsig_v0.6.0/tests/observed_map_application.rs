//! 元表・実callee/引数・構成条件を保つMap適用。
#[path = "common/map_application.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::check_inputs,
    },
};
use std::collections::BTreeMap;
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(x) = j else { panic!("object") };
    x
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(x) = j else { panic!("array") };
    x
}
fn get<'a>(j: &'a Json, k: &str) -> &'a Json {
    &obj(j)[k]
}
#[test]
fn map_application_legal_owned_key_outside_actual_table_has_condition_failure() {
    let input = fixture::owned("known");
    let checked = check_inputs(input.clone(), &mut quiet());
    assert!(checked.is_ok(), "input should pass static checking");
    let outcome = evaluate_observed_bytes(
        input,
        &["a=evaluate(Applications.apply,m=@v/m,x=@v/r)"],
        &mut quiet(),
    );
    let Ok(r) = outcome else {
        panic!("legal application should return a typed result")
    };
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    let a = &arr(get(&w, "answers"))[0];
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    assert!(a.canonical().contains("condition_failed"));
    assert!(!obj(get(a, "outputs")).contains_key("value"));
}

#[test]
fn map_application_known_plain_table_returns_the_original_image() {
    let r = evaluate_observed_bytes(
        fixture::plain("r1"),
        &["a=evaluate(Maps.apply,s=@v/s,x=@v/a)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    let a = &arr(get(&w, "answers"))[0];
    let v = get(get(get(a, "outputs"), "value"), "node");
    let n = arr(get(&w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == v)
        .unwrap();
    assert_eq!(
        get(n, "type"),
        &Json::Arr(vec![Json::str("Ref"), Json::str("Maps.Item")])
    );
    assert_eq!(
        get(n, "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("b")])
    );
}

fn text(j: &Json) -> &str {
    let Json::Str(s) = j else { panic!("text") };
    s
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == get(r, "node"))
        .unwrap()
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(get(w, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str(id))
        .unwrap()
}
fn result_value(w: &Json, id: &str, ty: Json) -> Json {
    let a = answer(w, id);
    assert_eq!(get(a, "status"), &Json::str("established"));
    let n = node(w, get(get(a, "outputs"), "value"));
    assert_eq!(get(n, "type"), &ty);
    assert_eq!(get(n, "state"), &Json::str("value"));
    get(n, "value").clone()
}
use std::collections::BTreeSet;
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
    for n in arr(get(&w, "nodes")) {
        let mut rs = vec![];
        refs(n, &mut rs);
        assert!(rs.iter().all(|r| seen.contains(r)));
        assert!(seen.insert(text(get(n, "id")).to_string()));
        if get(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if let Some(v) = obj(n).get("value") {
            let mut rs = vec![];
            refs(v, &mut rs);
            for r in rs {
                let target = arr(get(&w, "nodes"))
                    .iter()
                    .find(|n| get(n, "id") == &Json::str(r.clone()))
                    .unwrap();
                assert_eq!(get(target, "state"), &Json::str("value"));
                assert!(!obj(target).contains_key("partial"));
            }
        }
        for fact in arr(get(n, "support")) {
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
            let origin = if let Some(field) = obj(fact).get("field") {
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
            && obj(n)
                .get("value")
                .is_some_and(|v| obj(v).get("kind") == Some(&Json::str("finite")))
        {
            let payload = get(n, "value");
            for member in arr(get(payload, "elements")) {
                let target = node(&w, member);
                assert_eq!(get(target, "type"), get(payload, "type"));
                assert_eq!(get(target, "state"), &Json::str("value"));
            }
        }
        if get(n, "type") == &Json::str("Evidence")
            && obj(n)
                .get("value")
                .is_some_and(|v| obj(v).get("kind") == Some(&Json::str("finite_exhaustion")))
        {
            let data = get(get(n, "value"), "data");
            let instances = arr(get(data, "instances"));
            assert_eq!(get(data, "checked"), &Json::Nat(instances.len() as u64));
            for r in instances {
                assert_eq!(get(node(&w, r), "type"), &Json::str("Evaluation"));
            }
        }
    }
    for a in arr(get(&w, "answers")) {
        if let Some(claim) = obj(a).get("claim") {
            let claim = node(&w, claim);
            assert_eq!(get(claim, "type"), &Json::str("Proposition"));
            assert_eq!(get(get(claim, "judgment"), "status"), get(a, "status"));
        }
    }
}

fn assert_condition(r: &archsig::observed::ObservedEvaluation, keys: &[&str], argument: &str) {
    let w = r.wire();
    let a = answer(&w, "a");
    assert_eq!(r.status(), "partial");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    assert!(!obj(get(a, "outputs")).contains_key("value"));
    assert!(!obj(a).contains_key("claim"));
    let rs: Vec<_> = arr(get(a, "reasons"))
        .iter()
        .filter(|r| get(r, "code") == &Json::str("condition_failed"))
        .collect();
    assert_eq!(rs.len(), 1);
    let reason = rs[0];
    assert_eq!(
        get(get(reason, "details"), "construction"),
        &Json::str("evaluation")
    );
    let condition = node(&w, get(get(reason, "details"), "condition"));
    assert_eq!(get(condition, "type"), &Json::str("Proposition"));
    assert_eq!(
        get(get(condition, "judgment"), "status"),
        &Json::str("refuted")
    );
    assert_eq!(
        get(get(condition, "value"), "predicate"),
        &Json::str("equal")
    );
    let operands = arr(get(get(condition, "value"), "operands"));
    assert_eq!(operands.len(), 2);
    let actual = node(&w, &operands[0]);
    let required = node(&w, &operands[1]);
    let ty = Json::Arr(vec![
        Json::str("Set"),
        Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")]),
    ]);
    assert_eq!(get(actual, "type"), &ty);
    assert_eq!(get(required, "type"), &ty);
    let k = |s: &str| Json::Arr(vec![Json::str("v"), Json::str(s)]).canonical();
    let expected: BTreeSet<_> = keys.iter().map(|s| k(s)).collect();
    let mut union = expected.clone();
    union.insert(k(argument));
    assert_eq!(
        arr(get(required, "value"))
            .iter()
            .map(Json::canonical)
            .collect::<BTreeSet<_>>(),
        expected
    );
    assert_eq!(
        arr(get(actual, "value"))
            .iter()
            .map(Json::canonical)
            .collect::<BTreeSet<_>>(),
        union
    );
    let evidence = arr(get(condition, "evidence"));
    assert_eq!(evidence.len(), 1);
    let e = node(&w, &evidence[0]);
    assert_eq!(get(get(e, "value"), "kind"), &Json::str("counterexample"));
    assert_eq!(get(get(get(e, "value"), "data"), "left"), &operands[0]);
    assert_eq!(get(get(get(e, "value"), "data"), "right"), &operands[1]);
    let deps = arr(get(reason, "dependencies"));
    assert_eq!(deps.len(), 1);
    let source = node(&w, &deps[0]);
    assert_eq!(get(source, "type"), &Json::str("Expression"));
    assert_eq!(
        get(get(source, "value"), "location"),
        get(reason, "location")
    );
    audit(r);
}
#[test]
fn map_application_owned_valid_images_lexical_call_and_tuple_callee_keep_actual_parts() {
    for name in ["apply", "lexical", "called", "wrapped"] {
        for (key, image) in [("p", "r"), ("q", "s")] {
            let ask = format!("a=evaluate(Applications.{name},m=@v/m,x=@v/{key})");
            let input = fixture::owned("known");
            let before = check_inputs(input.clone(), &mut quiet()).unwrap();
            let r = evaluate_observed_bytes(input, &[&ask], &mut quiet()).unwrap();
            assert_eq!(r.status(), "complete");
            assert_eq!(
                result_value(
                    &r.wire(),
                    "a",
                    Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")])
                ),
                Json::Arr(vec![Json::str("v"), Json::str(image)])
            );
            assert_eq!(
                format!("{:?}", before.archmap()),
                format!("{:?}", r.prepared().inputs().archmap())
            );
            assert_eq!(
                format!("{:?}", before.sources()),
                format!("{:?}", r.prepared().inputs().sources())
            );
            assert!(
                r.wire()
                    .canonical()
                    .contains("Reservations.Migration.states")
            );
            audit(&r);
        }
    }
}
#[test]
fn map_application_plain_if_view_and_composition_keep_each_occurrence() {
    for (name, key, image) in [
        ("lexical", "a", "b"),
        ("choice", "a", "a"),
        ("call", "a", "b"),
        ("composed", "a", "a"),
        ("apply", "b", "a"),
    ] {
        let ask = format!("a=evaluate(Maps.{name},s=@v/s,x=@v/{key})");
        let r = evaluate_observed_bytes(fixture::plain("r1"), &[&ask], &mut quiet()).unwrap();
        assert_eq!(r.status(), "complete");
        assert_eq!(
            result_value(
                &r.wire(),
                "a",
                Json::Arr(vec![Json::str("Ref"), Json::str("Maps.Item")])
            ),
            Json::Arr(vec![Json::str("v"), Json::str(image)])
        );
        audit(&r);
    }
}
#[test]
fn map_application_generated_finite_functions_use_real_binder_and_complete_domain() {
    let r = evaluate_observed_bytes(
        fixture::plain("r1"),
        &["a=evaluate(Maps.generated,x=@v/a)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    assert_eq!(result_value(&w, "a", Json::str("Bool")), Json::Bool(true));
    let ds: Vec<_> = arr(get(&w, "nodes"))
        .iter()
        .filter(|n| get(n, "type") == &Json::str("Domain"))
        .collect();
    assert_eq!(ds.len(), 1);
    assert_eq!(arr(get(get(ds[0], "value"), "elements")).len(), 4);
    audit(&r);
}
#[test]
fn map_application_empty_owned_table_has_real_refuted_domain_condition() {
    let input = fixture::owned("empty");
    assert!(check_inputs(input.clone(), &mut quiet()).is_ok());
    let r = evaluate_observed_bytes(
        input,
        &["a=evaluate(Applications.apply,m=@v/m,x=@v/p)"],
        &mut quiet(),
    )
    .unwrap();
    assert_condition(&r, &[], "p");
}
#[test]
fn map_application_condition_failure_retains_original_operands_and_checked_counterexample() {
    let r = evaluate_observed_bytes(
        fixture::owned("known"),
        &["a=evaluate(Applications.apply,m=@v/m,x=@v/r)"],
        &mut quiet(),
    )
    .unwrap();
    assert_condition(&r, &["p", "q"], "r");
}
#[test]
fn map_application_missing_tables_keep_missing_slot_and_never_make_a_condition_failure() {
    for (input, ask, field) in [
        (
            fixture::owned("missing"),
            "a=evaluate(Applications.apply,m=@v/m,x=@v/p)",
            "Reservations.Migration.states",
        ),
        (
            fixture::plain("r1"),
            "a=evaluate(Maps.absent,s=@v/s,x=@v/a)",
            "Maps.Sample.missing",
        ),
    ] {
        let r = evaluate_observed_bytes(input, &[ask], &mut quiet()).unwrap();
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        let a = answer(&w, "a");
        assert_eq!(get(a, "status"), &Json::str("undetermined"));
        assert!(a.canonical().contains(field));
        assert!(a.canonical().contains("all_completions"));
        assert!(a.canonical().contains("missing_observation"));
        assert!(!a.canonical().contains("condition_failed"));
        assert!(!obj(get(a, "outputs")).contains_key("value"));
        audit(&r);
    }
}
#[test]
fn map_application_provenance_only_changes_return_current_sources() {
    let asks = ["a=evaluate(Maps.apply,s=@v/s,x=@v/a)"];
    let a = evaluate_observed_bytes(fixture::plain("r1"), &asks, &mut quiet()).unwrap();
    let b = evaluate_observed_bytes(fixture::plain("r2"), &asks, &mut quiet()).unwrap();
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
fn map_application_missing_reference_argument_retains_its_original_slot() {
    let input = fixture::owned("missing_key");
    let r = evaluate_observed_bytes(
        input,
        &["a=evaluate(Applications.from_edge,m=@v/m,e=@v/e)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    let a = answer(&w, "a");
    assert!(a.canonical().contains("Reservations.Reserve.from"));
    assert!(a.canonical().contains("missing_observation"));
    assert!(!a.canonical().contains("condition_failed"));
    assert!(!obj(get(a, "outputs")).contains_key("value"));
    audit(&r);
}
#[test]
fn map_application_condition_is_not_a_refuted_law_and_keeps_original_row_context() {
    for ask in [
        "c=check(Applications.holds,m=@v/m,x=@v/r)",
        "c=check(Applications.parameter,a=@v/A,b=@v/B,x=@v/r)",
    ] {
        let r = evaluate_observed_bytes(fixture::owned("known"), &[ask], &mut quiet()).unwrap();
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        let a = answer(&w, "c");
        assert_eq!(get(a, "status"), &Json::str("undetermined"));
        let claim = node(&w, get(a, "claim"));
        assert_eq!(
            get(get(claim, "value"), "predicate"),
            &Json::str("law_holds")
        );
        assert_eq!(
            get(get(claim, "judgment"), "status"),
            &Json::str("undetermined")
        );
        assert!(a.canonical().contains("condition_failed"));
        assert!(arr(get(&w, "nodes")).iter().any(|n| {
            obj(n).get("value").is_some_and(
                |v| matches!(v,Json::Obj(m) if m.get("predicate")==Some(&Json::str("equal"))),
            ) && get(get(n, "judgment"), "status") == &Json::str("refuted")
        }));
        audit(&r);
    }
}
#[test]
fn map_application_condition_provenance_pair_keeps_the_same_math_and_current_origin() {
    let asks = ["a=evaluate(Applications.apply,m=@v/m,x=@v/r)"];
    let a = evaluate_observed_bytes(fixture::owned_revision("known", "r1"), &asks, &mut quiet())
        .unwrap();
    let b = evaluate_observed_bytes(fixture::owned_revision("known", "r2"), &asks, &mut quiet())
        .unwrap();
    assert_eq!(get(&a.wire(), "answers"), get(&b.wire(), "answers"));
    assert_ne!(
        a.prepared().inputs().sources().archmap().bytes(),
        b.prepared().inputs().sources().archmap().bytes()
    );
    for (r, rev) in [(&a, "r1"), (&b, "r2")] {
        assert_eq!(r.prepared().inputs().archmap().sources[0].revision, rev);
        assert_condition(r, &["p", "q"], "r");
    }
}

#[test]
fn map_application_distinct_endpoint_types_and_cross_snapshot_images_are_preserved() {
    let r = evaluate_observed_bytes(
        fixture::distinct(),
        &["a=evaluate(Maps.generated,x=@v/a)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    assert_eq!(result_value(&w, "a", Json::str("Bool")), Json::Bool(true));
    let checked = r.prepared().inputs();
    let mut images = BTreeSet::new();
    let mut evaluations = 0;
    for n in arr(get(&w, "nodes")) {
        if get(n, "type") == &Json::str("Evaluation") {
            let p = get(n, "value");
            let source = node(&w, get(p, "expression"));
            let location = get(get(source, "value"), "location");
            if let Some(Json::Arr(span)) = obj(location).get("span") {
                let [Json::Nat(start), Json::Nat(end)] = span.as_slice() else {
                    continue;
                };
                if &checked.sources().law().bytes()[*start as usize..*end as usize] == b"f(x)" {
                    let v = node(&w, get(p, "value"));
                    assert_eq!(
                        get(v, "type"),
                        &Json::Arr(vec![Json::str("Ref"), Json::str("Maps.Image")])
                    );
                    images.insert(get(v, "value").canonical());
                    evaluations += 1;
                }
            }
        }
    }
    assert_eq!(evaluations, 8);
    assert_eq!(
        images,
        [
            Json::Arr(vec![Json::str("v"), Json::str("x")]).canonical(),
            Json::Arr(vec![Json::str("w"), Json::str("y")]).canonical()
        ]
        .into_iter()
        .collect()
    );
    audit(&r);
}
