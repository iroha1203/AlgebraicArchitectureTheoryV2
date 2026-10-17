//! 検査済みMap表の値・等値を三入力から確認する。
#[path = "common/known_map.rs"]
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
use std::collections::BTreeMap;
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

fn map_type() -> Json {
    Json::Arr(vec![
        Json::str("Map"),
        Json::Arr(vec![Json::str("Ref"), Json::str("Maps.Item")]),
        Json::Arr(vec![Json::str("Ref"), Json::str("Maps.Item")]),
    ])
}
fn expected() -> Json {
    Json::Arr(
        ["a", "b"]
            .iter()
            .map(|k| {
                Json::Arr(vec![
                    Json::Arr(vec![Json::str("v"), Json::str(*k)]),
                    Json::Arr(vec![Json::str("v"), Json::str("a")]),
                ])
            })
            .collect(),
    )
}
#[test]
fn known_map_values_and_extensional_equality_keep_original_pairs() {
    let input = sources("r1");
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let before = format!("{:?}", checked.archmap());
    let result = evaluate_observed_bytes(
        input,
        &[
            "read=evaluate(Maps.read,s=@v/s)",
            "eq=evaluate(Maps.equal,s=@v/s)",
            "ne=evaluate(Maps.unequal,s=@v/s)",
            "same=check(Maps.same,s=@v/s)",
            "changed=check(Maps.changed,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete");
    let wire = result.wire();
    assert_eq!(value(&wire, "read", map_type()), &expected());
    assert_eq!(value(&wire, "eq", Json::str("Bool")), &Json::Bool(true));
    assert_eq!(value(&wire, "ne", Json::str("Bool")), &Json::Bool(true));
    assert_eq!(
        get(answer(&wire, "same"), "status"),
        &Json::str("established")
    );
    assert_eq!(
        get(answer(&wire, "changed"), "status"),
        &Json::str("refuted")
    );
    assert_eq!(
        format!("{:?}", result.prepared().inputs().archmap()),
        before
    );
}

#[test]
fn known_map_wrappers_and_calls_keep_types_and_set_extensionality() {
    let result = evaluate_observed_bytes(
        sources("r1"),
        &[
            "w=evaluate(Maps.wrapped,s=@v/s)",
            "choice=evaluate(Maps.choice,s=@v/s)",
            "empty=evaluate(Maps.empty,s=@v/s)",
            "absent=evaluate(Maps.absent,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "partial");
    let wire = result.wire();
    let m = map_type();
    let option = Json::Arr(vec![Json::str("Option"), m.clone()]);
    let list = Json::Arr(vec![Json::str("List"), m.clone()]);
    let set = Json::Arr(vec![Json::str("Set"), m.clone()]);
    let wrapped_type = Json::Arr(vec![Json::str("Tuple"), m.clone(), option, list, set]);
    // All these types are primitive encodings: pairs remain refs, not invented result nodes.
    let reversed = Json::Arr(array(&expected()).iter().rev().cloned().collect());
    assert_eq!(
        value(&wire, "w", wrapped_type),
        &Json::Arr(vec![
            expected(),
            Json::obj([("some", expected())]),
            Json::Arr(vec![expected(), reversed]),
            Json::Arr(vec![expected()])
        ])
    );
    assert_eq!(value(&wire, "choice", m), &expected());
    let void = Json::Arr(vec![Json::str("Ref"), Json::str("Maps.Void")]);
    assert_eq!(
        value(
            &wire,
            "empty",
            Json::Arr(vec![Json::str("Map"), void.clone(), void])
        ),
        &Json::Arr(vec![])
    );
    let missing = answer(&wire, "absent");
    assert_eq!(get(missing, "status"), &Json::str("undetermined"));
    assert!(!object(get(missing, "outputs")).contains_key("value"));
    assert!(missing.canonical().contains("Maps.Sample.missing"));
    assert!(missing.canonical().contains("missing_observation"));
    assert!(missing.canonical().contains("all_completions"));
}
#[test]
fn known_owned_map_reads_original_reservations_owner_checked_pairs() {
    let definitions = include_bytes!("fixtures/reservations.atoms.json");
    let mut law = include_str!("fixtures/reservations.law").to_string();
    let close = law.rfind('}').unwrap();
    law.insert_str(
        close,
        "view table(m:Migration):Map<State,State> = m.states;",
    );
    let source = InputSources::from_bytes(
        vec![definitions.to_vec()],
        law.into_bytes(),
        include_bytes!("fixtures/reservations.archmap.json").to_vec(),
    );
    let checked = check_inputs(source.clone(), &mut quiet()).unwrap();
    let original = format!("{:?}", checked.archmap());
    let result = evaluate_observed_bytes(
        source,
        &["a=evaluate(Reservations.table,m=@v/m)"],
        &mut quiet(),
    )
    .unwrap();
    let t = Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")]);
    let wire = result.wire();
    let expected = Json::Arr(
        [("p", "r"), ("q", "s")]
            .iter()
            .map(|(a, b)| {
                Json::Arr(vec![
                    Json::Arr(vec![Json::str("v"), Json::str(*a)]),
                    Json::Arr(vec![Json::str("v"), Json::str(*b)]),
                ])
            })
            .collect(),
    );
    assert_eq!(
        value(&wire, "a", Json::Arr(vec![Json::str("Map"), t.clone(), t])),
        &expected
    );
    assert_eq!(
        format!("{:?}", result.prepared().inputs().archmap()),
        original
    );
}
#[test]
fn known_map_provenance_pairs_preserve_answers_and_current_sources() {
    let asks = [
        "v=evaluate(Maps.read,s=@v/s)",
        "eq=check(Maps.same,s=@v/s)",
        "ne=check(Maps.changed,s=@v/s)",
    ];
    let a = evaluate_observed_bytes(sources("r1"), &asks, &mut quiet()).unwrap();
    let b = evaluate_observed_bytes(sources("r2"), &asks, &mut quiet()).unwrap();
    let x = a.wire();
    let y = b.wire();
    assert_eq!(get(&x, "answers"), get(&y, "answers"));
    assert_ne!(
        a.prepared().inputs().sources().archmap().bytes(),
        b.prepared().inputs().sources().archmap().bytes()
    );
    for result in [&a, &b] {
        let wire = result.wire();
        let mut seen = std::collections::BTreeSet::new();
        fn refs(j: &Json, rs: &mut Vec<String>) {
            match j {
                Json::Obj(m) if m.len() == 1 && m.contains_key("node") => {
                    rs.push(text(&m["node"]).into())
                }
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
        let mut facts = 0;
        for node in array(get(&wire, "nodes")) {
            let mut rs = vec![];
            refs(node, &mut rs);
            assert!(rs.iter().all(|r| seen.contains(r)));
            assert!(seen.insert(text(get(node, "id")).to_string()));
            if get(node, "type") != &Json::str("Proposition") {
                assert!(!object(node).contains_key("judgment"));
            }
            for fact in array(get(node, "support")) {
                if let Some(atom) = object(fact).get("atom") {
                    let map = result.prepared().inputs().archmap();
                    let subject = map
                        .snapshots
                        .iter()
                        .find(|s| s.id == text(get(fact, "snapshot")))
                        .unwrap()
                        .subjects
                        .iter()
                        .find(|s| s.id == text(get(fact, "subject")))
                        .unwrap();
                    let field = subject
                        .fields
                        .iter()
                        .find(|f| f.name == text(get(fact, "field")))
                        .unwrap();
                    let archsig::archmap::Slot::Known {
                        atom: actual,
                        origin,
                        ..
                    } = &field.slot
                    else {
                        panic!("known")
                    };
                    assert_eq!(atom, &Json::str(actual));
                    let origin = map.origins.iter().find(|o| &o.id == origin).unwrap();
                    assert_eq!(origin.mode, archsig::archmap::Mode::Specification);
                    for loc in &origin.locations {
                        let source = map.sources.iter().find(|s| s.id == loc.source).unwrap();
                        assert_eq!(source.uri, "urn:fixture:known-map");
                        assert_eq!(
                            source.revision,
                            if std::ptr::eq(result, &a) { "r1" } else { "r2" }
                        );
                        assert!(loc.span.is_some());
                    }
                    facts += 1;
                }
            }
        }
        assert!(facts > 0);
    }
}

#[test]
fn known_map_values_do_not_enable_type_universes_or_application() {
    let input = sources("r1");
    let mut law = String::from_utf8(input.law().bytes().to_vec()).unwrap();
    let close = law.rfind('}').unwrap();
    law.insert_str(
        close,
        "view all():Bool=forall f:Map<Item,Item> . f=f;view apply(s:Sample,x:Item):Item=s.m(x);",
    );
    let d = maps::DEFINITIONS.as_bytes();
    let checked = check_definitions(&[("definition0", d)]).unwrap();
    let digest = &checked.vocabularies["Maps"].digest;
    let input = InputSources::from_bytes(
        vec![d.to_vec()],
        law.into_bytes(),
        maps::archmap(digest, "r1").into_bytes(),
    );
    for ask in [
        "all=evaluate(Maps.all)",
        "apply=evaluate(Maps.apply,s=@v/s,x=@v/a)",
    ] {
        let failure = evaluate_observed_bytes(input.clone(), &[ask], &mut quiet()).unwrap_err();
        assert!(failure.wire().is_none());
        assert!(matches!(
            failure,
            archsig::observed::EvaluationFailure::NotImplemented { .. }
        ));
    }
}

#[test]
fn owned_map_primitive_wrappers_erase_value_types_and_preserve_original_owner_slots() {
    let definitions = maps::OWNED_DEFINITIONS.as_bytes();
    let d = check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies["Maps"].digest;
    let input = InputSources::from_bytes(
        vec![definitions.to_vec()],
        maps::owned_law(digest).into_bytes(),
        maps::owned_archmap(digest).into_bytes(),
    );
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let before = format!("{:?}", checked.archmap());
    let m = map_type();
    let list = Json::Arr(vec![Json::str("List"), m.clone()]);
    let set = Json::Arr(vec![Json::str("Set"), m.clone()]);
    let option = Json::Arr(vec![Json::str("Option"), m.clone()]);
    let table = Json::Arr(vec![Json::Arr(vec![
        Json::Arr(vec![Json::str("v"), Json::str("a")]),
        Json::Arr(vec![Json::str("v"), Json::str("a")]),
    ])]);
    let some = Json::obj([("some", table.clone())]);
    let cases = [
        ("emptylist", list.clone(), Json::Arr(vec![])),
        ("emptyset", set.clone(), Json::Arr(vec![])),
        (
            "absent",
            option.clone(),
            Json::obj([("none", Json::Bool(true))]),
        ),
        ("tables", list, Json::Arr(vec![table.clone()])),
        ("bag", set, Json::Arr(vec![table.clone()])),
        ("maybe", option.clone(), some.clone()),
        (
            "nested",
            Json::Arr(vec![
                Json::str("Tuple"),
                Json::str("Unit"),
                Json::Arr(vec![Json::str("List"), option]),
            ]),
            Json::Arr(vec![Json::Arr(vec![]), Json::Arr(vec![some])]),
        ),
    ];
    let mut failures = vec![];
    for (name, ty, expected) in cases {
        let ask = format!("a=evaluate(Maps.{name},s=@v/h)");
        let result = evaluate_observed_bytes(input.clone(), &[&ask], &mut quiet()).unwrap();
        if result.status() != "complete" {
            failures.push((name.to_string(), result.status().to_string()));
            continue;
        }
        assert_eq!(value(&result.wire(), "a", ty), &expected);
        assert_eq!(
            format!("{:?}", result.prepared().inputs().archmap()),
            before
        );
        let owner = &result.prepared().inputs().archmap().snapshots[0]
            .subjects
            .iter()
            .find(|s| s.id == "h")
            .unwrap()
            .fields
            .iter()
            .find(|f| f.name == "Maps.Holder.owner")
            .unwrap()
            .slot;
        assert!(
            matches!(owner,archsig::archmap::Slot::Known{value:archsig::archmap::Value::Ref{snapshot,subject},..} if snapshot=="v"&&subject=="r")
        );
    }
    assert!(
        failures.is_empty(),
        "合法なOwned Map wrapperが失敗: {failures:?}"
    );
}
