#[path = "common/owned_partial_containers.rs"]
#[allow(dead_code)]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
fn f<'a>(j: &'a Json, key: &str) -> &'a Json {
    let Json::Obj(fields) = j else {
        panic!("object")
    };
    &fields[key]
}
fn array(j: &Json) -> &[Json] {
    let Json::Arr(items) = j else { panic!("array") };
    items
}
fn object(j: &Json) -> &std::collections::BTreeMap<String, Json> {
    let Json::Obj(fields) = j else {
        panic!("object")
    };
    fields
}
fn node<'a>(wire: &'a Json, reference: &Json) -> &'a Json {
    array(f(wire, "nodes"))
        .iter()
        .find(|node| f(node, "id") == f(reference, "node"))
        .unwrap()
}
fn answer<'a>(wire: &'a Json, id: &str) -> &'a Json {
    array(f(wire, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn run(unknown: bool, asks: &[&str]) -> Json {
    run_revision(unknown, "r1", asks)
}
fn run_revision(unknown: bool, revision: &str, asks: &[&str]) -> Json {
    let inputs = fixture::input(unknown, revision);
    run_input(inputs, revision, asks)
}
fn run_input(
    inputs: archsig::observed::input::InputSources,
    revision: &str,
    asks: &[&str],
) -> Json {
    let checked = archsig::observed::input::check_inputs(
        inputs.clone(),
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    let result = evaluate_observed_bytes(
        inputs.clone(),
        asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    assert_eq!(result.prepared().inputs().sources(), &inputs);
    assert_eq!(
        result.prepared().inputs().archmap().snapshots,
        checked.archmap().snapshots
    );
    assert_eq!(
        result.prepared().inputs().archmap().origins,
        checked.archmap().origins
    );
    assert_eq!(
        result.prepared().inputs().archmap().sources,
        checked.archmap().sources
    );
    assert_eq!(
        result.prepared().inputs().definitions().vocabularies,
        checked.definitions().vocabularies
    );
    assert_eq!(
        result.prepared().inputs().law().declarations,
        checked.law().declarations
    );
    assert!(
        checked
            .archmap()
            .sources
            .iter()
            .all(|s| s.revision == revision)
    );
    let wire = result.wire();
    assert_ne!(result.status(), "error", "{:?}", f(&wire, "issues"));
    for (index, n) in array(f(&wire, "nodes")).iter().enumerate() {
        let mut refs = Vec::new();
        collect_refs(n, &mut refs);
        assert!(
            refs.iter()
                .all(|id| id.strip_prefix('n').unwrap().parse::<usize>().unwrap() < index)
        );
        if f(n, "type") != &Json::str("Proposition") {
            assert!(!object(n).contains_key("judgment"));
        }
    }
    for a in array(f(&wire, "answers")) {
        if let Some(claim) = object(a).get("claim") {
            let claim = node(&wire, claim);
            assert_eq!(f(claim, "type"), &Json::str("Proposition"));
            assert_eq!(f(f(claim, "judgment"), "status"), f(a, "status"));
        }
    }
    wire
}
fn collect_refs(j: &Json, refs: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => {
            let Json::Str(id) = &m["node"] else {
                panic!("Ref")
            };
            refs.push(id.clone());
        }
        Json::Obj(m) => {
            for value in m.values() {
                collect_refs(value, refs);
            }
        }
        Json::Arr(items) => {
            for value in items {
                collect_refs(value, refs);
            }
        }
        _ => {}
    }
}
fn missing_owner(wire: &Json, id: &str) {
    missing_owner_with_axes(wire, id, &[("z", "Z")]);
}
fn missing_owner_with_axes(wire: &Json, id: &str, axes: &[(&str, &str)]) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    let expected = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("p")),
        ("field", Json::str("Reservations.State.owner")),
    ]);
    let reasons = array(f(a, "reasons"));
    let missing: Vec<_> = reasons
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .collect();
    assert!(!missing.is_empty());
    for reason in missing {
        assert_eq!(f(reason, "missing"), &Json::Arr(vec![expected.clone()]));
        assert!(!array(f(reason, "dependencies")).is_empty());
        for source in array(f(reason, "dependencies")) {
            let source = node(wire, source);
            assert_eq!(f(source, "type"), &Json::str("Expression"));
            assert_eq!(f(f(source, "value"), "kind"), &Json::str("source"));
        }
    }
    assert!(
        reasons
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
    assert!(!object(f(a, "outputs")).contains_key("value"));
    assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
    let owner_type = Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")]);
    let domains: Vec<_> = array(f(wire, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Domain")
                && object(f(n, "value")).get("type") == Some(&owner_type)
        })
        .collect();
    assert!(!domains.is_empty());
    for domain in domains {
        assert_eq!(f(f(domain, "value"), "kind"), &Json::str("finite"));
        let actual: std::collections::BTreeSet<_> = array(f(f(domain, "value"), "elements"))
            .iter()
            .map(|r| {
                let n = node(wire, r);
                assert_eq!(f(n, "type"), &owner_type);
                f(n, "value").canonical()
            })
            .collect();
        // fixtureのsecond=trueによりv/wの双方があり、ownerのRef域は全snapshot。
        let expected: std::collections::BTreeSet<_> = ["v", "w"]
            .into_iter()
            .flat_map(|snapshot| {
                ["A", "B", "Z"]
                    .into_iter()
                    .map(move |s| Json::Arr(vec![Json::str(snapshot), Json::str(s)]).canonical())
            })
            .collect();
        assert_eq!(actual, expected);
    }
    for (name, ty) in axes {
        assert!(
            array(f(f(a, "scope"), "quantifiers"))
                .iter()
                .any(|q| f(q, "kind") == &Json::str("forall")
                    && f(q, "name") == &Json::str(*name)
                    && f(q, "type") == &Json::str(*ty))
        );
    }
}
#[test]
fn unknown_owner_and_free_z_keep_membership_and_missing() {
    let inputs = fixture::input(true, "r1");
    let result = evaluate_observed_bytes(
        inputs.clone(),
        &["x=check(Reservations.ocSomeGood,a=@v/A,p=@v/p)"],
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    assert_eq!(result.prepared().inputs().sources(), &inputs);
    let wire = result.wire();
    assert_eq!(result.status(), "partial", "{:?}", f(&wire, "issues"));
    let answer = &array(f(&wire, "answers"))[0];
    assert_eq!(f(answer, "status"), &Json::str("undetermined"));
    assert!(
        array(f(answer, "reasons"))
            .iter()
            .any(|reason| f(reason, "code") == &Json::str("missing_observation"))
    );
    missing_owner(&wire, "x");
}

#[test]
fn known_owner_free_z_keeps_valid_and_invalid_call_conditions() {
    let wire = run(
        false,
        &[
            "good=check(Reservations.ocSomeGood,a=@v/A,p=@v/p)",
            "bad=check(Reservations.ocSomeGood,a=@v/A,p=@v/r)",
        ],
    );
    assert_eq!(
        f(answer(&wire, "good"), "status"),
        &Json::str("established")
    );
    let bad = answer(&wire, "bad");
    assert_eq!(f(bad, "status"), &Json::str("undetermined"));
    assert!(
        array(f(bad, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
    assert!(
        !array(f(bad, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation"))
    );
    let reason = array(f(bad, "reasons"))
        .iter()
        .find(|r| f(r, "code") == &Json::str("condition_failed"))
        .unwrap();
    let condition = node(&wire, f(f(reason, "details"), "condition"));
    assert_eq!(f(f(condition, "judgment"), "status"), &Json::str("refuted"));
    let operands = array(f(f(condition, "value"), "operands"));
    assert_eq!(
        f(node(&wire, &operands[0]), "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("B")])
    );
    assert_eq!(
        f(node(&wire, &operands[1]), "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("A")])
    );
}

#[test]
fn unknown_owner_free_z_set_keeps_all_owner_completions() {
    let wire = run(
        true,
        &["x=check(Reservations.ocSetGood,a=@v/A,p=@v/p,q=@v/q)"],
    );
    missing_owner(&wire, "x");
}

#[test]
fn unknown_owner_free_z_returned_tuple_keeps_conditions_and_missing() {
    let wire = run(true, &["x=check(Reservations.pcReturned,a=@v/A,p=@v/p)"]);
    missing_owner(&wire, "x");
}

#[test]
fn unknown_owner_free_q_affine_call_keeps_exact_axis_and_missing() {
    let wire = run(true, &["x=check(Reservations.pcQAffine,a=@v/A,p=@v/p)"]);
    missing_owner_with_axes(&wire, "x", &[("q", "Q")]);
}

#[test]
fn unknown_owner_nested_option_list_set_preserves_two_numeric_axes() {
    let wire = run(
        true,
        &["x=check(Reservations.ocNestedGood,a=@v/A,b=@v/B,p=@v/p,q=@v/r)"],
    );
    missing_owner_with_axes(&wire, "x", &[("z", "Z"), ("r", "Q")]);
}

#[test]
fn absent_owned_container_does_not_read_unrelated_owner_slots() {
    let wire = run(true, &["x=evaluate(Reservations.ocEmpty,a=@v/A)"]);
    let a = answer(&wire, "x");
    assert_eq!(f(a, "status"), &Json::str("established"));
    assert_eq!(
        f(node(&wire, f(f(a, "outputs"), "value")), "value"),
        &Json::Bool(true)
    );
    assert!(array(f(a, "reasons")).is_empty());
}

#[test]
fn unknown_owner_call_provenance_changes_keep_math_and_current_input_sources() {
    let asks = ["x=check(Reservations.ocSomeGood,a=@v/A,p=@v/p)"];
    let a = run_revision(true, "r1", &asks);
    let b = run_revision(true, "r2", &asks);
    missing_owner(&a, "x");
    missing_owner(&b, "x");
    assert_ne!(f(&a, "inputs"), f(&b, "inputs"));
    assert_eq!(f(answer(&a, "x"), "status"), f(answer(&b, "x"), "status"));
}

fn two_owner_input() -> archsig::observed::input::InputSources {
    use archsig::json::{JNode, JValue, parse};
    fn convert(n: &JNode) -> Json {
        match &n.value {
            JValue::Bool(v) => Json::Bool(*v),
            JValue::Str(v) => Json::str(v),
            JValue::Num(v) => Json::Nat(v.parse().unwrap()),
            JValue::Arr(v) => Json::Arr(v.iter().map(convert).collect()),
            JValue::Obj(v) => Json::Obj(v.iter().map(|(k, v)| (k.clone(), convert(v))).collect()),
            JValue::Null => panic!("fixtureにnullはない"),
        }
    }
    let input = fixture::input(true, "r1");
    let mut map = convert(&parse(input.archmap().bytes()).unwrap());
    let Json::Obj(m) = &mut map else { panic!() };
    let Json::Arr(snapshots) = m.get_mut("snapshots").unwrap() else {
        panic!()
    };
    snapshots.retain(|s| f(s, "id") != &Json::str("w"));
    for s in snapshots {
        let Json::Obj(s) = s else { panic!() };
        if s["id"] != Json::str("v") {
            continue;
        }
        let Json::Arr(subjects) = s.get_mut("subjects").unwrap() else {
            panic!()
        };
        subjects.retain(|s| f(s, "id") != &Json::str("Z"));
        let Json::Arr(atoms) = s.get_mut("atoms").unwrap() else {
            panic!()
        };
        let before = atoms.len();
        atoms.retain(|a| f(a, "id") != &Json::str("q-owner"));
        assert_eq!(atoms.len() + 1, before);
    }
    archsig::observed::input::InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        input.law().bytes().to_vec(),
        map.canonical().into_bytes(),
    )
}
#[test]
fn two_unknown_owner_slots_keep_four_joint_assignments_and_numeric_axes() {
    let input = two_owner_input();
    let checked = archsig::observed::input::check_inputs(
        input.clone(),
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    let snapshot = checked
        .archmap()
        .snapshots
        .iter()
        .find(|s| s.id == "v")
        .unwrap();
    for subject in ["p", "q"] {
        let owner = snapshot
            .subjects
            .iter()
            .find(|s| s.id == subject)
            .unwrap()
            .fields
            .iter()
            .find(|f| f.name == "Reservations.State.owner")
            .unwrap();
        assert!(matches!(owner.slot, archsig::archmap::Slot::Missing));
    }
    let w = run_input(
        input,
        "r1",
        &["x=check(Reservations.ocNestedGood,a=@v/A,b=@v/B,p=@v/p,q=@v/q)"],
    );
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(!object(f(a, "outputs")).contains_key("value"));
    let facts: std::collections::BTreeSet<_> = array(f(a, "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .flat_map(|r| array(f(r, "missing")))
        .map(Json::canonical)
        .collect();
    let expected: std::collections::BTreeSet<_> = ["p", "q"]
        .into_iter()
        .map(|s| {
            Json::obj([
                ("snapshot", Json::str("v")),
                ("subject", Json::str(s)),
                ("field", Json::str("Reservations.State.owner")),
            ])
            .canonical()
        })
        .collect();
    assert_eq!(facts, expected);
    let ref_ty = Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")]);
    let ty = Json::Arr(vec![Json::str("Tuple"), ref_ty.clone(), ref_ty]);
    let domains: Vec<_> = array(f(&w, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Domain") && object(f(n, "value")).get("type") == Some(&ty)
        })
        .collect();
    assert!(!domains.is_empty());
    for domain in domains {
        let elements = array(f(f(domain, "value"), "elements"));
        assert_eq!(elements.len(), 4);
        let actual: std::collections::BTreeSet<_> = elements
            .iter()
            .map(|r| f(node(&w, r), "value").canonical())
            .collect();
        let expected: std::collections::BTreeSet<_> = ["A", "B"]
            .into_iter()
            .flat_map(|p| {
                ["A", "B"].into_iter().map(move |q| {
                    Json::Arr(vec![
                        Json::Arr(vec![Json::str("v"), Json::str(p)]),
                        Json::Arr(vec![Json::str("v"), Json::str(q)]),
                    ])
                    .canonical()
                })
            })
            .collect();
        assert_eq!(actual, expected);
    }
    for (name, ty) in [("z", "Z"), ("r", "Q")] {
        assert!(
            array(f(f(a, "scope"), "quantifiers"))
                .iter()
                .any(|q| f(q, "kind") == &Json::str("forall")
                    && f(q, "name") == &Json::str(name)
                    && f(q, "type") == &Json::str(ty))
        );
    }
}

#[path = "common/owned_map_calls.rs"]
#[allow(dead_code)]
mod map_fixture;
fn small_map_input(mode: &str) -> archsig::observed::input::InputSources {
    use archsig::json::{JNode, JValue, parse};
    fn convert(n: &JNode) -> Json {
        match &n.value {
            JValue::Bool(v) => Json::Bool(*v),
            JValue::Str(v) => Json::str(v),
            JValue::Num(v) => Json::Nat(v.parse().unwrap()),
            JValue::Arr(v) => Json::Arr(v.iter().map(convert).collect()),
            JValue::Obj(v) => Json::Obj(v.iter().map(|(k, v)| (k.clone(), convert(v))).collect()),
            JValue::Null => panic!("fixtureにnullはない"),
        }
    }
    let input = map_fixture::input(mode, "r1");
    let mut map = convert(&parse(input.archmap().bytes()).unwrap());
    let Json::Obj(m) = &mut map else { panic!() };
    let Json::Arr(snapshots) = m.get_mut("snapshots").unwrap() else {
        panic!()
    };
    assert_eq!(snapshots.len(), 2);
    snapshots.retain(|s| f(s, "id") == &Json::str("v"));
    assert_eq!(snapshots.len(), 1);
    archsig::observed::input::InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        input.law().bytes().to_vec(),
        map.canonical().into_bytes(),
    )
}
#[test]
fn small_owned_map_missing_table_keeps_all_four_tables_and_original_conditions() {
    let w = run_input(
        small_map_input("missing"),
        "r1",
        &["x=evaluate(Applications.mcParameter,a=@v/B,b=@v/B,m=@v/m)"],
    );
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(!object(f(a, "outputs")).contains_key("value"));
    let missing: std::collections::BTreeSet<_> = array(f(a, "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .flat_map(|r| array(f(r, "missing")))
        .map(Json::canonical)
        .collect();
    assert_eq!(
        missing,
        [Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str("m")),
            ("field", Json::str("Reservations.Migration.states"))
        ])
        .canonical()]
        .into_iter()
        .collect()
    );
    assert!(
        array(f(a, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
    let evaluation = node(&w, f(f(a, "outputs"), "evaluation"));
    let domain = node(&w, &array(f(evaluation, "arguments"))[1]);
    assert_eq!(f(domain, "type"), &Json::str("Domain"));
    let values: std::collections::BTreeSet<_> = array(f(f(domain, "value"), "elements"))
        .iter()
        .map(|r| f(node(&w, r), "value").canonical())
        .collect();
    let expected: std::collections::BTreeSet<_> = ["r", "s"]
        .into_iter()
        .flat_map(|first| {
            ["r", "s"].into_iter().map(move |second| {
                Json::Arr(vec![
                    Json::Arr(vec![
                        Json::Arr(vec![Json::str("v"), Json::str("p")]),
                        Json::Arr(vec![Json::str("v"), Json::str(first)]),
                    ]),
                    Json::Arr(vec![
                        Json::Arr(vec![Json::str("v"), Json::str("q")]),
                        Json::Arr(vec![Json::str("v"), Json::str(second)]),
                    ]),
                ])
                .canonical()
            })
        })
        .collect();
    assert_eq!(values, expected);
    let i = small_map_input("unknown_owner");
    archsig::observed::input::check_inputs(
        i.clone(),
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    let unprovided = evaluate_observed_bytes(
        i,
        &["x=evaluate(Applications.mcParameter,a=@v/A,b=@v/B,m=@v/m)"],
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap_err();
    assert!(matches!(
        unprovided,
        archsig::observed::EvaluationFailure::NotImplemented { .. }
    ));
    assert!(unprovided.wire().is_none());
}
