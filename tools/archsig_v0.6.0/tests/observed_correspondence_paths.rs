use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
#[path = "common/correspondence_paths.rs"]
#[allow(dead_code)]
mod fixture;
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(o) = j else { panic!() };
    &o[k]
}
fn array(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!() };
    a
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    array(f(w, "nodes"))
        .iter()
        .find(|n| f(n, "id") == f(r, "node"))
        .unwrap()
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    array(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn value<'a>(w: &'a Json, id: &str) -> &'a Json {
    f(node(w, f(f(answer(w, id), "outputs"), "value")), "value")
}
fn run(mode: &str, asks: &[&str]) -> Json {
    let input = fixture::input(mode, "r1");
    let r = evaluate_observed_bytes(
        input.clone(),
        asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    assert_eq!(r.prepared().inputs().sources(), &input);
    assert!(
        matches!(r.status(), "complete" | "partial"),
        "{:?}",
        f(&r.wire(), "issues")
    );
    r.wire()
}
#[test]
fn correspondence_path_keeps_original_generator_endpoints_option_and_nested_refs() {
    let w = run(
        "normal",
        &[
            "x=evaluate(Reservations.step,m=@v/m)",
            "maybe=evaluate(Reservations.maybe,m=@v/m)",
            "nested=evaluate(Reservations.nested,m=@v/m)",
            "first=evaluate(Reservations.first,m=@v/m)",
            "last=evaluate(Reservations.last,m=@v/m)",
        ],
    );
    let p = value(&w, "x");
    assert_eq!(array(f(p, "generators")).len(), 1);
    assert_eq!(
        f(node(&w, &array(f(p, "generators"))[0]), "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("m")])
    );
    for (k, id) in [("source", "A"), ("target", "B")] {
        assert_eq!(
            f(node(&w, f(p, k)), "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(id)])
        );
    }
    assert_eq!(
        value(&w, "first"),
        &Json::Arr(vec![Json::str("v"), Json::str("A")])
    );
    assert_eq!(
        value(&w, "last"),
        &Json::Arr(vec![Json::str("v"), Json::str("B")])
    );
    let option_path = f(node(&w, f(value(&w, "maybe"), "some")), "value");
    assert_eq!(
        f(node(&w, &array(f(option_path, "generators"))[0]), "value"),
        f(node(&w, &array(f(p, "generators"))[0]), "value")
    );
    let list = array(f(node(&w, f(value(&w, "nested"), "some")), "value"));
    assert_eq!(list.len(), 2);
    for (i, item) in list.iter().enumerate() {
        let tuple = array(f(node(&w, item), "value"));
        assert_eq!(f(node(&w, &tuple[0]), "value"), &Json::Bool(i == 0));
        assert_eq!(
            array(f(f(node(&w, &tuple[1]), "value"), "generators")).len(),
            1
        );
    }
}
#[test]
fn correspondence_full_action_distinguishes_self_from_identity_and_equal_words() {
    let w = run(
        "normal",
        &[
            "same=evaluate(Reservations.same,m=@v/m,n=@v/alias)",
            "self=evaluate(Reservations.self_action,m=@v/self)",
            "left=evaluate(Reservations.left,m=@v/m)",
            "right=evaluate(Reservations.right,m=@v/m)",
            "word=evaluate(Reservations.different_word,i=@v/self,m=@v/m)",
            "joined=evaluate(Reservations.join,m=@v/self,n=@v/m)",
        ],
    );
    for (id, want) in [
        ("same", true),
        ("self", false),
        ("left", true),
        ("right", true),
        ("word", true),
    ] {
        assert_eq!(value(&w, id), &Json::Bool(want));
    }
    assert_eq!(array(f(value(&w, "joined"), "generators")).len(), 2);
}
#[test]
fn correspondence_invalid_then_keeps_typed_condition_and_transitive_dependency() {
    let w = run(
        "normal",
        &[
            "seed=evaluate(Reservations.seed)",
            "prior=check(Reservations.prior)",
            "bad=evaluate(Reservations.join,m=@v/m,n=@v/m)",
            "used=evaluate(Reservations.keep,p=$bad.value)",
            "later=evaluate(Reservations.seed)",
        ],
    );
    let a = answer(&w, "bad");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    let reason = array(f(a, "reasons"))
        .iter()
        .find(|r| f(r, "code") == &Json::str("condition_failed"))
        .unwrap();
    let condition = node(&w, f(f(reason, "details"), "condition"));
    let operands = array(f(f(condition, "value"), "operands"));
    assert_eq!(operands.len(), 2);
    for (r, name) in operands.iter().zip(["B", "A"]) {
        let n = node(&w, r);
        assert_eq!(
            f(n, "type"),
            &Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")])
        );
        assert_eq!(
            f(n, "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(name)])
        );
    }
    assert!(
        array(f(answer(&w, "used"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("dependency_blocked"))
    );
    assert_eq!(value(&w, "seed"), &Json::str("1"));
    assert_eq!(value(&w, "later"), &Json::str("1"));
    assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
}
#[test]
fn correspondence_arrow_endpoint_structure_failure_keeps_original_condition() {
    let w = run(
        "bad_endpoint",
        &[
            "seed=evaluate(Reservations.seed)",
            "prior=check(Reservations.prior)",
            "bad=evaluate(Reservations.step,m=@v/m)",
            "used=evaluate(Reservations.keep,p=$bad.value)",
            "later=evaluate(Reservations.seed)",
        ],
    );
    assert_eq!(f(answer(&w, "bad"), "status"), &Json::str("undetermined"));
    assert!(
        array(f(answer(&w, "bad"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
    assert!(
        array(f(answer(&w, "used"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("dependency_blocked"))
    );
    assert_eq!(value(&w, "seed"), &Json::str("1"));
    assert_eq!(value(&w, "later"), &Json::str("1"));
    assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
}
fn missing(mode: &str, field: &str) {
    let w = run(
        mode,
        &[
            "seed=evaluate(Reservations.seed)",
            "x=evaluate(Reservations.step,m=@v/m)",
            "used=evaluate(Reservations.keep,p=$x.value)",
        ],
    );
    assert_eq!(f(answer(&w, "x"), "status"), &Json::str("undetermined"));
    assert!(matches!(f(answer(&w,"x"),"outputs"),Json::Obj(m)if !m.contains_key("value")));
    let reasons = format!("{:?}", f(answer(&w, "x"), "reasons"));
    assert!(reasons.contains("missing_observation"), "{reasons}");
    assert!(reasons.contains(field), "{reasons}");
    assert_eq!(value(&w, "seed"), &Json::str("1"));
    assert!(format!("{:?}", f(answer(&w, "used"), "reasons")).contains("dependency_blocked"));
}
#[test]
fn correspondence_missing_map_preserves_original_slot_and_blocks_dependency() {
    missing("missing_map", "Reservations.Migration.states");
}
#[test]
fn correspondence_missing_endpoint_is_forced_by_actual_map_constraints() {
    let w = run(
        "missing_to",
        &[
            "x=evaluate(Reservations.step,m=@v/m)",
            "u=evaluate(Reservations.right,m=@v/m)",
        ],
    );
    assert_eq!(f(answer(&w, "x"), "status"), &Json::str("established"));
    assert_eq!(
        f(node(&w, f(value(&w, "x"), "target")), "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("B")])
    );
    assert_eq!(value(&w, "u"), &Json::Bool(true));
    assert!(format!("{:?}", f(answer(&w, "x"), "reasons")).contains("Reservations.Migration.to"));
}
#[test]
fn correspondence_missing_owner_is_forced_by_map_and_subject_is_retained() {
    let w = run("missing_owner", &["x=evaluate(Reservations.step,m=@v/m)"]);
    assert_eq!(f(answer(&w, "x"), "status"), &Json::str("established"));
    assert!(format!("{:?}", f(answer(&w, "x"), "reasons")).contains("Reservations.State.owner"));
    assert_eq!(array(f(value(&w, "x"), "generators")).len(), 1);
}
#[test]
fn correspondence_missing_target_atom_is_not_created_by_completion() {
    missing("missing_field", "Reservations.State.free");
}
#[test]
fn correspondence_current_provenance_pair_keeps_math_and_checked_input_tables() {
    use archsig::observed::input::check_inputs;
    let asks = [
        "x=evaluate(Reservations.step,m=@v/m)",
        "same=evaluate(Reservations.same,m=@v/m,n=@v/alias)",
    ];
    let mut wires = vec![];
    for revision in ["r1", "r2"] {
        let input = fixture::input("normal", revision);
        let checked = check_inputs(input.clone(), &mut Control::unlimited()).unwrap();
        let r = evaluate_observed_bytes(input.clone(), &asks, &mut Control::unlimited()).unwrap();
        assert_eq!(r.prepared().inputs().sources(), &input);
        assert_eq!(r.prepared().inputs().definitions(), checked.definitions());
        assert_eq!(
            format!("{:?}", r.prepared().inputs().archmap()),
            format!("{:?}", checked.archmap())
        );
        assert_eq!(
            format!("{:?}", r.prepared().inputs().law()),
            format!("{:?}", checked.law())
        );
        wires.push(r.wire());
    }
    assert_eq!(f(&wires[0], "answers"), f(&wires[1], "answers"));
    assert_eq!(f(&wires[0], "nodes"), f(&wires[1], "nodes"));
    assert_ne!(f(&wires[0], "inputs"), f(&wires[1], "inputs"));
}
#[test]
fn correspondence_single_completion_map_keeps_missing_and_shared_unit_result() {
    let w = run(
        "missing_arrow_map",
        &[
            "x=evaluate(Reservations.step,m=@v/m)",
            "same=evaluate(Reservations.unknown_same,m=@v/m)",
            "u=evaluate(Reservations.right,m=@v/m)",
        ],
    );
    assert_eq!(f(answer(&w, "x"), "status"), &Json::str("established"));
    for id in ["same", "u"] {
        assert_eq!(value(&w, id), &Json::Bool(true));
    }
    assert!(
        format!("{:?}", f(answer(&w, "x"), "reasons")).contains("Reservations.Migration.reserves")
    );
}
#[path = "common/aligned_paths.rs"]
mod aligned;
#[test]
fn correspondence_alignment_transports_reference_containers_set_collision_and_unequal_quantity_types()
 {
    let input = aligned::input(false);
    let r = evaluate_observed_bytes(
        input,
        &[
            "x=evaluate(Flow.step,m=@v/m)",
            "maybe=evaluate(Flow.maybe,m=@v/m)",
            "left=evaluate(Flow.left,m=@v/m)",
            "right=evaluate(Flow.right,m=@v/m)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    assert_eq!(value(&w, "left"), &Json::Bool(true));
    assert_eq!(value(&w, "right"), &Json::Bool(true));
    assert_eq!(array(f(value(&w, "x"), "generators")).len(), 1);
    assert_eq!(
        array(f(
            f(node(&w, f(value(&w, "maybe"), "some")), "value"),
            "generators"
        ))
        .len(),
        1
    );
    let r2 = evaluate_observed_bytes(
        aligned::input(true),
        &["x=evaluate(Flow.step,m=@v/m)"],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(r2.status(), "complete");
}
#[test]
fn correspondence_alignment_rejects_list_multiplicity_option_and_set_reference_mismatch() {
    for kind in 0..3 {
        let r = evaluate_observed_bytes(
            aligned::mismatched_input(kind),
            &["x=evaluate(Flow.step,m=@v/m)"],
            &mut Control::unlimited(),
        )
        .unwrap();
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        assert_eq!(f(answer(&w, "x"), "status"), &Json::str("undetermined"));
        assert!(format!("{:?}", f(answer(&w, "x"), "reasons")).contains("condition_failed"));
    }
}
#[test]
fn correspondence_missing_declared_target_root_field_is_condition_failure() {
    let r = evaluate_observed_bytes(
        aligned::unmatched_root_field_input(),
        &["x=evaluate(Flow.step,m=@v/m)"],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    assert!(format!("{:?}", f(answer(&w, "x"), "reasons")).contains("condition_failed"));
}
