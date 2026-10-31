use super::*;
use crate::{
    construction::{construct, readings::object_reading_instances},
    control::{Limits, Usage},
};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/primitive_valuation_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn input(body: &str) -> Arc<CheckedInputs> {
    let map = fixture::MAP.replace(r#""subjects":["#, r#""subjects":[{"id":"r","type":"Pattern.Part","origin":"model"},"#)
        .replace(r#""atoms":["#, r#""atoms":[{"id":"or","subject":"r","field":"Pattern.Part.owner","value":["v","r2"],"origin":"model"},{"id":"xr","subject":"r","field":"Pattern.Part.quantity","value":"1","origin":"model"},"#);
    fixture::with_body(&map, body)
}
fn readings(inputs: &CheckedInputs, root: &str) -> ObjectReadingInstances {
    let configuration = construct(inputs, "Selected", "v", root, &mut quiet()).unwrap();
    object_reading_instances(inputs, &configuration, &mut quiet()).unwrap()
}
fn index(readings: &ObjectReadingInstances, name: &str) -> usize {
    readings
        .objects()
        .iter()
        .position(|o| o.identity().subject().subject == name)
        .unwrap()
}
fn reference(name: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: name.into(),
        entity: "Pattern.Part".into(),
    }
}
fn selected(names: &[&str]) -> Vec<(String, Vec<(String, Scalar)>)> {
    names
        .iter()
        .map(|name| {
            (
                format!("Selected.{name}"),
                vec![("c".into(), reference("p"))],
            )
        })
        .collect()
}
fn names(r: &FiniteLawFamilyValuations) -> Vec<&str> {
    r.positions().iter().map(|f| f.subject.as_str()).collect()
}
fn indicators(r: &FiniteLawFamilyValuations, column: usize) -> Vec<String> {
    r.integer_function(column, None, &mut quiet())
        .unwrap()
        .values()
        .iter()
        .map(ToString::to_string)
        .collect()
}
const ALL: &str = "law required all(c:Part):forall x:Part . x.quantity=0;law optional copy(c:Part):forall x:Part . x.quantity=0;";

#[test]
fn base_owned_and_other_root_use_distinct_shared_domains_and_integer_functions() {
    let inputs = input(ALL);
    let original = inputs.sources().clone();
    let a = readings(&inputs, "root");
    let b = readings(&inputs, "r2");
    let base = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "root"),
        &selected(&["all", "copy"]),
        &mut quiet(),
    )
    .unwrap();
    let part = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "p"),
        &selected(&["all", "copy"]),
        &mut quiet(),
    )
    .unwrap();
    let other = finite_object_law_family_valuations(
        &inputs,
        &b,
        index(&b, "r2"),
        &selected(&["all", "copy"]),
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(names(&base), ["p", "q"]);
    assert_eq!(names(&part), ["p"]);
    assert_eq!(names(&other), ["r"]);
    assert_eq!(base.domain().len(), 4);
    assert_eq!(part.domain().len(), 2);
    assert_eq!(other.domain().len(), 2);
    assert_eq!(indicators(&base, 0), ["0", "1", "1", "1"]);
    assert_eq!(indicators(&part, 0), ["0", "1"]);
    assert_eq!(indicators(&other, 0), ["0", "1"]);
    for r in [&base, &part, &other] {
        assert!(r.is_complete());
        assert!(r.domain_complete());
        assert_eq!(r.required_zero(), Some([0].as_slice()));
        assert_eq!(indicators(r, 0), indicators(r, 1));
        assert!(r.columns()[0].required());
        assert!(!r.columns()[1].required());
        assert_eq!(r.columns()[0].bindings(), selected(&["all"])[0].1);
        r.recheck(&inputs, &mut quiet()).unwrap();
    }
    assert_eq!(base.observed_point(), Some(1));
    assert_eq!(part.observed_point(), Some(0));
    assert_eq!(other.observed_point(), Some(1));
    assert_eq!(
        base.object_identity(),
        Some(a.objects()[index(&a, "root")].identity())
    );
    part.recheck_on_object(&inputs, &a, index(&a, "p"), &mut quiet())
        .unwrap();
    assert!(
        other
            .recheck_on_object(&inputs, &a, index(&a, "p"), &mut quiet())
            .is_err()
    );
    assert_eq!(inputs.sources(), &original);
}

#[test]
fn ordinary_global_entry_still_reads_all_roots() {
    let inputs = input(ALL);
    let global =
        finite_law_family_valuations(&inputs, &selected(&["all", "copy"]), &mut quiet()).unwrap();
    assert_eq!(global.object_identity(), None);
    assert_eq!(names(&global), ["p", "q", "r"]);
    assert_eq!(global.domain().len(), 8);
    assert_eq!(
        indicators(&global, 0),
        ["0", "1", "1", "1", "1", "1", "1", "1"]
    );
    assert_eq!(global.observed_point(), Some(3));
    global.recheck(&inputs, &mut quiet()).unwrap();
}

#[test]
fn fixed_external_reference_is_not_removed_by_the_local_quantifier_domain() {
    let inputs = input("law required external(c:Part,ext:Part):ext.quantity=0;");
    let a = readings(&inputs, "root");
    let choice = vec![(
        "Selected.external".into(),
        vec![("c".into(), reference("p")), ("ext".into(), reference("r"))],
    )];
    let r = finite_object_law_family_valuations(&inputs, &a, index(&a, "p"), &choice, &mut quiet())
        .unwrap();
    assert_eq!(names(&r), ["r"]);
    assert_eq!(indicators(&r, 0), ["0", "1"]);
    assert_eq!(r.observed_point(), Some(1));
    assert_eq!(r.columns()[0].bindings(), choice[0].1);
    r.recheck_on_object(&inputs, &a, index(&a, "p"), &mut quiet())
        .unwrap();
}

#[test]
fn composite_reference_leaves_keep_their_full_typed_domain() {
    let inputs =
        input("law required all(c:Part):forall xs:Set<Part> . forall x in xs . x.quantity=0;");
    let a = readings(&inputs, "root");
    let r = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "p"),
        &selected(&["all"]),
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(names(&r), ["p", "q", "r"]);
    assert_eq!(r.domain().len(), 8);
    assert_eq!(indicators(&r, 0), ["0", "1", "1", "1", "1", "1", "1", "1"]);
    r.recheck(&inputs, &mut quiet()).unwrap();
}

#[test]
fn equal_numeric_results_cannot_be_consumed_as_another_object_or_global_family() {
    let inputs = input("law required constant(c:Part):true;");
    let a = readings(&inputs, "root");
    let r = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "p"),
        &selected(&["constant"]),
        &mut quiet(),
    )
    .unwrap();
    let q = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "q"),
        &selected(&["constant"]),
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(indicators(&r, 0), indicators(&q, 0));
    assert_ne!(r.object_identity(), q.object_identity());
    assert!(
        r.recheck_on_object(&inputs, &a, index(&a, "q"), &mut quiet())
            .is_err()
    );
    let global =
        finite_law_family_valuations(&inputs, &selected(&["constant"]), &mut quiet()).unwrap();
    assert!(
        global
            .recheck_on_object(&inputs, &a, index(&a, "p"), &mut quiet())
            .is_err()
    );
    assert!(
        r.integer_ring(&mut quiet())
            .unwrap()
            .add(
                &r.integer_function(0, None, &mut quiet()).unwrap(),
                &q.integer_function(0, None, &mut quiet()).unwrap(),
                &mut quiet()
            )
            .is_err()
    );
}

#[test]
fn recheck_rejects_forged_object_domain_rows_support_and_current_input_origin() {
    let inputs = input(ALL);
    let a = readings(&inputs, "root");
    let p = index(&a, "p");
    let q = index(&a, "q");
    for mode in 0..6 {
        let mut r =
            finite_object_law_family_valuations(&inputs, &a, p, &selected(&["all"]), &mut quiet())
                .unwrap();
        match mode {
            0 => {
                Arc::make_mut(r.object.as_mut().unwrap()).domain =
                    Arc::new(ObjectDomain::from_readings(&inputs, &a, q, &quiet()).unwrap())
            }
            1 => r.columns[0].rows[0].indicator = Some(1.into()),
            2 => r.columns[0].rows[0].support.clear(),
            3 => r.columns[0].rows[0].scope.readings.clear(),
            4 => r.domain.reverse(),
            _ => r.required_zero = Some(vec![1]),
        }
        assert!(
            r.recheck_on_object(&inputs, &a, p, &mut quiet()).is_err(),
            "mode={mode}"
        );
    }
    let r = finite_object_law_family_valuations(&inputs, &a, p, &selected(&["all"]), &mut quiet())
        .unwrap();
    let changed = fixture::with_body(
        &String::from_utf8(inputs.sources().archmap().bytes().to_vec())
            .unwrap()
            .replace("内部候補試験。", "改訂された由来。"),
        ALL,
    );
    assert!(r.recheck(&changed, &mut quiet()).is_err());
}

#[test]
fn missing_observed_value_keeps_a_complete_domain_without_an_observed_point() {
    let inputs=fixture::with_body(&fixture::MAP.replace(r#",{"id":"xp","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"}"#,""),"law required zero(c:Part):c.quantity=0;");
    let a = readings(&inputs, "root");
    let r = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "p"),
        &selected(&["zero"]),
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.observed_point(), None);
    assert_eq!(r.domain().len(), 2);
    assert_eq!(indicators(&r, 0), ["0", "1"]);
    assert_eq!(r.required_zero(), Some([0].as_slice()));
    assert!(r.is_complete());
}

#[test]
fn fixed_stops_keep_completed_rows_and_their_object_origin_without_total_functions() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let inputs = input(ALL);
    let a = readings(&inputs, "root");
    let root = index(&a, "root");
    for mode in 0..3 {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let mut c = Control::new(
            Limits {
                time_ms: (mode == 1).then_some(1),
                memory_mib: (mode == 2).then_some(1),
            },
            move |point| {
                if point == Checkpoint::FiniteLawEvaluation {
                    count.set(count.get() + 1);
                }
                let stop = count.get() >= 3;
                Usage {
                    signal: (stop && mode == 0).then_some(Signal::Term),
                    elapsed_ms: u128::from(stop && mode == 1),
                    memory_mib: u128::from(stop && mode == 2),
                }
            },
        );
        let err = finite_object_law_family_valuations(
            &inputs,
            &a,
            root,
            &selected(&["all", "copy"]),
            &mut c,
        )
        .err()
        .expect("固定停止");
        assert!(matches!(err.cause, ValidationFailure::Stop(_)));
        let partial = err.partial.unwrap();
        assert_eq!(
            partial.object_identity(),
            Some(a.objects()[root].identity())
        );
        assert!(!partial.is_complete());
        assert!(!partial.columns()[0].rows().is_empty());
        assert!(partial.integer_function(0, None, &mut quiet()).is_err());
        assert!(partial.required_quotient(&mut quiet()).is_err());
    }
}

#[test]
fn shared_required_ideal_and_projection_use_the_object_family_without_changing_epsilon() {
    let inputs =
        input("law required zero(c:Part):c.quantity=0;law optional other(c:Part):c.quantity=1;");
    let a = readings(&inputs, "root");
    let choices = vec![
        ("Selected.zero".into(), vec![("c".into(), reference("p"))]),
        ("Selected.zero".into(), vec![("c".into(), reference("q"))]),
        ("Selected.other".into(), vec![("c".into(), reference("p"))]),
    ];
    let r =
        finite_object_law_family_valuations(&inputs, &a, index(&a, "root"), &choices, &mut quiet())
            .unwrap();
    assert_eq!(names(&r), ["p", "q"]);
    assert_eq!(indicators(&r, 0), ["0", "0", "1", "1"]);
    assert_eq!(indicators(&r, 1), ["0", "1", "0", "1"]);
    assert_eq!(indicators(&r, 2), ["1", "1", "0", "0"]);
    let quotient = r.required_quotient(&mut quiet()).unwrap();
    assert_eq!(quotient.points(), [0]);
    let first = r.integer_function(0, None, &mut quiet()).unwrap();
    let optional = r.integer_function(2, None, &mut quiet()).unwrap();
    assert_eq!(
        quotient.project(&first, &mut quiet()).unwrap().values(),
        &[BigInt::from(0)]
    );
    assert_eq!(
        quotient.project(&optional, &mut quiet()).unwrap().values(),
        &[BigInt::from(1)]
    );
    assert_eq!(indicators(&r, 0), ["0", "0", "1", "1"]);
    assert_eq!(r.observed_point(), Some(1));
    assert_eq!(r.columns()[1].rows()[1].indicator, Some(1.into()));
    let membership = quotient.ideal_membership(&first, &mut quiet()).unwrap();
    quotient
        .recheck_membership(&inputs, &first, &membership, &mut quiet())
        .unwrap();
    quotient.recheck(&inputs, &mut quiet()).unwrap();
}

#[test]
fn a_nonfinite_field_keeps_its_original_position_and_type_without_a_total_function() {
    let inputs = input("law required integer(c:Part):c.integer=0;");
    let a = readings(&inputs, "root");
    let r = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "p"),
        &selected(&["integer"]),
        &mut quiet(),
    )
    .unwrap();
    assert!(
        matches!(r.state(),FiniteLawState::OutsideFinite {position,ty:Type::Z} if position.subject=="p" && position.field.as_deref()==Some("Pattern.Part.integer"))
    );
    assert!(!r.domain_complete());
    assert!(!r.is_complete());
    assert!(r.integer_ring(&mut quiet()).is_err());
    assert!(r.required_quotient(&mut quiet()).is_err());
    r.recheck(&inputs, &mut quiet()).unwrap();
}

#[test]
fn finite_body_membership_is_exhausted_without_turning_missing_observation_into_zero() {
    let inputs=fixture::with_body(&fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,""),ALL);
    let a = readings(&inputs, "root");
    let r = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "root"),
        &selected(&["all"]),
        &mut quiet(),
    )
    .unwrap();
    assert!(r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(r.domain().len(), 8);
    assert_eq!(r.observed_point(), None);
    assert_eq!(indicators(&r, 0), ["0", "0", "0", "1", "1", "1", "1", "1"]);
    assert_eq!(r.required_zero(), Some([0, 1, 2].as_slice()));
    assert!(
        r.reference_domain_conditions()
            .iter()
            .any(|f| f.subject == "q" && f.field.as_deref() == Some("Pattern.Part.owner"))
    );
    for row in r.columns()[0].rows() {
        assert!(row.scope.assignments);
        assert!(row.support.iter().any(|f| f.subject == "q"
            && f.field.as_deref() == Some("Pattern.Part.owner")
            && f.atom.is_none()));
    }
    assert_eq!(r.integer_ring(&mut quiet()).unwrap().dimension(), 8);
    assert!(r.required_quotient(&mut quiet()).is_ok());
    r.recheck(&inputs, &mut quiet()).unwrap();
}

#[test]
fn stopping_before_domain_completion_retains_the_object_but_never_constructs_its_ring() {
    use crate::result::Signal;
    let inputs = input(ALL);
    let a = readings(&inputs, "root");
    let p = index(&a, "p");
    let mut c = Control::new(Limits::default(), |point| Usage {
        signal: (point == Checkpoint::FiniteLawDomain).then_some(Signal::Int),
        ..Usage::default()
    });
    let err = finite_object_law_family_valuations(&inputs, &a, p, &selected(&["all"]), &mut c)
        .err()
        .unwrap();
    assert!(matches!(err.cause, ValidationFailure::Stop(_)));
    let r = err.partial.unwrap();
    assert_eq!(r.object_identity(), Some(a.objects()[p].identity()));
    assert!(!r.domain_complete());
    assert!(r.integer_ring(&mut quiet()).is_err());
    assert!(r.required_quotient(&mut quiet()).is_err());
}

#[test]
fn a_known_empty_reference_domain_has_the_one_assignment_and_zero_indicator() {
    let inputs = fixture::with_body(fixture::MAP, ALL);
    let empty = readings(&inputs, "r2");
    let r = finite_object_law_family_valuations(
        &inputs,
        &empty,
        index(&empty, "r2"),
        &selected(&["all"]),
        &mut quiet(),
    )
    .unwrap();
    assert!(r.is_complete());
    assert!(r.positions().is_empty());
    assert_eq!(r.domain(), &[Vec::<Scalar>::new()]);
    assert_eq!(indicators(&r, 0), ["0"]);
    assert_eq!(r.observed_point(), Some(0));
    assert!(r.reference_domain_conditions().is_empty());
    r.recheck(&inputs, &mut quiet()).unwrap();
}

#[test]
fn a_conditionally_owned_object_keeps_its_owner_position_without_an_unconditional_ring() {
    let inputs=fixture::with_body(&fixture::MAP.replace(r#"{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#,""),"law required constant(c:Part):true;");
    let a = readings(&inputs, "root");
    let p = index(&a, "p");
    let r =
        finite_object_law_family_valuations(&inputs, &a, p, &selected(&["constant"]), &mut quiet())
            .unwrap();
    assert!(matches!(r.state(), FiniteLawState::Undetermined { .. }));
    assert!(!r.domain_complete());
    assert!(
        r.reference_domain_conditions()
            .iter()
            .any(|f| f.subject == "p" && f.field.as_deref() == Some("Pattern.Part.owner"))
    );
    assert!(r.integer_ring(&mut quiet()).is_err());
    assert!(r.integer_function(0, None, &mut quiet()).is_err());
    assert!(r.required_quotient(&mut quiet()).is_err());
    r.recheck_on_object(&inputs, &a, p, &mut quiet()).unwrap();
    let bad = vec![(
        "Selected.constant".into(),
        vec![("missing".into(), reference("p"))],
    )];
    assert!(finite_object_law_family_valuations(&inputs, &a, p, &bad, &mut quiet()).is_err());
}

#[test]
fn tuple_components_keep_their_original_types_and_separate_integer_indicators() {
    let inputs = input("law required pair(c:Part):c.pair=(0,true);");
    let a = readings(&inputs, "root");
    let r = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "p"),
        &selected(&["pair"]),
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.domain().len(), 4);
    assert_eq!(indicators(&r, 0), ["1", "0", "1", "1"]);
    assert_eq!(r.required_zero(), Some([1].as_slice()));
    assert_eq!(r.observed_point(), Some(1));
    for (path, expected) in [(vec![0], vec![0, 0, 1, 1]), (vec![1], vec![1, 0, 1, 0])] {
        let value = r.integer_function(0, Some(&path), &mut quiet()).unwrap();
        assert_eq!(
            value.values(),
            expected.into_iter().map(BigInt::from).collect::<Vec<_>>()
        );
    }
    assert_eq!(
        r.columns()[0].rows()[0].operands.as_ref().unwrap().0,
        Type::Tuple(vec![Type::Fp("2".into()), Type::Bool])
    );
    r.recheck(&inputs, &mut quiet()).unwrap();
}

#[test]
fn foreign_reading_and_out_of_range_object_selection_are_rejected() {
    let original = input("law required constant(c:Part):true;");
    let digest = &original.definitions().vocabularies["Pattern"].digest;
    let law = format!(
        "{}reading Foreign{{use vocabulary Pattern version \"1\" digest \"{digest}\";law required constant(c:Part):true;}}",
        String::from_utf8(original.sources().law().bytes().to_vec()).unwrap()
    );
    let sources = InputSources::from_bytes(
        original
            .sources()
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        original.sources().archmap().bytes().to_vec(),
    );
    let inputs = crate::input::check_inputs(sources, &mut quiet()).unwrap();
    let a = readings(&inputs, "root");
    let choices = vec![(
        "Foreign.constant".into(),
        vec![("c".into(), reference("p"))],
    )];
    let err =
        finite_object_law_family_valuations(&inputs, &a, index(&a, "p"), &choices, &mut quiet())
            .err()
            .unwrap();
    assert!(
        matches!(err.cause,ValidationFailure::Internal(message) if message.contains("reading"))
    );
    assert!(
        finite_object_law_family_valuations(
            &inputs,
            &a,
            usize::MAX,
            &selected(&["constant"]),
            &mut quiet()
        )
        .is_err()
    );
}

#[test]
fn unread_membership_missing_does_not_block_a_constant_law_on_a_known_root() {
    let inputs=fixture::with_body(&fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,""),"law required constant(c:Part):true;");
    let a = readings(&inputs, "root");
    let r = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "root"),
        &selected(&["constant"]),
        &mut quiet(),
    )
    .unwrap();
    assert!(!r.reference_domain_conditions().is_empty());
    assert!(r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(indicators(&r, 0), ["0"]);
    assert!(
        r.columns()[0]
            .rows()
            .iter()
            .all(|row| !row.scope.completions)
    );
    r.recheck(&inputs, &mut quiet()).unwrap();
}

fn owner_choice(owner: &str) -> Vec<(String, Vec<(String, Scalar)>)> {
    vec![(
        "Selected.external".into(),
        vec![
            ("c".into(), reference("p")),
            (
                "ext".into(),
                Scalar::Subject {
                    snapshot: "v".into(),
                    subject: owner.into(),
                    entity: "Pattern.Root".into(),
                },
            ),
        ],
    )]
}
fn observed_indicator(r: &FiniteLawFamilyValuations) -> String {
    indicators(r, 0)[r.observed_point().unwrap()].clone()
}
#[test]
fn explicit_external_owner_quantification_keeps_its_family() {
    let inputs = input("law required external(c:Part,ext:Root):forall x:Part[ext] . x.quantity=0;");
    let a = readings(&inputs, "root");
    let choice = owner_choice("r2");
    let original = inputs.sources().clone();
    let global = finite_law_family_valuations(&inputs, &choice, &mut quiet()).unwrap();
    let local =
        finite_object_law_family_valuations(&inputs, &a, index(&a, "p"), &choice, &mut quiet())
            .unwrap();
    // owner位置も原始候補の軸。観測したr.owner=r2とr.quantity=1で原式は偽。
    assert_eq!(observed_indicator(&global), "1");
    assert_eq!(observed_indicator(&local), "1");
    assert!(
        local
            .positions()
            .iter()
            .any(|p| p.subject == "r" && p.field.as_deref() == Some("Pattern.Part.quantity"))
    );
    assert_eq!(local.positions(), global.positions());
    assert_eq!(local.domain(), global.domain());
    assert_eq!(indicators(&local, 0), indicators(&global, 0));
    assert_eq!(local.columns()[0].bindings(), choice[0].1);
    local
        .recheck_on_object(&inputs, &a, index(&a, "p"), &mut quiet())
        .unwrap();
    assert_eq!(inputs.sources(), &original);
}
#[test]
fn explicit_same_root_owner_quantification_remains_local() {
    let inputs = input("law required external(c:Part,ext:Root):forall x:Part[ext] . x.quantity=0;");
    let a = readings(&inputs, "root");
    let choice = owner_choice("root");
    let global = finite_law_family_valuations(&inputs, &choice, &mut quiet()).unwrap();
    let local =
        finite_object_law_family_valuations(&inputs, &a, index(&a, "p"), &choice, &mut quiet())
            .unwrap();
    // root族のq.quantity=1でglobalは偽、部分対象pではp.quantity=0で真。
    assert_eq!(observed_indicator(&global), "1");
    assert_eq!(observed_indicator(&local), "0");
    assert!(
        local
            .positions()
            .iter()
            .any(|p| p.subject == "p" && p.field.as_deref() == Some("Pattern.Part.quantity"))
    );
    assert!(
        !local
            .positions()
            .iter()
            .any(|p| p.subject == "q" && p.field.as_deref() == Some("Pattern.Part.quantity"))
    );
    assert!(
        !local
            .positions()
            .iter()
            .any(|p| p.subject == "r" && p.field.as_deref() == Some("Pattern.Part.quantity"))
    );
    local
        .recheck_on_object(&inputs, &a, index(&a, "p"), &mut quiet())
        .unwrap();
}

#[test]
fn missing_external_owner_keeps_finite_candidates_without_an_observed_point() {
    let body = "law required external(c:Part,ext:Root):forall x:Part[ext] . x.quantity=0;";
    let missing = fixture::MAP.replace(r#""subjects":["#, r#""subjects":[{"id":"r","type":"Pattern.Part","origin":"model"},"#)
        .replace(r#""atoms":["#, r#""atoms":[{"id":"xr","subject":"r","field":"Pattern.Part.quantity","value":"1","origin":"model"},"#);
    let inputs = fixture::with_body(&missing, body);
    let a = readings(&inputs, "root");
    let local = finite_object_law_family_valuations(
        &inputs,
        &a,
        index(&a, "p"),
        &owner_choice("r2"),
        &mut quiet(),
    )
    .unwrap();
    let global = finite_law_family_valuations(&inputs, &owner_choice("r2"), &mut quiet()).unwrap();
    // 三subjectのowner二候補とquantity二候補で64点。未観測ownerは観測点へ埋めない。
    assert!(local.is_complete());
    assert!(local.domain_complete());
    assert_eq!(local.domain().len(), 64);
    assert_eq!(local.observed_point(), None);
    assert!(
        local
            .positions()
            .iter()
            .any(|p| p.subject == "r" && p.field.as_deref() == Some("Pattern.Part.owner"))
    );
    assert!(
        local
            .positions()
            .iter()
            .any(|p| p.subject == "r" && p.field.as_deref() == Some("Pattern.Part.quantity"))
    );
    assert_eq!(local.positions(), global.positions());
    assert_eq!(local.domain(), global.domain());
    assert_eq!(indicators(&local, 0), indicators(&global, 0));
    local
        .recheck_on_object(&inputs, &a, index(&a, "p"), &mut quiet())
        .unwrap();
}
