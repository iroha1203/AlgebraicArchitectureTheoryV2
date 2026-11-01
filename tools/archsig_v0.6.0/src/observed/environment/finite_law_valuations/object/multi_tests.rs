use super::*;
use crate::construction::{construct, readings::object_reading_instances};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/primitive_valuation_data.rs");
}
use crate::control::quiet;
fn input(body: &str) -> Arc<CheckedInputs> {
    let map = fixture::MAP.replace(r#""subjects":["#, r#""subjects":[{"id":"r","type":"Pattern.Part","origin":"model"},"#)
        .replace(r#""atoms":["#, r#""atoms":[{"id":"or","subject":"r","field":"Pattern.Part.owner","value":["v","r2"],"origin":"model"},{"id":"xr","subject":"r","field":"Pattern.Part.quantity","value":"1","origin":"model"},"#);
    fixture::with_body(&map, body)
}
fn readings(i: &CheckedInputs, root: &str) -> ObjectReadingInstances {
    let c = construct(i, "Selected", "v", root, &mut quiet()).unwrap();
    object_reading_instances(i, &c, &mut quiet()).unwrap()
}
fn index(r: &ObjectReadingInstances, name: &str) -> usize {
    r.objects()
        .iter()
        .position(|o| o.identity().subject().subject == name)
        .unwrap()
}
fn reference(name: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: name.into(),
        entity: if ["root", "r2"].contains(&name) {
            "Pattern.Root"
        } else {
            "Pattern.Part"
        }
        .into(),
    }
}
fn choices(
    r: &ObjectReadingInstances,
    pairs: &[(&str, &str, &str)],
) -> Vec<(usize, String, Vec<(String, Scalar)>)> {
    pairs
        .iter()
        .map(|(object, law, binding)| {
            (
                index(r, object),
                format!("Selected.{law}"),
                vec![("c".into(), reference(binding))],
            )
        })
        .collect()
}
fn indicators(r: &FiniteLawFamilyValuations, column: usize) -> Vec<i32> {
    r.integer_function(column, None, &mut quiet())
        .unwrap()
        .values()
        .iter()
        .map(|v| v.to_string().parse().unwrap())
        .collect()
}
const ALL: &str = "law required all(c:Part):forall x:Part . x.quantity=0;law optional external(c:Part,ext:Part):ext.quantity=0;";

#[test]
fn multiple_objects_share_positions_coordinates_and_one_integer_ring() {
    let i = input(ALL);
    let a = readings(&i, "root");
    let mut selected = choices(
        &a,
        &[("root", "all", "p"), ("p", "all", "p"), ("q", "all", "q")],
    );
    for object in ["p", "q"] {
        selected.push((
            index(&a, object),
            "Selected.external".into(),
            vec![
                ("c".into(), reference(object)),
                ("ext".into(), reference("r")),
            ],
        ));
    }
    let r = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
    assert_eq!(
        r.positions()
            .iter()
            .map(|p| (p.subject.as_str(), p.field.as_deref()))
            .collect::<Vec<_>>(),
        [
            ("p", Some("Pattern.Part.quantity")),
            ("q", Some("Pattern.Part.quantity")),
            ("r", Some("Pattern.Part.quantity"))
        ]
    );
    assert_eq!(r.domain().len(), 8);
    assert!(r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(indicators(&r, 0), [0, 0, 1, 1, 1, 1, 1, 1]);
    assert_eq!(indicators(&r, 1), [0, 0, 0, 0, 1, 1, 1, 1]);
    assert_eq!(indicators(&r, 2), [0, 0, 1, 1, 0, 0, 1, 1]);
    assert_eq!(indicators(&r, 3), [0, 1, 0, 1, 0, 1, 0, 1]);
    assert_eq!(indicators(&r, 4), indicators(&r, 3));
    assert_eq!(r.observed_point(), Some(3));
    assert_eq!(r.required_zero(), Some([0, 1].as_slice()));
    for (n, (object, law, bindings)) in selected.iter().enumerate() {
        assert_eq!(
            r.column_object_identity(n),
            Some(a.objects()[*object].identity())
        );
        assert_eq!(r.columns()[n].declaration().name, *law);
        assert_eq!(r.columns()[n].bindings(), bindings);
        assert_eq!(
            r.columns()[n]
                .rows()
                .iter()
                .map(|row| row.point)
                .collect::<Vec<_>>(),
            (0..8).collect::<Vec<_>>()
        );
    }
    assert_eq!(r.column_object_identity(5), None);
    let ring = r.integer_ring(&mut quiet()).unwrap();
    let sum = ring
        .add(
            &r.integer_function(1, None, &mut quiet()).unwrap(),
            &r.integer_function(3, None, &mut quiet()).unwrap(),
            &mut quiet(),
        )
        .unwrap();
    assert_eq!(
        sum.values()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["0", "1", "0", "1", "1", "2", "1", "2"]
    );
    let quotient = r.required_quotient(&mut quiet()).unwrap();
    assert_eq!(quotient.points(), [0, 1]);
    for g in r.required_generators(&mut quiet()).unwrap() {
        assert!(
            quotient
                .integer_ring(&mut quiet())
                .unwrap()
                .is_zero(
                    &quotient.project(g.value(), &mut quiet()).unwrap(),
                    &mut quiet()
                )
                .unwrap()
        );
    }
    r.recheck_on_objects(
        &i,
        &a,
        &selected.iter().map(|s| s.0).collect::<Vec<_>>(),
        &mut quiet(),
    )
    .unwrap();
}
#[test]
fn a_single_column_matches_the_existing_object_entry_without_reusing_its_ring_owner() {
    let i = input(ALL);
    let a = readings(&i, "root");
    for object in ["root", "p", "q"] {
        let selected = choices(
            &a,
            &[(object, "all", if object == "root" { "p" } else { object })],
        );
        let multi =
            finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
        let legacy = finite_object_law_family_valuations(
            &i,
            &a,
            selected[0].0,
            &[(selected[0].1.clone(), selected[0].2.clone())],
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(multi.positions(), legacy.positions());
        assert_eq!(multi.types(), legacy.types());
        assert_eq!(multi.domain(), legacy.domain());
        assert_eq!(multi.observed_point(), legacy.observed_point());
        assert_eq!(indicators(&multi, 0), indicators(&legacy, 0));
        assert_eq!(multi.required_zero(), legacy.required_zero());
        assert!(
            multi
                .integer_ring(&mut quiet())
                .unwrap()
                .member(
                    &legacy.integer_function(0, None, &mut quiet()).unwrap(),
                    &mut quiet()
                )
                .is_err()
        );
        assert!(
            multi
                .recheck_on_object(&i, &a, selected[0].0, &mut quiet())
                .is_err()
        );
    }
}
#[test]
fn constant_and_empty_families_preserve_one_assignment_and_the_empty_reading_anchor() {
    let i = input("law optional never(c:Part):false;");
    let a = readings(&i, "root");
    let foreign = readings(&i, "r2");
    let selected = choices(
        &a,
        &[
            ("p", "never", "p"),
            ("q", "never", "q"),
            ("p", "never", "p"),
        ],
    );
    let r = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
    assert_eq!(r.columns().len(), 3);
    assert!(r.positions().is_empty());
    assert_eq!(r.domain(), [Vec::<Scalar>::new()]);
    assert_eq!(r.required_zero(), Some([0].as_slice()));
    assert_eq!(indicators(&r, 0), [1]);
    assert_eq!(indicators(&r, 1), [1]);
    assert_eq!(indicators(&r, 2), [1]);
    assert!(r.required_generators(&mut quiet()).unwrap().is_empty());
    assert_ne!(r.column_object_identity(0), r.column_object_identity(1));
    assert_eq!(r.column_object_identity(0), r.column_object_identity(2));
    let empty = finite_multi_object_law_family_valuations(&i, &a, &[], &mut quiet()).unwrap();
    assert!(empty.is_complete());
    assert_eq!(empty.domain(), [Vec::<Scalar>::new()]);
    assert_eq!(empty.observed_point(), Some(0));
    assert_eq!(empty.required_zero(), Some([0].as_slice()));
    assert_eq!(empty.integer_ring(&mut quiet()).unwrap().dimension(), 1);
    empty.recheck_on_objects(&i, &a, &[], &mut quiet()).unwrap();
    assert!(
        empty
            .recheck_on_objects(&i, &foreign, &[], &mut quiet())
            .is_err()
    );
    let global = finite_law_family_valuations(&i, &[], &mut quiet()).unwrap();
    assert!(
        global
            .recheck_on_objects(&i, &a, &[], &mut quiet())
            .is_err()
    );
}
#[test]
fn missing_observed_value_has_candidates_but_no_observed_shared_point() {
    let map=fixture::MAP.replace(r#",{"id":"xp","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required zero(c:Part):c.quantity=0;");
    let a = readings(&i, "root");
    let selected = choices(&a, &[("p", "zero", "p"), ("q", "zero", "q")]);
    let r = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
    assert_eq!(r.domain().len(), 4);
    assert_eq!(r.observed_point(), None);
    assert_eq!(indicators(&r, 0), [0, 0, 1, 1]);
    assert_eq!(indicators(&r, 1), [0, 1, 0, 1]);
    assert_eq!(r.required_zero(), Some([0].as_slice()));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn nonfinite_position_is_not_a_completed_shared_ring() {
    let i = input(
        "law required finite(c:Part):c.quantity=0;law required infinite(c:Part):c.integer=0;",
    );
    let a = readings(&i, "root");
    let selected = choices(&a, &[("p", "finite", "p"), ("q", "infinite", "q")]);
    let r = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
    assert!(
        matches!(r.state(),FiniteLawState::OutsideFinite{position,ty:Type::Z} if position.subject=="q")
    );
    assert!(!r.domain_complete());
    assert!(r.columns().iter().all(|c| c.rows().is_empty()));
    assert!(r.integer_ring(&mut quiet()).is_err());
    assert!(r.required_quotient(&mut quiet()).is_err());
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn body_membership_is_exhausted_while_unresolved_partial_objects_keep_their_conditions() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(&map, ALL);
    let a = readings(&i, "root");
    for pairs in [
        vec![("p", "all", "p"), ("root", "all", "p")],
        vec![("p", "all", "p"), ("q", "all", "q")],
    ] {
        let selected = choices(&a, &pairs);
        let r = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
        assert!(
            r.column_reference_domain_conditions(1)
                .unwrap()
                .iter()
                .any(|f| f.subject == "q" && f.field.as_deref() == Some("Pattern.Part.owner"))
        );
        if pairs[1].0 == "root" {
            assert!(r.is_complete());
            assert!(r.domain_complete());
            assert_eq!(r.domain().len(), 8);
            assert_eq!(r.observed_point(), None);
            assert_eq!(indicators(&r, 0), [0, 0, 0, 0, 1, 1, 1, 1]);
            assert_eq!(indicators(&r, 1), [0, 0, 0, 1, 1, 1, 1, 1]);
            assert_eq!(r.required_zero(), Some([0, 1, 2].as_slice()));
            assert_eq!(r.integer_ring(&mut quiet()).unwrap().dimension(), 8);
            assert!(r.required_quotient(&mut quiet()).is_ok());
        } else {
            assert!(matches!(r.state(), FiniteLawState::Undetermined { .. }));
            assert!(!r.domain_complete());
            assert!(r.integer_ring(&mut quiet()).is_err());
            assert!(r.integer_function(0, None, &mut quiet()).is_err());
            assert!(r.required_quotient(&mut quiet()).is_err());
        }
        r.recheck_on_objects(
            &i,
            &a,
            &selected.iter().map(|s| s.0).collect::<Vec<_>>(),
            &mut quiet(),
        )
        .unwrap();
    }
}
#[test]
fn incompatible_fixed_typed_bindings_keep_an_empty_admissible_domain() {
    let i = input("law required typed(r:Root,c:Part[r]):true;");
    let a = readings(&i, "root");
    let selected = vec![
        (
            index(&a, "p"),
            "Selected.typed".into(),
            vec![
                ("r".into(), reference("root")),
                ("c".into(), reference("p")),
            ],
        ),
        (
            index(&a, "q"),
            "Selected.typed".into(),
            vec![("r".into(), reference("r2")), ("c".into(), reference("p"))],
        ),
    ];
    let r = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(r.positions().len(), 1);
    assert_eq!(
        r.positions()[0].field.as_deref(),
        Some("Pattern.Part.owner")
    );
    assert!(r.domain().is_empty());
    assert_eq!(r.observed_point(), None);
    assert_eq!(r.required_zero(), Some([].as_slice()));
    assert_eq!(r.integer_ring(&mut quiet()).unwrap().dimension(), 0);
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn changed_readings_objects_columns_and_coordinates_are_rejected() {
    let i = input("law required zero(c:Part):c.quantity=0;");
    let a = readings(&i, "root");
    let foreign = readings(&i, "r2");
    let selected = choices(&a, &[("p", "zero", "p"), ("q", "zero", "q")]);
    let expected = selected.iter().map(|s| s.0).collect::<Vec<_>>();
    for mode in 0..9 {
        let mut r =
            finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
        match mode {
            0 => r.column_objects.as_mut().unwrap().columns.swap(0, 1),
            1 => {
                r.column_objects.as_mut().unwrap().columns.pop();
            }
            2 => r.column_objects.as_mut().unwrap().readings = foreign.clone(),
            3 => r.columns.swap(0, 1),
            4 => r.domain.reverse(),
            5 => r.columns[0].rows[0].indicator = Some(1.into()),
            6 => r.columns[0].rows[0].point = usize::MAX,
            7 => r.required_zero = Some(vec![1]),
            _ => r.columns[0].rows[0].support.clear(),
        }
        assert!(
            r.recheck_on_objects(&i, &a, &expected, &mut quiet())
                .is_err(),
            "mode={mode}"
        );
    }
    let r = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
    assert!(
        r.recheck_on_objects(&i, &foreign, &expected, &mut quiet())
            .is_err()
    );
    assert!(
        r.recheck_on_objects(&i, &a, &[expected[1], expected[0]], &mut quiet())
            .is_err()
    );
    let map = String::from_utf8(i.sources().archmap().bytes().to_vec())
        .unwrap()
        .replace("内部候補試験。", "別の由来。");
    let changed = fixture::with_body(&map, "law required zero(c:Part):c.quantity=0;");
    assert!(r.recheck(&changed, &mut quiet()).is_err());
}
#[test]
fn invalid_selections_and_binding_shapes_fail_before_any_shared_domain() {
    let i = input("law required zero(c:Part):c.quantity=0;view helper(c:Part):Fp(2)=c.quantity;");
    let a = readings(&i, "root");
    for selected in [
        vec![(
            usize::MAX,
            "Selected.zero".into(),
            vec![("c".into(), reference("p"))],
        )],
        vec![(
            index(&a, "p"),
            "Selected.absent".into(),
            vec![("c".into(), reference("p"))],
        )],
        vec![(
            index(&a, "p"),
            "Selected.helper".into(),
            vec![("c".into(), reference("p"))],
        )],
        vec![(index(&a, "p"), "Selected.zero".into(), vec![])],
        vec![(
            index(&a, "p"),
            "Selected.zero".into(),
            vec![("c".into(), reference("p")), ("c".into(), reference("q"))],
        )],
    ] {
        assert!(
            finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).is_err()
        );
    }
}
#[test]
fn fixed_stops_keep_finished_shared_rows_and_each_column_object() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = input("law required zero(c:Part):c.quantity=0;");
    let a = readings(&i, "root");
    let selected = choices(&a, &[("p", "zero", "p"), ("q", "zero", "q")]);
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let mut c = Control::new(move |point| {
        if point == Checkpoint::FiniteLawEvaluation {
            count.set(count.get() + 1);
        }
        (count.get() >= 3).then_some(Signal::Term)
    });
    let failure = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut c)
        .err()
        .unwrap();
    assert!(matches!(failure.cause, ValidationFailure::Stop(_)));
    let r = failure.partial.unwrap();
    assert!(r.domain_complete());
    assert!(!r.is_complete());
    assert_eq!(r.columns()[0].rows().len(), 1);
    assert!(r.columns()[1].rows().is_empty());
    assert_eq!(
        r.column_object_identity(0),
        Some(a.objects()[selected[0].0].identity())
    );
    assert_eq!(
        r.column_object_identity(1),
        Some(a.objects()[selected[1].0].identity())
    );
    assert!(r.integer_function(0, None, &mut quiet()).is_err());
    assert!(r.required_quotient(&mut quiet()).is_err());
}
#[test]
fn interruption_before_domain_completion_preserves_column_origins_without_a_ring() {
    use crate::result::Signal;
    let i = input(ALL);
    let a = readings(&i, "root");
    let selected = choices(&a, &[("p", "all", "p"), ("q", "all", "q")]);
    let mut c = Control::new(|point| (point == Checkpoint::FiniteLawDomain).then_some(Signal::Int));
    let failure = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut c)
        .err()
        .unwrap();
    assert!(matches!(failure.cause, ValidationFailure::Stop(_)));
    let r = failure.partial.unwrap();
    assert!(!r.domain_complete());
    assert!(r.integer_ring(&mut quiet()).is_err());
    for (n, (object, _, _)) in selected.iter().enumerate() {
        assert_eq!(
            r.column_object_identity(n),
            Some(a.objects()[*object].identity())
        );
    }
}

#[test]
fn column_order_preserves_the_shared_domain_and_reorders_only_the_original_columns() {
    let i = input(ALL);
    let a = readings(&i, "root");
    let selected = choices(
        &a,
        &[("root", "all", "p"), ("p", "all", "p"), ("q", "all", "q")],
    );
    let forward =
        finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
    let reversed = selected.iter().cloned().rev().collect::<Vec<_>>();
    let back = finite_multi_object_law_family_valuations(&i, &a, &reversed, &mut quiet()).unwrap();
    assert_eq!(forward.positions(), back.positions());
    assert_eq!(forward.types(), back.types());
    assert_eq!(forward.domain(), back.domain());
    assert_eq!(forward.required_zero(), back.required_zero());
    for column in 0..3 {
        assert_eq!(indicators(&forward, column), indicators(&back, 2 - column));
        assert_eq!(
            forward.column_object_identity(column),
            back.column_object_identity(2 - column)
        );
    }
    assert_eq!(forward.positions().len(), 2);
    assert_eq!(forward.domain().len(), 4);
    assert_eq!(indicators(&forward, 0), [0, 1, 1, 1]);
    assert_eq!(indicators(&forward, 1), [0, 0, 1, 1]);
    assert_eq!(indicators(&forward, 2), [0, 1, 0, 1]);
    back.recheck_on_objects(
        &i,
        &a,
        &reversed.iter().map(|s| s.0).collect::<Vec<_>>(),
        &mut quiet(),
    )
    .unwrap();
}
#[test]
fn typed_tuple_components_share_coordinates_and_keep_separate_required_generators() {
    let i = input("law required pair(c:Part):c.pair=(0,true);");
    let a = readings(&i, "root");
    let selected = choices(&a, &[("p", "pair", "p"), ("q", "pair", "q")]);
    let r = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
    assert_eq!(
        r.positions()
            .iter()
            .map(|f| f.subject.as_str())
            .collect::<Vec<_>>(),
        ["p", "q"]
    );
    assert_eq!(r.domain().len(), 16);
    assert_eq!(r.required_zero(), Some([5].as_slice()));
    assert_eq!(r.observed_point(), None);
    for column in 0..2 {
        let whole = r.integer_function(column, None, &mut quiet()).unwrap();
        let fp = r
            .integer_function(column, Some(&[0]), &mut quiet())
            .unwrap();
        let boolean = r
            .integer_function(column, Some(&[1]), &mut quiet())
            .unwrap();
        for point in 0..16 {
            let value = if column == 0 { point / 4 } else { point % 4 };
            assert_eq!(
                whole.values()[point].to_string(),
                if value == 1 { "0" } else { "1" }
            );
            assert_eq!(
                fp.values()[point].to_string(),
                if value < 2 { "0" } else { "1" }
            );
            assert_eq!(
                boolean.values()[point].to_string(),
                if value % 2 == 1 { "0" } else { "1" }
            );
            let components = r.columns()[column].rows()[point]
                .components
                .as_ref()
                .unwrap();
            assert_eq!(components[0].ty, Type::Fp("2".into()));
            assert_eq!(components[1].ty, Type::Bool);
        }
    }
    let generators = r.required_generators(&mut quiet()).unwrap();
    assert_eq!(generators.len(), 4);
    assert_eq!(
        generators
            .iter()
            .map(|g| (g.column(), g.component().unwrap().to_vec()))
            .collect::<Vec<_>>(),
        [(0, vec![0]), (0, vec![1]), (1, vec![0]), (1, vec![1])]
    );
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn the_same_name_and_shape_from_a_foreign_reading_are_rejected() {
    let original = input("law required zero(c:Part):c.quantity=0;");
    let sources = original.sources();
    let digest = &original.definitions().vocabularies["Pattern"].digest;
    let mut law = String::from_utf8(sources.law().bytes().to_vec()).unwrap();
    law.push_str(&format!("reading Other{{use vocabulary Pattern version \"1\" digest \"{digest}\";law required zero(c:Part):c.quantity=0;}}"));
    let i = Arc::new(
        crate::input::check_inputs(
            crate::input::InputSources::from_bytes(
                sources
                    .definitions()
                    .iter()
                    .map(|d| d.bytes().to_vec())
                    .collect(),
                law.into_bytes(),
                sources.archmap().bytes().to_vec(),
            ),
            &mut quiet(),
        )
        .unwrap(),
    );
    let a = readings(&i, "root");
    let selected = vec![(
        index(&a, "p"),
        "Other.zero".into(),
        vec![("c".into(), reference("p"))],
    )];
    let failure = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet())
        .err()
        .unwrap();
    assert!(matches!(failure.cause, ValidationFailure::Internal(_)));
    assert!(failure.partial.is_none());
}

#[test]
fn all_generated_finite_parameter_rows_of_several_objects_feed_the_same_family() {
    use super::instances::{ParameterFamilyState, finite_object_law_instances};
    let i = input("law required grid(c:Part,n:Fp(2),b:Bool):c.quantity=n;");
    let a = readings(&i, "root");
    let mut selected = vec![];
    for object in ["root", "p", "q"] {
        let parameters =
            finite_object_law_instances(&i, &a, index(&a, object), &mut quiet()).unwrap();
        assert!(parameters.is_complete());
        for entry in parameters.entries() {
            if entry.state == ParameterFamilyState::NotApplicable {
                assert!(entry.rows.is_empty());
                continue;
            }
            assert_eq!(entry.state, ParameterFamilyState::Ready);
            for row in &entry.rows {
                selected.push((
                    index(&a, object),
                    entry.source.declaration().name.clone(),
                    row.bindings.clone(),
                ));
            }
        }
    }
    assert_eq!(selected.len(), 16);
    let r = finite_multi_object_law_family_valuations(&i, &a, &selected, &mut quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(
        r.positions()
            .iter()
            .map(|p| p.subject.as_str())
            .collect::<Vec<_>>(),
        ["p", "q"]
    );
    assert_eq!(r.domain().len(), 4);
    assert_eq!(r.columns().len(), 16);
    assert_eq!(r.required_zero(), Some([].as_slice()));
    for (column, (_, _, bindings)) in selected.iter().enumerate() {
        assert_eq!(r.columns()[column].bindings(), bindings);
        let subject = bindings.iter().find(|(n, _)| n == "c").unwrap();
        let n = bindings.iter().find(|(name, _)| name == "n").unwrap();
        let Scalar::Subject { subject, .. } = &subject.1 else {
            panic!("reference")
        };
        let Scalar::Fp { value, .. } = &n.1 else {
            panic!("finite scalar")
        };
        for point in 0..4 {
            let actual = if subject == "p" { point / 2 } else { point % 2 };
            assert_eq!(
                r.integer_function(column, None, &mut quiet())
                    .unwrap()
                    .values()[point]
                    .to_string(),
                if value.to_string() == actual.to_string() {
                    "0"
                } else {
                    "1"
                }
            );
        }
    }
    r.recheck_on_objects(
        &i,
        &a,
        &selected.iter().map(|s| s.0).collect::<Vec<_>>(),
        &mut quiet(),
    )
    .unwrap();
}
