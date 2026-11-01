use crate::common::object_view_compatibility_data as fixture;
use crate::common::quiet;
use archsig_common::{control::Control, types::Type};
use archsig_computation::{
    construction::ConstructionFailure,
    observed::{
        object_equation_presentation::EquationPresentationStatus as S,
        object_polynomial_observable::{
            ObjectPolynomialObservable as O, PolynomialObservableFailure as F,
            PolynomialObservableReading as R, PolynomialObservableValue as V,
            object_polynomial_observable,
        },
    },
};
use archsig_input::input::{CheckedInputs, InputSources, check_inputs};
use std::sync::Arc;
fn inputs_with(body: &str, map: &str) -> Arc<CheckedInputs> {
    let d = archsig_input::definition::check_definitions(&[("definition0", fixture::D.as_bytes())])
        .unwrap();
    let digest = &d.vocabularies()["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";{body}}}"
    );
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![fixture::D.as_bytes().to_vec()],
                law.into_bytes(),
                map.replace("@DIGEST@", digest).into_bytes(),
            ),
            &quiet(),
        )
        .unwrap(),
    )
}
fn inputs(body: &str) -> Arc<CheckedInputs> {
    inputs_with(body, fixture::A)
}
fn run(i: Arc<CheckedInputs>) -> O {
    object_polynomial_observable(i, "Selected", "v", "root", 0, &quiet()).unwrap()
}
fn terms(v: &V, block: usize) -> Vec<(Vec<usize>, String)> {
    v.blocks()[block]
        .terms
        .iter()
        .map(|t| (t.variables.clone(), t.coefficient.wire().canonical()))
        .collect()
}
fn find(r: &O, name: &str) -> usize {
    r.coordinates()
        .iter()
        .position(|q| {
            r.base().base().base().readings().instances()[q.position.instance]
                .declaration()
                .name
                == format!("Selected.{name}")
        })
        .unwrap()
}
fn four_inputs() -> Arc<CheckedInputs> {
    inputs(
        "view half():Q=rat(1,2);view three():Fp(3)=1;view five():Fp(5)=1;law required zero(c:Part):c.quantity=0;law required one(c:Part):c.quantity=1;law optional stays(c:Part):c.quantity=2;law required rational(c:Part):half()=rat(1,3);law optional threeCase(c:Part):three()=2;law optional fiveCase(c:Part):five()=2;",
    )
}
#[test]
fn shared_factors_and_typed_product_coordinates_keep_original_equations_and_ideals() {
    let i = four_inputs();
    let r = run(i.clone());
    assert_eq!(r.status(), S::Ready);
    assert!(r.is_complete());
    assert_eq!(r.factors().len(), 4);
    assert_eq!(r.coordinates().len(), 6);
    let z = r.factors().iter().position(|f| f.ty == Type::Z).unwrap();
    let q = r.factors().iter().position(|f| f.ty == Type::Q).unwrap();
    let p3 = r
        .factors()
        .iter()
        .position(|f| f.ty == Type::Fp("3".into()))
        .unwrap();
    let p5 = r
        .factors()
        .iter()
        .position(|f| f.ty == Type::Fp("5".into()))
        .unwrap();
    let root = r.root_atom().unwrap();
    assert_eq!(
        &r.global_context()[root],
        r.base().base().base().readings().construction().root()
    );
    let zero = find(&r, "zero");
    let one = find(&r, "one");
    let stays = find(&r, "stays");
    assert_eq!(r.coordinates()[zero].factor, Some(z));
    assert_eq!(r.coordinates()[one].factor, Some(z));
    assert_eq!(r.coordinates()[stays].factor, Some(z));
    assert_eq!(r.factors()[z].symbols.len(), 1);
    let mut generators = r.factors()[z].required_generators.clone();
    generators.sort();
    let mut expected = vec![zero, one];
    expected.sort();
    assert_eq!(generators, expected);
    for (index, expected_nu, epsilon, holds) in [
        (zero, vec![(vec![0], "\"1\"".into())], "\"2\"", false),
        (
            one,
            vec![(vec![], "\"-1\"".into()), (vec![0], "\"1\"".into())],
            "\"1\"",
            false,
        ),
        (
            stays,
            vec![(vec![], "\"-2\"".into()), (vec![0], "\"1\"".into())],
            "\"0\"",
            true,
        ),
    ] {
        let nu = r.at(index, root, R::Nu, &quiet()).unwrap().unwrap();
        assert_eq!(terms(&nu, z), expected_nu);
        let residual = r.at(index, root, R::Residual, &quiet()).unwrap().unwrap();
        assert_eq!(
            terms(&residual, z),
            if holds {
                vec![]
            } else {
                vec![(vec![], epsilon.into())]
            }
        );
        assert_eq!(r.holds_at(index, root, &quiet()).unwrap(), Some(holds));
        assert_eq!(r.base().occurrences()[index].component_holds, Some(holds));
        for b in 0..4 {
            if b != z {
                assert!(terms(&nu, b).is_empty());
                assert!(terms(&residual, b).is_empty());
            }
        }
    }
    for (name, factor, coefficient) in [
        ("rational", q, "[\"1\",\"6\"]"),
        ("threeCase", p3, "\"2\""),
        ("fiveCase", p5, "\"4\""),
    ] {
        let index = find(&r, name);
        let value = r.at(index, root, R::Residual, &quiet()).unwrap().unwrap();
        assert_eq!(terms(&value, factor), [(vec![], coefficient.into())]);
        for b in 0..4 {
            if b != factor {
                assert!(terms(&value, b).is_empty());
            }
        }
    }
    let nu = r.at(stays, root, R::Nu, &quiet()).unwrap().unwrap();
    assert!(!r.is_zero(&nu, &quiet()).unwrap());
    assert_eq!(r.holds_at(stays, root, &quiet()).unwrap(), Some(true));
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn coordinate_placement_is_not_the_product_unit_and_arithmetic_is_componentwise() {
    let r = run(four_inputs());
    let root = r.root_atom().unwrap();
    let z = r.factors().iter().position(|f| f.ty == Type::Z).unwrap();
    let q = r.factors().iter().position(|f| f.ty == Type::Q).unwrap();
    let e = r
        .at(find(&r, "one"), root, R::Epsilon, &quiet())
        .unwrap()
        .unwrap();
    let f = r
        .at(find(&r, "rational"), root, R::Epsilon, &quiet())
        .unwrap()
        .unwrap();
    let zero = r.zero(&quiet()).unwrap();
    let unit = r.one(&quiet()).unwrap();
    assert!(!r.equal(&e, &unit, &quiet()).unwrap());
    assert_eq!(terms(&e, z), [(vec![], "\"1\"".into())]);
    assert!(terms(&e, q).is_empty());
    assert_eq!(terms(&unit, z), [(vec![], "\"1\"".into())]);
    assert_eq!(terms(&unit, q), [(vec![], "[\"1\",\"1\"]".into())]);
    let sum = r.add(&e, &f, &quiet()).unwrap();
    assert_eq!(terms(&sum, z), [(vec![], "\"1\"".into())]);
    assert_eq!(terms(&sum, q), [(vec![], "[\"1\",\"6\"]".into())]);
    assert!(
        r.is_zero(&r.mul(&e, &f, &quiet()).unwrap(), &quiet())
            .unwrap()
    );
    assert!(
        r.equal(&r.mul(&sum, &unit, &quiet()).unwrap(), &sum, &quiet())
            .unwrap()
    );
    assert!(
        r.equal(&r.sub(&sum, &f, &quiet()).unwrap(), &e, &quiet())
            .unwrap()
    );
    assert!(
        r.equal(&r.add(&sum, &zero, &quiet()).unwrap(), &sum, &quiet())
            .unwrap()
    );
    assert!(
        r.is_zero(&r.sub(&sum, &sum, &quiet()).unwrap(), &quiet())
            .unwrap()
    );
    let lhs = r
        .mul(&sum, &r.add(&e, &f, &quiet()).unwrap(), &quiet())
        .unwrap();
    let rhs = r
        .add(
            &r.mul(&sum, &e, &quiet()).unwrap(),
            &r.mul(&sum, &f, &quiet()).unwrap(),
            &quiet(),
        )
        .unwrap();
    assert!(r.equal(&lhs, &rhs, &quiet()).unwrap());
}
#[test]
fn all_other_atoms_are_zero_and_a_component_still_uses_the_base_root_atom() {
    let i = inputs("law required part(c:Part):c.quantity=0;");
    let r = object_polynomial_observable(i.clone(), "Selected", "v", "root", 1, &quiet()).unwrap();
    let root = r.root_atom().unwrap();
    assert_eq!(r.global_context()[root].subject, "root");
    assert_eq!(r.coordinates().len(), 1);
    assert!(
        !r.is_zero(
            &r.at(0, root, R::Residual, &quiet()).unwrap().unwrap(),
            &quiet()
        )
        .unwrap()
    );
    let mut found_part = false;
    for (atom, fact) in r.global_context().iter().enumerate() {
        if atom != root {
            found_part |= fact.subject == "p" && fact.field.is_none();
            for kind in [R::Nu, R::Epsilon, R::Residual] {
                let value = r.at(0, atom, kind, &quiet()).unwrap().unwrap();
                assert!(r.is_zero(&value, &quiet()).unwrap());
            }
            assert_eq!(r.holds_at(0, atom, &quiet()).unwrap(), Some(true));
        }
    }
    assert!(found_part);
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn empty_product_is_the_one_element_ring_without_fabricated_coordinates() {
    let i = inputs("");
    let r = run(i.clone());
    assert!(r.is_complete());
    assert_eq!(r.status(), S::Ready);
    assert!(r.factors().is_empty());
    assert!(r.coordinates().is_empty());
    assert!(r.root_atom().is_some());
    let zero = r.zero(&quiet()).unwrap();
    let one = r.one(&quiet()).unwrap();
    assert!(zero.blocks().is_empty());
    assert!(r.equal(&zero, &one, &quiet()).unwrap());
    assert!(
        r.equal(&r.mul(&one, &one, &quiet()).unwrap(), &zero, &quiet())
            .unwrap()
    );
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn a_missing_residual_is_unknown_at_root_and_zero_at_other_atoms() {
    let map = fixture::A
        .lines()
        .filter(|l| !l.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    let i = inputs_with("law required amount(c:Part):c.quantity=1;", &map);
    let r = run(i.clone());
    let root = r.root_atom().unwrap();
    assert_eq!(r.status(), S::Undetermined);
    assert!(r.at(0, root, R::Residual, &quiet()).unwrap().is_none());
    assert!(r.at(0, root, R::Epsilon, &quiet()).unwrap().is_none());
    assert_eq!(r.holds_at(0, root, &quiet()).unwrap(), None);
    let nu = r.at(0, root, R::Nu, &quiet()).unwrap().unwrap();
    assert_eq!(
        terms(&nu, 0),
        [(vec![], "\"-1\"".into()), (vec![0], "\"1\"".into())]
    );
    assert!(r.factors()[0].evaluation_images.is_none());
    for atom in 0..r.global_context().len() {
        if atom != root {
            assert!(
                r.is_zero(
                    &r.at(0, atom, R::Residual, &quiet()).unwrap().unwrap(),
                    &quiet()
                )
                .unwrap()
            );
        }
    }
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn invalid_indices_and_values_from_another_construction_are_rejected() {
    let i = four_inputs();
    let a = run(i.clone());
    let b = run(i);
    let zero = a.zero(&quiet()).unwrap();
    let foreign = b.zero(&quiet()).unwrap();
    for error in [
        a.add(&zero, &foreign, &quiet()).unwrap_err(),
        a.mul(&foreign, &zero, &quiet()).unwrap_err(),
        a.equal(&foreign, &zero, &quiet()).unwrap_err(),
        a.is_zero(&foreign, &quiet()).unwrap_err(),
        a.at(999, a.root_atom().unwrap(), R::Nu, &quiet())
            .unwrap_err(),
        a.at(0, 999, R::Residual, &quiet()).unwrap_err(),
    ] {
        assert!(matches!(error, ConstructionFailure::InvalidSelection(_)));
    }
}

#[test]
fn false_guard_has_zero_conditional_coordinate_without_changing_the_nonzero_raw_difference() {
    let i = inputs(
        "law required off(c:Part) when false:c.quantity=0;law required on(c:Part) when true:c.quantity=0;",
    );
    let r = run(i.clone());
    let root = r.root_atom().unwrap();
    let off = find(&r, "off");
    let on = find(&r, "on");
    assert_eq!(
        terms(&r.at(off, root, R::Epsilon, &quiet()).unwrap().unwrap(), 0),
        [(vec![], "\"2\"".into())]
    );
    assert!(
        r.is_zero(
            &r.at(off, root, R::Residual, &quiet()).unwrap().unwrap(),
            &quiet()
        )
        .unwrap()
    );
    assert_eq!(r.holds_at(off, root, &quiet()).unwrap(), Some(true));
    let original = &r.base().occurrences()[off];
    assert!(original.component_holds.is_none());
    assert!(original.evaluated_nu.is_none());
    assert_eq!(
        terms(&r.at(off, root, R::Nu, &quiet()).unwrap().unwrap(), 0),
        [(vec![0], "\"1\"".into())]
    );
    assert_eq!(r.holds_at(on, root, &quiet()).unwrap(), Some(false));
    assert_eq!(r.factors()[0].required_generators, [on]);
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn finite_parameter_rows_and_nested_tuple_components_share_factors_and_keep_individual_zeroes() {
    let i = inputs(
        "view half():Q=rat(1,2);view five():Fp(5)=1;law required axes(c:Part,b:Bool):((c.quantity,half()),five())=((if b then 2 else 1,rat(1,3)),2);",
    );
    let r = run(i.clone());
    let root = r.root_atom().unwrap();
    assert_eq!(r.factors().len(), 3);
    assert_eq!(r.coordinates().len(), 6);
    let z = r.factors().iter().position(|f| f.ty == Type::Z).unwrap();
    let q = r.factors().iter().position(|f| f.ty == Type::Q).unwrap();
    let fp = r
        .factors()
        .iter()
        .position(|f| f.ty == Type::Fp("5".into()))
        .unwrap();
    let mut z_values = vec![];
    let mut paths = vec![];
    let mut rows = std::collections::BTreeSet::new();
    let mut holds = 0;
    for (index, coordinate) in r.coordinates().iter().enumerate() {
        paths.push(coordinate.component.clone());
        rows.insert(coordinate.row);
        let value = r.at(index, root, R::Residual, &quiet()).unwrap().unwrap();
        let factor = match coordinate.component.as_slice() {
            [0, 0] => {
                z_values.push(terms(&value, z));
                z
            }
            [0, 1] => {
                assert_eq!(terms(&value, q), [(vec![], "[\"1\",\"6\"]".into())]);
                q
            }
            [1] => {
                assert_eq!(terms(&value, fp), [(vec![], "\"4\"".into())]);
                fp
            }
            _ => panic!("component path"),
        };
        assert_eq!(coordinate.factor, Some(factor));
        for other in 0..3 {
            if other != factor {
                assert!(terms(&value, other).is_empty());
            }
        }
        holds += usize::from(r.holds_at(index, root, &quiet()).unwrap() == Some(true));
    }
    paths.sort();
    assert_eq!(
        paths,
        [
            vec![0, 0],
            vec![0, 0],
            vec![0, 1],
            vec![0, 1],
            vec![1],
            vec![1]
        ]
    );
    assert_eq!(rows, std::collections::BTreeSet::from([Some(0), Some(1)]));
    z_values.sort();
    assert_eq!(z_values, [vec![], vec![(vec![], "\"1\"".into())]]);
    assert_eq!(holds, 1);
    assert_eq!(r.factors()[z].symbols.len(), 1);
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn unknown_parameter_family_and_unsupported_predicate_are_not_a_ready_empty_product() {
    let missing_owner = fixture::A
        .lines()
        .filter(|l| !l.contains("\"owner-p\""))
        .collect::<Vec<_>>()
        .join("\n");
    let i = inputs_with(
        "law required ownerDomain(a:Root,x:Option<Part[a]>):1=0;",
        &missing_owner,
    );
    let r = run(i.clone());
    assert_eq!(r.status(), S::Undetermined);
    assert!(!r.is_complete());
    assert!(r.coordinates().is_empty());
    assert!(r.factors().is_empty());
    assert!(
        r.base()
            .base()
            .base()
            .evaluations()
            .iter()
            .any(|v| !v.family().missing().is_empty())
    );
    r.recheck(i, &quiet()).unwrap();
    let i = inputs("law required predicate(c:Part):c.quantity>0;");
    let r = run(i.clone());
    assert_eq!(r.status(), S::UnsupportedAlgorithm);
    assert_eq!(r.coordinates().len(), 1);
    assert_eq!(r.coordinates()[0].status, S::UnsupportedAlgorithm);
    assert!(r.coordinates()[0].factor.is_none());
    assert_eq!(
        r.holds_at(0, r.root_atom().unwrap(), &quiet()).unwrap(),
        None
    );
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn an_unexecuted_match_body_keeps_missing_support_and_no_root_value() {
    let map = fixture::A
        .lines()
        .filter(|l| !l.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    let i = inputs_with(
        "law required amount(c:Part):match c.quantity {n=>n=0;};",
        &map,
    );
    let r = run(i.clone());
    assert_eq!(r.status(), S::Undetermined);
    let q = &r.coordinates()[0];
    assert!(q.nu.is_none() && q.epsilon.is_none() && q.residual.is_none());
    assert_eq!(q.conditional_holds, None);
    assert!(r.factors()[0].symbols[0].value.is_none());
    assert!(r.factors()[0].symbols[0].readings[0].fact.atom.is_none());
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn current_inputs_provenance_and_invalid_object_are_checked_again() {
    let body = "law required amount(c:Part):c.quantity=0;";
    let i = inputs(body);
    let r = run(i.clone());
    for changed in [
        inputs("law required amount(c:Part):c.quantity=1;"),
        inputs_with(body, &fixture::A.replace("fixture-r1", "fixture-other")),
    ] {
        assert!(matches!(r.recheck(changed, &quiet()), Err(F::Original(_))));
    }
    assert!(matches!(
        object_polynomial_observable(i, "Selected", "v", "root", 999, &quiet()),
        Err(F::Original(_))
    ));
}
#[test]
fn fixed_stops_keep_complete_coordinate_prefixes_raw_counterexamples_and_frozen_probes() {
    use archsig_common::control::Checkpoint as C;
    use archsig_input::result::Signal;
    use std::{cell::RefCell, rc::Rc};
    let i =
        inputs("law required first(c:Part):c.quantity=0;law required second(c:Part):c.quantity=1;");
    let baseline = run(i.clone());
    for recheck in [false, true] {
        let history = Rc::new(RefCell::new(vec![]));
        let h = history.clone();
        let traced = Control::new(move |p| {
            h.borrow_mut().push(p);
            None
        });
        if recheck {
            baseline.recheck(i.clone(), &traced).unwrap();
        } else {
            object_polynomial_observable(i.clone(), "Selected", "v", "root", 0, &traced).unwrap();
        }
        for at in [C::PolynomialObservable, C::PolynomialObservableCoordinate] {
            let count = history.borrow().iter().filter(|&&p| p == at).count();
            assert!(count > 0);
            for nth in [1, count] {
                for signal in [Signal::Int, Signal::Term] {
                    let hits = Rc::new(RefCell::new(0));
                    let h = hits.clone();
                    let probes = Rc::new(RefCell::new(0));
                    let p = probes.clone();
                    let c = Control::new(move |point| {
                        *p.borrow_mut() += 1;
                        if point == at {
                            *h.borrow_mut() += 1;
                        }
                        (point == at && *h.borrow() == nth).then_some(signal)
                    });
                    let failure = if recheck {
                        baseline.recheck(i.clone(), &c).unwrap_err()
                    } else {
                        object_polynomial_observable(i.clone(), "Selected", "v", "root", 0, &c)
                            .unwrap_err()
                    };
                    let F::Reading { cause, partial } = failure else {
                        panic!("new product stage")
                    };
                    assert_eq!(cause, ConstructionFailure::Stopped(signal));
                    for (index, q) in partial.coordinates().iter().enumerate() {
                        let expected = &baseline.coordinates()[index];
                        assert_eq!(q.occurrence, expected.occurrence);
                        assert_eq!(q.conditional_holds, Some(false));
                        assert_eq!(
                            q.nu.as_ref().map(|v| v.blocks()),
                            expected.nu.as_ref().map(|v| v.blocks())
                        );
                        assert_eq!(
                            q.epsilon.as_ref().map(|v| v.blocks()),
                            expected.epsilon.as_ref().map(|v| v.blocks())
                        );
                        assert_eq!(
                            q.residual.as_ref().map(|v| v.blocks()),
                            expected.residual.as_ref().map(|v| v.blocks())
                        );
                    }
                    assert!(
                        partial
                            .base()
                            .occurrences()
                            .iter()
                            .all(|q| q.component_holds == Some(false) && q.epsilon.is_some())
                    );
                    assert_eq!(
                        partial.is_complete(),
                        partial.coordinates().len() == baseline.coordinates().len()
                    );
                    if at == C::PolynomialObservableCoordinate && nth == count {
                        assert!(partial.is_complete());
                    }
                    if let Some(root) = partial.root_atom() {
                        assert_eq!(Some(root), baseline.root_atom());
                    }
                    let before = *probes.borrow();
                    assert_eq!(
                        partial.zero(&c).unwrap_err(),
                        ConstructionFailure::Stopped(signal)
                    );
                    assert_eq!(*probes.borrow(), before);
                }
            }
        }
    }
}
