use super::*;
use archsig_input::{definition, input::InputSources};
use std::{cell::Cell, rc::Rc};

#[path = "../../../../../tests/common/three_edge.rs"]
mod triangle;

#[test]
fn coordinate_references_keep_order_repetition_and_exact_owner_membership() {
    let arguments = [NodeRef(2), NodeRef(7), NodeRef(19)];
    let coordinates = [NodeRef(19).wire(), NodeRef(2).wire(), NodeRef(19).wire()];
    assert_eq!(
        coordinates
            .iter()
            .map(|wire| vector_reference(&arguments, wire))
            .collect::<Option<Vec<_>>>(),
        Some(vec![NodeRef(19), NodeRef(2), NodeRef(19)])
    );
    for wire in [
        NodeRef(3).wire(),
        Json::obj([("node", Json::str("n07"))]),
        Json::obj([("node", Json::str("n+7"))]),
        Json::obj([("node", Json::str("n184467440737095516160"))]),
        Json::obj([("node", Json::str("n7")), ("extra", Json::Bool(true))]),
        Json::obj([("node", Json::Nat(7))]),
        Json::obj([]),
        Json::str("n7"),
    ] {
        assert_eq!(vector_reference(&arguments, &wire), None, "{wire:?}");
    }
}

fn inputs(rational: bool) -> InputSources {
    let input = triangle::input(Some(3));
    if !rational {
        return input;
    }
    let original = std::str::from_utf8(input.definitions()[0].bytes()).unwrap();
    let definitions = original.replace("\"type\":\"Z\"", "\"type\":\"Q\"");
    let before = definition::check_definitions(&[("d", original.as_bytes())]).unwrap();
    let after = definition::check_definitions(&[("d", definitions.as_bytes())]).unwrap();
    let old = &before.vocabularies()["Coordinates"].digest;
    let new = &after.vocabularies()["Coordinates"].digest;
    let law = std::str::from_utf8(input.law().bytes())
        .unwrap()
        .replace(old, new)
        .replace("d:Z", "d:Q");
    let mut map = std::str::from_utf8(input.archmap().bytes())
        .unwrap()
        .replace(old, new);
    // 三辺fixtureの整数原始値だけを分母1の有理数へ写す。
    for number in ["0", "1", "3"] {
        map = map.replace(
            &format!("\"value\":\"{number}\""),
            &format!("\"value\":[\"{number}\",\"1\"]"),
        );
    }
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

#[test]
fn borrowed_local_vector_comparison_keeps_z_q_and_iteration_stops() {
    for rational in [false, true] {
        let evaluated = crate::observed::evaluate_observed_bytes(
            inputs(rational),
            &[
                "a=build(Coordinates,on=@triangle/root)",
                "l=localize($a.object,using=Coordinates.move)",
                "d=diagnose($l.system)",
            ],
            &Control::unlimited(),
        )
        .unwrap();
        let class = evaluated.answers[2].outputs["class"];
        let mut graph = Graph::default();
        graph.nodes = evaluated.nodes.into();
        let Json::Obj(fields) = vector_wire(&graph, class).unwrap() else {
            panic!()
        };
        let vector =
            vector_reference(&graph.get(class).unwrap().arguments, &fields["coordinates"]).unwrap();
        let calls = Rc::new(Cell::new(0));
        let seen = calls.clone();
        let probe = Control::new(move |point| {
            if point == Checkpoint::FiniteIteration {
                seen.set(seen.get() + 1);
            }
            None
        });
        assert!(vector_equal(&graph, vector, vector, &probe).unwrap());
        let total = calls.get();
        assert!(total > 0);
        for at in 1..=total {
            let mut count = 0;
            let stopped = Control::new(move |point| {
                if point == Checkpoint::FiniteIteration {
                    count += 1;
                }
                (count == at).then_some(Signal::Int)
            });
            assert!(matches!(
                vector_equal(&graph, vector, vector, &stopped),
                Err(ValidationFailure::Stop(Signal::Int))
            ));
        }
    }
}
