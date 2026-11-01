use super::*;
use crate::observed::{
    construction_result::ConstructionData as D, path_compose, public_path_compose::Part,
};
use std::{cell::Cell, rc::Rc};
mod fixture {
    use crate as archsig;
    include!("../../tests/common/public_path_compose.rs");
}
use fixture::{C, E, F};
fn example(qs: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(false, "unit-path"),
        qs,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    r
}
fn scalar(n: &Node) -> &Scalar {
    match &n.payload {
        Some(Payload::Scalar(s)) => s,
        Some(Payload::Construction(v)) => v.scalar().unwrap(),
        _ => panic!(),
    }
}
#[test]
fn public_paths_keep_all_46_atom_images_and_named_generators() {
    let r = example(&[
        E,
        F,
        C,
        "s=evaluate(Walk.step,e=@v/self)",
        "cc=compose($s.value,then=$c.operation)",
    ]);
    for (i, names) in [(2, vec!["e", "next"]), (4, vec!["self", "e", "next"])] {
        let Scalar::Path(p) = scalar(&r.nodes[r.answers[i].outputs["operation"].0]) else {
            panic!()
        };
        let step = p.step.as_ref().unwrap();
        assert_eq!(step.carrier.len(), 46);
        assert_eq!(step.images.len(), 46);
        let mut expected = vec![];
        for (snapshot, subjects) in [
            (
                "v",
                vec![
                    "A",
                    "p",
                    "q",
                    "r",
                    "e",
                    "alias",
                    "self",
                    "different",
                    "next",
                ],
            ),
            ("w", vec!["A", "p"]),
        ] {
            for subject in subjects {
                expected.push(Fact {
                    snapshot: snapshot.into(),
                    subject: subject.into(),
                    field: None,
                    atom: None,
                });
                if subject == "A" {
                    continue;
                }
                let (entity, fields) = if ["p", "q", "r"].contains(&subject) {
                    ("Node", vec!["owner", "mark", "link", "links", "members"])
                } else {
                    ("Hop", vec!["owner", "from", "to"])
                };
                for field in fields {
                    expected.push(Fact {
                        snapshot: snapshot.into(),
                        subject: subject.into(),
                        field: Some(format!("Paths.{entity}.{field}")),
                        atom: Some(format!("{subject}-{field}")),
                    });
                }
            }
        }
        expected.sort();
        assert_eq!(step.carrier, expected);
        for (a, b) in step.carrier.iter().zip(&step.images) {
            let expected = if a.snapshot == "v" && ["p", "q"].contains(&a.subject.as_str()) {
                Fact {
                    snapshot: "v".into(),
                    subject: "r".into(),
                    field: a.field.clone(),
                    atom: a
                        .atom
                        .as_ref()
                        .map(|id| format!("r-{}", id.split_once('-').unwrap().1)),
                }
            } else {
                a.clone()
            };
            assert_eq!(b, &expected);
        }
        assert_eq!(
            std::iter::once(&step.generator)
                .chain(&step.word_tail)
                .map(|g| {
                    let Scalar::Subject { subject, .. } = g else {
                        panic!()
                    };
                    subject.as_str()
                })
                .collect::<Vec<_>>(),
            names
        );
    }
}
#[test]
fn path_composition_recheck_rejects_forged_values_refs_conditions_scope_and_inputs() {
    let r = example(&[E, F, C]);
    assert_eq!(r.answers[2].status, Decision::Established);
    // 合成値の再検査の代表: 合成したPathのwordを書き換えると核が拒否する。
    let index = r.answers[2].outputs["operation"].0;
    rejects_mutated_prefix(&r, index, |nodes| {
        let Some(Payload::Construction(v)) = &mut nodes[index].payload else {
            panic!()
        };
        let D::PathComposition(Part::Path { value, .. }) = &mut v.data else {
            panic!()
        };
        let Scalar::Path(p) = value else { panic!() };
        p.step.as_mut().unwrap().word_tail.clear();
    });
    let bad = example(&[E, "bad=compose($e.value,then=$e.value)"]);
    assert_eq!(bad.answers[1].status, Decision::Refuted);
}
fn stopping(at: usize, point: Checkpoint) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let c = Control::new(move |p| {
        if p == point {
            seen.set(seen.get() + 1);
        }
        (seen.get() >= at).then_some(crate::result::Signal::Int)
    });
    (c, count)
}
#[test]
fn retained_path_calculation_keeps_only_fully_checked_words_and_actions() {
    let r = example(&[E, F]);
    let (Scalar::Path(a), Scalar::Path(b)) = (
        scalar(&r.nodes[r.answers[0].outputs["value"].0]),
        scalar(&r.nodes[r.answers[1].outputs["value"].0]),
    ) else {
        panic!()
    };
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(move |_| {
        seen.set(seen.get() + 1);
        None
    });
    let expected = path_compose::compose_retained(a, b, &a.reading, &control, |_, _| {})
        .ok()
        .unwrap();
    let total = count.get();
    assert!(total > 100);
    for at in [1, total / 2, total - 1, total] {
        let (control, _) = stopping(at, Checkpoint::FiniteIteration);
        let f = path_compose::compose_retained(a, b, &a.reading, &control, |_, _| {})
            .err()
            .unwrap();
        assert!(matches!(f.cause, ValidationFailure::Stop(_)));
        if at == total {
            assert_eq!(f.partial.as_ref(), Some(&expected));
        } else {
            assert!(f.partial.is_none());
        }
    }
}
#[test]
fn public_path_transfer_stops_keep_completed_values_and_verified_prefixes() {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut probe = Control::new(move |p| {
        if p == Checkpoint::NativeResultNode {
            seen.set(seen.get() + 1);
        }
        None
    });
    let prepared = prepare_observed(
        fixture::input(false, "unit-path"),
        &[E, F, C],
        &mut Control::unlimited(),
    )
    .unwrap();
    let normal = evaluate_observed(prepared, &mut probe).unwrap();
    assert_eq!(normal.status(), "complete");
    let total = count.get();
    assert!(total >= 3);
    // 停止の種類と位置は代表1つ(最初の転記点での time 停止)だけを見る。
    let (mut control, _) = stopping(1, Checkpoint::NativeResultNode);
    let prepared = prepare_observed(
        fixture::input(false, "unit-path"),
        &[E, F, C],
        &mut Control::unlimited(),
    )
    .unwrap();
    let stopped = evaluate_observed(prepared, &mut control).unwrap();
    assert_ne!(stopped.status(), "error", "{:?}", stopped.issues);
    let a = &stopped.answers[2];
    assert_eq!(a.status, Decision::Established);
    assert!(a.outputs.contains_key("operation"));
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
fn visibility_sources() -> InputSources {
    fixture::visibility_input()
}
const VISIBILITY_ASKS: [&str; 3] = [
    "p=evaluate(Reservations.route,e=@v/e)",
    "q=evaluate(Alternative.route,e=@v/h)",
    "bad=compose($p.value,then=$q.value)",
];
#[test]
fn invisible_path_conditions_recheck_actual_refs_and_keep_refutations_at_transfer_stops() {
    let r = evaluate_observed_bytes(
        visibility_sources(),
        &VISIBILITY_ASKS,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    assert_eq!(r.answers[2].status, Decision::Refuted);
    let condition=r.nodes.iter().position(|n| matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.data,D::PathComposition(Part::Visibility{..})))).unwrap();
    // 判断の再検査の代表: 可視性条件の判断を反転すると核が拒否する。
    rejects_mutated_prefix(&r, condition, |nodes| {
        nodes[condition].judgment.as_mut().unwrap().status = Decision::Established;
    });
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut probe = Control::new(move |p| {
        if p == Checkpoint::NativeResultNode {
            seen.set(seen.get() + 1);
        }
        None
    });
    let prepared = prepare_observed(
        visibility_sources(),
        &VISIBILITY_ASKS,
        &mut Control::unlimited(),
    )
    .unwrap();
    evaluate_observed(prepared, &mut probe).unwrap();
    let total = count.get();
    assert!(total >= 5);
    let (mut control, _) = stopping(1, Checkpoint::NativeResultNode);
    let prepared = prepare_observed(
        visibility_sources(),
        &VISIBILITY_ASKS,
        &mut Control::unlimited(),
    )
    .unwrap();
    let stopped = evaluate_observed(prepared, &mut control).unwrap();
    assert_ne!(stopped.status(), "error", "{:?}", stopped.issues);
    assert_eq!(stopped.answers[2].status, Decision::Refuted);
    assert!(!stopped.answers[2].outputs.contains_key("operation"));
    assert_eq!(stopped.answers[2].evidence.len(), 1);
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
