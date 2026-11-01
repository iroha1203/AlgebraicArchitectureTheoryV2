use super::*;
use crate::observed::public_compare::{values::Data as V, Part};
mod term_fixture {
    use crate as archsig;
    include!("../../tests/common/public_term_compare.rs");
}
const PREFIX: [&str; 2] = [
    "l=evaluate(Terms.observed,s=@v/s)",
    "r=evaluate(Terms.finiteSame)",
];
const FINITE: &str = "a=compare($l.value,to=$r.value,kind=value)";
fn term_input() -> InputSources {
    term_fixture::input("", false, "term-native")
}
fn term_example(qs: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(term_input(), qs, &mut Control::unlimited()).unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    r
}
#[test]
fn term_comparison_recheck_rejects_derived_domain_values_normalizations_and_point_forgery() {
    let r = term_example(&[
        PREFIX[0],
        PREFIX[1],
        FINITE,
        "f=evaluate(Terms.read,s=@v/s)",
        "other=evaluate(Terms.affineSlope)",
        "bad=compare($f.value,to=$other.value,kind=value)",
    ]);
    assert_eq!(r.answers[2].status, Decision::Established);
    assert_eq!(r.answers[5].status, Decision::Refuted);
    // 判断の再検査の代表: 導出した比較命題の判断を反転すると核が拒否する。
    let claim = r
        .nodes
        .iter()
        .position(|n| matches!(&n.payload, Some(Payload::Construction(v)) if matches!(&v.data, D::Comparison(Part::Derived { data, .. }) if matches!(data.as_ref(), V::Claim { .. }))))
        .unwrap();
    rejects_mutated_prefix(&r, claim, |nodes| {
        let Some(Payload::Construction(v)) = &mut nodes[claim].payload else {
            panic!()
        };
        let D::Comparison(Part::Derived { data, .. }) = &mut v.data else {
            panic!()
        };
        let V::Claim { status, .. } = data.as_mut() else {
            panic!()
        };
        *status = if *status == Decision::Refuted {
            Decision::Established
        } else {
            Decision::Refuted
        };
    });
}
#[test]
fn finite_and_affine_comparison_calculation_stops_keep_only_completed_derivations() {
    for (left, right, status) in [
        (PREFIX[0], PREFIX[1], Decision::Established),
        (
            "l=evaluate(Terms.read,s=@v/s)",
            "r=evaluate(Terms.affineSame)",
            Decision::Established,
        ),
        (
            "l=evaluate(Terms.read,s=@v/s)",
            "r=evaluate(Terms.affineSlope)",
            Decision::Refuted,
        ),
    ] {
        let prefix = term_example(&[left, right]);
        let prepared = prepare_observed(
            term_input(),
            &[left, right, FINITE],
            &mut Control::unlimited(),
        )
        .unwrap();
        let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
        let graph = || {
            let mut g = rebuild_for_origin_and_support_recheck(&prefix, &prefix.nodes).unwrap();
            g.requests = prepared.requests().requests().to_vec();
            g.active = crate::observed::call::Context {
                request: 2,
                frame: None,
                iteration: None,
                instance: None,
                case: None,
            };
            g
        };
        let point = Checkpoint::FiniteIteration;
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut probe = Control::new(move |p| {
            if p == point {
                seen.set(seen.get() + 1)
            }
            None
        });
        let normal = crate::observed::public_compare::evaluate(
            &prepared,
            &env,
            &mut graph(),
            &prepared.requests().requests()[2],
            &mut probe,
        )
        .unwrap();
        assert_eq!(normal.status, status);
        let total = count.get();
        assert!(total > 10);
        // 停止の種類と位置は代表1つ(計算の途中の time 停止)だけを見る。
        let (mut c, _) = stopping(total / 2, 0, point);
        let mut g = graph();
        let answer = crate::observed::public_compare::evaluate(
            &prepared,
            &env,
            &mut g,
            &prepared.requests().requests()[2],
            &mut c,
        );
        match answer {
            Ok(a) => {
                if !a.outputs.contains_key("comparison") {
                    assert_eq!(a.status, Decision::Undetermined);
                }
                env.validate_answer(&g, &prepared.requests().requests()[2], &a)
                    .unwrap();
                for (i, n) in g.nodes.iter().enumerate() {
                    env.recheck_node(&g, n, i).unwrap();
                }
            }
            Err(ValidationFailure::Stop(_)) => {}
            Err(e) => panic!("unexpected {e:?}"),
        }
    }
}
