use crate::observed::integer_fiber::{generated, reuse};
use crate::observed::result::*;
use crate::observed::*;
use archsig_common::control::quiet;
use std::sync::Arc;
#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/integer_reobservation_data.rs");
}
const BODY: &str = "view bound(s:State):Z=s.b;view first(s:State):Z=s.h;view second(s:State):Z=s.k;change choose(s:State,p:Z)=s with {h=p};law required valid(s:State):s.a*s.h=s.b;";
const ASKS: [&str; 5] = [
    "u=evaluate(Pair.bound,s=@v/s)",
    "s=solve(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
    "r=repair(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
    "h=evaluate(Pair.first,on=$r.object,s=@v/s)",
    "ok=check(Pair.valid,on=$r.object,s=@v/s)",
];
fn value(r: &ObservedEvaluation, id: &str) -> Scalar {
    let a = r.answers.iter().find(|a| a.id == id).unwrap();
    match &r.nodes[a.outputs["value"].0].payload {
        Some(Payload::Scalar(v)) => v.clone(),
        Some(Payload::Construction(v)) => v.scalar().unwrap().clone(),
        _ => panic!("scalar"),
    }
}
fn equivalent(a: &ObservedEvaluation, b: &ObservedEvaluation) {
    assert_eq!(a.result_wire(), b.result_wire());
    assert!(
        a.issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        a.issues
    );
    for node in &a.nodes {
        if let Some(Payload::Construction(v)) = &node.payload {
            assert_eq!(v.witness.inputs().sources(), a.prepared.inputs().sources());
        }
    }
}
#[test]
fn constant_update_reuses_integer_decomposition_before_current_fiber_and_original_law_check() {
    let c = quiet();
    let old = evaluate_observed_bytes(fixture::input(BODY, "2", "1"), &ASKS, &c).unwrap();
    assert!(!old.integer_cache.is_empty());
    let before = generated();
    let hits = reuse::reused();
    let current =
        reevaluate_observed_bytes(&old, fixture::input(BODY, "2", "2"), &ASKS, &c).unwrap();
    let warm_count = generated() - before;
    assert!(reuse::reused() > hits);
    let before = generated();
    let cold = evaluate_observed_bytes(fixture::input(BODY, "2", "2"), &ASKS, &c).unwrap();
    assert!(warm_count < generated() - before, "消去を実際に省く");
    equivalent(&current, &cold);
    assert_eq!(value(&current, "h"), Scalar::Z(1.into()));
    assert_eq!(
        current.answers.last().unwrap().status,
        Decision::Established
    );
    assert!(
        old.integer_cache
            .iter()
            .any(|a| current.integer_cache.iter().any(|b| Arc::ptr_eq(a, b)))
    );
    assert!(!old.answers[2].outputs.contains_key("object"));
    let maximum = current.integer_cache.len();
    let mut previous = current;
    for rhs in ["3", "4", "1", "6", "2"] {
        let current =
            reevaluate_observed_bytes(&previous, fixture::input(BODY, "2", rhs), &ASKS, &c)
                .unwrap();
        let cold = evaluate_observed_bytes(fixture::input(BODY, "2", rhs), &ASKS, &c).unwrap();
        equivalent(&current, &cold);
        assert!(current.integer_cache.len() <= maximum);
        previous = current;
    }
}
#[test]
fn guarded_free_and_unique_original_parameter_fibers_match_cold_evaluation() {
    let body = BODY.replace(
        "change choose(s:State,p:Z)=s with {h=p};",
        "change choose(s:State,p:Z,q:Z,t:Z) when p+q=s.b =s with {h=p,k=q+t};",
    ) + "law optional pinned(s:State):s.a*s.h=s.b and s.k=3;";
    let asks = [
        "free=solve(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "multi=repair(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "s=solve(Pair.pinned,using=Pair.choose,on=@v/s,s=@v/s)",
        "r=repair(Pair.pinned,using=Pair.choose,on=@v/s,s=@v/s)",
        "h=evaluate(Pair.first,on=$r.object,s=@v/s)",
        "k=evaluate(Pair.second,on=$r.object,s=@v/s)",
        "ok=check(Pair.pinned,on=$r.object,s=@v/s)",
    ];
    let c = quiet();
    let old = evaluate_observed_bytes(fixture::input(&body, "2", "2"), &asks, &c).unwrap();
    let current =
        reevaluate_observed_bytes(&old, fixture::input(&body, "2", "4"), &asks, &c).unwrap();
    let cold = evaluate_observed_bytes(fixture::input(&body, "2", "4"), &asks, &c).unwrap();
    equivalent(&current, &cold);
    assert_eq!(value(&current, "h"), Scalar::Z(2.into()));
    assert_eq!(value(&current, "k"), Scalar::Z(3.into()));
    let exists = current.answers[1].outputs["existence"];
    assert_eq!(
        current.nodes[exists.0].judgment.as_ref().unwrap().status,
        Decision::Established
    );
    assert!(current.answers[1].outputs.contains_key("solutions"));
    assert!(
        !current.answers[1].outputs.contains_key("object"),
        "非自明な元parameter核を消さない"
    );
    assert_eq!(
        current.answers.last().unwrap().status,
        Decision::Established
    );
    assert!(
        old.integer_cache
            .iter()
            .any(|a| current.integer_cache.iter().any(|b| Arc::ptr_eq(a, b)))
    );
}
#[test]
fn changed_coefficients_or_law_regenerate_and_current_input_is_always_checked() {
    let c = quiet();
    let old = evaluate_observed_bytes(fixture::input(BODY, "2", "2"), &ASKS, &c).unwrap();
    let before = generated();
    let current =
        reevaluate_observed_bytes(&old, fixture::input(BODY, "3", "2"), &ASKS, &c).unwrap();
    assert!(generated() > before);
    equivalent(
        &current,
        &evaluate_observed_bytes(fixture::input(BODY, "3", "2"), &ASKS, &c).unwrap(),
    );
    for body in [
        BODY.replace("s.a*s.h=s.b", "s.a*s.h=s.b+2"),
        BODY.replace("h=p", "h=p+1"),
        BODY.replace("p:Z)", "p:Z) when p=s.b"),
    ] {
        let current =
            reevaluate_observed_bytes(&old, fixture::input(&body, "2", "2"), &ASKS, &c).unwrap();
        equivalent(
            &current,
            &evaluate_observed_bytes(fixture::input(&body, "2", "2"), &ASKS, &c).unwrap(),
        );
        assert!(
            !old.integer_cache
                .iter()
                .any(|a| current.integer_cache.iter().any(|b| Arc::ptr_eq(a, b)))
        );
    }
    let input = fixture::input(BODY, "2", "2");
    let invalid = archsig_input::input::InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        input.law().bytes().to_vec(),
        std::str::from_utf8(input.archmap().bytes())
            .unwrap()
            .replace(
                "\"field\":\"Pair.State.k\",\"value\":\"0\"",
                "\"field\":\"Pair.State.k\",\"value\":false",
            )
            .into_bytes(),
    );
    assert!(reevaluate_observed_bytes(&old, invalid, &ASKS, &c).is_err());
}

fn replace_map(
    input: archsig_input::input::InputSources,
    change: impl FnOnce(&str) -> String,
) -> archsig_input::input::InputSources {
    archsig_input::input::InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        input.law().bytes().to_vec(),
        change(std::str::from_utf8(input.archmap().bytes()).unwrap()).into_bytes(),
    )
}
#[test]
fn shared_integer_decomposition_uses_current_sources_and_does_not_retain_withdrawn_rhs() {
    let c = quiet();
    let old = evaluate_observed_bytes(fixture::input(BODY, "2", "2"), &ASKS, &c).unwrap();
    let current_input = || {
        replace_map(fixture::input(BODY, "2", "4"), |s| {
            s.replace("\"id\":\"b\"", "\"id\":\"current-b\"")
                .replace("specification", "proposed")
                .replace("Integer reobservation fixture", "Current observation")
        })
    };
    let current = reevaluate_observed_bytes(&old, current_input(), &ASKS, &c).unwrap();
    equivalent(
        &current,
        &evaluate_observed_bytes(current_input(), &ASKS, &c).unwrap(),
    );
    assert!(
        old.integer_cache
            .iter()
            .any(|a| current.integer_cache.iter().any(|b| Arc::ptr_eq(a, b)))
    );
    assert!(
        current
            .nodes
            .iter()
            .flat_map(|n| n.support.iter())
            .any(|f| f.atom.as_deref() == Some("current-b"))
    );
    assert!(
        !current
            .nodes
            .iter()
            .flat_map(|n| n.support.iter())
            .any(|f| f.atom.as_deref() == Some("b"))
    );
    let missing = || {
        replace_map(fixture::input(BODY, "2", "2"), |s| {
            s.replace(
                r#",{"id":"b","subject":"s","field":"Pair.State.b","value":"2","origin":"model"}"#,
                "",
            )
        })
    };
    let current = reevaluate_observed_bytes(&old, missing(), &ASKS, &c).unwrap();
    equivalent(
        &current,
        &evaluate_observed_bytes(missing(), &ASKS, &c).unwrap(),
    );
    assert!(!current.answers[2].outputs.contains_key("object"));
}
#[test]
fn interrupted_integer_reobservation_keeps_the_verified_prefix_and_no_cache() {
    use archsig_common::control::{Checkpoint, Control};
    use std::{cell::Cell, rc::Rc};
    let old = evaluate_observed_bytes(fixture::input(BODY, "2", "2"), &ASKS, &quiet()).unwrap();
    let original = old.result_wire();
    let run = |stop: Option<usize>| {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let c = Control::new(move |kind| {
            if kind == Checkpoint::Reuse {
                count.set(count.get() + 1);
                if stop == Some(count.get()) {
                    return Some(archsig_input::result::Signal::Term);
                }
            }
            None
        });
        let result =
            reevaluate_observed_bytes(&old, fixture::input(BODY, "2", "4"), &ASKS, &c).unwrap();
        (result, seen.get())
    };
    let (complete, count) = run(None);
    assert_eq!(
        complete.answers.last().unwrap().status,
        Decision::Established
    );
    assert!(count > 3);
    let (stopped, _) = run(Some(count - 1));
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert!(stopped.integer_cache.is_empty());
    assert!(stopped.repair_cache.is_empty());
    assert_eq!(old.result_wire(), original);
}
