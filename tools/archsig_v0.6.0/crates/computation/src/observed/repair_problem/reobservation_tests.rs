use super::*;
use crate::observed::environment::repair_problem::reuse;
use crate::observed::{ObservedEvaluation, evaluate_observed_bytes, reevaluate_observed_bytes};
use std::collections::BTreeSet;
#[allow(dead_code)]
mod repair_problem_data {
    include!("../../../../../tests/common/repair_problem_data.rs");
}
#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/repair_observation_data.rs");
}
const BODY: &str = "view input(r:Root):Bool=r.h;view all(r:Root):Set<Part> =Part[r];view flag(c:Part):Bool=c.flag;change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):forall c in Part[r]. if c.label=\"a\" then c.flag=r.h else c.flag;";
const ASKS: [&str; 8] = [
    "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root)",
    "u=evaluate(Selected.all,r=@v/root)",
    "s=solve($p.problem,within=$u.value)",
    "c=candidate($s.solutions,index=0)",
    "ap=apply($c.assignment,in=$s.solutions)",
    "ok=check(Selected.valid,on=$ap.object,r=@v/root)",
    "a=evaluate(Selected.flag,on=$ap.object,c=@v/a)",
    "b=evaluate(Selected.flag,on=$ap.object,c=@v/b)",
];
fn input(body: &str, known: Option<&str>) -> archsig_input::input::InputSources {
    fixture::with_parts(
        &[("a", false, "a"), ("b", false, "b")],
        body,
        "\"Bool\"",
        known,
    )
}
fn shared(result: &ObservedEvaluation) -> &Arc<Shared> {
    let Some(Payload::Construction(v)) =
        &result.nodes[result.answers[0].outputs["problem"].0].payload
    else {
        panic!()
    };
    let D::SharedRepair(d) = &v.data else {
        panic!()
    };
    d.source.shared.as_ref().unwrap()
}
fn equivalent(current: &ObservedEvaluation, cold: &ObservedEvaluation) {
    assert_eq!(current.status(), cold.status());
    for (a, b) in current.answers.iter().zip(&cold.answers) {
        assert_eq!(a.id, b.id);
        assert_eq!(a.status, b.status, "{}", a.id);
        assert_eq!(a.scope, b.scope, "{}", a.id);
    }
    let support = |r: &ObservedEvaluation| {
        r.nodes
            .iter()
            .flat_map(|n| n.support.iter().cloned())
            .collect::<BTreeSet<_>>()
    };
    assert_eq!(support(current), support(cold));
    assert!(
        current
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        current.issues
    );
    for node in &current.nodes {
        if let Some(Payload::Construction(v)) = &node.payload {
            assert_eq!(
                v.witness.inputs().sources(),
                current.prepared.inputs().sources()
            );
        }
    }
}
fn value(result: &ObservedEvaluation, id: &str) -> Scalar {
    let answer = result.answers.iter().find(|a| a.id == id).unwrap();
    match &result.nodes[answer.outputs["value"].0].payload {
        Some(Payload::Scalar(value)) => value.clone(),
        Some(Payload::Construction(value)) => value.scalar().unwrap().clone(),
        _ => panic!("型付きの値"),
    }
}
#[test]
fn reobservation_regenerates_changed_law_factors_and_shares_unaffected_rows() {
    let c = archsig_common::control::quiet();
    let old = evaluate_observed_bytes(input(BODY, Some("false")), &ASKS, &c).unwrap();
    assert_eq!(old.status(), "complete", "{:?}", old.issues);
    let before = reuse::counts();
    let current = reevaluate_observed_bytes(&old, input(BODY, Some("true")), &ASKS, &c).unwrap();
    let after = reuse::counts();
    assert!(after.1 > before.1, "不変なLaw関係を再生成せず引き継ぐ");
    let cold_before = reuse::counts();
    let cold = evaluate_observed_bytes(input(BODY, Some("true")), &ASKS, &c).unwrap();
    let cold_after = reuse::counts();
    assert!(
        after.0 - before.0 < cold_after.0 - cold_before.0,
        "新規計算より関係生成が少ない"
    );
    equivalent(&current, &cold);
    assert_eq!(value(&old, "a"), Scalar::Bool(false));
    assert_eq!(value(&current, "a"), Scalar::Bool(true));
    assert_eq!(value(&current, "b"), Scalar::Bool(true));
    let old = shared(&old);
    let new = shared(&current);
    assert!(
        old.compiled.relations.relations().iter().any(|a| new
            .compiled
            .relations
            .relations()
            .iter()
            .any(|b| Arc::ptr_eq(&a.rows, &b.rows))),
        "純粋な行の所有を実際に共有する"
    );
}
#[test]
fn reobservation_uses_current_atom_provenance_even_when_values_are_unchanged() {
    let c = archsig_common::control::quiet();
    let old = evaluate_observed_bytes(input(BODY, Some("false")), &ASKS, &c).unwrap();
    let original = input(BODY, Some("false"));
    let map = std::str::from_utf8(original.archmap().bytes())
        .unwrap()
        .replace("\"id\":\"h\"", "\"id\":\"current-h\"")
        .replace("Finite repair fixture", "Current measurement")
        .replace("\"mode\":\"specification\"", "\"mode\":\"proposed\"");
    let changed = || {
        archsig_input::input::InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            original.law().bytes().to_vec(),
            map.as_bytes().to_vec(),
        )
    };
    let before = reuse::counts();
    let current = reevaluate_observed_bytes(&old, changed(), &ASKS, &c).unwrap();
    assert!(reuse::counts().1 > before.1);
    let cold = evaluate_observed_bytes(changed(), &ASKS, &c).unwrap();
    equivalent(&current, &cold);
    let facts = current
        .nodes
        .iter()
        .flat_map(|n| n.support.iter())
        .filter(|f| f.field.as_deref() == Some("Pattern.Root.h"))
        .collect::<Vec<_>>();
    assert!(facts.iter().any(|f| f.atom.as_deref() == Some("current-h")));
    assert!(facts.iter().all(|f| f.atom.as_deref() != Some("h")));
}
#[test]
fn observation_axis_identity_is_part_of_relation_reuse_conditions() {
    let c = archsig_common::control::quiet();
    let body = "view input(r:Root):Bool=r.h;view other(r:Root):Bool=r.z;view constant(r:Root):Bool=true;change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root):forall c in Part[r]. c.flag=r.h;";
    let asks = [
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)",
        "later=evaluate(Selected.constant,r=@v/root)",
    ];
    let sources = || fixture::input(body, "\"Bool\"", None);
    let old = evaluate_observed_bytes(sources(), &asks, &c).unwrap();
    assert_eq!(old.status(), "complete");
    let asks = [
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.other,r=@v/root)",
        asks[1],
    ];
    let current = reevaluate_observed_bytes(&old, sources(), &asks, &c).unwrap();
    let cold = evaluate_observed_bytes(sources(), &asks, &c).unwrap();
    equivalent(&current, &cold);
    assert_eq!(current.answers[0].status, Decision::Undetermined);
    assert!(!current.answers[0].outputs.contains_key("problem"));
    assert_eq!(current.answers[1].status, Decision::Established);
}
#[test]
fn observation_addition_correction_and_withdrawal_match_fresh_evaluation() {
    let c = archsig_common::control::quiet();
    let mut previous = evaluate_observed_bytes(input(BODY, Some("false")), &ASKS, &c).unwrap();
    for known in [None, Some("true"), Some("false"), None, Some("false")] {
        let before = reuse::counts();
        let current = reevaluate_observed_bytes(&previous, input(BODY, known), &ASKS, &c).unwrap();
        assert!(
            reuse::counts().1 > before.1,
            "不変な関係を訂正・撤回・追加で引き継ぐ"
        );
        let cold = evaluate_observed_bytes(input(BODY, known), &ASKS, &c).unwrap();
        equivalent(&current, &cold);
        if let Some(known) = known {
            assert_eq!(current.status(), "complete");
            assert_eq!(value(&current, "a"), Scalar::Bool(known == "true"));
        } else {
            assert_eq!(current.status(), "partial");
            assert_eq!(current.answers[0].status, Decision::Undetermined);
            assert!(!current.answers[0].outputs.contains_key("problem"));
            assert!(!current.answers[4].outputs.contains_key("object"));
        }
        assert!(
            current.repair_cache.len() <= 1,
            "一つの生成条件について履歴を蓄積しない"
        );
        previous = current;
    }
}
#[test]
fn changed_law_operation_and_types_regenerate_relations() {
    let c = archsig_common::control::quiet();
    let old = evaluate_observed_bytes(input(BODY, Some("false")), &ASKS, &c).unwrap();
    for body in [
        BODY.replace("c.flag=r.h", "c.flag=not r.h"),
        BODY.replace("{flag=p}", "{flag=not p}"),
        BODY.replace("p:Bool", "p:Fp(3)")
            .replace("{flag=p}", "{flag=p=1}"),
    ] {
        let before = reuse::counts();
        let current =
            reevaluate_observed_bytes(&old, input(&body, Some("false")), &ASKS, &c).unwrap();
        assert_eq!(reuse::counts().1, before.1, "Law/操作の変更を失効させる");
        let cold = evaluate_observed_bytes(input(&body, Some("false")), &ASKS, &c).unwrap();
        equivalent(&current, &cold);
        assert_eq!(current.status(), "complete", "{:?}", current.issues);
    }
    let body = BODY
        .replace("input(r:Root):Bool=r.h", "input(r:Root):Z=r.h")
        .replace("c.flag=r.h", "c.flag=(r.h=0)");
    let sources = || {
        fixture::with_parts(
            &[("a", false, "a"), ("b", false, "b")],
            &body,
            "\"Z\"",
            Some("\"0\""),
        )
    };
    let before = reuse::counts();
    let current = reevaluate_observed_bytes(&old, sources(), &ASKS, &c).unwrap();
    assert_eq!(reuse::counts().1, before.1);
    let cold = evaluate_observed_bytes(sources(), &ASKS, &c).unwrap();
    equivalent(&current, &cold);
    assert_eq!(current.status(), "complete");
    assert_eq!(value(&current, "a"), Scalar::Bool(true));
}
#[test]
fn current_input_is_checked_outside_the_reused_region() {
    let c = archsig_common::control::quiet();
    let old = evaluate_observed_bytes(input(BODY, Some("false")), &ASKS, &c).unwrap();
    let source = input(BODY, Some("true"));
    let map = std::str::from_utf8(source.archmap().bytes())
        .unwrap()
        .replace("\"value\":\"b\"", "\"value\":false");
    let invalid = archsig_input::input::InputSources::from_bytes(
        source
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        source.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let Err(crate::observed::EvaluationFailure::Prepare(crate::observed::PrepareFailure::Inputs(
        error,
    ))) = reevaluate_observed_bytes(&old, invalid, &ASKS, &c)
    else {
        panic!("不正な現在入力を拒否する")
    };
    assert_eq!(error.status(), archsig_input::input::InputStatus::Invalid);
    assert_eq!(old.status(), "complete");
    assert_eq!(value(&old, "a"), Scalar::Bool(false));
}
#[test]
fn observation_family_refinement_reuses_unaffected_semantic_coordinates() {
    let c = archsig_common::control::quiet();
    let mut asks = ASKS;
    asks[0] = "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,r=@v/root)";
    asks[2] =
        "obs=observe(Selected.input,on=$p.problem,within=$u.value,output=assignment,r=@v/root)";
    asks[3] = "c=candidate($obs.solutions,index=0)";
    asks[4] = "ap=apply($c.assignment,in=$obs.solutions)";
    let mut previous = evaluate_observed_bytes(input(BODY, None), &asks, &c).unwrap();
    for known in [Some("true"), None, Some("false")] {
        let before = reuse::counts();
        let current = reevaluate_observed_bytes(&previous, input(BODY, known), &asks, &c).unwrap();
        assert!(
            reuse::counts().1 > before.1,
            "観測軸が増減しても不変なLaw関係を引き継ぐ"
        );
        let cold = evaluate_observed_bytes(input(BODY, known), &asks, &c).unwrap();
        equivalent(&current, &cold);
        let plan = current.answers[2].outputs["plan"];
        let Some(Payload::Construction(plan)) = &current.nodes[plan.0].payload else {
            panic!()
        };
        let wire = plan.wire();
        let Json::Obj(fields) = &wire else { panic!() };
        let Some(Json::Arr(requirements)) = fields.get("requirements") else {
            panic!()
        };
        assert_eq!(requirements.len(), usize::from(known.is_none()));
        if let Some(known) = known {
            assert_eq!(current.status(), "complete");
            assert_eq!(value(&current, "a"), Scalar::Bool(known == "true"));
        } else {
            assert!(!current.answers[4].outputs.contains_key("object"));
        }
        previous = current;
    }
}
#[test]
fn previously_unreachable_points_are_not_cached_as_false_law_rows() {
    let c = archsig_common::control::quiet();
    let body = BODY
        .replace(
            "{flag=p}",
            "{flag=if c.label=\"a\" and c.owner.h then true else p}",
        )
        .replace("c.flag=r.h", "not c.flag");
    let old = evaluate_observed_bytes(input(&body, Some("true")), &ASKS, &c).unwrap();
    assert_eq!(old.answers[2].status, Decision::Refuted);
    let before = reuse::counts();
    let current = reevaluate_observed_bytes(&old, input(&body, Some("false")), &ASKS, &c).unwrap();
    assert!(reuse::counts().1 > before.1);
    let cold = evaluate_observed_bytes(input(&body, Some("false")), &ASKS, &c).unwrap();
    equivalent(&current, &cold);
    assert_eq!(current.status(), "complete", "{:?}", current.issues);
    assert_eq!(current.answers[2].status, Decision::Established);
    assert_eq!(value(&current, "a"), Scalar::Bool(false));
}
#[test]
fn cache_dependencies_do_not_require_now_unreachable_observations() {
    let c = archsig_common::control::quiet();
    let body = BODY
        .replace(
            "{flag=p}",
            "{flag=if c.label=\"a\" and c.owner.h then true else p}",
        )
        .replace("c.flag=r.h", "(if c.flag then true else r.z)");
    let sources = |h, z: bool| {
        let original = input(&body, Some(h));
        let mut map = std::str::from_utf8(original.archmap().bytes())
            .unwrap()
            .to_owned();
        if z {
            map=map.replace("\"atoms\":[","\"atoms\":[{\"id\":\"z\",\"subject\":\"root\",\"field\":\"Pattern.Root.z\",\"value\":true,\"origin\":\"model\"},");
        }
        archsig_input::input::InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            original.law().bytes().to_vec(),
            map.into_bytes(),
        )
    };
    let old = evaluate_observed_bytes(sources("false", true), &ASKS, &c).unwrap();
    assert_eq!(old.status(), "complete");
    let current = reevaluate_observed_bytes(&old, sources("true", false), &ASKS, &c).unwrap();
    let cold = evaluate_observed_bytes(sources("true", false), &ASKS, &c).unwrap();
    equivalent(&current, &cold);
    assert_eq!(current.status(), "complete", "{:?}", current.issues);
    assert_eq!(value(&current, "a"), Scalar::Bool(true));
    // The normal check records discarded-branch diagnostics in the graph too.
    // They are not additional observations required to construct this problem.
    assert!(!current.answers[0].reasons.iter().any(|r| {
        r.missing
            .iter()
            .any(|f| f.field.as_deref() == Some("Pattern.Root.z"))
    }));
    assert_eq!(current.answers[5].status, Decision::Established);
}
#[test]
fn interrupted_reobservation_keeps_confirmed_answers_and_no_partial_cache() {
    use std::{cell::Cell, rc::Rc};
    let old = evaluate_observed_bytes(
        input(BODY, Some("false")),
        &ASKS,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    let asks = [ASKS[1], ASKS[0]];
    let run = |stop: Option<usize>| {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let c = Control::new(move |point| {
            if point == Checkpoint::Reuse {
                seen.set(seen.get() + 1);
                stop.filter(|n| *n == seen.get())
                    .map(|_| archsig_common::control::Signal::Term)
            } else {
                None
            }
        });
        let result = reevaluate_observed_bytes(&old, input(BODY, Some("true")), &asks, &c).unwrap();
        (result, count.get())
    };
    let (complete, count) = run(None);
    assert_eq!(complete.status(), "complete");
    assert!(count > 2);
    for at in [1, count / 2, count] {
        let (result, _) = run(Some(at));
        assert_eq!(result.status(), "interrupted");
        assert_eq!(result.answers[0].status, Decision::Established);
        assert_eq!(result.answers[1].status, Decision::Undetermined);
        assert!(!result.answers[1].outputs.contains_key("problem"));
        assert!(result.repair_cache.is_empty());
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_)))
        );
    }
    assert_eq!(old.status(), "complete");
    assert_eq!(value(&old, "a"), Scalar::Bool(false));
}
#[test]
fn opaque_function_bindings_fall_back_to_normal_evaluation() {
    let c = archsig_common::control::quiet();
    let body = "view program(r:Root):Term<(Bool)->Bool> =fn(x:Bool)=>x;view all(r:Root):Set<Part> =Part[r];view flag(c:Part):Bool=c.flag;change choose(c:Part,p:Bool)=c with {flag=p};law required valid(r:Root,f:Term<(Bool)->Bool>):forall c in Part[r]. f(c.flag)=r.h;";
    let asks = [
        "f=evaluate(Selected.program,r=@v/root)",
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root,f=$f.value)",
        "s=solve($p.problem,within=$u.value)",
        "c=candidate($s.solutions,index=0)",
        "ap=apply($c.assignment,in=$s.solutions)",
        "ok=check(Selected.valid,on=$ap.object,r=@v/root,f=$f.value)",
        "a=evaluate(Selected.flag,on=$ap.object,c=@v/a)",
    ];
    let old = evaluate_observed_bytes(input(body, Some("false")), &asks, &c).unwrap();
    assert_eq!(old.status(), "complete", "{:?}", old.issues);
    assert!(old.repair_cache.is_empty());
    let current = reevaluate_observed_bytes(&old, input(body, Some("true")), &asks, &c).unwrap();
    let cold = evaluate_observed_bytes(input(body, Some("true")), &asks, &c).unwrap();
    equivalent(&current, &cold);
    assert_eq!(current.status(), "complete", "{:?}", current.issues);
    assert!(current.repair_cache.is_empty());
    assert_eq!(value(&current, "a"), Scalar::Bool(true));
}
#[test]
fn reordered_subjects_keep_relation_correspondence_and_current_sources() {
    let c = archsig_common::control::quiet();
    let old = evaluate_observed_bytes(input(BODY, Some("false")), &ASKS, &c).unwrap();
    let original = input(BODY, Some("false"));
    let text = std::str::from_utf8(original.archmap().bytes()).unwrap();
    let a = r#"{"id":"a","type":"Pattern.Part","origin":"model"}"#;
    let b = r#"{"id":"b","type":"Pattern.Part","origin":"model"}"#;
    let map = text
        .replace(a, "REORDER_SUBJECT")
        .replace(b, a)
        .replace("REORDER_SUBJECT", b);
    let sources = || {
        archsig_input::input::InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            original.law().bytes().to_vec(),
            map.as_bytes().to_vec(),
        )
    };
    let before = reuse::counts();
    let current = reevaluate_observed_bytes(&old, sources(), &ASKS, &c).unwrap();
    assert!(reuse::counts().1 > before.1);
    let cold = evaluate_observed_bytes(sources(), &ASKS, &c).unwrap();
    equivalent(&current, &cold);
    assert_eq!(value(&current, "a"), Scalar::Bool(false));
    assert_eq!(value(&current, "b"), Scalar::Bool(true));
}
