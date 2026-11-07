use super::*;
use crate::observed::repair_problem::integer::tests::{data_for, fixture, without_atom};
use crate::observed::{evaluate_observed_bytes, reevaluate_observed_bytes};
use archsig_common::control::quiet;
const VIEWS: &str = "view all(s:State):Set<State> =set<State>{s};view vacant(s:State):Set<State> =set<State>{};view input(s:State):Z=s.b;view uninformative(s:State):Z=0;view first(s:State):Z=s.h;";
const ASKS: [&str; 8] = [
    "u=evaluate(Pair.all,s=@v/s)",
    "z=evaluate(Pair.vacant,s=@v/s)",
    "p=prepare(Pair.valid,using=Pair.choose,on=@v/s,inputs=Pair.input,s=@v/s)",
    "d=observe(Pair.uninformative,on=$p.problem,within=$u.value,output=decision,s=@v/s)",
    "a=observe(Pair.input,on=$p.problem,within=$u.value,output=assignment,s=@v/s)",
    "fixed=observe(Pair.input,on=$p.problem,within=$z.value,output=decision,s=@v/s)",
    "again=observe($a.plan,on=$p.problem,within=$u.value,output=decision)",
    "s=solve($p.problem,within=$u.value)",
];
fn body(law: &str) -> String {
    format!("{VIEWS}change choose(s:State,p:Z)=s with{{h=p}};law required valid(s:State):{law};")
}
fn pending_input(law: &str, a: &str) -> archsig_input::input::InputSources {
    without_atom(fixture::input(&body(law), a, "2"), "b")
}
fn evaluate(law: &str, a: &str) -> crate::observed::ObservedEvaluation {
    let result = evaluate_observed_bytes(pending_input(law, a), &ASKS, &quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    result
}
fn field<'a>(
    result: &'a crate::observed::ObservedEvaluation,
    answer: usize,
    name: &str,
) -> &'a Json {
    let plan = result.answers[answer].outputs["plan"];
    let Some(Payload::Construction(v)) = &result.nodes[plan.0].payload else {
        panic!()
    };
    // Inspect native typed output; numeric reasoning does not consume JSON.
    let D::SharedRepair(d) = &v.data else {
        panic!()
    };
    d.source.parts[d.index]
        .wire_ref()
        .and_then(crate::observed::repair_problem::fields)
        .and_then(|f| f.get(name))
        .unwrap()
}
fn requirements(result: &crate::observed::ObservedEvaluation, answer: usize) -> usize {
    let Json::Arr(xs) = field(result, answer, "requirements") else {
        panic!()
    };
    xs.len()
}
#[test]
fn integer_decision_and_assignment_need_different_raw_readings_and_share_the_same_math() {
    let result = evaluate("s.a*s.h=s.b", "1");
    for i in [2, 3, 4, 5, 6] {
        assert_eq!(
            result.answers[i].status,
            Decision::Established,
            "{} {:?}",
            result.answers[i].id,
            result.issues
        );
    }
    assert_eq!(requirements(&result, 3), 0);
    assert_eq!(requirements(&result, 4), 1);
    assert_eq!(requirements(&result, 5), 1);
    assert_eq!(requirements(&result, 6), 0);
    assert_eq!(
        result.answers[7].status,
        Decision::Refuted,
        "共通pは全てのbには存在しない"
    );
    let a = data_for(&result, result.answers[3].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    let b = data_for(&result, result.answers[4].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    let again = data_for(&result, result.answers[6].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    assert!(Arc::ptr_eq(&a.math, &b.math));
    assert!(Arc::ptr_eq(&a.math, &again.math));
    assert!(Arc::ptr_eq(&a.affine, &b.affine));
    assert!(Arc::ptr_eq(&a.affine, &again.affine));
    let fixed = data_for(&result, result.answers[5].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    assert!(Arc::ptr_eq(&a.math.joint, &fixed.math.joint));
    assert_eq!(a.math.effects, [Effect::Image]);
    let (x, y, kind) = a.math.example(0).unwrap();
    assert_eq!(y[0].clone() - &x[0], Z::one());
    assert_eq!(kind, "no_common_assignment");
}
#[test]
fn parity_requires_the_input_for_decision_and_counterexamples_are_actual_integer_inputs() {
    let result = evaluate("s.a*s.h=s.b", "2");
    assert_eq!(result.answers[3].status, Decision::Refuted);
    for i in [4, 5, 6] {
        assert_eq!(result.answers[i].status, Decision::Established);
        assert_eq!(requirements(&result, i), 1);
    }
    let state = data_for(&result, result.answers[3].outputs["plan"])
        .source
        .integer()
        .unwrap();
    let math = &state.observation.as_ref().unwrap().math;
    assert_eq!(math.effects, [Effect::Outside]);
    let (x, y, kind) = math.example(0).unwrap();
    assert_eq!((&x[0] % 2u8), Z::zero());
    assert_ne!((&y[0] % 2u8), Z::zero());
    assert_eq!(kind, "decision_difference");
    assert!(matches!(field(&result,3,"counterexamples"),Json::Arr(xs) if xs.len()==1));
}
#[test]
fn no_input_is_repairable_is_sufficient_but_no_common_repair_is_not() {
    let result = evaluate("2*s.h=2*s.b+1", "1");
    for i in [3, 4, 5, 6] {
        assert_eq!(result.answers[i].status, Decision::Established);
        assert_eq!(requirements(&result, i), 0);
    }
    let state = data_for(&result, result.answers[4].outputs["plan"])
        .source
        .integer()
        .unwrap();
    assert!(state.observation.as_ref().unwrap().math.seed.is_none());
    assert!(result.answers[4].outputs.contains_key("solutions"));
    assert_eq!(result.answers[7].status, Decision::Refuted);
    let result = evaluate("s.h=s.b", "1");
    assert_eq!(requirements(&result, 4), 1);
    assert!(!result.answers[4].outputs.contains_key("solutions"));
}
#[test]
fn a_common_original_assignment_is_selected_applied_and_checked_without_imputing_input_values() {
    let mut asks = ASKS[..5].to_vec();
    asks.extend([
        "c=candidate($a.solutions,index=0)",
        "a1=apply($c.assignment,in=$a.solutions)",
        "ok=check(Pair.valid,on=$a1.object,s=@v/s)",
        "h=evaluate(Pair.first,on=$a1.object,s=@v/s)",
    ]);
    let result = evaluate_observed_bytes(pending_input("s.h=s.b-s.b", "1"), &asks, &quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    for a in &result.answers {
        assert_eq!(a.status, Decision::Established, "{a:?}");
    }
    assert_eq!(requirements(&result, 4), 0);
    assert!(
        matches!(&result.nodes[result.answers[8].outputs["value"].0].payload,Some(Payload::Construction(v)) if v.scalar()==Some(&Scalar::Z(Z::zero())))
    );
    let compiled = &data_for(&result, result.answers[2].outputs["problem"])
        .source
        .integer()
        .unwrap()
        .shared
        .compiled;
    assert!(
        compiled
            .fixed
            .iter()
            .all(|(f, _)| f.field.as_deref() != Some("Pair.State.b"))
    );
}
#[test]
fn observing_the_input_removes_requirements_and_restores_the_current_integer_fiber() {
    let old = evaluate("s.a*s.h=s.b", "2");
    let mut asks = ASKS[..5].to_vec();
    asks.extend([
        "c=candidate($a.solutions,index=0)",
        "ap=apply($c.assignment,in=$a.solutions)",
        "ok=check(Pair.valid,on=$ap.object,s=@v/s)",
    ]);
    let current = fixture::input(&body("s.a*s.h=s.b"), "2", "2");
    let warm = reevaluate_observed_bytes(&old, current.clone(), &asks, &quiet()).unwrap();
    let cold = evaluate_observed_bytes(current, &asks, &quiet()).unwrap();
    assert_eq!(warm.result_wire(), cold.result_wire());
    for a in &warm.answers {
        assert_eq!(a.status, Decision::Established, "{a:?}");
    }
    for i in [3, 4] {
        assert_eq!(requirements(&warm, i), 0);
    }
    let p = data_for(&warm, warm.answers[5].outputs["assignment"])
        .source
        .integer()
        .unwrap()
        .parameters
        .as_ref()
        .unwrap();
    assert_eq!(p, &[Z::one()]);
}

#[test]
fn multiple_correlated_integer_inputs_use_exact_image_and_keep_original_parameters() {
    let views = VIEWS.replace(
        "view input(s:State):Z=s.b;",
        "view input(s:State):(Z,Z)=(s.a,s.b);view onlyA(s:State):Z=s.a;",
    );
    let body = format!(
        "{views}change choose(s:State,p:Z,q:Z)=s with{{h=p,k=q}};law required valid(s:State):2*s.h+3*s.k=s.a+2*s.b and s.h-s.k=s.b;"
    );
    let input = without_atom(without_atom(fixture::input(&body, "2", "2"), "a"), "b");
    let mut asks = ASKS.to_vec();
    asks.push("partial=observe(Pair.onlyA,on=$p.problem,within=$u.value,output=decision,s=@v/s)");
    let result = evaluate_observed_bytes(input, &asks, &quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    assert_eq!(requirements(&result, 4), 2);
    assert_eq!(requirements(&result, 6), 1);
    assert_eq!(result.answers[8].status, Decision::Established);
    assert_eq!(requirements(&result, 8), 1);
    let state = data_for(&result, result.answers[4].outputs["plan"])
        .source
        .integer()
        .unwrap();
    assert_eq!(
        state.observation.as_ref().unwrap().math.effects,
        [Effect::Outside, Effect::Image]
    );
    let system = &state.shared.compiled.family.as_ref().unwrap().system;
    for a in -6..=6 {
        for b in -2..=2 {
            let x = [Z::from(a), Z::from(b)];
            let shift = integer_fiber::apply(&system.inputs, &x, &quiet()).unwrap();
            let rhs = system
                .rhs
                .iter()
                .zip(shift)
                .map(|(c, s)| c - s)
                .collect::<Vec<_>>();
            let fiber = integer_fiber::solve(&system.equations, 2, &rhs, &quiet()).unwrap();
            // 元の二式から直接 k=a/5,h=b+a/5。内部表示基底に依存しない。
            assert_eq!(fiber.particular.is_some(), a % 5 == 0);
            if let Some(p) = fiber.particular {
                assert_eq!(p, [Z::from(b + a / 5), Z::from(a / 5)]);
            }
        }
    }
}
#[test]
fn the_same_missing_field_is_one_coordinate_and_cancels_without_observation() {
    let views = VIEWS.replace(
        "view input(s:State):Z=s.b;",
        "view input(s:State):(Z,Z)=(s.b,s.b);",
    );
    let body = format!(
        "{views}change choose(s:State,p:Z,q:Z)=s with{{h=p}};law required valid(s:State):s.h=s.b-s.b;"
    );
    let result = evaluate_observed_bytes(
        without_atom(fixture::input(&body, "2", "2"), "b"),
        &ASKS,
        &quiet(),
    )
    .unwrap();
    let state = data_for(&result, result.answers[2].outputs["problem"])
        .source
        .integer()
        .unwrap();
    assert_eq!(
        state.shared.compiled.family.as_ref().unwrap().fields.len(),
        1
    );
    for i in [3, 4, 6] {
        assert_eq!(result.answers[i].status, Decision::Established);
        assert_eq!(requirements(&result, i), 0);
    }
    let set = result.answers[4].outputs["solutions"];
    let family = data_for(&result, set).source.integer().unwrap();
    let range = family.range_result.as_ref().unwrap();
    let RangeMath::Constrained { fiber, .. } = range.as_ref() else {
        panic!()
    };
    assert_eq!(
        family
            .shared
            .projection
            .as_ref()
            .unwrap()
            .free(fiber)
            .unwrap(),
        1,
        "未使用qは元Assignmentの自由度に残す"
    );
}
#[test]
fn a_missing_input_baseline_is_a_shared_coordinate_not_zero_or_an_extra_missing_fact() {
    let views = VIEWS.replace("view input(s:State):Z=s.b;", "view input(s:State):Z=s.h;");
    let body = format!(
        "{views}change choose(s:State,p:Z)=s with{{h=p}};law required valid(s:State):s.h=s.h;"
    );
    let input = without_atom(fixture::input(&body, "1", "2"), "h");
    let mut asks = ASKS.to_vec();
    asks.extend([
        "fixedset=solve($p.problem,within=$z.value)",
        "ranges=scopes($p.problem)",
        "actual=candidate($a.solutions,index=1)",
        "ap=apply($actual.assignment,in=$a.solutions)",
        "ok=check(Pair.valid,on=$ap.object,s=@v/s)",
    ]);
    let result = evaluate_observed_bytes(input, &asks, &quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    for i in [2, 3, 4, 5, 6, 7, 9, 10, 11, 12] {
        assert_eq!(
            result.answers[i].status,
            Decision::Established,
            "{} {:?}",
            result.answers[i].id,
            result.issues
        );
    }
    assert_eq!(result.answers[8].status, Decision::Refuted);
    assert_eq!(requirements(&result, 3), 0);
    assert_eq!(requirements(&result, 4), 0);
    assert_eq!(requirements(&result, 5), 0);
    let old = data_for(&result, result.answers[3].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    let fixed = data_for(&result, result.answers[5].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    assert!(Arc::ptr_eq(&old.math.joint, &fixed.math.joint));
    assert_eq!(fixed.math.effects, [Effect::Image]);
    let state = data_for(&result, result.answers[10].outputs["assignment"])
        .source
        .integer()
        .unwrap();
    assert_eq!(state.parameters.as_deref(), Some([Z::one()].as_slice()));
}
#[test]
fn integer_input_guards_use_the_same_original_change_and_preserve_their_fiber() {
    for (guard, decision_needed) in [("p+q=3", 0), ("p=1", 1), ("2*p=1", 0)] {
        let body = format!(
            "{VIEWS}change choose(s:State,p:Z,q:Z) when {guard} =s with{{h=p}};law required valid(s:State):s.h=s.b;"
        );
        let result = evaluate_observed_bytes(
            without_atom(fixture::input(&body, "1", "2"), "b"),
            &ASKS,
            &quiet(),
        )
        .unwrap();
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
            "{:?}",
            result.issues
        );
        assert_eq!(requirements(&result, 6), decision_needed);
        if guard == "2*p=1" {
            assert_eq!(requirements(&result, 4), 0);
        } else {
            assert_eq!(requirements(&result, 4), 1);
        }
    }
}
#[test]
fn input_dependent_updates_guards_and_nonaffine_laws_are_unsupported_without_poisoning_later_checks()
 {
    for (change, law) in [
        ("change choose(s:State,p:Z)=s with{h=p+s.b};", "s.h=0"),
        (
            "change choose(s:State,p:Z) when p=s.b =s with{h=p};",
            "s.h=0",
        ),
        ("change choose(s:State,p:Z)=s with{h=p};", "s.h=s.b*s.b"),
        (
            "change choose(s:State,p:Z)=s with{h=p};",
            "if s.b=0 then s.h=0 else s.h=1",
        ),
    ] {
        let body = format!(
            "{VIEWS}{change}law required valid(s:State):{law};law required known(s:State):s.h=s.h;"
        );
        let asks = [
            ASKS[2],
            "blocked=check(Pair.valid,on=$p.problem.domain.base,s=@v/s)",
            "later=check(Pair.known,s=@v/s)",
        ];
        let result = evaluate_observed_bytes(
            without_atom(fixture::input(&body, "1", "2"), "b"),
            &asks,
            &quiet(),
        )
        .unwrap();
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
            "{change} {law} {:?}",
            result.issues
        );
        assert_eq!(result.answers[0].status, Decision::Undetermined);
        assert!(
            result.answers[0]
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. })),
            "{change} {law} {:?}",
            result.issues
        );
        assert_eq!(result.answers[2].status, Decision::Established);
    }
}

#[test]
fn internal_parameters_keep_their_input_effect_and_view_bindings_share_the_compiler() {
    use crate::observed::repair_problem::integer::tests::parts;
    let body = "view all(r:Root):Set<Part> =Part[r];view inside(r:Root):Set<Part> =set {c|c in Part[r] where c.label!=\"b\"};view outside(r:Root):Set<Part> =set {c|c in Part[r] where c.label=\"b\"};view vacant(r:Root):Set<Part> =set<Part>{};view input(c:Part):Z=c.y;view uninformative(c:Part):Z=0;change choose(c:Part,p:Z,q:Z)=c with{x=p};law required valid(r:Root,c:Part):forall a in Part[r]. forall b in Part[r]. if a.label=\"a\" and b.label=\"b\" then b.x=2*a.x+b.y else true;";
    let input = without_atom(
        parts::input(
            &[("a", 0, 0, "a"), ("b", 2, 0, "b"), ("c", 0, 0, "c")],
            body,
        ),
        "y-b",
    );
    let asks = [
        "i=evaluate(Selected.inside,r=@v/root)",
        "u=evaluate(Selected.outside,r=@v/root)",
        "z=evaluate(Selected.vacant,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$i.value,inputs=Selected.input,r=@v/root,c=@v/b)",
        "d=observe(Selected.uninformative,on=$p.problem,within=$u.value,output=decision,c=@v/b)",
        "f=observe(Selected.input,on=$p.problem,within=$z.value,output=decision,c=@v/b)",
        "a=observe(Selected.input,on=$p.problem,within=$u.value,output=assignment,c=@v/b)",
        "again=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$i.value,inputs=Selected.input,r=@v/root,c=@v/b)",
    ];
    let result = evaluate_observed_bytes(input, &asks, &quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    for a in &result.answers {
        assert_eq!(a.status, Decision::Established, "{a:?}");
    }
    assert_eq!(requirements(&result, 4), 0);
    assert_eq!(requirements(&result, 5), 1);
    assert_eq!(requirements(&result, 6), 1);
    let p = data_for(&result, result.answers[3].outputs["problem"])
        .source
        .integer()
        .unwrap();
    let again = data_for(&result, result.answers[7].outputs["problem"])
        .source
        .integer()
        .unwrap();
    assert!(Arc::ptr_eq(&p.shared.compiled, &again.shared.compiled));
    let d = data_for(&result, result.answers[4].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    let f = data_for(&result, result.answers[5].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    assert!(Arc::ptr_eq(&d.math.joint, &f.math.joint));
    assert_eq!(d.math.effects, [Effect::Image]);
    assert_eq!(f.math.effects, [Effect::Outside]);
}
#[test]
fn unrelated_missing_fields_stay_missing_and_noninteger_input_fields_are_unsupported() {
    let views = VIEWS.replace("view input(s:State):Z=s.b;", "view input(s:State):Z=s.a;");
    let body = format!(
        "{views}change choose(s:State,p:Z)=s with{{h=p}};law required valid(s:State):s.h=s.b;law required known(s:State):s.h=s.h;"
    );
    let asks = [ASKS[2], "later=check(Pair.known,s=@v/s)"];
    let result = evaluate_observed_bytes(
        without_atom(fixture::input(&body, "1", "2"), "b"),
        &asks,
        &quiet(),
    )
    .unwrap();
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    assert!(result.answers[0].reasons.iter().any(|r| {
        matches!(r.kind, ReasonKind::Missing)
            && r.missing
                .iter()
                .any(|f| f.field.as_deref() == Some("Pair.State.b"))
    }));
    assert_eq!(result.answers[1].status, Decision::Established);
    use crate::observed::repair_problem::integer::tests::parts;
    let body = "view input(c:Part):Bool=c.flag;change choose(c:Part,p:Z)=c with{x=p};law required valid(c:Part):c.x=c.x;";
    let input = without_atom(parts::input(&[("a", 0, 0, "a")], body), "flag-a");
    let asks = [
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,c=@v/a)",
        "later=check(Selected.valid,c=@v/a)",
    ];
    let result = evaluate_observed_bytes(input, &asks, &quiet()).unwrap();
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
    );
    assert_eq!(result.answers[1].status, Decision::Established);
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
}

#[test]
fn observation_reobservation_reuses_linear_parts_but_rebuilds_current_rhs_and_input_family() {
    let asks = ASKS;
    let old = evaluate("2*s.h=s.b+s.a", "2");
    for (law, a, withdraw) in [
        ("2*s.h=s.b+s.a", "4", false),
        ("3*s.h=s.b+s.a", "4", false),
        ("2*s.h=s.b+s.a", "2", true),
    ] {
        let input = pending_input(law, a);
        let input = if withdraw {
            without_atom(input, "a")
        } else {
            input
        };
        let warm = reevaluate_observed_bytes(&old, input.clone(), &asks, &quiet()).unwrap();
        let cold = evaluate_observed_bytes(input, &asks, &quiet()).unwrap();
        assert_eq!(
            warm.result_wire(),
            cold.result_wire(),
            "{law} {a} {withdraw}"
        );
        assert!(
            warm.issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
            "{:?}",
            warm.issues
        );
        if withdraw {
            assert_eq!(warm.answers[2].status, Decision::Undetermined);
            assert!(warm.answers[2].reasons.iter().any(|r| {
                matches!(r.kind, ReasonKind::Missing)
                    && r.missing
                        .iter()
                        .any(|f| f.field.as_deref() == Some("Pair.State.a"))
            }));
            continue;
        }
        let prior = data_for(&old, old.answers[4].outputs["plan"])
            .source
            .integer()
            .unwrap()
            .observation
            .as_ref()
            .unwrap();
        let current = data_for(&warm, warm.answers[4].outputs["plan"])
            .source
            .integer()
            .unwrap()
            .observation
            .as_ref()
            .unwrap();
        assert_eq!(
            Arc::ptr_eq(
                &prior.math.joint.fiber.decomposition,
                &current.math.joint.fiber.decomposition
            ),
            law.starts_with("2*")
        );
        assert!(
            !Arc::ptr_eq(&prior.math, &current.math),
            "由来と現在rhsを前runのSourceから移さない"
        );
    }
}
#[test]
fn foreign_integer_and_finite_plans_and_ranges_are_rejected_without_blocking_later_requests() {
    let body = format!(
        "{VIEWS}change choose(s:State,p:Z)=s with{{h=p}};change finite(s:State,p:Bool)=s with{{h=if p then 1 else 0}};law required valid(s:State):s.h=s.h;"
    );
    let asks = [
        ASKS[0],
        ASKS[2],
        ASKS[4],
        "q=prepare(Pair.valid,using=Pair.choose,on=@v/s,inputs=Pair.input,s=@v/s)",
        "f=prepare(Pair.valid,using=Pair.finite,on=@v/s,inputs=Pair.uninformative,s=@v/s)",
        "fp=observe(Pair.uninformative,on=$f.problem,within=$u.value,output=assignment,s=@v/s)",
        "bad1=observe($a.plan,on=$q.problem,within=$u.value,output=decision)",
        "bad2=observe($fp.plan,on=$p.problem,within=$u.value,output=decision)",
        "bad3=observe($a.plan,on=$f.problem,within=$u.value,output=decision)",
        "bad4=observe(Pair.input,on=$q.problem,within=$a.plan.range,output=assignment,s=@v/s)",
        "later=check(Pair.valid,s=@v/s)",
    ];
    let result = evaluate_observed_bytes(
        without_atom(fixture::input(&body, "1", "2"), "b"),
        &asks,
        &quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    for a in &result.answers[6..10] {
        assert_eq!(a.status, Decision::Refuted, "{a:?}");
        assert!(!a.outputs.contains_key("plan"));
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
        );
    }
    assert_eq!(result.answers[10].status, Decision::Established);
}
#[test]
fn native_integer_observation_validates_its_owner_edges_and_current_scope() {
    let asks = ASKS[..7]
        .iter()
        .enumerate()
        .filter_map(|(i, ask)| (i != 3).then_some(*ask))
        .collect::<Vec<_>>();
    let result =
        evaluate_observed_bytes(pending_input("s.a*s.h=s.b", "2"), &asks, &quiet()).unwrap();
    let c = quiet();
    let rebuild = |nodes: &[Node]| -> Result<(), ValidationFailure> {
        let env = Environment::with_requests(
            result.prepared.inputs(),
            result.prepared.requests().requests(),
            &c,
        )?;
        let mut graph = Graph::new(&c);
        graph.requests = result.prepared.requests().requests().to_vec();
        graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
        for (i, node) in nodes.iter().enumerate() {
            graph.active = result.contexts[i];
            env.validate(&graph, node)?;
            graph.push(node.clone())?;
        }
        Ok(())
    };
    rebuild(&result.nodes).unwrap();
    let plan = result.answers[3].outputs["plan"];
    let mut nodes = result.nodes.clone();
    nodes[plan.0].arguments.pop();
    assert!(rebuild(&nodes).is_err());
    let mut nodes = result.nodes.clone();
    nodes[plan.0].scope.completions = false;
    assert!(rebuild(&nodes).is_err());
    let mut nodes = result.nodes.clone();
    nodes[plan.0].scope.readings.clear();
    assert!(rebuild(&nodes).is_err());
}
#[test]
fn interrupted_integer_observations_keep_prior_answers_and_never_publish_partial_plans_or_cache() {
    use std::{cell::Cell, rc::Rc};
    let input = pending_input("s.a*s.h=s.b", "2");
    let old = evaluate_observed_bytes(input.clone(), &ASKS, &quiet()).unwrap();
    let before = old.result_wire();
    let run = |asks: &[&str], stop: Option<usize>| {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let control = Control::new(move |point| {
            if matches!(
                point,
                Checkpoint::PrimitiveValuation | Checkpoint::NativeResultNode
            ) {
                seen.set(seen.get() + 1);
                if stop == Some(seen.get()) {
                    return Some(archsig_common::control::Signal::Term);
                }
            }
            None
        });
        let result = reevaluate_observed_bytes(&old, input.clone(), asks, &control).unwrap();
        (result, count.get())
    };
    for i in [2, 3, 4, 5] {
        let (_, prior) = run(&ASKS[..i], None);
        let (complete, total) = run(&ASKS[..=i], None);
        assert!(total > prior);
        for at in [prior + 1, prior + (total - prior).div_ceil(2)] {
            let (result, _) = run(&ASKS[..=i], Some(at));
            assert_eq!(result.status(), "interrupted");
            for (a, b) in result.answers[..i].iter().zip(&complete.answers[..i]) {
                assert_eq!(a.status, b.status);
                assert_eq!(a.outputs, b.outputs);
            }
            if result.answers[i].outputs.is_empty() {
                assert_eq!(result.answers[i].status, Decision::Undetermined);
            } else {
                // commit後の停止では完成した現在回答も保持する。部分planは許さない。
                assert_eq!(result.answers[i].outputs, complete.answers[i].outputs);
                assert_eq!(result.answers[i].status, complete.answers[i].status);
                assert_eq!(result.answers[i].scope, complete.answers[i].scope);
            }
            assert!(result.integer_cache.is_empty());
            assert!(
                result
                    .issues
                    .iter()
                    .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
                "{:?}",
                result.issues
            );
        }
    }
    assert_eq!(old.result_wire(), before);
}

#[test]
fn a_refuted_assignment_plan_remains_a_typed_input_for_the_decision_question() {
    let mut asks = ASKS[..5].to_vec();
    asks.extend([
        "insufficient=observe(Pair.uninformative,on=$p.problem,within=$u.value,output=assignment,s=@v/s)",
        "decision=observe($insufficient.plan,on=$p.problem,within=$u.value,output=decision)",
        "assignment=observe($d.plan,on=$p.problem,within=$u.value,output=assignment)",
    ]);
    let result = evaluate_observed_bytes(pending_input("s.h=s.b", "1"), &asks, &quiet()).unwrap();
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    assert_eq!(result.answers[5].status, Decision::Refuted);
    assert_eq!(result.answers[6].status, Decision::Established);
    assert_eq!(result.answers[7].status, Decision::Refuted);
    for i in [5, 6, 7] {
        assert_eq!(requirements(&result, i), 0);
    }
    let a = data_for(&result, result.answers[5].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    let d = data_for(&result, result.answers[6].outputs["plan"])
        .source
        .integer()
        .unwrap()
        .observation
        .as_ref()
        .unwrap();
    assert!(Arc::ptr_eq(&a.math, &d.math));
}

#[test]
fn repeated_common_observations_and_solve_share_the_native_solution_and_hidden_embedding() {
    let views = VIEWS;
    let body = format!(
        "{views}change choose(s:State,p:Z,q:Z)=s with{{h=p}};law required valid(s:State):s.h=s.b-s.b;"
    );
    let asks = [
        ASKS[0],
        ASKS[2],
        ASKS[4],
        "b=observe(Pair.input,on=$p.problem,within=$u.value,output=assignment,s=@v/s)",
        "again=observe($a.plan,on=$p.problem,within=$u.value,output=assignment)",
        "s=solve($p.problem,within=$u.value)",
        "c=candidate($again.solutions,index=3)",
        "ap=apply($c.assignment,in=$s.solutions)",
        "ok=check(Pair.valid,on=$ap.object,s=@v/s)",
    ];
    let result = evaluate_observed_bytes(
        without_atom(fixture::input(&body, "1", "2"), "b"),
        &asks,
        &quiet(),
    )
    .unwrap();
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    for a in &result.answers {
        assert_eq!(a.status, Decision::Established, "{a:?}");
    }
    let set = result.answers[2].outputs["solutions"];
    for i in [3, 4, 5] {
        assert_eq!(result.answers[i].outputs["solutions"], set);
    }
    let first = data_for(&result, result.answers[2].outputs["plan"])
        .source
        .integer()
        .unwrap();
    for i in [3, 4] {
        let state = data_for(&result, result.answers[i].outputs["plan"])
            .source
            .integer()
            .unwrap();
        let source = &data_for(&result, result.answers[i].outputs["plan"]).source;
        assert!(
            source.parts.iter().all(|part| !matches!(
                part.ty,
                NodeType::ModuleMap(_, _) | NodeType::Construction(T::SolutionSet)
            )),
            "反復回答に全核や全解の別表示を生成しない"
        );
        assert!(Arc::ptr_eq(
            first.range_result.as_ref().unwrap(),
            state.range_result.as_ref().unwrap()
        ));
        assert!(state.public_model.is_none(), "新しい全核表示を保持しない");
    }
    let parameters = data_for(&result, result.answers[6].outputs["assignment"])
        .source
        .integer()
        .unwrap()
        .parameters
        .as_ref()
        .unwrap();
    assert_eq!(parameters.len(), 2);
    assert_eq!(parameters[0], Z::zero());
    assert_eq!(parameters[1], Z::from(2));
}
#[test]
fn integer_problem_and_input_domain_publish_the_same_explicit_bindings() {
    let result = evaluate("s.h=s.b", "1");
    let problem = result.answers[2].outputs["problem"];
    let state = data_for(&result, problem).source.integer().unwrap();
    let input = state.shared.input_domain.unwrap().domain;
    let problem = data_for(&result, problem);
    let domain = data_for(&result, input);
    let problem = crate::observed::repair_problem::fields(
        problem.source.parts[problem.index].wire_ref().unwrap(),
    )
    .unwrap();
    let domain = crate::observed::repair_problem::fields(
        domain.source.parts[domain.index].wire_ref().unwrap(),
    )
    .unwrap();
    let inputs = crate::observed::repair_problem::fields(&problem["inputs"]).unwrap();
    assert_eq!(inputs["bindings"], domain["bindings"]);
    let Json::Arr(bindings) = &inputs["bindings"] else {
        panic!()
    };
    assert_eq!(bindings.len(), 1);
    let binding = crate::observed::repair_problem::fields(&bindings[0]).unwrap();
    assert_eq!(binding["name"], Json::str("s"));
}
