use super::*;
use crate::observed::{evaluate_observed_bytes, reevaluate_observed_bytes};
use archsig_common::control::quiet;
#[allow(dead_code)]
pub(super) mod fixture {
    include!("../../../../../../tests/common/integer_reobservation_data.rs");
}
const BODY: &str = "view all(s:State):Set<State> =set<State>{s};view vacant(s:State):Set<State> =set<State>{};view first(s:State):Z=s.h;change choose(s:State,p:Z)=s with{h=p};law required valid(s:State):s.a*s.h=s.b;";
const ASKS: [&str; 12] = [
    "u=evaluate(Pair.all,s=@v/s)",
    "z=evaluate(Pair.vacant,s=@v/s)",
    "p=prepare(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
    "lo=solve($p.problem,within=$z.value)",
    "hi=solve($p.problem,within=$u.value)",
    "ranges=scopes($p.problem)",
    "again=solve($p.problem,within=$ranges.ranges[0])",
    "c=candidate($hi.solutions,index=0)",
    "a=apply($c.assignment,in=$hi.solutions)",
    "ok=check(Pair.valid,on=$a.object,s=@v/s)",
    "h=evaluate(Pair.first,on=$a.object,s=@v/s)",
    "bad=candidate($hi.solutions,index=1)",
];
#[test]
fn integer_problem_ranges_candidate_and_applied_original_law_form_one_loop() {
    let c = quiet();
    let result = evaluate_observed_bytes(fixture::input(BODY, "2", "2"), &ASKS, &c)
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    assert_eq!(result.answers[3].status, Decision::Refuted);
    for index in [2, 4, 5, 6, 7, 8, 9, 10] {
        assert_eq!(
            result.answers[index].status,
            Decision::Established,
            "{}: {:?}",
            result.answers[index].id,
            result.issues
        );
    }
    assert_eq!(result.answers[11].status, Decision::Refuted);
    let value = result.answers[10].outputs["value"];
    assert_eq!(
        result.nodes[value.0]
            .payload
            .as_ref()
            .and_then(|p| match p {
                Payload::Scalar(s) => Some(s),
                Payload::Construction(v) => v.scalar(),
                _ => None,
            }),
        Some(&Scalar::Z(1.into()))
    );
    let d = data_for(&result, result.answers[4].outputs["solutions"]);
    let p = data_for(&result, result.answers[2].outputs["problem"]);
    assert!(Arc::ptr_eq(
        &d.source.integer().unwrap().shared,
        &p.source.integer().unwrap().shared
    ));
    let original = result.answers[7].outputs["assignment"];
    let source = data_for(&result, original);
    assert_eq!(
        source.source.integer().unwrap().parameters.as_deref(),
        Some([Z::from(1)].as_slice())
    );
}
pub(super) fn data_for(result: &crate::observed::ObservedEvaluation, at: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &result.nodes[at.0].payload else {
        panic!()
    };
    let D::SharedRepair(d) = &v.data else {
        panic!()
    };
    d
}
#[allow(dead_code)]
#[path = "../../../../../../tests/common/integer_repair_problem_data.rs"]
pub(super) mod parts;
const PART_BODY: &str = "view all(r:Root):Set<Part> =Part[r];view inside(r:Root):Set<Part> =set {c|c in Part[r] where c.label!=\"b\"};view vacant(r:Root):Set<Part> =set {c|c in Part[r] where false};view outside(r:Root):Set<Part> =set {c|c in Part[r] where c.label=\"b\"};view read(c:Part):Z=c.x;change choose(c:Part,p:Z,q:Z)=c with{x=p};law required valid(r:Root):forall a in Part[r]. forall b in Part[r]. if a.label=\"a\" and b.label=\"b\" then b.x=2*a.x else true;";
fn part_input(b: i64) -> archsig_input::input::InputSources {
    parts::input(
        &[("a", 0, 0, "a"), ("b", b, 0, "b"), ("c", 0, 0, "c")],
        PART_BODY,
    )
}
fn part_asks() -> Vec<&'static str> {
    vec![
        "u=evaluate(Selected.all,r=@v/root)",
        "i=evaluate(Selected.inside,r=@v/root)",
        "z=evaluate(Selected.vacant,r=@v/root)",
        "b=evaluate(Selected.outside,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$i.value,r=@v/root)",
        "lo=solve($p.problem,within=$z.value)",
        "hi=solve($p.problem,within=$b.value)",
        "ranges=scopes($p.problem)",
        "c=candidate($hi.solutions,index=2)",
        "a=apply($c.assignment,in=$hi.solutions)",
        "ok=check(Selected.valid,on=$a.object,r=@v/root)",
        "again=solve($p.problem,within=$b.value)",
        "next=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$i.value,r=@v/root)",
    ]
}
#[test]
fn internal_integer_elimination_retains_the_shared_image_and_every_hidden_assignment() {
    let c = quiet();
    let asks = part_asks();
    let before = crate::observed::environment::repair_problem::integer::generated();
    let result = evaluate_observed_bytes(part_input(1), &asks, &c)
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    assert_eq!(result.answers[5].status, Decision::Refuted);
    for i in [4, 6, 7, 8, 9, 10, 11, 12] {
        assert_eq!(
            result.answers[i].status,
            Decision::Established,
            "{}: {:?}",
            result.answers[i].id,
            result.issues
        );
    }
    assert_eq!(
        crate::observed::environment::repair_problem::integer::generated() - before,
        1,
        "元式の生成は範囲とprepareの反復で増えない"
    );
    let p = data_for(&result, result.answers[4].outputs["problem"])
        .source
        .integer()
        .unwrap();
    let again = data_for(&result, result.answers[12].outputs["problem"])
        .source
        .integer()
        .unwrap();
    assert!(Arc::ptr_eq(&p.shared.compiled, &again.shared.compiled));
    assert!(Arc::ptr_eq(
        p.shared.projection.as_ref().unwrap(),
        again.shared.projection.as_ref().unwrap()
    ));
    assert_eq!(
        result.answers[6].outputs["solutions"], result.answers[11].outputs["solutions"],
        "同じ所有者・入力の公開表示を参照共有する"
    );
    let state = data_for(&result, result.answers[6].outputs["solutions"])
        .source
        .integer()
        .unwrap();
    let projection = state.shared.projection.as_ref().unwrap();
    assert_eq!(projection.visible(), 1);
    assert_eq!(projection.hidden(), 4);
    let RangeMath::Constrained { fiber, .. } = state.range_result.as_ref().unwrap().as_ref() else {
        panic!()
    };
    assert_eq!(projection.free(fiber).unwrap(), 5);
    let origin = state.shared.compiled.linear.particular.as_ref().unwrap();
    let kernel = &state.shared.compiled.linear.kernel;
    let points = (0u32..1024)
        .map(|i| {
            projection
                .candidate(origin, kernel, fiber, &i.into(), &c)
                .unwrap()
                .unwrap()
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(points.len(), 1024);
    assert!(points.iter().all(|p| p[2] == 2 * &p[0]));
    for q0 in -1..=1 {
        for q1 in -1..=1 {
            for p2 in -1..=1 {
                for q2 in -1..=1 {
                    assert!(points.contains(&vec![
                        0.into(),
                        q0.into(),
                        0.into(),
                        q1.into(),
                        p2.into(),
                        q2.into()
                    ]));
                }
            }
        }
    }
}
#[test]
fn fixed_integer_output_keeps_the_baseline_and_all_unused_parameter_fibers() {
    let c = quiet();
    let asks = part_asks();
    let result = evaluate_observed_bytes(part_input(2), &asks, &c)
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    assert_eq!(result.answers[5].status, Decision::Established);
    let state = data_for(&result, result.answers[5].outputs["solutions"])
        .source
        .integer()
        .unwrap();
    let projection = state.shared.projection.as_ref().unwrap();
    let RangeMath::Constrained { fiber, .. } = state.range_result.as_ref().unwrap().as_ref() else {
        panic!()
    };
    assert_eq!(projection.free(fiber).unwrap(), 4);
    let origin = state.shared.compiled.linear.particular.as_ref().unwrap();
    for i in 0..10u32 {
        let p = projection
            .candidate(
                origin,
                &state.shared.compiled.linear.kernel,
                fiber,
                &i.into(),
                &c,
            )
            .unwrap()
            .unwrap();
        assert_eq!(p[0], Z::from(1));
        assert_eq!(p[2], Z::from(2), "範囲外のparameterを零へ固定しない");
    }
}
#[test]
fn integer_problem_reobservation_reuses_linear_parts_with_current_rhs_and_provenance() {
    use crate::observed::integer_fiber as arithmetic;
    let c = quiet();
    let asks = part_asks();
    let old = evaluate_observed_bytes(part_input(1), &asks, &c).unwrap();
    let inputs = || {
        let input = part_input(2);
        archsig_input::input::InputSources::from_bytes(
            input
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            input.law().bytes().to_vec(),
            std::str::from_utf8(input.archmap().bytes())
                .unwrap()
                .replace("\"id\":\"x-b\"", "\"id\":\"current-x-b\"")
                .replace("specification", "proposed")
                .replace("Integer repair fixture", "Current integer observation")
                .into_bytes(),
        )
    };
    let before = arithmetic::generated();
    let current = reevaluate_observed_bytes(&old, inputs(), &asks, &c).unwrap();
    let warm = arithmetic::generated() - before;
    let before = arithmetic::generated();
    let cold = evaluate_observed_bytes(inputs(), &asks, &c).unwrap();
    assert!(warm < arithmetic::generated() - before);
    assert_eq!(current.result_wire(), cold.result_wire());
    assert_eq!(current.answers[5].status, Decision::Established);
    assert!(
        old.integer_cache
            .iter()
            .any(|a| current.integer_cache.iter().any(|b| Arc::ptr_eq(a, b)))
    );
    assert!(
        current
            .nodes
            .iter()
            .flat_map(|n| n.support.materialize_for_test().into_iter())
            .any(|f| f.atom.as_deref() == Some("current-x-b"))
    );
    assert!(
        !current
            .nodes
            .iter()
            .flat_map(|n| n.support.materialize_for_test().into_iter())
            .any(|f| f.atom.as_deref() == Some("x-b"))
    );
    for node in &current.nodes {
        if let Some(Payload::Construction(v)) = &node.payload {
            assert_eq!(
                v.witness.inputs().sources(),
                current.prepared.inputs().sources()
            );
        }
    }
    let changed = parts::input(
        &[("a", 0, 0, "a"), ("b", 2, 0, "b"), ("c", 0, 0, "c")],
        &PART_BODY.replace("x=p", "x=2*p"),
    );
    let current = reevaluate_observed_bytes(&old, changed.clone(), &asks, &c).unwrap();
    let cold = evaluate_observed_bytes(changed, &asks, &c).unwrap();
    assert_eq!(current.result_wire(), cold.result_wire());
    assert_eq!(current.answers[5].status, Decision::Refuted);
}
#[test]
fn different_integer_range_owners_and_original_candidate_domains_are_rejected() {
    let c = quiet();
    let body = format!("{PART_BODY}change other(c:Part,p:Z,q:Z)=c with{{x=p}};");
    let input = parts::input(
        &[("a", 0, 0, "a"), ("b", 1, 0, "b"), ("c", 0, 0, "c")],
        &body,
    );
    let asks = [
        "i=evaluate(Selected.inside,r=@v/root)",
        "b=evaluate(Selected.outside,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$i.value,r=@v/root)",
        "q=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$i.value,r=@v/root)",
        "r=scopes($p.problem)",
        "bad=solve($q.problem,within=$r.ranges[0])",
        "s=solve($p.problem,within=$b.value)",
        "c=candidate($s.solutions,index=0)",
        "other=prepare(Selected.valid,using=Selected.other,on=@v/root,internal=$i.value,r=@v/root)",
        "t=solve($other.problem,within=$b.value)",
        "no=apply($c.assignment,in=$t.solutions)",
    ];
    let result = evaluate_observed_bytes(input, &asks, &c).unwrap();
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    assert_eq!(result.answers[5].status, Decision::Refuted);
    assert!(!result.answers[5].outputs.contains_key("range"));
    assert_eq!(result.answers[10].status, Decision::Refuted);
    assert!(!result.answers[10].outputs.contains_key("object"));
}
#[test]
fn integer_ranges_transfer_original_values_across_changed_display_bases() {
    let c = quiet();
    let prefix = PART_BODY
        .split("law required valid")
        .next()
        .unwrap()
        .replace("x=p", "x=p,y=q");
    let body = format!(
        "{prefix}law required valid(r:Root):(forall b in Part[r]. if b.label=\"b\" then b.x=2*b.link.x else true) and (forall a in Part[r]. if a.label=\"a\" then a.link.y=a.x+a.link.x else true);view second(c:Part):Z=c.y;view only_a(r:Root):Set<Part> =set {{c|c in Part[r] where c.label=\"a\"}};view only_c(r:Root):Set<Part> =set {{c|c in Part[r] where c.label=\"c\"}};"
    );
    let input = parts::input(
        &[("a", 0, 0, "c"), ("b", 2, 0, "a"), ("c", 0, 0, "c")],
        &body,
    );
    let asks = [
        "i=evaluate(Selected.inside,r=@v/root)",
        "z=evaluate(Selected.vacant,r=@v/root)",
        "single=evaluate(Selected.only_a,r=@v/root)",
        "out=evaluate(Selected.only_c,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$i.value,r=@v/root)",
        "q=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$single.value,r=@v/root)",
        "s=solve($p.problem,within=$z.value)",
        "t=solve($q.problem,within=$out.value)",
        "c=candidate($s.solutions,index=1)",
        "a=apply($c.assignment,in=$t.solutions)",
        "ok=check(Selected.valid,on=$a.object,r=@v/root)",
        "a0=evaluate(Selected.read,on=$a.object,c=@v/a)",
        "a1=evaluate(Selected.second,on=$a.object,c=@v/a)",
        "b0=evaluate(Selected.read,on=$a.object,c=@v/b)",
        "b1=evaluate(Selected.second,on=$a.object,c=@v/b)",
        "c0=evaluate(Selected.read,on=$a.object,c=@v/c)",
        "c1=evaluate(Selected.second,on=$a.object,c=@v/c)",
    ];
    let result =
        evaluate_observed_bytes(input, &asks, &c).unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    assert_eq!(
        result.answers[10].status,
        Decision::Established,
        "{:?}",
        result.issues
    );
    let p = data_for(&result, result.answers[6].outputs["solutions"])
        .source
        .integer()
        .unwrap();
    let q = data_for(&result, result.answers[7].outputs["solutions"])
        .source
        .integer()
        .unwrap();
    assert!(Arc::ptr_eq(&p.shared.compiled, &q.shared.compiled));
    let RangeMath::Constrained { fiber: pf, .. } = p.range_result.as_ref().unwrap().as_ref() else {
        panic!()
    };
    let RangeMath::Constrained { fiber: qf, .. } = q.range_result.as_ref().unwrap().as_ref() else {
        panic!()
    };
    let pk = p
        .shared
        .projection
        .as_ref()
        .unwrap()
        .kernel(&p.shared.compiled.linear.kernel, pf, &c)
        .unwrap();
    let qk = q
        .shared
        .projection
        .as_ref()
        .unwrap()
        .kernel(&q.shared.compiled.linear.kernel, qf, &c)
        .unwrap();
    assert_ne!(pk, qk, "公開する元座標の表示基底が実際に異なる");
    let values = data_for(&result, result.answers[8].outputs["assignment"])
        .source
        .integer()
        .unwrap()
        .parameters
        .as_ref()
        .unwrap();
    for (index, value) in (11..17).zip(values) {
        let at = result.answers[index].outputs["value"];
        let scalar = match &result.nodes[at.0].payload {
            Some(Payload::Scalar(s)) => s,
            Some(Payload::Construction(v)) => v.scalar().unwrap(),
            _ => panic!(),
        };
        assert_eq!(scalar, &Scalar::Z(value.clone()));
    }
}

#[test]
fn integer_existence_and_scope_search_publish_no_unrequested_fibers_or_candidates() {
    let c = quiet();
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root)",
        "s=solve($p.problem,within=$u.value,mode=existence)",
        "ranges=scopes($p.problem)",
    ];
    let before = evaluate_observed_bytes(part_input(1), &asks[..2], &c).unwrap();
    let result = evaluate_observed_bytes(part_input(1), &asks, &c).unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert!(!result.answers[2].outputs.contains_key("solutions"));
    for node in &result.nodes {
        assert!(
            !matches!(
                node.ty,
                NodeType::Construction(T::SolutionSet | T::Assignment | T::Selection)
                    | NodeType::ModuleMap(..)
            ),
            "{:?}",
            node.ty
        );
    }
    // scopesの一時行列を履歴cacheに蓄積しない。solveの明示範囲だけは現在の入力部品になる。
    let only_solve = evaluate_observed_bytes(part_input(1), &asks[..3], &c).unwrap();
    assert_eq!(result.integer_cache.len(), only_solve.integer_cache.len());
    assert!(before.integer_cache.len() <= result.integer_cache.len());
}
pub(super) fn without_atom(
    input: archsig_input::input::InputSources,
    id: &str,
) -> archsig_input::input::InputSources {
    let mut map = std::str::from_utf8(input.archmap().bytes())
        .unwrap()
        .to_owned();
    let start = map.find(&format!(r#"{{"id":"{id}","#)).unwrap();
    let end = start + map[start..].find('}').unwrap() + 1;
    if map.as_bytes().get(end) == Some(&b',') {
        map.replace_range(start..end + 1, "");
    } else {
        assert_eq!(map.as_bytes().get(start - 1), Some(&b','));
        map.replace_range(start - 1..end, "");
    }
    archsig_input::input::InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        input.law().bytes().to_vec(),
        map.into_bytes(),
    )
}
#[test]
fn integer_missing_fixed_outputs_are_pending_without_imputing_zero_or_requiring_internal_baselines()
{
    let c = quiet();
    let asks = part_asks();
    let internal_missing = without_atom(part_input(2), "x-a");
    let result = evaluate_observed_bytes(internal_missing, &asks, &c).unwrap();
    for i in [4, 5, 6, 7, 8, 9, 10] {
        assert_eq!(
            result.answers[i].status,
            Decision::Established,
            "{} {:?}",
            result.answers[i].id,
            result.issues
        );
    }
    let fixed_missing = without_atom(part_input(2), "x-b");
    let result = evaluate_observed_bytes(fixed_missing, &asks, &c).unwrap();
    for i in [4, 6, 8, 9, 10] {
        assert_eq!(
            result.answers[i].status,
            Decision::Established,
            "{} {:?}",
            result.answers[i].id,
            result.issues
        );
    }
    assert_eq!(result.answers[5].status, Decision::Undetermined);
    assert_eq!(result.answers[7].status, Decision::Undetermined);
    assert!(result.issues.iter().any(|r| {
        matches!(r.kind, ReasonKind::Missing)
            && r.missing
                .iter()
                .any(|f| f.subject == "b" && f.field.as_deref() == Some("Pattern.Part.x"))
    }));
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
fn empty_integer_instance_family_has_one_empty_assignment_and_one_minimal_range() {
    let c = quiet();
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "ranges=scopes($p.problem)",
        "c=candidate($s.solutions,index=0)",
        "bad=candidate($s.solutions,index=1)",
        "a=apply($c.assignment,in=$s.solutions)",
        "ok=check(Selected.valid,on=$a.object,r=@v/root)",
    ];
    let result = evaluate_observed_bytes(parts::input(&[], PART_BODY), &asks, &c)
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    for i in [0, 1, 2, 3, 4, 6, 7] {
        assert_eq!(
            result.answers[i].status,
            Decision::Established,
            "{} {:?}",
            result.answers[i].id,
            result.issues
        );
    }
    assert_eq!(result.answers[5].status, Decision::Refuted);
    let state = data_for(&result, result.answers[4].outputs["assignment"])
        .source
        .integer()
        .unwrap();
    assert_eq!(state.parameters.as_deref(), Some([].as_slice()));
    assert_eq!(
        data_for(&result, result.answers[3].outputs["ranges"])
            .source
            .ranges
            .len(),
        1
    );
}
#[test]
fn affine_quotient_uses_the_integer_range_fiber_in_original_parameter_coordinates() {
    let c = quiet();
    let asks = [
        "z=evaluate(Selected.vacant,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root)",
        "s=solve($p.problem,within=$z.value)",
        "q=quotient(Selected.read,on=$s.solutions,c=@v/b)",
        "all=quotient(Selected.read,on=$p.problem.domain,c=@v/b)",
    ];
    let result = evaluate_observed_bytes(
        parts::input(
            &[("a", 1, 0, "a"), ("b", 2, 0, "b"), ("c", 0, 0, "c")],
            PART_BODY,
        ),
        &asks,
        &c,
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    for answer in &result.answers {
        assert_eq!(
            answer.status,
            Decision::Established,
            "{} {:?}",
            answer.id,
            result.issues
        );
    }
    let rank = |index: usize| {
        let at = result.answers[index].outputs["quotient"];
        let Some(Payload::Construction(value)) = &result.nodes[at.0].payload else {
            panic!()
        };
        let wire = value.wire();
        let record = fields(&wire).unwrap();
        let representation = fields(&record["representation"]).unwrap();
        assert_eq!(representation["kind"], Json::str("affine"));
        let image = value
            .arguments()
            .iter()
            .copied()
            .find(|r| r.wire() == representation["image"])
            .unwrap();
        let Some(Payload::Construction(module)) = &result.nodes[image.0].payload else {
            panic!()
        };
        let wire = module.wire();
        fields(&wire).unwrap()["free_rank"].clone()
    };
    assert_eq!(rank(3), Json::Nat(0), "範囲外b.xは現在値2へ固定される");
    assert_eq!(rank(4), Json::Nat(1), "元候補域ではb.xは任意整数");
}

#[test]
fn legacy_integer_solutions_and_original_repairs_join_the_same_candidate_apply_path() {
    let c = quiet();
    let asks = [
        "u=evaluate(Pair.all,s=@v/s)",
        "p=prepare(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "s=solve($p.problem,within=$u.value)",
        "old=solve(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "repair=repair(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "c=candidate($old.solutions,index=0)",
        "a=apply($c.assignment,in=$s.solutions)",
        "back=apply($c.assignment,in=$old.solutions)",
        "other=apply($repair.repair.parameters,in=$s.solutions)",
        "ok=check(Pair.valid,on=$a.object,s=@v/s)",
        "next=candidate($old.solutions,index=0)",
    ];
    let result = evaluate_observed_bytes(fixture::input(BODY, "2", "2"), &asks, &c)
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    for a in &result.answers {
        assert_eq!(
            a.status,
            Decision::Established,
            "{} {:?}",
            a.id,
            result.issues
        );
    }
    let first = data_for(&result, result.answers[5].outputs["assignment"])
        .source
        .integer()
        .unwrap();
    let next = data_for(&result, result.answers[10].outputs["assignment"])
        .source
        .integer()
        .unwrap();
    assert!(Arc::ptr_eq(&first.shared, &next.shared));
}

#[test]
fn integer_minimal_ranges_are_complete_including_overlapping_ranges() {
    let c = quiet();
    let prefix = PART_BODY.split("law required valid").next().unwrap();
    let body = format!(
        "{prefix}law required valid(r:Root):forall a in Part[r]. forall b in Part[r]. if a.label=\"a\" and b.label=\"b\" then a.x+b.x=1 else true;"
    );
    let asks = [
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root)",
        "r=scopes($p.problem)",
    ];
    let result = evaluate_observed_bytes(
        parts::input(
            &[("a", 0, 0, "a"), ("b", 0, 0, "b"), ("c", 0, 0, "c")],
            &body,
        ),
        &asks,
        &c,
    )
    .unwrap();
    assert_eq!(
        result.answers[1].status,
        Decision::Established,
        "{:?}",
        result.issues
    );
    let ranges = data_for(&result, result.answers[1].outputs["ranges"]);
    assert_eq!(
        ranges.source.ranges.values().cloned().collect::<Vec<_>>(),
        vec![vec![true, false, false], vec![false, true, false]]
    );
    let shared = &ranges.source.integer().unwrap().shared;
    for bits in 0..8 {
        let enabled = (0..3).map(|j| bits & (1 << j) != 0).collect::<Vec<_>>();
        let math = resolve_range_for_test(shared, &enabled, &c);
        assert_eq!(math, enabled[0] || enabled[1]);
    }
    let body = format!(
        "{prefix}law required valid(r:Root):(forall a in Part[r]. forall c in Part[r]. if a.label=\"a\" and c.label=\"c\" then a.x+c.x=1 else true) and (forall b in Part[r]. forall c in Part[r]. if b.label=\"b\" and c.label=\"c\" then b.x+c.x=2 else true);"
    );
    let result = evaluate_observed_bytes(
        parts::input(
            &[("a", 0, 0, "a"), ("b", 0, 0, "b"), ("c", 0, 0, "c")],
            &body,
        ),
        &asks,
        &c,
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_eq!(
        result.answers[1].status,
        Decision::Established,
        "{:?}",
        result.issues
    );
    let ranges = data_for(&result, result.answers[1].outputs["ranges"]);
    assert_eq!(
        ranges.source.ranges.values().cloned().collect::<Vec<_>>(),
        vec![
            vec![true, true, false],
            vec![true, false, true],
            vec![false, true, true]
        ],
        "三つの包含極小範囲は重なりを持つ"
    );
}
fn resolve_range_for_test(shared: &Shared, enabled: &[bool], c: &Control) -> bool {
    let Some(projection) = &shared.projection else {
        return false;
    };
    let fixed = fixed(shared, enabled, c).unwrap().unwrap();
    let (matrix, rhs) = projection.constraints(&fixed, c).unwrap();
    integer_fiber::solve(&matrix, projection.visible(), &rhs, c)
        .unwrap()
        .particular
        .is_some()
}
#[test]
fn huge_integer_ordinal_selects_one_original_assignment_without_erasing_nonuniqueness() {
    let c = quiet();
    let body = BODY.replace("p:Z)", "p:Z,q:Z)");
    let asks = [
        "u=evaluate(Pair.all,s=@v/s)",
        "p=prepare(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "s=solve($p.problem,within=$u.value)",
        "c=candidate($s.solutions,index=18446744073709551617)",
        "a=apply($c.assignment,in=$s.solutions)",
        "ok=check(Pair.valid,on=$a.object,s=@v/s)",
        "old=repair(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
    ];
    let result = evaluate_observed_bytes(fixture::input(&body, "2", "2"), &asks, &c).unwrap();
    for a in &result.answers[..6] {
        assert_eq!(
            a.status,
            Decision::Established,
            "{} {:?}",
            a.id,
            result.issues
        );
    }
    assert_eq!(result.answers[6].status, Decision::Refuted);
    assert!(!result.answers[6].outputs.contains_key("repair"));
    let state = data_for(&result, result.answers[3].outputs["assignment"])
        .source
        .integer()
        .unwrap();
    assert_eq!(
        state.parameters.as_deref(),
        Some([Z::from(1), Z::from(9223372036854775809u64)].as_slice())
    );
}

#[test]
fn interrupted_integer_stages_keep_prior_answers_and_publish_no_partial_choice_or_cache() {
    use std::{cell::Cell, rc::Rc};
    let c = quiet();
    let old = evaluate_observed_bytes(fixture::input(BODY, "2", "2"), &ASKS, &c).unwrap();
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
        let result =
            reevaluate_observed_bytes(&old, fixture::input(BODY, "2", "2"), asks, &control)
                .unwrap();
        (result, count.get())
    };
    for index in [2, 4, 5, 7, 8] {
        let (_, prior) = run(&ASKS[..index], None);
        let (complete, total) = run(&ASKS[..=index], None);
        assert_eq!(complete.status(), "complete");
        assert!(total > prior);
        for at in [prior + 1, prior + (total - prior).div_ceil(2)] {
            let (result, _) = run(&ASKS[..=index], Some(at));
            assert_eq!(
                result.status(),
                "interrupted",
                "stage {index} checkpoint {at}"
            );
            for (a, b) in result.answers[..index]
                .iter()
                .zip(&complete.answers[..index])
            {
                assert_eq!(a.status, b.status);
                assert_eq!(a.outputs, b.outputs);
            }
            assert_eq!(result.answers[index].status, Decision::Undetermined);
            assert!(result.answers[index].outputs.is_empty());
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
    assert_eq!(
        old.result_wire(),
        before,
        "停止した再観測は先行結果を書き換えない"
    );
}

#[test]
fn integer_native_validation_rejects_changed_owner_edges_metadata_and_request() {
    let c = quiet();
    let asks = ASKS[..9]
        .iter()
        .enumerate()
        .filter_map(|(i, ask)| (i != 3).then_some(*ask))
        .collect::<Vec<_>>();
    let result = evaluate_observed_bytes(fixture::input(BODY, "2", "2"), &asks, &c).unwrap();
    let rebuild = |nodes: &[Node], requests: Vec<Request>| -> Result<(), ValidationFailure> {
        let env = Environment::with_requests(
            result.prepared.inputs(),
            result.prepared.requests().requests(),
            &c,
        )?;
        let mut graph = Graph::new(&c);
        graph.requests = requests;
        graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
        for (i, node) in nodes.iter().enumerate() {
            graph.active = result.contexts[i];
            env.validate(&graph, node)?;
            graph.push(node.clone())?;
        }
        Ok(())
    };
    let requests = result.prepared.requests().requests().to_vec();
    rebuild(&result.nodes, requests.clone()).unwrap();
    for (answer, key) in [
        (2, "problem"),
        (3, "solutions"),
        (6, "assignment"),
        (7, "object"),
    ] {
        let at = result.answers[answer].outputs[key].0;
        let mut nodes = result.nodes.clone();
        assert!(nodes[at].arguments.pop().is_some());
        assert!(
            matches!(
                rebuild(&nodes, requests.clone()),
                Err(ValidationFailure::Internal(_))
            ),
            "{key} owner edge"
        );
        let mut nodes = result.nodes.clone();
        assert_ne!(nodes[at].scope, Scope::default());
        nodes[at].scope = Scope::default();
        assert!(
            matches!(
                rebuild(&nodes, requests.clone()),
                Err(ValidationFailure::Internal(_))
            ),
            "{key} scope"
        );
    }
    let mut changed = requests;
    changed[2].id = "foreign-producer".into();
    assert!(matches!(
        rebuild(&result.nodes, changed),
        Err(ValidationFailure::Internal(_))
    ));
}

#[test]
fn legacy_integer_ordinal_uses_the_public_origin_and_kernel_order() {
    for body in [
        "view first(s:State):Z=s.h;change choose(s:State,p:Z,q:Z)=s with{h=q};law required valid(s:State):s.h=s.h;",
        "view first(s:State):Z=s.h;change choose(s:State,p:Z,q:Z,t:Z) when p+q=3 =s with{h=t};law required valid(s:State):s.h=s.h;",
    ] {
        let c = quiet();
        let asks = [
            "s=solve(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
            "c=candidate($s.solutions,index=1)",
            "a=apply($c.assignment,in=$s.solutions)",
            "h=evaluate(Pair.first,on=$a.object,s=@v/s)",
        ];
        let result = evaluate_observed_bytes(fixture::input(body, "2", "2"), &asks, &c)
            .unwrap_or_else(|e| panic!("{:?}", e.wire()));
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        let at = |wire: &Json| -> usize {
            (0..result.nodes.len())
                .find(|i| NodeRef(*i).wire() == *wire)
                .unwrap()
        };
        let value = |i: usize| -> Z {
            match result.nodes[i].payload.as_ref().unwrap() {
                Payload::Scalar(Scalar::Z(z)) => z.clone(),
                Payload::Construction(v) => match v.scalar().unwrap() {
                    Scalar::Z(z) => z.clone(),
                    _ => panic!(),
                },
                _ => panic!(),
            }
        };
        let record = |i: usize| -> Json {
            let Some(Payload::Construction(v)) = &result.nodes[i].payload else {
                panic!()
            };
            v.wire()
        };
        let set = record(result.answers[0].outputs["solutions"].0);
        let representation = fields(&fields(&set).unwrap()["representation"]).unwrap();
        let origin = record(at(&representation["particular"]));
        let Json::Arr(origin) = &fields(&origin).unwrap()["coordinates"] else {
            panic!()
        };
        let embedding = record(at(&representation["embedding"]));
        let Json::Arr(columns) = &fields(&embedding).unwrap()["columns"] else {
            panic!()
        };
        let Json::Arr(first) = &columns[0] else {
            panic!()
        };
        // index=1は公開された第1核列の係数だけが1。他の自由係数は0。
        let expected = origin
            .iter()
            .zip(first)
            .map(|(a, b)| value(at(a)) + value(at(b)))
            .collect::<Vec<_>>();
        let state = data_for(&result, result.answers[1].outputs["assignment"])
            .source
            .integer()
            .unwrap();
        assert_eq!(state.parameters.as_ref(), Some(&expected));
        assert_eq!(
            value(result.answers[3].outputs["value"].0),
            *expected.last().unwrap()
        );
        if expected.len() == 2 {
            assert_eq!(expected, vec![Z::from(1), Z::from(0)]);
        }
    }
}

#[test]
fn integer_regression_known_branches_share_the_complete_update_layout() {
    let body = "view all(s:State):Set<State> =set<State>{s};view vacant(s:State):Set<State> =set<State>{};view first(s:State):Z=s.h;view second(s:State):Z=s.k;change choose(s:State,p:Z)=if s.a=2 then s with{h=p} else s with{k=p};law required valid(s:State):if s.a=2 then s.h=s.b else s.k=s.b;";
    let asks = [
        "u=evaluate(Pair.all,s=@v/s)",
        "z=evaluate(Pair.vacant,s=@v/s)",
        "p=prepare(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "lo=solve($p.problem,within=$z.value)",
        "hi=solve($p.problem,within=$u.value)",
        "r=scopes($p.problem)",
        "c=candidate($hi.solutions,index=0)",
        "a=apply($c.assignment,in=$hi.solutions)",
        "ok=check(Pair.valid,on=$a.object,s=@v/s)",
        "h=evaluate(Pair.first,on=$a.object,s=@v/s)",
        "k=evaluate(Pair.second,on=$a.object,s=@v/s)",
        "next=prepare(Pair.valid,using=Pair.choose,on=$a.object,s=@v/s)",
        "fixed=solve($next.problem,within=$z.value)",
        "old=solve(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "explicit=candidate($old.solutions,index=0)",
    ];
    let c = quiet();
    let first = evaluate_observed_bytes(fixture::input(body, "2", "2"), &asks, &c).unwrap();
    let current =
        reevaluate_observed_bytes(&first, fixture::input(body, "3", "2"), &asks, &c).unwrap();
    let cold = evaluate_observed_bytes(fixture::input(body, "3", "2"), &asks, &c).unwrap();
    assert_eq!(current.result_wire(), cold.result_wire());
    for (result, expected) in [(&first, [2, 0]), (&current, [0, 2])] {
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        for (i, answer) in result.answers.iter().enumerate() {
            assert_eq!(
                answer.status,
                if i == 3 {
                    Decision::Refuted
                } else {
                    Decision::Established
                },
                "{} {:?}",
                answer.id,
                result.issues
            );
        }
        for (i, z) in (9..=10).zip(expected) {
            let at = result.answers[i].outputs["value"].0;
            let value = match result.nodes[at].payload.as_ref().unwrap() {
                Payload::Scalar(value) => value,
                Payload::Construction(value) => value.scalar().unwrap(),
                _ => panic!(),
            };
            assert_eq!(value, &Scalar::Z(z.into()));
        }
        let state = data_for(result, result.answers[6].outputs["assignment"])
            .source
            .integer()
            .unwrap();
        assert_eq!(state.parameters.as_deref(), Some([Z::from(2)].as_slice()));
    }
}
#[test]
fn integer_regression_quotient_builds_only_the_requested_domain_coordinates() {
    use crate::observed::environment::quotient_affine::coefficients;
    let c = quiet();
    let result = evaluate_observed_bytes(part_input(2), &part_asks()[..7], &c).unwrap();
    let prepared = data_for(&result, result.answers[4].outputs["problem"])
        .source
        .integer()
        .unwrap();
    assert!(prepared.shared.compiled.linear.particular.is_some());
    assert!(!prepared.shared.compiled.linear.kernel[0].is_empty());
    let domain = candidate_input(prepared, NodeType::Construction(T::CandidateSpace)).unwrap();
    let coordinates = coefficients::Input::from_candidate(&domain, &c).unwrap();
    assert!(coordinates.particular.is_none());
    assert!(
        coordinates.kernel.is_empty(),
        "候補域の商ではLaw全解の密な表示を作らない"
    );
    assert!(coordinates.guard_origin.is_some());
    assert_eq!(coordinates.guard_kernel.len(), 6);
    let solved = data_for(&result, result.answers[6].outputs["solutions"])
        .source
        .integer()
        .unwrap();
    let domain = candidate_input(solved, NodeType::Construction(T::SolutionSet)).unwrap();
    let coordinates = coefficients::Input::from_candidate(&domain, &c).unwrap();
    assert!(coordinates.particular.is_some());
    assert_eq!(coordinates.kernel.len(), 6);
    assert_eq!(coordinates.kernel[0].len(), 5);
    assert!(coordinates.guard_origin.is_none());
    assert!(coordinates.guard_kernel.is_empty());
}

#[test]
fn legacy_and_prepared_integer_assignments_transfer_by_subject_across_coordinate_orders() {
    let body = "view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Z,q:Z)=c with{x=p,y=q};law required valid(r:Root):forall c in Part[r]. c.x=(if c.label=\"a\" then 1 else if c.label=\"b\" then 2 else 3);";
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "old=solve(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root)",
        "c=candidate($old.solutions,index=1)",
        "a=apply($c.assignment,in=$s.solutions)",
        "d=candidate($s.solutions,index=1)",
        "back=apply($d.assignment,in=$old.solutions)",
        "ok=check(Selected.valid,on=$a.object,r=@v/root)",
        "also=check(Selected.valid,on=$back.object,r=@v/root)",
    ];
    let c = quiet();
    for order in [["a", "b", "c"], ["c", "a", "b"], ["b", "c", "a"]] {
        let parts = order.map(|id| (id, 0, 0, id));
        let result = evaluate_observed_bytes(parts::input(&parts, body), &asks, &c)
            .unwrap_or_else(|e| panic!("{:?}", e.wire()));
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        for answer in &result.answers {
            assert_eq!(
                answer.status,
                Decision::Established,
                "{order:?} {} {:?}",
                answer.id,
                result.issues
            );
        }
        let scalar = |wire: &Json| -> Scalar {
            let at = (0..result.nodes.len())
                .find(|i| NodeRef(*i).wire() == *wire)
                .unwrap();
            match result.nodes[at].payload.as_ref().unwrap() {
                Payload::Scalar(s) => s.clone(),
                Payload::Construction(v) => v.scalar().unwrap().clone(),
                _ => panic!(),
            }
        };
        for (source, applied) in [(4, 5), (6, 7)] {
            let assignment = result.answers[source].outputs["assignment"];
            let source = data_for(&result, assignment).source.integer().unwrap();
            let selection = result.answers[applied].outputs["selection"];
            let state = data_for(&result, selection).source.integer().unwrap();
            assert!(
                state.parameters.is_none(),
                "適用後は元Assignmentを参照し、一時の元値を重複保持しない"
            );
            let Some(Payload::Construction(selected)) = &result.nodes[selection.0].payload else {
                panic!()
            };
            let selected = selected.wire();
            assert_eq!(fields(&selected).unwrap()["parameters"], assignment.wire());
            let object = result.answers[applied].outputs["object"];
            let Some(Payload::Construction(value)) = &result.nodes[object.0].payload else {
                panic!()
            };
            let wire = value.wire();
            let Json::Arr(overrides) = &fields(&wire).unwrap()["overrides"] else {
                panic!()
            };
            assert_eq!(overrides.len(), 6);
            for row in overrides {
                let row = fields(row).unwrap();
                let slot = fields(&row["slot"]).unwrap();
                let subject = scalar(&slot["subject"]);
                let from = source
                    .shared
                    .compiled
                    .subjects
                    .iter()
                    .position(|s| *s == subject)
                    .unwrap();
                let Json::Str(field) = &slot["field"] else {
                    panic!()
                };
                let offset = match field.as_str() {
                    "Pattern.Part.x" => 0,
                    "Pattern.Part.y" => 1,
                    _ => panic!("更新先が違う"),
                };
                assert_eq!(
                    scalar(&row["value"]),
                    Scalar::Z(source.parameters.as_ref().unwrap()[2 * from + offset].clone()),
                    "元subjectの元parameterを実対象の各座標へ戻す"
                );
            }
        }
    }
}

#[test]
fn parameter_block_transfer_preserves_every_permutation_and_stops_at_each_checkpoint() {
    use std::{cell::Cell, rc::Rc};
    let original = [10, 11, 20, 21, 30, 31].map(Z::from).to_vec();
    let c = quiet();
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let expected = order
            .iter()
            .flat_map(|i| original[2 * i..2 * i + 2].iter().cloned())
            .collect::<Vec<_>>();
        assert_eq!(
            transfer_parameters(original.clone(), order.to_vec(), &c).unwrap(),
            expected
        );
    }
    assert!(transfer_parameters(vec![], vec![], &c).unwrap().is_empty());
    let run = |stop: Option<usize>| {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let c = Control::new(move |_| {
            seen.set(seen.get() + 1);
            (stop == Some(seen.get())).then_some(archsig_common::control::Signal::Term)
        });
        let result = transfer_parameters(original.clone(), vec![2, 0, 1], &c);
        (result, count.get())
    };
    let (complete, count) = run(None);
    assert!(complete.is_ok());
    assert!(count > 3);
    for at in 1..=count {
        assert!(
            matches!(run(Some(at)).0, Err(ValidationFailure::Stop(_))),
            "checkpoint {at}"
        );
    }
}

#[test]
fn pending_integer_reasons_keep_source_expressions_and_do_not_block_independent_checks() {
    let c = quiet();
    let asks = [
        "p=prepare(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "blocked=check(Pair.valid,on=$p.problem.domain.base,s=@v/s)",
        "later=check(Pair.known,s=@v/s)",
    ];
    for (change, law, missing) in [
        (
            "change choose(s:State,p:Z,q:Z)=s with{h=p*q};",
            "s.h=s.b",
            None,
        ),
        (
            "change choose(s:State,p:Z) when p>0 =s with{h=p};",
            "s.h=s.b",
            None,
        ),
        (
            "change choose(s:State,p:Z)=s with{h=p};",
            "s.h=s.b",
            Some("b"),
        ),
        (
            "change choose(s:State,p:Z)=s with{h=p};",
            "s.a*s.h=s.b",
            Some("a"),
        ),
        (
            "change choose(s:State,p:Z)=s with{h=s.a*p};",
            "s.h=s.b",
            Some("a"),
        ),
        (
            "change choose(s:State,p:Z) when s.a*p=1 =s with{h=p};",
            "s.h=s.b",
            Some("a"),
        ),
    ] {
        let body = format!(
            "{change}law required valid(s:State):{law};law required known(s:State):s.h=s.h;"
        );
        let input = fixture::input(&body, "2", "2");
        let input = missing.map_or_else(|| input.clone(), |name| without_atom(input.clone(), name));
        let result = evaluate_observed_bytes(input, &asks, &c)
            .unwrap_or_else(|e| panic!("{change} {law}: {:?}", e.wire()));
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
            "{:?}",
            result.issues
        );
        assert_eq!(result.answers[0].status, Decision::Undetermined);
        assert_eq!(result.answers[1].status, Decision::Undetermined);
        assert_eq!(result.answers[2].status, Decision::Established);
        let reasons = &result.answers[0].reasons;
        assert!(!reasons.is_empty());
        for reason in reasons {
            if matches!(
                reason.kind,
                ReasonKind::Missing | ReasonKind::UnsupportedAlgorithm { .. }
            ) {
                assert!(!reason.dependencies.is_empty());
                assert!(
                    reason
                        .dependencies
                        .iter()
                        .all(|at| matches!(result.nodes[at.0].ty, NodeType::Expression(_)))
                );
                assert!(reason.location.is_some());
            }
        }
        if let Some(name) = missing {
            assert!(
                reasons.iter().any(|r| matches!(r.kind, ReasonKind::Missing)
                    && r.missing
                        .iter()
                        .any(|f| f.field.as_deref() == Some(&format!("Pair.State.{name}")))),
                "{reasons:?}"
            );
        }
    }
}

#[test]
fn finite_and_integer_foreign_assignments_and_ranges_are_condition_failures() {
    let body = "view all(s:State):Set<State> =set<State>{s};change zi(s:State,p:Z)=s with{h=p};change bf(s:State,p:Bool)=s with{h=if p then 1 else 0};law required valid(s:State):s.h=s.h;";
    let asks = [
        "u=evaluate(Pair.all,s=@v/s)",
        "i=prepare(Pair.valid,using=Pair.zi,on=@v/s,s=@v/s)",
        "f=prepare(Pair.valid,using=Pair.bf,on=@v/s,s=@v/s)",
        "is=solve($i.problem,within=$u.value)",
        "fs=solve($f.problem,within=$u.value)",
        "ic=candidate($is.solutions,index=0)",
        "fc=candidate($fs.solutions,index=0)",
        "ir=scopes($i.problem)",
        "fr=scopes($f.problem)",
        "bad1=apply($fc.assignment,in=$is.solutions)",
        "bad2=apply($ic.assignment,in=$fs.solutions)",
        "bad3=solve($f.problem,within=$ir.ranges[0])",
        "bad4=solve($i.problem,within=$fr.ranges[0])",
        "later=check(Pair.valid,s=@v/s)",
    ];
    let result = evaluate_observed_bytes(fixture::input(body, "2", "2"), &asks, &quiet()).unwrap();
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    for a in &result.answers[9..13] {
        assert_eq!(a.status, Decision::Refuted, "{a:?}");
        assert!(a.outputs.keys().all(|key| key == "proposition"));
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. })),
            "{a:?}"
        );
    }
    assert_eq!(result.answers[13].status, Decision::Established);
}

#[test]
fn integer_candidate_environments_share_only_the_selected_object_domain() {
    let c = quiet();
    let result = evaluate_observed_bytes(fixture::input(BODY, "2", "2"), &ASKS[..3], &c).unwrap();
    let state = data_for(&result, result.answers[2].outputs["problem"])
        .source
        .integer()
        .unwrap();
    let env = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &c,
    )
    .unwrap();
    let first = state.shared.compiled.environment(&env, &c).unwrap();
    let second = state.shared.compiled.environment(&env, &c).unwrap();
    // Candidate point environments inherit the immutable domain without rebuilding its tables.
    state.shared.compiled.assert_object_shared(&first);
    state.shared.compiled.assert_object_shared(&second);
    assert!(first.fixed_values().is_empty());
    assert!(second.fixed_values().is_empty());
}

#[test]
fn unsupported_integer_input_family_keeps_source_expression_and_later_checks() {
    let c = quiet();
    let asks = [
        "p=prepare(Pair.valid,using=Pair.choose,on=@v/s,inputs=Pair.first,s=@v/s)",
        "blocked=check(Pair.valid,on=$p.problem.domain.base,s=@v/s)",
        "later=check(Pair.valid,s=@v/s)",
    ];
    let result = evaluate_observed_bytes(without_atom(fixture::input("view first(s:State):Z=s.a;change choose(s:State,p:Z)=s with{h=s.a*p};law required valid(s:State):s.h=s.h;", "2", "0"),"a"), &asks, &c).unwrap();
    assert!(
        result
            .issues
            .iter()
            .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
        "{:?}",
        result.issues
    );
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    assert_eq!(result.answers[2].status, Decision::Established);
    assert!(result.answers[0].reasons.iter().any(|r| {
        matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. })
            && !r.dependencies.is_empty()
            && r.dependencies
                .iter()
                .all(|at| matches!(result.nodes[at.0].ty, NodeType::Expression(_)))
    }));
}
