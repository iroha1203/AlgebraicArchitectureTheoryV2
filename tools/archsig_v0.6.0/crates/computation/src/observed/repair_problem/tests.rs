use super::*;
#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/repair_problem_data.rs");
}
use fixture::input;

#[test]
fn shared_problem_range_selection_reaches_original_law_and_next_change() {
    let before = super::super::environment::repair_problem::generations();
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "r=scopes($p.problem)",
        "m=solve($p.problem,within=$r.ranges[0])",
        "c=candidate($m.solutions,index=1)",
        "a=apply($c.assignment,in=$m.solutions)",
        "ok=check(Selected.valid,on=$a.object)",
        "v=evaluate(Selected.flag,c=@v/q,on=$a.object)",
        "next=solve(Selected.valid,using=Selected.choose,on=$a.object)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input(""), &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    for a in &result.answers {
        assert_eq!(a.status, Decision::Established, "{} {:?}", a.id, a.reasons);
    }
    let value = result.answers[8].outputs["value"];
    assert!(match &result.nodes[value.0].payload {
        Some(Payload::Scalar(Scalar::Bool(true))) => true,
        Some(Payload::Construction(v)) => matches!(v.scalar(), Some(Scalar::Bool(true))),
        _ => false,
    });
    assert_eq!(
        super::super::environment::repair_problem::generations() - before,
        1
    );
    let shared_for = |at: NodeRef| match &result.nodes[at.0].payload {
        Some(Payload::Construction(v)) => match &v.data {
            D::SharedRepair(d) => d.source.finite().unwrap(),
            _ => panic!("共有経路"),
        },
        _ => panic!("native結果"),
    };
    let initial = shared_for(result.answers[1].outputs["problem"]);
    for (answer, field) in [
        (2, "solutions"),
        (3, "ranges"),
        (4, "solutions"),
        (5, "assignment"),
        (6, "object"),
    ] {
        assert!(Arc::ptr_eq(
            initial,
            shared_for(result.answers[answer].outputs[field])
        ));
    }
    let selected = result.answers[5].outputs["assignment"];
    let Some(Payload::Construction(v)) = &result.nodes[selected.0].payload else {
        panic!()
    };
    let D::SharedRepair(candidate) = &v.data else {
        panic!()
    };
    assert_eq!(candidate.source.chosen.as_ref().unwrap()[..4], [1, 0, 1, 1]);
}

#[test]
fn six_instance_shared_fibers_match_original_assignments_and_updated_targets() {
    for cross in [false, true] {
        let count = if cross { 4 } else { 8 };
        let mut asks=vec!["i=evaluate(Selected.internal,r=@v/root)".to_owned(),"xy=evaluate(Selected.xy,r=@v/root)".into(),"xyz=evaluate(Selected.xyz,r=@v/root)".into(),
                "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$i.value,r=@v/root)".into(),
                "small=solve($p.problem,within=$xy.value,mode=existence)".into(),"full=solve($p.problem,within=$xyz.value)".into()];
        for i in 0..count {
            asks.push(format!("c{i}=candidate($full.solutions,index={i})"));
        }
        asks.push("last=apply($c0.assignment,in=$full.solutions)".into());
        asks.push("check=check(Selected.valid,on=$last.object,r=@v/root)".into());
        let result = super::super::evaluate_observed_bytes(
            fixture::six(cross),
            &asks.iter().map(String::as_str).collect::<Vec<_>>(),
            &archsig_common::control::quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(result.answers[4].status, Decision::Refuted);
        assert_eq!(result.answers[5].status, Decision::Established);
        assert!(!result.answers[4].outputs.contains_key("solutions"));
        for (index, node) in result.nodes.iter().enumerate() {
            if matches!(result.contexts[index].request, 4 | 5) {
                assert!(!matches!(
                    node.ty,
                    NodeType::Construction(T::Assignment | T::Architecture)
                ));
            }
        }

        let mut actual = vec![];
        for a in &result.answers[6..6 + count] {
            let r = a.outputs["assignment"];
            let Some(Payload::Construction(v)) = &result.nodes[r.0].payload else {
                panic!()
            };
            let D::SharedRepair(d) = &v.data else {
                panic!()
            };
            let s = d.source.finite().unwrap();
            let point = d.source.chosen.as_ref().unwrap();
            let mut row = BTreeMap::new();
            for (i, subject) in s.compiled.subjects.iter().enumerate() {
                let Scalar::Subject { subject, .. } = subject else {
                    panic!()
                };
                let Scalar::Bool(v) = s.compiled.domains[i][point[i]] else {
                    panic!()
                };
                row.insert(subject.clone(), v);
            }
            for o in &s.compiled.outputs {
                assert_eq!(
                    s.compiled.domains[o.column][point[o.column]],
                    Scalar::Bool(row[&o.fact.subject])
                );
            }
            actual.push(row);
        }
        let mut expected = vec![];
        for bits in 0..64 {
            let labels = ["a", "b", "c", "x", "y", "z"];
            let row = labels
                .into_iter()
                .enumerate()
                .map(|(i, n)| (n.to_owned(), bits & (1 << i) != 0))
                .collect::<BTreeMap<_, _>>();
            if row["x"]
                && row["x"] == row["y"]
                && row["y"] == row["z"]
                && (!cross || row["a"] == row["b"])
            {
                expected.push(row);
            }
        }
        actual.sort();
        expected.sort();
        assert_eq!(actual, expected);
        assert_eq!(result.answers.last().unwrap().status, Decision::Established);
    }
}
#[test]
fn separate_internal_masks_share_compilation_and_keep_problem_identity() {
    let before = super::super::environment::repair_problem::generations();
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "q=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$u.value)",
        "a=scopes($p.problem)",
        "b=scopes($q.problem)",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input(""),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    let shared = |i: usize| {
        let at = result.answers[i].outputs["problem"];
        let Some(Payload::Construction(v)) = &result.nodes[at.0].payload else {
            panic!()
        };
        let D::SharedRepair(d) = &v.data else {
            panic!()
        };
        d.source.finite().unwrap()
    };
    let (a, b) = (shared(1), shared(2));
    assert!(Arc::ptr_eq(&a.compiled, &b.compiled));
    assert_ne!(a.problem, b.problem);
    assert_ne!(a.internal, b.internal);
    assert_eq!(
        super::super::environment::repair_problem::generations() - before,
        1
    );
}
#[test]
fn original_finite_solution_supports_explicit_selection_without_unique_repair() {
    let asks = [
        "s=solve(Selected.valid,using=Selected.choose,on=@v/root)",
        "c=candidate($s.solutions,index=3)",
        "a=apply($c.assignment,in=$s.solutions)",
        "ok=check(Selected.valid,on=$a.object)",
        "r=repair(Selected.valid,using=Selected.choose,on=@v/root)",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input(""),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    for a in &result.answers[..4] {
        assert_eq!(a.status, Decision::Established, "{} {:?}", a.id, a.reasons);
    }
    assert_eq!(result.answers[4].status, Decision::Refuted);
    assert!(!result.answers[4].outputs.contains_key("object"));
}
#[test]
fn missing_baseline_is_retained_and_range_projection_out_of_bounds_is_blocked() {
    let asks = [
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "r=scopes($p.problem)",
        "s=solve($p.problem,within=$r.ranges[1])",
    ];
    let input = fixture::input("");
    let map=String::from_utf8(input.archmap().bytes().to_vec()).unwrap().replace(r#",{"id":"flag-q","subject":"q","field":"Pattern.Part.flag","value":false,"origin":"model"}"# ,"");
    let missing = archsig_input::input::InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        input.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let result =
        super::super::evaluate_observed_bytes(missing, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    assert!(!result.answers[0].outputs.contains_key("problem"));
    assert!(result.answers[0].reasons.iter().any(|r| {
        r.missing
            .iter()
            .any(|f| f.subject == "q" && f.field.as_deref() == Some("Pattern.Part.flag"))
    }));
    assert_eq!(result.answers[1].status, Decision::Undetermined);
    let result = super::super::evaluate_observed_bytes(
        fixture::input(""),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.answers[1].status, Decision::Established);
    assert_eq!(result.answers[2].status, Decision::Undetermined);
    assert!(!result.answers[2].outputs.contains_key("solutions"));
    assert!(
        !result
            .issues
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Internal(_)))
    );
}
#[test]
fn normal_validator_rejects_changed_producer_edges_and_support() {
    let asks = [
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "r=scopes($p.problem)",
    ];
    let c = archsig_common::control::quiet();
    let result = super::super::evaluate_observed_bytes(fixture::input(""), &asks, &c).unwrap();
    let rebuild = |nodes: &[Node], requests: Vec<Request>| -> Result<(), ValidationFailure> {
        let env = Environment::with_requests(
            result.prepared.inputs(),
            result.prepared.requests().requests(),
            &c,
        )?;
        let mut g = Graph::new(&c);
        g.requests = requests;
        g.checked_answers = result.answers.iter().cloned().enumerate().collect();
        for (index, node) in nodes.iter().enumerate() {
            g.active = result.contexts[index];
            env.validate(&g, node)?;
            g.push(node.clone())?;
        }
        Ok(())
    };
    let requests = result.prepared.requests().requests().to_vec();
    rebuild(&result.nodes, requests.clone()).unwrap();
    let at = result.answers[0].outputs["problem"].0;
    let mut nodes = result.nodes.clone();
    nodes[at].arguments.pop();
    assert!(matches!(
        rebuild(&nodes, requests.clone()),
        Err(ValidationFailure::Internal(_))
    ));
    let mut nodes = result.nodes.clone();
    nodes[at].support = Default::default();
    assert!(matches!(
        rebuild(&nodes, requests.clone()),
        Err(ValidationFailure::Internal(_))
    ));
    let mut changed = requests;
    changed[0].id = "other".into();
    assert!(matches!(
        rebuild(&result.nodes, changed),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn inclusion_minimal_ranges_keep_larger_incomparable_choices() {
    let input = fixture::sources(
        &[("a", false, "a"), ("b", false, "b"), ("c", false, "c")],
        r#"change choose(c:Part,p:Bool)=c with {flag=p};law required valid(a:Part,b:Part,c:Part):a.flag or (b.flag and c.flag);"#,
    );
    let asks = [
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,a=@v/a,b=@v/b,c=@v/c)",
        "r=scopes($p.problem)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    let at = result.answers[1].outputs["ranges"];
    let Some(Payload::Construction(v)) = &result.nodes[at.0].payload else {
        panic!()
    };
    let D::SharedRepair(d) = &v.data else {
        panic!()
    };
    let actual = d.source.ranges.values().cloned().collect::<Vec<_>>();
    assert_eq!(
        actual,
        vec![vec![true, false, false], vec![false, true, true]]
    );
}
#[test]
fn ranges_and_candidates_cannot_be_transferred_between_distinct_problems() {
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "q=prepare(Selected.valid,using=Selected.other,on=@v/root)",
        "r=scopes($p.problem)",
        "wrong=solve($q.problem,within=$r.ranges[0])",
        "s=solve($p.problem,within=$u.value)",
        "t=solve($q.problem,within=$u.value)",
        "c=candidate($s.solutions,index=0)",
        "a=apply($c.assignment,in=$t.solutions)",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input("change other(c:Part,p:Bool,q:Bool)=c with {flag=p};"),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(result.answers[4].status, Decision::Refuted);
    assert_eq!(result.answers[8].status, Decision::Refuted);
    assert!(!result.answers[8].outputs.contains_key("object"));
}
#[test]
fn selected_assignment_must_preserve_the_target_range_fixed_values() {
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "e=evaluate(Selected.empty,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "fixed=solve($p.problem,within=$e.value)",
        "c=candidate($s.solutions,index=0)",
        "a=apply($c.assignment,in=$fixed.solutions)",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input("view empty(r:Root):Set<Part> =set {c|c in Part[r] where false};"),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(result.answers[3].status, Decision::Established);
    assert_eq!(result.answers[4].status, Decision::Refuted);
    assert_eq!(result.answers[5].status, Decision::Established);
    assert_eq!(result.answers[6].status, Decision::Refuted);
    assert!(!result.answers[6].outputs.contains_key("object"));
}
#[test]
fn public_ordinal_larger_than_safe_json_integer_is_not_truncated() {
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "c=candidate($s.solutions,index=900719925474099312345678901234567890)",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input(""),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    let selector = &result.prepared.requests().requests()[3]
        .arguments
        .iter()
        .find(|a| a.name == "index")
        .unwrap()
        .value;
    assert_eq!(
        selector,
        &Selector::Ordinal {
            value: "900719925474099312345678901234567890".into()
        }
    );
    assert_eq!(
        selector.wire(),
        Json::obj([
            ("kind", Json::str("ordinal")),
            ("value", Json::str("900719925474099312345678901234567890"))
        ])
    );
    assert_eq!(result.answers[3].status, Decision::Refuted);
    assert_eq!(result.answers[2].status, Decision::Established);
}
#[test]
fn out_of_range_candidate_preserves_prior_answers_and_blocks_application() {
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "c=candidate($s.solutions,index=4)",
        "a=apply($c.assignment,in=$s.solutions)",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input(""),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "partial", "{:?}", result.issues);
    assert_eq!(result.answers[2].status, Decision::Established);
    assert_eq!(result.answers[3].status, Decision::Refuted);
    assert_eq!(result.answers[4].status, Decision::Undetermined);
    assert!(!result.answers[4].outputs.contains_key("object"));
    assert!(
        result.answers[4]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::DependencyBlocked { .. }))
    );
}

#[test]
fn fixed_outside_values_can_require_nonzero_identity_parameters() {
    let input = fixture::sources(
        &[("p", false, "p"), ("q", false, "q")],
        "view empty(r:Root):Set<Part> =set {c|c in Part[r] where false};change choose(c:Part,p:Bool)=c with {flag=not p};law required valid(c:Part):not c.flag;",
    );
    let asks = [
        "e=evaluate(Selected.empty,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$e.value)",
        "c=candidate($s.solutions,index=0)",
        "a=apply($c.assignment,in=$s.solutions)",
        "ok=check(Selected.valid,on=$a.object)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert!(
        result
            .answers
            .iter()
            .all(|a| a.status == Decision::Established)
    );
    let at = result.answers[3].outputs["assignment"];
    let Some(Payload::Construction(v)) = &result.nodes[at.0].payload else {
        panic!()
    };
    let D::SharedRepair(d) = &v.data else {
        panic!()
    };
    assert_eq!(&d.source.chosen.as_ref().unwrap()[..2], &[1, 1]);
}

#[test]
fn internal_instances_must_belong_to_the_selected_owner() {
    let original = fixture::input("");
    let map=String::from_utf8(original.archmap().bytes().to_vec()).unwrap().replace(r#"{"id":"root","type":"Pattern.Root","origin":"model"}"#,r#"{"id":"root","type":"Pattern.Root","origin":"model"},{"id":"other","type":"Pattern.Root","origin":"model"}"#).replace(r#"{"id":"owner-q","subject":"q","field":"Pattern.Part.owner","value":["v","root"]"#,r#"{"id":"owner-q","subject":"q","field":"Pattern.Part.owner","value":["v","other"]"#);
    let source = archsig_input::input::InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        original.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let asks = [
        "u=evaluate(Selected.all,r=@v/other)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,internal=$u.value)",
    ];
    let result =
        super::super::evaluate_observed_bytes(source, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(result.answers[0].status, Decision::Established);
    assert_eq!(result.answers[1].status, Decision::Refuted);
    assert!(!result.answers[1].outputs.contains_key("problem"));
}

#[test]
fn semantically_same_domains_allow_selection_and_check_target_requirements() {
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "q=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "r=scopes($p.problem)",
        "s=solve($p.problem,within=$u.value)",
        "t=solve($q.problem,within=$r.ranges[0])",
        "c=candidate($s.solutions,index=0)",
        "a=apply($c.assignment,in=$t.solutions)",
        "off=prepare(Selected.off,using=Selected.choose,on=@v/root)",
        "os=solve($off.problem,within=$u.value)",
        "bad=apply($c.assignment,in=$os.solutions)",
        "any=prepare(Selected.any,using=Selected.choose,on=@v/root)",
        "free=solve($any.problem,within=$u.value)",
        "b=apply($c.assignment,in=$free.solutions)",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input("law required off(c:Part):not c.flag;law required any(c:Part):true;"),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(result.answers[7].status, Decision::Established);
    assert_eq!(result.answers[10].status, Decision::Refuted);
    assert!(!result.answers[10].outputs.contains_key("object"));
    assert_eq!(result.answers[13].status, Decision::Established);
}

#[test]
fn existing_unique_repair_assignment_is_accepted_and_legacy_candidates_share_parts() {
    let input = fixture::sources(
        &[("p", false, "p")],
        "view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p};law required valid(c:Part):c.flag;",
    );
    let asks = [
        "r=repair(Selected.valid,using=Selected.choose,on=@v/root)",
        "a=apply($r.repair.parameters,in=$r.repair.solutions)",
        "ok=check(Selected.valid,on=$a.object)",
        "c0=candidate($r.solutions,index=0)",
        "c1=candidate($r.solutions,index=0)",
    ];
    let before = super::super::environment::repair_problem::generations();
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert!(
        result
            .answers
            .iter()
            .all(|a| a.status == Decision::Established)
    );
    assert_eq!(
        super::super::environment::repair_problem::generations() - before,
        1
    );
}

#[test]
fn unsupported_mixed_integer_prepare_and_supported_integer_candidates_preserve_later_checks() {
    let input = fixture::sources(
        &[("p", true, "p")],
        "change choose(c:Part,p:Z)=c with {flag=p=0};law required valid(c:Part):c.flag=c.flag;",
    );
    let asks = [
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "later=check(Selected.valid,c=@v/p)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "partial", "{:?}", result.issues);
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
    );
    assert_eq!(result.answers[1].status, Decision::Established);
    let input = archsig_input::input::InputSources::from_bytes(
        vec![include_bytes!("../../../../../tests/fixtures/counter.atoms.json").to_vec()],
        include_str!("../../../../../tests/fixtures/counter.law")
            .replace(
                "view amount",
                "change choose(s:State,n:Z)=s with {count=n};view amount",
            )
            .replace("s.count >= 0", "s.count = s.count")
            .into_bytes(),
        include_bytes!("../../../../../tests/fixtures/counter.archmap.json").to_vec(),
    );
    let asks = [
        "s=solve(CountCheck.nonnegative,using=CountCheck.choose,on=@v/s)",
        "c=candidate($s.solutions,index=0)",
        "a=apply($c.assignment,in=$s.solutions)",
        "blocked=check(CountCheck.nonnegative,on=$a.object,s=@v/s)",
        "later=check(CountCheck.nonnegative,s=@v/s)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert!(
        result
            .answers
            .iter()
            .all(|answer| answer.status == Decision::Established)
    );
    let assignment = data_from(&result, result.answers[1].outputs["assignment"]);
    assert_eq!(
        assignment.source.integer().unwrap().parameters.as_deref(),
        Some([num_bigint::BigInt::from(0)].as_slice())
    );
}

#[test]
fn selected_object_prepares_a_problem_consumed_by_scopes_and_solve() {
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "c=candidate($s.solutions,index=0)",
        "a=apply($c.assignment,in=$s.solutions)",
        "next=prepare(Selected.valid,using=Selected.choose,on=$a.object)",
        "r=scopes($next.problem)",
        "n=solve($next.problem,within=$r.ranges[0])",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input(""),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert!(
        result
            .answers
            .iter()
            .all(|a| a.status == Decision::Established)
    );
    let at = result.answers[6].outputs["ranges"];
    let d = data_from(&result, at);
    assert_eq!(
        d.source.ranges.values().cloned().collect::<Vec<_>>(),
        vec![vec![false; 2]]
    );
}
fn data_from(result: &super::super::ObservedEvaluation, at: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &result.nodes[at.0].payload else {
        panic!("native result")
    };
    let D::SharedRepair(d) = &v.data else {
        panic!("shared repair")
    };
    d
}
#[test]
fn completed_empty_scope_avoids_enumerating_its_supersets() {
    let parts = (0..30)
        .map(|i| (format!("p{i:02}"), false, format!("p{i:02}")))
        .collect::<Vec<_>>();
    let refs = parts
        .iter()
        .map(|(a, b, c)| (a.as_str(), *b, c.as_str()))
        .collect::<Vec<_>>();
    let input = fixture::sources(
        &refs,
        "change choose(c:Part,p:Bool)=c with {flag=p};law required valid(c:Part):true;",
    );
    let result = super::super::evaluate_observed_bytes(
        input,
        &["p=prepare(Selected.valid,using=Selected.choose,on=@v/root)"],
        &archsig_common::control::quiet(),
    )
    .unwrap();
    let shared = data_from(&result, result.answers[0].outputs["problem"])
        .source
        .finite()
        .unwrap();
    let mut probes = 0;
    let control = Control::new(move |_| {
        probes += 1;
        (probes > 2000).then_some(archsig_common::control::Signal::Term)
    });
    assert_eq!(minimal(shared, &control).unwrap(), vec![vec![false; 30]]);
}
#[test]
fn overlapping_minimal_ranges_are_complete_without_duplicate_bounds() {
    let input = fixture::sources(
        &[
            ("a", false, "a"),
            ("b", false, "b"),
            ("c", false, "c"),
            ("d", false, "d"),
        ],
        "change choose(c:Part,p:Bool)=c with {flag=p};law required valid(a:Part,b:Part,c:Part,d:Part):(a.flag and b.flag) or (a.flag and c.flag) or (b.flag and d.flag) or (c.flag and d.flag);",
    );
    let result=super::super::evaluate_observed_bytes(input,&["p=prepare(Selected.valid,using=Selected.choose,on=@v/root,a=@v/a,b=@v/b,c=@v/c,d=@v/d)","r=scopes($p.problem)"],&archsig_common::control::quiet()).unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    let d = data_from(&result, result.answers[1].outputs["ranges"]);
    assert_eq!(
        d.source.ranges.values().cloned().collect::<Vec<_>>(),
        vec![
            vec![true, true, false, false],
            vec![true, false, true, false],
            vec![false, true, false, true],
            vec![false, false, true, true]
        ]
    );
}
#[test]
fn guard_excluded_missing_branch_does_not_require_observation_or_lose_the_candidate() {
    let original = fixture::sources(
        &[("p", false, "p")],
        "view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool) when p=c with {flag=if p then true else c.label=\"x\"};law required valid(c:Part):c.flag;",
    );
    let map=String::from_utf8(original.archmap().bytes().to_vec()).unwrap().replace(r#",{"id":"label-p","subject":"p","field":"Pattern.Part.label","value":"p","origin":"model"}"#,"");
    let input = archsig_input::input::InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        original.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let asks = [
        "old=solve(Selected.valid,using=Selected.choose,on=@v/root)",
        "oc=candidate($old.solutions,index=0)",
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "c=candidate($s.solutions,index=0)",
        "a=apply($c.assignment,in=$s.solutions)",
        "ok=check(Selected.valid,on=$a.object)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert!(
        result
            .answers
            .iter()
            .all(|a| a.status == Decision::Established)
    );
}

#[test]
fn correlated_updates_do_not_read_an_unreachable_law_branch() {
    let original = fixture::sources(
        &[("p", false, "q"), ("q", false, "q")],
        "view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p,label=if p then \"yes\" else \"no\"};law required valid(c:Part):if c.flag=(c.label=\"yes\") then true else c.link.label=\"x\";",
    );
    let map=String::from_utf8(original.archmap().bytes().to_vec()).unwrap().replace(r#"{"id":"root","type":"Pattern.Root","origin":"model"}"#,r#"{"id":"root","type":"Pattern.Root","origin":"model"},{"id":"other","type":"Pattern.Root","origin":"model"}"#).replace(r#"{"id":"owner-q","subject":"q","field":"Pattern.Part.owner","value":["v","root"]"#,r#"{"id":"owner-q","subject":"q","field":"Pattern.Part.owner","value":["v","other"]"#).replace(r#",{"id":"label-q","subject":"q","field":"Pattern.Part.label","value":"q","origin":"model"}"#,"");
    let input = archsig_input::input::InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        original.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let asks = [
        "old=solve(Selected.valid,using=Selected.choose,on=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(
        result.answers[0].status,
        Decision::Established,
        "{:?}",
        result.issues
    );
    assert_eq!(
        result.answers[1].status,
        Decision::Established,
        "{:?}",
        result.issues
    );
}

#[test]
fn other_law_factors_exclude_missing_rows_before_observation_is_required() {
    for body in [
        "false and c.label=\"x\"",
        "not c.flag and (if c.flag then c.label=\"x\" else true)",
    ] {
        let original = fixture::sources(
            &[("p", false, "p")],
            &format!(
                "view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {{flag=p}};law required valid(c:Part):{body};"
            ),
        );
        let map=String::from_utf8(original.archmap().bytes().to_vec()).unwrap().replace(r#",{"id":"label-p","subject":"p","field":"Pattern.Part.label","value":"p","origin":"model"}"#,"");
        let input = archsig_input::input::InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            original.law().bytes().to_vec(),
            map.into_bytes(),
        );
        let asks = [
            "old=solve(Selected.valid,using=Selected.choose,on=@v/root)",
            "u=evaluate(Selected.all,r=@v/root)",
            "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
            "s=solve($p.problem,within=$u.value)",
        ];
        let result =
            super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
                .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(result.answers[2].status, Decision::Established);
        assert_eq!(result.answers[3].status, result.answers[0].status);
        let expected = if body.starts_with("false") {
            Decision::Refuted
        } else {
            Decision::Established
        };
        assert_eq!(result.answers[0].status, expected);
    }
}

#[test]
fn a_reachable_unknown_law_row_still_blocks_a_complete_problem() {
    let original = fixture::sources(
        &[("p", false, "p")],
        r#"change choose(c:Part,p:Bool)=c with {flag=p};law required valid(c:Part):c.flag or c.label="x";"#,
    );
    let map=String::from_utf8(original.archmap().bytes().to_vec()).unwrap().replace(r#",{"id":"label-p","subject":"p","field":"Pattern.Part.label","value":"p","origin":"model"}"#,"");
    let input = archsig_input::input::InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        original.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let result = super::super::evaluate_observed_bytes(
        input,
        &["p=prepare(Selected.valid,using=Selected.choose,on=@v/root)"],
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    assert!(!result.answers[0].outputs.contains_key("problem"));
    assert!(result.answers[0].reasons.iter().any(|r| {
        r.missing
            .iter()
            .any(|f| f.subject == "p" && f.field.as_deref() == Some("Pattern.Part.label"))
    }));
}

#[test]
fn localize_and_diagnose_consume_the_selected_values() {
    for using in ["", ",using=Selected.choose"] {
        let input = fixture::sources(
            &[("p", false, "p")],
            "view all(r:Root):Set<Part> =Part[r];view flag(c:Part):Bool=c.flag;change choose(c:Part,p:Bool)=c with {flag=p};law required valid(c:Part):c.flag;",
        );
        let mut asks = vec![
            "u=evaluate(Selected.all,r=@v/root)".to_owned(),
            "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)".into(),
            "s=solve($p.problem,within=$u.value)".into(),
            "c=candidate($s.solutions,index=0)".into(),
            "a=apply($c.assignment,in=$s.solutions)".into(),
        ];
        asks.extend([
            format!("l=localize($a.object,law=Selected.valid{using})"),
            "d=diagnose($l.system,degree=0)".into(),
            "v=evaluate(Selected.flag,c=@v/p,on=$l.system.base)".into(),
        ]);
        let result = super::super::evaluate_observed_bytes(
            input,
            &asks.iter().map(String::as_str).collect::<Vec<_>>(),
            &archsig_common::control::quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert!(
            result
                .answers
                .iter()
                .all(|a| a.status == Decision::Established),
            "{:?}",
            result.issues
        );
    }
}

#[test]
fn assignment_comparison_uses_original_parameters_and_semantic_domains() {
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "c0=candidate($s.solutions,index=0)",
        "c1=candidate($s.solutions,index=1)",
        "same=compare($c0.assignment,to=$c0.assignment,kind=value)",
        "different=compare($c0.assignment,to=$c1.assignment,kind=value)",
        "q=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "t=solve($q.problem,within=$u.value)",
        "d=candidate($t.solutions,index=0)",
        "cross=compare($c0.assignment,to=$d.assignment,kind=value)",
        "old=solve(Selected.valid,using=Selected.choose,on=@v/root)",
        "o=candidate($old.solutions,index=0)",
        "original=compare($c0.assignment,to=$o.assignment,kind=value)",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input(""),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    for i in [5, 10, 13] {
        assert_eq!(result.answers[i].status, Decision::Established);
    }
    assert_eq!(result.answers[6].status, Decision::Refuted);
}

#[test]
fn independent_forall_and_view_factors_keep_linear_relation_storage() {
    for n in [8, 24] {
        let parts = (0..n)
            .map(|i| (format!("p{i:02}"), false, format!("p{i:02}")))
            .collect::<Vec<_>>();
        let refs = parts
            .iter()
            .map(|(a, b, c)| (a.as_str(), *b, c.as_str()))
            .collect::<Vec<_>>();
        for (body, binding) in [
            (
                "law required valid(r:Root):forall c in Part[r]. c.flag=c.flag;",
                "r",
            ),
            (
                "view good(s:Root):Bool=forall c in Part[s]. c.flag=c.flag;law required valid(r:Root):good(r);",
                "r",
            ),
            (
                "law required valid(r:Root):forall c:Part. c.flag=c.flag;",
                "r",
            ),
            (
                "law required valid(r:Root) when r=r:forall c in Part[r]. c.flag=c.flag;",
                "r",
            ),
            (
                "view gate(c:Part):Bool=c.flag;law required valid(r:Root,c:Part):if gate(c) then forall x in Part[r]. x.flag else true;",
                "r",
            ),
        ] {
            let input = fixture::sources(
                &refs,
                &format!("change choose(c:Part,p:Bool)=c with {{flag=p}};{body}"),
            );
            let extra = if body.contains("view gate") {
                ",c=@v/p00"
            } else {
                ""
            };
            let ask = format!(
                "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,{binding}=@v/root{extra})"
            );
            let result = super::super::evaluate_observed_bytes(
                input,
                &[ask.as_str()],
                &archsig_common::control::quiet(),
            )
            .unwrap();
            assert_eq!(result.status(), "complete", "{:?}", result.issues);
            assert_eq!(result.answers[0].status, Decision::Established);
            let shared = data_from(&result, result.answers[0].outputs["problem"])
                .source
                .finite()
                .unwrap();
            if body.contains("view gate") && n == 8 {
                let mut count = 0;
                shared
                    .compiled
                    .relations
                    .visit_solutions(
                        &vec![None; shared.compiled.domains.len()],
                        &archsig_common::control::quiet(),
                        |_: &[usize]| {
                            count += 1;
                            Ok(())
                        },
                    )
                    .unwrap();
                assert_eq!(count, 129);
            }
            let (factors, rows, width) = shared.compiled.relations.relation_shape();
            assert!(
                factors <= 2 * n + 1 && rows <= 8 * n && width <= 2,
                "n={n}, {body}: {factors} factors / {rows} rows / width {width}"
            );
        }
    }
}

#[test]
fn quotient_consumes_factored_solutions_and_the_original_candidate_domain() {
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "q=quotient(Selected.flag,on=$s.solutions,c=@v/q)",
        "all=quotient(Selected.flag,on=$p.problem.domain,c=@v/q)",
        "old=solve(Selected.valid,using=Selected.choose,on=@v/root)",
        "before=quotient(Selected.flag,on=$old.solutions,c=@v/q)",
    ];
    let result = super::super::evaluate_observed_bytes(
        fixture::input(""),
        &asks,
        &archsig_common::control::quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert!(
        result
            .answers
            .iter()
            .all(|a| a.status == Decision::Established)
    );
    let classes = |answer: usize| {
        let at = result.answers[answer].outputs["quotient"];
        let Some(Payload::Construction(v)) = &result.nodes[at.0].payload else {
            panic!()
        };
        let (at, _) = v
            .project(&[ProjectionStep::Field("classes".into())])
            .unwrap();
        let Some(Payload::Construction(v)) = &result.nodes[at.0].payload else {
            panic!()
        };
        let wire = v.wire();
        let Json::Obj(record) = &wire else { panic!() };
        let Some(Json::Arr(values)) = record.get("elements") else {
            panic!()
        };
        values.len()
    };
    assert_eq!(classes(3), 1);
    assert_eq!(classes(4), 2);
    assert_eq!(classes(6), 1);
}

#[test]
fn assignment_comparison_accepts_existing_repair_and_rejects_different_spaces() {
    let input = fixture::sources(
        &[("p", false, "p")],
        "view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {flag=p};change other(c:Part,p:Bool)=c with {flag=p};law required valid(c:Part):c.flag;",
    );
    let asks = [
        "u=evaluate(Selected.all,r=@v/root)",
        "p=prepare(Selected.valid,using=Selected.choose,on=@v/root)",
        "s=solve($p.problem,within=$u.value)",
        "c=candidate($s.solutions,index=0)",
        "r=repair(Selected.valid,using=Selected.choose,on=@v/root)",
        "same=compare($c.assignment,to=$r.repair.parameters,kind=value)",
        "q=prepare(Selected.valid,using=Selected.other,on=@v/root)",
        "t=solve($q.problem,within=$u.value)",
        "d=candidate($t.solutions,index=0)",
        "wrong=compare($c.assignment,to=$d.assignment,kind=value)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(result.answers[5].status, Decision::Established);
    assert_eq!(result.answers[9].status, Decision::Refuted);
    assert!(result.answers[9].reasons.iter().any(|r| matches!(
        r.kind,
        ReasonKind::ConditionFailed {
            construction: "comparison",
            ..
        }
    )));
}

#[test]
fn factored_conditions_and_views_keep_their_lexical_bindings() {
    for body in [
        "law required valid(r:Root):if (forall c in Part[r]. c.flag) then false else (forall c in Part[r]. not c.flag);",
        "view good(s:Root):Bool=forall c in Part[s]. not c.flag;law required valid(r:Root,c:Part):good(r);",
    ] {
        let input = fixture::sources(
            &[("p", false, "p"), ("q", false, "q"), ("t", false, "t")],
            &format!(
                "view all(r:Root):Set<Part> =Part[r];change choose(c:Part,p:Bool)=c with {{flag=p}};{body}"
            ),
        );
        let extra = if body.contains("view good") {
            ",c=@v/p"
        } else {
            ""
        };
        let asks = vec![
            "u=evaluate(Selected.all,r=@v/root)".to_owned(),
            format!("old=solve(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root{extra})"),
            format!("p=prepare(Selected.valid,using=Selected.choose,on=@v/root,r=@v/root{extra})"),
            "s=solve($p.problem,within=$u.value)".into(),
            "a=candidate($old.solutions,index=0)".into(),
            "b=candidate($s.solutions,index=0)".into(),
            "eq=compare($a.assignment,to=$b.assignment,kind=value)".into(),
            "no=candidate($s.solutions,index=1)".into(),
        ];
        let result = super::super::evaluate_observed_bytes(
            input,
            &asks.iter().map(String::as_str).collect::<Vec<_>>(),
            &archsig_common::control::quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        for answer in &result.answers[..7] {
            assert_eq!(
                answer.status,
                Decision::Established,
                "{} {:?}",
                answer.id,
                answer.reasons
            );
        }
        assert_eq!(result.answers[7].status, Decision::Refuted);
    }
}

#[test]
fn existing_complete_solutions_select_without_observing_overwritten_values() {
    let original = fixture::sources(
        &[("p", false, "p")],
        "change choose(c:Part,p:Bool)=c with {flag=p};law required valid(c:Part):c.flag;",
    );
    let map=String::from_utf8(original.archmap().bytes().to_vec()).unwrap().replace(r#",{"id":"flag-p","subject":"p","field":"Pattern.Part.flag","value":false,"origin":"model"}"#,"");
    let input = archsig_input::input::InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        original.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let asks = [
        "s=solve(Selected.valid,using=Selected.choose,on=@v/root)",
        "c=candidate($s.solutions,index=0)",
        "a=apply($c.assignment,in=$s.solutions)",
        "ok=check(Selected.valid,on=$a.object,c=@v/p)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    for answer in &result.answers {
        assert_eq!(
            answer.status,
            Decision::Established,
            "{} {:?}",
            answer.id,
            answer.reasons
        );
    }
}

#[test]
fn prepared_input_family_keeps_each_completion_and_uniform_assignments_distinct() {
    for known in [false, true] {
        let original = fixture::sources(
            &[("p", true, "p"), ("q", false, "q")],
            "view all(r:Root):Set<Part> =Part[r];view input(c:Part):Bool=c.flag;change choose(c:Part,p:Bool)=c with {flag=if p then c.flag else not c.flag};law required valid(c:Part):c.flag;",
        );
        let map = String::from_utf8(original.archmap().bytes().to_vec()).unwrap();
        let map = if known {
            map
        } else {
            map.replace(r#",{"id":"flag-q","subject":"q","field":"Pattern.Part.flag","value":false,"origin":"model"}"#,"")
        };
        let input = archsig_input::input::InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            original.law().bytes().to_vec(),
            map.into_bytes(),
        );
        let asks = [
            "u=evaluate(Selected.all,r=@v/root)",
            "p=prepare(Selected.valid,using=Selected.choose,on=@v/root,inputs=Selected.input,c=@v/q)",
            "s=solve($p.problem,within=$u.value)",
        ];
        let result =
            super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
                .unwrap();
        assert_eq!(result.status(), "complete", "{:?}", result.issues);
        assert_eq!(
            result.answers[1].status,
            Decision::Established,
            "{:?}",
            result.answers[1].reasons
        );
        let d = data_from(&result, result.answers[1].outputs["problem"]);
        let shared = d.source.finite().unwrap();
        let (family, _) = shared.family.as_ref().unwrap();
        assert_eq!(family.points.len(), if known { 1 } else { 2 });
        assert!(family.variants.iter().all(|v| {
            v.relations
                .exists(
                    &vec![None; v.relations.variables()],
                    &archsig_common::control::quiet(),
                )
                .unwrap()
        }));
        assert_eq!(
            result.answers[2].status,
            if known {
                Decision::Established
            } else {
                Decision::Refuted
            }
        );
    }
}
