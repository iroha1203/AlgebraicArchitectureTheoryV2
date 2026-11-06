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
            D::SharedRepair(d) => d.source.shared.as_ref().unwrap(),
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
            let s = d.source.shared.as_ref().unwrap();
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
        d.source.shared.as_ref().unwrap()
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
fn nonfinite_candidate_and_prepare_are_unsupported_without_blocking_independent_checks() {
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
        "later=check(CountCheck.nonnegative,s=@v/s)",
    ];
    let result =
        super::super::evaluate_observed_bytes(input, &asks, &archsig_common::control::quiet())
            .unwrap();
    assert_eq!(result.status(), "partial", "{:?}", result.issues);
    assert_eq!(result.answers[0].status, Decision::Established);
    assert_eq!(result.answers[1].status, Decision::Undetermined);
    assert!(
        result.answers[1]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
    );
    assert_eq!(result.answers[2].status, Decision::Established);
}
