fn witness_example(script: &str, asks: &[&str]) -> ObservedEvaluation {
    let result =
        evaluate_observed_bytes(finite_completion_fixture(script, false), asks, &quiet()).unwrap();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    assert_known_answer_raw(&result);
    result
}
fn witness_pair(result: &ObservedEvaluation, answer: usize) -> NodeRef {
    *result.answers[answer]
        .evidence
        .iter()
        .find(|r| {
            matches!(
                result.nodes[r.0].payload,
                Some(Payload::CompletionPair { .. })
            )
        })
        .expect("supplemental pair")
}
#[test]
fn completion_witness_keeps_original_whole_parts_claim_and_needed_without_full_domain() {
    let result = witness_example(
        "law required current(s:Sample):count(s.k)=1;",
        &[
            "current=check(Calc.current,s=@v/sample)",
            "plan=needed($current)",
        ],
    );
    let answer = &result.answers[0];
    assert_eq!(answer.status, Decision::Undetermined);
    let root = answer.outputs["evaluation"];
    let pair = witness_pair(&result, 0);
    assert!(!matches!(
        result.nodes[result.nodes[root.0].arguments[0].0].payload,
        Some(Payload::CompletionSeed { .. })
    ));
    assert!(
        result
            .cases
            .iter()
            .all(|case| case.origin == crate::observed::call::CompletionOrigin::Assignment)
    );
    assert!(
        !result
            .nodes
            .iter()
            .any(|n| matches!(n.payload, Some(Payload::Domain { .. })))
    );
    let claim = &result.nodes[answer.claim.unwrap().0];
    assert!(claim.evidence.is_empty());
    assert_eq!(answer.evidence, vec![pair]);
    let Some(Payload::CompletionPair {
        first_result,
        second_result,
        ..
    }) = &result.nodes[pair.0].payload
    else {
        unreachable!();
    };
    let values = [first_result, second_result].map(|r| {
        let Some(Payload::Evaluation { value: Some(v), .. }) = &result.nodes[r.0].payload else {
            panic!("known whole");
        };
        data_scalar_at(&result, v.0).clone()
    });
    assert_eq!(values, [Scalar::Bool(false), Scalar::Bool(true)]);
    let plan = result.answers[1].outputs["plan"];
    assert!(
        matches!(&result.nodes[plan.0].payload,Some(Payload::ObservationPlan{requirements,blockers,..}) if requirements.len()==1 && blockers.is_empty())
    );
    recheck_mutation(&result, |nodes| nodes[pair.0].scope.completions = false);
    recheck_mutation(&result, |nodes| {
        let Some(Payload::CompletionPair {
            first_result,
            second_result,
            ..
        }) = &mut nodes[pair.0].payload
        else {
            unreachable!();
        };
        *second_result = *first_result;
    });
    let member = result.cases[0].member;
    recheck_mutation(&result, |nodes| {
        nodes[member.0].payload = Some(Payload::scalar(Scalar::Bool(false)));
        nodes[member.0].ty = NodeType::Value(Type::Bool);
    });
}
#[test]
fn completion_witness_separates_unknown_if_branch_proposals_and_real_binders() {
    let result = witness_example(
        "law required current(s:Sample):if s.o=none<Bool> then count(s.k)=1 else count(s.k)=0;",
        &["current=check(Calc.current,s=@v/sample)"],
    );
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    let pair = witness_pair(&result, 0);
    let root = result.answers[0].outputs["evaluation"];
    assert!(!matches!(
        result.nodes[result.nodes[root.0].arguments[0].0].payload,
        Some(Payload::CompletionSeed { .. })
    ));
    assert!(result.nodes[pair.0].reasons.iter().any(|r| {
        r.missing
            .iter()
            .any(|f| f.field.as_deref() == Some("ClosedValue.Sample.o"))
    }));
}
#[test]
fn completion_witness_rejects_other_request_and_forged_answer_scope_and_prefix() {
    let result = witness_example(
        "law required current(s:Sample):count(s.k)=1;",
        &[
            "one=check(Calc.current,s=@v/sample)",
            "two=check(Calc.current,s=@v/sample)",
        ],
    );
    let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let control = quiet();
    let environment = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &control,
    )
    .unwrap();
    let pair = witness_pair(&result, 1);
    let mut wrong = result.answers[0].clone();
    wrong.evidence.push(pair);
    assert!(
        environment
            .validate_answer(&graph, &result.prepared.requests().requests()[0], &wrong)
            .is_err()
    );
    let mut wrong = result.answers[0].clone();
    wrong.scope.snapshots.insert("foreign".into());
    assert!(
        environment
            .validate_answer(&graph, &result.prepared.requests().requests()[0], &wrong)
            .is_err()
    );
    let mut wrong = result.answers[0].clone();
    wrong.status = Decision::Refuted;
    assert!(
        environment
            .validate_answer(&graph, &result.prepared.requests().requests()[0], &wrong)
            .is_err()
    );
}
#[test]
fn completion_witness_equal_sets_and_unknown_wholes_keep_existing_full_fallback() {
    let result = witness_example(
        "view current(s:Sample):Set<Bool>=set<Bool>{count(s.k)=0,count(s.k)!=0};"
            .replace(">=", "> =")
            .as_str(),
        &["current=evaluate(Calc.current,s=@v/sample)"],
    );
    assert_eq!(result.answers[0].status, Decision::Established);
    assert!(result.answers[0].evidence.iter().any(|r| matches!(
        result.nodes[r.0].payload,
        Some(Payload::FiniteExhaustion { checked: 4, .. })
    )));
    assert!(
        result
            .cases
            .iter()
            .any(|c| matches!(c.origin, crate::observed::call::CompletionOrigin::Domain(_)))
    );
    let result = evaluate_observed_bytes(
        finite_completion_fixture(
            "law required current(s:Sample):count(s.k)=1 or s.q>rat(0,1);",
            true,
        ),
        &["current=check(Calc.current,s=@v/sample)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        result.answers[0].status,
        Decision::Undetermined,
        "{:?}",
        result.issues
    );
    assert!(!result.answers[0].evidence.iter().any(|r| matches!(
        result.nodes[r.0].payload,
        Some(Payload::CompletionPair { .. })
    )));
    assert_known_answer_raw(&result);
}
#[test]
fn completion_witness_stop_after_first_known_whole_keeps_original_undetermined() {
    use std::{cell::Cell, rc::Rc};
    for signal in [Signal::Int, Signal::Term] {
        let stopped = Rc::new(Cell::new(false));
        let flag = stopped.clone();
        let control = Control::new(move |_| flag.get().then_some(signal));
        let trigger = stopped.clone();
        data::observe_iterations(move |_, _, phase, index| {
            if phase == "completion_probe_whole" && index == 0 {
                trigger.set(true);
            }
        });
        let result = evaluate_observed_bytes(
            finite_completion_fixture("law required current(s:Sample):count(s.k)=1;", false),
            &["current=check(Calc.current,s=@v/sample)"],
            &control,
        )
        .unwrap();
        data::clear_iteration_observer();
        assert_eq!(result.answers[0].status, Decision::Undetermined);
        assert!(result.answers[0].evidence.is_empty());
        assert!(
            result.answers[0]
                .reasons
                .iter()
                .any(|r| matches!(r.kind,ReasonKind::Stop(s) if s==signal))
        );
        let root = result.answers[0].outputs["evaluation"];
        assert!(matches!(
            result.nodes[root.0].payload,
            Some(Payload::Evaluation { value: None, .. })
        ));
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
}

fn witness_extended_fixture(script: &str, refs: bool, peer: bool) -> InputSources {
    let input = finite_completion_fixture(script, false);
    let original = std::str::from_utf8(input.definitions()[0].bytes()).unwrap();
    let old = archsig_input::definition::check_definitions(&[("definition0", original.as_bytes())])
        .unwrap();
    let mut definitions=original.replace("{\"name\":\"q\",",r#"{"name":"j","type":["Set","Bool"],"meaning":"第二の集合。"},{"name":"l","type":["Set","Bool"],"meaning":"第三の集合。"},{"name":"q","#);
    if refs {
        definitions = definitions.replace(
            r#""name":"k","type":["Set","Bool"]"#,
            r#""name":"k","type":["Set",["Ref","ClosedValue.Sample"]]"#,
        );
    }
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
    let old_digest = &old.vocabularies()["ClosedValue"].digest;
    let digest = &checked.vocabularies()["ClosedValue"].digest;
    let law = std::str::from_utf8(input.law().bytes())
        .unwrap()
        .replace(old_digest, digest);
    let mut map = std::str::from_utf8(input.archmap().bytes())
        .unwrap()
        .replace(old_digest, digest);
    if peer {
        map=map.replace(r#""snapshots":["#,r#""snapshots":[{"id":"w","origin":"base","subjects":[{"id":"peer","type":"ClosedValue.Sample","origin":"base"}],"atoms":[]},"#);
    }
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
#[test]
fn completion_witness_branch_goals_require_a_real_same_branch_joint_assignment() {
    let input = witness_extended_fixture(
        "law required current(s:Sample):if s.o=none<Bool> then count(s.k)=1 and count(s.j)=1 and count(s.l)=0 else count(s.k)=0 and count(s.j)=0 and count(s.l)=1;",
        false,
        false,
    );
    let result = evaluate_observed_bytes(
        input,
        &["current=check(Calc.current,s=@v/sample)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        result.answers[0].status,
        Decision::Undetermined,
        "{:?}",
        result.issues
    );
    let pair = witness_pair(&result, 0);
    assert!(
        result
            .cases
            .iter()
            .all(|case| case.origin == crate::observed::call::CompletionOrigin::Assignment)
    );
    let Some(Payload::CompletionPair {
        fields,
        first,
        second,
        first_result,
        second_result,
    }) = &result.nodes[pair.0].payload
    else {
        unreachable!();
    };
    for (values, whole) in [(first, first_result), (second, second_result)] {
        let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &result.nodes[whole.0].payload
        else {
            unreachable!();
        };
        if data_scalar_at(&result, value.0) == &Scalar::Bool(true) {
            for (field, reference) in fields.iter().zip(values) {
                if let Some(name) = field.field.as_deref()
                    && [
                        "ClosedValue.Sample.k",
                        "ClosedValue.Sample.j",
                        "ClosedValue.Sample.l",
                    ]
                    .contains(&name)
                {
                    let Scalar::Set { items, .. } = data_scalar_at(&result, reference.0) else {
                        panic!("typed set");
                    };
                    assert_eq!(items.len(), usize::from(name != "ClosedValue.Sample.l"));
                }
            }
        }
    }
    assert_known_answer_raw(&result);
}
#[test]
fn completion_witness_retains_new_missing_dependencies_and_additional_snapshot_scope() {
    let input = witness_extended_fixture(
        "law required current(s:Sample):count(s.k)=1 and (exists r in s.k . r.o=none<Bool> or true);",
        true,
        true,
    );
    let result = evaluate_observed_bytes(
        input,
        &[
            "current=check(Calc.current,s=@v/sample)",
            "plan=needed($current)",
        ],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        result.answers[0].status,
        Decision::Undetermined,
        "{:?}",
        result.issues
    );
    let pair = witness_pair(&result, 0);
    let answer = &result.answers[0];
    let root = &result.nodes[answer.outputs["evaluation"].0];
    assert!(!root.scope.snapshots.contains("w"));
    assert!(answer.scope.snapshots.contains("w"));
    assert!(result.nodes[pair.0].reasons.iter().any(|reason| {
        reason
            .missing
            .iter()
            .any(|f| f.snapshot == "w" && f.field.as_deref() == Some("ClosedValue.Sample.o"))
    }));
    let plan = answer.outputs.get("plan");
    assert!(plan.is_none());
    let plan = result.answers[1].outputs["plan"];
    assert!(
        matches!(&result.nodes[plan.0].payload,Some(Payload::ObservationPlan{requirements,..}) if requirements.len()==1 && requirements[0].wire().canonical().contains("ClosedValue.Sample.k"))
    );
    assert!(!answer.reasons.iter().any(|reason| {
        reason
            .missing
            .iter()
            .any(|f| f.snapshot == "w" && f.field.as_deref() == Some("ClosedValue.Sample.o"))
    }));
    let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let control = quiet();
    let env = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &control,
    )
    .unwrap();
    let mut polluted = answer.clone();
    polluted
        .reasons
        .extend(result.nodes[pair.0].reasons.iter().cloned());
    sort_reasons(&mut polluted.reasons);
    assert!(
        env.validate_answer(&graph, &result.prepared.requests().requests()[0], &polluted)
            .is_err()
    );
    assert_known_answer_raw(&result);
}

fn witness_owned_fixture() -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Witness","version":"1","dependencies":[],"declarations":[
{"kind":"entity","name":"Witness.Root","meaning":"所有者。","parameters":[],"fields":[],"alignments":[]},
{"kind":"entity","name":"Witness.Item","meaning":"所属する対象。","parameters":[{"name":"owner","type":["Ref","Witness.Root"],"meaning":"所有者。"}],"fields":[],"alignments":[]},
{"kind":"entity","name":"Witness.Holder","meaning":"集合と全域写像。","parameters":[{"name":"owner","type":["Ref","Witness.Root"],"meaning":"所有者。"}],"fields":[{"name":"items","type":["Set",["Owned","Witness.Item","owner"]],"meaning":"欠測集合。"},{"name":"table","type":["Map",["Owned","Witness.Item","owner"],["Owned","Witness.Item","owner"]],"meaning":"既知全域写像。"}],"alignments":[]}]}]}"#;
    let definitions_checked =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
    let digest = &definitions_checked.vocabularies()["Witness"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";reading Calc{{use vocabulary Witness version "1" digest "{digest}";law required current(h:Holder):count(h.items)=1;}}"#
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Witness","version":"1","digest":"{digest}"}}],"sources":[{{"id":"src","uri":"urn:witness:owned","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"origin","mode":"observed","method":"型と所属を読む。","locations":[{{"source":"src","path":"owned","span":[0,1]}}]}}],"snapshots":[{{"id":"v","origin":"origin","subjects":[{{"id":"A","type":"Witness.Root","origin":"origin"}},{{"id":"B","type":"Witness.Root","origin":"origin"}},{{"id":"a","type":"Witness.Item","origin":"origin"}},{{"id":"b","type":"Witness.Item","origin":"origin"}},{{"id":"h","type":"Witness.Holder","origin":"origin"}}],"atoms":[{{"id":"aowner","subject":"a","field":"Witness.Item.owner","value":["v","A"],"origin":"origin"}},{{"id":"bowner","subject":"b","field":"Witness.Item.owner","value":["v","B"],"origin":"origin"}},{{"id":"howner","subject":"h","field":"Witness.Holder.owner","value":["v","B"],"origin":"origin"}},{{"id":"table","subject":"h","field":"Witness.Holder.table","value":[[["v","b"],["v","b"]]],"origin":"origin"}}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
#[test]
fn completion_witness_owned_set_uses_observed_owner_and_rejects_other_owner_and_map_root() {
    let result = evaluate_observed_bytes(
        witness_owned_fixture(),
        &["current=check(Calc.current,h=@v/h)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        result.answers[0].status,
        Decision::Undetermined,
        "{:?}",
        result.issues
    );
    let pair = witness_pair(&result, 0);
    assert_known_answer_raw(&result);
    let Some(Payload::CompletionPair { second_result, .. }) = &result.nodes[pair.0].payload else {
        unreachable!();
    };
    let case = &result.cases[result.contexts[second_result.0].case.unwrap()];
    let member = case.member;
    recheck_mutation(&result, |nodes| {
        let Some(value) = nodes[member.0].scalar_payload_mut() else {
            unreachable!();
        };
        let Scalar::Set { items, .. } = value else {
            unreachable!();
        };
        items[0] = Scalar::Subject {
            snapshot: "v".into(),
            subject: "a".into(),
            entity: "Witness.Item".into(),
        };
    });
    // 元の全域Mapが読む所属を変えても、同じ補助対を再利用できない。
    let inputs = witness_owned_fixture();
    let map = std::str::from_utf8(inputs.archmap().bytes())
        .unwrap()
        .replace(
            r#""subject":"h","field":"Witness.Holder.owner","value":["v","B"]"#,
            r#""subject":"h","field":"Witness.Holder.owner","value":["v","A"]"#,
        );
    assert!(
        prepare_observed(
            InputSources::from_bytes(
                inputs
                    .definitions()
                    .iter()
                    .map(|d| d.bytes().to_vec())
                    .collect(),
                inputs.law().bytes().to_vec(),
                map.into_bytes()
            ),
            &["current=check(Calc.current,h=@v/h)"],
            &quiet()
        )
        .is_err()
    );
}
#[test]
fn completion_witness_stop_before_pair_and_after_pair_commit_preserves_only_checked_answer() {
    use std::{cell::Cell, rc::Rc};
    for (phase, committed) in [
        ("completion_probe_pair", false),
        ("completion_probe_committed", true),
    ] {
        for signal in [Signal::Int, Signal::Term] {
            let stopped = Rc::new(Cell::new(false));
            let flag = stopped.clone();
            let control = Control::new(move |_| flag.get().then_some(signal));
            let trigger = stopped.clone();
            data::observe_iterations(move |_, _, actual, _| {
                if actual == phase {
                    trigger.set(true);
                }
            });
            let result = evaluate_observed_bytes(
                finite_completion_fixture("law required current(s:Sample):count(s.k)=1;", false),
                &["current=check(Calc.current,s=@v/sample)"],
                &control,
            )
            .unwrap();
            data::clear_iteration_observer();
            assert_eq!(result.answers[0].status, Decision::Undetermined);
            assert_eq!(
                result.answers[0].evidence.iter().any(|r| matches!(
                    result.nodes[r.0].payload,
                    Some(Payload::CompletionPair { .. })
                )),
                committed
            );
            assert!(
                result.answers[0]
                    .reasons
                    .iter()
                    .any(|r| matches!(r.kind,ReasonKind::Stop(s) if s==signal))
            );
            rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        }
    }
}

#[test]
fn completion_witness_does_not_generalize_two_applicable_guards_or_original_body() {
    let result = witness_example(
        "law required current(s:Sample) when s.o=none<Bool>:count(s.k)=1;",
        &["current=check(Calc.current,s=@v/sample)"],
    );
    let pair = witness_pair(&result, 0);
    let root = &result.nodes[result.answers[0].outputs["evaluation"].0];
    let Some(Payload::Evaluation {
        parts,
        applicability,
        ..
    }) = &root.payload
    else {
        unreachable!();
    };
    assert_eq!(*applicability, "undetermined");
    assert_eq!(parts.len(), 2);
    assert!(parts.iter().all(|part| part.value.is_none()));
    let Some(Payload::CompletionPair {
        first_result,
        second_result,
        ..
    }) = &result.nodes[pair.0].payload
    else {
        unreachable!();
    };
    for reference in [first_result, second_result] {
        assert!(matches!(
            &result.nodes[reference.0].payload,
            Some(Payload::Evaluation {
                applicability: "applicable",
                ..
            })
        ));
    }
    assert!(
        result
            .cases
            .iter()
            .all(|case| case.origin == crate::observed::call::CompletionOrigin::Assignment)
    );
}

#[test]
fn completion_witness_zero_count_owned_set_has_legal_true_and_false_points_and_public_projection() {
    let input = witness_owned_fixture();
    let law = std::str::from_utf8(input.law().bytes())
        .unwrap()
        .replace("count(h.items)=1", "count(h.items)=0");
    let input = InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        input.archmap().bytes().to_vec(),
    );
    let result =
        evaluate_observed_bytes(input, &["current=check(Calc.current,h=@v/h)"], &quiet()).unwrap();
    assert_eq!(
        result.answers[0].status,
        Decision::Undetermined,
        "{:?}",
        result.issues
    );
    let pair = witness_pair(&result, 0);
    assert!(
        result
            .cases
            .iter()
            .all(|c| c.origin == crate::observed::call::CompletionOrigin::Assignment)
    );
    let Some(Payload::CompletionPair {
        first_result,
        second_result,
        ..
    }) = &result.nodes[pair.0].payload
    else {
        unreachable!();
    };
    for (reference, expected) in [(first_result, true), (second_result, false)] {
        let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &result.nodes[reference.0].payload
        else {
            unreachable!();
        };
        assert_eq!(data_scalar_at(&result, value.0), &Scalar::Bool(expected));
    }
    assert_known_answer_raw(&result);
    let archsig_common::canonical::Json::Obj(ref wire) = result.result_wire() else {
        panic!("public object");
    };
    let archsig_common::canonical::Json::Arr(answers) = &wire["answers"] else {
        panic!("public answers");
    };
    let archsig_common::canonical::Json::Obj(answer) = &answers[0] else {
        panic!("public answer");
    };
    assert!(answer.contains_key("counterexamples"));
}
#[test]
fn completion_witness_missing_option_filter_gets_real_binder_reference_proposals() {
    let input = witness_owned_fixture();
    let original = std::str::from_utf8(input.definitions()[0].bytes()).unwrap();
    let definitions=original.replace(r#"{"name":"items","# ,r#"{"name":"marker","type":["Option",["Owned","Witness.Item","owner"]],"meaning":"欠測参照。"},{"name":"items","#);
    let old = archsig_input::definition::check_definitions(&[("definition0", original.as_bytes())])
        .unwrap();
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
    let from = &old.vocabularies()["Witness"].digest;
    let to = &checked.vocabularies()["Witness"].digest;
    let law=std::str::from_utf8(input.law().bytes()).unwrap().replace(from,to).replace("law required current(h:Holder):count(h.items)=1;","view choices(h:Holder):Set<Item>=set {r | r in Item[h.owner] where h.marker=some(r)}; law required current(h:Holder):count(h.items)=0 and (exists r in choices(h) . true);").replace(">=","> =");
    let map = std::str::from_utf8(input.archmap().bytes())
        .unwrap()
        .replace(from, to);
    let result = evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![definitions.into_bytes()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &["current=check(Calc.current,h=@v/h)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        result.answers[0].status,
        Decision::Undetermined,
        "{:?}",
        result.issues
    );
    witness_pair(&result, 0);
    assert!(
        result
            .cases
            .iter()
            .all(|c| c.origin == crate::observed::call::CompletionOrigin::Assignment)
    );
    assert_known_answer_raw(&result);
}

// ローカル調査専用。入力pathと問いを環境から選び、全域列挙の前に必ず停止する。
#[test]
fn completion_witness_option_filter_discovers_nested_set_and_preserves_selected_assignment() {
    witness_option_filter_nested_set("Bool");
}
#[test]
fn completion_witness_option_filter_discovers_nonfinite_text_set() {
    witness_option_filter_nested_set("Text");
}
fn witness_option_filter_nested_set(element: &str) {
    use std::{cell::RefCell, rc::Rc};
    let input = witness_owned_fixture();
    let original = std::str::from_utf8(input.definitions()[0].bytes()).unwrap();
    let mut definitions=original.replace(r#"{"name":"items","#,r#"{"name":"marker","type":["Option",["Owned","Witness.Item","owner"]],"meaning":"欠測参照。"},{"name":"items","#);
    let item = definitions.find(r#""name":"Witness.Item""#).unwrap();
    let start = item + definitions[item..].find(r#""fields":[]"#).unwrap();
    definitions.replace_range(
        start..start + r#""fields":[]"#.len(),
        &format!(r#""fields":[{{"name":"tokens","type":["Set","{element}"],"meaning":"選択後に読む集合。"}}]"#),
    );
    let old = archsig_input::definition::check_definitions(&[("definition0", original.as_bytes())])
        .unwrap();
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
    let from = &old.vocabularies()["Witness"].digest;
    let to = &checked.vocabularies()["Witness"].digest;
    let law=std::str::from_utf8(input.law().bytes()).unwrap().replace(from,to).replace("law required current(h:Holder):count(h.items)=1;","view choices(h:Holder):Set<Item>=set {r | r in Item[h.owner] where h.marker=some(r)}; law required current(h:Holder):exists r in choices(h) . count(r.tokens)=0;").replace(">=","> =");
    let map = std::str::from_utf8(input.archmap().bytes())
        .unwrap()
        .replace(from, to);
    let events = Rc::new(RefCell::new(Vec::new()));
    let record = events.clone();
    data::observe_iterations(move |_, _, phase, _| {
        if phase.starts_with("completion_") {
            record.borrow_mut().push(phase);
        }
    });
    let result = evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![definitions.into_bytes()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &[
            "current=check(Calc.current,h=@v/h)",
            "plan=needed($current)",
        ],
        &quiet(),
    )
    .unwrap();
    data::clear_iteration_observer();
    assert_eq!(
        result.answers[0].status,
        Decision::Undetermined,
        "{:?}",
        result.issues
    );
    let pair = witness_pair(&result, 0);
    assert!(events.borrow().contains(&"completion_probe_discovered"));
    assert!(!events.borrow().contains(&"completion_before_full_domain"));
    assert!(
        result
            .cases
            .iter()
            .all(|case| case.origin == crate::observed::call::CompletionOrigin::Assignment)
    );
    let Some(Payload::CompletionPair {
        fields,
        first,
        second,
        ..
    }) = &result.nodes[pair.0].payload
    else {
        unreachable!();
    };
    let marker = fields
        .iter()
        .position(|field| field.field.as_deref() == Some("Witness.Holder.marker"))
        .unwrap();
    for values in [first, second] {
        assert!(
            matches!(data_scalar_at(&result,values[marker].0),Scalar::Option{value:Some(item),..} if matches!(item.as_ref(),Scalar::Subject{subject,..} if subject=="b"))
        );
    }
    assert!(
        fields
            .iter()
            .any(|field| field.subject == "b"
                && field.field.as_deref() == Some("Witness.Item.tokens"))
    );
    assert_known_answer_raw(&result);
}

#[test]
fn completion_witness_nonfinite_text_set_points_are_typed_and_never_full_domain() {
    for count in [0, 1] {
        let input = finite_completion_fixture(
            &format!("law required current(s:Sample):count(s.k)={count};"),
            false,
        );
        let original = std::str::from_utf8(input.definitions()[0].bytes()).unwrap();
        let definitions = original.replace(r#"["Set","Bool"]"#, r#"["Set","Text"]"#);
        let old =
            archsig_input::definition::check_definitions(&[("definition0", original.as_bytes())])
                .unwrap();
        let new = archsig_input::definition::check_definitions(&[(
            "definition0",
            definitions.as_bytes(),
        )])
        .unwrap();
        let from = &old.vocabularies()["ClosedValue"].digest;
        let to = &new.vocabularies()["ClosedValue"].digest;
        let result = evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![definitions.into_bytes()],
                std::str::from_utf8(input.law().bytes())
                    .unwrap()
                    .replace(from, to)
                    .into_bytes(),
                std::str::from_utf8(input.archmap().bytes())
                    .unwrap()
                    .replace(from, to)
                    .into_bytes(),
            ),
            &[
                "current=check(Calc.current,s=@v/sample)",
                "plan=needed($current)",
            ],
            &quiet(),
        )
        .unwrap();
        assert_eq!(
            result.answers[0].status,
            Decision::Undetermined,
            "{:?}",
            result.issues
        );
        let pair = witness_pair(&result, 0);
        let Some(Payload::CompletionPair {
            first,
            second,
            first_result,
            second_result,
            ..
        }) = &result.nodes[pair.0].payload
        else {
            unreachable!()
        };
        assert!(
            matches!(data_scalar_at(&result,first[0].0), Scalar::Set{element:Type::Text,items} if items.is_empty())
        );
        assert!(
            matches!(data_scalar_at(&result,second[0].0), Scalar::Set{element:Type::Text,items} if items==&[Scalar::Text(String::new())])
        );
        let truth = [first_result, second_result].map(|r| {
            let Some(Payload::Evaluation { value: Some(v), .. }) = &result.nodes[r.0].payload
            else {
                panic!("whole must be known")
            };
            data_scalar_at(&result, v.0).clone()
        });
        assert_eq!(truth, [Scalar::Bool(count == 0), Scalar::Bool(count == 1)]);
        assert!(!result.nodes.iter().any(|n| matches!(
            n.payload,
            Some(Payload::Domain { .. } | Payload::FiniteExhaustion { .. })
        )));
        assert_known_answer_raw(&result);
        let seed = result.cases[0].seed;
        recheck_mutation(&result, |nodes| {
            let Some(Payload::CompletionSeed { mode, .. }) = &mut nodes[seed.0].payload else {
                unreachable!()
            };
            *mode = crate::observed::call::CompletionMode::FiniteDomain;
        });
        let member = result.cases[0].member;
        recheck_mutation(&result, |nodes| {
            nodes[member.0].payload = Some(Payload::scalar(Scalar::Set {
                element: Type::Bool,
                items: vec![],
            }));
            nodes[member.0].ty = NodeType::Value(Type::Set(Box::new(Type::Bool)));
        });
    }
}
