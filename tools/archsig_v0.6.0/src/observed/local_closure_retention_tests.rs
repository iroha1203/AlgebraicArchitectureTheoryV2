//! Localizeの全協調中断位置で、確定Contextの値と依存を正常実行と照合する。
use super::{
    construction_result::ConstructionType,
    control::{Checkpoint, Control, Limits, Usage},
    evaluate::evaluate_observed,
    input::{InputSources, check_inputs},
    prepare_shared_observed,
    result::{Decision, NodeRef, NodeType, ObservedEvaluation, Payload, ReasonKind},
};
use crate::{canonical::Json, definition, result::Signal};
use std::{cell::Cell, collections::BTreeSet, rc::Rc, sync::Arc};

fn inputs(finite: bool) -> InputSources {
    let definition = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Fixed","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Fixed.State","meaning":"固定状態。","parameters":[],"fields":[{"name":"flag","type":"Bool","meaning":"観測値。"},{"name":"other","type":"Bool","meaning":"別の観測値。"}],"alignments":[]}]}]}"#;
    let checked = definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Fixed"].digest;
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Fixed","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"固定状態の独立試験。","locations":[],"note":"観測有無を分ける試験モデル。"}}],"snapshots":[{{"id":"fixed","origin":"model","subjects":[{{"id":"s","type":"Fixed.State","origin":"model"}}],"atoms":[{{"id":"other","subject":"s","field":"Fixed.State.other","value":true,"origin":"model"}},{{"id":"f","subject":"s","field":"Fixed.State.flag","value":true,"origin":"model"}}]}}]}}"#
    );
    let change = if finite {
        "change choose(t:State,b:Bool,c:Bool)=t with {flag=b,other=c};"
    } else {
        ""
    };
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Fixed {{ use vocabulary Fixed version \"1\" digest \"{digest}\"; law required valid(s:State):s.flag=true; law required second(s:State):s.other=true; {change} view current(s:State):Bool=s.flag; }}"
    );
    InputSources::from_bytes(
        vec![definition.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

// native値は実行ごとのArc identityを持つため、値・型・由来・依存を比較する。
// 全resultのJSON化や再parseはしない。依存先も同じ正常実行の型付きDAGから読む。
fn assert_fragment(normal: &ObservedEvaluation, partial: &ObservedEvaluation, roots: Vec<NodeRef>) {
    let mut pending = roots;
    let mut visited = BTreeSet::new();
    while let Some(reference) = pending.pop() {
        if !visited.insert(reference.0) {
            continue;
        }
        let actual = &partial.nodes[reference.0];
        let expected = &normal.nodes[reference.0];
        let mut actual_metadata = actual.clone();
        let mut expected_metadata = expected.clone();
        actual_metadata.payload = None;
        expected_metadata.payload = None;
        assert_eq!(
            actual_metadata, expected_metadata,
            "fragment n{}",
            reference.0
        );
        match (&actual.payload, &expected.payload) {
            (Some(Payload::Construction(a)), Some(Payload::Construction(b))) => {
                assert_eq!(a.wire(), b.wire(), "value n{}", reference.0);
                assert_eq!(
                    a.arguments(),
                    b.arguments(),
                    "value dependencies n{}",
                    reference.0
                );
                pending.extend(a.arguments());
            }
            (a, b) => assert_eq!(a, b, "payload n{}", reference.0),
        }
        pending.extend(actual.arguments.iter().copied());
        pending.extend(actual.evidence.iter().copied());
        pending.extend(actual.conditions());
        for reason in &actual.reasons {
            pending.extend(reason.dependencies.iter().copied());
        }
        if let Some(judgment) = &actual.judgment {
            pending.extend(judgment.evidence.iter().copied());
            for reason in &judgment.reasons {
                pending.extend(reason.dependencies.iter().copied());
            }
        }
    }
}

#[test]
fn support_closure_all_stops_preserve_completed_context_values_and_dependencies() {
    for finite in [false, true] {
        let asks = [
            "a=build(Fixed,on=@fixed/s)",
            if finite {
                "l=localize($a.object,using=Fixed.choose)"
            } else {
                "l=localize($a.object)"
            },
        ];
        let mut setup = Control::new(Limits::default(), |_| Usage::default());
        let checked = Arc::new(check_inputs(inputs(finite), &mut setup).unwrap());
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let mut control = Control::new(Limits::default(), move |point| {
            if point == Checkpoint::Localize {
                count.set(count.get() + 1);
            }
            Usage::default()
        });
        let prepared = prepare_shared_observed(checked.clone(), &asks, &mut control).unwrap();
        let normal = evaluate_observed(prepared, &mut control).unwrap();
        assert_eq!(normal.status(), "complete");
        assert!(normal.answers[1].outputs.contains_key("system"));
        let total = seen.get();
        assert!(total > 0);
        let mut retained = false;
        let mut completed = false;
        // 全位置を維持する。Context確定前後・closure→Systemの間も省略しない。
        // total+1は全Localizeを通過したcommit後の正常結果を照合する。
        for stop in 1..=total + 1 {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let mut control = Control::new(Limits::default(), move |point| {
                if point == Checkpoint::Localize {
                    count.set(count.get() + 1);
                }
                Usage {
                    signal: (count.get() >= stop).then_some(Signal::Term),
                    ..Usage::default()
                }
            });
            let prepared = prepare_shared_observed(checked.clone(), &asks, &mut control).unwrap();
            let partial = evaluate_observed(prepared, &mut control).unwrap();
            assert_eq!(seen.get(), stop.min(total));
            let answer = &partial.answers[1];
            assert!(
                answer
                    .reasons
                    .iter()
                    .all(|r| !matches!(r.kind, ReasonKind::Internal(_)))
            );
            if stop <= total {
                let reason = control.stop_reason().expect("停止probeが実発火する");
                assert!(
                    answer
                        .reasons
                        .iter()
                        .any(|r| matches!(&r.kind, ReasonKind::Stop(s) if *s == reason)),
                    "finite={finite}, stop={stop}/{total}"
                );
            } else {
                assert!(control.stop_reason().is_none());
                assert_eq!(answer, &normal.answers[1]);
                completed = true;
            }
            let mut fragments = vec![];
            for (index, n) in partial.nodes.iter().enumerate() {
                if n.ty != NodeType::Construction(ConstructionType::Context) {
                    continue;
                }
                let Some(Payload::Construction(value)) = &n.payload else {
                    panic!("Context value");
                };
                let Json::Obj(ref fields) = value.wire() else {
                    panic!("Context record");
                };
                if !matches!(fields.get("readings"), Some(Json::Arr(rs)) if !rs.is_empty()) {
                    continue;
                }
                fragments.push(NodeRef(index));
                if !answer.outputs.contains_key("system") {
                    retained = true;
                    assert_eq!(answer.status, Decision::Undetermined);
                    assert!(answer.claim.is_none());
                    let reason = answer
                        .reasons
                        .iter()
                        .find(|r| matches!(r.kind, ReasonKind::Stop(_)))
                        .unwrap();
                    assert!(!reason.dependencies.is_empty());
                    assert!(reason.dependencies.contains(&NodeRef(index)));

                    assert!(
                        partial
                            .nodes
                            .iter()
                            .all(|n| n.ty != NodeType::Construction(ConstructionType::LocalSystem))
                    );
                }
            }
            if !fragments.is_empty() && !answer.outputs.contains_key("system") {
                let reason = answer
                    .reasons
                    .iter()
                    .find(|r| matches!(r.kind, ReasonKind::Stop(_)))
                    .unwrap();
                fragments.extend(reason.dependencies.iter().copied());
            }
            assert_fragment(&normal, &partial, fragments);
        }
        println!(
            "finite={finite}: Localize checkpoints={total}, stopped runs={total}, post-commit runs=1"
        );
        assert!(retained, "finite={finite}: closure fragments were lost");
        assert!(completed);
    }
}
