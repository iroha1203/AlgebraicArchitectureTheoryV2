use super::*;
use crate::observed::{
    control::{Limits, Usage},
    evaluate::evaluate_observed_bytes,
    input::InputSources,
};
mod fixture {
    include!("../../tests/common/object_view_compatibility_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn completed() -> ObservedEvaluation {
    let definitions = fixture::D.replace(
        r#"{"name":"quantity","type":"Z","meaning":"数量。"}"#,
        r#"{"name":"flag","type":"Bool","meaning":"条件。"}"#,
    );
    let checked = crate::definition::check_definitions(&[("d", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Pattern"].digest;
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pattern","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"o","mode":"specification","method":"有限owner補完の再検査。","locations":[],"note":"全case。"}}],"snapshots":[{{"id":"v","origin":"o","subjects":[{{"id":"root","type":"Pattern.Root","origin":"o"}},{{"id":"other","type":"Pattern.Root","origin":"o"}},{{"id":"p","type":"Pattern.Part","origin":"o"}},{{"id":"q","type":"Pattern.Part","origin":"o"}}],"atoms":[{{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"o"}},{{"id":"fp","subject":"p","field":"Pattern.Part.flag","value":true,"origin":"o"}},{{"id":"fq","subject":"q","field":"Pattern.Part.flag","value":false,"origin":"o"}}]}}]}}"#
    );
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";change choose(c:Part,b:Bool)=c with{{flag=b}};law required valid(c:Part):c.flag;}}"
    );
    let inputs = InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    );
    let result = evaluate_observed_bytes(
        inputs,
        &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
        &mut quiet(),
    )
    .unwrap_err();
    let crate::observed::EvaluationFailure::NotImplemented {
        partial, feature, ..
    } = result
    else {
        panic!("段階2の構成は未実装")
    };
    assert!(feature.contains("存在・一意性は検査済み"), "{feature}");
    *partial
}
fn rebuild(result: &ObservedEvaluation, nodes: &[Node]) -> Result<Graph, ValidationFailure> {
    let mut c = quiet();
    let env = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &mut c,
    )
    .map_err(ValidationFailure::from)?;
    let mut g = Graph::new(&c);
    g.requests = result.prepared.requests().requests().to_vec();
    g.checked_answers = result.answers.iter().cloned().enumerate().collect();
    g.frames = result.frames.clone();
    g.iterations = result.iterations.clone();
    g.instances = result.instances.clone();
    g.cases = result.cases.clone();
    g.universal_witnesses = result.universal_witnesses.clone();
    for (i, n) in nodes.iter().enumerate() {
        g.active = result.contexts[i];
        env.validate(&g, n)?;
        g.push(n.clone())?;
    }
    Ok(g)
}
fn field<'a>(j: &'a mut Json, key: &str) -> &'a mut Json {
    let Json::Obj(fields) = j else {
        panic!("record")
    };
    fields.get_mut(key).unwrap()
}
#[test]
fn finite_owner_completion_recheck_regenerates_missing_duplicate_assignment_and_request_cases() {
    let result = completed();
    rebuild(&result, &result.nodes).expect("元証拠は全再構成で一致");
    let Some(Payload::Construction(v)) = &result.nodes[result.answers[0].claim.unwrap().0].payload
    else {
        panic!("native")
    };
    let D::Change(data) = &v.data else {
        panic!("change")
    };
    let old = &data.source;
    let cert=old.parts.iter().position(|p| matches!(&p.wire,Json::Obj(fields) if fields.get("kind")==Some(&Json::str("completion_fibers")))).unwrap();
    for mode in 0..4 {
        let mut parts = old.parts.clone();
        let data = field(&mut parts[cert].wire, "data");
        if mode == 3 {
            *field(data, "request") = Json::str("different_request");
        } else {
            let Json::Arr(cases) = field(data, "cases") else {
                panic!("cases")
            };
            match mode {
                0 => {
                    cases.pop();
                }
                1 => cases.push(cases[0].clone()),
                _ => {
                    let Json::Arr(assignments) = field(&mut cases[0], "assignments") else {
                        panic!("assignments")
                    };
                    assignments.clear();
                }
            }
        }
        let a = &old.architecture;
        let changed = Arc::new(Source {
            architecture: Architecture {
                witness: a.witness.clone(),
                reference: a.reference,
                root: a.root,
                universe: a.universe,
                complete: a.complete,
                reasons: a.reasons.clone(),
            },
            boundary: old.boundary.clone(),
            base: old.base,
            parts,
            answer: old.answer.clone(),
        });
        let mut nodes = result.nodes.clone();
        for n in &mut nodes {
            let Some(Payload::Construction(v)) = &mut n.payload else {
                continue;
            };
            let D::Change(d) = &mut v.data else { continue };
            if Arc::ptr_eq(&d.source, old) {
                d.source = changed.clone();
            }
        }
        assert!(rebuild(&result, &nodes).is_err(), "tamper mode {mode}");
    }
}

#[test]
fn finite_owner_completion_later_validation_failure_revokes_delivery_qualification() {
    let normal = completed();
    assert!(normal.verified_incomplete().is_some());
    let prepared = crate::observed::prepare_observed(
        normal.prepared.inputs().sources().clone(),
        &[
            "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
            "fail=repair(Selected.valid,on=@v/root,using=Selected.choose)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let failed = crate::observed::evaluate::evaluate_observed_with_rejected_answer(
        prepared,
        &mut quiet(),
        "fail",
    )
    .unwrap_err();
    let crate::observed::EvaluationFailure::NotImplemented { partial, .. } = failed else {
        panic!("先の構成未完成を保持")
    };
    assert_eq!(partial.status(), "error");
    assert!(partial.verified_incomplete().is_none());
    assert!(!partial.answers[0].outputs.is_empty());
    assert!(partial.answers[1].outputs.is_empty());
}
