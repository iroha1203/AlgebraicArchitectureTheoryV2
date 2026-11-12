use super::*;
#[allow(dead_code)]
mod fixture {
    include!("../../../../tests/common/affine_field_chains.rs");
}

// Use the driver's actual evaluator entry and finish boundary directly so an
// Internal failure retains its diagnostic message and source location here.
fn direct_answer(script: &str, expected: Decision, check: impl FnOnce(&Graph, &Answer)) {
    let c = quiet();
    let input = fixture::input(script, "Z", &[], "r1");
    let prepared = prepare_observed(input, &["a=check(Walk.finite)"], &c).unwrap();
    let env = Environment::with_prepared(&prepared, &c).unwrap();
    let mut graph = Graph::new(&c);
    graph.requests = prepared.requests().requests().to_vec();
    let request = &prepared.requests().requests()[0];
    let declaration = &prepared.inputs().law().declarations()["Walk.finite"];
    let Signature::Law {
        params,
        guard,
        body,
        role,
    } = &declaration.signature
    else {
        panic!("law")
    };
    let mut base = Scope::default();
    base.readings.insert(declaration.reading.clone());
    let mut evaluator = Evaluator {
        environment: &env,
        graph: &mut graph,
        control: &c,
        request,
        declaration,
        bindings: vec![],
        lexical: BTreeMap::new(),
        formal: BTreeMap::new(),
        base,
        retained_scope: Scope::default(),
        reasons: vec![],
        completed: BTreeMap::new(),
        answer_evaluation: None,
        verified_observed: None,
        completing: false,
        finite_universal: None,
        sources: BTreeMap::new(),
    };
    let result = evaluator
        .projection_conditions()
        .and_then(|()| evaluator.family_answer(params, *guard, *body, Some(*role)));
    let answer = match result {
        Ok(answer) => answer,
        Err(Failure::Internal(error)) => panic!(
            "direct finite universal evaluation: {} at {}; script={script}",
            error.message(),
            error.location()
        ),
        Err(Failure::NotImplemented { feature, .. }) => {
            panic!("unsupported {feature}; script={script}")
        }
        Err(Failure::Stop(signal)) => panic!("unexpected stop {signal:?}"),
    };
    match evaluator.finish_answer(&answer) {
        Ok(()) => {}
        Err(Failure::Internal(error)) => panic!(
            "direct finite universal answer: {} at {}; script={script}",
            error.message(),
            error.location()
        ),
        _ => panic!("unexpected finite answer failure"),
    }
    assert_eq!(answer.status, expected);
    assert!(answer.claim.is_some());
    assert!(!answer.evidence.is_empty());
    check(evaluator.graph, &answer);
}
#[test]
fn finite_in_and_type_domains_keep_the_universal_evaluation_context() {
    for (expr, len, ty) in [
        ("forall x in list<Z>[1,1,2] . x>0", 2, Type::Z),
        ("forall x in set<Z>{2,1} . x>0", 2, Type::Z),
        ("forall x in list<Z>[] . x>0", 0, Type::Z),
        ("forall b:Bool . b or not b", 2, Type::Bool),
        ("forall u:Unit . true", 1, Type::Unit),
        ("forall r:Fp(3) . r=r", 3, Type::Fp("3".into())),
        ("not (exists x in list<Z>[] . x>0)", 0, Type::Z),
    ] {
        let script = format!("law required finite(z:Z):z+(if ({expr}) then 2 else 3)=z+2;");
        direct_answer(&script, Decision::Established, |graph, answer| {
            let domains = graph
                .nodes
                .iter()
                .filter_map(|n| match &n.payload {
                    Some(Payload::Domain { ty, elements }) => Some((ty, elements)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(domains.len(), 1, "{expr}");
            assert_eq!(domains[0].0, &ty);
            assert_eq!(domains[0].1.len(), len);
            assert!(
                answer
                    .scope
                    .quantifiers
                    .iter()
                    .any(|q| q.name == "z" && q.domain.is_some())
            );
            assert!(
                answer
                    .scope
                    .quantifiers
                    .iter()
                    .any(|q| q.name != "z" && q.domain.is_some())
            );
        });
    }
}
#[test]
fn finite_symbolic_bodies_keep_their_actual_counterexample_cases() {
    for (domain, kind) in [
        ("list<Bool>[true]", "forall"),
        ("list<Bool>[true]", "exists"),
        ("list<Bool>[true,false]", "forall"),
    ] {
        let script = format!(
            "view inner(x:Q):Bool=forall y:Q . x+y=y; law required finite(z:Q):{kind} b in {domain} . inner(z);"
        );
        direct_answer(&script, Decision::Refuted, |_, answer| {
            assert!(
                answer
                    .scope
                    .quantifiers
                    .iter()
                    .any(|q| q.name == "b" && q.domain.is_some())
            );
        });
    }
}
