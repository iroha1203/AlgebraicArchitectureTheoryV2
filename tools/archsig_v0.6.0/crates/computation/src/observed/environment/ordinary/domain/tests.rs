use super::*;
use crate::observed::{ObservedEvaluation, evaluate_observed_bytes};
use archsig_common::control::{Control, Signal, quiet};
use archsig_input::input::InputSources;
use std::{cell::Cell, rc::Rc};

fn fixture(collection: &str) -> ObservedEvaluation {
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff\"; view domainKernel():Bool=forall b in {collection} . true; }}"
    );
    evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![
                include_bytes!("../../../../../../../tests/fixtures/reservations.atoms.json")
                    .to_vec(),
            ],
            law.into_bytes(),
            include_bytes!("../../../../../../../tests/fixtures/reservations.archmap.json")
                .to_vec(),
        ),
        &["all=evaluate(Reservations.domainKernel)"],
        &quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()))
}
fn graph(result: &ObservedEvaluation, c: &Control) -> Graph {
    let mut g = Graph::new(c);
    g.nodes = result.nodes.clone().into();
    g.contexts = result.contexts.clone();
    g.requests = result.prepared.requests().requests().to_vec();
    g.frames = result.frames.clone();
    g.iterations = result.iterations.clone();
    g.instances = result.instances.clone();
    g.cases = result.cases.clone();
    g.universal_witnesses = result.universal_witnesses.clone();
    g
}
fn refs(g: &Graph) -> (NodeRef, NodeRef, NodeRef, NodeRef) {
    let domain = g
        .nodes
        .iter()
        .position(|n| n.rule == Rule::InDomain)
        .map(NodeRef)
        .expect("actual normal In Domain");
    let n = g.get(domain).unwrap();
    (n.arguments[0], n.arguments[1], n.arguments[2], domain)
}

#[test]
fn existing_collection_can_be_used_by_a_later_source_but_not_before_its_inputs() {
    let result = fixture("list<Bool>[true,false,true]");
    let control = quiet();
    let mut g = graph(&result, &control);
    let (source, input, _, _) = refs(&g);
    g.active = g.context_at(source.0);
    let later = g.push(g.get(source).unwrap().clone()).unwrap();
    assert!(input.0 < later.0);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    let built = env
        .construct_in_domain(&mut g, later, input, |_, _| {})
        .unwrap()
        .unwrap();
    assert_eq!(built.elements_len, 2);
    let cold = Environment::with_prepared(&result.prepared, &control).unwrap();
    cold.validate_at(&g, g.get(built.domain).unwrap(), built.domain.0)
        .unwrap();
    let before_source = Environment::with_prepared(&result.prepared, &control).unwrap();
    assert!(
        before_source
            .validate_at(&g, g.get(built.producer).unwrap(), later.0)
            .is_err()
    );
}
#[test]
fn normal_in_domain_uses_one_set_recipe_and_positional_members_in_first_appearance_order() {
    for collection in ["list<Bool>[true,false,true]", "set<Bool>{true,false,true}"] {
        let r = fixture(collection);
        assert_eq!(r.status(), "complete", "{:?}", r.issues);
        let c = quiet();
        let mut g = graph(&r, &c);
        let (source, input, _, _) = refs(&g);
        g.active = g.context_at(source.0);
        let env = Environment::with_prepared(&r.prepared, &c).unwrap();
        // Input source can still use the legacy path in this isolated worktree.
        // Certify it before measuring only the completed real Domain operation.
        env.validate_at(&g, g.get(source).unwrap(), source.0)
            .unwrap();
        env.validate_at(&g, g.get(input).unwrap(), input.0).unwrap();
        let enumerations = Rc::new(Cell::new(0));
        let observed = enumerations.clone();
        let normalizations = Rc::new(Cell::new(0));
        let set_observed = normalizations.clone();
        data::observe_iterations(move |_, _, phase, _| {
            if phase == "in_set_normalization" {
                set_observed.set(set_observed.get() + 1);
            }
            if phase == "in_domain_normalize" {
                observed.set(observed.get() + 1);
            }
        });
        let built = env
            .construct_in_domain(&mut g, source, input, |_, _| {})
            .unwrap()
            .unwrap();
        data::clear_iteration_observer();
        assert_eq!(
            enumerations.get(),
            1,
            "one normal producer, no per-member normalization"
        );
        assert_eq!(
            normalizations.get(),
            usize::from(collection.starts_with("list")),
            "normal List converts once; checked Set does not re-normalize"
        );
        assert_eq!(built.elements_len, 2);
        let Scalar::Set { items, .. } = g.scalar(built.producer).unwrap() else {
            panic!("set")
        };
        assert_eq!(items.as_slice(), &[Scalar::Bool(true), Scalar::Bool(false)]);
        let Some(Payload::Domain { elements, .. }) = &g.get(built.domain).unwrap().payload else {
            panic!("domain")
        };
        assert_eq!(
            g.get(built.domain).unwrap().arguments[..3],
            [source, input, built.producer]
        );
        for (position, reference) in elements.iter().enumerate() {
            let n = g.get(*reference).unwrap();
            assert_eq!(n.rule, Rule::InMember { position });
            assert_eq!(n.arguments, [built.producer]);
            assert_eq!(n.scope, g.get(input).unwrap().scope);
            assert_eq!(n.support, g.get(input).unwrap().support);
        }
        assert_eq!(
            g.get(built.domain)
                .unwrap()
                .scope
                .quantifiers
                .last()
                .unwrap()
                .domain,
            None
        );
        let cold_count = Rc::new(Cell::new(0));
        let observed = cold_count.clone();
        let cold_normalizations = Rc::new(Cell::new(0));
        let cold_set_observed = cold_normalizations.clone();
        data::observe_iterations(move |_, _, phase, _| {
            if phase == "in_set_normalization" {
                cold_set_observed.set(cold_set_observed.get() + 1);
            }
            if phase == "in_domain_normalize" {
                observed.set(observed.get() + 1);
            }
        });
        let cold = Environment::with_prepared(&r.prepared, &c).unwrap();
        cold.validate_at(&g, g.get(built.domain).unwrap(), built.domain.0)
            .unwrap();
        assert_eq!(
            cold_count.get(),
            1,
            "cold coverage authenticates one Set producer"
        );
        cold.validate_at(&g, g.get(built.domain).unwrap(), built.domain.0)
            .unwrap();
        assert_eq!(cold_count.get(), 1, "warm exact prefix reuses success");
        assert_eq!(
            cold_normalizations.get(),
            usize::from(collection.starts_with("list")),
            "one cold List normalization, no additional warm one"
        );
        data::clear_iteration_observer();
    }
}
#[test]
fn cold_in_domain_rejects_coverage_member_recipe_support_context_and_cutoff_coforgery() {
    let r = fixture("list<Bool>[true,false,true]");
    let c = quiet();
    let original = graph(&r, &c);
    let (source, input, set, domain) = refs(&original);
    let Some(Payload::Domain { elements, .. }) = &original.get(domain).unwrap().payload else {
        panic!("domain")
    };
    let members = elements.clone();
    for mutation in 0..8 {
        let mut g = graph(&r, &c);
        match mutation {
            0 => {
                let Some(Scalar::Set { items, .. }) = g.nodes[set.0].scalar_payload_mut() else {
                    panic!("set")
                };
                items.truncate(1);
                let Some(Payload::Domain { elements, .. }) = &mut g.nodes[domain.0].payload else {
                    panic!("domain")
                };
                elements.truncate(1);
                g.nodes[domain.0].arguments.truncate(4);
            }
            1 => {
                g.nodes[members[0].0].rule = Rule::InMember { position: 1 };
            }
            2 => {
                g.nodes[domain.0].arguments.swap(3, 4);
                let Some(Payload::Domain { elements, .. }) = &mut g.nodes[domain.0].payload else {
                    panic!("domain")
                };
                elements.swap(0, 1);
            }
            3 => {
                g.nodes[set.0].scope.readings.insert("forged".into());
                g.nodes[domain.0].scope.readings.insert("forged".into());
                for m in &members {
                    g.nodes[m.0].scope.readings.insert("forged".into());
                }
            }
            4 => {
                g.nodes[members[0].0].support =
                    vec![Fact::from(archsig_input::archmap::FactData {
                        snapshot: "v".into(),
                        subject: "A".into(),
                        field: None,
                        atom: None,
                    })]
                    .into();
            }
            5 => {
                g.contexts[members[0].0].case = Some(0);
            }
            6 => {
                g.nodes[set.0].arguments[1] = domain;
            }
            _ => {
                let Some(Scalar::Set { items, .. }) = g.nodes[set.0].scalar_payload_mut() else {
                    panic!("set");
                };
                items.reverse();
                g.nodes[members[0].0].payload = Some(Payload::scalar(Scalar::Bool(false)));
                g.nodes[members[1].0].payload = Some(Payload::scalar(Scalar::Bool(true)));
            }
        }
        let env = Environment::with_prepared(&r.prepared, &c).unwrap();
        assert!(
            env.validate_at(&g, g.get(domain).unwrap(), domain.0)
                .is_err(),
            "mutation={mutation}, source={source:?}, input={input:?}"
        );
    }
}
#[test]
fn in_domain_stop_keeps_only_committed_positions_and_no_fake_coverage() {
    let r = fixture("list<Bool>[true,false,true]");
    for signal in [Signal::Int, Signal::Term] {
        let armed = Rc::new(Cell::new(false));
        let flag = armed.clone();
        let c = Control::new(move |_| flag.replace(false).then_some(signal));
        let mut g = graph(&r, &c);
        let (source, input, _, _) = refs(&g);
        g.active = g.context_at(source.0);
        let env = Environment::with_prepared(&r.prepared, &c).unwrap();
        let before = g.nodes.len();
        let kept = Rc::new(Cell::new(0));
        let observed = kept.clone();
        let outcome = env.construct_in_domain(&mut g, source, input, |_, _| {
            observed.set(observed.get() + 1);
            armed.set(true);
        });
        assert!(matches!(outcome, Err(ValidationFailure::Stop(_))));
        assert_eq!(kept.get(), 1);
        assert_eq!(g.nodes.len(), before + 1);
        assert_eq!(g.nodes[before].rule, Rule::InSet);
        assert!(!g.nodes[before..].iter().any(|n| n.rule == Rule::InDomain));
        let fresh = quiet();
        let mut copy = graph(&r, &fresh);
        copy.nodes = g.nodes.clone();
        copy.contexts = g.contexts.clone();
        let cold = Environment::with_prepared(&r.prepared, &fresh).unwrap();
        cold.validate_at(&copy, copy.get(NodeRef(before)).unwrap(), before)
            .unwrap();
    }
}

#[test]
fn empty_known_in_domain_retains_actual_zero_coverage() {
    let r = fixture("list<Bool>[]");
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    let c = quiet();
    let g = graph(&r, &c);
    let (_, _, set, domain) = refs(&g);
    assert!(matches!(g.scalar(set).unwrap(),Scalar::Set{items,..}if items.is_empty()));
    assert!(
        matches!(&g.get(domain).unwrap().payload,Some(Payload::Domain{elements,..})if elements.is_empty())
    );
    assert_eq!(g.get(domain).unwrap().arguments.len(), 3);
    let cold = Environment::with_prepared(&r.prepared, &c).unwrap();
    cold.validate_at(&g, g.get(domain).unwrap(), domain.0)
        .unwrap();
}

#[allow(dead_code)]
mod owned_fixture {
    include!("../../../../../../../tests/common/owned_partial_calls.rs");
}
#[test]
fn genuine_owned_collection_unknown_pending_and_failed_do_not_create_empty_initial_domain() {
    const EXTRA: &str = "\nview domainBlocked(a:System,e:Reserve):List<Bool> =let n=read(a,e.to) in list<Bool>[true,false];\nview domainBlockedQuant(a:System,e:Reserve):Bool=forall b in domainBlocked(a,e) . true;\n";
    for pending in [true, false] {
        let original = if pending {
            owned_fixture::missing_reference_input()
        } else {
            owned_fixture::input(false, "r1")
        };
        let law = String::from_utf8(original.law().bytes().to_vec()).unwrap();
        assert_eq!(law.matches(owned_fixture::SCRIPT).count(), 1);
        let law = law.replacen(
            owned_fixture::SCRIPT,
            &(owned_fixture::SCRIPT.to_owned() + EXTRA),
            1,
        );
        let input = InputSources::from_bytes(
            original
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            law.into_bytes(),
            original.archmap().bytes().to_vec(),
        );
        let r = evaluate_observed_bytes(
            input,
            &["blocked=evaluate(Reservations.domainBlockedQuant,a=@v/B,e=@v/e)"],
            &quiet(),
        )
        .unwrap_or_else(|e| panic!("pending={pending}: {:?}", e.wire()));
        let c = quiet();
        let g = graph(&r, &c);
        let env = Environment::with_prepared(&r.prepared, &c).unwrap();
        let bytes = r.prepared.inputs().sources().law().bytes();
        let mut found = 0;
        for (index, node) in g.nodes.iter().enumerate() {
            if g.context_at(index).case.is_some() {
                continue;
            }
            let Some(Payload::Evaluation {
                expression,
                value,
                parts,
                ..
            }) = &node.payload
            else {
                continue;
            };
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &g.get(*expression).unwrap().payload
            else {
                continue;
            };
            if &bytes[span.0..span.1] != b"forall b in domainBlocked(a,e) . true" {
                continue;
            }
            found += 1;
            assert!(value.is_none());
            assert_eq!(parts[0].children.len(), 1);
            let collection = parts[0].children[0];
            let child = g.get(collection).unwrap();
            assert!(matches!(
                child.payload,
                Some(Payload::Evaluation { value: None, .. })
            ));
            assert_eq!(
                env.evaluation_condition_pending(&g, collection).unwrap(),
                pending
            );
            assert_eq!(
                child
                    .reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. })),
                !pending
            );
            if pending {
                assert!(
                    node.reasons
                        .iter()
                        .any(|r| matches!(r.kind, ReasonKind::Missing))
                );
            } else {
                assert!(
                    node.reasons
                        .iter()
                        .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
                );
            }
            assert!(
                !g.nodes
                    .iter()
                    .enumerate()
                    .any(|(i, n)| g.context_at(i).case.is_none()
                        && n.rule == Rule::InDomain
                        && n.arguments.first() == Some(expression))
            );
        }
        assert!(
            found > 0,
            "initial genuine Quant Eval must exist: {:?}",
            r.issues
        );
    }
}
