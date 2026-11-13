use super::*;
use crate::observed::{ObservedEvaluation, evaluate_observed_bytes};
use archsig_input::input::InputSources;
use std::{cell::Cell, rc::Rc};

fn fixture() -> ObservedEvaluation {
    let law = include_str!("../../../../../../tests/fixtures/counter.law").replace(
        "view amount(s: State): Z = s.count;",
        r#"view nested(): Bool = forall n in list<Z>[1,2] . forall m in list<Z>[n] . m=n;
        view other(): Bool = forall n in list<Z>[3] . n=n;
        view called(): Bool = forall n in list<Z>[4] . n=n;
        view caller(): Bool = forall n in list<Z>[5] . called() and n=n;
        view typed(): Bool = forall n:Bool . n=n;
        view items(): Set<Z> = set { n | n in list<Z>[1,2] };"#,
    );
    let result = evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![include_bytes!("../../../../../../tests/fixtures/counter.atoms.json").to_vec()],
            law.into_bytes(),
            include_bytes!("../../../../../../tests/fixtures/counter.archmap.json").to_vec(),
        ),
        &[
            "nested=evaluate(CountCheck.nested)",
            "other=evaluate(CountCheck.other)",
            "caller=evaluate(CountCheck.caller)",
            "typed=evaluate(CountCheck.typed)",
            "items=evaluate(CountCheck.items)",
        ],
        &Control::unlimited(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    result
}

fn graph(result: &ObservedEvaluation, control: &Control, cold: bool) -> Graph {
    let env = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        control,
    )
    .unwrap();
    let mut graph = Graph::new(control);
    graph.requests = result.prepared.requests().requests().to_vec();
    graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
    graph.frames = result.frames.clone();
    graph.iterations = result.iterations.clone();
    graph.instances = result.instances.clone();
    graph.cases = result.cases.clone();
    graph.universal_witnesses = result.universal_witnesses.clone();
    for (index, node) in result.nodes.iter().enumerate() {
        graph.active = result.contexts[index];
        if cold {
            env.validate(&graph, node).unwrap();
        }
        graph.push(node.clone()).unwrap();
    }
    graph
}

// Previous discovery, independent of the new active-chain selection.
fn static_binder(
    env: &Environment<'_>,
    graph: &Graph,
    span: (usize, usize),
    limit: usize,
) -> Result<Option<(NodeRef, NodeRef, Scope)>, ValidationFailure> {
    let name = env.find_name_token(span)?.unwrap();
    let mut found = None;
    for (actual, origin) in env.lexical_context(span)? {
        if actual == name
            && let LexicalOrigin::Iteration(comp) = origin
        {
            if !env.ordinary_in_domain(comp)? {
                return Ok(None);
            }
            let index = env
                .iteration_for(graph, comp)?
                .ok_or(internal!("In binderの実反復無し"))?;
            assert!(found.replace(index).is_none());
        }
    }
    found
        .map(|index| env.ordinary_iteration_input(graph, index, limit))
        .transpose()
}

fn uses(result: &ObservedEvaluation) -> Vec<(usize, (usize, usize))> {
    result
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            let Rule::OrdinarySource(Location::Law { span }) = &node.rule else {
                return None;
            };
            let law = result.prepared.inputs().law();
            let &id = law.program().expressions.get(span)?;
            let expr = &law.program().nodes[id];
            (matches!(&expr.kind,ExprKind::Dotted(parts) if parts.len()==1)
                && matches!(
                    expr.lexical.as_ref().map(|l| l.source),
                    Some(archsig_input::law::ir::BindingSource::Iteration)
                ))
            .then_some((index, *span))
        })
        .collect()
}

#[test]
fn ordinary_runtime_binder_matches_static_discovery_nested_domains_and_same_names() {
    let result = fixture();
    let control = Control::unlimited();
    let mut graph = graph(&result, &control, true);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    let mut outer_in_inner = false;
    let mut outer_in_domain = false;
    let mut callee = false;
    for (index, span) in uses(&result) {
        graph.active = result.contexts[index];
        if !env.ordinary_context(&graph).unwrap() {
            continue;
        }
        let actual = env.ordinary_binder(&graph, span, index).unwrap().unwrap();
        assert_eq!(
            Some(actual.clone()),
            static_binder(&env, &graph, span, index).unwrap()
        );
        let current = graph.active.iteration.unwrap();
        let record = &graph.iterations[current];
        if actual.0 != record.domain {
            outer_in_inner = true;
        }
        outer_in_domain |= result.prepared.inputs().law().exprs().iter().any(|expr| {
            let ExprKind::Quant {
                split:
                    archsig_input::law::ast::QuantSplit::Fixed {
                        domain: archsig_input::law::ast::QuantDomain::In(domain),
                        ..
                    },
                ..
            } = &expr.kind
            else {
                return false;
            };
            let domain = result.prepared.inputs().law().exprs()[*domain].span;
            domain.0 <= span.0 && span.1 <= domain.1
        });
        callee |= graph.active.frame.is_some();
        assert!(
            env.ordinary_binder(&graph, span, actual.1.0).is_err(),
            "member at cutoff is not prior"
        );
    }
    // The inner domain executes in the outer context, before inner activation.
    assert!(outer_in_inner && outer_in_domain && callee);
}

#[test]
fn ordinary_runtime_binder_keeps_missing_and_unsupported_static_contracts() {
    let result = fixture();
    let control = Control::unlimited();
    let mut graph = graph(&result, &control, false);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    let (index, span) = uses(&result)
        .into_iter()
        .find(|(i, _)| result.contexts[*i].request == 0)
        .unwrap();
    let context = result.contexts[index];
    graph.active = context;
    graph.active.iteration = None;
    assert!(matches!(
        env.ordinary_binder(&graph, span, index),
        Err(ValidationFailure::Internal(_))
    ));
    graph.active.iteration = Some(graph.iterations.len());
    assert!(env.ordinary_binder(&graph, span, index).unwrap().is_none());
    graph.active = context;
    let active = context.iteration.unwrap();
    let saved = graph.iterations[active].clone();
    graph.iterations[active].caller.iteration = Some(active);
    assert!(env.ordinary_binder(&graph, span, index).unwrap().is_none());
    graph.iterations[active] = saved;
    // Preserve the old helper contract: active frame mismatch is diagnosed by
    // raw Source validation, not silently hardened in binder discovery.
    graph.active.frame = Some(987);
    assert_eq!(
        env.ordinary_binder(&graph, span, index).unwrap(),
        static_binder(&env, &graph, span, index).unwrap()
    );
    let sibling = result
        .contexts
        .iter()
        .find(|c| c.request == 1 && c.iteration.is_some())
        .unwrap();
    graph.active = *sibling;
    assert!(matches!(
        env.ordinary_binder(&graph, span, graph.nodes.len()),
        Err(ValidationFailure::Internal(_))
    ));
    let law = result.prepared.inputs().law();
    for request in [3, 4] {
        let span=law.program().nodes.iter().find(|expr| {
            matches!(&expr.kind,ExprKind::Dotted(parts) if parts.len()==1 && parts[0].name=="n")
            && expr.ty.is_some()
            && result.nodes.iter().zip(&result.contexts).any(|(node,context)| context.request==request && matches!(&node.payload,Some(Payload::Expression{location:Location::Law{span},..}) if *span==expr.span))
        }).unwrap().span;
        graph.active = Default::default();
        assert!(
            env.ordinary_binder(&graph, span, graph.nodes.len())
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn ordinary_runtime_binder_propagates_stop_without_restarting_probe() {
    let result = fixture();
    for stop_at in [1, 3, 4] {
        let probes = Rc::new(Cell::new(0));
        let armed = Rc::new(Cell::new(false));
        let (count, arm) = (probes.clone(), armed.clone());
        let control = Control::new(move |_| {
            if !arm.get() {
                return None;
            }
            count.set(count.get() + 1);
            (count.get() == stop_at).then_some(Signal::Term)
        });
        let mut graph = graph(&result, &control, false);
        let env = Environment::with_prepared(&result.prepared, &control).unwrap();
        let (index, span) = uses(&result)
            .into_iter()
            .find(|(i, span)| {
                let context = result.contexts[*i];
                let Some(active) = context.iteration else {
                    return false;
                };
                context.request == 0
                    && graph.iterations[active].caller.iteration.is_some()
                    && env.find_name_token(*span).unwrap() == Some("n")
            })
            .unwrap();
        graph.active = result.contexts[index];
        armed.set(true);
        assert!(matches!(
            env.ordinary_binder(&graph, span, index),
            Err(ValidationFailure::Stop(Signal::Term))
        ));
        let frozen = probes.get();
        assert!(matches!(
            env.ordinary_binder(&graph, span, index),
            Err(ValidationFailure::Stop(Signal::Term))
        ));
        assert_eq!(probes.get(), frozen);
    }
}
