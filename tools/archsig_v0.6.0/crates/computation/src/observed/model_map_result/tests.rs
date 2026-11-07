use super::*;
#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/model_map_assembly_data.rs");
}
fn example() -> ObservedEvaluation {
    let other = fixture::ASSEMBLE.replacen("a=", "other=", 1);
    super::super::evaluate_observed_bytes(
        fixture::query(|s| s),
        &[fixture::ASSEMBLE, &other, fixture::MAP],
        &Control::unlimited(),
    )
    .unwrap()
}
fn replay(
    result: &ObservedEvaluation,
    nodes: &[Node],
    contexts: &[super::super::call::Context],
) -> Result<Graph, ValidationFailure> {
    let c = Control::unlimited();
    let env = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &c,
    )?;
    let mut graph = Graph::new(&c);
    graph.requests = result.prepared.requests().requests().to_vec();
    graph.frames = result.frames.clone();
    graph.iterations = result.iterations.clone();
    graph.instances = result.instances.clone();
    graph.cases = result.cases.clone();
    graph.universal_witnesses = result.universal_witnesses.clone();
    graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
    for (index, node) in nodes.iter().enumerate() {
        graph.active = contexts[index];
        env.validate(&graph, node)?;
        graph.push(node.clone())?;
    }
    Ok(graph)
}
#[test]
fn saved_native_assembly_map_replays_from_original_inputs_and_rejects_changed_records() {
    let result = example();
    assert!(result.issues.is_empty(), "{:?}", result.issues);
    replay(&result, &result.nodes, &result.contexts).unwrap();
    let wrapper = result.answers[2].outputs["map"];
    for mutation in 0..8 {
        let mut nodes = result.nodes.clone();
        let Some(Payload::Construction(value)) = &mut nodes[wrapper.0].payload else {
            panic!("native")
        };
        let D::ModelMap(data) = &mut value.data else {
            panic!("assembly map")
        };
        let source = Arc::make_mut(&mut data.source);
        match mutation {
            0 => source.request.id = "forged".into(),
            1 => source.references[0] = result.answers[1].outputs["assembly"],
            2 => {
                source.binding_refs.insert("x".into(), NodeRef(0));
            }
            3 => source.computed.maps.clear(),
            4 => source.computed.actions.clear(),
            5 => source.shape.correspondence = "Assemble.Root".into(),
            6 => source.base += 1,
            7 => source.computed.answer.outputs.clear(),
            _ => unreachable!(),
        }
        assert!(
            replay(&result, &nodes, &result.contexts).is_err(),
            "mutation {mutation}"
        );
    }
    let mut contexts = result.contexts.to_vec();
    contexts[wrapper.0].request = 1;
    assert!(replay(&result, &result.nodes, &contexts).is_err());
}
#[test]
fn current_input_check_is_kept_even_when_a_native_source_was_verified_before() {
    let result = example();
    let graph = replay(&result, &result.nodes, &result.contexts).unwrap();
    let other = fixture::ASSEMBLE.replacen("a=", "other=", 1);
    let prepared = super::super::prepare_observed(
        fixture::query(|s| fixture::atom(s, "a-quantity", Some(Json::str("1")))),
        &[fixture::ASSEMBLE, &other, fixture::MAP],
        &Control::unlimited(),
    )
    .unwrap();
    let env = Environment::with_prepared(&prepared, &Control::unlimited()).unwrap();
    assert!(validate_answer(&env, &graph, &graph.requests[2], &result.answers[2]).is_err());
}

#[test]
fn stop_keeps_a_replayable_native_prefix_and_never_returns_a_completed_answer() {
    use std::{cell::Cell, rc::Rc};
    let result = example();
    let prefix = result
        .contexts
        .iter()
        .position(|context| context.request == 2)
        .unwrap();
    let run = |stop: Option<usize>| {
        let armed = Rc::new(Cell::new(false));
        let arm = armed.clone();
        let seen = Rc::new(Cell::new(0usize));
        let counter = seen.clone();
        let control = Control::new(move |point| {
            if arm.get() && point == Checkpoint::ConfigurationMap {
                counter.set(counter.get() + 1);
                if stop.is_some_and(|stop| counter.get() >= stop) {
                    return Some(archsig_input::result::Signal::Int);
                }
            }
            None
        });
        let environment = Environment::with_prepared(&result.prepared, &control).unwrap();
        let mut graph = Graph::new(&control);
        graph.requests = result.prepared.requests().requests().to_vec();
        graph.frames = result.frames.clone();
        graph.iterations = result.iterations.clone();
        graph.instances = result.instances.clone();
        graph.cases = result.cases.clone();
        graph.universal_witnesses = result.universal_witnesses.clone();
        graph.checked_answers = result.answers[..2].iter().cloned().enumerate().collect();
        for (index, node) in result.nodes[..prefix].iter().enumerate() {
            graph.active = result.contexts[index];
            graph.push(node.clone()).unwrap();
        }
        graph.active = super::super::call::Context {
            request: 2,
            ..Default::default()
        };
        armed.set(true);
        let outcome = evaluate(
            &result.prepared,
            &environment,
            &mut graph,
            &graph_request(&result),
            &control,
        );
        (graph, outcome, seen.get())
    };
    let (full, outcome, total) = run(None);
    outcome.unwrap();
    assert!(total > 20);
    let mut retained = false;
    for at in [1, total / 2, total - 2] {
        let (partial, outcome, _) = run(Some(at));
        assert!(matches!(outcome, Err(ValidationFailure::Stop(_))));
        assert!(partial.nodes.len() <= full.nodes.len());
        retained |= partial.nodes.len() > prefix;
        for (index, node) in partial.nodes.iter().enumerate() {
            assert_eq!(
                node.wire(index, &partial.nodes[..index]),
                full.nodes[index].wire(index, &full.nodes[..index])
            );
        }
        replay(&result, &partial.nodes, &partial.contexts).unwrap();
    }
    assert!(retained, "停止時にも完成済みのnative節点を保持する");
}
fn graph_request(result: &ObservedEvaluation) -> Request {
    result.prepared.requests().requests()[2].clone()
}

#[test]
fn native_map_and_its_source_keep_one_shared_support_buffer() {
    let result = example();
    let at = result.answers[2].outputs["configuration_map"];
    let node = &result.nodes[at.0];
    assert!(!node.support.is_empty());
    let Some(Payload::Construction(value)) = &node.payload else {
        panic!("native")
    };
    let D::ModelMap(data) = &value.data else {
        panic!("map")
    };
    assert_eq!(node.support.as_ptr(), data.part().support.as_ptr());
    let candidate = data.part().reference("candidate").unwrap();
    let other = &result.nodes[candidate.0];
    assert_eq!(node.support, other.support);
    assert_eq!(node.support.as_ptr(), other.support.as_ptr());
}
#[test]
fn a_native_set_operand_and_its_identity_view_keep_the_original_value_reference() {
    let input = fixture::replace_law(
        fixture::query(|s| s),
        "law required zero(p:Part):p.quantity=0;",
        "view supplied(xs:Set<Move>):Set<Move> = xs;law required zero(p:Part):p.quantity=0;",
    );
    let result = super::super::evaluate_observed_bytes(
        input,
        &[
            fixture::ASSEMBLE,
            "v=evaluate(Assembly.moves,x=@v/moveA,y=@v/moveB)",
            "m=assemble_map(Assembly.supplied,from=$a.assembly,to=$a.assembly,xs=$v.value)",
        ],
        &Control::unlimited(),
    )
    .unwrap();
    assert!(result.issues.is_empty(), "{:?}", result.issues);
    let Some(Payload::Construction(value)) =
        &result.nodes[result.answers[2].outputs["map"].0].payload
    else {
        panic!("native")
    };
    let D::ModelMap(data) = &value.data else {
        panic!("map")
    };
    let (reference, used) = data
        .project(&[ProjectionStep::Field("correspondences".into())])
        .unwrap();
    assert_eq!(used, 1);
    assert_eq!(reference, result.answers[1].outputs["value"]);
}
