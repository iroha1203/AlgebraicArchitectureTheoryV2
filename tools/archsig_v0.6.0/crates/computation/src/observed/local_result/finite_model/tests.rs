use super::*;
use archsig_common::control::quiet;
use archsig_input::input::InputSources;

fn nested_inputs() -> InputSources {
    let definition = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Nested","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Nested.Root","meaning":"状態。","parameters":[],"fields":[{"name":"flag","type":"Bool","meaning":"自由値。"}],"alignments":[]},{"kind":"entity","name":"Nested.Edge","meaning":"参照。","parameters":[{"name":"owner","type":["Ref","Nested.Root"],"meaning":"所有者。"}],"fields":[],"alignments":[]}]}]}"#;
    let checked =
        archsig_input::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Nested"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Nested {{ use vocabulary Nested version \"1\" digest \"{digest}\"; view holds(s:Root):Bool=s.flag; law required valid(e:Edge):holds(e.owner); local patch(e:Edge) reads e.owner.flag; change choose(s:Root,b:Bool)=s with {{flag=b}}; }}"
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Nested","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"参照経路の有限試験。","locations":[],"note":"独立原始入力。"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"Nested.Root","origin":"model"}},{{"id":"e","type":"Nested.Edge","origin":"model"}}],"atoms":[{{"id":"flag","subject":"s","field":"Nested.Root.flag","value":true,"origin":"model"}},{{"id":"owner","subject":"e","field":"Nested.Edge.owner","value":["v","s"],"origin":"model"}}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

#[test]
fn finite_nested_owner_read_reaches_gluing_and_diagnosis() {
    let result = crate::observed::evaluate_observed_bytes(
        nested_inputs(),
        &[
            "b=build(Nested,on=@v/s)",
            "l=localize($b.object,using=Nested.choose)",
            "d=diagnose($l.system,side=semantic)",
        ],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        result.answers[1].status,
        Decision::Established,
        "{:?}",
        result.answers[1].reasons
    );
    assert!(result.answers[1].outputs.contains_key("system"));
    assert!(result.answers[2].outputs.contains_key("diagnostic"));
    assert!(
        !result.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::DependencyBlocked { .. }))
    );
}

fn fact(name: &str) -> Fact {
    Fact::from(archsig_input::archmap::FactData {
        snapshot: "v".into(),
        subject: "s".into(),
        field: Some(name.into()),
        atom: None,
    })
}
fn model() -> (Model, geometry::Support) {
    let x = fact("Nested.Root.x");
    let y = fact("Nested.Root.y");
    let owner = fact("Nested.Edge.owner");
    let carrier = vec![Json::obj([
        ("type", Type::Ref("Nested.Root".into()).wire()),
        ("value", Json::Arr(vec![Json::str("v"), Json::str("s")])),
    ])];
    let required = geometry::Support {
        carrier: carrier.clone(),
        positions: vec![x.clone(), y.clone(), owner.clone()],
        visible: vec![x.clone(), y.clone(), owner],
    };
    let patch = geometry::Support {
        carrier,
        positions: required.positions.clone(),
        visible: vec![x.clone()],
    };
    (
        Model {
            change: "Nested.choose".into(),
            affine_equations: false,
            rational_equations: false,
            assignments: vec![],
            candidates: Candidates {
                subjects: vec![],
                parameter_types: vec![],
                rows: vec![],
                complete: true,
            },
            bindings: vec![],
            slots: vec![x, y],
            slot_types: vec![Type::Bool, Type::Bool],
            points: vec![
                vec![Scalar::Bool(false), Scalar::Bool(false)],
                vec![Scalar::Bool(false), Scalar::Bool(true)],
                vec![Scalar::Bool(true), Scalar::Bool(false)],
                vec![Scalar::Bool(true), Scalar::Bool(true)],
            ],
            candidate_points: vec![],
            requirements: vec![],
            universal: vec![],
            truth: vec![
                vec![false, false, true],
                vec![false, true, true],
                vec![true, false, true],
                vec![true, true, true],
            ],
            law_supports: vec![required.clone(), required.clone(), required],
            readings: vec![],
            missing: vec![],
            scope: Scope::default(),
        },
        patch,
    )
}
#[test]
fn finite_fiber_uses_all_states_and_rejects_hidden_truth_variation() {
    let (model, patch) = model();
    assert!(
        model.candidates.rows.is_empty(),
        "candidate image must not replace the full state domain"
    );
    assert_eq!(model.visible_indexes(&patch), vec![0]);
    assert!(model.visible_law(&patch, 0, &quiet()).unwrap());
    assert!(
        !model.visible_law(&patch, 1, &quiet()).unwrap(),
        "hidden y changes truth inside each x fiber"
    );
    assert!(
        model.visible_law(&patch, 2, &quiet()).unwrap(),
        "constant truth factors through the same projection"
    );
    assert!(
        !model
            .covered_by(std::slice::from_ref(&patch), &quiet())
            .unwrap()
    );
    let full = model.law_supports[0].clone();
    assert!(model.covered_by(&[patch, full], &quiet()).unwrap());
}
#[test]
fn finite_fiber_preserves_carrier_and_positions_and_excludes_affine_domains() {
    let (mut model, patch) = model();
    let mut missing = patch.clone();
    missing.carrier.clear();
    assert!(!model.visible_law(&missing, 2, &quiet()).unwrap());
    missing = patch.clone();
    missing.positions.pop();
    assert!(!model.visible_law(&missing, 2, &quiet()).unwrap());
    model.affine_equations = true;
    assert!(!model.visible_law(&patch, 2, &quiet()).unwrap());
    model.affine_equations = false;
    model.rational_equations = true;
    assert!(!model.visible_law(&patch, 2, &quiet()).unwrap());
    assert!(
        model
            .visible_law(&model.law_supports[0], 2, &quiet())
            .unwrap(),
        "ordinary contains remains valid"
    );
}
#[test]
fn finite_fiber_stop_is_not_a_completed_factorization() {
    use std::{cell::Cell, rc::Rc};
    let (model, patch) = model();
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let control = Control::new(move |point| {
        if point == archsig_common::control::Checkpoint::Localize {
            count.set(count.get() + 1);
        }
        (count.get() == 3).then_some(archsig_input::result::Signal::Term)
    });
    assert!(matches!(
        model.visible_law(&patch, 0, &control),
        Err(ValidationFailure::Stop(archsig_input::result::Signal::Term))
    ));
    assert_eq!(seen.get(), 3);
}

#[test]
fn finite_summary_inhabitation_is_rechecked_from_both_complete_state_tables() {
    let control = Control::unlimited();
    let normal = crate::observed::evaluate_observed_bytes(
        nested_inputs(),
        &[
            "b=build(Nested,on=@v/s)",
            "l=localize($b.object,using=Nested.choose)",
        ],
        &control,
    )
    .unwrap();
    let source = normal
        .nodes
        .iter()
        .find_map(|node| match &node.payload {
            Some(Payload::Construction(value)) => match &value.data {
                D::Local(data)
                    if data
                        .source
                        .system
                        .as_ref()
                        .is_some_and(|system| system.finite.is_some()) =>
                {
                    Some(data.source.clone())
                }
                _ => None,
            },
            _ => None,
        })
        .unwrap();
    let base = source.base;
    let env = Environment::with_prepared(&normal.prepared, &control).unwrap();
    let mut graph = Graph::new(&control);
    graph.requests = normal.prepared.requests().requests().to_vec();
    graph.frames = normal.frames.clone();
    graph.iterations = normal.iterations.clone();
    graph.instances = normal.instances.clone();
    graph.cases = normal.cases.clone();
    graph.universal_witnesses = normal.universal_witnesses.clone();
    graph.checked_answers.push((0, normal.answers[0].clone()));
    for (node, context) in normal.nodes.iter().zip(&normal.contexts).take(base) {
        graph.active = *context;
        env.validate(&graph, node).unwrap();
        graph.push(node.clone()).unwrap();
    }
    graph.active = normal.contexts[base];
    let value = |source: Arc<super::super::Source>| ConstructionValue {
        witness: Witness::Architecture(source.witness.clone()),
        data: D::Local(super::super::Data { source, index: 0 }),
    };
    env.recheck_local(&graph, &value(source), base).unwrap();
    let request = &normal.prepared.requests().requests()[1];
    for equation in [false, true] {
        let mut altered = super::super::compute(&env, &graph, request, base, &control).unwrap();
        let finite = altered.system.as_mut().unwrap().finite.as_mut().unwrap();
        let side = if equation {
            finite.equation.as_mut().unwrap()
        } else {
            &mut finite.semantic
        };
        side.inhabited = !side.inhabited;
        // A fresh source identity must be checked against independently rebuilt parts/system.
        assert!(
            env.recheck_local(&graph, &value(Arc::new(altered)), base)
                .is_err()
        );
    }
}
