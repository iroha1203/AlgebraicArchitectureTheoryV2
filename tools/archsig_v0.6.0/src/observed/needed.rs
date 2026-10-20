//! 現在の検査済み回答から、未観測位置とその他の理由を収集する。
use super::{
    control::{Checkpoint, Control, StopReason},
    environment::Environment,
    request::{QuestionKind, Request, Selector},
    result::{
        Answer, Decision, Fact, Graph, Node, NodeRef, NodeType, Payload, ReasonKind, Rule, Scope,
        ValidationFailure, sort_reasons,
    },
};
use crate::{canonical::Json, issue::Location, result::location_wire};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Requirement {
    field: Fact,
    dependents: Vec<NodeRef>,
    locations: Vec<Location>,
}
impl Requirement {
    pub(super) fn wire(&self) -> Json {
        Json::obj([
            ("field", self.field.wire()),
            (
                "dependents",
                Json::Arr(self.dependents.iter().map(|r| r.wire()).collect()),
            ),
            (
                "locations",
                Json::Arr(self.locations.iter().map(location_wire).collect()),
            ),
        ])
    }
}
fn tick(control: &Control) -> Result<(), ValidationFailure> {
    control.clone().checkpoint(Checkpoint::ObservationPlan)?;
    Ok(())
}
fn target(request: &Request) -> Result<&str, ValidationFailure> {
    match &request.head {
        Selector::Answer { id, path }
            if request.kind == QuestionKind::Needed
                && path.is_empty()
                && request.arguments.is_empty()
                && request.defaults.is_empty()
                && request.constraints.is_empty()
                && request.dependencies == [id.clone()] =>
        {
            Ok(id)
        }
        _ => Err("ObservationPlanの元要求がneeded($Id)でない".into()),
    }
}
pub(super) fn sources<'a>(
    graph: &'a Graph,
    request: &Request,
    control: &Control,
) -> Result<Vec<(usize, &'a Answer)>, ValidationFailure> {
    let mut requests = BTreeMap::new();
    for (index, candidate) in graph.requests.iter().enumerate() {
        tick(control)?;
        if requests.insert(candidate.id.as_str(), index).is_some() {
            return Err("ObservationPlanの元要求IDが重複する".into());
        }
    }
    let mut answers = BTreeMap::new();
    for (index, candidate) in &graph.checked_answers {
        tick(control)?;
        if answers.insert(*index, candidate).is_some() {
            return Err("ObservationPlanの元回答IDが重複する".into());
        }
    }
    let mut pending = vec![target(request)?.to_owned()];
    let mut seen = BTreeSet::new();
    let mut result = BTreeMap::new();
    while let Some(id) = pending.pop() {
        tick(control)?;
        if !seen.insert(id.clone()) {
            continue;
        }
        if id == request.id {
            return Err("ObservationPlanの元要求が循環する".into());
        }
        let index = *requests
            .get(id.as_str())
            .ok_or("ObservationPlanの元要求がない")?;
        let answer = *answers
            .get(&index)
            .ok_or("ObservationPlanの元回答が未生成")?;
        if answer.id != id {
            return Err("ObservationPlanの元回答IDが不整合".into());
        }
        result.insert(index, answer);
        for dependency in &graph.requests[index].dependencies {
            tick(control)?;
            pending.push(dependency.clone());
        }
    }
    Ok(result.into_iter().collect())
}
fn expected(
    graph: &Graph,
    request: &Request,
    cutoff: usize,
    control: &Control,
) -> Result<Node, ValidationFailure> {
    tick(control)?;
    let mut requirements: BTreeMap<Fact, Requirement> = BTreeMap::new();
    let mut blockers = Vec::new();
    let mut scope = Scope::default();
    let mut support = BTreeSet::new();
    let mut arguments = BTreeSet::new();
    let mut pending = Vec::new();
    let sources = sources(graph, request, control)?;
    let mut original_reasons = BTreeSet::new();
    for (_, answer) in &sources {
        for reference in answer.outputs.values().chain(answer.claim.iter()) {
            tick(control)?;
            if reference.0 >= cutoff {
                return Err("planの元回答が既出でない".into());
            }
            let node = graph.get(*reference)?;
            for reason in node
                .reasons
                .iter()
                .chain(node.judgment.iter().flat_map(|j| &j.reasons))
            {
                tick(control)?;
                original_reasons.insert(reason.wire().canonical());
                // 確定値・反証・適用外に保持された診断は、追加観測の要求にしない。
                if answer.status == Decision::Undetermined {
                    pending.push(reason.clone());
                }
            }
        }
    }
    for (_, answer) in sources {
        tick(control)?;
        // registryの理由も表示済みの型付き出力へ照合する。出力のない依存停止/族は
        // Environmentの元要求検査に従い、それ以外の理由をregistryだけから供給しない。
        if !answer.outputs.is_empty() {
            for reason in &answer.reasons {
                tick(control)?;
                if !matches!(reason.kind, ReasonKind::DependencyBlocked { .. })
                    && !original_reasons.contains(&reason.wire().canonical())
                {
                    return Err("ObservationPlanの理由が元の型付き出力にない".into());
                }
            }
        }
        scope.merge(&answer.scope);
        for reference in answer
            .outputs
            .values()
            .chain(answer.claim.iter())
            .chain(&answer.evidence)
        {
            tick(control)?;
            if reference.0 >= cutoff {
                return Err("ObservationPlanの元回答が既出でない".into());
            }
            let node = graph.get(*reference)?;
            support.extend(node.support.iter().cloned());
            arguments.insert(reference.0);
        }
        if answer.status == Decision::Undetermined {
            pending.extend(answer.reasons.iter().cloned());
        }
    }
    let mut visited = BTreeSet::new();
    while let Some(reason) = pending.pop() {
        tick(control)?;
        let key = reason.wire().canonical();
        if !visited.insert(key) {
            continue;
        }
        if !matches!(reason.kind, ReasonKind::Missing) {
            blockers.push(reason.clone());
        }
        for field in &reason.missing {
            tick(control)?;
            let entry = requirements
                .entry(field.clone())
                .or_insert_with(|| Requirement {
                    field: field.clone(),
                    dependents: vec![],
                    locations: vec![],
                });
            if let Some(location) = &reason.location {
                entry.locations.push(location.clone());
            }
            for reference in &reason.dependencies {
                tick(control)?;
                if reference.0 >= cutoff {
                    return Err("ObservationPlanの元理由が既出でない".into());
                }
                let node = graph.get(*reference)?;
                entry.dependents.push(*reference);
                if let Rule::Input { location, .. } = &node.rule {
                    entry.locations.push(location.clone());
                }
            }
        }
        for reference in &reason.dependencies {
            tick(control)?;
            if reference.0 >= cutoff {
                return Err("ObservationPlanの理由依存が既出でない".into());
            }
            let node = graph.get(*reference)?;
            arguments.insert(reference.0);
            support.extend(node.support.iter().cloned());
            pending.extend(node.reasons.iter().cloned());
        }
    }
    let mut requirements: Vec<_> = requirements.into_values().collect();
    for requirement in &mut requirements {
        tick(control)?;
        requirement.dependents.sort_by_key(|r| r.0);
        requirement.dependents.dedup();
        requirement
            .locations
            .sort_by_key(|l| location_wire(l).canonical());
        requirement.locations.dedup();
    }
    sort_reasons(&mut blockers);
    tick(control)?;
    Ok(Node {
        ty: NodeType::ObservationPlan,
        payload: Some(Payload::ObservationPlan {
            request: target(request)?.into(),
            requirements,
            blockers,
        }),
        rule: Rule::Construction("observation_plan"),
        arguments: arguments.into_iter().map(NodeRef).collect(),
        support: support.into_iter().collect(),
        evidence: vec![],
        judgment: None,
        scope,
        reasons: vec![],
    })
}
fn producer<'a>(graph: &'a Graph, limit: usize) -> Result<&'a Request, ValidationFailure> {
    let context = graph.context_at(limit);
    if context.frame.is_some()
        || context.iteration.is_some()
        || context.instance.is_some()
        || context.case.is_some()
    {
        return Err("ObservationPlanが元要求のcontextに属さない".into());
    }
    graph
        .requests
        .get(context.request)
        .ok_or_else(|| "ObservationPlanの生成要求がない".into())
}
pub(super) fn validate_node(
    graph: &Graph,
    node: &Node,
    limit: usize,
    control: &Control,
) -> Result<(), ValidationFailure> {
    let request = producer(graph, limit)?;
    let original = expected(graph, request, limit, control)?;
    if node != &original {
        return Err("ObservationPlanのslot・依存・位置・理由・由来が元回答と違う".into());
    }
    tick(control)
}
/// Answerの形を検査する。plan本体の意味検査はEnvironment::validate_atが行う。
pub(super) fn validate_answer(
    graph: &Graph,
    request: &Request,
    answer: &Answer,
    control: &Control,
) -> Result<(), ValidationFailure> {
    let Some(reference) = answer.outputs.get("plan") else {
        return Err("neededのplan出力がない".into());
    };
    let node = graph.get(*reference)?;
    if producer(graph, reference.0)? != request
        || answer.id != request.id
        || answer.status != Decision::Established
        || answer.outputs.len() != 1
        || answer.claim.is_some()
        || !answer.evidence.is_empty()
        || !answer.reasons.is_empty()
        || answer.scope != node.scope
    {
        return Err("needed回答が元planと一致しない".into());
    }
    if node.ty != NodeType::ObservationPlan {
        return Err("neededの出力がObservationPlanでない".into());
    }
    tick(control)
}
pub(super) fn evaluate(
    graph: &mut Graph,
    environment: &Environment<'_>,
    request: &Request,
    control: &Control,
) -> Result<(Answer, Option<StopReason>), ValidationFailure> {
    let node = expected(graph, request, graph.nodes.len(), control)?;
    environment.validate(graph, &node)?;
    let scope = node.scope.clone();
    let mut committed = None;
    let result = graph.push_with_metadata(node, |reference| {
        committed = Some(Answer {
            id: request.id.clone(),
            status: Decision::Established,
            outputs: BTreeMap::from([("plan".into(), reference)]),
            claim: None,
            evidence: vec![],
            reasons: vec![],
            scope,
        });
    });
    match (result, committed) {
        (Ok(_), Some(answer)) => Ok((
            answer,
            control
                .clone()
                .checkpoint(Checkpoint::ObservationPlan)
                .err(),
        )),
        (Err(ValidationFailure::Stop(reason)), Some(answer)) => Ok((answer, Some(reason))),
        (Err(failure), _) => Err(failure),
        _ => Err("ObservationPlanの確定callbackがない".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::{ObservedEvaluation, evaluate_observed_bytes, input::InputSources};
    fn example() -> ObservedEvaluation {
        let map=include_str!("../../tests/fixtures/counter.archmap.json").replace("{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}","");
        evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![include_bytes!("../../tests/fixtures/counter.atoms.json").to_vec()],
                include_bytes!("../../tests/fixtures/counter.law").to_vec(),
                map.into_bytes(),
            ),
            &["p=needed($n)", "n=evaluate(CountCheck.amount,s=@v/s)"],
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    fn graph(result: &ObservedEvaluation) -> Graph {
        let mut graph = Graph::new(&Control::unlimited());
        graph.nodes = result.nodes.clone();
        graph.contexts = result.contexts.clone();
        graph.requests = result.prepared.requests().requests().to_vec();
        graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
        graph.frames = result.frames.clone();
        graph.iterations = result.iterations.clone();
        graph.instances = result.instances.clone();
        graph.cases = result.cases.clone();
        graph.universal_witnesses = result.universal_witnesses.clone();
        graph
    }
    #[test]
    fn rejects_forged_plan_slots_locations_refs_scope_and_answers_against_original_sources() {
        let result = example();
        let control = Control::unlimited();
        let environment = Environment::with_requests(
            result.prepared.inputs(),
            result.prepared.requests().requests(),
            &mut control.clone(),
        )
        .unwrap();
        let original = graph(&result);
        for (index, node) in original.nodes.iter().enumerate() {
            environment
                .recheck_node(&original, node, index)
                .expect("元の全導出を先に独立再検査する");
        }
        for (request, answer) in original.requests.iter().zip(&result.answers) {
            environment
                .validate_answer(&original, request, answer)
                .unwrap();
        }
        let index = result.answers[0].outputs["plan"].0;
        for kind in [
            "slot",
            "location",
            "dependent",
            "blocker",
            "argument",
            "scope",
            "support",
        ] {
            let mut changed = original.nodes[index].clone();
            let Some(Payload::ObservationPlan {
                requirements,
                blockers,
                ..
            }) = &mut changed.payload
            else {
                panic!("plan")
            };
            match kind {
                "slot" => requirements[0].field.subject = "forged".into(),
                "location" => requirements[0].locations = vec![Location::Law { span: (0, 1) }],
                "dependent" => requirements[0].dependents = vec![NodeRef(index)],
                "blocker" => {
                    blockers.push(super::super::result::Reason::internal("n", "forged".into()))
                }
                "argument" => changed.arguments.clear(),
                "scope" => {
                    changed.scope.readings.insert("Forged".into());
                }
                "support" => changed.support.push(Fact {
                    snapshot: "v".into(),
                    subject: "forged".into(),
                    field: None,
                    atom: None,
                }),
                _ => unreachable!(),
            }
            assert!(
                matches!(
                    environment.recheck_node(&original, &changed, index),
                    Err(ValidationFailure::Internal(_))
                ),
                "{kind}"
            );
        }
        let mut forged = result.answers[0].clone();
        forged
            .outputs
            .insert("plan".into(), result.answers[1].outputs["evaluation"]);
        assert!(matches!(
            environment.validate_answer(&original, &original.requests[0], &forged),
            Err(ValidationFailure::Internal(_))
        ));
        // planとregistryを一緒に偽造しても、元の入力/式から回答を再検査する。
        let mut changed = graph(&result);
        changed.checked_answers[1].1.reasons[0].missing[0].subject = "forged".into();
        let mut forged = original.nodes[index].clone();
        let Some(Payload::ObservationPlan { requirements, .. }) = &mut forged.payload else {
            panic!("plan")
        };
        requirements[0].field.subject = "forged".into();
        assert!(matches!(
            environment.recheck_node(&changed, &forged, index),
            Err(ValidationFailure::Internal(_))
        ));
        let evaluation = result.answers[1].outputs["evaluation"].0;
        changed.nodes[evaluation].reasons[0].missing[0].subject = "forged".into();
        assert!(
            matches!(
                environment.recheck_node(&changed, &forged, index),
                Err(ValidationFailure::Internal(_))
            ),
            "元nodeとregistryとplanの同時偽造も入力再検査が拒否する"
        );
        let mut removed = graph(&result);
        removed.checked_answers[1].1.reasons.clear();
        let mut omitted = original.nodes[index].clone();
        let Some(Payload::ObservationPlan { requirements, .. }) = &mut omitted.payload else {
            panic!("plan")
        };
        requirements.clear();
        assert!(
            matches!(
                environment.recheck_node(&removed, &omitted, index),
                Err(ValidationFailure::Internal(_))
            ),
            "registryだけで不足理由を消せない"
        );
        let mut decided = graph(&result);
        decided.checked_answers[1].1.status = Decision::Established;
        assert!(
            matches!(
                environment.recheck_node(&decided, &omitted, index),
                Err(ValidationFailure::Internal(_))
            ),
            "registryの判定を偽造して追加観測を消せない"
        );
        let mut renamed = graph(&result);
        renamed.requests[0].id = "forged".into();
        assert!(
            matches!(
                environment.recheck_node(&renamed, &original.nodes[index], index),
                Err(ValidationFailure::Internal(_))
            ),
            "元の解決済み要求も固定して照合する"
        );
    }
}
