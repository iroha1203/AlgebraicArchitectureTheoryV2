//! 未決・元relationの反証・構成失敗を、合同の非同値と分ける。
use super::*;
pub(super) struct Calculated {
    pub nodes: Vec<Data>,
    pub evidence: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
    pub condition: Option<NodeRef>,
}
pub(super) fn calculate(
    graph: &Graph,
    model: &Congruence,
    rows: &[Row],
    references: &BTreeMap<(String, String, String), NodeRef>,
    dependencies: &[NodeRef],
    sources: &[NodeRef],
    base: usize,
    left: NodeRef,
    right: NodeRef,
    request: &Request,
    c: &Control,
) -> Result<Calculated, ValidationFailure> {
    let table = model.relations.as_ref().ok_or("元relation表がない")?;
    let mut reasons = missing_reasons(table, rows, sources, request)?;
    if model.complete() {
        let (nodes, evidence) = build_nodes(
            graph,
            model,
            rows,
            references,
            dependencies,
            base,
            left,
            right,
            c,
        )?;
        return Ok(Calculated {
            nodes,
            evidence,
            reasons,
            condition: None,
        });
    }
    let mut nodes = vec![];
    let mut evidence = vec![];
    for reason in &reasons {
        if let ReasonKind::ConditionFailed { condition, .. } = reason.kind {
            evidence.extend(graph.get(condition)?.evidence.iter().copied());
        }
    }
    evidence.sort_by_key(|r| r.0);
    evidence.dedup();
    for visible in rows {
        c.checkpoint(Checkpoint::FiniteIteration)?;
        let row = table
            .instances
            .get(visible.original)
            .ok_or("元relation rowがない")?;
        if row.state == RelationState::Refuted {
            let left = visible
                .left
                .as_ref()
                .and_then(|s| s.value)
                .ok_or("反証されたrelationの左値がない")?;
            let right = visible
                .right
                .as_ref()
                .and_then(|s| s.value)
                .ok_or("反証されたrelationの右値がない")?;
            let facts=match &row.difference {
                Some(crate::observed::environment::relation_instances::RelationDifference::Action { fact,left,right })=>vec![fact.clone(),left.clone(),right.clone()],
                Some(crate::observed::environment::relation_instances::RelationDifference::Endpoints { .. })=>vec![],
                None=>return Err("relationの原始反例がない".into()),
            };
            let counter = put_data(
                &mut nodes,
                base,
                Data::FailureEvidence {
                    left,
                    right,
                    facts,
                    arguments: visible.references(),
                },
            );
            let condition = put_data(
                &mut nodes,
                base,
                Data::FailureCondition {
                    left,
                    right,
                    evidence: vec![counter],
                    arguments: visible.references(),
                },
            );
            evidence.push(counter);
            reasons.push(failed(request, condition));
        }
    }
    sort_reasons(&mut reasons);
    let condition = reasons.iter().find_map(|reason| match reason.kind {
        ReasonKind::ConditionFailed { condition, .. } => Some(condition),
        _ => None,
    });
    if table
        .instances
        .iter()
        .any(|r| r.state == RelationState::ConditionFailed)
        && condition.is_none()
    {
        return Err("元Path構成失敗の命題がない".into());
    }
    if condition.is_none() && reasons.is_empty() {
        return Err("未決relationの元理由がない".into());
    }
    Ok(Calculated {
        nodes,
        evidence,
        reasons,
        condition,
    })
}
