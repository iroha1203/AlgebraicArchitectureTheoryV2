//! 有限Law parameterの全型域と既存family DAGの各行を接続する。
use super::*;
use crate::observed::{
    data, finite,
    result::ValidationFailure,
    value_transport::{
        DeclarationValuePosition, FiniteTransportValue, FiniteValueTransport,
        finite_declaration_value_transport,
    },
};
use std::collections::BTreeMap;

fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectLawFamily)
        .map_err(Into::into)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawParameterComparison {
    source_bindings: Vec<(String, FiniteTransportValue)>,
    target_bindings: Vec<(String, FiniteTransportValue)>,
    source_evaluations: Vec<NodeRef>,
    target_evaluations: Vec<NodeRef>,
    source: LawBooleanReading,
    target: LawBooleanReading,
    outcome: LawTransportOutcome,
}
impl LawParameterComparison {
    pub fn source_bindings(&self) -> &[(String, FiniteTransportValue)] {
        &self.source_bindings
    }
    pub fn target_bindings(&self) -> &[(String, FiniteTransportValue)] {
        &self.target_bindings
    }
    /// 対応する側の元評価DAG内の参照。有限欠測補完では全caseの行を保持する。
    pub fn source_evaluations(&self) -> Vec<usize> {
        self.source_evaluations.iter().map(|r| r.0).collect()
    }
    pub fn target_evaluations(&self) -> Vec<usize> {
        self.target_evaluations.iter().map(|r| r.0).collect()
    }
    pub fn source(&self) -> &LawBooleanReading {
        &self.source
    }
    pub fn target(&self) -> &LawBooleanReading {
        &self.target
    }
    pub fn outcome(&self) -> &LawTransportOutcome {
        &self.outcome
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct FiniteLawFamily {
    parameters: Vec<FiniteValueTransport>,
    rows: Vec<LawParameterComparison>,
}
impl FiniteLawFamily {
    /// 元宣言の残parameter順。position()は参照binderも含む元宣言での位置。
    pub fn parameters(&self) -> &[FiniteValueTransport] {
        &self.parameters
    }
    /// 完成した比較のみ。停止結果ではこの列を族全体の結論としない。
    pub fn rows(&self) -> &[LawParameterComparison] {
        &self.rows
    }
}
fn validation(f: ValidationFailure) -> ConstructionFailure {
    match f {
        ValidationFailure::Stop(s) => ConstructionFailure::Stopped(s),
        f => inconsistent(&format!("Law族の型付き値検査: {f:?}")),
    }
}
fn unsupported(r: &ObjectLawTransport) -> ObjectLawTransportFailure {
    ObjectLawTransportFailure::NotImplemented {
        operation: Box::new(r.operation().clone()),
        object: r.object().clone(),
        instance: Box::new(r.instance().clone()),
    }
}
pub(super) fn prepare(
    inputs: &CheckedInputs,
    r: &mut ObjectLawTransport,
    c: &mut Control,
) -> Result<(), ObjectLawTransportFailure> {
    let source = r.instance().clone();
    let target = r
        .target_instance()
        .ok_or_else(|| inconsistent("Law族の対応instanceがない"))?
        .clone();
    for p in source.parameters().iter().chain(target.parameters()) {
        tick(c)?;
        if !finite::supported(&p.ty, inputs.law(), c).map_err(validation)? {
            return Err(unsupported(r));
        }
    }
    r.family = Some(FiniteLawFamily::default());
    for p in source.parameters() {
        tick(c)?;
        let position = source
            .declaration()
            .parameters
            .iter()
            .position(|(name, _)| name == &p.name)
            .ok_or_else(|| inconsistent("元Lawのparameter位置がない"))?;
        let transport = finite_declaration_value_transport(
            inputs,
            &r.declarations,
            &source.declaration().name,
            DeclarationValuePosition::Parameter(position),
            c,
        )?;
        let preserved = transport.bijection().is_some();
        r.family
            .as_mut()
            .ok_or_else(|| inconsistent("有限Law族がない"))?
            .parameters
            .push(transport);
        if !preserved {
            r.outcome =
                LawTransportOutcome::Refuted(LawConditionFailure::ParameterType { position });
            return Ok(());
        }
    }
    Ok(())
}
pub(super) fn is_ground_reading(e: Option<&ObjectEvaluation>) -> bool {
    e.is_some_and(|e| e.instance().parameters().is_empty())
}
pub(super) fn compare(
    source: &LawBooleanReading,
    target: &LawBooleanReading,
) -> LawTransportOutcome {
    match (source.application.value(), target.application.value()) {
        (Some(a), Some(b)) if a != b => {
            LawTransportOutcome::Refuted(LawConditionFailure::Applicability)
        }
        (Some(false), Some(false)) => LawTransportOutcome::Preserved,
        (Some(true), Some(true)) => match (source.body, target.body) {
            (Some(a), Some(b)) if a == b => LawTransportOutcome::Preserved,
            (Some(_), Some(_)) => LawTransportOutcome::Refuted(LawConditionFailure::Holds),
            _ => LawTransportOutcome::Undetermined,
        },
        _ => LawTransportOutcome::Undetermined,
    }
}
fn coordinates(lengths: &[usize], c: &mut Control) -> Result<Vec<Vec<usize>>, ConstructionFailure> {
    let mut rows = vec![vec![]];
    for &length in lengths {
        let mut next = Vec::new();
        for row in rows {
            for index in 0..length {
                tick(c)?;
                let mut row = row.clone();
                row.push(index);
                next.push(row);
            }
        }
        rows = next;
    }
    Ok(rows)
}
type Rows = BTreeMap<Vec<usize>, Vec<NodeRef>>;
fn scalar(e: &ObservedEvaluation, r: NodeRef) -> Result<&Scalar, ConstructionFailure> {
    match e.nodes.get(r.0).and_then(|n| n.payload.as_ref()) {
        Some(Payload::Scalar(s)) => Ok(s),
        _ => Err(inconsistent("Law族のbindingに型付き値がない")),
    }
}
/// wholeのforall真偽を使わず、全caseで全parameter直積の行を確認する。
fn collect(
    e: &ObservedEvaluation,
    root: NodeRef,
    params: &[crate::law::model::Param],
    domains: &[&[FiniteTransportValue]],
    keys: &[Vec<usize>],
    c: &mut Control,
) -> Result<Rows, ConstructionFailure> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        tick(c)?;
        let node = e
            .nodes
            .get(root.0)
            .ok_or_else(|| inconsistent("Law族の評価がない"))?;
        let Some(Payload::Evaluation {
            expression, parts, ..
        }) = &node.payload
        else {
            return Err(inconsistent("Law族のwholeが評価でない"));
        };
        let [part] = parts.as_slice() else {
            return Err(inconsistent("Law族の直積行がない"));
        };
        let completion = matches!(
            e.nodes.get(expression.0).and_then(|n| n.payload.as_ref()),
            Some(Payload::CompletionSeed { .. })
        );
        if completion {
            if part.children.is_empty() {
                return Err(inconsistent("Law族の空補完を全域へ使わない"));
            }
            let mut all: Rows = keys.iter().cloned().map(|k| (k, vec![])).collect();
            for &child in &part.children {
                if child.0 >= root.0 {
                    return Err(inconsistent("Law族のcaseが導出順でない"));
                }
                let case = collect(e, child, params, domains, keys, c)?;
                for (key, refs) in case {
                    tick(c)?;
                    all.get_mut(&key)
                        .ok_or_else(|| inconsistent("補完caseのparameter域が違う"))?
                        .extend(refs);
                }
            }
            return Ok(all);
        }
        // 既存family評価器のwholeはtemplate, 実直積Domain, 全行を引数に持つ。
        let domain = node
            .arguments
            .get(1)
            .and_then(|r| e.nodes.get(r.0))
            .and_then(|n| n.payload.as_ref());
        let Some(Payload::Domain { elements, .. }) = domain else {
            return Err(inconsistent("Law族の実直積Domainがない"));
        };
        if elements.len() != keys.len() || part.children.len() != keys.len() {
            return Err(inconsistent("Law族の行が型の全直積を覆わない"));
        }
        let mut rows = BTreeMap::new();
        for &child in &part.children {
            tick(c)?;
            if child.0 >= root.0 {
                return Err(inconsistent("Law族の行が導出順でない"));
            }
            let Some(Payload::Evaluation { bindings, .. }) =
                e.nodes.get(child.0).and_then(|n| n.payload.as_ref())
            else {
                return Err(inconsistent("Law族の行に評価がない"));
            };
            let mut key = Vec::new();
            for (p, domain) in params.iter().zip(domains) {
                let binding = bindings
                    .iter()
                    .find(|b| b.name == p.name)
                    .ok_or_else(|| inconsistent("Law族の行にparameter bindingがない"))?;
                let value = scalar(e, binding.value)?;
                let mut found = None;
                for (index, candidate) in domain.iter().enumerate() {
                    tick(c)?;
                    if data::equal(value, candidate.scalar(), c).map_err(validation)? {
                        if found.is_some() {
                            return Err(inconsistent("Law族の全域値が重複する"));
                        }
                        found = Some(index);
                    }
                }
                key.push(found.ok_or_else(|| inconsistent("Law族のbindingが元の全型域にない"))?);
            }
            if rows.insert(key, vec![child]).is_some() {
                return Err(inconsistent("Law族の同じ代入が重複する"));
            }
        }
        if keys.iter().any(|key| !rows.contains_key(key)) {
            return Err(inconsistent("Law族に未評価の代入がある"));
        }
        Ok(rows)
    })
}
fn root_rows(
    e: &ObjectEvaluation,
    domains: &[&[FiniteTransportValue]],
    keys: &[Vec<usize>],
    c: &mut Control,
) -> Result<Option<Rows>, ConstructionFailure> {
    let ObjectEvaluationOutcome::Evaluated(evaluation) = e.outcome() else {
        return Ok(None);
    };
    let root = evaluation
        .answers
        .first()
        .and_then(|a| a.outputs.get("evaluation"));
    root.map(|&root| {
        collect(
            evaluation,
            root,
            e.instance().parameters(),
            domains,
            keys,
            c,
        )
    })
    .transpose()
}
fn consensus(values: impl Iterator<Item = Option<bool>>) -> Option<bool> {
    let mut values = values;
    let first = values.next().flatten()?;
    values.all(|v| v == Some(first)).then_some(first)
}
fn row_reading(
    e: &ObjectEvaluation,
    refs: &[NodeRef],
    c: &mut Control,
) -> Result<LawBooleanReading, ConstructionFailure> {
    let ObjectEvaluationOutcome::Evaluated(evaluation) = e.outcome() else {
        return reading(e, c);
    };
    if refs.is_empty() {
        return Err(inconsistent("有限Lawの行に元評価がない"));
    }
    let explicit = e
        .instance()
        .declaration()
        .expressions
        .iter()
        .any(|x| x.kind == ExpressionKind::Guard);
    let mut truths = Vec::new();
    for &root in refs {
        tick(c)?;
        truths.push(truth_at(evaluation, root, explicit, c)?);
    }
    Ok(LawBooleanReading {
        required: required(e.instance())?,
        application: LawApplication::Guard(consensus(truths.iter().map(|t| t.application))),
        body: consensus(truths.iter().map(|t| t.body)),
        conditional: if truths.iter().any(|t| t.conditional == Some(false)) {
            Some(false)
        } else {
            consensus(truths.iter().map(|t| t.conditional))
        },
    })
}
pub(super) fn compare_rows(
    r: &mut ObjectLawTransport,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    let family = r
        .family
        .as_mut()
        .ok_or_else(|| inconsistent("Law族がない"))?;
    let source = r
        .source
        .as_ref()
        .ok_or_else(|| inconsistent("Law族のsource評価がない"))?;
    let target = r
        .target
        .as_ref()
        .ok_or_else(|| inconsistent("Law族のtarget評価がない"))?;
    let sources: Vec<_> = family.parameters.iter().map(|p| p.source()).collect();
    let targets: Vec<_> = family.parameters.iter().map(|p| p.target()).collect();
    let source_keys = coordinates(&sources.iter().map(|d| d.len()).collect::<Vec<_>>(), c)?;
    let target_keys = coordinates(&targets.iter().map(|d| d.len()).collect::<Vec<_>>(), c)?;
    let source_rows = root_rows(source, &sources, &source_keys, c)?;
    let target_rows = root_rows(target, &targets, &target_keys, c)?;
    if (matches!(source.outcome(), ObjectEvaluationOutcome::Evaluated(_)) && source_rows.is_none())
        || (matches!(target.outcome(), ObjectEvaluationOutcome::Evaluated(_))
            && target_rows.is_none())
    {
        return Ok(());
    }
    let mut outcome = LawTransportOutcome::Preserved;
    for key in source_keys {
        tick(c)?;
        let mut image = Vec::new();
        for (p, &index) in family.parameters.iter().zip(&key) {
            image.push(
                *p.bijection()
                    .and_then(|b| b.forward().get(index))
                    .ok_or_else(|| inconsistent("Law族の全域順写像がない"))?,
            );
        }
        let sr = source_rows
            .as_ref()
            .and_then(|rs| rs.get(&key))
            .cloned()
            .unwrap_or_default();
        let tr = target_rows
            .as_ref()
            .and_then(|rs| rs.get(&image))
            .cloned()
            .unwrap_or_default();
        let a = row_reading(source, &sr, c)?;
        let b = row_reading(target, &tr, c)?;
        let point = compare(&a, &b);
        if !matches!(outcome, LawTransportOutcome::Refuted(_)) {
            match &point {
                LawTransportOutcome::Refuted(_) => outcome = point.clone(),
                LawTransportOutcome::Undetermined => outcome = LawTransportOutcome::Undetermined,
                _ => {}
            }
        }
        let bindings =
            |e: &ObjectEvaluation, key: &[usize], domains: &[&[FiniteTransportValue]]| {
                e.instance()
                    .parameters()
                    .iter()
                    .zip(key)
                    .zip(domains)
                    .map(|((p, &index), domain)| (p.name.clone(), domain[index].clone()))
                    .collect()
            };
        family.rows.push(LawParameterComparison {
            source_bindings: bindings(source, &key, &sources),
            target_bindings: bindings(target, &image, &targets),
            source_evaluations: sr,
            target_evaluations: tr,
            source: a,
            target: b,
            outcome: point,
        });
        tick(c)?;
    }
    r.outcome = outcome;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn recheck_rejects_forged_family_domain_rows_bindings_truth_and_references() {
        for mode in 0..7 {
            let (i, mut r) = super::super::tests::example("family");
            let f = r.family.as_mut().unwrap();
            match mode {
                0 => f.parameters.clear(),
                1 => {
                    f.rows.pop();
                }
                2 => f.rows[0].source_bindings[0].0 = "forged".into(),
                3 => f.rows[0].source.body = Some(true),
                4 => f.rows[0].outcome = LawTransportOutcome::Refuted(LawConditionFailure::Holds),
                5 => f.rows[0].source_evaluations.clear(),
                _ => f.rows[0].target_evaluations[0] = NodeRef(usize::MAX),
            }
            assert!(
                r.recheck(i, &mut Control::unlimited()).is_err(),
                "mode={mode}"
            );
        }
    }
}
