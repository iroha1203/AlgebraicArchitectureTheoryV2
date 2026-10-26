//! 有限Law parameterの全型域と既存family DAGの各行を接続する。
use super::*;
use crate::observed::{
    data, finite,
    result::{NodeType, ValidationFailure},
    value_transport::{
        DeclarationValuePosition, FiniteTransportValue, FiniteValueTransport,
        finite_declaration_value_transport,
    },
};
use crate::types::Type;
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
/// 補完で上書きされた最終answerではなく、同じEvaluatorが先に保持した実観測の行。
impl LawReadingFamily {
    pub(in crate::observed) fn observed_row_evaluations(
        &self,
        e: &ObjectEvaluation,
        row: Option<usize>,
        c: &mut Control,
    ) -> Result<Vec<NodeRef>, ConstructionFailure> {
        if row.is_none() {
            if self.uniform.as_ref().is_some_and(|r| r.application.value() == Some(false))
                && e.instance().parameters().iter().all(|p| matches!(p.ty, Type::Z | Type::Q))
                && let ObjectEvaluationOutcome::Evaluated(g) = e.outcome() {
                return Ok(g.answers.first().and_then(|a| a.outputs.get("evaluation"))
                    .copied().into_iter().collect());
            }
            return Ok(constant_numeric_family(e, c)?.map(|(root, _, _)| root).into_iter().collect());
        }
        let (ObjectEvaluationOutcome::Evaluated(g), Some(row)) = (e.outcome(), row) else {
            return Ok(vec![]);
        };
        let Some(mut root) = g
            .answers
            .first()
            .and_then(|a| a.outputs.get("evaluation"))
            .copied()
        else {
            return Ok(vec![]);
        };
        loop {
            tick(c)?;
            let Some(Payload::Evaluation { expression, .. }) =
                g.nodes.get(root.0).and_then(|n| n.payload.as_ref())
            else {
                return Err(inconsistent("元観測のLaw評価がない"));
            };
            let Some(Payload::CompletionSeed {
                location,
                parameters,
                bindings,
                ..
            }) = g.nodes.get(expression.0).and_then(|n| n.payload.as_ref())
            else {
                break;
            };
            // 欠測の追加発見後のseedにはcaseの根も増える。同じSourceの最初のseedは
            // それらを生成する前の既出根を保持する。Scopeは数学的な読取り域であり、
            // 実観測かcaseかの実行索引として使わない。
            let mut roots = None;
            for n in g.nodes.iter().take(expression.0 + 1) {
                tick(c)?;
                if let Some(Payload::CompletionSeed {
                    location: l,
                    parameters: p,
                    bindings: b,
                    roots: r,
                    ..
                }) = &n.payload
                {
                    if l == location && p == parameters && b == bindings {
                        roots = Some(r);
                        break;
                    }
                }
            }
            let roots = roots.ok_or_else(|| inconsistent("元観測の最初の補完Sourceがない"))?;
            let mut original = None;
            for &r in roots {
                tick(c)?;
                let n = g
                    .nodes
                    .get(r.0)
                    .ok_or_else(|| inconsistent("元観測の根参照がない"))?;
                if matches!(n.ty, NodeType::Evaluation(Type::Bool)) {
                    if original.replace(r).is_some() {
                        // 元のwholeを生成できず部分式だけが残った場合、実εは未生成。
                        return Ok(vec![]);
                    }
                }
            }
            let Some(original) = original else {
                return Ok(vec![]);
            };
            if original.0 >= root.0 {
                return Err(inconsistent("元観測のLaw評価根が導出順でない"));
            }
            root = original;
        }
        if e.instance().parameters().is_empty() {
            return if row == 0 {
                Ok(vec![root])
            } else {
                Err(inconsistent("元観測のLaw行が域外"))
            };
        }
        let domains = self
            .domains
            .iter()
            .map(|d| d.values.as_slice())
            .collect::<Vec<_>>();
        let keys = coordinates(&domains.iter().map(|d| d.len()).collect::<Vec<_>>(), c)?;
        let key = keys
            .get(row)
            .ok_or_else(|| inconsistent("元観測のparameter行が域外"))?;
        let rows = collect(g, root, e.instance().parameters(), &domains, &keys, c)?;
        rows.get(key)
            .cloned()
            .ok_or_else(|| inconsistent("元観測のparameter行がない"))
    }
}
/// 元評価器が全parameter上で正規化した、観測fieldに依存しない数値差。
/// 全称Boolだけでは非定数関数の一様性を判断しない。
pub(in crate::observed) fn constant_numeric_family(
    e: &ObjectEvaluation, c: &mut Control,
) -> Result<Option<(NodeRef, NodeRef, Scalar)>, ConstructionFailure> {
    use crate::law::{ast::{BinOp, ExprKind}, model::Signature};
    tick(c)?;
    if e.instance().parameters().is_empty()
        || !e.instance().parameters().iter().all(|p| matches!(p.ty.erase(), Type::Z | Type::Q)) {
        return Ok(None);
    }
    let ObjectEvaluationOutcome::Evaluated(g) = e.outcome() else { return Ok(None) };
    let law = g.prepared().inputs().law();
    let Signature::Law { body, guard, .. } = &law.declarations
        .get(&e.instance().declaration().name).ok_or_else(|| inconsistent("元数値族の宣言がない"))?.signature
    else { return Ok(None) };
    // この共有は数値parameterと算術だけの式に限る。対象の量化・参照・fieldを
    // 観測時の定数へ畳んで記号的な差と取り違えない。
    let names = Arc::new(e.instance().parameters().iter().map(|p| p.name.clone()).collect::<std::collections::BTreeSet<_>>());
    let mut pending = vec![(*body, names.clone())];
    let mut helpers = std::collections::BTreeSet::new();
    if let Some(guard) = guard { pending.push((*guard, names)); }
    while let Some((id, names)) = pending.pop() {
        tick(c)?;
        match &law.exprs[id].kind {
            ExprKind::Int(_) | ExprKind::Bool(_) => {},
            ExprKind::Dotted(path) if path.len() == 1 && names.contains(&path[0].name) => {},
            ExprKind::Group(child) | ExprKind::Unary { operand: child, .. } => pending.push((*child, names)),
            ExprKind::Binary { lhs, rhs, .. } => {
                pending.push((*lhs, names.clone()));
                pending.push((*rhs, names));
            },
            ExprKind::Let { name, value, body } => {
                pending.push((*value, names.clone()));
                let mut inner = (*names).clone();
                inner.insert(name.name.clone());
                pending.push((*body, Arc::new(inner)));
            },
            ExprKind::Call { callee, args } => {
                let mut callee = *callee;
                while let ExprKind::Group(inner) = law.exprs[callee].kind {
                    tick(c)?;
                    callee = inner;
                }
                if matches!(&law.exprs[callee].kind, ExprKind::Dotted(path) if path.len() == 1 && path[0].name == "rat") {
                    if args.len() != 2 || !args.iter().all(|arg| matches!(law.exprs[*arg].kind, ExprKind::Int(_))) { return Ok(None); }
                } else {
                    let span = law.exprs[callee].span;
                    let target = law.infos.iter().flat_map(|info| &info.references).find_map(|(at, name)| (*at == span).then_some(name));
                    let Some(target) = target else { return Ok(None) };
                    let declaration = law.declarations.get(target).ok_or_else(|| inconsistent("元数値helperの宣言がない"))?;
                    let Signature::View { params, body, .. } = &declaration.signature else { return Ok(None) };
                    if params.len() != args.len() || !params.iter().all(|p| matches!(p.ty, Type::Z | Type::Q))
                        || !matches!(law.expr_type(*body), Some(Type::Z | Type::Q)) { return Ok(None); }
                    pending.extend(args.iter().map(|arg| (*arg, names.clone())));
                    if helpers.insert(target.clone()) {
                        let parameters = params.iter().map(|p| p.name.clone()).collect();
                        pending.push((*body, Arc::new(parameters)));
                    }
                }
            },
            _ => return Ok(None),
        }
    }
    let mut expression = *body;
    loop {
        tick(c)?;
        match &law.exprs[expression].kind {
            ExprKind::Group(next) | ExprKind::Let { body: next, .. } => expression = *next,
            ExprKind::Binary { op: BinOp::Eq, .. } => break,
            _ => return Ok(None),
        }
    }
    let Some(root) = g.answers.first().and_then(|a| a.outputs.get("evaluation")).copied() else { return Ok(None) };
    let node = g.nodes.get(root.0).ok_or_else(|| inconsistent("元数値族の評価がない"))?;
    if node.support.iter().any(|f| f.field.is_some()) || !node.reasons.is_empty() { return Ok(None) }
    let Some(Payload::Evaluation { parts, applicability: "applicable", .. }) = &node.payload else { return Ok(None) };
    let part = match (guard, parts.as_slice()) {
        (None, [body]) => body,
        (Some(_), [guard, body]) if matches!(guard.value.and_then(|value| g.nodes.get(value.0)).and_then(|node| node.payload.as_ref()), Some(Payload::Scalar(Scalar::Bool(true)))) => body,
        _ => return Ok(None),
    };
    let Some(residual) = part.residual else { return Ok(None) };
    let Some(Payload::Evaluation { expression, value: Some(value), .. }) = g.nodes.get(residual.0).and_then(|n| n.payload.as_ref()) else { return Ok(None) };
    if !matches!(g.nodes.get(expression.0).and_then(|n| n.payload.as_ref()),
        Some(Payload::ParameterizedTransform { operation: super::super::result::TransformOp::Difference, .. })) {
        return Ok(None);
    }
    let Some(Payload::Scalar(value)) = g.nodes.get(value.0).and_then(|n| n.payload.as_ref()) else { return Ok(None) };
    if !matches!(value.ty(), Type::Z | Type::Q) { return Ok(None) }
    Ok(Some((root, residual, value.clone())))
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
        conditional: consensus(truths.iter().map(|t| t.conditional)),
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

/// 元Lawの全有限代入と、その読みを支える元DAG内の全case。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawReadingRow {
    pub(in crate::observed) bindings: Vec<(String, FiniteTransportValue)>,
    pub(in crate::observed) evaluations: Vec<NodeRef>,
    pub(in crate::observed) reading: LawBooleanReading,
}
impl LawReadingRow {
    pub fn bindings(&self) -> &[(String, FiniteTransportValue)] {
        &self.bindings
    }
    pub fn evaluations(&self) -> Vec<usize> {
        self.evaluations.iter().map(|r| r.0).collect()
    }
    pub fn reading(&self) -> &LawBooleanReading {
        &self.reading
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawReadingDomain {
    pub(in crate::observed) parameter: crate::law::model::Param,
    pub(in crate::observed) values: Vec<FiniteTransportValue>,
    pub(in crate::observed) scope: super::super::result::Scope,
    pub(in crate::observed) support: Vec<super::super::result::Fact>,
    pub(in crate::observed) missing: Vec<super::super::result::Fact>,
}
impl LawReadingDomain {
    pub fn parameter(&self) -> &crate::law::model::Param {
        &self.parameter
    }
    pub fn values(&self) -> &[FiniteTransportValue] {
        &self.values
    }
    pub fn missing(&self) -> &[super::super::result::Fact] {
        &self.missing
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct LawReadingFamily {
    pub(in crate::observed) domains: Vec<LawReadingDomain>,
    pub(in crate::observed) rows: Vec<LawReadingRow>,
    pub(in crate::observed) uniform: Option<LawBooleanReading>,
    pub(in crate::observed) missing: Vec<super::super::result::Fact>,
    pub(in crate::observed) complete: bool,
}
impl LawReadingFamily {
    pub fn domains(&self) -> &[LawReadingDomain] {
        &self.domains
    }
    pub fn rows(&self) -> &[LawReadingRow] {
        &self.rows
    }
    pub fn uniform(&self) -> Option<&LawBooleanReading> {
        self.uniform.as_ref()
    }
    pub fn missing(&self) -> &[super::super::result::Fact] {
        &self.missing
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    pub(in crate::observed) fn known(&self) -> bool {
        fn known(r: &LawBooleanReading) -> bool {
            match r.application.value() {
                Some(false) => true,
                Some(true) => r.body.is_some(),
                None => false,
            }
        }
        self.complete
            && self.missing.is_empty()
            && self
                .uniform
                .as_ref()
                .map_or_else(|| self.rows.iter().all(|r| known(&r.reading)), known)
    }
}
// 対象外の一様な読取りを、既知の有限型域の全代入へ制限する。
// bindingsは型域由来であり、未実行のbodyの評価参照を作らない。
fn finite_outside_rows(
    inputs: &CheckedInputs,
    e: &ObjectEvaluation,
    result: &mut LawReadingFamily,
    c: &mut Control,
) -> Result<(), ObjectEvaluationFailure> {
    for p in e.instance().parameters() {
        tick(c)?;
        if !finite::supported(&p.ty, inputs.law(), c).map_err(validation)? {
            return tick(c).map_err(Into::into);
        }
    }
    let env = crate::observed::environment::Environment::new(inputs, c)
        .map_err(ConstructionFailure::from)?;
    let mut domains = vec![];
    for p in e.instance().parameters() {
        tick(c)?;
        let Some((domain, missing)) = env
            .object_view_domain(p, e.instance())
            .map_err(validation)?
        else {
            return tick(c).map_err(Into::into);
        };
        if !missing.is_empty() {
            return tick(c).map_err(Into::into);
        }
        domains.push(LawReadingDomain {
            parameter: p.clone(),
            values: domain
                .values
                .into_iter()
                .map(FiniteTransportValue::observed)
                .collect(),
            scope: domain.scope,
            support: domain.support,
            missing,
        });
    }
    let keys = coordinates(
        &domains.iter().map(|d| d.values.len()).collect::<Vec<_>>(),
        c,
    )?;
    let reading = result
        .uniform
        .take()
        .ok_or_else(|| inconsistent("対象外の一様読取りがない"))?;
    result.complete = false;
    result.domains = domains;
    for key in keys {
        tick(c)?;
        let bindings = result
            .domains
            .iter()
            .zip(key)
            .map(|(domain, index)| (domain.parameter.name.clone(), domain.values[index].clone()))
            .collect();
        result.rows.push(LawReadingRow {
            bindings,
            evaluations: vec![],
            reading: reading.clone(),
        });
    }
    result.complete = true;
    tick(c).map_err(Into::into)
}
/// ObjectEvaluationの元評価を読む。対応表やOperationを作って読みを補わない。
pub(in crate::observed) fn read_native_family(
    inputs: &CheckedInputs,
    e: &ObjectEvaluation,
    result: &mut LawReadingFamily,
    c: &mut Control,
) -> Result<(), ObjectEvaluationFailure> {
    tick(c)?;
    if e.instance().declaration().kind != "law" {
        return Err(inconsistent("元Law instanceでない").into());
    }
    if e.instance().parameters().is_empty() {
        let value = reading(e, c)?;
        let refs = match e.outcome() {
            ObjectEvaluationOutcome::Evaluated(graph) => graph
                .answers
                .first()
                .and_then(|a| a.outputs.get("evaluation"))
                .copied()
                .into_iter()
                .collect(),
            _ => vec![],
        };
        result.rows.push(LawReadingRow {
            bindings: vec![],
            evaluations: refs,
            reading: value.clone(),
        });
        result.uniform = Some(value);
        result.complete = true;
        return tick(c).map_err(Into::into);
    }
    match e.outcome() {
        ObjectEvaluationOutcome::NotApplicable => {
            result.uniform = Some(reading(e, c)?);
            result.complete = true;
            return finite_outside_rows(inputs, e, result, c);
        }
        ObjectEvaluationOutcome::Conditional(_) => {
            result.uniform = Some(reading(e, c)?);
            result.complete = true;
            return tick(c).map_err(Into::into);
        }
        ObjectEvaluationOutcome::FiniteView(_) => {
            return Err(inconsistent("Lawにview関数族がある").into());
        }
        ObjectEvaluationOutcome::Evaluated(_) => {}
    }
    let env = crate::observed::environment::Environment::new(inputs, c)
        .map_err(ConstructionFailure::from)?;
    let value = reading(e, c)?;
    let inactive_numeric = value.application.value() == Some(false)
        && e.instance().parameters().iter().all(|p| matches!(p.ty, Type::Z | Type::Q));
    if inactive_numeric || constant_numeric_family(e, c)?.is_some() {
        result.uniform = Some(value);
        result.complete = true;
        return tick(c).map_err(Into::into);
    }
    for p in e.instance().parameters() {
        tick(c)?;
        let Some((domain, missing)) = env
            .object_view_domain(p, e.instance())
            .map_err(validation)?
        else {
            return Err(ObjectEvaluationFailure::NotImplemented {
                object: e.object().clone(),
                instance: e.instance().clone(),
            });
        };
        result.missing.extend(missing.iter().cloned());
        result.domains.push(LawReadingDomain {
            parameter: p.clone(),
            values: domain
                .values
                .into_iter()
                .map(FiniteTransportValue::observed)
                .collect(),
            scope: domain.scope,
            support: domain.support,
            missing,
        });
        tick(c)?;
    }
    result.missing.sort();
    result.missing.dedup();
    if !result.missing.is_empty() {
        return Ok(());
    }
    let domains: Vec<_> = result.domains.iter().map(|d| d.values.as_slice()).collect();
    let keys = coordinates(&domains.iter().map(|d| d.len()).collect::<Vec<_>>(), c)?;
    let Some(rows) = root_rows(e, &domains, &keys, c)? else {
        return Ok(());
    };
    for key in &keys {
        tick(c)?;
        let refs = rows
            .get(key)
            .ok_or_else(|| inconsistent("全Law代入の元行がない"))?
            .clone();
        let value = row_reading(e, &refs, c)?;
        let bindings = e
            .instance()
            .parameters()
            .iter()
            .zip(key)
            .zip(&domains)
            .map(|((p, &index), domain)| (p.name.clone(), domain[index].clone()))
            .collect();
        result.rows.push(LawReadingRow {
            bindings,
            evaluations: refs,
            reading: value,
        });
        if result.rows.len() == keys.len() {
            result.complete = true;
        }
        tick(c)?;
    }
    result.complete = true;
    tick(c).map_err(Into::into)
}
pub(in crate::observed) fn compare_native_readings(
    a: &LawBooleanReading,
    b: &LawBooleanReading,
) -> LawTransportOutcome {
    compare(a, b)
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
