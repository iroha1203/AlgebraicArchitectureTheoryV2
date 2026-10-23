//! 元Evaluatorの実観測行を、補完集約や表示witnessと分けて保持する。
use super::*;
use crate::observed::{
    object_evaluate::ObjectEvaluationOutcome,
    object_law_transport::{LawApplication, native_case_reading},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Reading {
    pub instance: NodeRef,
    pub application: Option<LawApplication>,
    /// 元ObjectEvaluation内の実観測row。公開DAGのRefとは区別する。
    pub evaluations: Vec<usize>,
    pub body: Option<NodeRef>,
    pub holds: Option<NodeRef>,
}
fn consensus(values: &[Option<bool>]) -> Option<bool> {
    values
        .first()
        .copied()
        .flatten()
        .filter(|v| values.iter().all(|x| x == &Some(*v)))
}
/// 元の閉じた値を保持し、Pathを含む値の表示依存だけを同じnative計画へ移す。
pub(super) fn domain_value(
    value: &Scalar,
    parts: &mut Vec<Part>,
    base: usize,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        for (index, part) in parts.iter().enumerate().rev() {
            tick(c)?;
            if matches!(part, Part::Scalar(s) | Part::ReadingValue { value: s, .. } if s == value) {
                return Ok(NodeRef(
                    base.checked_add(index).ok_or("元量化値の番号が範囲外")?,
                ));
            }
        }
        if !crate::observed::path_value::contains_path(&value.ty(), c)? {
            // 元Evaluatorの検査済みTerm・複合値を、原始有限型へ制限しない。
            return push(parts, base, Part::Scalar(value.clone()), c);
        }
        let mut arguments = vec![];
        let wire = match value {
            Scalar::Path(path) => {
                path.check(c)?;
                let source = domain_value(&path.object(), parts, base, c)?;
                let target = domain_value(&path.target(), parts, base, c)?;
                arguments.extend([source, target]);
                let mut generators = vec![];
                if let Some(step) = &path.step {
                    for generator in std::iter::once(&step.generator).chain(&step.word_tail) {
                        tick(c)?;
                        let reference = domain_value(generator, parts, base, c)?;
                        arguments.push(reference);
                        generators.push(reference.wire());
                    }
                }
                Json::obj([
                    ("reading", Json::str(&path.reading)),
                    ("source", source.wire()),
                    ("target", target.wire()),
                    ("generators", Json::Arr(generators)),
                ])
            }
            Scalar::Tuple(items) | Scalar::List { items, .. } => {
                for item in items {
                    arguments.push(domain_value(item, parts, base, c)?);
                }
                refs(&arguments)
            }
            Scalar::Option { value: None, .. } => Json::obj([("none", Json::Bool(true))]),
            Scalar::Option {
                value: Some(item), ..
            } => {
                let reference = domain_value(item, parts, base, c)?;
                arguments.push(reference);
                Json::obj([("some", reference.wire())])
            }
            _ => return Err("元量化域のPathを含む結果型が違う".into()),
        };
        push(
            parts,
            base,
            Part::ReadingValue {
                value: value.clone(),
                arguments,
                wire,
            },
            c,
        )
    })
}
/// 独立EvaluatorのScope中のDomain参照を、同じ値を持つnativeの既出Domainへ移す。
fn scope(
    value: &Scope,
    raw: &ObservedEvaluation,
    parts: &mut Vec<Part>,
    base: usize,
    domains: &mut std::collections::BTreeMap<usize, NodeRef>,
    c: &mut Control,
) -> Result<Scope, ValidationFailure> {
    let mut value = value.clone();
    for q in &mut value.quantifiers {
        tick(c)?;
        let Some(original) = q.domain else { continue };
        let domain = if let Some(&known) = domains.get(&original.0) {
            known
        } else {
            let node = raw
                .nodes
                .get(original.0)
                .ok_or("元読取りScopeの量化域がない")?;
            let (ty, elements) = match &node.payload {
                Some(Payload::TypeDomain { ty }) => (ty.clone(), None),
                Some(Payload::Domain { ty, elements }) => {
                    let mut values = vec![];
                    for &element in elements {
                        tick(c)?;
                        if element.0 >= original.0 {
                            return Err("元量化域の値が既出でない".into());
                        }
                        let scalar =
                            match &raw.nodes.get(element.0).ok_or("元量化値がない")?.payload
                            {
                                Some(Payload::Scalar(s)) => s,
                                Some(Payload::Construction(v)) => {
                                    v.scalar().ok_or("元量化値が通常値でない")?
                                }
                                _ => return Err("元量化値の生成元が違う".into()),
                            };
                        if scalar.ty() != *ty {
                            return Err("元量化域の型が違う".into());
                        }
                        values.push(domain_value(scalar, parts, base, c)?);
                    }
                    (ty.clone(), Some(values))
                }
                _ => return Err("元読取りScopeの参照が型付きDomainでない".into()),
            };
            if ty != q.ty {
                return Err("元Scopeと量化Domainの型が違う".into());
            }
            let result = push(parts, base, Part::ReadingDomain { ty, elements }, c)?;
            domains.insert(original.0, result);
            result
        };
        q.domain = Some(domain);
    }
    Ok(value)
}
pub(super) fn append(
    a: &Arc<ArchitectureWitness>,
    core: &EquationPresentation,
    parts: &mut Vec<Part>,
    out: &mut Diagram,
    base: usize,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    let (base_support, base_scope) = native::metadata(&ConstructionValue {
        witness: Witness::Architecture(a.clone()),
        data: D::ConstructionLabel(Scalar::Text("polynomial_law_reading".into())),
    })?;
    for original in &out.originals {
        tick(c)?;
        let e = core
            .base()
            .base()
            .evaluations()
            .iter()
            .find(|e| {
                e.position().object == core.object() && e.position().instance == original.instance
            })
            .ok_or("多項式Law読取りの元対象・instanceがない")?;
        // Noneは記号的instance。実rowがある場合に同じ読取りを重ねない。
        if original.row.is_none() && !e.family().rows().is_empty() {
            continue;
        }
        let roots = e
            .family()
            .observed_row_evaluations(e.evaluation(), original.row, c)
            .map_err(|e| construction_failure(&e))?;
        let mut support = base_support.clone();
        let mut scope = base_scope.clone();
        for q in &original.quantifiers {
            if !scope.quantifiers.contains(q) {
                scope.quantifiers.push(q.clone());
            }
        }
        let mut domains = std::collections::BTreeMap::new();
        let mut applications = vec![];
        let mut bodies = vec![];
        let mut holds = vec![];
        match e.evaluation().outcome() {
            ObjectEvaluationOutcome::Evaluated(graph) => {
                let explicit = e
                    .evaluation()
                    .instance()
                    .declaration()
                    .expressions
                    .iter()
                    .any(|x| x.kind == crate::law::model::ExpressionKind::Guard);
                for &root in &roots {
                    tick(c)?;
                    let row = native_case_reading(e.evaluation(), root, explicit, c)
                        .map_err(|e| construction_failure(&e))?;
                    applications.push(row.application().clone());
                    // 非適用の条件付き成立を、元bodyの観測値へ昇格しない。
                    bodies.push(
                        (row.application().value() != Some(false))
                            .then(|| row.body())
                            .flatten(),
                    );
                    holds.push(row.conditional());
                    let node = graph.nodes.get(root.0).ok_or("元観測Law評価の参照がない")?;
                    support.extend(node.support.iter().cloned());
                    scope.merge(&self::scope(
                        &node.scope,
                        graph,
                        parts,
                        base,
                        &mut domains,
                        c,
                    )?);
                }
            }
            ObjectEvaluationOutcome::NotApplicable | ObjectEvaluationOutcome::Conditional(_) => {
                let row = e
                    .family()
                    .uniform()
                    .ok_or("対象非適用Lawの元読取りがない")?;
                applications.push(row.application().clone());
                bodies.push(row.body());
                holds.push(row.conditional());
            }
            ObjectEvaluationOutcome::FiniteView(_) => {
                return Err("Law読取りがview族になった".into());
            }
        }
        support.sort_by_key(|f| f.wire().canonical());
        support.dedup();
        let application = applications
            .first()
            .filter(|v| applications.iter().all(|x| x == *v))
            .cloned();
        let mut make = |value: Option<bool>, body| -> Result<_, ValidationFailure> {
            value
                .map(|v| {
                    push(
                        parts,
                        base,
                        Part::ObservedBoolean {
                            origin: original.reference,
                            body,
                            value: Scalar::Bool(v),
                            support: support.clone(),
                            scope: scope.clone(),
                        },
                        c,
                    )
                })
                .transpose()
        };
        let body = make(consensus(&bodies), true)?;
        let holds = make(consensus(&holds), false)?;
        out.readings.push(Reading {
            instance: original.reference,
            application,
            evaluations: roots.into_iter().map(|r| r.0).collect(),
            body,
            holds,
        });
    }
    tick(c)
}
