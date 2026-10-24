//! 同じ候補状態の通常view評価から有限な全fiberを作る。
use super::*;
use crate::law::model::Signature;
use crate::observed::{
    change_result::CandidateInput, object_evaluate::ObjectDomain, projection::ProjectionType,
};
use std::sync::Arc;
pub(in crate::observed) struct Row {
    pub parameters: Scalar,
    pub image: Scalar,
}
pub(in crate::observed) struct Table {
    pub rows: Vec<Row>,
    pub missing: Vec<Fact>,
    pub parameter_type: Type,
    pub bindings: Vec<(String, Scalar)>,
}
fn unsupported(request: &Request, feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law { span: (0, 0) },
        feature: format!("{}: {feature}", request.id),
    }
}
fn exact_type(ty: &Type, c: &mut Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        Ok(match ty {
            Type::Unit | Type::Bool | Type::Z | Type::Q | Type::Fp(_) | Type::Text => true,
            Type::Tuple(items) => {
                for item in items {
                    if !exact_type(item, c)? {
                        return Ok(false);
                    }
                }
                true
            }
            _ => false,
        })
    })
}
pub(in crate::observed) fn compute(
    original: &Environment<'_>,
    graph: &Graph,
    input: &CandidateInput,
    request: &Request,
    c: &mut Control,
) -> Result<Table, ValidationFailure> {
    if input.search.linear.is_some() {
        return Err(unsupported(request, "整数アフィン商の公開配送は未実装"));
    }
    let candidates = input.search.candidates.as_ref().ok_or("商の候補表がない")?;
    if !input.search.complete || !candidates.complete {
        return Err(unsupported(request, "商の有限候補全域が未確定"));
    }
    let declaration =
        &original.inputs.law().declarations[request.declaration().ok_or("商のviewがない")?];
    let Signature::View {
        params,
        returns,
        body,
    } = &declaration.signature
    else {
        return Err("商のheadがviewでない".into());
    };
    if !exact_type(returns, c)? {
        return Err(unsupported(request, "このview型の有限商の等値は未実装"));
    }
    let bindings = params
        .iter()
        .map(|p| {
            let arg = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
                .ok_or("商のview束縛がない")?;
            Ok((
                p.name.clone(),
                change_search::selector(original, graph, &arg.value)?,
            ))
        })
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    let domain = Arc::new(ObjectDomain::from_readings(
        original.inputs,
        input.witness.readings(),
        0,
        c,
    )?);
    let mut rows = vec![];
    let mut missing = BTreeSet::new();
    for (index, candidate) in candidates.rows.iter().enumerate() {
        c.checkpoint(Checkpoint::Quotient)?;
        if candidate.update.state == change_evaluation::State::Excluded {
            continue;
        }
        if matches!(input.domain_type, ProjectionType::SolutionSet(_)) {
            match input
                .search
                .solutions
                .iter()
                .find(|row| row.candidate == index)
                .and_then(|row| row.member)
            {
                Some(false) => continue,
                Some(true) => {}
                None => return Err(unsupported(request, "商の解所属が未確定")),
            }
        }
        if candidate.update.state != change_evaluation::State::Ready {
            return Err(unsupported(request, "商の候補状態が未確定"));
        }
        let mut assignments = input
            .assignments
            .iter()
            .cloned()
            .collect::<BTreeMap<_, _>>();
        assignments.extend(candidate.update.values.iter().cloned());
        let assignments = assignments.into_iter().collect::<Vec<_>>();
        let mut env = Environment::try_primitive_valuation(original.inputs, &assignments, c)?
            .ok_or("商の候補代入が不適合")?;
        env.object = Some(domain.clone());
        env.missing_slot_reads.replace(Some(BTreeSet::new()));
        let mut checked = BTreeMap::new();
        let mut checks = owned_call::Checks::default();
        let mut vars = BTreeMap::new();
        for (param, (name, value)) in params.iter().zip(&bindings) {
            env.owned_call_value_check(
                &param.ty,
                &crate::observed::term::affine::Value::Known(value.clone()),
                &checked,
                &declaration.reading,
                declaration.span,
                &mut checks,
            )?;
            checked.insert(name.as_str(), Some(value));
            vars.insert(
                name.clone(),
                SourceValue {
                    known_value: Some(value.clone()),
                    scalar_scope: Some(Scope::default()),
                    scope: Scope::default(),
                    support: vec![],
                    condition_failed: false,
                    condition_pending: false,
                    symbolic: None,
                    comparison: None,
                    affine: None,
                },
            );
        }
        if checks.failure.is_some() || checks.blocked {
            if !checks.missing.is_empty() {
                missing.extend(checks.missing);
                continue;
            }
            return Err(unsupported(request, "候補上のview適用条件の公開配送は未実装"));
        }
        let value = env.scoped_ast(*body, &vars, &Scope::default(), &declaration.reading)?;
        if value.condition_failed || value.condition_pending || value.known_value.is_none() {
            let reads = env.missing_slot_reads.replace(None).ok_or("商の不足位置収集がない")?;
            if !reads.is_empty() {
                missing.extend(reads);
                continue;
            }
            return Err(unsupported(request, "候補上のview構成条件・記号値の商は未実装"));
        }
        rows.push(Row {
            parameters: Scalar::Tuple(candidate.parameters.clone()),
            image: value.known_value.ok_or("検査済みview値がない")?,
        });
    }
    Ok(Table {
        rows,
        missing: missing.into_iter().collect(),
        parameter_type: Type::Tuple(candidates.parameter_types.clone()),
        bindings,
    })
}
