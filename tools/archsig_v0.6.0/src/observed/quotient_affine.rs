//! 元の整数候補座標上でViewを評価し、選択された部分域へ制限する。
use super::*;
use crate::law::model::Signature;
use crate::observed::{
    affine,
    change_result::CandidateInput,
    integer_fiber::{self, Matrix},
    object_evaluate::ObjectDomain,
    projection::ProjectionType,
};
use num_bigint::BigInt as Z;
use num_traits::{One, Zero};
use std::sync::Arc;

pub(in crate::observed) struct Image {
    pub bindings: Vec<(String, Scalar)>,
    pub matrix: Matrix,
    pub offset: Vec<Z>,
    pub embedding: Matrix,
    pub origin: Vec<Z>,
    pub dimensions: usize,
    pub empty: bool,
    pub missing: Vec<Fact>,
    pub scope: Scope,
}
fn unsupported(request: &Request, feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law { span: (0, 0) },
        feature: format!("{}: {feature}", request.id),
    }
}
pub(in crate::observed) fn compute(
    original: &Environment<'_>,
    graph: &Graph,
    input: &CandidateInput,
    request: &Request,
    c: &mut Control,
) -> Result<Image, ValidationFailure> {
    c.checkpoint(Checkpoint::Quotient)?;
    if request.arguments.iter().any(|a| a.name == "law") {
        return Err(unsupported(request, "整数商のLaw降下の公開配送は未実装"));
    }
    if !input.search.complete {
        return Err(unsupported(request, "整数商の候補全域が未確定"));
    }
    let linear = input
        .search
        .linear
        .as_ref()
        .ok_or("整数商の線形表示がない")?;
    let decl =
        &original.inputs.law().declarations[request.declaration().ok_or("整数商のViewがない")?];
    let Signature::View {
        params,
        returns,
        body,
    } = &decl.signature
    else {
        return Err("整数商のheadがViewでない".into());
    };
    if *returns != Type::Z {
        return Err(unsupported(request, "整数商のこのView値型は未実装"));
    }
    let bindings = params
        .iter()
        .map(|p| {
            let arg = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
                .ok_or("整数商の束縛がない")?;
            Ok((
                p.name.clone(),
                change_search::selector(original, graph, &arg.value)?,
            ))
        })
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
    let n = linear.parameter_count;
    let (origin, embedding, dimensions, empty) =
        if matches!(input.domain_type, ProjectionType::SolutionSet(_)) {
            let dimensions = linear.kernel.first().map_or(0, Vec::len);
            (
                linear
                    .particular
                    .clone()
                    .unwrap_or_else(|| vec![Z::zero(); n]),
                linear.kernel.clone(),
                dimensions,
                linear.particular.is_none(),
            )
        } else if linear.candidates_empty {
            (vec![Z::zero(); n], vec![vec![]; n], 0, true)
        } else if let Some(guard) = &linear.guard {
            (
                guard
                    .fiber
                    .particular
                    .clone()
                    .ok_or("整数候補guardの原点がない")?,
                guard.fiber.kernel.clone(),
                n - guard.fiber.rank,
                false,
            )
        } else {
            let mut identity = vec![];
            for i in 0..n {
                c.checkpoint(Checkpoint::Quotient)?;
                let mut row = vec![Z::zero(); n];
                row[i] = Z::one();
                identity.push(row);
            }
            (vec![Z::zero(); n], identity, n, false)
        };
    let mut result = Image {
        bindings,
        matrix: vec![],
        offset: vec![],
        embedding,
        origin,
        dimensions,
        empty,
        missing: vec![],
        scope: Scope::default(),
    };
    if empty {
        return Ok(result);
    }
    let mut env = Environment::with_primitive_valuation(original.inputs, &input.assignments, c)?;
    env.object = Some(Arc::new(ObjectDomain::from_readings(
        original.inputs,
        input.witness.readings(),
        0,
        c,
    )?));
    env.missing_slot_reads.replace(Some(BTreeSet::new()));
    for ((slot, row), offset) in linear.slots.iter().zip(&linear.action).zip(&linear.offset) {
        let mut form =
            affine::constant(&Scalar::Z(offset.clone()), c)?.ok_or("整数商の定数がない")?;
        for (axis, coefficient) in linear.axes.iter().zip(row) {
            let parameter = affine::parameter(&Type::Z, axis, c)?;
            let coefficient = affine::constant(&Scalar::Z(coefficient.clone()), c)?;
            let term = affine::binary(BinOp::Mul, parameter.as_ref(), coefficient.as_ref(), c)?;
            form = affine::binary(BinOp::Add, Some(&form), term.as_ref(), c)?
                .ok_or("整数商の更新式がない")?;
        }
        env.affine_valuation.insert(slot.clone(), form);
    }
    let mut vars = BTreeMap::new();
    let mut checked = BTreeMap::new();
    let mut checks = owned_call::Checks::default();
    for (param, (name, v)) in params.iter().zip(&result.bindings) {
        env.owned_call_value_check(
            &param.ty,
            &crate::observed::term::affine::Value::Known(v.clone()),
            &checked,
            &decl.reading,
            decl.span,
            &mut checks,
        )?;
        checked.insert(name.as_str(), Some(v));
        vars.insert(
            name.clone(),
            SourceValue {
                known_value: Some(v.clone()),
                scalar_scope: Some(Scope::default()),
                scope: Scope::default(),
                support: vec![],
                condition_failed: false,
                condition_pending: false,
                symbolic: None,
                comparison: None,
                affine: affine::constant(v, c)?.map(Box::new),
            },
        );
    }
    result.scope.merge(&checks.scope);
    if checks.failure.is_some() || checks.blocked {
        result.missing = checks.missing;
        if !result.missing.is_empty() {
            return Ok(result);
        }
        return Err(unsupported(
            request,
            "整数商のView適用条件の公開配送は未実装",
        ));
    }
    let value = env.scoped_ast(*body, &vars, &Scope::default(), &decl.reading)?;
    result.scope.merge(&value.scope);
    result.missing = env
        .missing_slot_reads
        .take()
        .ok_or("整数商の不足収集がない")?
        .into_iter()
        .collect();
    if value.condition_failed || value.condition_pending {
        if !result.missing.is_empty() {
            return Ok(result);
        }
        return Err(unsupported(request, "整数商のView構成条件が未成立"));
    }
    let coordinates = value
        .affine
        .as_ref()
        .map(|form| form.integer_coordinates(&linear.axes, c))
        .transpose()?
        .flatten();
    let Some((constant, row)) = coordinates else {
        if !result.missing.is_empty() {
            return Ok(result);
        }
        return Err(unsupported(
            request,
            "整数商のViewが候補parameterのZアフィン式でない",
        ));
    };
    result.missing.clear();
    let mut offset = constant;
    for (a, x) in row.iter().zip(&result.origin) {
        c.checkpoint(Checkpoint::Quotient)?;
        offset += a * x;
    }
    result.matrix = integer_fiber::multiply(&vec![row], &result.embedding, dimensions, c)?;
    result.offset = vec![offset];
    Ok(result)
}
