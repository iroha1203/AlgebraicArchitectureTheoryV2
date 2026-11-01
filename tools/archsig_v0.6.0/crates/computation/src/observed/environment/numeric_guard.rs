//! 通常評価の数値guardを正規化し、対応範囲と未決理由を部分表示に残す。
use super::*;
use crate::construction::ConstructionFailure;
use crate::observed::environment::state::ScopedReplace;
use crate::observed::{
    affine::{self, Form},
    equation_polynomial::EquationPolynomial as Polynomial,
};
use archsig_input::law::ast::UnOp;

#[derive(Default)]
pub(super) struct Analysis {
    pub forms: Option<Vec<Form>>,
    pub unsupported_numeric: bool,
    pub missing: Vec<Fact>,
}
fn constant_guard(value: bool, control: &Control) -> Result<Analysis, ValidationFailure> {
    Ok(Analysis {
        forms: Some(if value {
            vec![]
        } else {
            vec![affine::constant(&Scalar::Z(1.into()), control)?.ok_or("偽guardの定数がない")?]
        }),
        ..Analysis::default()
    })
}
fn constant_forms(
    forms: &Option<Vec<Form>>,
    control: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    let Some(forms) = forms else {
        return Ok(None);
    };
    let mut known = true;
    for form in forms {
        control.checkpoint(archsig_common::control::Checkpoint::ObjectLawFamily)?;
        match form.value(control)? {
            Some(value) if value != numeric::zero(&value.ty(), control)? => return Ok(Some(false)),
            Some(_) => (),
            None => known = false,
        }
    }
    Ok(known.then_some(true))
}
fn numeric_forms(forms: &Option<Vec<Form>>, control: &Control) -> Result<bool, ValidationFailure> {
    let Some(forms) = forms else {
        return Ok(false);
    };
    for form in forms {
        if form.numeric_parameter_terms(control)?.is_none()
            && form.parameter_coordinates(control)?.is_none()
        {
            return Ok(false);
        }
    }
    Ok(true)
}
fn negated(value: Analysis, control: &Control) -> Result<Analysis, ValidationFailure> {
    if let Some(holds) = constant_forms(&value.forms, control)? {
        return constant_guard(!holds, control);
    }
    Ok(Analysis {
        unsupported_numeric: value.unsupported_numeric || numeric_forms(&value.forms, control)?,
        ..Analysis::default()
    })
}
#[derive(Clone, Default)]
struct Normalized {
    basis: Vec<Form>,
    bindings: BTreeMap<String, Polynomial>,
}
fn invalid(error: ConstructionFailure) -> ValidationFailure {
    match error {
        ConstructionFailure::Stopped(reason) => reason.into(),
        error => format!("数値guardの正規化: {error:?}").into(),
    }
}
/// 既存の線形解析を優先し、その外側では正確な数値多項式だけを分類する。
/// 分類できない式を未対応算法へ丸めず、呼出し側の構成検査に残す。
pub(super) fn analyze(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    base: &Scope,
    reading: &str,
) -> Result<Analysis, ValidationFailure> {
    let outer = env.state.value_read.scoped(true);
    let captured = change_affine::capture_missing(env, || {
        analyze_inner(env, id, vars, base, reading, &mut Normalized::default())
    });
    outer.restore();
    let (result, missing) = captured?;
    let mut result = result?;
    result.missing = missing;
    Ok(result)
}
fn analyze_inner(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    base: &Scope,
    reading: &str,
    normalized: &mut Normalized,
) -> Result<Analysis, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        if let Some(forms) = change_affine::affine_guard_forms(env, id, vars, base, reading)? {
            return Ok(Analysis {
                forms: Some(forms),
                ..Analysis::default()
            });
        }
        let value = env.scoped_ast(id, vars, base, reading)?;
        if value.condition_failed || value.condition_pending {
            return Ok(Analysis::default());
        }
        if let Some(mut call) = selected_body(env, id, vars, base, reading, normalized)? {
            let result = analyze_inner(
                env,
                call.body,
                &call.variables,
                &call.base,
                &call.reading,
                &mut call.normalized,
            );
            normalized.basis = call.normalized.basis;
            return result;
        }
        match &env.indexes.inputs.law().exprs()[id].kind {
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => match env.scoped_ast(*cond, vars, base, reading)?.known_value {
                Some(Scalar::Bool(take)) => analyze_inner(
                    env,
                    if take { *then_branch } else { *else_branch },
                    vars,
                    base,
                    reading,
                    normalized,
                ),
                _ => Ok(Analysis::default()),
            },
            ExprKind::Group(body) => analyze_inner(env, *body, vars, base, reading, normalized),
            ExprKind::Let { name, value, body } => {
                let mut normalized = normalized.clone();
                let normalized_value =
                    polynomial(env, *value, vars, base, reading, &mut normalized)?;
                let value = env.scoped_ast(*value, vars, base, reading)?;
                if value.condition_failed || value.condition_pending {
                    return Ok(Analysis::default());
                }
                if let Some(polynomial) = normalized_value {
                    normalized.bindings.insert(name.name.clone(), polynomial);
                } else {
                    normalized.bindings.remove(&name.name);
                }
                let mut vars = vars.clone();
                vars.insert(name.name.clone(), value);
                analyze_inner(env, *body, &vars, base, reading, &mut normalized)
            }
            ExprKind::Unary {
                op: UnOp::Not,
                operand,
            } => {
                let mut child = *operand;
                while let ExprKind::Group(body) = env.indexes.inputs.law().exprs()[child].kind {
                    env.tick()?;
                    child = body;
                }
                if let ExprKind::Unary {
                    op: UnOp::Not,
                    operand,
                } = env.indexes.inputs.law().exprs()[child].kind
                {
                    return analyze_inner(env, operand, vars, base, reading, normalized);
                }
                let value = analyze_inner(env, *operand, vars, base, reading, normalized)?;
                negated(value, &env.control)
            }
            ExprKind::Binary {
                op: op @ (BinOp::And | BinOp::Or | BinOp::Implies),
                lhs,
                rhs,
            } => {
                let left = analyze_inner(env, *lhs, vars, base, reading, normalized)?;
                let right = analyze_inner(env, *rhs, vars, base, reading, normalized)?;
                let a = constant_forms(&left.forms, &env.control)?;
                let z = constant_forms(&right.forms, &env.control)?;
                match (*op, a, z) {
                    (BinOp::And, Some(false), _) | (BinOp::And, _, Some(false)) => {
                        return constant_guard(false, &env.control);
                    }
                    (BinOp::Or, Some(true), _)
                    | (BinOp::Or, _, Some(true))
                    | (BinOp::Implies, Some(false), _)
                    | (BinOp::Implies, _, Some(true)) => return constant_guard(true, &env.control),
                    (BinOp::And, Some(true), _)
                    | (BinOp::Or, Some(false), _)
                    | (BinOp::Implies, Some(true), _) => return Ok(right),
                    (BinOp::And, _, Some(true)) | (BinOp::Or, _, Some(false)) => return Ok(left),
                    (BinOp::Implies, _, Some(false)) => return negated(left, &env.control),
                    _ => (),
                }
                if *op == BinOp::Implies && left.forms.is_some() && left.forms == right.forms {
                    return constant_guard(true, &env.control);
                }
                let unsupported_numeric = left.unsupported_numeric
                    || right.unsupported_numeric
                    || (*op != BinOp::And
                        && numeric_forms(&left.forms, &env.control)?
                        && numeric_forms(&right.forms, &env.control)?
                        && left.forms != right.forms);
                let forms = match (left.forms, right.forms) {
                    (Some(mut left), Some(right)) if *op == BinOp::And => {
                        left.extend(right);
                        Some(left)
                    }
                    (Some(left), Some(right)) if left == right => Some(left),
                    _ => None,
                };
                Ok(Analysis {
                    forms,
                    unsupported_numeric,
                    missing: vec![],
                })
            }
            ExprKind::Binary {
                op: op @ (BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge),
                lhs,
                rhs,
            } => {
                let Some(left) = polynomial(env, *lhs, vars, base, reading, normalized)? else {
                    return Ok(Analysis::default());
                };
                let Some(right) = polynomial(env, *rhs, vars, base, reading, normalized)? else {
                    return Ok(Analysis::default());
                };
                let difference = left
                    .binary(BinOp::Sub, &right, &env.control)
                    .map_err(invalid)?;
                if *op != BinOp::Eq {
                    if let Some(value) = difference.evaluate(&[], &env.control).map_err(invalid)? {
                        let zero = numeric::zero(&difference.ty, &env.control)?;
                        let Scalar::Bool(holds) =
                            numeric::binary(*op, value.scalar(), &zero, &env.control)?
                        else {
                            return Err("数値比較がBoolでない".into());
                        };
                        return constant_guard(holds, &env.control);
                    }
                    return Ok(Analysis {
                        unsupported_numeric: true,
                        ..Analysis::default()
                    });
                }
                if difference.terms.iter().any(|term| term.variables.len() > 1) {
                    return Ok(Analysis {
                        unsupported_numeric: true,
                        ..Analysis::default()
                    });
                }
                let zero = numeric::zero(&difference.ty, &env.control)?;
                let mut form =
                    affine::constant(&zero, &env.control)?.ok_or("数値guardの零形式がない")?;
                for term in difference.terms {
                    let coefficient = affine::constant(term.coefficient.scalar(), &env.control)?
                        .ok_or("数値guardの係数がない")?;
                    let value = if let Some(index) = term.variables.first() {
                        let argument = normalized.basis[*index].clone();
                        affine::binary(
                            BinOp::Mul,
                            Some(&coefficient),
                            Some(&argument),
                            &env.control,
                        )?
                        .ok_or("数値guardの一次項がない")?
                    } else {
                        coefficient
                    };
                    form = affine::binary(BinOp::Add, Some(&form), Some(&value), &env.control)?
                        .ok_or("数値guardの和がない")?;
                }
                Ok(Analysis {
                    forms: Some(vec![form]),
                    ..Analysis::default()
                })
            }
            _ => Ok(Analysis::default()),
        }
    })
}
// 葉の値・束縛・選択は通常Evaluatorに任せる。既存多項式演算で相殺後の次数を確認する。
fn polynomial(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    base: &Scope,
    reading: &str,
    normalized: &mut Normalized,
) -> Result<Option<Polynomial>, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let value = env.scoped_ast(id, vars, base, reading)?;
        if value.condition_failed || value.condition_pending {
            return Ok(None);
        }
        if let Some(value @ (Scalar::Z(_) | Scalar::Q(..))) = value.known_value.as_ref() {
            return Polynomial::constant(value.clone(), &env.control)
                .map(Some)
                .map_err(invalid);
        }
        let coordinates = if let Some(form) = value.affine.as_deref() {
            if let Some((constant, terms)) = form.numeric_parameter_terms(&env.control)? {
                let terms = terms
                    .into_iter()
                    .map(|(argument, coefficient)| {
                        Ok((affine::term_argument(argument, &env.control)?, coefficient))
                    })
                    .collect::<Result<Vec<_>, ValidationFailure>>()?;
                Some((constant, terms))
            } else if let Some((constant, terms)) = form.parameter_coordinates(&env.control)? {
                let terms = terms
                    .into_iter()
                    .map(|(parameter, coefficient)| {
                        Ok((
                            affine::parameter(&parameter.kind.ty(), &parameter, &env.control)?
                                .ok_or("数値binderの形式がない")?,
                            coefficient,
                        ))
                    })
                    .collect::<Result<Vec<_>, ValidationFailure>>()?;
                Some((constant, terms))
            } else {
                None
            }
        } else {
            None
        };
        if let Some((constant, terms)) = coordinates {
            let control = env.control.clone();
            let mut result = Polynomial::constant(constant, &control).map_err(invalid)?;
            for (argument, coefficient) in terms {
                let index = match normalized.basis.iter().position(|a| a == &argument) {
                    Some(index) => index,
                    None => {
                        normalized.basis.push(argument);
                        normalized.basis.len() - 1
                    }
                };
                let variable =
                    Polynomial::variable(&result.ty, index, &control).map_err(invalid)?;
                let coefficient = Polynomial::constant(coefficient, &control).map_err(invalid)?;
                let term = variable
                    .binary(BinOp::Mul, &coefficient, &control)
                    .map_err(invalid)?;
                result = result
                    .binary(BinOp::Add, &term, &control)
                    .map_err(invalid)?;
            }
            return Ok(Some(result));
        }
        if let Some(mut call) = selected_body(env, id, vars, base, reading, normalized)? {
            let result = polynomial(
                env,
                call.body,
                &call.variables,
                &call.base,
                &call.reading,
                &mut call.normalized,
            );
            normalized.basis = call.normalized.basis;
            return result;
        }
        match &env.indexes.inputs.law().exprs()[id].kind {
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => match env.scoped_ast(*cond, vars, base, reading)?.known_value {
                Some(Scalar::Bool(take)) => polynomial(
                    env,
                    if take { *then_branch } else { *else_branch },
                    vars,
                    base,
                    reading,
                    normalized,
                ),
                _ => Ok(None),
            },

            ExprKind::Dotted(path) if path.len() == 1 => {
                Ok(normalized.bindings.get(&path[0].name).cloned())
            }
            ExprKind::Let { name, value, body } => {
                let mut child = normalized.clone();
                let normalized_value = polynomial(env, *value, vars, base, reading, &mut child)?;
                let value = env.scoped_ast(*value, vars, base, reading)?;
                if value.condition_failed || value.condition_pending {
                    return Ok(None);
                }
                if let Some(polynomial) = normalized_value {
                    child.bindings.insert(name.name.clone(), polynomial);
                } else {
                    child.bindings.remove(&name.name);
                }
                let mut vars = vars.clone();
                vars.insert(name.name.clone(), value);
                let result = polynomial(env, *body, &vars, base, reading, &mut child);
                normalized.basis = child.basis;
                result
            }

            ExprKind::Group(body) => polynomial(env, *body, vars, base, reading, normalized),
            ExprKind::Binary {
                op: op @ (BinOp::Add | BinOp::Sub | BinOp::Mul),
                lhs,
                rhs,
            } => {
                let Some(left) = polynomial(env, *lhs, vars, base, reading, normalized)? else {
                    return Ok(None);
                };
                let Some(right) = polynomial(env, *rhs, vars, base, reading, normalized)? else {
                    return Ok(None);
                };
                left.binary(*op, &right, &env.control)
                    .map(Some)
                    .map_err(invalid)
            }
            ExprKind::Unary {
                op: UnOp::Neg,
                operand,
            } => {
                let Some(value) = polynomial(env, *operand, vars, base, reading, normalized)?
                else {
                    return Ok(None);
                };
                let control = env.control.clone();
                let zero = numeric::zero(&value.ty, &control)?;
                Polynomial::constant(zero, &control)
                    .map_err(invalid)?
                    .binary(BinOp::Sub, &value, &control)
                    .map(Some)
                    .map_err(invalid)
            }
            _ => Ok(None),
        }
    })
}

struct ScopedBody {
    body: usize,
    variables: BTreeMap<String, SourceValue>,
    base: Scope,
    reading: String,
    normalized: Normalized,
}
// named_viewの静的解決と通常Evaluatorの引数を共有する。呼出し全体の条件検査は
// 呼出し元のscoped_astが既に終えており、calleeの自由変数をcallerから補わない。
fn selected_body(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    base: &Scope,
    reading: &str,
    normalized: &mut Normalized,
) -> Result<Option<ScopedBody>, ValidationFailure> {
    if let ExprKind::Match { scrutinee, arms } = &env.indexes.inputs.law().exprs()[id].kind {
        let input = env.scoped_ast(*scrutinee, vars, base, reading)?;
        let Some((arm, variables)) = env.scoped_match_bindings(id, &input, vars)? else {
            return Ok(None);
        };
        let mut child = normalized.clone();
        if let archsig_input::law::ast::Pattern::Name(name) = &arms[arm].pattern
            && variables.contains_key(&name.name)
            && !vars.contains_key(&name.name)
        {
            if let Some(value) = polynomial(env, *scrutinee, vars, base, reading, &mut child)? {
                child.bindings.insert(name.name.clone(), value);
            } else {
                child.bindings.remove(&name.name);
            }
        }
        return Ok(Some(ScopedBody {
            body: arms[arm].body,
            variables,
            base: base.clone(),
            reading: reading.into(),
            normalized: child,
        }));
    }
    let Some(declaration) = env.named_view(id)? else {
        return Ok(None);
    };
    let archsig_input::law::model::Signature::View { params, body, .. } = &declaration.signature
    else {
        return Err("数値guardのcalleeがviewでない".into());
    };
    let ExprKind::Call { args, .. } = &env.indexes.inputs.law().exprs()[id].kind else {
        return Err("数値guardの呼出し式がない".into());
    };
    if params.len() != args.len() {
        return Err("数値guardの呼出し引数数が違う".into());
    }
    let mut variables = BTreeMap::new();
    let mut bindings = BTreeMap::new();
    let mut call_base = base.clone();
    call_base.readings.insert(declaration.reading.clone());
    for (parameter, argument) in params.iter().zip(args) {
        env.tick()?;
        if let Some(value) = polynomial(env, *argument, vars, base, reading, normalized)? {
            bindings.insert(parameter.name.clone(), value);
        }
        let value = env.scoped_ast(*argument, vars, base, reading)?;
        call_base.merge(&value.scope);
        variables.insert(parameter.name.clone(), value);
    }
    for value in variables.values_mut() {
        value.scope.merge(&call_base);
    }
    Ok(Some(ScopedBody {
        body: *body,
        variables,
        base: call_base,
        reading: declaration.reading.clone(),
        normalized: Normalized {
            basis: normalized.basis.clone(),
            bindings,
        },
    }))
}
