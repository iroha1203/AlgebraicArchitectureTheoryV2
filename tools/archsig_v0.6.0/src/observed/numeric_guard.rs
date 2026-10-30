//! 通常評価の数値guardを正規化し、非線形の未対応理由を部分表示に残す。
use super::*;
use crate::construction::ConstructionFailure;
use crate::law::ast::UnOp;
use crate::observed::{
    affine::{self, Form, TermArgument},
    equation_polynomial::EquationPolynomial as Polynomial,
};

#[derive(Default)]
pub(super) struct Analysis {
    pub forms: Option<Vec<Form>>,
    pub unsupported_numeric: bool,
    pub missing: Vec<Fact>,
}
#[derive(Clone, Default)]
struct Normalized {
    basis: Vec<TermArgument>,
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
    let (result, missing) = change_affine::capture_missing(env, || {
        analyze_inner(env, id, vars, base, reading, &mut Normalized::default())
    })?;
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
        if let Some(forms) = change_affine::guard_forms(env, id, vars, base, reading)? {
            return Ok(Analysis {
                forms: Some(forms),
                ..Analysis::default()
            });
        }
        let value = env.scoped_ast(id, vars, base, reading)?;
        if value.condition_failed || value.condition_pending {
            return Ok(Analysis::default());
        }
        match &env.inputs.law().exprs[id].kind {
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
            ExprKind::Binary {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                let left = analyze_inner(env, *lhs, vars, base, reading, normalized)?;
                let right = analyze_inner(env, *rhs, vars, base, reading, normalized)?;
                Ok(Analysis {
                    forms: match (left.forms, right.forms) {
                        (Some(mut left), Some(right)) => {
                            left.extend(right);
                            Some(left)
                        }
                        _ => None,
                    },
                    unsupported_numeric: left.unsupported_numeric || right.unsupported_numeric,
                    missing: vec![],
                })
            }
            ExprKind::Binary {
                op: BinOp::Eq,
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
                    .binary(BinOp::Sub, &right, &mut env.control.clone())
                    .map_err(invalid)?;
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
                        let argument =
                            affine::term_argument(normalized.basis[*index].clone(), &env.control)?;
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
        if let Some(form) = value.affine.as_deref() {
            if let Some((constant, terms)) = form.numeric_parameter_terms(&env.control)? {
                let mut control = env.control.clone();
                let mut result = Polynomial::constant(constant, &mut control).map_err(invalid)?;
                for (argument, coefficient) in terms {
                    let index = match normalized.basis.iter().position(|a| a == &argument) {
                        Some(index) => index,
                        None => {
                            normalized.basis.push(argument);
                            normalized.basis.len() - 1
                        }
                    };
                    let variable =
                        Polynomial::variable(&result.ty, index, &mut control).map_err(invalid)?;
                    let coefficient =
                        Polynomial::constant(coefficient, &mut control).map_err(invalid)?;
                    let term = variable
                        .binary(BinOp::Mul, &coefficient, &mut control)
                        .map_err(invalid)?;
                    result = result
                        .binary(BinOp::Add, &term, &mut control)
                        .map_err(invalid)?;
                }
                return Ok(Some(result));
            }
        }
        match &env.inputs.law().exprs[id].kind {
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
                left.binary(*op, &right, &mut env.control.clone())
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
                let mut control = env.control.clone();
                let zero = numeric::zero(&value.ty, &control)?;
                Polynomial::constant(zero, &mut control)
                    .map_err(invalid)?
                    .binary(BinOp::Sub, &value, &mut control)
                    .map(Some)
                    .map_err(invalid)
            }
            _ => Ok(None),
        }
    })
}
