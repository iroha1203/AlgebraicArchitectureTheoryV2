//! ArchMap 由来・観測座標解決と多項式式の反復 lowering（名前空間分離）。

use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{OriginKind, SourceRef};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::ValidationError;
use archsig_input::archmap::{
    CheckedArchMap, Origin, OriginKind as InputOriginKind, Slot, Snapshot, Subject, Value,
};
use archsig_input::law::shigure::ShigurePolyExpr;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};
use std::collections::BTreeSet;

pub(super) fn conv_err(detail: impl Into<String>) -> ValidationError {
    ValidationError::ConversionError {
        detail: detail.into(),
    }
}

pub(super) fn law_source_ref(decl_name: &str) -> SourceRef {
    SourceRef::new("law", OriginKind::HumanAdopted).with_law_declaration(decl_name)
}

fn lower_origin_kind(k: InputOriginKind) -> OriginKind {
    match k {
        InputOriginKind::StaticAnalysis => OriginKind::StaticAnalysis,
        InputOriginKind::RuntimeObservation => OriginKind::RuntimeObservation,
        InputOriginKind::LlmCandidate => OriginKind::LlmCandidate,
        InputOriginKind::HumanAdopted => OriginKind::HumanAdopted,
    }
}

fn origin_to_source_refs(
    origin: &Origin,
    atom_ref: Option<String>,
) -> Result<Vec<SourceRef>, ValidationError> {
    let Some(kind) = origin.kind else {
        return Err(conv_err(format!(
            "SHIGURE observed origin `{}` must declare an explicit `kind` (`static_analysis`, `runtime_observation`, `llm_candidate`, or `human_adopted`)",
            origin.id
        )));
    };
    let kind = lower_origin_kind(kind);
    if origin.locations.is_empty() {
        let mut r = SourceRef::new(&origin.id, kind);
        if let Some(a) = atom_ref {
            r = r.with_atom_ref(a);
        }
        return Ok(vec![r]);
    }
    let mut out = Vec::with_capacity(origin.locations.len());
    for loc in &origin.locations {
        let mut r =
            SourceRef::new(&origin.id, kind).with_location(&loc.source, &loc.path, loc.span);
        if let Some(a) = &atom_ref {
            r = r.with_atom_ref(a);
        }
        out.push(r);
    }
    Ok(out)
}

/// `observed <Entity.field>` 座標を ArchMap から解決し、値と全 `SourceLocation` 由来の
/// `SourceRef` 列を返す（複数 location の `atom_ref` を落とさない）。
pub(super) fn resolve_observed_coord(
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    entity: &str,
    field_full: &str,
    domain: &CoeffDomain,
    fallback_law_ref: &SourceRef,
) -> Result<(CoordValue, Vec<SourceRef>), ValidationError> {
    let mut matches: Vec<(&Snapshot, &Subject)> = Vec::new();
    for snap in archmap.snapshots() {
        if let Some(sid) = snapshot_id
            && snap.id != sid
        {
            continue;
        }
        for subj in &snap.subjects {
            if subj.ty.as_str() == entity {
                matches.push((snap, subj));
            }
        }
    }
    if matches.len() > 1 {
        return Err(conv_err(format!(
            "ambiguous observed subjects for entity `{entity}` (found {}); specify a snapshot or narrow ArchMap",
            matches.len()
        )));
    }
    let Some((snap, subj)) = matches.first().copied() else {
        let missing_ref = fallback_law_ref
            .clone()
            .with_atom_ref(format!("missing_subject:{entity}:{field_full}"));
        return Ok((CoordValue::Missing, vec![missing_ref]));
    };

    let field = subj
        .fields
        .iter()
        .find(|f| f.name.as_str() == field_full)
        .ok_or_else(|| ValidationError::UnknownRef {
            kind: "archmap field",
            name: field_full.to_owned(),
            context: format!("{}:{}", snap.id, subj.id),
        })?;

    match &field.slot {
        Slot::Missing => {
            let origin = archmap
                .origins()
                .iter()
                .find(|o| o.id == subj.origin)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "origin",
                    name: subj.origin.clone(),
                    context: format!("{}:{}", snap.id, subj.id),
                })?;
            let atom_slot = format!("{}:{}:{}", snap.id, subj.id, field_full);
            let refs = origin_to_source_refs(origin, Some(atom_slot))?;
            Ok((CoordValue::Missing, refs))
        }
        Slot::Known {
            atom,
            origin: origin_id,
            value,
            ..
        } => {
            let origin = archmap
                .origins()
                .iter()
                .find(|o| o.id == *origin_id)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "origin",
                    name: origin_id.clone(),
                    context: format!("{}:{}:{atom}", snap.id, subj.id),
                })?;
            let atom_ref = format!("{}:{}:{}:{atom}", snap.id, subj.id, field_full);
            let refs = origin_to_source_refs(origin, Some(atom_ref))?;
            let lit = archmap_value_to_scalar(value, domain, field_full)?;
            Ok((CoordValue::Observed(lit), refs))
        }
    }
}

fn archmap_value_to_scalar(
    value: &Value,
    domain: &CoeffDomain,
    context: &str,
) -> Result<ScalarLit, ValidationError> {
    match (value, domain) {
        (Value::Z(n), CoeffDomain::Z) => Ok(ScalarLit::Z(n.clone())),
        (Value::Q(num, den), CoeffDomain::Q) => {
            if *den <= BigInt::zero() {
                return Err(ValidationError::InvalidRational {
                    context: context.to_owned(),
                });
            }
            let g = num.gcd(den);
            Ok(ScalarLit::Q {
                num: num / &g,
                den: den / g,
            })
        }
        (Value::Fp(val), CoeffDomain::Fp(modulus)) => {
            if val >= modulus {
                return Err(ValidationError::InvalidFpLiteral {
                    context: context.to_owned(),
                });
            }
            Ok(ScalarLit::Fp {
                value: val.clone(),
                modulus: modulus.clone(),
            })
        }
        _ => Err(conv_err(format!(
            "observed field `{context}` value does not match presentation coefficient domain `{domain}`"
        ))),
    }
}

enum LowerFrame<'a> {
    Visit(&'a ShigurePolyExpr),
    ApplyNeg,
    ApplyAdd,
    ApplySub,
    ApplyMul,
    ApplyPow(u32),
}

/// 深い平坦和でもスタックを枯渇させない反復ワークリストによる `ShigurePolyExpr` → `PolyExpr` 変換。
pub(super) fn lower_poly_expr(
    expr: &ShigurePolyExpr,
    domain: &CoeffDomain,
    state_vars: &BTreeSet<String>,
    arg_vars: &BTreeSet<String>,
    param_vars: &BTreeSet<String>,
    forbidden_params: Option<&BTreeSet<String>>,
    context: &str,
) -> Result<PolyExpr, ValidationError> {
    // 名前空間の衝突を事前に検出し、暗黙シャドーイングを禁止する。
    for v in state_vars {
        if arg_vars.contains(v) || param_vars.contains(v) {
            return Err(conv_err(format!(
                "ambiguous identifier `{v}` appears in multiple variable namespaces in {context}"
            )));
        }
    }
    for v in arg_vars {
        if param_vars.contains(v) {
            return Err(conv_err(format!(
                "ambiguous identifier `{v}` appears as both argument and parameter in {context}"
            )));
        }
    }

    let mut work: Vec<LowerFrame<'_>> = vec![LowerFrame::Visit(expr)];
    let mut values: Vec<PolyExpr> = Vec::new();

    while let Some(frame) = work.pop() {
        match frame {
            LowerFrame::Visit(node) => match node {
                ShigurePolyExpr::Int(n) => {
                    let lit = match domain {
                        CoeffDomain::Z => ScalarLit::Z(n.clone()),
                        CoeffDomain::Q => ScalarLit::Q {
                            num: n.clone(),
                            den: BigInt::one(),
                        },
                        CoeffDomain::Fp(p) => {
                            let Some(u) = n.to_biguint() else {
                                return Err(ValidationError::InvalidFpLiteral {
                                    context: context.to_owned(),
                                });
                            };
                            if &u >= p {
                                return Err(ValidationError::InvalidFpLiteral {
                                    context: context.to_owned(),
                                });
                            }
                            ScalarLit::Fp {
                                value: u,
                                modulus: p.clone(),
                            }
                        }
                    };
                    values.push(PolyExpr::Const(lit));
                }
                ShigurePolyExpr::Rat { num, den } => {
                    if !matches!(domain, CoeffDomain::Q) {
                        return Err(ValidationError::DomainMismatch {
                            expected: domain.clone(),
                            actual: CoeffDomain::Q,
                            context: context.to_owned(),
                        });
                    }
                    if *den <= BigInt::zero() {
                        return Err(ValidationError::InvalidRational {
                            context: context.to_owned(),
                        });
                    }
                    let g = num.gcd(den);
                    values.push(PolyExpr::Const(ScalarLit::Q {
                        num: num / &g,
                        den: den / g,
                    }));
                }
                ShigurePolyExpr::Fp { value, modulus } => match domain {
                    CoeffDomain::Fp(expected) if expected == modulus => {
                        if value >= modulus {
                            return Err(ValidationError::InvalidFpLiteral {
                                context: context.to_owned(),
                            });
                        }
                        values.push(PolyExpr::Const(ScalarLit::Fp {
                            value: value.clone(),
                            modulus: modulus.clone(),
                        }));
                    }
                    _ => {
                        return Err(ValidationError::DomainMismatch {
                            expected: domain.clone(),
                            actual: CoeffDomain::Fp(modulus.clone()),
                            context: context.to_owned(),
                        });
                    }
                },
                ShigurePolyExpr::Var(v) => {
                    if state_vars.contains(v) {
                        values.push(PolyExpr::StateVar(v.clone()));
                    } else if arg_vars.contains(v) {
                        values.push(PolyExpr::ArgVar(v.clone()));
                    } else if param_vars.contains(v) {
                        values.push(PolyExpr::ParamVar(v.clone()));
                    } else if forbidden_params.is_some_and(|fp| fp.contains(v)) {
                        return Err(conv_err(format!(
                            "parameter `{v}` cannot appear in `before` presentation ({context})"
                        )));
                    } else {
                        return Err(ValidationError::UnknownRef {
                            kind: "variable",
                            name: v.clone(),
                            context: context.to_owned(),
                        });
                    }
                }
                ShigurePolyExpr::Neg(a) => {
                    work.push(LowerFrame::ApplyNeg);
                    work.push(LowerFrame::Visit(a));
                }
                ShigurePolyExpr::Add(a, b) => {
                    work.push(LowerFrame::ApplyAdd);
                    work.push(LowerFrame::Visit(b));
                    work.push(LowerFrame::Visit(a));
                }
                ShigurePolyExpr::Sub(a, b) => {
                    work.push(LowerFrame::ApplySub);
                    work.push(LowerFrame::Visit(b));
                    work.push(LowerFrame::Visit(a));
                }
                ShigurePolyExpr::Mul(a, b) => {
                    work.push(LowerFrame::ApplyMul);
                    work.push(LowerFrame::Visit(b));
                    work.push(LowerFrame::Visit(a));
                }
                ShigurePolyExpr::Pow(a, exp) => {
                    work.push(LowerFrame::ApplyPow(*exp));
                    work.push(LowerFrame::Visit(a));
                }
            },
            LowerFrame::ApplyNeg => {
                let a = values.pop().expect("neg operand");
                values.push(PolyExpr::negate(a));
            }
            LowerFrame::ApplyAdd => {
                let b = values.pop().expect("add rhs");
                let a = values.pop().expect("add lhs");
                values.push(PolyExpr::sum(a, b));
            }
            LowerFrame::ApplySub => {
                let b = values.pop().expect("sub rhs");
                let a = values.pop().expect("sub lhs");
                values.push(PolyExpr::diff(a, b));
            }
            LowerFrame::ApplyMul => {
                let b = values.pop().expect("mul rhs");
                let a = values.pop().expect("mul lhs");
                values.push(PolyExpr::prod(a, b));
            }
            LowerFrame::ApplyPow(exp) => {
                let a = values.pop().expect("pow base");
                values.push(PolyExpr::pow(a, exp));
            }
        }
    }

    Ok(values.pop().expect("root lowered expression"))
}
