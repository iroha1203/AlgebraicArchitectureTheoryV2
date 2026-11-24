//! 変数順序 `VarOrder`・名前空間束縛 `ExprBindings`・`PolyExpr` 展開・多項式エラー型。

use crate::algebra::poly::Poly;
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::ir::term::{PolyExpr, ScalarLit};
use archsig_common::prime::is_prime;
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// 多項式環計算で発生し得るエラー。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgebraError {
    /// 未観測値への依存が残るため多項式展開できない（沈黙へ接続）。
    UnobservedDependency { slots: Vec<String> },
    /// 環に未登録の変数を参照した。
    UnknownVariable { name: String },
    /// 係数域が計算環と一致しない。
    DomainMismatch { expected: String, actual: String },
    /// 素数でない法を指定した。
    InvalidPrimeModulus { modulus: BigUint },
    /// 変数数の不一致。
    ArityMismatch { expected: usize, actual: usize },
    /// 計算資源・ステップ上限超過または適用域外。
    OutOfScope { detail: String },
}

impl fmt::Display for AlgebraError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AlgebraError::UnobservedDependency { slots } => {
                write!(
                    f,
                    "expression depends on unobserved slots: {}",
                    slots.join(", ")
                )
            }
            AlgebraError::UnknownVariable { name } => write!(f, "unknown variable `{name}`"),
            AlgebraError::DomainMismatch { expected, actual } => {
                write!(
                    f,
                    "coefficient domain mismatch: expected {expected}, got {actual}"
                )
            }
            AlgebraError::InvalidPrimeModulus { modulus } => {
                write!(f, "modulus `{modulus}` is not prime")
            }
            AlgebraError::ArityMismatch { expected, actual } => {
                write!(f, "arity mismatch: expected {expected}, got {actual}")
            }
            AlgebraError::OutOfScope { detail } => write!(f, "out of scope: {detail}"),
        }
    }
}

impl std::error::Error for AlgebraError {}

/// 多項式環の変数順序（インデックス 0 が最上位変数）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VarOrder {
    vars: Vec<String>,
    index: BTreeMap<String, usize>,
}

impl VarOrder {
    pub fn new(vars: Vec<String>) -> Result<Self, AlgebraError> {
        let mut index = BTreeMap::new();
        for (i, v) in vars.iter().enumerate() {
            if v.trim().is_empty() || index.insert(v.clone(), i).is_some() {
                return Err(AlgebraError::OutOfScope {
                    detail: format!("invalid or duplicate variable name `{v}`"),
                });
            }
        }
        Ok(Self { vars, index })
    }

    pub fn len(&self) -> usize {
        self.vars.len()
    }

    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }

    pub fn vars(&self) -> &[String] {
        &self.vars
    }

    pub fn index_of(&self, name: &str) -> Option<usize> {
        self.index.get(name).copied()
    }

    /// 先頭に補助変数（Rabinowitsch 変数等）を追加した消去用の変数順序を返す。
    pub fn prepend_vars(&self, extra: Vec<String>) -> Result<Self, AlgebraError> {
        let mut combined = extra;
        combined.extend(self.vars.iter().cloned());
        Self::new(combined)
    }
}

/// `PolyExpr` の 3 名前空間（`StateVar` / `ArgVar` / `ParamVar`）を互いに分離して
/// 多項式環の変数インデックスへ対応付ける束縛表。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprBindings {
    num_vars: usize,
    state_vars: BTreeMap<String, usize>,
    arg_vars: BTreeMap<String, usize>,
    param_vars: BTreeMap<String, usize>,
}

impl ExprBindings {
    /// `VarOrder` の全変数を `ParamVar` 名前空間のみに束縛する（状態変数・引数変数は未束縛）。
    pub fn params_only(vars: &VarOrder) -> Self {
        let mut param_vars = BTreeMap::new();
        for (i, name) in vars.vars().iter().enumerate() {
            param_vars.insert(name.clone(), i);
        }
        Self {
            num_vars: vars.len(),
            state_vars: BTreeMap::new(),
            arg_vars: BTreeMap::new(),
            param_vars,
        }
    }

    /// 状態変数・引数変数・パラメータ変数の 3 名前空間を順に `[state..., arg..., param...]` へ配置し、
    /// 対応する `VarOrder` と `ExprBindings` を構築する。
    /// 異なる名前空間間で同名変数がある場合は表示名のみ接頭辞で分離し、名前空間自体は衝突させない。
    pub fn from_slices(
        state_names: &[String],
        arg_names: &[String],
        param_names: &[String],
    ) -> Result<(VarOrder, Self), AlgebraError> {
        for (kind, names) in [
            ("state", state_names),
            ("arg", arg_names),
            ("param", param_names),
        ] {
            let mut seen = BTreeSet::new();
            for name in names {
                if name.trim().is_empty() || !seen.insert(name.as_str()) {
                    return Err(AlgebraError::OutOfScope {
                        detail: format!("invalid or duplicate {kind} variable name `{name}`"),
                    });
                }
            }
        }

        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for name in state_names
            .iter()
            .chain(arg_names.iter())
            .chain(param_names.iter())
        {
            *counts.entry(name.as_str()).or_insert(0) += 1;
        }

        let mut used_display: BTreeSet<String> = BTreeSet::new();
        let mut display_vars: Vec<String> =
            Vec::with_capacity(state_names.len() + arg_names.len() + param_names.len());
        let mut state_vars = BTreeMap::new();
        let mut arg_vars = BTreeMap::new();
        let mut param_vars = BTreeMap::new();

        let mut push_var = |prefix: &str, name: &str, map: &mut BTreeMap<String, usize>| {
            let idx = display_vars.len();
            let base = if counts.get(name).copied().unwrap_or(0) > 1 {
                format!("{prefix}::{name}")
            } else {
                name.to_owned()
            };
            let mut disp = base;
            while !used_display.insert(disp.clone()) {
                disp.push('_');
            }
            display_vars.push(disp);
            map.insert(name.to_owned(), idx);
        };

        for name in state_names {
            push_var("state", name, &mut state_vars);
        }
        for name in arg_names {
            push_var("arg", name, &mut arg_vars);
        }
        for name in param_names {
            push_var("param", name, &mut param_vars);
        }

        let order = VarOrder::new(display_vars)?;
        let bindings = Self {
            num_vars: order.len(),
            state_vars,
            arg_vars,
            param_vars,
        };
        Ok((order, bindings))
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    pub fn state_index(&self, name: &str) -> Option<usize> {
        self.state_vars.get(name).copied()
    }

    pub fn arg_index(&self, name: &str) -> Option<usize> {
        self.arg_vars.get(name).copied()
    }

    pub fn param_index(&self, name: &str) -> Option<usize> {
        self.param_vars.get(name).copied()
    }
}

fn expand_expr_with<C, F>(
    expr: &PolyExpr,
    bindings: &ExprBindings,
    zero: &C,
    lit_to_coeff: &F,
) -> Result<Poly<C>, AlgebraError>
where
    C: RingCoeff,
    F: Fn(&ScalarLit) -> Result<C, AlgebraError>,
{
    let n = bindings.num_vars();
    match expr {
        PolyExpr::Const(lit) => Ok(Poly::constant(n, lit_to_coeff(lit)?)),
        PolyExpr::StateVar(v) => {
            let idx = bindings
                .state_index(v)
                .ok_or_else(|| AlgebraError::UnknownVariable {
                    name: format!("state:{v}"),
                })?;
            Ok(Poly::var(n, idx, zero.clone()))
        }
        PolyExpr::ArgVar(v) => {
            let idx = bindings
                .arg_index(v)
                .ok_or_else(|| AlgebraError::UnknownVariable {
                    name: format!("arg:{v}"),
                })?;
            Ok(Poly::var(n, idx, zero.clone()))
        }
        PolyExpr::ParamVar(v) => {
            let idx = bindings
                .param_index(v)
                .ok_or_else(|| AlgebraError::UnknownVariable {
                    name: format!("param:{v}"),
                })?;
            Ok(Poly::var(n, idx, zero.clone()))
        }
        PolyExpr::Unobserved { slot, .. } => Err(AlgebraError::UnobservedDependency {
            slots: vec![slot.clone()],
        }),
        PolyExpr::Neg(e) => Ok(expand_expr_with(e, bindings, zero, lit_to_coeff)?.neg()),
        PolyExpr::Add(a, b) => Ok(expand_expr_with(a, bindings, zero, lit_to_coeff)?
            .add(&expand_expr_with(b, bindings, zero, lit_to_coeff)?)),
        PolyExpr::Sub(a, b) => Ok(expand_expr_with(a, bindings, zero, lit_to_coeff)?
            .sub(&expand_expr_with(b, bindings, zero, lit_to_coeff)?)),
        PolyExpr::Mul(a, b) => expand_expr_with(a, bindings, zero, lit_to_coeff)?
            .checked_mul(&expand_expr_with(b, bindings, zero, lit_to_coeff)?),
        PolyExpr::Pow(e, exp) => {
            expand_expr_with(e, bindings, zero, lit_to_coeff)?.checked_pow(*exp)
        }
    }
}

fn check_unobserved(expr: &PolyExpr) -> Result<(), AlgebraError> {
    let mut missing = BTreeSet::new();
    expr.collect_unobserved(&mut missing);
    if !missing.is_empty() {
        return Err(AlgebraError::UnobservedDependency {
            slots: missing.into_iter().collect(),
        });
    }
    Ok(())
}

impl Poly<Rat> {
    /// `PolyExpr` を `Q` 上の多項式へ展開する。未観測値を含む場合は零化せず `UnobservedDependency` を返す。
    pub fn from_expr_q(expr: &PolyExpr, bindings: &ExprBindings) -> Result<Self, AlgebraError> {
        check_unobserved(expr)?;
        let zero = Rat::zero();
        expand_expr_with(expr, bindings, &zero, &|lit| match lit {
            ScalarLit::Q { num, den } => {
                Rat::new(num.clone(), den.clone()).ok_or_else(|| AlgebraError::OutOfScope {
                    detail: "zero denominator in rational literal".to_owned(),
                })
            }
            ScalarLit::Z(z) => Ok(Rat::from_int(z.clone())),
            ScalarLit::Fp { modulus, .. } => Err(AlgebraError::DomainMismatch {
                expected: "Q".to_owned(),
                actual: format!("Fp({modulus})"),
            }),
        })
    }
}

impl Poly<BigInt> {
    /// `PolyExpr` を `Z` 上の多項式へ展開する。
    pub fn from_expr_z(expr: &PolyExpr, bindings: &ExprBindings) -> Result<Self, AlgebraError> {
        check_unobserved(expr)?;
        let zero = BigInt::zero();
        expand_expr_with(expr, bindings, &zero, &|lit| match lit {
            ScalarLit::Z(z) => Ok(z.clone()),
            other => Err(AlgebraError::DomainMismatch {
                expected: "Z".to_owned(),
                actual: other.domain().to_string(),
            }),
        })
    }
}

impl Poly<FpElem> {
    /// `PolyExpr` を素数体 `Fp(modulus)` 上の多項式へ展開する。
    pub fn from_expr_fp(
        expr: &PolyExpr,
        bindings: &ExprBindings,
        modulus: &BigUint,
    ) -> Result<Self, AlgebraError> {
        if !is_prime(modulus) {
            return Err(AlgebraError::InvalidPrimeModulus {
                modulus: modulus.clone(),
            });
        }
        check_unobserved(expr)?;
        let zero = FpElem::from_checked_prime(BigInt::zero(), modulus.clone());
        expand_expr_with(expr, bindings, &zero, &|lit| match lit {
            ScalarLit::Fp {
                value,
                modulus: lit_mod,
            } => {
                if lit_mod != modulus {
                    return Err(AlgebraError::DomainMismatch {
                        expected: format!("Fp({modulus})"),
                        actual: format!("Fp({lit_mod})"),
                    });
                }
                Ok(FpElem::from_checked_prime(
                    BigInt::from(value.clone()),
                    modulus.clone(),
                ))
            }
            other => Err(AlgebraError::DomainMismatch {
                expected: format!("Fp({modulus})"),
                actual: other.domain().to_string(),
            }),
        })
    }
}
