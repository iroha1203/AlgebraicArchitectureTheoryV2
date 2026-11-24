//! 全 syzygy 平方零 lift・相対障害・宣言被覆比較・有限 étale 被覆 cocycle descent の検証済み IR
//! （G-141 E1–E8・C8–C9・H1–H4・H10 / W5）。

use crate::ir::change::NamedPoly;
use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::{ValidationError, validate_coeff_domain};
use std::collections::{BTreeMap, BTreeSet};

/// 平方零拡大 `R' ↠ R` の入力仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SquareZeroSpec {
    /// 1 変数打ち切り冪零商の 1 段拡大 `k[var]/(var^{base_degree + 2}) ↠ k[var]/(var^{base_degree + 1})`。
    TruncatedPoly { var_name: String, base_degree: usize },
    /// 乗法表と射影行列による明示的有限代数拡大（`M² = 0` は計算核で厳密検証する）。
    ExplicitTable {
        r_prime_basis: Vec<String>,
        r_prime_one: Vec<ScalarLit>,
        r_prime_mul: Vec<Vec<Vec<ScalarLit>>>,
        r_base_basis: Vec<String>,
        r_base_one: Vec<ScalarLit>,
        r_base_mul: Vec<Vec<Vec<ScalarLit>>>,
        projection: Vec<Vec<ScalarLit>>,
    },
}

impl SquareZeroSpec {
    pub fn r_base_dim(&self) -> usize {
        match self {
            SquareZeroSpec::TruncatedPoly { base_degree, .. } => base_degree + 1,
            SquareZeroSpec::ExplicitTable { r_base_basis, .. } => r_base_basis.len(),
        }
    }

    pub fn r_prime_dim(&self) -> usize {
        match self {
            SquareZeroSpec::TruncatedPoly { base_degree, .. } => base_degree + 2,
            SquareZeroSpec::ExplicitTable { r_prime_basis, .. } => r_prime_basis.len(),
        }
    }
}

/// 係数環の既知パラメータ（例: H3 の `t ∈ R'` で `f'_3 = x_0 - x_2 - t` のように
/// Law 中に `R'` の定数パラメータを含む場合）の指定。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingParamSpec {
    pub name: String,
    /// `R'` 基底における座標（長さ `r_prime_dim`）。
    pub value_in_r_prime: Vec<PolyExpr>,
}

/// 相対 reading `u: P -> P'` と指定観測 lift `y'`（G-141 E5・H4・H10）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelativeReadingSpec {
    pub obs_vars: Vec<String>,
    pub obs_laws: Vec<NamedPoly>,
    /// 各観測変数に対する `P'` 座標上の原始代入式 `ρ(z')`。
    pub reading_map: Vec<(String, PolyExpr)>,
    /// 指定観測 lift `y' ∈ (R')^{|obs_vars|}`。
    pub designated_obs_lift: Vec<(String, Vec<PolyExpr>)>,
    /// 任意: raw read 差（例: H10 の `-μδ = -ε²`）と障害類 `o_u` の符号付き比較式。
    pub raw_read_diff: Option<RawReadComparisonSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawReadComparisonSpec {
    pub label: String,
    pub expr: PolyExpr,
    /// 期待する符号比較（`true` = 負号比較 `raw_read_diff == -o_u`、`false` = 同符号比較）。
    pub negated: bool,
}

/// 宣言文脈被覆の 1 文脈（G-141 E7–E8）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationContextSpec {
    pub name: String,
    pub vars: Vec<String>,
    pub laws: Vec<String>,
    /// この文脈に属する観測式（E7 の参照閉包検査対象）。
    pub observations: Vec<NamedPoly>,
}

/// 二文脈共有演算 Čech 比較仕様（G-141 F5・H4・H10）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwoContextCechSpec {
    pub left_context: String,
    pub right_context: String,
    pub shared_vars: Vec<String>,
}

/// 宣言文脈被覆と `T_raw` / E7 / 二文脈 Čech 比較の束。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationCoverSpec {
    pub contexts: Vec<DeclarationContextSpec>,
    pub two_context_cech: Option<TwoContextCechSpec>,
}

/// アフィン許容部分加群 `H` による修復仕様（G-141 E6・H1）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineAllowedSpec {
    /// 変更を許す変数名集合（含まれない変数は固定 `Δ = 0`）。
    pub allowed_vars: Vec<String>,
    /// `true` のとき有限変位アフィン修復 `L(p + a) = b`（E6/H1）、`false` のとき平方零変位修復。
    pub finite_displacement: bool,
}

/// 冗長 Law 系と単一／参照 Law 系の `H^0/H^1`/障害比較仕様（G-141 E2・H2）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RedundantLawComparisonSpec {
    pub reference_laws: Vec<NamedPoly>,
}

/// 有限 étale 被覆 `z^d = t` 上の局所選択 cocycle descent 検査仕様（G-141 C9・W5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteEtaleDescentSpec {
    pub base_var: String,
    pub cover_var: String,
    pub degree: u32,
    pub base_invertible: bool,
}

/// 全 syzygy 平方零 lift タスクの未検証入力仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiftTaskSpec {
    pub name: String,
    pub coeff_domain: CoeffDomain,
    pub variables: Vec<String>,
    /// Law 中に現れる係数環 `R'` 側の既知パラメータ（例: H3 の `t`）。
    pub ring_params: Vec<RingParamSpec>,
    pub laws: Vec<NamedPoly>,
    pub extension: SquareZeroSpec,
    /// 基点実現 `x ∈ R^n`（各変数は `R` 基底上の座標列）。
    pub base_point: Vec<(String, Vec<PolyExpr>)>,
    /// 任意の ambient lift `z~ ∈ (R')^n`（省略時は `R -> R'` 零切断 lift を自動構成）。
    pub ambient_lift: Option<Vec<(String, Vec<PolyExpr>)>>,
    pub relative_reading: Option<RelativeReadingSpec>,
    pub declaration_cover: Option<DeclarationCoverSpec>,
    pub affine_allowed: Option<AffineAllowedSpec>,
    pub redundant_comparison: Option<RedundantLawComparisonSpec>,
    pub etale_descent: Option<FiniteEtaleDescentSpec>,
    pub max_syzygy_pairs: Option<usize>,
    pub provenance: Provenance,
}

/// 型・参照・次元・整合を検証済みの全 syzygy 平方零 lift タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedLiftTask {
    spec: LiftTaskSpec,
}

impl CheckedLiftTask {
    pub fn spec(&self) -> &LiftTaskSpec {
        &self.spec
    }
}

/// `LiftTaskSpec` を検証して `CheckedLiftTask` を構築する。
pub fn validate_lift_task(spec: LiftTaskSpec) -> Result<CheckedLiftTask, ValidationError> {
    if spec.name.trim().is_empty() {
        return Err(ValidationError::EmptyName { context: "lift_task".to_owned() });
    }
    validate_coeff_domain(&spec.coeff_domain, "phase4_ir")?;
    if spec.provenance.origins.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: format!("missing provenance in lift_task `{}`", spec.name),
        });
    }

    let mut var_set = BTreeSet::new();
    for v in &spec.variables {
        if v.trim().is_empty() {
            return Err(ValidationError::EmptyName { context: "variable".to_owned() });
        }
        if !var_set.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "variable",
                name: v.clone(),
            });
        }
    }

    let r_dim = spec.extension.r_base_dim();
    let rp_dim = spec.extension.r_prime_dim();
    if r_dim == 0 || rp_dim == 0 {
        return Err(ValidationError::ConversionError {
            detail: "square-zero extension algebras must have positive dimension".to_owned(),
        });
    }
    if let SquareZeroSpec::TruncatedPoly { var_name, .. } = &spec.extension
        && var_name.trim().is_empty()
    {
        return Err(ValidationError::EmptyName { context: "extension_var".to_owned() });
    }

    let mut param_set = BTreeSet::new();
    for rp in &spec.ring_params {
        if rp.name.trim().is_empty() {
            return Err(ValidationError::EmptyName { context: "ring_param".to_owned() });
        }
        if var_set.contains(rp.name.as_str()) || !param_set.insert(rp.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "ring_param",
                name: rp.name.clone(),
            });
        }
        if rp.value_in_r_prime.len() != rp_dim {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "ring_param `{}` has {} coordinates in R', expected {rp_dim}",
                    rp.name,
                    rp.value_in_r_prime.len()
                ),
            });
        }
    }

    let mut law_names = BTreeSet::new();
    for law in &spec.laws {
        if law.name.trim().is_empty() {
            return Err(ValidationError::EmptyName { context: "law".to_owned() });
        }
        if !law_names.insert(law.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "law",
                name: law.name.clone(),
            });
        }
    }

    // base_point 整合検査
    let mut bp_seen = BTreeSet::new();
    for (v, coords) in &spec.base_point {
        if !var_set.contains(v.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "variable",
                name: v.clone(),
                context: format!("lift_task `{}` base_point", spec.name),
            });
        }
        if !bp_seen.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "base_point_var",
                name: v.clone(),
            });
        }
        if coords.len() != r_dim {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "base_point for `{v}` has {} coordinates in R, expected {r_dim}",
                    coords.len()
                ),
            });
        }
    }
    if bp_seen.len() != var_set.len() {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "lift_task `{}` base_point must assign every declared variable",
                spec.name
            ),
        });
    }

    // ambient_lift 整合検査
    if let Some(lift) = &spec.ambient_lift {
        let mut lift_seen = BTreeSet::new();
        for (v, coords) in lift {
            if !var_set.contains(v.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "variable",
                    name: v.clone(),
                    context: format!("lift_task `{}` ambient_lift", spec.name),
                });
            }
            if !lift_seen.insert(v.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "ambient_lift_var",
                    name: v.clone(),
                });
            }
            if coords.len() != rp_dim {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "ambient_lift for `{v}` has {} coordinates in R', expected {rp_dim}",
                        coords.len()
                    ),
                });
            }
        }
        if lift_seen.len() != var_set.len() {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "lift_task `{}` ambient_lift must assign every declared variable",
                    spec.name
                ),
            });
        }
    }

    // 相対 reading 整合検査
    if let Some(rel) = &spec.relative_reading {
        let mut obs_set = BTreeSet::new();
        for v in &rel.obs_vars {
            if v.trim().is_empty() {
                return Err(ValidationError::EmptyName { context: "obs_var".to_owned() });
            }
            if !obs_set.insert(v.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "obs_var",
                    name: v.clone(),
                });
            }
        }
        let mut rm_seen = BTreeSet::new();
        for (ov, _) in &rel.reading_map {
            if !obs_set.contains(ov.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "obs_var",
                    name: ov.clone(),
                    context: format!("lift_task `{}` reading_map", spec.name),
                });
            }
            if !rm_seen.insert(ov.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "reading_map_var",
                    name: ov.clone(),
                });
            }
        }
        if rm_seen.len() != obs_set.len() {
            return Err(ValidationError::ConversionError {
                detail: "reading_map must assign every observation variable".to_owned(),
            });
        }
        let mut dl_seen = BTreeSet::new();
        for (ov, coords) in &rel.designated_obs_lift {
            if !obs_set.contains(ov.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "obs_var",
                    name: ov.clone(),
                    context: format!("lift_task `{}` designated_obs_lift", spec.name),
                });
            }
            if !dl_seen.insert(ov.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "designated_obs_lift_var",
                    name: ov.clone(),
                });
            }
            if coords.len() != rp_dim {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "designated_obs_lift for `{ov}` has {} coordinates in R', expected {rp_dim}",
                        coords.len()
                    ),
                });
            }
        }
        if dl_seen.len() != obs_set.len() {
            return Err(ValidationError::ConversionError {
                detail: "designated_obs_lift must assign every observation variable".to_owned(),
            });
        }
    }

    // 宣言文脈被覆の整合検査
    if let Some(cover) = &spec.declaration_cover {
        let mut ctx_map: BTreeMap<&str, &DeclarationContextSpec> = BTreeMap::new();
        for ctx in &cover.contexts {
            if ctx.name.trim().is_empty() {
                return Err(ValidationError::EmptyName { context: "declaration_context".to_owned() });
            }
            if ctx_map.insert(ctx.name.as_str(), ctx).is_some() {
                return Err(ValidationError::DuplicateDecl {
                    kind: "declaration_context",
                    name: ctx.name.clone(),
                });
            }
            for v in &ctx.vars {
                if !var_set.contains(v.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "variable",
                        name: v.clone(),
                        context: format!("declaration_context `{}`", ctx.name),
                    });
                }
            }
            for l in &ctx.laws {
                if !law_names.contains(l.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "law",
                        name: l.clone(),
                        context: format!("declaration_context `{}`", ctx.name),
                    });
                }
            }
        }
        if let Some(cech) = &cover.two_context_cech {
            if !ctx_map.contains_key(cech.left_context.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "declaration_context",
                    name: cech.left_context.clone(),
                    context: "two_context_cech.left_context".to_owned(),
                });
            }
            if !ctx_map.contains_key(cech.right_context.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "declaration_context",
                    name: cech.right_context.clone(),
                    context: "two_context_cech.right_context".to_owned(),
                });
            }
            for sv in &cech.shared_vars {
                if !var_set.contains(sv.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "variable",
                        name: sv.clone(),
                        context: "two_context_cech.shared_vars".to_owned(),
                    });
                }
            }
        }
    }

    // affine_allowed 検査
    if let Some(aff) = &spec.affine_allowed {
        for v in &aff.allowed_vars {
            if !var_set.contains(v.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "variable",
                    name: v.clone(),
                    context: "affine_allowed.allowed_vars".to_owned(),
                });
            }
        }
    }

    // finite étale descent 検査
    if let Some(etale) = &spec.etale_descent {
        if etale.base_var.trim().is_empty() || etale.cover_var.trim().is_empty() {
            return Err(ValidationError::EmptyName { context: "etale_var".to_owned() });
        }
        if etale.degree < 2 {
            return Err(ValidationError::ConversionError {
                detail: "finite etale cover degree must be >= 2".to_owned(),
            });
        }
    }

    Ok(CheckedLiftTask { spec })
}
