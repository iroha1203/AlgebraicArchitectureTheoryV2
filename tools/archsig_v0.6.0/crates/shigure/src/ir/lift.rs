//! 全 syzygy 平方零 lift・相対障害・宣言被覆比較・有限 étale 被覆 cocycle descent の検証済み IR
//! （G-141 E1–E8・C8–C9・H1–H4・H10 / W5）。

use crate::ir::artin::{check_expr_refs, check_named_poly, validate_lit_for_domain};
use crate::ir::change::NamedPoly;
use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::{ValidationError, validate_coeff_domain, validate_provenance};
use std::collections::{BTreeMap, BTreeSet};

/// 平方零拡大 `R' ↠ R` の入力仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SquareZeroSpec {
    /// 1 変数打ち切り冪零商の 1 段拡大 `k[var]/(var^{base_degree + 2}) ↠ k[var]/(var^{base_degree + 1})`。
    TruncatedPoly {
        var_name: String,
        base_degree: usize,
    },
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
    pub fn r_base_dim(&self) -> Option<usize> {
        match self {
            SquareZeroSpec::TruncatedPoly { base_degree, .. } => base_degree.checked_add(1),
            SquareZeroSpec::ExplicitTable { r_base_basis, .. } => Some(r_base_basis.len()),
        }
    }

    pub fn r_prime_dim(&self) -> Option<usize> {
        match self {
            SquareZeroSpec::TruncatedPoly { base_degree, .. } => base_degree.checked_add(2),
            SquareZeroSpec::ExplicitTable { r_prime_basis, .. } => Some(r_prime_basis.len()),
        }
    }
}

/// 係数環の既知パラメータ（例: H3 の `t ∈ R'` で `f'_3 = x_0 - x_2 - t` のように
/// Law 中に `R'` の定数パラメータを含む場合）の指定。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingParamSpec {
    pub name: String,
    /// `R'` 基底における座標（長さ `r_prime_dim`、定数または未観測）。
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
        return Err(ValidationError::EmptyName {
            context: "lift_task".to_owned(),
        });
    }
    let ctx = format!("lift_task `{}`", spec.name);
    validate_coeff_domain(&spec.coeff_domain, &ctx)?;
    if spec.provenance.origins.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: format!("missing provenance in {ctx}"),
        });
    }
    validate_provenance(&spec.provenance, &ctx)?;

    let mut var_set = BTreeSet::new();
    for v in &spec.variables {
        if v.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "variable".to_owned(),
            });
        }
        if !var_set.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "variable",
                name: v.clone(),
            });
        }
    }

    validate_square_zero_spec(&spec.extension, &spec.coeff_domain, &ctx)?;
    let r_dim = spec
        .extension
        .r_base_dim()
        .ok_or_else(|| ValidationError::ConversionError {
            detail: format!("{ctx} extension base dimension overflow"),
        })?;
    let rp_dim = spec
        .extension
        .r_prime_dim()
        .ok_or_else(|| ValidationError::ConversionError {
            detail: format!("{ctx} extension prime dimension overflow"),
        })?;
    let empty_vars = BTreeSet::new();

    let dom = &spec.coeff_domain;
    let mut param_set = BTreeSet::new();
    for rp in &spec.ring_params {
        if rp.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "ring_param".to_owned(),
            });
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
        for expr in &rp.value_in_r_prime {
            check_expr_refs(
                expr,
                dom,
                &empty_vars,
                &empty_vars,
                &empty_vars,
                &format!("ring_param `{}`", rp.name),
            )?;
        }
    }

    let mut law_names = BTreeSet::new();
    for law in &spec.laws {
        if law.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "law".to_owned(),
            });
        }
        if !law_names.insert(law.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "law",
                name: law.name.clone(),
            });
        }
        check_named_poly(
            law,
            dom,
            &var_set,
            &empty_vars,
            &param_set,
            &format!("law `{}`", law.name),
        )?;
    }

    // base_point 整合検査
    let mut bp_seen = BTreeSet::new();
    for (v, coords) in &spec.base_point {
        if !var_set.contains(v.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "variable",
                name: v.clone(),
                context: format!("{ctx} base_point"),
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
        for expr in coords {
            check_expr_refs(
                expr,
                dom,
                &empty_vars,
                &empty_vars,
                &empty_vars,
                &format!("base_point `{v}`"),
            )?;
        }
    }
    if bp_seen.len() != var_set.len() {
        return Err(ValidationError::ConversionError {
            detail: format!("{ctx} base_point must assign every declared variable"),
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
                    context: format!("{ctx} ambient_lift"),
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
            for expr in coords {
                check_expr_refs(
                    expr,
                    dom,
                    &empty_vars,
                    &empty_vars,
                    &empty_vars,
                    &format!("ambient_lift `{v}`"),
                )?;
            }
        }
        if lift_seen.len() != var_set.len() {
            return Err(ValidationError::ConversionError {
                detail: format!("{ctx} ambient_lift must assign every declared variable"),
            });
        }
    }

    // 相対 reading 整合検査
    if let Some(rel) = &spec.relative_reading {
        let mut obs_set = BTreeSet::new();
        for v in &rel.obs_vars {
            if v.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "obs_var".to_owned(),
                });
            }
            if param_set.contains(v.as_str()) || !obs_set.insert(v.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "obs_var",
                    name: v.clone(),
                });
            }
        }
        let mut obs_law_seen = BTreeSet::new();
        for ol in &rel.obs_laws {
            if ol.name.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "obs_law".to_owned(),
                });
            }
            if !obs_law_seen.insert(ol.name.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "obs_law",
                    name: ol.name.clone(),
                });
            }
            check_named_poly(
                ol,
                dom,
                &obs_set,
                &empty_vars,
                &param_set,
                &format!("obs_law `{}`", ol.name),
            )?;
        }
        let mut rm_seen = BTreeSet::new();
        for (ov, expr) in &rel.reading_map {
            if !obs_set.contains(ov.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "obs_var",
                    name: ov.clone(),
                    context: format!("{ctx} reading_map"),
                });
            }
            if !rm_seen.insert(ov.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "reading_map_var",
                    name: ov.clone(),
                });
            }
            check_expr_refs(
                expr,
                dom,
                &var_set,
                &empty_vars,
                &param_set,
                &format!("reading_map `{ov}`"),
            )?;
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
                    context: format!("{ctx} designated_obs_lift"),
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
            for expr in coords {
                check_expr_refs(
                    expr,
                    dom,
                    &empty_vars,
                    &empty_vars,
                    &empty_vars,
                    &format!("designated_obs_lift `{ov}`"),
                )?;
            }
        }
        if dl_seen.len() != obs_set.len() {
            return Err(ValidationError::ConversionError {
                detail: "designated_obs_lift must assign every observation variable".to_owned(),
            });
        }
        if let Some(rr) = &rel.raw_read_diff {
            if rr.label.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "raw_read_diff.label".to_owned(),
                });
            }
            check_expr_refs(
                &rr.expr,
                dom,
                &var_set,
                &empty_vars,
                &param_set,
                &format!("raw_read_diff `{}`", rr.label),
            )?;
        }
    }

    // 宣言文脈被覆の整合検査
    if let Some(cover) = &spec.declaration_cover {
        let mut ctx_map: BTreeMap<&str, &DeclarationContextSpec> = BTreeMap::new();
        for c in &cover.contexts {
            if c.name.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "declaration_context".to_owned(),
                });
            }
            if ctx_map.insert(c.name.as_str(), c).is_some() {
                return Err(ValidationError::DuplicateDecl {
                    kind: "declaration_context",
                    name: c.name.clone(),
                });
            }
            let mut cv_seen = BTreeSet::new();
            for v in &c.vars {
                if !var_set.contains(v.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "variable",
                        name: v.clone(),
                        context: format!("declaration_context `{}`", c.name),
                    });
                }
                if !cv_seen.insert(v.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "context_var",
                        name: v.clone(),
                    });
                }
            }
            let mut cl_seen = BTreeSet::new();
            for l in &c.laws {
                if !law_names.contains(l.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "law",
                        name: l.clone(),
                        context: format!("declaration_context `{}`", c.name),
                    });
                }
                if !cl_seen.insert(l.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "context_law",
                        name: l.clone(),
                    });
                }
            }
            let mut co_seen = BTreeSet::new();
            for obs in &c.observations {
                if obs.name.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "context_observation".to_owned(),
                    });
                }
                if !co_seen.insert(obs.name.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "context_observation",
                        name: obs.name.clone(),
                    });
                }
                // 観測式は全体変数集合に対して整合すること（個別文脈内での参照閉包性は E7 検査対象）。
                check_named_poly(
                    obs,
                    dom,
                    &var_set,
                    &empty_vars,
                    &param_set,
                    &format!("declaration_context `{}` obs `{}`", c.name, obs.name),
                )?;
            }
        }
        if let Some(cech) = &cover.two_context_cech {
            let Some(left_ctx) = ctx_map.get(cech.left_context.as_str()) else {
                return Err(ValidationError::UnknownRef {
                    kind: "declaration_context",
                    name: cech.left_context.clone(),
                    context: "two_context_cech.left_context".to_owned(),
                });
            };
            let Some(right_ctx) = ctx_map.get(cech.right_context.as_str()) else {
                return Err(ValidationError::UnknownRef {
                    kind: "declaration_context",
                    name: cech.right_context.clone(),
                    context: "two_context_cech.right_context".to_owned(),
                });
            };
            let left_vars: BTreeSet<&str> = left_ctx.vars.iter().map(String::as_str).collect();
            let right_vars: BTreeSet<&str> = right_ctx.vars.iter().map(String::as_str).collect();
            let mut sv_seen = BTreeSet::new();
            for sv in &cech.shared_vars {
                if !var_set.contains(sv.as_str())
                    || !left_vars.contains(sv.as_str())
                    || !right_vars.contains(sv.as_str())
                {
                    return Err(ValidationError::UnknownRef {
                        kind: "variable",
                        name: sv.clone(),
                        context: format!(
                            "two_context_cech.shared_vars (must belong to both `{}` and `{}`)",
                            cech.left_context, cech.right_context
                        ),
                    });
                }
                if !sv_seen.insert(sv.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "shared_var",
                        name: sv.clone(),
                    });
                }
            }
        }
    }

    // affine_allowed 検査
    if let Some(aff) = &spec.affine_allowed {
        let mut av_seen = BTreeSet::new();
        for v in &aff.allowed_vars {
            if !var_set.contains(v.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "variable",
                    name: v.clone(),
                    context: "affine_allowed.allowed_vars".to_owned(),
                });
            }
            if !av_seen.insert(v.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "allowed_var",
                    name: v.clone(),
                });
            }
        }
    }

    // redundant_comparison 検査
    if let Some(red) = &spec.redundant_comparison {
        let mut r_seen = BTreeSet::new();
        for rl in &red.reference_laws {
            if rl.name.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "reference_law".to_owned(),
                });
            }
            if !r_seen.insert(rl.name.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "reference_law",
                    name: rl.name.clone(),
                });
            }
            check_named_poly(
                rl,
                dom,
                &var_set,
                &empty_vars,
                &param_set,
                &format!("redundant_comparison `{}`", rl.name),
            )?;
        }
    }

    // finite étale descent 検査
    if let Some(etale) = &spec.etale_descent {
        if etale.base_var.trim().is_empty() || etale.cover_var.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "etale_var".to_owned(),
            });
        }
        if etale.base_var == etale.cover_var {
            return Err(ValidationError::ConversionError {
                detail: "finite etale base_var and cover_var must be distinct".to_owned(),
            });
        }
        if etale.degree < 2 {
            return Err(ValidationError::ConversionError {
                detail: "finite etale cover degree must be >= 2".to_owned(),
            });
        }
    }

    Ok(CheckedLiftTask { spec })
}

fn validate_square_zero_spec(
    ext: &SquareZeroSpec,
    domain: &CoeffDomain,
    context: &str,
) -> Result<(), ValidationError> {
    match ext {
        SquareZeroSpec::TruncatedPoly {
            var_name,
            base_degree,
        } => {
            if var_name.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "extension_var".to_owned(),
                });
            }
            let Some(rp_dim) = base_degree.checked_add(2) else {
                return Err(ValidationError::ConversionError {
                    detail: format!("{context} extension base_degree overflow"),
                });
            };
            let max_artin_dim = crate::limits::active_limits().max_artin_dim;
            if rp_dim > max_artin_dim {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "{context} extension dimension {rp_dim} exceeds limit {max_artin_dim}"
                    ),
                });
            }
            Ok(())
        }
        SquareZeroSpec::ExplicitTable {
            r_prime_basis,
            r_prime_one,
            r_prime_mul,
            r_base_basis,
            r_base_one,
            r_base_mul,
            projection,
        } => {
            let dp = r_prime_basis.len();
            let dr = r_base_basis.len();
            if dp == 0 || dr == 0 {
                return Err(ValidationError::ConversionError {
                    detail: format!("{context} explicit algebras must have positive dimension"),
                });
            }
            let max_artin_dim = crate::limits::active_limits().max_artin_dim;
            if dp > max_artin_dim || dr > max_artin_dim {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "{context} explicit algebra dimension exceeds limit {max_artin_dim}"
                    ),
                });
            }
            check_unique_basis(r_prime_basis, "r_prime_basis")?;
            check_unique_basis(r_base_basis, "r_base_basis")?;
            if r_prime_one.len() != dp || r_base_one.len() != dr {
                return Err(ValidationError::ConversionError {
                    detail: format!("{context} algebra identity vector length mismatch"),
                });
            }
            for lit in r_prime_one.iter().chain(r_base_one) {
                validate_lit_for_domain(lit, domain, context)?;
            }
            validate_mul_table_shape(r_prime_mul, dp, domain, &format!("{context} r_prime_mul"))?;
            validate_mul_table_shape(r_base_mul, dr, domain, &format!("{context} r_base_mul"))?;
            if projection.len() != dr || projection.iter().any(|r| r.len() != dp) {
                return Err(ValidationError::ConversionError {
                    detail: format!("{context} projection matrix must have shape {dr} x {dp}"),
                });
            }
            for row in projection {
                for lit in row {
                    validate_lit_for_domain(lit, domain, &format!("{context} projection"))?;
                }
            }
            Ok(())
        }
    }
}

fn check_unique_basis(basis: &[String], kind: &'static str) -> Result<(), ValidationError> {
    let mut seen = BTreeSet::new();
    for b in basis {
        if b.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: kind.to_owned(),
            });
        }
        if !seen.insert(b.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind,
                name: b.clone(),
            });
        }
    }
    Ok(())
}

fn validate_mul_table_shape(
    table: &[Vec<Vec<ScalarLit>>],
    dim: usize,
    domain: &CoeffDomain,
    context: &str,
) -> Result<(), ValidationError> {
    if table.len() != dim
        || table
            .iter()
            .any(|row| row.len() != dim || row.iter().any(|v| v.len() != dim))
    {
        return Err(ValidationError::ConversionError {
            detail: format!("{context} must be a {dim}x{dim}x{dim} table"),
        });
    }
    for row in table {
        for vec in row {
            for lit in vec {
                validate_lit_for_domain(lit, domain, context)?;
            }
        }
    }
    Ok(())
}
