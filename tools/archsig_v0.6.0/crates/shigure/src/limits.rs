//! SHIGURE 計算核の全リソース上限を集約する `ShigureLimits` と暴走検査。

use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::scalar::{Rat, RingCoeff};
use archsig_common::canonical::{Json, JsonObject};
use num_bigint::BigInt;
use std::cell::RefCell;

pub const DEFAULT_MAX_BUCHBERGER_PAIRS: usize = 4_096;
pub const DEFAULT_MAX_SYZYGY_PAIRS: usize = 4_096;
pub const DEFAULT_MAX_FP_POINTS: usize = 65_536;
pub const DEFAULT_MAX_ARTIN_DIM: usize = 256;
pub const DEFAULT_MAX_CONSTRUCTIBLE_STRATA: usize = 128;
pub const DEFAULT_MAX_IMAGE_BRANCHES: usize = 64;
pub const DEFAULT_MAX_IMAGE_Y_PAIRS: usize = 256;
pub const DEFAULT_MAX_QUOTIENT_BRANCHES: usize = 64;
pub const DEFAULT_MAX_QUOTIENT_Y_PAIRS: usize = 256;
pub const DEFAULT_MAX_CONGRUENCE_STEPS: usize = 10_000;
pub const DEFAULT_MAX_HITTING_SET_STEPS: usize = 50_000;
pub const DEFAULT_MAX_HITTING_SET_RESULTS: usize = 4_096;
pub const DEFAULT_MAX_SET_PARTITIONS: usize = 4_096;
pub const DEFAULT_MAX_COMPLETIONS: usize = 4_096;
pub const DEFAULT_MAX_REVISION_COMPLETIONS: usize = 4_096;
pub const DEFAULT_MAX_OBS_REALIZATIONS: usize = 256;
pub const DEFAULT_MAX_OBS_CANDIDATES: usize = 256;
pub const DEFAULT_MAX_OBS_INDICES: usize = 16;
pub const DEFAULT_MAX_SUBSET_STEPS: usize = 65_536;
pub const DEFAULT_SUPPORT_MAX_COMPLETIONS: usize = 4_096;
pub const MAX_COMBINED_STRATA: usize = 128;
pub const MAX_WORD_LIFT_SKELETONS: usize = 256;
pub const MAX_LIFT_BASIS_TERMS: usize = 28;
pub const DEFAULT_MAX_DIM_REALIZATION_VERTICES: usize = 16;
pub const DEFAULT_MAX_DIAGNOSTIC_PARTITIONS: usize = 128;
pub const DEFAULT_MAX_ENUM_POINTS: usize = 256;
pub const MAX_RATIONAL_ROOT_COEFF: u64 = 1_000_000_000;
pub const MAX_RATIONAL_ROOT_DIVISORS: usize = 4_096;
pub const MAX_PATH_CANDIDATES: usize = 512;
pub const MAX_AFFINE_MUS_RECORDS: usize = 16;
pub const MAX_MUS_RECORDS: usize = 14;
pub const DEFAULT_MAX_BIGINT_BITS: u64 = 16_384;
pub const DEFAULT_MAX_POLY_TERMS: usize = 16_384;

/// `crates/shigure/src/` 全体の計算資源上限を一元管理する構造体。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureLimits {
    pub max_buchberger_pairs: usize,
    pub max_syzygy_pairs: usize,
    pub max_fp_points: usize,
    pub max_artin_dim: usize,
    pub max_constructible_strata: usize,
    pub max_image_branches: usize,
    pub max_image_y_pairs: usize,
    pub max_quotient_branches: usize,
    pub max_quotient_y_pairs: usize,
    pub max_congruence_steps: usize,
    pub max_hitting_set_steps: usize,
    pub max_hitting_set_results: usize,
    pub max_set_partitions: usize,
    pub max_completions: usize,
    pub max_revision_completions: usize,
    pub max_obs_realizations: usize,
    pub max_obs_candidates: usize,
    pub max_obs_indices: usize,
    pub max_subset_steps: usize,
    pub max_support_completions: usize,
    pub max_combined_strata: usize,
    pub max_word_lift_skeletons: usize,
    pub max_lift_basis_terms: usize,
    pub max_dim_realization_vertices: usize,
    pub max_diagnostic_partitions: usize,
    pub max_enum_points: usize,
    pub max_rational_root_coeff: u64,
    pub max_rational_root_divisors: usize,
    pub max_path_candidates: usize,
    pub max_affine_mus_records: usize,
    pub max_mus_records: usize,
    pub max_bigint_bits: u64,
    pub max_poly_terms: usize,
}

impl Default for ShigureLimits {
    fn default() -> Self {
        Self {
            max_buchberger_pairs: DEFAULT_MAX_BUCHBERGER_PAIRS,
            max_syzygy_pairs: DEFAULT_MAX_SYZYGY_PAIRS,
            max_fp_points: DEFAULT_MAX_FP_POINTS,
            max_artin_dim: DEFAULT_MAX_ARTIN_DIM,
            max_constructible_strata: DEFAULT_MAX_CONSTRUCTIBLE_STRATA,
            max_image_branches: DEFAULT_MAX_IMAGE_BRANCHES,
            max_image_y_pairs: DEFAULT_MAX_IMAGE_Y_PAIRS,
            max_quotient_branches: DEFAULT_MAX_QUOTIENT_BRANCHES,
            max_quotient_y_pairs: DEFAULT_MAX_QUOTIENT_Y_PAIRS,
            max_congruence_steps: DEFAULT_MAX_CONGRUENCE_STEPS,
            max_hitting_set_steps: DEFAULT_MAX_HITTING_SET_STEPS,
            max_hitting_set_results: DEFAULT_MAX_HITTING_SET_RESULTS,
            max_set_partitions: DEFAULT_MAX_SET_PARTITIONS,
            max_completions: DEFAULT_MAX_COMPLETIONS,
            max_revision_completions: DEFAULT_MAX_REVISION_COMPLETIONS,
            max_obs_realizations: DEFAULT_MAX_OBS_REALIZATIONS,
            max_obs_candidates: DEFAULT_MAX_OBS_CANDIDATES,
            max_obs_indices: DEFAULT_MAX_OBS_INDICES,
            max_subset_steps: DEFAULT_MAX_SUBSET_STEPS,
            max_support_completions: DEFAULT_SUPPORT_MAX_COMPLETIONS,
            max_combined_strata: MAX_COMBINED_STRATA,
            max_word_lift_skeletons: MAX_WORD_LIFT_SKELETONS,
            max_lift_basis_terms: MAX_LIFT_BASIS_TERMS,
            max_dim_realization_vertices: DEFAULT_MAX_DIM_REALIZATION_VERTICES,
            max_diagnostic_partitions: DEFAULT_MAX_DIAGNOSTIC_PARTITIONS,
            max_enum_points: DEFAULT_MAX_ENUM_POINTS,
            max_rational_root_coeff: MAX_RATIONAL_ROOT_COEFF,
            max_rational_root_divisors: MAX_RATIONAL_ROOT_DIVISORS,
            max_path_candidates: MAX_PATH_CANDIDATES,
            max_affine_mus_records: MAX_AFFINE_MUS_RECORDS,
            max_mus_records: MAX_MUS_RECORDS,
            max_bigint_bits: DEFAULT_MAX_BIGINT_BITS,
            max_poly_terms: DEFAULT_MAX_POLY_TERMS,
        }
    }
}

const FIELD_NAMES: &[&str] = &[
    "max_buchberger_pairs",
    "max_syzygy_pairs",
    "max_fp_points",
    "max_artin_dim",
    "max_constructible_strata",
    "max_image_branches",
    "max_image_y_pairs",
    "max_quotient_branches",
    "max_quotient_y_pairs",
    "max_congruence_steps",
    "max_hitting_set_steps",
    "max_hitting_set_results",
    "max_set_partitions",
    "max_completions",
    "max_revision_completions",
    "max_obs_realizations",
    "max_obs_candidates",
    "max_obs_indices",
    "max_subset_steps",
    "max_support_completions",
    "max_combined_strata",
    "max_word_lift_skeletons",
    "max_lift_basis_terms",
    "max_dim_realization_vertices",
    "max_diagnostic_partitions",
    "max_enum_points",
    "max_rational_root_coeff",
    "max_rational_root_divisors",
    "max_path_candidates",
    "max_affine_mus_records",
    "max_mus_records",
    "max_bigint_bits",
    "max_poly_terms",
];

impl ShigureLimits {
    /// 設定可能な全上限フィールド名の一覧（定義順）。
    pub fn field_names() -> &'static [&'static str] {
        FIELD_NAMES
    }

    /// フィールド名から現在の上限値を参照する。
    pub fn get(&self, name: &str) -> Option<u64> {
        Some(match name {
            "max_buchberger_pairs" => self.max_buchberger_pairs as u64,
            "max_syzygy_pairs" => self.max_syzygy_pairs as u64,
            "max_fp_points" => self.max_fp_points as u64,
            "max_artin_dim" => self.max_artin_dim as u64,
            "max_constructible_strata" => self.max_constructible_strata as u64,
            "max_image_branches" => self.max_image_branches as u64,
            "max_image_y_pairs" => self.max_image_y_pairs as u64,
            "max_quotient_branches" => self.max_quotient_branches as u64,
            "max_quotient_y_pairs" => self.max_quotient_y_pairs as u64,
            "max_congruence_steps" => self.max_congruence_steps as u64,
            "max_hitting_set_steps" => self.max_hitting_set_steps as u64,
            "max_hitting_set_results" => self.max_hitting_set_results as u64,
            "max_set_partitions" => self.max_set_partitions as u64,
            "max_completions" => self.max_completions as u64,
            "max_revision_completions" => self.max_revision_completions as u64,
            "max_obs_realizations" => self.max_obs_realizations as u64,
            "max_obs_candidates" => self.max_obs_candidates as u64,
            "max_obs_indices" => self.max_obs_indices as u64,
            "max_subset_steps" => self.max_subset_steps as u64,
            "max_support_completions" => self.max_support_completions as u64,
            "max_combined_strata" => self.max_combined_strata as u64,
            "max_word_lift_skeletons" => self.max_word_lift_skeletons as u64,
            "max_lift_basis_terms" => self.max_lift_basis_terms as u64,
            "max_dim_realization_vertices" => self.max_dim_realization_vertices as u64,
            "max_diagnostic_partitions" => self.max_diagnostic_partitions as u64,
            "max_enum_points" => self.max_enum_points as u64,
            "max_rational_root_coeff" => self.max_rational_root_coeff,
            "max_rational_root_divisors" => self.max_rational_root_divisors as u64,
            "max_path_candidates" => self.max_path_candidates as u64,
            "max_affine_mus_records" => self.max_affine_mus_records as u64,
            "max_mus_records" => self.max_mus_records as u64,
            "max_bigint_bits" => self.max_bigint_bits,
            "max_poly_terms" => self.max_poly_terms as u64,
            _ => return None,
        })
    }

    /// フィールド名と正整数値で上限を明示調整する。
    pub fn set(&mut self, name: &str, value: u64) -> Result<(), String> {
        if value == 0 {
            return Err(format!("limit `{name}` must be positive"));
        }
        let to_usize = |v: u64| -> Result<usize, String> {
            usize::try_from(v).map_err(|_| format!("limit `{name}` value {v} exceeds usize"))
        };
        match name {
            "max_buchberger_pairs" => self.max_buchberger_pairs = to_usize(value)?,
            "max_syzygy_pairs" => self.max_syzygy_pairs = to_usize(value)?,
            "max_fp_points" => self.max_fp_points = to_usize(value)?,
            "max_artin_dim" => self.max_artin_dim = to_usize(value)?,
            "max_constructible_strata" => self.max_constructible_strata = to_usize(value)?,
            "max_image_branches" => self.max_image_branches = to_usize(value)?,
            "max_image_y_pairs" => self.max_image_y_pairs = to_usize(value)?,
            "max_quotient_branches" => self.max_quotient_branches = to_usize(value)?,
            "max_quotient_y_pairs" => self.max_quotient_y_pairs = to_usize(value)?,
            "max_congruence_steps" => self.max_congruence_steps = to_usize(value)?,
            "max_hitting_set_steps" => self.max_hitting_set_steps = to_usize(value)?,
            "max_hitting_set_results" => self.max_hitting_set_results = to_usize(value)?,
            "max_set_partitions" => self.max_set_partitions = to_usize(value)?,
            "max_completions" => self.max_completions = to_usize(value)?,
            "max_revision_completions" => self.max_revision_completions = to_usize(value)?,
            "max_obs_realizations" => self.max_obs_realizations = to_usize(value)?,
            "max_obs_candidates" => self.max_obs_candidates = to_usize(value)?,
            "max_obs_indices" => self.max_obs_indices = to_usize(value)?,
            "max_subset_steps" => self.max_subset_steps = to_usize(value)?,
            "max_support_completions" => self.max_support_completions = to_usize(value)?,
            "max_combined_strata" => self.max_combined_strata = to_usize(value)?,
            "max_word_lift_skeletons" => self.max_word_lift_skeletons = to_usize(value)?,
            "max_lift_basis_terms" => self.max_lift_basis_terms = to_usize(value)?,
            "max_dim_realization_vertices" => self.max_dim_realization_vertices = to_usize(value)?,
            "max_diagnostic_partitions" => self.max_diagnostic_partitions = to_usize(value)?,
            "max_enum_points" => self.max_enum_points = to_usize(value)?,
            "max_rational_root_coeff" => self.max_rational_root_coeff = value,
            "max_rational_root_divisors" => self.max_rational_root_divisors = to_usize(value)?,
            "max_path_candidates" => self.max_path_candidates = to_usize(value)?,
            "max_affine_mus_records" => self.max_affine_mus_records = to_usize(value)?,
            "max_mus_records" => self.max_mus_records = to_usize(value)?,
            "max_bigint_bits" => self.max_bigint_bits = value,
            "max_poly_terms" => self.max_poly_terms = to_usize(value)?,
            _ => {
                return Err(format!(
                    "unknown shigure limit `{name}`; expected one of: {}",
                    FIELD_NAMES.join(", ")
                ));
            }
        }
        Ok(())
    }

    /// 適用中の上限一式を診断・監査用 JSON として出力する。
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::new();
        for &name in FIELD_NAMES {
            if let Some(v) = self.get(name) {
                obj.insert(name.to_owned(), Json::Nat(v));
            }
        }
        Json::Obj(obj)
    }

    /// `BigInt` のビット長上限を検査する。
    pub fn check_bigint_bits(&self, value: &BigInt, context: &str) -> Result<(), AlgebraError> {
        let bits = value.bits();
        if bits > self.max_bigint_bits {
            return Err(AlgebraError::ResourceLimitExceeded {
                limit_name: "max_bigint_bits".to_owned(),
                limit: self.max_bigint_bits,
                observed: bits,
                detail: format!(
                    "{context}: BigInt bit length {bits} exceeds limit ({})",
                    self.max_bigint_bits
                ),
            });
        }
        Ok(())
    }

    /// `Rat` の分子・分母ビット長上限を検査する。
    pub fn check_rat_bits(&self, value: &Rat, context: &str) -> Result<(), AlgebraError> {
        self.check_bigint_bits(value.num(), context)?;
        self.check_bigint_bits(value.den(), context)
    }

    /// 係数のビット長上限を検査する。
    pub fn check_coeff<C: RingCoeff>(&self, coeff: &C, context: &str) -> Result<(), AlgebraError> {
        let bits = coeff.coeff_max_bits();
        if bits > self.max_bigint_bits {
            return Err(AlgebraError::ResourceLimitExceeded {
                limit_name: "max_bigint_bits".to_owned(),
                limit: self.max_bigint_bits,
                observed: bits,
                detail: format!(
                    "{context}: scalar bit length {bits} exceeds limit ({})",
                    self.max_bigint_bits
                ),
            });
        }
        Ok(())
    }

    /// 多項式の項数上限を検査する。
    pub fn check_poly_terms(&self, terms: usize, context: &str) -> Result<(), AlgebraError> {
        if terms > self.max_poly_terms {
            return Err(AlgebraError::ResourceLimitExceeded {
                limit_name: "max_poly_terms".to_owned(),
                limit: self.max_poly_terms as u64,
                observed: terms as u64,
                detail: format!(
                    "{context}: polynomial term count {terms} exceeds limit ({})",
                    self.max_poly_terms
                ),
            });
        }
        Ok(())
    }

    /// 多項式の項数上限および全係数のビット長上限を検査する。
    pub fn check_poly<C: RingCoeff>(
        &self,
        poly: &Poly<C>,
        context: &str,
    ) -> Result<(), AlgebraError> {
        self.check_poly_terms(poly.terms().len(), context)?;
        for coeff in poly.terms().values() {
            self.check_coeff(coeff, context)?;
        }
        Ok(())
    }
}

thread_local! {
    static ACTIVE_LIMITS: RefCell<Vec<ShigureLimits>> = const { RefCell::new(Vec::new()) };
}

struct LimitsGuard;

impl Drop for LimitsGuard {
    fn drop(&mut self) {
        ACTIVE_LIMITS.with(|stack| {
            stack.borrow_mut().pop();
        });
    }
}

/// 指定した `ShigureLimits` を現在のスレッド実行スコープへ適用する。
pub fn with_active_limits<T>(limits: &ShigureLimits, f: impl FnOnce() -> T) -> T {
    ACTIVE_LIMITS.with(|stack| {
        stack.borrow_mut().push(limits.clone());
    });
    let _guard = LimitsGuard;
    f()
}

/// 現在のスレッド実行スコープで有効な `ShigureLimits` を取得する（未設定時は既定値）。
pub fn active_limits() -> ShigureLimits {
    ACTIVE_LIMITS.with(|stack| stack.borrow().last().cloned().unwrap_or_default())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shigure_limits_default_and_roundtrip_all_33_fields() {
        let mut limits = ShigureLimits::default();
        assert_eq!(ShigureLimits::field_names().len(), 33);
        let json = limits.to_json();
        let Json::Obj(ref map) = json else {
            panic!("limits json must be object");
        };
        assert_eq!(map.len(), 33);
        for &name in ShigureLimits::field_names() {
            let v = limits.get(name).unwrap();
            assert!(v > 0);
            limits.set(name, v + 1).unwrap();
            assert_eq!(limits.get(name), Some(v + 1));
        }
        assert!(limits.set("unknown_limit", 10).is_err());
        assert!(limits.set("max_bigint_bits", 0).is_err());
    }

    #[test]
    fn active_limits_scope_restores_on_exit_and_panic() {
        assert_eq!(active_limits(), ShigureLimits::default());
        let custom = ShigureLimits {
            max_bigint_bits: 128,
            ..ShigureLimits::default()
        };
        with_active_limits(&custom, || {
            assert_eq!(active_limits().max_bigint_bits, 128);
        });
        assert_eq!(active_limits(), ShigureLimits::default());
        let res = std::panic::catch_unwind(|| {
            with_active_limits(&custom, || panic!("unwind check"));
        });
        assert!(res.is_err());
        assert_eq!(active_limits(), ShigureLimits::default());
    }
}
