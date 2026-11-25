//! Phase 4（高次変形・全 syzygy 平方零 lift・Artin 試験・診断層・Atlas 細分化）の型付き結果詳細
//! （`LiftOutcomeDetail`・`ArtinOutcomeDetail`・`DiagnosticsOutcomeDetail`・`AtlasOutcomeDetail`）。

use crate::ir::result::ReevalCheck;
use archsig_common::canonical::{Json, JsonObject};
use std::collections::BTreeMap;

/// 全 syzygy 平方零 lift・相対障害・宣言被覆・有限 étale 被覆 descent の詳細出力（AC3）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiftOutcomeDetail {
    pub coeff_ring_label: String,
    pub r_base_label: String,
    pub r_prime_label: String,
    pub kernel_dim: usize,
    pub square_zero_verified: bool,
    pub base_point_lawful: bool,
    /// 全 syzygy 生成族（各 syzygy は原始 Law 成分ごとの多項式文字列）。
    pub syzygy_generators: Vec<Vec<String>>,
    pub syzygy_identity_verified: bool,
    pub complex_d1_d0_zero_verified: bool,
    pub residual_cocycle_verified: bool,
    pub residual_in_m: Vec<String>,
    /// 全 syzygy 複体 `D` のコホモロジー次元。
    pub h0_dim: usize,
    pub h1_dim: usize,
    pub h0_basis: Vec<Vec<String>>,
    pub obstruction_class_coords: Vec<String>,
    pub obstruction_is_zero: bool,
    pub lift_exists: bool,
    /// 復元された実 lift（存在時）と元 Law への独立再評価検算。
    pub restored_lift: Option<BTreeMap<String, String>>,
    pub reevaluation: Option<ReevalCheck>,
    /// 生宣言 Čech total complex `T_raw` との比較（G-141 E8・H3）。
    pub raw_cech_comparison: Option<RawCechComparisonResult>,
    /// 相対 cone 複体 `F_u = Cone(φ)[-1]` の計算結果（G-141 E5・H4・H10）。
    pub relative_cone: Option<RelativeConeResult>,
    /// 二文脈共有演算 Čech 類と観測支持閉包検査（G-141 E7・F5・H4・H10）。
    pub declaration_cover: Option<DeclarationCoverResult>,
    /// 許容部分加群 `H` 上のアフィン修復全解（G-141 E6・H1）。
    pub affine_repair: Option<AffineRepairResult>,
    /// 冗長 Law 比較結果（G-141 E2・H2）。
    pub redundant_comparison: Option<RedundantComparisonResult>,
    /// 有限 étale 被覆 cocycle descent 検査結果（G-141 C9・W5）。
    pub etale_descent: Option<FiniteEtaleDescentResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCechComparisonResult {
    pub h0_t_raw_dim: usize,
    pub h1_t_raw_dim: usize,
    pub h1_d_dim: usize,
    pub kernel_map_exact_verified: bool,
    pub differs_from_full_syzygy: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelativeConeResult {
    pub h0_fu_dim: usize,
    pub h1_fu_dim: usize,
    pub relative_obstruction_coords: Vec<String>,
    pub relative_obstruction_is_zero: bool,
    pub relative_lift_exists: bool,
    pub restored_relative_lift: Option<BTreeMap<String, String>>,
    pub reevaluation: Option<ReevalCheck>,
    pub raw_read_diff_value: Option<String>,
    pub raw_read_diff_signed_match: Option<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationCoverResult {
    pub support_closed: bool,
    pub unclosed_observations: Vec<String>,
    pub two_context_cech_diff: Option<BTreeMap<String, String>>,
    pub matches_relative_obstruction: Option<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineRepairResult {
    pub finite_displacement: bool,
    pub allowed_vars: Vec<String>,
    pub repair_exists: bool,
    pub particular_delta: Option<BTreeMap<String, String>>,
    pub torsor_basis: Vec<BTreeMap<String, String>>,
    pub reevaluation: Option<ReevalCheck>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RedundantComparisonResult {
    pub ref_h0_dim: usize,
    pub ref_h1_dim: usize,
    pub ref_obstruction_is_zero: bool,
    pub h0_matches: bool,
    pub h1_matches: bool,
    pub obstruction_matches: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteEtaleDescentResult {
    pub cover_equation: String,
    pub degree: u32,
    pub is_finite_etale: bool,
    pub derivative_unit_verified: bool,
    pub cocycle_group: String,
    pub cocycle_verified: bool,
    pub local_selection_exists_on_cover: bool,
    pub global_regular_section_exists: bool,
    pub nonexistence_reason: String,
}

impl LiftOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("coeff_ring".into(), Json::str(&self.coeff_ring_label)),
            ("r_base".into(), Json::str(&self.r_base_label)),
            ("r_prime".into(), Json::str(&self.r_prime_label)),
            ("kernel_dim".into(), Json::Nat(self.kernel_dim as u64)),
            (
                "square_zero_verified".into(),
                Json::Bool(self.square_zero_verified),
            ),
            (
                "base_point_lawful".into(),
                Json::Bool(self.base_point_lawful),
            ),
            (
                "syzygy_generators".into(),
                Json::Arr(
                    self.syzygy_generators
                        .iter()
                        .map(|s| Json::Arr(s.iter().map(Json::str).collect()))
                        .collect(),
                ),
            ),
            (
                "syzygy_identity_verified".into(),
                Json::Bool(self.syzygy_identity_verified),
            ),
            (
                "complex_d1_d0_zero_verified".into(),
                Json::Bool(self.complex_d1_d0_zero_verified),
            ),
            (
                "residual_cocycle_verified".into(),
                Json::Bool(self.residual_cocycle_verified),
            ),
            (
                "residual_in_m".into(),
                Json::Arr(self.residual_in_m.iter().map(Json::str).collect()),
            ),
            ("h0_dim".into(), Json::Nat(self.h0_dim as u64)),
            ("h1_dim".into(), Json::Nat(self.h1_dim as u64)),
            (
                "h0_basis".into(),
                Json::Arr(
                    self.h0_basis
                        .iter()
                        .map(|v| Json::Arr(v.iter().map(Json::str).collect()))
                        .collect(),
                ),
            ),
            (
                "obstruction_class_coords".into(),
                Json::Arr(
                    self.obstruction_class_coords
                        .iter()
                        .map(Json::str)
                        .collect(),
                ),
            ),
            (
                "obstruction_is_zero".into(),
                Json::Bool(self.obstruction_is_zero),
            ),
            ("lift_exists".into(), Json::Bool(self.lift_exists)),
        ]);
        if let Some(restored) = &self.restored_lift {
            obj.insert("restored_lift".into(), str_map_json(restored));
        }
        if let Some(reeval) = &self.reevaluation {
            obj.insert("reevaluation".into(), reeval.to_json());
        }
        if let Some(raw) = &self.raw_cech_comparison {
            obj.insert(
                "raw_cech_comparison".into(),
                Json::obj([
                    ("h0_t_raw_dim", Json::Nat(raw.h0_t_raw_dim as u64)),
                    ("h1_t_raw_dim", Json::Nat(raw.h1_t_raw_dim as u64)),
                    ("h1_d_dim", Json::Nat(raw.h1_d_dim as u64)),
                    (
                        "kernel_map_exact_verified",
                        Json::Bool(raw.kernel_map_exact_verified),
                    ),
                    (
                        "differs_from_full_syzygy",
                        Json::Bool(raw.differs_from_full_syzygy),
                    ),
                ]),
            );
        }
        if let Some(rel) = &self.relative_cone {
            let mut r_obj = JsonObject::from([
                ("h0_fu_dim".into(), Json::Nat(rel.h0_fu_dim as u64)),
                ("h1_fu_dim".into(), Json::Nat(rel.h1_fu_dim as u64)),
                (
                    "relative_obstruction_coords".into(),
                    Json::Arr(
                        rel.relative_obstruction_coords
                            .iter()
                            .map(Json::str)
                            .collect(),
                    ),
                ),
                (
                    "relative_obstruction_is_zero".into(),
                    Json::Bool(rel.relative_obstruction_is_zero),
                ),
                (
                    "relative_lift_exists".into(),
                    Json::Bool(rel.relative_lift_exists),
                ),
            ]);
            if let Some(rl) = &rel.restored_relative_lift {
                r_obj.insert("restored_relative_lift".into(), str_map_json(rl));
            }
            if let Some(re) = &rel.reevaluation {
                r_obj.insert("reevaluation".into(), re.to_json());
            }
            if let Some(v) = &rel.raw_read_diff_value {
                r_obj.insert("raw_read_diff_value".into(), Json::str(v));
            }
            if let Some(m) = rel.raw_read_diff_signed_match {
                r_obj.insert("raw_read_diff_signed_match".into(), Json::Bool(m));
            }
            obj.insert("relative_cone".into(), Json::Obj(r_obj));
        }
        if let Some(cov) = &self.declaration_cover {
            let mut c_obj = JsonObject::from([
                ("support_closed".into(), Json::Bool(cov.support_closed)),
                (
                    "unclosed_observations".into(),
                    Json::Arr(cov.unclosed_observations.iter().map(Json::str).collect()),
                ),
            ]);
            if let Some(diff) = &cov.two_context_cech_diff {
                c_obj.insert("two_context_cech_diff".into(), str_map_json(diff));
            }
            if let Some(m) = cov.matches_relative_obstruction {
                c_obj.insert("matches_relative_obstruction".into(), Json::Bool(m));
            }
            obj.insert("declaration_cover".into(), Json::Obj(c_obj));
        }
        if let Some(aff) = &self.affine_repair {
            let mut a_obj = JsonObject::from([
                (
                    "finite_displacement".into(),
                    Json::Bool(aff.finite_displacement),
                ),
                (
                    "allowed_vars".into(),
                    Json::Arr(aff.allowed_vars.iter().map(Json::str).collect()),
                ),
                ("repair_exists".into(), Json::Bool(aff.repair_exists)),
                (
                    "torsor_basis".into(),
                    Json::Arr(aff.torsor_basis.iter().map(str_map_json).collect()),
                ),
            ]);
            if let Some(p) = &aff.particular_delta {
                a_obj.insert("particular_delta".into(), str_map_json(p));
            }
            if let Some(re) = &aff.reevaluation {
                a_obj.insert("reevaluation".into(), re.to_json());
            }
            obj.insert("affine_repair".into(), Json::Obj(a_obj));
        }
        if let Some(red) = &self.redundant_comparison {
            obj.insert(
                "redundant_comparison".into(),
                Json::obj([
                    ("ref_h0_dim", Json::Nat(red.ref_h0_dim as u64)),
                    ("ref_h1_dim", Json::Nat(red.ref_h1_dim as u64)),
                    (
                        "ref_obstruction_is_zero",
                        Json::Bool(red.ref_obstruction_is_zero),
                    ),
                    ("h0_matches", Json::Bool(red.h0_matches)),
                    ("h1_matches", Json::Bool(red.h1_matches)),
                    ("obstruction_matches", Json::Bool(red.obstruction_matches)),
                ]),
            );
        }
        if let Some(et) = &self.etale_descent {
            obj.insert(
                "etale_descent".into(),
                Json::obj([
                    ("cover_equation", Json::str(&et.cover_equation)),
                    ("degree", Json::Nat(u64::from(et.degree))),
                    ("is_finite_etale", Json::Bool(et.is_finite_etale)),
                    (
                        "derivative_unit_verified",
                        Json::Bool(et.derivative_unit_verified),
                    ),
                    ("cocycle_group", Json::str(&et.cocycle_group)),
                    ("cocycle_verified", Json::Bool(et.cocycle_verified)),
                    (
                        "local_selection_exists_on_cover",
                        Json::Bool(et.local_selection_exists_on_cover),
                    ),
                    (
                        "global_regular_section_exists",
                        Json::Bool(et.global_regular_section_exists),
                    ),
                    ("nonexistence_reason", Json::str(&et.nonexistence_reason)),
                ]),
            );
        }
        Json::Obj(obj)
    }
}

/// 原始消去・全 Artin 試験・検出次数 `ν`・一般係数冪零商 base change の詳細出力（AC4）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArtinOutcomeDetail {
    /// 試験対象環族の明示（体上では `"all_local_artin_algebras_universal_quotient"`、$\mathbb{Z}$ 上では `"general_coeff_nilpotent_quotient"`、F8–F9）。
    pub test_ring_family: String,
    pub is_free_observation_chart: bool,
    pub eliminated_residuals: Vec<String>,
    /// 自由観測 chart 上の構文次数上界 `D`（既存関係付き表示では `None`、F7・H5）。
    pub syntactic_degree_bound: Option<u64>,
    /// 初回検出次数 `ν`（`None` は `ν = ∞`＝局所同型）。
    pub detection_order_nu: Option<usize>,
    pub local_isomorphism_at_base: bool,
    /// F4 の区別: `"nu_ge_2_realization_unliftable"` / `"nu_eq_1_designated_direction_only_constant_lift_exists"` / `"infinite_local_iso"`。
    pub lift_failure_mode: String,
    /// 普遍初回拡大 `A/m^{ν+1} -> A/m^ν` の相対障害 `κ_u` と二文脈 Čech 差（F4–F5）。
    pub universal_first_obstruction: Option<UniversalObstructionSummary>,
    /// 2 段合成則 `ν(v ∘ u) = min(ν(u), ν(v))` の検算結果（F6）。
    pub composition_law: Option<ArtinCompositionResult>,
    /// 一般係数冪零商 base change `D_r` の比較結果（F8・H6）。
    pub base_change: Option<NilpotentBaseChangeResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniversalObstructionSummary {
    pub nu: usize,
    pub r_base_label: String,
    pub r_prime_label: String,
    pub kernel_dim: usize,
    pub kappa_u_images: Vec<String>,
    pub kappa_u_nonzero: bool,
    pub two_context_cech_matches: bool,
    pub constant_lift_exists: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArtinCompositionResult {
    pub nu_u: Option<usize>,
    pub nu_v: Option<usize>,
    pub nu_vu: Option<usize>,
    pub min_law_verified: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NilpotentBaseChangeResult {
    pub source_domain: String,
    pub target_domain: String,
    pub source_nu: Option<usize>,
    pub target_nu: Option<usize>,
    pub test_order: usize,
    pub source_dr_generators: Vec<String>,
    pub abstract_tensor_nonzero: bool,
    pub target_image_generators: Vec<String>,
    pub target_image_is_zero: bool,
    pub flat_base_change: bool,
    pub faithfully_flat: bool,
}

impl ArtinOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("test_ring_family".into(), Json::str(&self.test_ring_family)),
            (
                "is_free_observation_chart".into(),
                Json::Bool(self.is_free_observation_chart),
            ),
            (
                "eliminated_residuals".into(),
                Json::Arr(self.eliminated_residuals.iter().map(Json::str).collect()),
            ),
            (
                "local_isomorphism_at_base".into(),
                Json::Bool(self.local_isomorphism_at_base),
            ),
            (
                "lift_failure_mode".into(),
                Json::str(&self.lift_failure_mode),
            ),
        ]);
        if let Some(d) = self.syntactic_degree_bound {
            obj.insert("syntactic_degree_bound".into(), Json::Nat(d));
        }
        match self.detection_order_nu {
            Some(nu) => {
                obj.insert("detection_order_nu".into(), Json::Nat(nu as u64));
            }
            None => {
                obj.insert("detection_order_nu".into(), Json::str("infinity"));
            }
        }
        if let Some(u) = &self.universal_first_obstruction {
            obj.insert(
                "universal_first_obstruction".into(),
                Json::obj([
                    ("nu", Json::Nat(u.nu as u64)),
                    ("r_base", Json::str(&u.r_base_label)),
                    ("r_prime", Json::str(&u.r_prime_label)),
                    ("kernel_dim", Json::Nat(u.kernel_dim as u64)),
                    (
                        "kappa_u_images",
                        Json::Arr(u.kappa_u_images.iter().map(Json::str).collect()),
                    ),
                    ("kappa_u_nonzero", Json::Bool(u.kappa_u_nonzero)),
                    (
                        "two_context_cech_matches",
                        Json::Bool(u.two_context_cech_matches),
                    ),
                    ("constant_lift_exists", Json::Bool(u.constant_lift_exists)),
                ]),
            );
        }
        if let Some(c) = &self.composition_law {
            obj.insert(
                "composition_law".into(),
                Json::obj([
                    ("nu_u", opt_nu_json(c.nu_u)),
                    ("nu_v", opt_nu_json(c.nu_v)),
                    ("nu_vu", opt_nu_json(c.nu_vu)),
                    ("min_law_verified", Json::Bool(c.min_law_verified)),
                ]),
            );
        }
        if let Some(bc) = &self.base_change {
            obj.insert(
                "base_change".into(),
                Json::obj([
                    ("source_domain", Json::str(&bc.source_domain)),
                    ("target_domain", Json::str(&bc.target_domain)),
                    ("source_nu", opt_nu_json(bc.source_nu)),
                    ("target_nu", opt_nu_json(bc.target_nu)),
                    ("test_order", Json::Nat(bc.test_order as u64)),
                    (
                        "source_dr_generators",
                        Json::Arr(bc.source_dr_generators.iter().map(Json::str).collect()),
                    ),
                    (
                        "abstract_tensor_nonzero",
                        Json::Bool(bc.abstract_tensor_nonzero),
                    ),
                    (
                        "target_image_generators",
                        Json::Arr(bc.target_image_generators.iter().map(Json::str).collect()),
                    ),
                    ("target_image_is_zero", Json::Bool(bc.target_image_is_zero)),
                    ("flat_base_change", Json::Bool(bc.flat_base_change)),
                    ("faithfully_flat", Json::Bool(bc.faithfully_flat)),
                ]),
            );
        }
        Json::Obj(obj)
    }
}

pub use crate::ir::result_phase4_diag_atlas::{
    AtlasOutcomeDetail, AtlasRefinementResult, CoeffChangeResult, CollisionMayerVietorisResult,
    ConditionCResult, ConstrainedRepairSummary, DiagnosticsOutcomeDetail,
    DimensionProbePointResult, DimensionRealizationResult, ExplicitComplexChangeResult,
    ExtendedCheckOutcome, ExtendedLanguageResult, ForgetfulReadingResult, LawValueBlockSummary,
    PartitionStratumSummary, RPointContrastResult, UpperSemicontinuityRefutation,
};

fn str_map_json(map: &BTreeMap<String, String>) -> Json {
    Json::Obj(
        map.iter()
            .map(|(k, v)| (k.clone(), Json::str(v)))
            .collect(),
    )
}

fn opt_nu_json(nu: Option<usize>) -> Json {
    match nu {
        Some(n) => Json::Nat(n as u64),
        None => Json::str("infinity"),
    }
}
