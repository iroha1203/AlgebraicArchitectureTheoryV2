//! Phase 4 診断層（`DiagnosticsOutcomeDetail`）・Atlas 細分化（`AtlasOutcomeDetail`）の結果詳細と JSON 出力。

use crate::ir::result::ReevalCheck;
use archsig_common::canonical::{Json, JsonObject};
use std::collections::BTreeMap;

/// 整数診断複体・係数変更・診断層 `B_π`・合流 Mayer–Vietoris・診断次元実現の詳細出力（AC5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagnosticsOutcomeDetail {
    pub diagnostic_coeff_label: String,
    pub reading_adequate: bool,
    pub d1_d0_zero_verified: bool,
    pub cell_dims: [usize; 3],
    pub h0_summary: String,
    pub h1_summary: String,
    pub h2_summary: String,
    pub h0_free_rank: usize,
    pub h1_free_rank: usize,
    pub h1_torsion: Vec<String>,
    pub h2_free_rank: usize,
    pub block_decomposition: Vec<LawValueBlockSummary>,
    pub coeff_change: Option<CoeffChangeResult>,
    pub strata: Vec<PartitionStratumSummary>,
    pub collisions: Vec<CollisionMayerVietorisResult>,
    pub upper_semicontinuity_refutation: Option<UpperSemicontinuityRefutation>,
    pub r_point_contrast: Option<RPointContrastResult>,
    pub dimension_realization: Option<DimensionRealizationResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawValueBlockSummary {
    pub law_name: String,
    pub value_label: String,
    pub cell_dims: [usize; 3],
    pub h0_free_rank: usize,
    pub h1_free_rank: usize,
    pub h1_torsion: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoeffChangeResult {
    pub source_domain: String,
    pub target_domain: String,
    pub is_flat: bool,
    pub is_faithfully_flat: bool,
    pub fixed_label_c0_dim: usize,
    pub fixed_label_h0_summary: String,
    pub fixed_label_h1_summary: String,
    pub regenerated_c0_dim: Option<usize>,
    pub regenerated_h0_summary: Option<String>,
    pub regenerated_h1_summary: Option<String>,
    pub label_collision_map_description: Option<String>,
    pub explicit_complex_check: Option<ExplicitComplexChangeResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExplicitComplexChangeResult {
    pub source_h0: String,
    pub source_h1: String,
    pub target_h0: String,
    pub target_h1: String,
    pub flat_preservation_holds: bool,
    pub designated_class_zero_in_source: Option<bool>,
    pub designated_class_zero_in_target: Option<bool>,
    pub torsion_vanished_in_target: Option<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartitionStratumSummary {
    pub partition: Vec<Vec<String>>,
    pub equations: Vec<String>,
    pub invertibles: Vec<String>,
    pub h0_free_rank: usize,
    pub h1_free_rank: usize,
    pub h2_free_rank: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CollisionMayerVietorisResult {
    pub label: String,
    pub ker_h1_r_dim: usize,
    pub coker_h1_r_dim: usize,
    pub coker_h0_rho_dim: usize,
    pub im_h1_rho_dim: usize,
    pub mayer_vietoris_identity_verified: bool,
    pub h1_r_is_isomorphism: bool,
    pub multi_stage_order_independent: Option<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpperSemicontinuityRefutation {
    pub generic_partition: Vec<Vec<String>>,
    pub special_partition: Vec<Vec<String>>,
    pub generic_h1_dim: usize,
    pub special_h1_dim: usize,
    pub pseudo_coherent_complex_excluded: bool,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RPointContrastResult {
    pub ring_label: String,
    pub r_values_by_point: BTreeMap<String, BTreeMap<String, String>>,
    pub r_values_differ: bool,
    pub geometric_stalk_h1_dims: BTreeMap<String, usize>,
    pub geometric_stalks_agree: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DimensionRealizationResult {
    pub cycle_vertices: usize,
    pub probe_results: Vec<DimensionProbePointResult>,
    pub all_probes_matched: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DimensionProbePointResult {
    pub label: String,
    pub expected_indicator: usize,
    pub computed_h1_dim: usize,
    pub matched: bool,
}

impl DiagnosticsOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            (
                "diagnostic_coeff".into(),
                Json::str(&self.diagnostic_coeff_label),
            ),
            ("reading_adequate".into(), Json::Bool(self.reading_adequate)),
            (
                "d1_d0_zero_verified".into(),
                Json::Bool(self.d1_d0_zero_verified),
            ),
            (
                "cell_dims".into(),
                Json::Arr(
                    self.cell_dims
                        .iter()
                        .map(|&d| Json::Nat(d as u64))
                        .collect(),
                ),
            ),
            ("h0".into(), Json::str(&self.h0_summary)),
            ("h1".into(), Json::str(&self.h1_summary)),
            ("h2".into(), Json::str(&self.h2_summary)),
            ("h0_free_rank".into(), Json::Nat(self.h0_free_rank as u64)),
            ("h1_free_rank".into(), Json::Nat(self.h1_free_rank as u64)),
            (
                "h1_torsion".into(),
                Json::Arr(self.h1_torsion.iter().map(Json::str).collect()),
            ),
            ("h2_free_rank".into(), Json::Nat(self.h2_free_rank as u64)),
            (
                "block_decomposition".into(),
                Json::Arr(
                    self.block_decomposition
                        .iter()
                        .map(|b| {
                            Json::obj([
                                ("law_name", Json::str(&b.law_name)),
                                ("value_label", Json::str(&b.value_label)),
                                (
                                    "cell_dims",
                                    Json::Arr(
                                        b.cell_dims.iter().map(|&d| Json::Nat(d as u64)).collect(),
                                    ),
                                ),
                                ("h0_free_rank", Json::Nat(b.h0_free_rank as u64)),
                                ("h1_free_rank", Json::Nat(b.h1_free_rank as u64)),
                                (
                                    "h1_torsion",
                                    Json::Arr(b.h1_torsion.iter().map(Json::str).collect()),
                                ),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "strata".into(),
                Json::Arr(
                    self.strata
                        .iter()
                        .map(|s| {
                            Json::obj([
                                ("partition", partition_json(&s.partition)),
                                (
                                    "equations",
                                    Json::Arr(s.equations.iter().map(Json::str).collect()),
                                ),
                                (
                                    "invertibles",
                                    Json::Arr(s.invertibles.iter().map(Json::str).collect()),
                                ),
                                ("h0_free_rank", Json::Nat(s.h0_free_rank as u64)),
                                ("h1_free_rank", Json::Nat(s.h1_free_rank as u64)),
                                ("h2_free_rank", Json::Nat(s.h2_free_rank as u64)),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "collisions".into(),
                Json::Arr(
                    self.collisions
                        .iter()
                        .map(|c| {
                            let mut co = JsonObject::from([
                                ("label".into(), Json::str(&c.label)),
                                ("ker_h1_r_dim".into(), Json::Nat(c.ker_h1_r_dim as u64)),
                                ("coker_h1_r_dim".into(), Json::Nat(c.coker_h1_r_dim as u64)),
                                (
                                    "coker_h0_rho_dim".into(),
                                    Json::Nat(c.coker_h0_rho_dim as u64),
                                ),
                                ("im_h1_rho_dim".into(), Json::Nat(c.im_h1_rho_dim as u64)),
                                (
                                    "mayer_vietoris_identity_verified".into(),
                                    Json::Bool(c.mayer_vietoris_identity_verified),
                                ),
                                (
                                    "h1_r_is_isomorphism".into(),
                                    Json::Bool(c.h1_r_is_isomorphism),
                                ),
                            ]);
                            if let Some(indep) = c.multi_stage_order_independent {
                                co.insert(
                                    "multi_stage_order_independent".into(),
                                    Json::Bool(indep),
                                );
                            }
                            Json::Obj(co)
                        })
                        .collect(),
                ),
            ),
        ]);
        if let Some(cc) = &self.coeff_change {
            let mut co = JsonObject::from([
                ("source_domain".into(), Json::str(&cc.source_domain)),
                ("target_domain".into(), Json::str(&cc.target_domain)),
                ("is_flat".into(), Json::Bool(cc.is_flat)),
                (
                    "is_faithfully_flat".into(),
                    Json::Bool(cc.is_faithfully_flat),
                ),
                (
                    "fixed_label_c0_dim".into(),
                    Json::Nat(cc.fixed_label_c0_dim as u64),
                ),
                (
                    "fixed_label_h0".into(),
                    Json::str(&cc.fixed_label_h0_summary),
                ),
                (
                    "fixed_label_h1".into(),
                    Json::str(&cc.fixed_label_h1_summary),
                ),
            ]);
            if let Some(rc0) = cc.regenerated_c0_dim {
                co.insert("regenerated_c0_dim".into(), Json::Nat(rc0 as u64));
            }
            if let Some(rh0) = &cc.regenerated_h0_summary {
                co.insert("regenerated_h0".into(), Json::str(rh0));
            }
            if let Some(rh1) = &cc.regenerated_h1_summary {
                co.insert("regenerated_h1".into(), Json::str(rh1));
            }
            if let Some(desc) = &cc.label_collision_map_description {
                co.insert("label_collision_map".into(), Json::str(desc));
            }
            if let Some(ex) = &cc.explicit_complex_check {
                let mut eo = JsonObject::from([
                    ("source_h0".into(), Json::str(&ex.source_h0)),
                    ("source_h1".into(), Json::str(&ex.source_h1)),
                    ("target_h0".into(), Json::str(&ex.target_h0)),
                    ("target_h1".into(), Json::str(&ex.target_h1)),
                    (
                        "flat_preservation_holds".into(),
                        Json::Bool(ex.flat_preservation_holds),
                    ),
                ]);
                if let Some(b) = ex.designated_class_zero_in_source {
                    eo.insert("designated_class_zero_in_source".into(), Json::Bool(b));
                }
                if let Some(b) = ex.designated_class_zero_in_target {
                    eo.insert("designated_class_zero_in_target".into(), Json::Bool(b));
                }
                if let Some(b) = ex.torsion_vanished_in_target {
                    eo.insert("torsion_vanished_in_target".into(), Json::Bool(b));
                }
                co.insert("explicit_complex_check".into(), Json::Obj(eo));
            }
            obj.insert("coeff_change".into(), Json::Obj(co));
        }
        if let Some(u) = &self.upper_semicontinuity_refutation {
            obj.insert(
                "upper_semicontinuity_refutation".into(),
                Json::obj([
                    ("generic_partition", partition_json(&u.generic_partition)),
                    ("special_partition", partition_json(&u.special_partition)),
                    ("generic_h1_dim", Json::Nat(u.generic_h1_dim as u64)),
                    ("special_h1_dim", Json::Nat(u.special_h1_dim as u64)),
                    (
                        "pseudo_coherent_complex_excluded",
                        Json::Bool(u.pseudo_coherent_complex_excluded),
                    ),
                    ("reason", Json::str(&u.reason)),
                ]),
            );
        }
        if let Some(rp) = &self.r_point_contrast {
            let vals = rp
                .r_values_by_point
                .iter()
                .map(|(pt, m)| (pt.clone(), str_map_json(m)))
                .collect();
            let stalks = rp
                .geometric_stalk_h1_dims
                .iter()
                .map(|(pt, &d)| (pt.clone(), Json::Nat(d as u64)))
                .collect();
            obj.insert(
                "r_point_contrast".into(),
                Json::obj([
                    ("ring", Json::str(&rp.ring_label)),
                    ("r_values_by_point", Json::Obj(vals)),
                    ("r_values_differ", Json::Bool(rp.r_values_differ)),
                    ("geometric_stalk_h1_dims", Json::Obj(stalks)),
                    (
                        "geometric_stalks_agree",
                        Json::Bool(rp.geometric_stalks_agree),
                    ),
                ]),
            );
        }
        if let Some(dr) = &self.dimension_realization {
            obj.insert(
                "dimension_realization".into(),
                Json::obj([
                    ("cycle_vertices", Json::Nat(dr.cycle_vertices as u64)),
                    ("all_probes_matched", Json::Bool(dr.all_probes_matched)),
                    (
                        "probe_results",
                        Json::Arr(
                            dr.probe_results
                                .iter()
                                .map(|p| {
                                    Json::obj([
                                        ("label", Json::str(&p.label)),
                                        (
                                            "expected_indicator",
                                            Json::Nat(p.expected_indicator as u64),
                                        ),
                                        ("computed_h1_dim", Json::Nat(p.computed_h1_dim as u64)),
                                        ("matched", Json::Bool(p.matched)),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                ]),
            );
        }
        Json::Obj(obj)
    }
}

/// 有限グラフ実 adapter・SAGA 比較・制約付き全修復・指定診断類 `κ_b`・Atlas 細分化 C0–C6 の詳細出力（AC6）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtlasOutcomeDetail {
    pub coeff_ring_label: String,
    pub num_vertices: usize,
    pub num_edges: usize,
    pub graph_connected: bool,
    pub saga_sign_commutes_verified: bool,
    pub real_residuals: BTreeMap<String, String>,
    pub spanning_tree_edges: Vec<String>,
    pub chord_edges: Vec<String>,
    pub designated_class_o_b_coords: Vec<String>,
    pub designated_class_kappa_b_coords: Vec<String>,
    pub o_b_is_zero: bool,
    pub kappa_b_is_zero: bool,
    pub diagnostic_h1_rank: usize,
    pub primitive_relation_connected_verified: bool,
    pub z_to_q_zero_reflection_verified: Option<bool>,
    pub unconstrained_global_operation_exists: bool,
    pub unconstrained_particular_lambda: Option<BTreeMap<String, String>>,
    pub unconstrained_h0_torsor_rank: usize,
    pub unconstrained_reevaluation: Option<ReevalCheck>,
    pub vertex_constrained_repair: ConstrainedRepairSummary,
    pub edge_constrained_repair: ConstrainedRepairSummary,
    pub refinement: Option<AtlasRefinementResult>,
    pub extended_language_non_transport: Option<ExtendedLanguageResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstrainedRepairSummary {
    pub allowed_items: Vec<String>,
    pub repair_exists: bool,
    pub particular_delta: Option<BTreeMap<String, String>>,
    pub torsor_basis: Vec<BTreeMap<String, String>>,
    pub h0_operation_torsor_rank: usize,
    pub reevaluation: Option<ReevalCheck>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConditionCResult {
    pub c0_support_image: bool,
    pub c1_block_fiber_connected: bool,
    pub c2_edge_lift: bool,
    pub c3_fiber_rational_1_cycles: bool,
    pub c4_face_lift: bool,
    pub c5_edge_lift_unique: bool,
    pub c6_self_loop: bool,
    pub all_passed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtlasRefinementResult {
    pub condition_c: ConditionCResult,
    pub cochain_map_commutes: bool,
    pub h0_isomorphism: bool,
    pub h1_isomorphism: bool,
    pub designated_o_preserved: bool,
    pub designated_kappa_preserved: bool,
    pub repair_fiber_isomorphism_verified: bool,
    pub inverse_reconstruction_verified: bool,
    pub eval_condition_fiber_preserved: Option<bool>,
    pub forgetful_reading_contrast: Option<ForgetfulReadingResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForgetfulReadingResult {
    pub adequacy_and_c0_c6_hold: bool,
    pub eval_constant_on_fiber: bool,
    pub eval_descends_to_coarse: bool,
    pub condition_constant_on_fiber: bool,
    pub condition_descends_to_coarse: bool,
    pub sample_eval_values: BTreeMap<String, String>,
    pub sample_condition_holds: BTreeMap<String, bool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtendedCheckOutcome {
    pub name: String,
    /// `"protocol_sequence"` または `"runtime_arg_op"`。
    pub kind: String,
    pub transport_preserved: bool,
    pub before_values: Vec<String>,
    pub after_values: Vec<String>,
    pub law_residuals: Vec<String>,
    pub detail: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtendedLanguageResult {
    pub atomic_ops_commute: BTreeMap<String, bool>,
    pub all_atomic_ops_commute: bool,
    pub extended_check_results: Vec<ExtendedCheckOutcome>,
    pub all_extended_checks_preserved: bool,
}

impl AtlasOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("coeff_ring".into(), Json::str(&self.coeff_ring_label)),
            ("num_vertices".into(), Json::Nat(self.num_vertices as u64)),
            ("num_edges".into(), Json::Nat(self.num_edges as u64)),
            ("graph_connected".into(), Json::Bool(self.graph_connected)),
            (
                "saga_sign_commutes_verified".into(),
                Json::Bool(self.saga_sign_commutes_verified),
            ),
            ("real_residuals".into(), str_map_json(&self.real_residuals)),
            (
                "spanning_tree_edges".into(),
                Json::Arr(self.spanning_tree_edges.iter().map(Json::str).collect()),
            ),
            (
                "chord_edges".into(),
                Json::Arr(self.chord_edges.iter().map(Json::str).collect()),
            ),
            (
                "designated_class_o_b_coords".into(),
                Json::Arr(
                    self.designated_class_o_b_coords
                        .iter()
                        .map(Json::str)
                        .collect(),
                ),
            ),
            (
                "designated_class_kappa_b_coords".into(),
                Json::Arr(
                    self.designated_class_kappa_b_coords
                        .iter()
                        .map(Json::str)
                        .collect(),
                ),
            ),
            ("o_b_is_zero".into(), Json::Bool(self.o_b_is_zero)),
            ("kappa_b_is_zero".into(), Json::Bool(self.kappa_b_is_zero)),
            (
                "diagnostic_h1_rank".into(),
                Json::Nat(self.diagnostic_h1_rank as u64),
            ),
            (
                "primitive_relation_connected_verified".into(),
                Json::Bool(self.primitive_relation_connected_verified),
            ),
            (
                "unconstrained_global_operation_exists".into(),
                Json::Bool(self.unconstrained_global_operation_exists),
            ),
            (
                "unconstrained_h0_torsor_rank".into(),
                Json::Nat(self.unconstrained_h0_torsor_rank as u64),
            ),
            (
                "vertex_constrained_repair".into(),
                constrained_repair_json(&self.vertex_constrained_repair),
            ),
            (
                "edge_constrained_repair".into(),
                constrained_repair_json(&self.edge_constrained_repair),
            ),
        ]);
        if let Some(reflected) = self.z_to_q_zero_reflection_verified {
            obj.insert(
                "z_to_q_zero_reflection_verified".into(),
                Json::Bool(reflected),
            );
        }
        if let Some(p) = &self.unconstrained_particular_lambda {
            obj.insert("unconstrained_particular_lambda".into(), str_map_json(p));
        }
        if let Some(re) = &self.unconstrained_reevaluation {
            obj.insert("unconstrained_reevaluation".into(), re.to_json());
        }
        if let Some(r) = &self.refinement {
            let mut ro = JsonObject::from([
                (
                    "condition_c".into(),
                    Json::obj([
                        (
                            "c0_support_image",
                            Json::Bool(r.condition_c.c0_support_image),
                        ),
                        (
                            "c1_block_fiber_connected",
                            Json::Bool(r.condition_c.c1_block_fiber_connected),
                        ),
                        ("c2_edge_lift", Json::Bool(r.condition_c.c2_edge_lift)),
                        (
                            "c3_fiber_rational_1_cycles",
                            Json::Bool(r.condition_c.c3_fiber_rational_1_cycles),
                        ),
                        ("c4_face_lift", Json::Bool(r.condition_c.c4_face_lift)),
                        (
                            "c5_edge_lift_unique",
                            Json::Bool(r.condition_c.c5_edge_lift_unique),
                        ),
                        ("c6_self_loop", Json::Bool(r.condition_c.c6_self_loop)),
                        ("all_passed", Json::Bool(r.condition_c.all_passed)),
                    ]),
                ),
                (
                    "cochain_map_commutes".into(),
                    Json::Bool(r.cochain_map_commutes),
                ),
                ("h0_isomorphism".into(), Json::Bool(r.h0_isomorphism)),
                ("h1_isomorphism".into(), Json::Bool(r.h1_isomorphism)),
                (
                    "designated_o_preserved".into(),
                    Json::Bool(r.designated_o_preserved),
                ),
                (
                    "designated_kappa_preserved".into(),
                    Json::Bool(r.designated_kappa_preserved),
                ),
                (
                    "repair_fiber_isomorphism_verified".into(),
                    Json::Bool(r.repair_fiber_isomorphism_verified),
                ),
                (
                    "inverse_reconstruction_verified".into(),
                    Json::Bool(r.inverse_reconstruction_verified),
                ),
            ]);
            if let Some(ep) = r.eval_condition_fiber_preserved {
                ro.insert("eval_condition_fiber_preserved".into(), Json::Bool(ep));
            }
            if let Some(fg) = &r.forgetful_reading_contrast {
                let cond_map = fg
                    .sample_condition_holds
                    .iter()
                    .map(|(k, &v)| (k.clone(), Json::Bool(v)))
                    .collect();
                ro.insert(
                    "forgetful_reading_contrast".into(),
                    Json::obj([
                        (
                            "adequacy_and_c0_c6_hold",
                            Json::Bool(fg.adequacy_and_c0_c6_hold),
                        ),
                        (
                            "eval_constant_on_fiber",
                            Json::Bool(fg.eval_constant_on_fiber),
                        ),
                        (
                            "eval_descends_to_coarse",
                            Json::Bool(fg.eval_descends_to_coarse),
                        ),
                        (
                            "condition_constant_on_fiber",
                            Json::Bool(fg.condition_constant_on_fiber),
                        ),
                        (
                            "condition_descends_to_coarse",
                            Json::Bool(fg.condition_descends_to_coarse),
                        ),
                        ("sample_eval_values", str_map_json(&fg.sample_eval_values)),
                        ("sample_condition_holds", Json::Obj(cond_map)),
                    ]),
                );
            }
            obj.insert("refinement".into(), Json::Obj(ro));
        }
        if let Some(ext) = &self.extended_language_non_transport {
            let atomic_map = ext
                .atomic_ops_commute
                .iter()
                .map(|(k, &v)| (k.clone(), Json::Bool(v)))
                .collect();
            let checks = ext
                .extended_check_results
                .iter()
                .map(|c| {
                    Json::obj([
                        ("name", Json::str(&c.name)),
                        ("kind", Json::str(&c.kind)),
                        ("transport_preserved", Json::Bool(c.transport_preserved)),
                        (
                            "before_values",
                            Json::Arr(c.before_values.iter().map(Json::str).collect()),
                        ),
                        (
                            "after_values",
                            Json::Arr(c.after_values.iter().map(Json::str).collect()),
                        ),
                        (
                            "law_residuals",
                            Json::Arr(c.law_residuals.iter().map(Json::str).collect()),
                        ),
                        ("detail", Json::str(&c.detail)),
                    ])
                })
                .collect();
            obj.insert(
                "extended_language_non_transport".into(),
                Json::obj([
                    ("atomic_ops_commute", Json::Obj(atomic_map)),
                    (
                        "all_atomic_ops_commute",
                        Json::Bool(ext.all_atomic_ops_commute),
                    ),
                    ("extended_check_results", Json::Arr(checks)),
                    (
                        "all_extended_checks_preserved",
                        Json::Bool(ext.all_extended_checks_preserved),
                    ),
                ]),
            );
        }
        Json::Obj(obj)
    }
}

fn constrained_repair_json(s: &ConstrainedRepairSummary) -> Json {
    let mut obj = JsonObject::from([
        (
            "allowed_items".into(),
            Json::Arr(s.allowed_items.iter().map(Json::str).collect()),
        ),
        ("repair_exists".into(), Json::Bool(s.repair_exists)),
        (
            "torsor_basis".into(),
            Json::Arr(s.torsor_basis.iter().map(str_map_json).collect()),
        ),
        (
            "h0_operation_torsor_rank".into(),
            Json::Nat(s.h0_operation_torsor_rank as u64),
        ),
    ]);
    if let Some(p) = &s.particular_delta {
        obj.insert("particular_delta".into(), str_map_json(p));
    }
    if let Some(re) = &s.reevaluation {
        obj.insert("reevaluation".into(), re.to_json());
    }
    Json::Obj(obj)
}

fn str_map_json(map: &BTreeMap<String, String>) -> Json {
    Json::Obj(map.iter().map(|(k, v)| (k.clone(), Json::str(v))).collect())
}

fn partition_json(partition: &[Vec<String>]) -> Json {
    Json::Arr(
        partition
            .iter()
            .map(|b| Json::Arr(b.iter().map(Json::str).collect()))
            .collect(),
    )
}
