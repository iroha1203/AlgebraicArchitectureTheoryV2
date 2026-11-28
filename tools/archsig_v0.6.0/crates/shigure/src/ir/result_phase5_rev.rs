//! Phase 5 第19章（`RevisionOutcomeDetail`・`MultisourceOutcomeDetail`）の結果詳細型。

use crate::ir::result::ReevalCheck;
use archsig_common::canonical::{Json, JsonObject};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevisionProbeResult {
    pub probe_name: String,
    pub outside_cone: bool,
    pub before_eval: String,
    pub after_eval: String,
    pub invariant_satisfied: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnfReuseDetail {
    pub coeff_domain_label: String,
    pub rank: usize,
    pub diagonals: Vec<String>,
    pub cokernel_torsion: Vec<String>,
    pub cokernel_free_rank: usize,
    pub umv_verified: bool,
    pub reused_snf: bool,
    pub after_solvable: bool,
    pub after_particular: Option<Vec<String>>,
    pub kernel_basis: Vec<Vec<String>>,
    pub inconsistency_cert_row: Option<usize>,
    pub reeval: ReevalCheck,
}

/// `shigure_revision`（第19章前半）の計算詳細結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevisionOutcomeDetail {
    pub kind: String,
    pub before_consistent: bool,
    pub after_consistent: bool,
    pub monotonicity_applicable: bool,
    pub monotonicity_preserved: Option<bool>,
    pub delta_coords: Vec<String>,
    pub invalidation_cone: Vec<String>,
    pub outside_cone_coords: Vec<String>,
    pub outside_projection_equal: Option<bool>,
    pub probe_results: Vec<RevisionProbeResult>,
    pub snf_reuse: Option<SnfReuseDetail>,
}

impl RevisionOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let probes = self
            .probe_results
            .iter()
            .map(|p| {
                Json::obj([
                    ("probe_name", Json::str(&p.probe_name)),
                    ("outside_cone", Json::Bool(p.outside_cone)),
                    ("before_eval", Json::str(&p.before_eval)),
                    ("after_eval", Json::str(&p.after_eval)),
                    ("invariant_satisfied", Json::Bool(p.invariant_satisfied)),
                ])
            })
            .collect();

        let mut obj = JsonObject::from([
            ("kind".into(), Json::str(&self.kind)),
            (
                "before_consistent".into(),
                Json::Bool(self.before_consistent),
            ),
            ("after_consistent".into(), Json::Bool(self.after_consistent)),
            (
                "monotonicity_applicable".into(),
                Json::Bool(self.monotonicity_applicable),
            ),
            (
                "delta_coords".into(),
                Json::Arr(self.delta_coords.iter().map(Json::str).collect()),
            ),
            (
                "invalidation_cone".into(),
                Json::Arr(self.invalidation_cone.iter().map(Json::str).collect()),
            ),
            (
                "outside_cone_coords".into(),
                Json::Arr(self.outside_cone_coords.iter().map(Json::str).collect()),
            ),
            ("probe_results".into(), Json::Arr(probes)),
        ]);
        if let Some(m) = self.monotonicity_preserved {
            obj.insert("monotonicity_preserved".into(), Json::Bool(m));
        }
        if let Some(eq) = self.outside_projection_equal {
            obj.insert("outside_projection_equal".into(), Json::Bool(eq));
        }
        if let Some(snf) = &self.snf_reuse {
            let mut so = JsonObject::from([
                ("coeff_domain".into(), Json::str(&snf.coeff_domain_label)),
                ("rank".into(), Json::Nat(snf.rank as u64)),
                (
                    "diagonals".into(),
                    Json::Arr(snf.diagonals.iter().map(Json::str).collect()),
                ),
                (
                    "cokernel_torsion".into(),
                    Json::Arr(snf.cokernel_torsion.iter().map(Json::str).collect()),
                ),
                (
                    "cokernel_free_rank".into(),
                    Json::Nat(snf.cokernel_free_rank as u64),
                ),
                ("umv_verified".into(), Json::Bool(snf.umv_verified)),
                ("reused_snf".into(), Json::Bool(snf.reused_snf)),
                ("after_solvable".into(), Json::Bool(snf.after_solvable)),
                (
                    "kernel_basis".into(),
                    Json::Arr(
                        snf.kernel_basis
                            .iter()
                            .map(|k| Json::Arr(k.iter().map(Json::str).collect()))
                            .collect(),
                    ),
                ),
                ("reevaluation".into(), snf.reeval.to_json()),
            ]);
            if let Some(part) = &snf.after_particular {
                so.insert(
                    "after_particular".into(),
                    Json::Arr(part.iter().map(Json::str).collect()),
                );
            }
            if let Some(row) = snf.inconsistency_cert_row {
                so.insert("inconsistency_cert_row".into(), Json::Nat(row as u64));
            }
            obj.insert("snf_reuse".into(), Json::Obj(so));
        }
        Json::Obj(obj)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupportCostEntry {
    pub support: Vec<String>,
    pub total_cost: Option<String>,
    pub stability_verified: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupportGoalDetail {
    pub all_candidates_consistent: bool,
    pub minimal_supports: Vec<SupportCostEntry>,
    pub min_cost_supports: Vec<SupportCostEntry>,
    pub insufficiency_witness: Option<BTreeMap<String, String>>,
    pub post_verification_reeval_needed: bool,
    pub post_verification_minimal_supports: Option<Vec<SupportCostEntry>>,
    pub reevaluation: Option<ReevalCheck>,
}

/// `shigure_multisource`（第19章後半）の計算詳細結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultisourceOutcomeDetail {
    pub pairwise_consistent: bool,
    pub all_sources_consistent: bool,
    pub minimal_conflict_sets: Vec<Vec<String>>,
    pub minimal_conflicts_verified: bool,
    pub support_goal: Option<SupportGoalDetail>,
}

impl MultisourceOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            (
                "pairwise_consistent".into(),
                Json::Bool(self.pairwise_consistent),
            ),
            (
                "all_sources_consistent".into(),
                Json::Bool(self.all_sources_consistent),
            ),
            (
                "minimal_conflict_sets".into(),
                Json::Arr(
                    self.minimal_conflict_sets
                        .iter()
                        .map(|s| Json::Arr(s.iter().map(Json::str).collect()))
                        .collect(),
                ),
            ),
            (
                "minimal_conflicts_verified".into(),
                Json::Bool(self.minimal_conflicts_verified),
            ),
        ]);
        if let Some(sg) = &self.support_goal {
            let map_entries = |entries: &[SupportCostEntry]| -> Vec<Json> {
                entries
                    .iter()
                    .map(|e| {
                        let mut eo = JsonObject::from([
                            (
                                "support".into(),
                                Json::Arr(e.support.iter().map(Json::str).collect()),
                            ),
                            (
                                "stability_verified".into(),
                                Json::Bool(e.stability_verified),
                            ),
                        ]);
                        if let Some(c) = &e.total_cost {
                            eo.insert("total_cost".into(), Json::str(c));
                        }
                        Json::Obj(eo)
                    })
                    .collect()
            };
            let mut sgo = JsonObject::from([
                (
                    "all_candidates_consistent".into(),
                    Json::Bool(sg.all_candidates_consistent),
                ),
                (
                    "minimal_supports".into(),
                    Json::Arr(map_entries(&sg.minimal_supports)),
                ),
                (
                    "min_cost_supports".into(),
                    Json::Arr(map_entries(&sg.min_cost_supports)),
                ),
                (
                    "post_verification_reeval_needed".into(),
                    Json::Bool(sg.post_verification_reeval_needed),
                ),
            ]);
            if let Some(w) = &sg.insufficiency_witness {
                sgo.insert(
                    "insufficiency_witness".into(),
                    Json::Obj(w.iter().map(|(k, v)| (k.clone(), Json::str(v))).collect()),
                );
            }
            if let Some(pv) = &sg.post_verification_minimal_supports {
                sgo.insert(
                    "post_verification_minimal_supports".into(),
                    Json::Arr(map_entries(pv)),
                );
            }
            if let Some(re) = &sg.reevaluation {
                sgo.insert("reevaluation".into(), re.to_json());
            }
            obj.insert("support_goal".into(), Json::Obj(sgo));
        }
        Json::Obj(obj)
    }
}
