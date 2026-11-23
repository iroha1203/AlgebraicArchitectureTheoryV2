//! SHIGURE Phase 3（複数解釈族・頑健判定・Chevalley 四分類・追加観測）の型付き結果構造。

use crate::ir::change::PointDomain;
use crate::ir::family::GoodnessKind;
use crate::ir::provenance::SourceRef;
use crate::ir::result::{EmptyWitness, ReevalCheck, RestoredArtifact, SilenceReason, Verdict};
use archsig_common::canonical::{Json, JsonObject};
use std::collections::BTreeMap;

fn str_map_to_json(map: &BTreeMap<String, String>) -> Json {
    Json::Obj(map.iter().map(|(k, v)| (k.clone(), Json::str(v))).collect())
}

/// 整合実現 $w \in U_b(R)$ の具体 witness（由来と raw 表示フラグを含む）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealizationWitness {
    pub member_id: Option<String>,
    pub assignments: BTreeMap<String, String>,
    pub is_raw_candidate: bool,
    pub origin: SourceRef,
}

impl RealizationWitness {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("assignments".into(), str_map_to_json(&self.assignments)),
            ("is_raw_candidate".into(), Json::Bool(self.is_raw_candidate)),
            ("origin".into(), self.origin.to_json()),
        ]);
        if let Some(id) = &self.member_id {
            obj.insert("member_id".into(), Json::str(id));
        }
        Json::Obj(obj)
    }
}

/// 存在型 $E_{\mathrm{exists}}$ において $\mathcal{F}_{u,c}(R)$ から復元された補完 witness と再評価検算。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RestoredCompletionWitness {
    pub witness_assignments: BTreeMap<String, String>,
    pub restored_artifact: Option<RestoredArtifact>,
    pub reeval: ReevalCheck,
}

impl RestoredCompletionWitness {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            (
                "witness_assignments".into(),
                str_map_to_json(&self.witness_assignments),
            ),
            ("reevaluation".into(), self.reeval.to_json()),
        ]);
        if let Some(art) = &self.restored_artifact {
            obj.insert("restored_artifact".into(), art.to_json());
        }
        Json::Obj(obj)
    }
}

/// 単一組 $(u, c) \in U_b \times C_b$ の評価・補完・反証証拠。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairEvaluationWitness {
    pub realization: RealizationWitness,
    pub candidate_id: Option<String>,
    pub candidate_assignments: BTreeMap<String, String>,
    pub passed: bool,
    pub legal_execution_exists: Option<bool>,
    pub residuals: Vec<String>,
    pub empty_witness: Option<EmptyWitness>,
    pub restored_completion: Option<RestoredCompletionWitness>,
}

impl PairEvaluationWitness {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("realization".into(), self.realization.to_json()),
            (
                "candidate_assignments".into(),
                str_map_to_json(&self.candidate_assignments),
            ),
            ("passed".into(), Json::Bool(self.passed)),
            (
                "residuals".into(),
                Json::Arr(self.residuals.iter().map(Json::str).collect()),
            ),
        ]);
        if let Some(cid) = &self.candidate_id {
            obj.insert("candidate_id".into(), Json::str(cid));
        }
        if let Some(legal) = self.legal_execution_exists {
            obj.insert("legal_execution_exists".into(), Json::Bool(legal));
        }
        if let Some(ew) = &self.empty_witness {
            obj.insert("empty_witness".into(), ew.to_json());
        }
        if let Some(rc) = &self.restored_completion {
            obj.insert("restored_completion".into(), rc.to_json());
        }
        Json::Obj(obj)
    }
}

/// reading 整合実現 fiber $U_b(R)$ の非空性判定（空虚な真の分離、G-140 E4 / G-142 G2）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiberNonEmptinessResult {
    pub non_empty: bool,
    pub status: String,
    pub witness: Option<RealizationWitness>,
    pub empty_witness: Option<EmptyWitness>,
}

impl FiberNonEmptinessResult {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("non_empty".into(), Json::Bool(self.non_empty)),
            ("status".into(), Json::str(&self.status)),
        ]);
        if let Some(w) = &self.witness {
            obj.insert("witness".into(), w.to_json());
        }
        if let Some(ew) = &self.empty_witness {
            obj.insert("empty_witness".into(), ew.to_json());
        }
        Json::Obj(obj)
    }
}

/// 第 1 量化: 指定候補 $c$ の頑健性 $\forall u \in U_b(R),\ E_{\mathrm{ok},R}(u,c)$。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DesignatedValidityResult {
    pub candidate_id: Option<String>,
    pub candidate_assignments: BTreeMap<String, String>,
    pub satisfied: bool,
    pub vacuously_true_empty_fiber: bool,
    pub supporting_witnesses: Vec<PairEvaluationWitness>,
    pub counterexample: Option<PairEvaluationWitness>,
}

impl DesignatedValidityResult {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            (
                "candidate_assignments".into(),
                str_map_to_json(&self.candidate_assignments),
            ),
            ("satisfied".into(), Json::Bool(self.satisfied)),
            (
                "vacuously_true_empty_fiber".into(),
                Json::Bool(self.vacuously_true_empty_fiber),
            ),
            (
                "supporting_witnesses".into(),
                Json::Arr(
                    self.supporting_witnesses
                        .iter()
                        .map(PairEvaluationWitness::to_json)
                        .collect(),
                ),
            ),
        ]);
        if let Some(cid) = &self.candidate_id {
            obj.insert("candidate_id".into(), Json::str(cid));
        }
        if let Some(ce) = &self.counterexample {
            obj.insert("counterexample".into(), ce.to_json());
        }
        Json::Obj(obj)
    }
}

/// 第 2 量化: 各実現での可解性 $\forall u \in U_b(R)\ \exists c \in C_b(R),\ E_{\mathrm{ok},R}(u,c)$。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointwiseQuantifierResult {
    pub satisfied: bool,
    pub vacuously_true_empty_fiber: bool,
    pub witnesses: Vec<PairEvaluationWitness>,
    pub counterexample: Option<RealizationWitness>,
}

impl PointwiseQuantifierResult {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("satisfied".into(), Json::Bool(self.satisfied)),
            (
                "vacuously_true_empty_fiber".into(),
                Json::Bool(self.vacuously_true_empty_fiber),
            ),
            (
                "witnesses".into(),
                Json::Arr(
                    self.witnesses
                        .iter()
                        .map(PairEvaluationWitness::to_json)
                        .collect(),
                ),
            ),
        ]);
        if let Some(ce) = &self.counterexample {
            obj.insert("counterexample".into(), ce.to_json());
        }
        Json::Obj(obj)
    }
}

/// 第 3 量化: 共通候補の存在 $\exists c \in C_b(R)\ \forall u \in U_b(R),\ E_{\mathrm{ok},R}(u,c)$。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommonQuantifierResult {
    pub satisfied: bool,
    pub vacuously_true_empty_fiber: bool,
    pub candidate_id: Option<String>,
    pub candidate_assignments: Option<BTreeMap<String, String>>,
    pub witnesses: Vec<PairEvaluationWitness>,
    pub counterexample_witnesses: Vec<PairEvaluationWitness>,
    pub counterexample_detail: Option<String>,
}

impl CommonQuantifierResult {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("satisfied".into(), Json::Bool(self.satisfied)),
            (
                "vacuously_true_empty_fiber".into(),
                Json::Bool(self.vacuously_true_empty_fiber),
            ),
            (
                "witnesses".into(),
                Json::Arr(
                    self.witnesses
                        .iter()
                        .map(PairEvaluationWitness::to_json)
                        .collect(),
                ),
            ),
            (
                "counterexample_witnesses".into(),
                Json::Arr(
                    self.counterexample_witnesses
                        .iter()
                        .map(PairEvaluationWitness::to_json)
                        .collect(),
                ),
            ),
        ]);
        if let Some(cid) = &self.candidate_id {
            obj.insert("candidate_id".into(), Json::str(cid));
        }
        if let Some(assign) = &self.candidate_assignments {
            obj.insert("candidate_assignments".into(), str_map_to_json(assign));
        }
        if let Some(detail) = &self.counterexample_detail {
            obj.insert("counterexample_detail".into(), Json::str(detail));
        }
        Json::Obj(obj)
    }
}

/// 双対数環 $k[\varepsilon]/(\varepsilon^2)$ 等の冪零方向における反証 witness（W6）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DualNumberCounterexample {
    pub ring_description: String,
    pub assignments: BTreeMap<String, String>,
    pub nonzero_residuals: Vec<String>,
}

impl DualNumberCounterexample {
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("ring_description", Json::str(&self.ring_description)),
            ("assignments", str_map_to_json(&self.assignments)),
            (
                "nonzero_residuals",
                Json::Arr(self.nonzero_residuals.iter().map(Json::str).collect()),
            ),
        ])
    }
}

/// 全係数移送で安定な全称条件 $\mathcal{R}(R)$ および $\mathcal{R}_{\mathrm{dec}}(R)$ の検査結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniversalRingStabilityResult {
    pub evaluated: bool,
    pub stable: Option<bool>,
    pub inhabited_stable: Option<bool>,
    pub counterexample_ring: Option<String>,
    pub counterexample_point: BTreeMap<String, String>,
    pub counterexample_residuals: Vec<String>,
    pub dual_number_counterexample: Option<DualNumberCounterexample>,
    pub silence_reason: Option<SilenceReason>,
}

impl UniversalRingStabilityResult {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("evaluated".into(), Json::Bool(self.evaluated)),
            (
                "counterexample_point".into(),
                str_map_to_json(&self.counterexample_point),
            ),
            (
                "counterexample_residuals".into(),
                Json::Arr(
                    self.counterexample_residuals
                        .iter()
                        .map(Json::str)
                        .collect(),
                ),
            ),
        ]);
        if let Some(s) = self.stable {
            obj.insert("stable".into(), Json::Bool(s));
        }
        if let Some(is) = self.inhabited_stable {
            obj.insert("inhabited_stable".into(), Json::Bool(is));
        }
        if let Some(ring) = &self.counterexample_ring {
            obj.insert("counterexample_ring".into(), Json::str(ring));
        }
        if let Some(dual) = &self.dual_number_counterexample {
            obj.insert("dual_number_counterexample".into(), dual.to_json());
        }
        if let Some(sr) = &self.silence_reason {
            obj.insert("silence_reason".into(), sr.to_json());
        }
        Json::Obj(obj)
    }
}

/// P7 の raw 表示候補に対する原始式残差評価結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCandidateEvaluationSummary {
    pub member_id: String,
    pub origin: SourceRef,
    pub q_value: Vec<String>,
    pub passed: bool,
    pub legal_execution_exists: Option<bool>,
    pub residuals: Vec<String>,
}

impl RawCandidateEvaluationSummary {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("member_id".into(), Json::str(&self.member_id)),
            ("origin".into(), self.origin.to_json()),
            (
                "q_value".into(),
                Json::Arr(self.q_value.iter().map(Json::str).collect()),
            ),
            ("passed".into(), Json::Bool(self.passed)),
            (
                "residuals".into(),
                Json::Arr(self.residuals.iter().map(Json::str).collect()),
            ),
        ]);
        if let Some(legal) = self.legal_execution_exists {
            obj.insert("legal_execution_exists".into(), Json::Bool(legal));
        }
        Json::Obj(obj)
    }
}

/// 粗/細 reading 比較（G-140 E5.1 / P7 / G-142 G4）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadingComparisonResult {
    pub name: String,
    pub coarse_b: Vec<String>,
    pub fine_b: Vec<String>,
    pub commutativity_verified: bool,
    pub coarse_robust: bool,
    pub fine_robust: bool,
    pub coarse_implies_fine_preserved: bool,
    pub reverse_implication_not_claimed: bool,
    pub fine_only_counterexample: Option<PairEvaluationWitness>,
    pub raw_candidate_evaluations: Vec<RawCandidateEvaluationSummary>,
}

impl ReadingComparisonResult {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("name".into(), Json::str(&self.name)),
            (
                "coarse_b".into(),
                Json::Arr(self.coarse_b.iter().map(Json::str).collect()),
            ),
            (
                "fine_b".into(),
                Json::Arr(self.fine_b.iter().map(Json::str).collect()),
            ),
            (
                "commutativity_verified".into(),
                Json::Bool(self.commutativity_verified),
            ),
            ("coarse_robust".into(), Json::Bool(self.coarse_robust)),
            ("fine_robust".into(), Json::Bool(self.fine_robust)),
            (
                "coarse_implies_fine_preserved".into(),
                Json::Bool(self.coarse_implies_fine_preserved),
            ),
            (
                "reverse_implication_not_claimed".into(),
                Json::Bool(self.reverse_implication_not_claimed),
            ),
            (
                "raw_candidate_evaluations".into(),
                Json::Arr(
                    self.raw_candidate_evaluations
                        .iter()
                        .map(RawCandidateEvaluationSummary::to_json)
                        .collect(),
                ),
            ),
        ]);
        if let Some(ce) = &self.fine_only_counterexample {
            obj.insert("fine_only_counterexample".into(), ce.to_json());
        }
        Json::Obj(obj)
    }
}

/// `shigure_robustness` の計算結果詳細。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RobustnessOutcomeDetail {
    pub goodness_kind: GoodnessKind,
    pub fiber_non_empty: FiberNonEmptinessResult,
    pub valid_designated: Option<DesignatedValidityResult>,
    pub pointwise: Option<PointwiseQuantifierResult>,
    pub common_candidate: Option<CommonQuantifierResult>,
    pub universal_ring: Option<UniversalRingStabilityResult>,
    pub reading_comparison: Option<ReadingComparisonResult>,
}

impl RobustnessOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("goodness_kind".into(), Json::str(self.goodness_kind.wire())),
            ("fiber_non_empty".into(), self.fiber_non_empty.to_json()),
        ]);
        if let Some(vd) = &self.valid_designated {
            obj.insert("valid_designated".into(), vd.to_json());
        }
        if let Some(pw) = &self.pointwise {
            obj.insert("pointwise".into(), pw.to_json());
        }
        if let Some(cc) = &self.common_candidate {
            obj.insert("common_candidate".into(), cc.to_json());
        }
        if let Some(ur) = &self.universal_ring {
            obj.insert("universal_ring".into(), ur.to_json());
        }
        if let Some(rc) = &self.reading_comparison {
            obj.insert("reading_comparison".into(), rc.to_json());
        }
        Json::Obj(obj)
    }
}

/// 構成可能集合の各領域の局所閉層記述 `⋃ (V(equations) ∩ D(invertibles))`。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChevalleyRegionSummary {
    pub strata: Vec<(Vec<String>, Vec<String>)>,
    pub is_empty: bool,
}

impl ChevalleyRegionSummary {
    pub fn to_json(&self) -> Json {
        let strata_json = self
            .strata
            .iter()
            .map(|(eqs, invs)| {
                Json::obj([
                    ("equations", Json::Arr(eqs.iter().map(Json::str).collect())),
                    (
                        "invertibles",
                        Json::Arr(invs.iter().map(Json::str).collect()),
                    ),
                ])
            })
            .collect();
        Json::obj([
            ("is_empty", Json::Bool(self.is_empty)),
            ("strata", Json::Arr(strata_json)),
        ])
    }
}

/// Chevalley `mixed` 領域（$P_+ \cap P_-$）に対する成立実現 $u_+$ と不成立実現 $u_-$ の対。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MixedWitnessPair {
    pub candidate_id: Option<String>,
    pub candidate_assignments: BTreeMap<String, String>,
    pub pass_witness: PairEvaluationWitness,
    pub fail_witness: PairEvaluationWitness,
}

impl MixedWitnessPair {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            (
                "candidate_assignments".into(),
                str_map_to_json(&self.candidate_assignments),
            ),
            ("pass_witness".into(), self.pass_witness.to_json()),
            ("fail_witness".into(), self.fail_witness.to_json()),
        ]);
        if let Some(cid) = &self.candidate_id {
            obj.insert("candidate_id".into(), Json::str(cid));
        }
        Json::Obj(obj)
    }
}

/// 幾何点分類と対照する有理点 fiber プローブの判定結果（W5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RationalFiberProbeResult {
    pub probe_name: String,
    pub u_assignments: BTreeMap<String, String>,
    pub c_assignments: BTreeMap<String, String>,
    pub verdict: Verdict,
    pub rational_witness: Option<BTreeMap<String, String>>,
    pub detail: String,
}

impl RationalFiberProbeResult {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("probe_name".into(), Json::str(&self.probe_name)),
            ("u_assignments".into(), str_map_to_json(&self.u_assignments)),
            ("c_assignments".into(), str_map_to_json(&self.c_assignments)),
            ("verdict".into(), Json::str(self.verdict.wire())),
            ("detail".into(), Json::str(&self.detail)),
        ]);
        if let Some(rw) = &self.rational_witness {
            obj.insert("rational_witness".into(), str_map_to_json(rw));
        }
        if let Verdict::Undetermined(reason) = &self.verdict {
            obj.insert("silence_reason".into(), reason.to_json());
        }
        Json::Obj(obj)
    }
}

/// 大域 regular section 存在判定結果（W5: Laurent 多項式環上の付値障害等）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalRegularSectionResult {
    pub checked: bool,
    pub exists: Option<bool>,
    pub obstruction_detail: Option<String>,
    pub silence_reason: Option<SilenceReason>,
}

impl GlobalRegularSectionResult {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([("checked".into(), Json::Bool(self.checked))]);
        if let Some(ex) = self.exists {
            obj.insert("exists".into(), Json::Bool(ex));
        }
        if let Some(det) = &self.obstruction_detail {
            obj.insert("obstruction_detail".into(), Json::str(det));
        }
        if let Some(sr) = &self.silence_reason {
            obj.insert("silence_reason".into(), sr.to_json());
        }
        Json::Obj(obj)
    }
}

/// `shigure_chevalley` の計算結果詳細（G-141 D6–D7 / G-142 G7）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChevalleyOutcomeDetail {
    pub goodness_kind: GoodnessKind,
    pub point_domain: PointDomain,
    pub effective_image_e: Option<ChevalleyRegionSummary>,
    pub p_plus: ChevalleyRegionSummary,
    pub p_minus: ChevalleyRegionSummary,
    pub robust_all_pass: ChevalleyRegionSummary,
    pub all_fail: ChevalleyRegionSummary,
    pub mixed: ChevalleyRegionSummary,
    pub empty_realizations: ChevalleyRegionSummary,
    pub designated_candidate_class: Option<String>,
    pub mixed_witness_pair: Option<MixedWitnessPair>,
    pub rational_fiber_probes: Vec<RationalFiberProbeResult>,
    pub global_regular_section: Option<GlobalRegularSectionResult>,
    pub universal_ring_contrast: Option<UniversalRingStabilityResult>,
}

impl ChevalleyOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("goodness_kind".into(), Json::str(self.goodness_kind.wire())),
            ("point_domain".into(), self.point_domain.wire()),
            ("p_plus".into(), self.p_plus.to_json()),
            ("p_minus".into(), self.p_minus.to_json()),
            ("robust_all_pass".into(), self.robust_all_pass.to_json()),
            ("all_fail".into(), self.all_fail.to_json()),
            ("mixed".into(), self.mixed.to_json()),
            (
                "empty_realizations".into(),
                self.empty_realizations.to_json(),
            ),
            (
                "rational_fiber_probes".into(),
                Json::Arr(
                    self.rational_fiber_probes
                        .iter()
                        .map(RationalFiberProbeResult::to_json)
                        .collect(),
                ),
            ),
        ]);
        if let Some(ee) = &self.effective_image_e {
            obj.insert("effective_image_e".into(), ee.to_json());
        }
        if let Some(cls) = &self.designated_candidate_class {
            obj.insert("designated_candidate_class".into(), Json::str(cls));
        }
        if let Some(mwp) = &self.mixed_witness_pair {
            obj.insert("mixed_witness_pair".into(), mwp.to_json());
        }
        if let Some(grs) = &self.global_regular_section {
            obj.insert("global_regular_section".into(), grs.to_json());
        }
        if let Some(ur) = &self.universal_ring_contrast {
            obj.insert("universal_ring_contrast".into(), ur.to_json());
        }
        Json::Obj(obj)
    }
}

/// 異判定対 $d = (u, u', c) \in \mathcal{D}_R$ と分離添字集合 $D_d$。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistinguishingPairSummary {
    pub u_pass: RealizationWitness,
    pub u_fail: RealizationWitness,
    pub candidate_id: Option<String>,
    pub candidate_assignments: BTreeMap<String, String>,
    pub separating_observations: Vec<String>,
}

impl DistinguishingPairSummary {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("u_pass".into(), self.u_pass.to_json()),
            ("u_fail".into(), self.u_fail.to_json()),
            (
                "candidate_assignments".into(),
                str_map_to_json(&self.candidate_assignments),
            ),
            (
                "separating_observations".into(),
                Json::Arr(self.separating_observations.iter().map(Json::str).collect()),
            ),
        ]);
        if let Some(cid) = &self.candidate_id {
            obj.insert("candidate_id".into(), Json::str(cid));
        }
        Json::Obj(obj)
    }
}

/// 宣言済み観測族が不足する場合（$D_d = \varnothing$）の反証 witness。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InsufficiencyWitness {
    pub pair: DistinguishingPairSummary,
    pub identical_observation_values: BTreeMap<String, Vec<String>>,
}

impl InsufficiencyWitness {
    pub fn to_json(&self) -> Json {
        let vals = self
            .identical_observation_values
            .iter()
            .map(|(obs_id, comps)| {
                (
                    obs_id.clone(),
                    Json::Arr(comps.iter().map(Json::str).collect()),
                )
            })
            .collect();
        Json::obj([
            ("pair", self.pair.to_json()),
            ("identical_observation_values", Json::Obj(vals)),
        ])
    }
}

/// 包含極小集合 $J$ から 1 要素 $j \in J$ を除去すると $J \setminus \{j\}$ が不十分となる証拠対。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RemovalCounterexample {
    pub removed_observation: String,
    pub unseparated_pair: DistinguishingPairSummary,
}

impl RemovalCounterexample {
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("removed_observation", Json::str(&self.removed_observation)),
            ("unseparated_pair", self.unseparated_pair.to_json()),
        ])
    }
}

/// 包含極小な十分観測集合 $J \subseteq I$ と全 1 要素削除反例対。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinimalObservationSet {
    pub observations: Vec<String>,
    pub total_cost: Option<String>,
    pub removal_counterexamples: Vec<RemovalCounterexample>,
}

impl MinimalObservationSet {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            (
                "observations".into(),
                Json::Arr(self.observations.iter().map(Json::str).collect()),
            ),
            (
                "removal_counterexamples".into(),
                Json::Arr(
                    self.removal_counterexamples
                        .iter()
                        .map(RemovalCounterexample::to_json)
                        .collect(),
                ),
            ),
        ]);
        if let Some(cost) = &self.total_cost {
            obj.insert("total_cost".into(), Json::str(cost));
        }
        Json::Obj(obj)
    }
}

/// 応用側費用指定時の全包含極小集合の費用比較要約。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CostRankedObservationSet {
    pub rank: usize,
    pub observations: Vec<String>,
    pub total_cost: String,
}

impl CostRankedObservationSet {
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("rank", Json::Nat(self.rank as u64)),
            (
                "observations",
                Json::Arr(self.observations.iter().map(Json::str).collect()),
            ),
            ("total_cost", Json::str(&self.total_cost)),
        ])
    }
}

/// 元の Law readout に対する adequacy と保存判定 $\chi_E$ に対する adequacy の対比結果（W6 / G5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawReadoutAdequacyComparison {
    pub readout_name: String,
    pub coarse_adequate_for_law_readout: bool,
    pub coarse_adequate_for_decision: bool,
    pub detail: String,
}

impl LawReadoutAdequacyComparison {
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("readout_name", Json::str(&self.readout_name)),
            (
                "coarse_adequate_for_law_readout",
                Json::Bool(self.coarse_adequate_for_law_readout),
            ),
            (
                "coarse_adequate_for_decision",
                Json::Bool(self.coarse_adequate_for_decision),
            ),
            ("detail", Json::str(&self.detail)),
        ])
    }
}

/// `shigure_observations` の計算結果詳細（G-142 G5–G6 / W4・W6）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservationOutcomeDetail {
    pub sufficient: bool,
    pub distinguishing_pair_count: usize,
    pub distinguishing_pairs: Vec<DistinguishingPairSummary>,
    pub insufficiency_witness: Option<InsufficiencyWitness>,
    pub minimal_sufficient_sets: Vec<MinimalObservationSet>,
    pub cost_ranked_sets: Vec<CostRankedObservationSet>,
    pub law_readout_comparison: Option<LawReadoutAdequacyComparison>,
}

impl ObservationOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("sufficient".into(), Json::Bool(self.sufficient)),
            (
                "distinguishing_pair_count".into(),
                Json::Nat(self.distinguishing_pair_count as u64),
            ),
            (
                "distinguishing_pairs".into(),
                Json::Arr(
                    self.distinguishing_pairs
                        .iter()
                        .map(DistinguishingPairSummary::to_json)
                        .collect(),
                ),
            ),
            (
                "minimal_sufficient_sets".into(),
                Json::Arr(
                    self.minimal_sufficient_sets
                        .iter()
                        .map(MinimalObservationSet::to_json)
                        .collect(),
                ),
            ),
            (
                "cost_ranked_sets".into(),
                Json::Arr(
                    self.cost_ranked_sets
                        .iter()
                        .map(CostRankedObservationSet::to_json)
                        .collect(),
                ),
            ),
        ]);
        if let Some(iw) = &self.insufficiency_witness {
            obj.insert("insufficiency_witness".into(), iw.to_json());
        }
        if let Some(lrc) = &self.law_readout_comparison {
            obj.insert("law_readout_comparison".into(), lrc.to_json());
        }
        Json::Obj(obj)
    }
}
