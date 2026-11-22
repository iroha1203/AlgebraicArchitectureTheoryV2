//! SHIGURE Phase 2（図式補完・一段変更経路・合法状態移送）の型付き結果拡張。

use crate::ir::morphism::MorphismDirection;
use crate::ir::result::ReevalCheck;
use archsig_common::canonical::{Json, JsonObject};
use std::collections::BTreeMap;

/// 復元された図式頂点の表示内容。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RestoredVertex {
    pub name: String,
    pub is_fixed: bool,
    pub operations: BTreeMap<String, BTreeMap<String, String>>,
    pub state_laws: BTreeMap<String, Vec<String>>,
}

impl RestoredVertex {
    pub fn to_json(&self) -> Json {
        let ops = self
            .operations
            .iter()
            .map(|(op, updates)| {
                let inner = updates
                    .iter()
                    .map(|(c, e)| (c.clone(), Json::str(e)))
                    .collect();
                (op.clone(), Json::Obj(inner))
            })
            .collect();
        let laws = self
            .state_laws
            .iter()
            .map(|(ph, list)| (ph.clone(), Json::Arr(list.iter().map(Json::str).collect())))
            .collect();
        Json::obj([
            ("name", Json::str(&self.name)),
            ("is_fixed", Json::Bool(self.is_fixed)),
            ("operations", Json::Obj(ops)),
            ("state_laws", Json::Obj(laws)),
        ])
    }
}

/// 復元された図式辺（実状態比較射 h と操作語翻訳 τ）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RestoredEdge {
    pub name: String,
    pub source: String,
    pub target: String,
    pub is_fixed: bool,
    pub state_comparisons: BTreeMap<String, BTreeMap<String, String>>,
    pub word_translation: BTreeMap<String, Vec<String>>,
}

impl RestoredEdge {
    pub fn to_json(&self) -> Json {
        let scs = self
            .state_comparisons
            .iter()
            .map(|(ph, map)| {
                let inner = map.iter().map(|(c, e)| (c.clone(), Json::str(e))).collect();
                (ph.clone(), Json::Obj(inner))
            })
            .collect();
        let wt = self
            .word_translation
            .iter()
            .map(|(op, steps)| (op.clone(), Json::Arr(steps.iter().map(Json::str).collect())))
            .collect();
        Json::obj([
            ("name", Json::str(&self.name)),
            ("source", Json::str(&self.source)),
            ("target", Json::str(&self.target)),
            ("is_fixed", Json::Bool(self.is_fixed)),
            ("state_comparisons", Json::Obj(scs)),
            ("word_translation", Json::Obj(wt)),
        ])
    }
}

/// 補完された図式全体と再評価検算。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RestoredDiagram {
    pub parameter_assignments: BTreeMap<String, String>,
    pub free_parameters: Vec<String>,
    pub vertices: Vec<RestoredVertex>,
    pub edges: Vec<RestoredEdge>,
    pub reeval: ReevalCheck,
}

impl RestoredDiagram {
    pub fn to_json(&self) -> Json {
        let assigns = self
            .parameter_assignments
            .iter()
            .map(|(k, v)| (k.clone(), Json::str(v)))
            .collect();
        Json::obj([
            ("parameter_assignments", Json::Obj(assigns)),
            (
                "free_parameters",
                Json::Arr(self.free_parameters.iter().map(Json::str).collect()),
            ),
            (
                "vertices",
                Json::Arr(self.vertices.iter().map(RestoredVertex::to_json).collect()),
            ),
            (
                "edges",
                Json::Arr(self.edges.iter().map(RestoredEdge::to_json).collect()),
            ),
            ("reevaluation", self.reeval.to_json()),
        ])
    }
}

/// `shigure_diagram` の計算結果詳細。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagramOutcomeDetail {
    pub direction: MorphismDirection,
    pub commutativity_residuals: BTreeMap<String, Vec<String>>,
    pub structural_mismatches: BTreeMap<String, String>,
    pub restored_diagram: Option<RestoredDiagram>,
}

impl DiagramOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let res = self
            .commutativity_residuals
            .iter()
            .map(|(rel, polys)| {
                (
                    rel.clone(),
                    Json::Arr(polys.iter().map(Json::str).collect()),
                )
            })
            .collect();
        let mut obj = JsonObject::from([
            ("direction".into(), Json::str(self.direction.wire())),
            ("commutativity_residuals".into(), Json::Obj(res)),
        ]);
        if !self.structural_mismatches.is_empty() {
            let mm = self
                .structural_mismatches
                .iter()
                .map(|(k, v)| (k.clone(), Json::str(v)))
                .collect();
            obj.insert("structural_mismatches".into(), Json::Obj(mm));
        }
        if let Some(rd) = &self.restored_diagram {
            obj.insert("restored_diagram".into(), rd.to_json());
        }
        Json::Obj(obj)
    }
}

/// 経路出力の種別区別（P5.2: 固定 protocol 間変更経路 vs 拡大 protocol 内実行経路）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathOutcomeKind {
    FixedProtocolChangePath,
    EnlargedProtocolExecutionPath,
}

impl PathOutcomeKind {
    pub fn wire(self) -> &'static str {
        match self {
            PathOutcomeKind::FixedProtocolChangePath => "fixed_protocol_change_path",
            PathOutcomeKind::EnlargedProtocolExecutionPath => "enlarged_protocol_execution_path",
        }
    }
}

/// 復元された 1 本の合法変更／実行経路。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RestoredPath {
    pub steps: Vec<String>,
    pub intermediate_vertices: Vec<String>,
    pub parameter_assignments: BTreeMap<String, String>,
    pub free_parameters: Vec<String>,
    pub step_states: Vec<BTreeMap<String, String>>,
    pub composite_state_comparisons: BTreeMap<String, BTreeMap<String, String>>,
    pub composite_word_translation: BTreeMap<String, Vec<String>>,
    pub composite_is_one_step: Option<bool>,
    pub reeval: ReevalCheck,
}

impl RestoredPath {
    pub fn to_json(&self) -> Json {
        let assigns = self
            .parameter_assignments
            .iter()
            .map(|(k, v)| (k.clone(), Json::str(v)))
            .collect();
        let states = self
            .step_states
            .iter()
            .map(|m| Json::Obj(m.iter().map(|(k, v)| (k.clone(), Json::str(v))).collect()))
            .collect();
        let scs = self
            .composite_state_comparisons
            .iter()
            .map(|(ph, m)| {
                (
                    ph.clone(),
                    Json::Obj(m.iter().map(|(k, v)| (k.clone(), Json::str(v))).collect()),
                )
            })
            .collect();
        let wt = self
            .composite_word_translation
            .iter()
            .map(|(op, ws)| (op.clone(), Json::Arr(ws.iter().map(Json::str).collect())))
            .collect();
        let mut obj = JsonObject::from([
            (
                "steps".into(),
                Json::Arr(self.steps.iter().map(Json::str).collect()),
            ),
            (
                "intermediate_vertices".into(),
                Json::Arr(self.intermediate_vertices.iter().map(Json::str).collect()),
            ),
            ("parameter_assignments".into(), Json::Obj(assigns)),
            (
                "free_parameters".into(),
                Json::Arr(self.free_parameters.iter().map(Json::str).collect()),
            ),
            ("step_states".into(), Json::Arr(states)),
            ("composite_state_comparisons".into(), Json::Obj(scs)),
            ("composite_word_translation".into(), Json::Obj(wt)),
            ("reevaluation".into(), self.reeval.to_json()),
        ]);
        if let Some(one_step) = self.composite_is_one_step {
            obj.insert("composite_is_one_step".into(), Json::Bool(one_step));
        }
        Json::Obj(obj)
    }
}

/// 経路探索で中間段・評価条件・細分化一致に失敗して拒否された候補（P5.1 / P5.2 等）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RejectedPathCandidate {
    pub steps: Vec<String>,
    pub failed_step: usize,
    pub intermediate_state: BTreeMap<String, String>,
    pub residuals: Vec<String>,
    pub reason: String,
}

impl RejectedPathCandidate {
    pub fn to_json(&self) -> Json {
        let state = self
            .intermediate_state
            .iter()
            .map(|(k, v)| (k.clone(), Json::str(v)))
            .collect();
        Json::obj([
            (
                "steps",
                Json::Arr(self.steps.iter().map(Json::str).collect()),
            ),
            ("failed_step", Json::Nat(self.failed_step as u64)),
            ("intermediate_state", Json::Obj(state)),
            (
                "residuals",
                Json::Arr(self.residuals.iter().map(Json::str).collect()),
            ),
            ("reason", Json::str(&self.reason)),
        ])
    }
}

/// `shigure_path` の計算結果詳細。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathOutcomeDetail {
    pub path_kind: PathOutcomeKind,
    pub direction: MorphismDirection,
    pub query_mode: String,
    pub length: Option<usize>,
    pub protocol_preservation_verified: Option<bool>,
    pub valid_paths: Vec<RestoredPath>,
    pub rejected_candidates: Vec<RejectedPathCandidate>,
}

impl PathOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("path_kind".into(), Json::str(self.path_kind.wire())),
            ("direction".into(), Json::str(self.direction.wire())),
            ("query_mode".into(), Json::str(&self.query_mode)),
            (
                "valid_paths".into(),
                Json::Arr(self.valid_paths.iter().map(RestoredPath::to_json).collect()),
            ),
            (
                "rejected_candidates".into(),
                Json::Arr(
                    self.rejected_candidates
                        .iter()
                        .map(RejectedPathCandidate::to_json)
                        .collect(),
                ),
            ),
        ]);
        if let Some(n) = self.length {
            obj.insert("length".into(), Json::Nat(n as u64));
        }
        if let Some(verified) = self.protocol_preservation_verified {
            obj.insert(
                "protocol_preservation_verified".into(),
                Json::Bool(verified),
            );
        }
        Json::Obj(obj)
    }
}

/// 2 段以上の移送合成における定義域 $D_{0k}$ と開始域 $D_0$ の関係（G-140 G3）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DomainRelation {
    FullIsomorphic,
    ProperSubdomain,
    Empty,
}

impl DomainRelation {
    pub fn wire(self) -> &'static str {
        match self {
            DomainRelation::FullIsomorphic => "full_isomorphic",
            DomainRelation::ProperSubdomain => "proper_subdomain",
            DomainRelation::Empty => "empty",
        }
    }
}

/// 各移送段の残差・失敗診断。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransferStepDiagnostic {
    pub step_name: String,
    pub source_phase: String,
    pub target_phase: String,
    pub target_law_residuals: Vec<String>,
    pub lift_residuals: Vec<String>,
}

impl TransferStepDiagnostic {
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("step_name", Json::str(&self.step_name)),
            ("source_phase", Json::str(&self.source_phase)),
            ("target_phase", Json::str(&self.target_phase)),
            (
                "target_law_residuals",
                Json::Arr(self.target_law_residuals.iter().map(Json::str).collect()),
            ),
            (
                "lift_residuals",
                Json::Arr(self.lift_residuals.iter().map(Json::str).collect()),
            ),
        ])
    }
}

/// 移送後の共通操作語定義域 $D_w$ 上での観測保存検算結果（G-140 G2）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordPreservationCheck {
    pub word_name: String,
    pub new_word: Vec<String>,
    pub translated_old_word: Vec<String>,
    pub common_domain_equations: Vec<String>,
    pub domain_nonempty: bool,
    pub state_commutativity_matched: bool,
    pub observation_preserved: bool,
    pub detail: String,
}

impl WordPreservationCheck {
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("word_name", Json::str(&self.word_name)),
            (
                "new_word",
                Json::Arr(self.new_word.iter().map(Json::str).collect()),
            ),
            (
                "translated_old_word",
                Json::Arr(self.translated_old_word.iter().map(Json::str).collect()),
            ),
            (
                "common_domain_equations",
                Json::Arr(self.common_domain_equations.iter().map(Json::str).collect()),
            ),
            ("domain_nonempty", Json::Bool(self.domain_nonempty)),
            (
                "state_commutativity_matched",
                Json::Bool(self.state_commutativity_matched),
            ),
            (
                "observation_preserved",
                Json::Bool(self.observation_preserved),
            ),
            ("detail", Json::str(&self.detail)),
        ])
    }
}

/// 旧語 $v$ の新側への lift 存在探索結果（G-140 G2 独立存在条件）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OldWordLiftResult {
    pub check_name: String,
    pub target_old_word: Vec<String>,
    pub lift_found: bool,
    pub lifted_new_word: Option<Vec<String>>,
    pub common_domain_equations: Vec<String>,
    pub detail: String,
}

impl OldWordLiftResult {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("check_name".into(), Json::str(&self.check_name)),
            (
                "target_old_word".into(),
                Json::Arr(self.target_old_word.iter().map(Json::str).collect()),
            ),
            ("lift_found".into(), Json::Bool(self.lift_found)),
            (
                "common_domain_equations".into(),
                Json::Arr(self.common_domain_equations.iter().map(Json::str).collect()),
            ),
            ("detail".into(), Json::str(&self.detail)),
        ]);
        if let Some(w) = &self.lifted_new_word {
            obj.insert(
                "lifted_new_word".into(),
                Json::Arr(w.iter().map(Json::str).collect()),
            );
        }
        Json::Obj(obj)
    }
}

/// 復元された状態移送写像 $m$ と合成結果・再評価検算。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RestoredTransfer {
    pub parameter_assignments: BTreeMap<String, String>,
    pub free_parameters: Vec<String>,
    pub step_lifts: Vec<(String, BTreeMap<String, String>)>,
    pub composed_lift: BTreeMap<String, String>,
    pub composed_state_comparison: BTreeMap<String, BTreeMap<String, String>>,
    pub composed_word_translation: BTreeMap<String, Vec<String>>,
    pub reeval: ReevalCheck,
}

impl RestoredTransfer {
    pub fn to_json(&self) -> Json {
        let assigns = self
            .parameter_assignments
            .iter()
            .map(|(k, v)| (k.clone(), Json::str(v)))
            .collect();
        let step_lifts = self
            .step_lifts
            .iter()
            .map(|(name, m)| {
                Json::obj([
                    ("step_name", Json::str(name)),
                    (
                        "map",
                        Json::Obj(m.iter().map(|(k, v)| (k.clone(), Json::str(v))).collect()),
                    ),
                ])
            })
            .collect();
        let comp_lift = self
            .composed_lift
            .iter()
            .map(|(k, v)| (k.clone(), Json::str(v)))
            .collect();
        let comp_sc = self
            .composed_state_comparison
            .iter()
            .map(|(ph, m)| {
                (
                    ph.clone(),
                    Json::Obj(m.iter().map(|(k, v)| (k.clone(), Json::str(v))).collect()),
                )
            })
            .collect();
        let comp_wt = self
            .composed_word_translation
            .iter()
            .map(|(op, ws)| (op.clone(), Json::Arr(ws.iter().map(Json::str).collect())))
            .collect();
        Json::obj([
            ("parameter_assignments", Json::Obj(assigns)),
            (
                "free_parameters",
                Json::Arr(self.free_parameters.iter().map(Json::str).collect()),
            ),
            ("step_lifts", Json::Arr(step_lifts)),
            ("composed_lift", Json::Obj(comp_lift)),
            ("composed_state_comparison", Json::Obj(comp_sc)),
            ("composed_word_translation", Json::Obj(comp_wt)),
            ("reevaluation", self.reeval.to_json()),
        ])
    }
}

/// `shigure_transfer` の計算結果詳細。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransferOutcomeDetail {
    pub domain_relation: DomainRelation,
    pub composed_domain_equations: Vec<String>,
    pub step_diagnostics: Vec<TransferStepDiagnostic>,
    pub restored_transfer: Option<RestoredTransfer>,
    pub word_checks: Vec<WordPreservationCheck>,
    pub old_word_lifts: Vec<OldWordLiftResult>,
}

impl TransferOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            (
                "domain_relation".into(),
                Json::str(self.domain_relation.wire()),
            ),
            (
                "composed_domain_equations".into(),
                Json::Arr(
                    self.composed_domain_equations
                        .iter()
                        .map(Json::str)
                        .collect(),
                ),
            ),
            (
                "step_diagnostics".into(),
                Json::Arr(
                    self.step_diagnostics
                        .iter()
                        .map(TransferStepDiagnostic::to_json)
                        .collect(),
                ),
            ),
            (
                "word_checks".into(),
                Json::Arr(
                    self.word_checks
                        .iter()
                        .map(WordPreservationCheck::to_json)
                        .collect(),
                ),
            ),
            (
                "old_word_lifts".into(),
                Json::Arr(
                    self.old_word_lifts
                        .iter()
                        .map(OldWordLiftResult::to_json)
                        .collect(),
                ),
            ),
        ]);
        if let Some(rt) = &self.restored_transfer {
            obj.insert("restored_transfer".into(), rt.to_json());
        }
        Json::Obj(obj)
    }
}
