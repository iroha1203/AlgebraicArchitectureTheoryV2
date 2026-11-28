//! SHIGURE 計算結果・適用条件検査・沈黙理由（SilenceReason）・復元と再評価検算型。

use crate::ir::change::PointDomain;
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result_ext::{DiagramOutcomeDetail, PathOutcomeDetail, TransferOutcomeDetail};
use crate::ir::result_phase3::{
    ChevalleyOutcomeDetail, ObservationOutcomeDetail, RobustnessOutcomeDetail,
};
use crate::ir::result_phase4::{
    ArtinOutcomeDetail, AtlasOutcomeDetail, DiagnosticsOutcomeDetail, LiftOutcomeDetail,
};
use crate::ir::result_phase5_obs::{OccurrenceOutcomeDetail, PartialOutcomeDetail};
use crate::ir::result_phase5_rev::{MultisourceOutcomeDetail, RevisionOutcomeDetail};
use crate::ir::term::CoeffDomain;
use archsig_common::canonical::{Json, JsonObject};
use std::collections::BTreeMap;

/// 紙上証明条項ごとの適用条件検査の記録（R3.2 / Tool guideline 数学対応規律）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ApplicabilityCheck {
    pub condition: String,
    pub clause: MathClause,
    pub satisfied: bool,
    pub detail: Option<String>,
}

impl ApplicabilityCheck {
    pub fn passed(condition: impl Into<String>, clause: MathClause) -> Self {
        Self {
            condition: condition.into(),
            clause,
            satisfied: true,
            detail: None,
        }
    }

    pub fn failed(
        condition: impl Into<String>,
        clause: MathClause,
        detail: impl Into<String>,
    ) -> Self {
        Self {
            condition: condition.into(),
            clause,
            satisfied: false,
            detail: Some(detail.into()),
        }
    }

    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("condition".into(), Json::str(&self.condition)),
            ("clause".into(), Json::str(self.clause.stable_id())),
            ("satisfied".into(), Json::Bool(self.satisfied)),
        ]);
        if let Some(detail) = &self.detail {
            obj.insert("detail".into(), Json::str(detail));
        }
        Json::Obj(obj)
    }
}

/// 判断不能（沈黙: `undetermined`）の明示理由（R3.3 / AC5(b)）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SilenceReason {
    /// 未観測の原始値への依存が残る。
    UnobservedDependency { slots: Vec<String> },
    /// 代数閉包では非空だが、Q 点・Z 点存在の一般非線形判定は適用域外（例: `x^2 + 1 = 0`）。
    NonLinearRationalOrIntegerExistence {
        point_domain: PointDomain,
        detail: String,
    },
    /// D8 型の無限表示など、有限還元できない入力。
    InfinitePresentationNotFinitelyReducible { detail: String },
    /// 適用対象外の係数環・演算。
    UnsupportedCoeffRing { domain: CoeffDomain, detail: String },
    /// 商環上の ideal 所属判定の適用域外（ambient 零へ暗黙に強めない）。
    QuotientIdealOutOfScope { detail: String },
    /// 相互作用解析（F10–F12）において開条件が本質的に絡むため閉条件へ丸めない。
    OpenConditionInInteraction { detail: String },
    /// 無界の経路長探索や無界の旧語 lift 探索など有限還元不能な無界探索。
    UnboundedSearchOutOfScope { detail: String },
    /// 構成可能集合・D6 射影層別の分岐／S-pair 上限超過または適用域外。
    ConstructibleStratificationOutOfScope { detail: String },
    /// 有限列挙・観測候補数・部分集合探索上限超過。
    FiniteEnumerationOutOfScope { detail: String },
    /// 全係数移送安定性 $\mathcal{R}(R)$ 検査が適用域外（例: 存在型・未対応非線形）。
    UniversalRingOutOfScope { detail: String },
    /// 非 Noetherian 無限表示（例: G-141 H7 `T_i = T_{i+1}^2`）により全 Artin 試験から局所同型を主張不能。
    NonNoetherianInfinitePresentation { detail: String },
    /// 平方零条件 `M^2 = 0` または拡大準同型条件の未充足。
    SquareZeroConditionViolated { detail: String },
    /// syzygy 生成族計算の適用域外・上限超過（未検証 Z 族や S-pair 上限超過）。
    SyzygyOutOfScope { detail: String },
    /// Artin 試験の探索次数・次元上限超過または適用域外。
    ArtinOrderOutOfScope { detail: String },
    /// 診断層 partition 層別の上限超過または適用域外。
    DiagnosticsStratificationOutOfScope { detail: String },
    /// 非連結グラフまたは単純グラフ適用条件外。
    DisconnectedGraphOutOfScope { detail: String },
    /// Phase 5: 有限表でもアフィン表示（Q/F_p/Z）でもない非対応補完クラス。
    UnsupportedCompletionClass { detail: String },
    /// Phase 5: 共通部分 $P_0$ から修復作用素 $M$ が一意に定まらない。
    OperatorNotUniquelyDetermined { detail: String },
    /// Phase 5: 作用素改訂時に既存 SNF 分解の再利用が強制指定された。
    OperatorRevisionReuseRejected { detail: String },
    /// BigInt ビット長・多項式項数・計算ステップ等のリソース上限超過。
    ResourceLimitExceeded {
        limit_name: String,
        limit: u64,
        observed: u64,
        detail: String,
    },
    /// その他の適用条件未充足。
    ApplicabilityConditionNotMet { condition: String, detail: String },
}

impl SilenceReason {
    /// `AlgebraError` を `SilenceReason` へ変換し、`ResourceLimitExceeded` を常に保持する。
    pub fn from_algebra_with(
        err: crate::algebra::poly::AlgebraError,
        fallback: impl FnOnce(crate::algebra::poly::AlgebraError) -> Self,
    ) -> Self {
        match err {
            crate::algebra::poly::AlgebraError::ResourceLimitExceeded {
                limit_name,
                limit,
                observed,
                detail,
            } => Self::ResourceLimitExceeded {
                limit_name,
                limit,
                observed,
                detail,
            },
            other => fallback(other),
        }
    }

    pub fn code(&self) -> &'static str {
        match self {
            SilenceReason::UnobservedDependency { .. } => "unobserved_dependency",
            SilenceReason::NonLinearRationalOrIntegerExistence { .. } => {
                "nonlinear_point_existence_out_of_scope"
            }
            SilenceReason::InfinitePresentationNotFinitelyReducible { .. } => {
                "infinite_presentation_not_finitely_reducible"
            }
            SilenceReason::UnsupportedCoeffRing { .. } => "unsupported_coeff_ring",
            SilenceReason::QuotientIdealOutOfScope { .. } => "quotient_ideal_out_of_scope",
            SilenceReason::OpenConditionInInteraction { .. } => "open_condition_in_interaction",
            SilenceReason::UnboundedSearchOutOfScope { .. } => "unbounded_search_out_of_scope",
            SilenceReason::ConstructibleStratificationOutOfScope { .. } => {
                "constructible_stratification_out_of_scope"
            }
            SilenceReason::FiniteEnumerationOutOfScope { .. } => "finite_enumeration_out_of_scope",
            SilenceReason::UniversalRingOutOfScope { .. } => "universal_ring_out_of_scope",
            SilenceReason::NonNoetherianInfinitePresentation { .. } => {
                "non_noetherian_infinite_presentation"
            }
            SilenceReason::SquareZeroConditionViolated { .. } => "square_zero_condition_violated",
            SilenceReason::SyzygyOutOfScope { .. } => "syzygy_out_of_scope",
            SilenceReason::ArtinOrderOutOfScope { .. } => "artin_order_out_of_scope",
            SilenceReason::DiagnosticsStratificationOutOfScope { .. } => {
                "diagnostics_stratification_out_of_scope"
            }
            SilenceReason::DisconnectedGraphOutOfScope { .. } => "disconnected_graph_out_of_scope",
            SilenceReason::UnsupportedCompletionClass { .. } => "unsupported_completion_class",
            SilenceReason::OperatorNotUniquelyDetermined { .. } => {
                "operator_not_uniquely_determined"
            }
            SilenceReason::OperatorRevisionReuseRejected { .. } => {
                "operator_revision_reuse_rejected"
            }
            SilenceReason::ResourceLimitExceeded { .. } => "resource_limit_exceeded",
            SilenceReason::ApplicabilityConditionNotMet { .. } => "applicability_condition_not_met",
        }
    }

    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([("code".into(), Json::str(self.code()))]);
        match self {
            SilenceReason::UnobservedDependency { slots } => {
                obj.insert(
                    "missing_slots".into(),
                    Json::Arr(slots.iter().map(Json::str).collect()),
                );
            }
            SilenceReason::NonLinearRationalOrIntegerExistence {
                point_domain,
                detail,
            } => {
                obj.insert("point_domain".into(), point_domain.wire());
                obj.insert("detail".into(), Json::str(detail));
            }
            SilenceReason::InfinitePresentationNotFinitelyReducible { detail }
            | SilenceReason::QuotientIdealOutOfScope { detail }
            | SilenceReason::OpenConditionInInteraction { detail }
            | SilenceReason::UnboundedSearchOutOfScope { detail }
            | SilenceReason::ConstructibleStratificationOutOfScope { detail }
            | SilenceReason::FiniteEnumerationOutOfScope { detail }
            | SilenceReason::UniversalRingOutOfScope { detail }
            | SilenceReason::NonNoetherianInfinitePresentation { detail }
            | SilenceReason::SquareZeroConditionViolated { detail }
            | SilenceReason::SyzygyOutOfScope { detail }
            | SilenceReason::ArtinOrderOutOfScope { detail }
            | SilenceReason::DiagnosticsStratificationOutOfScope { detail }
            | SilenceReason::DisconnectedGraphOutOfScope { detail }
            | SilenceReason::UnsupportedCompletionClass { detail }
            | SilenceReason::OperatorNotUniquelyDetermined { detail }
            | SilenceReason::OperatorRevisionReuseRejected { detail } => {
                obj.insert("detail".into(), Json::str(detail));
            }
            SilenceReason::ResourceLimitExceeded {
                limit_name,
                limit,
                observed,
                detail,
            } => {
                obj.insert("limit_name".into(), Json::str(limit_name));
                obj.insert("limit".into(), Json::Nat(*limit));
                obj.insert("observed".into(), Json::Nat(*observed));
                obj.insert("detail".into(), Json::str(detail));
            }
            SilenceReason::UnsupportedCoeffRing { domain, detail } => {
                obj.insert("coeff_domain".into(), domain.wire());
                obj.insert("detail".into(), Json::str(detail));
            }
            SilenceReason::ApplicabilityConditionNotMet { condition, detail } => {
                obj.insert("condition".into(), Json::str(condition));
                obj.insert("detail".into(), Json::str(detail));
            }
        }
        Json::Obj(obj)
    }
}

/// 計算の最終状態。`Undetermined` はエラーではなく正常出力の一種（沈黙）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    Established,
    Refuted,
    Undetermined(SilenceReason),
}

impl Verdict {
    pub fn wire(&self) -> &'static str {
        match self {
            Verdict::Established => "established",
            Verdict::Refuted => "refuted",
            Verdict::Undetermined(_) => "undetermined",
        }
    }
}

/// 空性証明 witness: `1 = sum_i cofactor_i * generator_i`（G-141 D5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EmptyWitness {
    pub generators: Vec<String>,
    pub cofactors: Vec<String>,
    /// 展開した線形結合が定数 `1` と一致することの検算結果。
    pub verified: bool,
}

impl EmptyWitness {
    pub fn to_json(&self) -> Json {
        Json::obj([
            (
                "generators",
                Json::Arr(self.generators.iter().map(Json::str).collect()),
            ),
            (
                "cofactors",
                Json::Arr(self.cofactors.iter().map(Json::str).collect()),
            ),
            ("verified", Json::Bool(self.verified)),
        ])
    }
}

/// 復元した操作式・状態表示・状態比較 h・語翻訳 τ の元式への再評価検算。
/// 実コードへの反映・変更後再観測の確認とは明確に区別する（R3.3）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReevalCheck {
    pub checked: bool,
    pub matched: bool,
    pub detail: String,
}

impl ReevalCheck {
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("checked", Json::Bool(self.checked)),
            ("matched", Json::Bool(self.matched)),
            ("detail", Json::str(&self.detail)),
            ("scope", Json::str("mathematical_model_reevaluation")),
        ])
    }
}

/// 解から復元した具体的な操作式・状態 Law・h・τ。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RestoredArtifact {
    pub parameter_assignments: BTreeMap<String, String>,
    pub free_parameters: Vec<String>,
    pub operations: BTreeMap<String, BTreeMap<String, String>>,
    pub state_laws: BTreeMap<String, Vec<String>>,
    pub state_comparisons: BTreeMap<String, BTreeMap<String, String>>,
    pub word_translation: BTreeMap<String, Vec<String>>,
    pub reeval: ReevalCheck,
}

impl RestoredArtifact {
    pub fn to_json(&self) -> Json {
        let assignments = self
            .parameter_assignments
            .iter()
            .map(|(k, v)| (k.clone(), Json::str(v)))
            .collect();
        let ops = self
            .operations
            .iter()
            .map(|(op, updates)| {
                let map = updates
                    .iter()
                    .map(|(c, expr)| (c.clone(), Json::str(expr)))
                    .collect();
                (op.clone(), Json::Obj(map))
            })
            .collect();
        let laws = self
            .state_laws
            .iter()
            .map(|(phase, list)| {
                (
                    phase.clone(),
                    Json::Arr(list.iter().map(Json::str).collect()),
                )
            })
            .collect();
        let comparisons = self
            .state_comparisons
            .iter()
            .map(|(phase, map)| {
                let inner = map
                    .iter()
                    .map(|(c, expr)| (c.clone(), Json::str(expr)))
                    .collect();
                (phase.clone(), Json::Obj(inner))
            })
            .collect();
        let translations = self
            .word_translation
            .iter()
            .map(|(op, word)| (op.clone(), Json::Arr(word.iter().map(Json::str).collect())))
            .collect();
        Json::obj([
            ("parameter_assignments", Json::Obj(assignments)),
            (
                "free_parameters",
                Json::Arr(self.free_parameters.iter().map(Json::str).collect()),
            ),
            ("operations", Json::Obj(ops)),
            ("state_laws", Json::Obj(laws)),
            ("state_comparisons", Json::Obj(comparisons)),
            ("word_translation", Json::Obj(translations)),
            ("reevaluation", self.reeval.to_json()),
        ])
    }
}

/// 相互作用解析（G-141 F10–F12）の結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InteractionSummary {
    /// 極小不成立部分族の最小サイズ（不成立なし＝残差 ideal 零なら `None`、
    /// 定数残差 `1 in J` で空集合不成立なら `Some(0)`、`t^m` なら `Some(1)`、`mu*delta` なら `Some(2)`）。
    pub min_interacting_variables: Option<usize>,
    /// G-141 F11 の最大零化部分集合サイズ r（`forall |S| <= r, i_S^* J = 0` を満たす最大 r）。
    /// 定数残差（空集合でも不成立）なら `None`、`t^m` なら `Some(0)`、`mu*delta` なら `Some(1)`、
    /// 残差 ideal 零なら `Some(parameters.len())`。
    pub max_vanishing_subset_size: Option<usize>,
    /// 多項式恒等式として不成立となる包含極小の部分変数族。
    pub minimal_failing_subsets: Vec<Vec<String>>,
    /// 自由パラメータ全体。
    pub parameters: Vec<String>,
}

impl InteractionSummary {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            (
                "minimal_failing_subsets".into(),
                Json::Arr(
                    self.minimal_failing_subsets
                        .iter()
                        .map(|subset| Json::Arr(subset.iter().map(Json::str).collect()))
                        .collect(),
                ),
            ),
            (
                "parameters".into(),
                Json::Arr(self.parameters.iter().map(Json::str).collect()),
            ),
        ]);
        if let Some(min_vars) = self.min_interacting_variables {
            obj.insert(
                "min_interacting_variables".into(),
                Json::Nat(min_vars as u64),
            );
        }
        if let Some(max_r) = self.max_vanishing_subset_size {
            obj.insert("max_vanishing_subset_size".into(), Json::Nat(max_r as u64));
        }
        Json::Obj(obj)
    }
}

/// SHIGURE 計算の共通出力構造。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOutcome {
    pub verdict: Verdict,
    pub coeff_domain: CoeffDomain,
    pub point_domain: PointDomain,
    pub applicability: Vec<ApplicabilityCheck>,
    pub provenance: Provenance,
    pub residual_ideal: Vec<String>,
    pub empty_witness: Option<EmptyWitness>,
    pub restored: Option<RestoredArtifact>,
    pub interaction: Option<InteractionSummary>,
    pub diagram: Option<DiagramOutcomeDetail>,
    pub path: Option<PathOutcomeDetail>,
    pub transfer: Option<TransferOutcomeDetail>,
    pub robustness: Option<RobustnessOutcomeDetail>,
    pub chevalley: Option<ChevalleyOutcomeDetail>,
    pub observations: Option<ObservationOutcomeDetail>,
    pub lift: Option<LiftOutcomeDetail>,
    pub artin: Option<ArtinOutcomeDetail>,
    pub diagnostics: Option<DiagnosticsOutcomeDetail>,
    pub atlas: Option<AtlasOutcomeDetail>,
    pub occurrence: Option<OccurrenceOutcomeDetail>,
    pub partial: Option<PartialOutcomeDetail>,
    pub revision: Option<RevisionOutcomeDetail>,
    pub multisource: Option<MultisourceOutcomeDetail>,
}

impl ShigureOutcome {
    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("verdict".into(), Json::str(self.verdict.wire())),
            ("coeff_domain".into(), self.coeff_domain.wire()),
            ("point_domain".into(), self.point_domain.wire()),
            (
                "applicability".into(),
                Json::Arr(
                    self.applicability
                        .iter()
                        .map(ApplicabilityCheck::to_json)
                        .collect(),
                ),
            ),
            ("provenance".into(), self.provenance.to_json()),
            (
                "residual_ideal".into(),
                Json::Arr(self.residual_ideal.iter().map(Json::str).collect()),
            ),
            ("result_kind".into(), Json::str("mathematical_computation")),
        ]);
        if let Verdict::Undetermined(reason) = &self.verdict {
            obj.insert("silence_reason".into(), reason.to_json());
        }
        if let Some(witness) = &self.empty_witness {
            obj.insert("empty_witness".into(), witness.to_json());
        }
        if let Some(restored) = &self.restored {
            obj.insert("restored".into(), restored.to_json());
        }
        if let Some(interaction) = &self.interaction {
            obj.insert("interaction".into(), interaction.to_json());
        }
        if let Some(diagram) = &self.diagram {
            obj.insert("diagram".into(), diagram.to_json());
        }
        if let Some(path) = &self.path {
            obj.insert("path".into(), path.to_json());
        }
        if let Some(transfer) = &self.transfer {
            obj.insert("transfer".into(), transfer.to_json());
        }
        if let Some(robustness) = &self.robustness {
            obj.insert("robustness".into(), robustness.to_json());
        }
        if let Some(chevalley) = &self.chevalley {
            obj.insert("chevalley".into(), chevalley.to_json());
        }
        if let Some(observations) = &self.observations {
            obj.insert("observations".into(), observations.to_json());
        }
        if let Some(lift) = &self.lift {
            obj.insert("lift".into(), lift.to_json());
        }
        if let Some(artin) = &self.artin {
            obj.insert("artin".into(), artin.to_json());
        }
        if let Some(diagnostics) = &self.diagnostics {
            obj.insert("diagnostics".into(), diagnostics.to_json());
        }
        if let Some(atlas) = &self.atlas {
            obj.insert("atlas".into(), atlas.to_json());
        }
        if let Some(occurrence) = &self.occurrence {
            obj.insert("occurrence".into(), occurrence.to_json());
        }
        if let Some(partial) = &self.partial {
            obj.insert("partial".into(), partial.to_json());
        }
        if let Some(revision) = &self.revision {
            obj.insert("revision".into(), revision.to_json());
        }
        if let Some(multisource) = &self.multisource {
            obj.insert("multisource".into(), multisource.to_json());
        }
        Json::Obj(obj)
    }
}
