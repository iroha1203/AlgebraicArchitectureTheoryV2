//! SHIGURE 中心中間表現（IR）。
//!
//! - `provenance`: 由来種別（静的解析・実行観測・LLM 読解候補・人間採用）と紙上証明条項参照
//! - `term`: 係数域（Z / Q / F_p）・スカラー定数・型付き affine / 多項式構文木
//! - `presentation`: 原始表示 IR・守る意味 Law と編集可能な表示 Law・状態比較 h・語翻訳 τ
//! - `change`: 許容変換仕様 H と評価条件 P（V(f), D(g), PointDomain）
//! - `morphism`: 射の向き（状態比較射と時間順）の型レベル統一と合成
//! - `diagram`: 固定図式の全補完 IR (`DiagramSpec` / `CheckedDiagramTask`)
//! - `path`: 一段変更経路・細分化 IR (`PathSpec` / `CheckedPathTask`)
//! - `transfer`: 合法状態移送・共通操作語保存・合成 IR (`TransferSpec` / `CheckedTransferTask`)
//! - `family`: 複数解釈族・共有規則候補・$E_{\mathrm{dir}}$/$E_{\mathrm{exists}}$・reading 比較 IR (`CheckedFamilySpec`)
//! - `robustness`: 頑健判定（`CheckedRobustnessTask`）と Chevalley 四分類（`CheckedChevalleyTask`）
//! - `observation`: 追加観測 kernel 条件と全包含極小観測（`CheckedObservationTask`）
//! - `result` / `result_ext` / `result_phase3`: 適用条件検査・沈黙理由・空性 witness・復元と再評価検算・出力 JSON
//! - `validate`: 型・参照・係数域・意味 Law 保護・未観測検出の検証済み構築経路

pub mod change;
pub mod diagram;
pub mod family;
pub mod morphism;
pub mod observation;
pub mod path;
pub mod presentation;
pub mod provenance;
pub mod result;
pub mod result_ext;
pub mod result_phase3;
pub mod robustness;
pub mod term;
pub mod transfer;
pub mod validate;
mod validate_change;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_phase2;
#[cfg(test)]
mod tests_phase2_extra;
#[cfg(test)]
mod tests_phase3;

pub use change::{
    ChangeSpec, EditableTarget, EvalCondition, FixedTarget, NamedPoly, ParamDecl, PointDomain,
};
pub use diagram::{CheckedDiagramTask, DiagramEdge, DiagramRelation, DiagramSpec, DiagramVertex};
pub use family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, CheckedFamilySpec, FamilySpec,
    GoodnessKind, GoodnessSpec, PreservationGoodnessSource, RawSequenceCheck,
    ReadingComparisonSpec, RealizationFamilySpec, RealizationMember, RealizationSpace,
};
pub use morphism::{
    MorphismDirection, StateMorphism, TimeStepMorphism, compose_state_order, compose_time_order,
    identity_state_morphism,
};
pub use observation::{
    CandidateObservationDecl, CheckedObservationTask, LawReadoutSpec, ObservationTaskSpec,
};
pub use path::{
    CheckedPathTask, ModelEndpoint, OneStepRule, PathKind, PathQueryMode, PathSpec,
    ProtocolExecutionSpec,
};
pub use presentation::{
    ComparisonPair, CoordDecl, CoordValue, LawKind, ObservationDecl, OperationDecl, PhaseDecl,
    Presentation, SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord,
    WordTranslation,
};
pub use provenance::{MathClause, OriginKind, Provenance, SourceRef};
pub use result::{
    ApplicabilityCheck, EmptyWitness, InteractionSummary, ReevalCheck, RestoredArtifact,
    ShigureOutcome, SilenceReason, Verdict,
};
pub use result_ext::{
    DiagramOutcomeDetail, DomainRelation, OldWordLiftResult, PathOutcomeDetail, PathOutcomeKind,
    RejectedPathCandidate, RestoredDiagram, RestoredEdge, RestoredPath, RestoredTransfer,
    RestoredVertex, TransferOutcomeDetail, TransferStepDiagnostic, WordPreservationCheck,
};
pub use result_phase3::{
    ChevalleyOutcomeDetail, ChevalleyRegionSummary, CommonQuantifierResult,
    CostRankedObservationSet, DesignatedValidityResult, DistinguishingPairSummary,
    DualNumberCounterexample, FiberNonEmptinessResult, GlobalRegularSectionResult,
    InsufficiencyWitness, LawReadoutAdequacyComparison, MinimalObservationSet, MixedWitnessPair,
    ObservationOutcomeDetail, PairEvaluationWitness, PointwiseQuantifierResult,
    RationalFiberProbeResult, RawCandidateEvaluationSummary, ReadingComparisonResult,
    RealizationWitness, RemovalCounterexample, RestoredCompletionWitness, RobustnessOutcomeDetail,
    UniversalRingStabilityResult,
};
pub use robustness::{
    CandidateSelector, CheckedChevalleyTask, CheckedRobustnessTask, ChevalleyTaskSpec,
    RationalFiberProbe, RobustnessTaskSpec,
};
pub use term::{CoeffDomain, PolyExpr, ScalarLit};
pub use transfer::{
    CheckedTransferTask, OldWordLiftSpec, TransferSpec, TransferStepSpec, WordCheckSpec,
    WordStepExpr,
};
pub use validate::{
    CheckedChangeSpec, CheckedComparisonPair, CheckedEvalCondition, CheckedPresentation,
    CheckedShigureTask, ValidationError, validate_change_spec, validate_coeff_domain,
    validate_comparison_pair, validate_eval_condition, validate_presentation,
};
