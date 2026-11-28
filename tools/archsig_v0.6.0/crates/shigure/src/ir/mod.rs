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

pub mod artin;
pub mod atlas;
pub mod change;
pub mod diagnostics;
pub mod diagram;
pub mod family;
pub mod lift;
pub mod morphism;
pub mod multisource;
pub mod observation;
pub mod occurrence;
pub mod partial;
mod partial_open_validate;
mod partial_validate;
pub mod path;
pub mod presentation;
pub mod provenance;
pub mod result;
pub mod result_ext;
pub mod result_phase3;
pub mod result_phase4;
pub mod result_phase4_diag_atlas;
pub mod result_phase5_obs;
pub mod result_phase5_rev;
pub mod revision;
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
#[cfg(test)]
mod tests_phase4;
#[cfg(test)]
mod tests_phase4_edge;
#[cfg(test)]
mod tests_phase5;

pub use artin::{
    ArtinTaskSpec, AuxiliaryDefSpec, BaseChangeSpec, CheckedArtinTask, CompositeStageSpec,
    validate_artin_task,
};
pub use atlas::{
    AtlasEvalConditionSpec, AtlasRefinementSpec, AtlasTaskSpec, AtomicOpCompareSpec,
    CheckedAtlasTask, ExtendedLanguageCheckSpec, ExtendedOperationCheckSpec, ForgetfulReadingSpec,
    GraphEdgeSpec, validate_atlas_task,
};
pub use change::{
    ChangeSpec, EditableTarget, EvalCondition, FixedTarget, NamedPoly, ParamDecl, PointDomain,
};
pub use diagnostics::{
    ChartSupportSpec, CheckedDiagnosticsTask, CoeffChangeComparisonSpec, CollisionComparisonSpec,
    DiagnosticsReadoutSpec, DiagnosticsTaskSpec, DimensionRealizationSpec, ExplicitZComplexSpec,
    NamedBasePointSpec, NamedRPointSpec, NerveEdgeSpec, NerveFaceSpec, PolyLawReadoutSpec,
    RPointProbeSpec, StaticLawReadoutSpec, SupportedNerveSpec, validate_diagnostics_task,
    validate_supported_nerve,
};
pub use diagram::{CheckedDiagramTask, DiagramEdge, DiagramRelation, DiagramSpec, DiagramVertex};
pub use family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, CheckedFamilySpec, FamilySpec,
    GoodnessKind, GoodnessSpec, PreservationGoodnessSource, RawSequenceCheck,
    ReadingComparisonSpec, RealizationFamilySpec, RealizationMember, RealizationSpace,
};
pub use lift::{
    AffineAllowedSpec, CheckedLiftTask, DeclarationContextSpec, DeclarationCoverSpec,
    FiniteEtaleDescentSpec, LiftTaskSpec, RawReadComparisonSpec, RedundantLawComparisonSpec,
    RelativeReadingSpec, RingParamSpec, SquareZeroSpec, TwoContextCechSpec, validate_lift_task,
};
pub use morphism::{
    MorphismDirection, StateMorphism, TimeStepMorphism, compose_state_order, compose_time_order,
    identity_state_morphism,
};
pub use multisource::{
    CandidateRecordSpec, CheckedMultisourceTask, MultisourceTaskSpec, SourcePresentationSpec,
    SupportGoalFormula, SupportGoalSpec, validate_multisource_task,
};
pub use observation::{
    CandidateObservationDecl, CheckedObservationTask, LawReadoutSpec, ObservationTaskSpec,
};
pub use occurrence::{
    CheckedOccurrenceTask, OccurrenceInitialReadoutSpec, OccurrenceOpSpec, OccurrenceReadingSpec,
    OccurrenceRelSpec, OccurrenceSortSpec, OccurrenceTaskSpec, validate_occurrence_task,
};
pub use partial::{
    AffinePartialPresentation, AffineRestrictionSpec, BackgroundConstraint, CheckedPartialTask,
    FiberCoverageCheckSpec, FinitePartialPresentation, OpenDomainSpec, OpenOpTable, OpenRelTable,
    PartialArithOp, PartialEvalLawSpec, PartialFormula, PartialOpSignature, PartialPredSignature,
    PartialRecordKind, PartialRecordSpec, PartialRepresentation, PartialSlotDecl, PartialTaskSpec,
    PartialTerm, PartialTruth, PartialValue, QuantifierCompletionSpec, QuantifierHierarchySpec,
    validate_partial_task,
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
pub use result_phase4::{
    AffineRepairResult, ArtinCompositionResult, ArtinOutcomeDetail, AtlasOutcomeDetail,
    AtlasRefinementResult, CoeffChangeResult, CollisionMayerVietorisResult, ConditionCResult,
    ConstrainedRepairSummary, DeclarationCoverResult, DiagnosticsOutcomeDetail,
    DimensionProbePointResult, DimensionRealizationResult, ExplicitComplexChangeResult,
    ExtendedCheckOutcome, ExtendedLanguageResult, FiniteEtaleDescentResult, ForgetfulReadingResult,
    LawValueBlockSummary, LiftOutcomeDetail, NilpotentBaseChangeResult, PartitionStratumSummary,
    RPointContrastResult, RawCechComparisonResult, RedundantComparisonResult, RelativeConeResult,
    UniversalObstructionSummary, UpperSemicontinuityRefutation,
};
pub use result_phase5_obs::{
    AttributeRealizationDetail, OccurrenceCollisionDetail, OccurrenceOutcomeDetail,
    OpenDomainResultDetail, PartialLawEvalSummary, PartialOutcomeDetail, QuantifierHierarchyDetail,
    SeparatingContextDetail,
};
pub use result_phase5_rev::{
    MultisourceOutcomeDetail, RevisionOutcomeDetail, RevisionProbeResult, SnfReuseDetail,
    SupportCostEntry, SupportGoalDetail,
};
pub use revision::{
    CheckedRevisionTask, RevisionConstraintSpec, RevisionCoordSpec, RevisionEvalProbe,
    RevisionKind, RevisionPredicate, RevisionSideSpec, RevisionTaskSpec, SnfRevisionSpec,
    validate_revision_task,
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
