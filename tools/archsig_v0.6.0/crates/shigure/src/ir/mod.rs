//! SHIGURE 中心中間表現（IR）。
//!
//! - `provenance`: 由来種別（静的解析・実行観測・LLM 読解候補・人間採用）と紙上証明条項参照
//! - `term`: 係数域（Z / Q / F_p）・スカラー定数・型付き affine / 多項式構文木
//! - `presentation`: 原始表示 IR・守る意味 Law と編集可能な表示 Law・状態比較 h・語翻訳 τ
//! - `change`: 許容変換仕様 H と評価条件 P（V(f), D(g), PointDomain）
//! - `result`: 適用条件検査・沈黙理由・空性 witness・復元と再評価検算・出力 JSON
//! - `validate`: 型・参照・係数域・意味 Law 保護・未観測検出の検証済み構築経路

pub mod change;
pub mod presentation;
pub mod provenance;
pub mod result;
pub mod term;
pub mod validate;
mod validate_change;

#[cfg(test)]
mod tests;

pub use change::{
    ChangeSpec, EditableTarget, EvalCondition, FixedTarget, NamedPoly, ParamDecl, PointDomain,
};
pub use presentation::{
    ComparisonPair, CoordDecl, LawKind, ObservationDecl, OperationDecl, PhaseDecl, Presentation,
    SortDecl, StateComparison, StateLaw, TranslatedStep, TranslatedWord, WordTranslation,
};
pub use provenance::{MathClause, OriginKind, Provenance, SourceRef};
pub use result::{
    ApplicabilityCheck, EmptyWitness, InteractionSummary, ReevalCheck, RestoredArtifact,
    ShigureOutcome, SilenceReason, Verdict,
};
pub use term::{CoeffDomain, PolyExpr, ScalarLit};
pub use validate::{
    CheckedChangeSpec, CheckedComparisonPair, CheckedEvalCondition, CheckedPresentation,
    CheckedShigureTask, ValidationError, validate_change_spec, validate_coeff_domain,
    validate_comparison_pair, validate_eval_condition, validate_presentation,
};
