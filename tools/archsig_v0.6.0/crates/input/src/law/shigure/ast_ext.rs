//! `shigure diagram`・`shigure path`・`shigure transfer` 用の未解決 AST および検査済み入力モデル。

use super::{
    RawStateComparison, RawStateLawDecl, RawTranslatedWord, ShigurePolyExpr,
    ShigureStateComparison, ShigureStateLawDecl, ShigureTranslatedWord,
};
use crate::law::ast::{Ident, QName, Span};
use num_bigint::{BigInt, BigUint};
use std::collections::BTreeMap;

/// 射の向き指定（`state_map`: `src -> tgt`、`time_order`: `before -> after` で内部逆向き）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShigureDirection {
    StateMap,
    TimeOrder,
}

/// 端点パラメータ固定などに使うスカラー定数。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureScalarLit {
    Int(BigInt),
    Rat { num: BigInt, den: BigInt },
    Fp { value: BigUint, modulus: BigUint },
}

/// 辺・規則・移送段の射本体（名前付き比較射・恒等射・インライン定義）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawMorphismBody {
    Comparison(QName),
    Identity(Span),
    Inline {
        state_comparisons: Vec<RawStateComparison>,
        word_translation: Vec<RawTranslatedWord>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureMorphismBody {
    Comparison(String),
    Identity,
    Inline {
        state_comparisons: Vec<ShigureStateComparison>,
        word_translation: Vec<ShigureTranslatedWord>,
    },
}

// ---- 図式補完 (`shigure diagram`) ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawDiagramVertex {
    pub name: Ident,
    pub presentation: QName,
    pub is_fixed: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawDiagramEdge {
    pub name: Ident,
    pub source: Ident,
    pub target: Ident,
    pub is_fixed: bool,
    pub morphism: RawMorphismBody,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawDiagramRelation {
    pub name: Ident,
    pub lhs: Vec<Ident>,
    pub rhs: Vec<Ident>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawEdgeEvalCondition {
    pub edge: Ident,
    pub eval_condition: QName,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawDiagramTask {
    pub name: Ident,
    pub direction: ShigureDirection,
    pub vertices: Vec<RawDiagramVertex>,
    pub edges: Vec<RawDiagramEdge>,
    pub relations: Vec<RawDiagramRelation>,
    pub change_spec: QName,
    pub eval_condition: Option<QName>,
    pub edge_eval_conditions: Vec<RawEdgeEvalCondition>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureDiagramVertex {
    pub name: String,
    pub presentation: String,
    pub is_fixed: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureDiagramEdge {
    pub name: String,
    pub source: String,
    pub target: String,
    pub is_fixed: bool,
    pub morphism: ShigureMorphismBody,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureDiagramRelation {
    pub name: String,
    pub lhs: Vec<String>,
    pub rhs: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureDiagramTask {
    pub name: String,
    pub reading: String,
    pub direction: ShigureDirection,
    pub vertices: Vec<ShigureDiagramVertex>,
    pub edges: Vec<ShigureDiagramEdge>,
    pub relations: Vec<ShigureDiagramRelation>,
    pub change_spec: String,
    pub eval_condition: Option<String>,
    pub edge_eval_conditions: BTreeMap<String, String>,
    pub span: Span,
}

// ---- 一段変更経路 (`shigure path`) ----

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShigurePathKind {
    FixedProtocolChangePath,
    EnlargedProtocolExecutionPath,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawPathQueryMode {
    Find,
    Concatenate {
        first: Vec<Ident>,
        second: Vec<Ident>,
    },
    Subdivide {
        target_edge: RawMorphismBody,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigurePathQueryMode {
    Find,
    Concatenate {
        first: Vec<String>,
        second: Vec<String>,
    },
    Subdivide {
        target_edge: ShigureMorphismBody,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawModelEndpoint {
    pub vertex: Ident,
    pub param_values: Vec<(Ident, ShigureScalarLit, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureModelEndpoint {
    pub vertex: String,
    pub param_values: BTreeMap<String, ShigureScalarLit>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOneStepRule {
    pub name: Ident,
    pub from_vertex: Ident,
    pub to_vertex: Ident,
    pub param_guards: Vec<(Ident, ShigurePolyExpr, Span)>,
    pub param_updates: Vec<(Ident, ShigurePolyExpr, Span)>,
    pub morphism: RawMorphismBody,
    pub eval_condition: Option<QName>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOneStepRule {
    pub name: String,
    pub from_vertex: String,
    pub to_vertex: String,
    pub param_guards: Vec<(String, ShigurePolyExpr, Span)>,
    pub param_updates: BTreeMap<String, ShigurePolyExpr>,
    pub morphism: ShigureMorphismBody,
    pub eval_condition: Option<String>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawProtocolExecution {
    pub comparison: QName,
    pub start_phase: Ident,
    pub start_laws: Vec<RawStateLawDecl>,
    pub end_phase: Ident,
    pub end_laws: Vec<RawStateLawDecl>,
    pub allowed_ops: Vec<Ident>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureProtocolExecution {
    pub comparison: String,
    pub start_phase: String,
    pub start_laws: Vec<ShigureStateLawDecl>,
    pub end_phase: String,
    pub end_laws: Vec<ShigureStateLawDecl>,
    pub allowed_ops: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPathVertexBinding {
    pub vertex: Ident,
    pub presentation: QName,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPathTask {
    pub name: Ident,
    pub kind: ShigurePathKind,
    pub direction: ShigureDirection,
    pub query_mode: RawPathQueryMode,
    pub length: Option<usize>,
    pub vertices: Vec<RawPathVertexBinding>,
    pub rules: Vec<RawOneStepRule>,
    pub start: Option<RawModelEndpoint>,
    pub end: Option<RawModelEndpoint>,
    pub protocol: Option<RawProtocolExecution>,
    pub change_spec: QName,
    pub eval_condition: Option<QName>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigurePathTask {
    pub name: String,
    pub reading: String,
    pub kind: ShigurePathKind,
    pub direction: ShigureDirection,
    pub query_mode: ShigurePathQueryMode,
    pub length: Option<usize>,
    pub vertices: BTreeMap<String, String>,
    pub rules: Vec<ShigureOneStepRule>,
    pub start: Option<ShigureModelEndpoint>,
    pub end: Option<ShigureModelEndpoint>,
    pub protocol: Option<ShigureProtocolExecution>,
    pub change_spec: String,
    pub eval_condition: Option<String>,
    pub span: Span,
}

// ---- 合法状態移送 (`shigure transfer`) ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawWordStep {
    pub operation: Ident,
    pub arg_exprs: Vec<ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureWordStep {
    pub operation: String,
    pub arg_exprs: Vec<ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawWordCheck {
    pub name: Ident,
    pub args: Vec<Ident>,
    pub steps: Vec<RawWordStep>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureWordCheck {
    pub name: String,
    pub args: Vec<String>,
    pub steps: Vec<ShigureWordStep>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOldWordLift {
    pub name: Ident,
    pub args: Vec<Ident>,
    pub target_steps: Vec<RawWordStep>,
    pub max_length: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOldWordLift {
    pub name: String,
    pub args: Vec<String>,
    pub target_steps: Vec<ShigureWordStep>,
    pub max_length: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawTransferStepSource {
    Comparison(QName),
    Inline {
        before: QName,
        after: QName,
        morphism: RawMorphismBody,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureTransferStepSource {
    Comparison(String),
    Inline {
        before: String,
        after: String,
        morphism: ShigureMorphismBody,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawTransferStep {
    pub name: Ident,
    pub source: RawTransferStepSource,
    pub source_phase: Ident,
    pub target_phase: Ident,
    pub domain_laws: Vec<RawStateLawDecl>,
    pub lift_map: Vec<(Ident, ShigurePolyExpr, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureTransferStep {
    pub name: String,
    pub source: ShigureTransferStepSource,
    pub source_phase: String,
    pub target_phase: String,
    pub domain_laws: Vec<ShigureStateLawDecl>,
    pub lift_map: BTreeMap<String, ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawTransferTask {
    pub name: Ident,
    pub steps: Vec<RawTransferStep>,
    pub word_checks: Vec<RawWordCheck>,
    pub old_word_lifts: Vec<RawOldWordLift>,
    pub change_spec: QName,
    pub eval_condition: Option<QName>,
    pub require_full_domain: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureTransferTask {
    pub name: String,
    pub reading: String,
    pub steps: Vec<ShigureTransferStep>,
    pub word_checks: Vec<ShigureWordCheck>,
    pub old_word_lifts: Vec<ShigureOldWordLift>,
    pub change_spec: String,
    pub eval_condition: Option<String>,
    pub require_full_domain: bool,
    pub span: Span,
}
