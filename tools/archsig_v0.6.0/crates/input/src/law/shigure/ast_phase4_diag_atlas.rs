//! `shigure diagnostics`・`shigure atlas` 宣言の未解決 AST および検査済み入力モデル（Phase 4 / AC2）。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::{
    RawMemberCoordValue, RawOriginRef, ShigureMemberCoordValue, ShigureOriginRef,
};
use super::{RawCoeffDomain, RawNamedPoly, ShigureCoeffDomain, ShigureNamedPoly, ShigurePolyExpr};
use crate::law::ast::{Ident, QName, Span};

// ---- 共通: K1 `TargetSupportedNerve` ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawChartSupport {
    pub name: Ident,
    pub support: Vec<Ident>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawNerveEdge {
    pub name: Ident,
    pub left: Ident,
    pub right: Ident,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawNerveFace {
    pub name: Ident,
    pub e0: Ident,
    pub e1: Ident,
    pub e2: Ident,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSupportedNerve {
    pub charts: Vec<RawChartSupport>,
    pub edges: Vec<RawNerveEdge>,
    pub faces: Vec<RawNerveFace>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureChartSupport {
    pub name: String,
    pub support: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureNerveEdge {
    pub name: String,
    pub left: String,
    pub right: String,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureNerveFace {
    pub name: String,
    pub e0: String,
    pub e1: String,
    pub e2: String,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureSupportedNerve {
    pub charts: Vec<ShigureChartSupport>,
    pub edges: Vec<ShigureNerveEdge>,
    pub faces: Vec<ShigureNerveFace>,
    pub span: Span,
}

/// 多項式または ArchMap observed / 欠測値（`poly_readout` などで欠測スロットを保持）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawPolyOrObserved {
    Poly(ShigurePolyExpr),
    ObservedField { field: QName, span: Span },
    Missing(Span),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigurePolyOrObserved {
    Poly(ShigurePolyExpr),
    ObservedField {
        entity: String,
        field: String,
        span: Span,
    },
    Missing,
}

// ---- `shigure diagnostics` 未解決 AST ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawStaticLawReadout {
    pub law_name: Ident,
    pub values: Vec<(Ident, ShigureScalarLit, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPolyLawReadout {
    pub law_name: Ident,
    pub values: Vec<(Ident, RawPolyOrObserved, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawDiagnosticsReadout {
    Static {
        sources: Vec<Ident>,
        targets: Vec<Ident>,
        reading: Vec<(Ident, Ident, Span)>,
        laws: Vec<RawStaticLawReadout>,
        span: Span,
    },
    Polynomial {
        base_domain: RawCoeffDomain,
        base_vars: Vec<Ident>,
        base_relations: Vec<RawNamedPoly>,
        sources: Vec<Ident>,
        laws: Vec<RawPolyLawReadout>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawExplicitZComplex {
    pub dim0: usize,
    pub dim1: usize,
    pub d0: Vec<Vec<i64>>,
    pub designated_cocycle: Option<Vec<i64>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCoeffChangeComparison {
    pub target_domain: RawCoeffDomain,
    pub compare_codomain_regeneration: bool,
    pub explicit_z_complex: Option<RawExplicitZComplex>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCollisionComparison {
    pub label: String,
    pub law_name: Ident,
    pub fine_partition: Vec<Vec<Ident>>,
    pub coarse_partition: Vec<Vec<Ident>>,
    pub alternative_merge_paths: Vec<Vec<Vec<Vec<Ident>>>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawNamedRPoint {
    pub label: String,
    pub coords: Vec<(Ident, Vec<RawMemberCoordValue>, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRPointProbe {
    pub ring_var: Ident,
    pub ring_max_deg: usize,
    pub points: Vec<RawNamedRPoint>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawNamedBasePoint {
    pub label: String,
    pub coords: Vec<(Ident, RawMemberCoordValue, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawDimensionRealization {
    pub base_domain: RawCoeffDomain,
    pub base_vars: Vec<Ident>,
    pub vanishing_polys: Vec<RawNamedPoly>,
    pub invertible_poly: RawNamedPoly,
    pub probe_points: Vec<RawNamedBasePoint>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawDiagnosticsTask {
    pub name: Ident,
    pub diagnostic_coeff: RawCoeffDomain,
    pub origins: Vec<RawOriginRef>,
    pub nerve: RawSupportedNerve,
    pub readout: RawDiagnosticsReadout,
    pub coeff_change: Option<RawCoeffChangeComparison>,
    pub collisions: Vec<RawCollisionComparison>,
    pub r_point_probe: Option<RawRPointProbe>,
    pub dimension_realization: Option<RawDimensionRealization>,
    pub max_partitions: Option<usize>,
    pub span: Span,
}

// ---- `shigure diagnostics` 検査済みモデル ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureStaticLawReadout {
    pub law_name: String,
    pub values: Vec<(String, ShigureScalarLit)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigurePolyLawReadout {
    pub law_name: String,
    pub values: Vec<(String, ShigurePolyOrObserved)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureDiagnosticsReadout {
    Static {
        sources: Vec<String>,
        targets: Vec<String>,
        reading: Vec<(String, String)>,
        laws: Vec<ShigureStaticLawReadout>,
        span: Span,
    },
    Polynomial {
        base_domain: ShigureCoeffDomain,
        base_vars: Vec<String>,
        base_relations: Vec<ShigureNamedPoly>,
        sources: Vec<String>,
        laws: Vec<ShigurePolyLawReadout>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureExplicitZComplex {
    pub dim0: usize,
    pub dim1: usize,
    pub d0: Vec<Vec<i64>>,
    pub designated_cocycle: Option<Vec<i64>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureCoeffChangeComparison {
    pub target_domain: ShigureCoeffDomain,
    pub compare_codomain_regeneration: bool,
    pub explicit_z_complex: Option<ShigureExplicitZComplex>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureCollisionComparison {
    pub label: String,
    pub law_name: String,
    pub fine_partition: Vec<Vec<String>>,
    pub coarse_partition: Vec<Vec<String>>,
    pub alternative_merge_paths: Vec<Vec<Vec<Vec<String>>>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureNamedRPoint {
    pub label: String,
    pub coords: Vec<(String, Vec<ShigureMemberCoordValue>)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRPointProbe {
    pub ring_var: String,
    pub ring_max_deg: usize,
    pub points: Vec<ShigureNamedRPoint>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureNamedBasePoint {
    pub label: String,
    pub coords: Vec<(String, ShigureMemberCoordValue)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureDimensionRealization {
    pub base_domain: ShigureCoeffDomain,
    pub base_vars: Vec<String>,
    pub vanishing_polys: Vec<ShigureNamedPoly>,
    pub invertible_poly: ShigureNamedPoly,
    pub probe_points: Vec<ShigureNamedBasePoint>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureDiagnosticsTask {
    pub name: String,
    pub reading: String,
    pub diagnostic_coeff: ShigureCoeffDomain,
    pub origins: Vec<ShigureOriginRef>,
    pub nerve: ShigureSupportedNerve,
    pub readout: ShigureDiagnosticsReadout,
    pub coeff_change: Option<ShigureCoeffChangeComparison>,
    pub collisions: Vec<ShigureCollisionComparison>,
    pub r_point_probe: Option<ShigureRPointProbe>,
    pub dimension_realization: Option<ShigureDimensionRealization>,
    pub max_partitions: Option<usize>,
    pub span: Span,
}

// ---- `shigure atlas` 未解決 AST ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawGraphEdge {
    pub name: Ident,
    pub from: Ident,
    pub to: Ident,
    pub offset: RawMemberCoordValue,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAtlasEvalCondition {
    pub evaluations: Vec<RawNamedPoly>,
    pub equations: Vec<RawNamedPoly>,
    pub invertibles: Vec<RawNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawForgetfulReading {
    pub forgotten_var: Ident,
    pub eval_expr: ShigurePolyExpr,
    pub condition_eq: ShigurePolyExpr,
    pub sample_values: Vec<RawMemberCoordValue>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAtlasRefinement {
    pub fine_vertices: Vec<Ident>,
    pub fine_edges: Vec<RawGraphEdge>,
    pub vertex_map: Vec<(Ident, Ident, Span)>,
    pub edge_map: Vec<(Ident, Option<Ident>, Span)>,
    pub common_sources: Vec<Ident>,
    pub coarse_reading: Vec<(Ident, Ident, Span)>,
    pub fine_reading: Vec<(Ident, Ident, Span)>,
    pub coarse_nerve: RawSupportedNerve,
    pub fine_nerve: RawSupportedNerve,
    pub nerve_chart_map: Vec<(Ident, Ident, Span)>,
    pub nerve_edge_map: Vec<(Ident, Option<Ident>, Span)>,
    pub nerve_face_map: Vec<(Ident, Option<Ident>, Span)>,
    pub eval_condition: Option<RawAtlasEvalCondition>,
    pub forgetful_reading: Option<RawForgetfulReading>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAtomicOpCompare {
    pub name: Ident,
    pub arg_vars: Vec<Ident>,
    pub before_updates: Vec<(Ident, ShigurePolyExpr, Span)>,
    pub after_updates: Vec<(Ident, ShigurePolyExpr, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawExtendedOperationCheck {
    ProtocolSequence {
        name: String,
        extended_state_vars: Vec<Ident>,
        initial_state: Vec<(Ident, RawMemberCoordValue, Span)>,
        before_steps: Vec<Vec<(Ident, ShigurePolyExpr, Span)>>,
        after_steps: Vec<Vec<(Ident, ShigurePolyExpr, Span)>>,
        before_read: Box<ShigurePolyExpr>,
        after_read: Box<ShigurePolyExpr>,
        intermediate_laws: Vec<RawNamedPoly>,
        span: Span,
    },
    RuntimeArgOp {
        name: String,
        before_updates: Vec<(Ident, ShigurePolyExpr, Span)>,
        after_updates: Vec<(Ident, ShigurePolyExpr, Span)>,
        sample_state: Vec<(Ident, RawMemberCoordValue, Span)>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawExtendedLanguageCheck {
    pub state_vars: Vec<Ident>,
    pub adapter_map: Vec<(Ident, ShigurePolyExpr, Span)>,
    pub atomic_ops: Vec<RawAtomicOpCompare>,
    pub extended_checks: Vec<RawExtendedOperationCheck>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAtlasTask {
    pub name: Ident,
    pub domain: RawCoeffDomain,
    pub origins: Vec<RawOriginRef>,
    pub vertices: Vec<Ident>,
    pub edges: Vec<RawGraphEdge>,
    pub mu: (RawMemberCoordValue, Span),
    pub base_lambdas: Vec<(Ident, RawMemberCoordValue, Span)>,
    pub allowed_vertices: Vec<Ident>,
    pub allowed_edges: Vec<Ident>,
    pub compare_to_q: bool,
    pub refinement: Option<Box<RawAtlasRefinement>>,
    pub extended_language_check: Option<RawExtendedLanguageCheck>,
    pub span: Span,
}

// ---- `shigure atlas` 検査済みモデル ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureGraphEdge {
    pub name: String,
    pub from: String,
    pub to: String,
    pub offset: ShigureMemberCoordValue,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureAtlasEvalCondition {
    pub evaluations: Vec<ShigureNamedPoly>,
    pub equations: Vec<ShigureNamedPoly>,
    pub invertibles: Vec<ShigureNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureForgetfulReading {
    pub forgotten_var: String,
    pub eval_expr: ShigurePolyExpr,
    pub condition_eq: ShigurePolyExpr,
    pub sample_values: Vec<ShigureMemberCoordValue>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureAtlasRefinement {
    pub fine_vertices: Vec<String>,
    pub fine_edges: Vec<ShigureGraphEdge>,
    pub vertex_map: Vec<(String, String)>,
    pub edge_map: Vec<(String, Option<String>)>,
    pub common_sources: Vec<String>,
    pub coarse_reading: Vec<(String, String)>,
    pub fine_reading: Vec<(String, String)>,
    pub coarse_nerve: ShigureSupportedNerve,
    pub fine_nerve: ShigureSupportedNerve,
    pub nerve_chart_map: Vec<(String, String)>,
    pub nerve_edge_map: Vec<(String, Option<String>)>,
    pub nerve_face_map: Vec<(String, Option<String>)>,
    pub eval_condition: Option<ShigureAtlasEvalCondition>,
    pub forgetful_reading: Option<ShigureForgetfulReading>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureAtomicOpCompare {
    pub name: String,
    pub arg_vars: Vec<String>,
    pub before_updates: Vec<(String, ShigurePolyExpr)>,
    pub after_updates: Vec<(String, ShigurePolyExpr)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureExtendedOperationCheck {
    ProtocolSequence {
        name: String,
        extended_state_vars: Vec<String>,
        initial_state: Vec<(String, ShigureMemberCoordValue)>,
        before_steps: Vec<Vec<(String, ShigurePolyExpr)>>,
        after_steps: Vec<Vec<(String, ShigurePolyExpr)>>,
        before_read: Box<ShigurePolyExpr>,
        after_read: Box<ShigurePolyExpr>,
        intermediate_laws: Vec<ShigureNamedPoly>,
        span: Span,
    },
    RuntimeArgOp {
        name: String,
        before_updates: Vec<(String, ShigurePolyExpr)>,
        after_updates: Vec<(String, ShigurePolyExpr)>,
        sample_state: Vec<(String, ShigureMemberCoordValue)>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureExtendedLanguageCheck {
    pub state_vars: Vec<String>,
    pub adapter_map: Vec<(String, ShigurePolyExpr)>,
    pub atomic_ops: Vec<ShigureAtomicOpCompare>,
    pub extended_checks: Vec<ShigureExtendedOperationCheck>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureAtlasTask {
    pub name: String,
    pub reading: String,
    pub coeff_domain: ShigureCoeffDomain,
    pub origins: Vec<ShigureOriginRef>,
    pub vertices: Vec<String>,
    pub edges: Vec<ShigureGraphEdge>,
    pub mu: ShigureMemberCoordValue,
    pub base_lambdas: Vec<(String, ShigureMemberCoordValue)>,
    pub allowed_vertices: Vec<String>,
    pub allowed_edges: Vec<String>,
    pub compare_to_q: bool,
    pub refinement: Option<Box<ShigureAtlasRefinement>>,
    pub extended_language_check: Option<ShigureExtendedLanguageCheck>,
    pub span: Span,
}
