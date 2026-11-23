//! `shigure family`・`shigure robustness`・`shigure chevalley`・`shigure observations` の
//! 未解決 AST および検査済み入力モデル（AC2）。

use super::ast_ext::ShigureScalarLit;
use super::{
    RawCoeffDomain, RawNamedPoly, RawPointDomain, ShigureCoeffDomain, ShigureNamedPoly,
    ShigurePointDomain, ShigurePolyExpr,
};
use crate::law::ast::{Ident, QName, Span};
use num_bigint::BigInt;
use std::collections::BTreeMap;

/// 候補・実現・観測に明示付与する由来種別。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShigureOriginKind {
    StaticAnalysis,
    RuntimeObservation,
    LlmCandidate,
    HumanAdopted,
}

/// 法宣言内の由来参照（明示宣言または ArchMap 由来 ID 参照）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawOriginRef {
    Explicit {
        kind: ShigureOriginKind,
        id: String,
        span: Span,
    },
    ArchMap {
        id: String,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureOriginRef {
    Explicit {
        kind: ShigureOriginKind,
        id: String,
        span: Span,
    },
    ArchMap {
        id: String,
        span: Span,
    },
}

/// 有限列挙メンバーの座標割り当て（定数・ArchMap observed 参照・明示欠測）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawMemberCoordValue {
    Literal(ShigureScalarLit),
    ObservedField { field: QName, span: Span },
    Missing(Span),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureMemberCoordValue {
    Literal(ShigureScalarLit),
    ObservedField {
        entity: String,
        field: String,
        span: Span,
    },
    Missing,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRealizationMember {
    pub id: Ident,
    pub assignments: Vec<(Ident, RawMemberCoordValue, Span)>,
    pub is_raw_candidate: bool,
    pub presentation: Option<QName>,
    pub origin: RawOriginRef,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRealizationMember {
    pub id: String,
    pub assignments: BTreeMap<String, ShigureMemberCoordValue>,
    pub is_raw_candidate: bool,
    pub presentation: Option<String>,
    pub origin: ShigureOriginRef,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawRealizationSpace {
    FiniteMembers {
        members: Vec<RawRealizationMember>,
        explicit_empty: bool,
    },
    PolynomialScheme {
        equations: Vec<RawNamedPoly>,
        invertibles: Vec<RawNamedPoly>,
        is_raw_candidate: bool,
        origin: RawOriginRef,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureRealizationSpace {
    FiniteMembers(Vec<ShigureRealizationMember>),
    PolynomialScheme {
        equations: Vec<ShigureNamedPoly>,
        invertibles: Vec<ShigureNamedPoly>,
        is_raw_candidate: bool,
        origin: ShigureOriginRef,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRealizationFamily {
    pub name: Ident,
    pub u_vars: Vec<Ident>,
    pub b_vars: Vec<Ident>,
    pub reading_q: Vec<ShigurePolyExpr>,
    pub space: RawRealizationSpace,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRealizationFamily {
    pub name: String,
    pub u_vars: Vec<String>,
    pub b_vars: Vec<String>,
    pub reading_q: Vec<ShigurePolyExpr>,
    pub space: ShigureRealizationSpace,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCandidateMember {
    pub id: Ident,
    pub assignments: Vec<(Ident, RawMemberCoordValue, Span)>,
    pub origin: RawOriginRef,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureCandidateMember {
    pub id: String,
    pub assignments: BTreeMap<String, ShigureMemberCoordValue>,
    pub origin: ShigureOriginRef,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawCandidateSpace {
    FiniteMembers {
        members: Vec<RawCandidateMember>,
        explicit_empty: bool,
    },
    PolynomialScheme {
        equations: Vec<RawNamedPoly>,
        invertibles: Vec<RawNamedPoly>,
        origin: RawOriginRef,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureCandidateSpace {
    FiniteMembers(Vec<ShigureCandidateMember>),
    PolynomialScheme {
        equations: Vec<ShigureNamedPoly>,
        invertibles: Vec<ShigureNamedPoly>,
        origin: ShigureOriginRef,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCandidateFamily {
    pub name: Ident,
    pub c_vars: Vec<Ident>,
    pub pi: Vec<ShigurePolyExpr>,
    pub space: RawCandidateSpace,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureCandidateFamily {
    pub name: String,
    pub c_vars: Vec<String>,
    pub pi: Vec<ShigurePolyExpr>,
    pub space: ShigureCandidateSpace,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPreservationSource {
    pub comparison: QName,
    pub change_spec: QName,
    pub param_bindings: Vec<(Ident, ShigurePolyExpr, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigurePreservationSource {
    pub comparison: String,
    pub change_spec: String,
    pub param_bindings: BTreeMap<String, ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSequenceStep {
    pub operation: Ident,
    pub args: Vec<ShigureScalarLit>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSequenceSpec {
    pub start_phase: Ident,
    pub start_state: Vec<(Ident, ShigureScalarLit, Span)>,
    pub steps: Vec<RawSequenceStep>,
    pub observation_name: Ident,
    pub baseline_step_index: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRawSequenceSpec {
    pub start_phase: String,
    pub start_state: BTreeMap<String, ShigureScalarLit>,
    pub steps: Vec<(String, Vec<ShigureScalarLit>)>,
    pub observation_name: String,
    pub baseline_step_index: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawGoodnessSpec {
    Direct {
        equations: Vec<RawNamedPoly>,
        invertibles: Vec<RawNamedPoly>,
        preservation: Option<RawPreservationSource>,
        raw_sequence: Option<RawSequenceSpec>,
        span: Span,
    },
    Existential {
        witness_vars: Vec<Ident>,
        equations: Vec<RawNamedPoly>,
        invertibles: Vec<RawNamedPoly>,
        preservation: Option<RawPreservationSource>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureGoodnessSpec {
    Direct {
        equations: Vec<ShigureNamedPoly>,
        invertibles: Vec<ShigureNamedPoly>,
        preservation: Option<ShigurePreservationSource>,
        raw_sequence: Option<ShigureRawSequenceSpec>,
    },
    Existential {
        witness_vars: Vec<String>,
        equations: Vec<ShigureNamedPoly>,
        invertibles: Vec<ShigureNamedPoly>,
        preservation: Option<ShigurePreservationSource>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawReadingComparison {
    pub name: Ident,
    pub fine_b_vars: Vec<Ident>,
    pub fine_q: Vec<ShigurePolyExpr>,
    pub coarsen_r: Vec<ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureReadingComparison {
    pub name: String,
    pub fine_b_vars: Vec<String>,
    pub fine_q: Vec<ShigurePolyExpr>,
    pub coarsen_r: Vec<ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawFamilySpec {
    pub name: Ident,
    pub domain: RawCoeffDomain,
    pub realizations: RawRealizationFamily,
    pub candidates: RawCandidateFamily,
    pub goodness: RawGoodnessSpec,
    pub reading_comparison: Option<RawReadingComparison>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureFamilySpec {
    pub name: String,
    pub reading: String,
    pub coeff_domain: ShigureCoeffDomain,
    pub realizations: ShigureRealizationFamily,
    pub candidates: ShigureCandidateFamily,
    pub goodness: ShigureGoodnessSpec,
    pub reading_comparison: Option<ShigureReadingComparison>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawCandidateSelector {
    ById(Ident),
    ByValues(Vec<(Ident, ShigureScalarLit, Span)>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureCandidateSelector {
    ById(String),
    ByValues(BTreeMap<String, ShigureScalarLit>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRobustnessTask {
    pub name: Ident,
    pub family: QName,
    pub point_domain: RawPointDomain,
    pub base_value: Vec<ShigureScalarLit>,
    pub designated_candidate: Option<RawCandidateSelector>,
    pub check_universal_ring: bool,
    pub fine_base_value: Option<Vec<ShigureScalarLit>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRobustnessTask {
    pub name: String,
    pub reading: String,
    pub family: String,
    pub point_domain: ShigurePointDomain,
    pub base_value: Vec<ShigureScalarLit>,
    pub designated_candidate: Option<ShigureCandidateSelector>,
    pub check_universal_ring: bool,
    pub fine_base_value: Option<Vec<ShigureScalarLit>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRationalProbe {
    pub name: Ident,
    pub assignments: Vec<(Ident, ShigureScalarLit, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRationalProbe {
    pub name: String,
    pub u_assignments: BTreeMap<String, ShigureScalarLit>,
    pub c_assignments: BTreeMap<String, ShigureScalarLit>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawChevalleyTask {
    pub name: Ident,
    pub family: QName,
    pub point_domain: RawPointDomain,
    pub base_value: Option<Vec<ShigureScalarLit>>,
    pub designated_candidate: Option<RawCandidateSelector>,
    pub probes: Vec<RawRationalProbe>,
    pub check_global_regular_section: bool,
    pub check_universal_ring: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureChevalleyTask {
    pub name: String,
    pub reading: String,
    pub family: String,
    pub point_domain: ShigurePointDomain,
    pub base_value: Option<Vec<ShigureScalarLit>>,
    pub designated_candidate: Option<ShigureCandidateSelector>,
    pub probes: Vec<ShigureRationalProbe>,
    pub check_global_regular_section: bool,
    pub check_universal_ring: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCandidateObservationDecl {
    pub id: Ident,
    pub components: Vec<RawNamedPoly>,
    pub cost: Option<(BigInt, Span)>,
    pub origin: RawOriginRef,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureCandidateObservationDecl {
    pub id: String,
    pub components: Vec<ShigureNamedPoly>,
    pub cost: Option<BigInt>,
    pub origin: ShigureOriginRef,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawLawReadoutDecl {
    pub name: Ident,
    pub components: Vec<RawNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureLawReadoutDecl {
    pub name: String,
    pub components: Vec<ShigureNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawObservationTask {
    pub name: Ident,
    pub family: QName,
    pub point_domain: RawPointDomain,
    pub base_value: Vec<ShigureScalarLit>,
    pub observations: Vec<RawCandidateObservationDecl>,
    pub law_readout: Option<RawLawReadoutDecl>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureObservationTask {
    pub name: String,
    pub reading: String,
    pub family: String,
    pub point_domain: ShigurePointDomain,
    pub base_value: Vec<ShigureScalarLit>,
    pub observations: Vec<ShigureCandidateObservationDecl>,
    pub law_readout: Option<ShigureLawReadoutDecl>,
    pub span: Span,
}
