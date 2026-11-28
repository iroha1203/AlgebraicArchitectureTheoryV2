//! `shigure revision`・`shigure multisource` 宣言の未解決 AST および検査済み入力モデル（Phase 5 / AC2）。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::{
    RawMemberCoordValue, RawOriginRef, ShigureMemberCoordValue, ShigureOriginRef,
};
use super::{RawCoeffDomain, ShigureCoeffDomain};
use crate::law::ast::{Ident, Span};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShigureRevisionKind {
    Extension,
    Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRevisionCoord {
    pub id: Ident,
    pub domain_values: Vec<ShigureScalarLit>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRevisionCoord {
    pub id: String,
    pub domain_values: Vec<ShigureScalarLit>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawRevisionPredicate {
    Equality(Ident, Ident),
    LinearZero {
        terms: Vec<(ShigureScalarLit, Ident)>,
    },
    AllowedTuples {
        coords: Vec<Ident>,
        tuples: Vec<Vec<ShigureScalarLit>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureRevisionPredicate {
    Equality(String, String),
    LinearZero {
        terms: Vec<(ShigureScalarLit, String)>,
    },
    AllowedTuples {
        coords: Vec<String>,
        tuples: Vec<Vec<ShigureScalarLit>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRevisionConstraint {
    pub id: Ident,
    pub support: Vec<Ident>,
    pub predicate: RawRevisionPredicate,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRevisionConstraint {
    pub id: String,
    pub support: Vec<String>,
    pub predicate: ShigureRevisionPredicate,
    pub span: Span,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RawRevisionSide {
    pub assignments: Vec<(Ident, RawMemberCoordValue, Span)>,
    pub extra_constraints: Vec<RawRevisionConstraint>,
    pub span: Span,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ShigureRevisionSide {
    pub assignments: Vec<(String, ShigureMemberCoordValue)>,
    pub extra_constraints: Vec<ShigureRevisionConstraint>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRevisionEvalProbe {
    pub name: Ident,
    pub support: Vec<Ident>,
    pub target_coord: Ident,
    pub expected_value: ShigureScalarLit,
    pub antecedent_coord: Option<Ident>,
    pub antecedent_value: Option<ShigureScalarLit>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRevisionEvalProbe {
    pub name: String,
    pub support: Vec<String>,
    pub target_coord: String,
    pub expected_value: ShigureScalarLit,
    pub antecedent_coord: Option<String>,
    pub antecedent_value: Option<ShigureScalarLit>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawSnfOperatorMode {
    Common(Vec<Vec<RawMemberCoordValue>>),
    Split {
        before: Vec<Vec<RawMemberCoordValue>>,
        after: Vec<Vec<RawMemberCoordValue>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureSnfOperatorMode {
    Common(Vec<Vec<ShigureMemberCoordValue>>),
    Split {
        before: Vec<Vec<ShigureMemberCoordValue>>,
        after: Vec<Vec<ShigureMemberCoordValue>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSnfRevision {
    pub domain: RawCoeffDomain,
    pub num_cols: usize,
    pub operator: RawSnfOperatorMode,
    pub rhs_before: Vec<RawMemberCoordValue>,
    pub rhs_after: Vec<RawMemberCoordValue>,
    pub operator_unobserved: Vec<Ident>,
    pub force_reuse_existing_snf: bool,
    pub origin_label_only: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureSnfRevision {
    pub coeff_domain: ShigureCoeffDomain,
    pub num_cols: usize,
    pub operator: ShigureSnfOperatorMode,
    pub rhs_before: Vec<ShigureMemberCoordValue>,
    pub rhs_after: Vec<ShigureMemberCoordValue>,
    pub operator_unobserved: Vec<String>,
    pub force_reuse_existing_snf: bool,
    pub origin_label_only: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRevisionTask {
    pub name: Ident,
    pub kind: ShigureRevisionKind,
    pub domain: RawCoeffDomain,
    pub origins: Vec<RawOriginRef>,
    pub coords: Vec<RawRevisionCoord>,
    pub shared_constraints: Vec<RawRevisionConstraint>,
    pub before: RawRevisionSide,
    pub after: RawRevisionSide,
    pub explicit_delta_coords: Vec<Ident>,
    pub probes: Vec<RawRevisionEvalProbe>,
    pub snf: Option<RawSnfRevision>,
    pub max_completions: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRevisionTask {
    pub name: String,
    pub reading: String,
    pub kind: ShigureRevisionKind,
    pub coeff_domain: ShigureCoeffDomain,
    pub origins: Vec<ShigureOriginRef>,
    pub coords: Vec<ShigureRevisionCoord>,
    pub shared_constraints: Vec<ShigureRevisionConstraint>,
    pub before: ShigureRevisionSide,
    pub after: ShigureRevisionSide,
    pub explicit_delta_coords: Vec<String>,
    pub probes: Vec<ShigureRevisionEvalProbe>,
    pub snf: Option<ShigureSnfRevision>,
    pub max_completions: usize,
    pub span: Span,
}

// ---- `shigure multisource`（第19章後半）----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSourcePresentation {
    pub source_id: Ident,
    pub origin: RawOriginRef,
    pub assignments: Vec<(Ident, RawMemberCoordValue, Span)>,
    pub forbidden_values: Vec<(Ident, RawMemberCoordValue, Span)>,
    pub extra_constraints: Vec<RawRevisionConstraint>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureSourcePresentation {
    pub source_id: String,
    pub origin: ShigureOriginRef,
    pub assignments: Vec<(String, ShigureMemberCoordValue)>,
    pub forbidden_values: Vec<(String, ShigureMemberCoordValue)>,
    pub extra_constraints: Vec<ShigureRevisionConstraint>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCandidateRecord {
    pub id: Ident,
    pub coord: Ident,
    pub value: RawMemberCoordValue,
    pub cost: Option<(ShigureScalarLit, Span)>,
    pub origin: RawOriginRef,
    pub verified_actual_value: Option<(RawMemberCoordValue, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureCandidateRecord {
    pub id: String,
    pub coord: String,
    pub value: ShigureMemberCoordValue,
    pub cost: Option<ShigureScalarLit>,
    pub origin: ShigureOriginRef,
    pub verified_actual_value: Option<ShigureMemberCoordValue>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawSupportGoalFormula {
    CoordEquality(Ident, Ident, Span),
    CoordEqualsConst(Ident, ShigureScalarLit, Span),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureSupportGoalFormula {
    CoordEquality(String, String),
    CoordEqualsConst(String, ShigureScalarLit),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSupportGoalSpec {
    pub trusted_assignments: Vec<(Ident, RawMemberCoordValue, Span)>,
    pub candidates: Vec<RawCandidateRecord>,
    pub goal: RawSupportGoalFormula,
    pub expected_truth: bool,
    pub check_post_adoption_stability: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureSupportGoalSpec {
    pub trusted_assignments: Vec<(String, ShigureMemberCoordValue)>,
    pub candidates: Vec<ShigureCandidateRecord>,
    pub goal: ShigureSupportGoalFormula,
    pub expected_truth: bool,
    pub check_post_adoption_stability: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawMultisourceTask {
    pub name: Ident,
    pub domain: RawCoeffDomain,
    pub origins: Vec<RawOriginRef>,
    pub coords: Vec<RawRevisionCoord>,
    pub background_constraints: Vec<RawRevisionConstraint>,
    pub sources: Vec<RawSourcePresentation>,
    pub support_goal: Option<RawSupportGoalSpec>,
    pub max_sources_subset_steps: Option<usize>,
    pub max_results: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureMultisourceTask {
    pub name: String,
    pub reading: String,
    pub coeff_domain: ShigureCoeffDomain,
    pub origins: Vec<ShigureOriginRef>,
    pub coords: Vec<ShigureRevisionCoord>,
    pub background_constraints: Vec<ShigureRevisionConstraint>,
    pub sources: Vec<ShigureSourcePresentation>,
    pub support_goal: Option<ShigureSupportGoalSpec>,
    pub max_sources_subset_steps: usize,
    pub max_results: usize,
    pub span: Span,
}
