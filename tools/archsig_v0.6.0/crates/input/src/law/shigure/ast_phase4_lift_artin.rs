//! `shigure lift`・`shigure artin` 宣言の未解決 AST および検査済み入力モデル（Phase 4 / AC2）。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::{
    RawMemberCoordValue, RawOriginRef, ShigureMemberCoordValue, ShigureOriginRef,
};
use super::{RawCoeffDomain, RawNamedPoly, ShigureCoeffDomain, ShigureNamedPoly, ShigurePolyExpr};
use crate::law::ast::{Ident, Span};

// ---- 平方零拡大 (`extension`) ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawSquareZeroSpec {
    TruncatedPoly {
        var_name: Ident,
        base_degree: usize,
        span: Span,
    },
    ExplicitTable {
        r_prime_basis: Vec<Ident>,
        r_prime_one: Vec<ShigureScalarLit>,
        r_prime_mul: Vec<Vec<Vec<ShigureScalarLit>>>,
        r_base_basis: Vec<Ident>,
        r_base_one: Vec<ShigureScalarLit>,
        r_base_mul: Vec<Vec<Vec<ShigureScalarLit>>>,
        projection: Vec<Vec<ShigureScalarLit>>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureSquareZeroSpec {
    TruncatedPoly {
        var_name: String,
        base_degree: usize,
        span: Span,
    },
    ExplicitTable {
        r_prime_basis: Vec<String>,
        r_prime_one: Vec<ShigureScalarLit>,
        r_prime_mul: Vec<Vec<Vec<ShigureScalarLit>>>,
        r_base_basis: Vec<String>,
        r_base_one: Vec<ShigureScalarLit>,
        r_base_mul: Vec<Vec<Vec<ShigureScalarLit>>>,
        projection: Vec<Vec<ShigureScalarLit>>,
        span: Span,
    },
}

// ---- `shigure lift` 未解決 AST ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRingParam {
    pub name: Ident,
    pub value_in_r_prime: Vec<RawMemberCoordValue>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawReadComparisonAst {
    pub label: String,
    pub expr: ShigurePolyExpr,
    pub negated: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRelativeReading {
    pub obs_vars: Vec<Ident>,
    pub obs_laws: Vec<RawNamedPoly>,
    pub reading_map: Vec<(Ident, ShigurePolyExpr, Span)>,
    pub designated_obs_lift: Vec<(Ident, Vec<RawMemberCoordValue>, Span)>,
    pub raw_read_diff: Option<RawReadComparisonAst>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawDeclarationContext {
    pub name: Ident,
    pub vars: Vec<Ident>,
    pub laws: Vec<Ident>,
    pub observations: Vec<RawNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawTwoContextCech {
    pub left_context: Ident,
    pub right_context: Ident,
    pub shared_vars: Vec<Ident>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawDeclarationCover {
    pub contexts: Vec<RawDeclarationContext>,
    pub two_context_cech: Option<RawTwoContextCech>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAffineAllowed {
    pub allowed_vars: Vec<Ident>,
    pub finite_displacement: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawRedundantComparison {
    pub reference_laws: Vec<RawNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawFiniteEtaleDescent {
    pub base_var: Ident,
    pub cover_var: Ident,
    pub degree: u32,
    pub base_invertible: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawLiftTask {
    pub name: Ident,
    pub domain: RawCoeffDomain,
    pub origins: Vec<RawOriginRef>,
    pub variables: Vec<Ident>,
    pub ring_params: Vec<RawRingParam>,
    pub laws: Vec<RawNamedPoly>,
    pub extension: RawSquareZeroSpec,
    pub base_point: Vec<(Ident, Vec<RawMemberCoordValue>, Span)>,
    pub ambient_lift: Option<Vec<(Ident, Vec<RawMemberCoordValue>, Span)>>,
    pub relative_reading: Option<RawRelativeReading>,
    pub declaration_cover: Option<RawDeclarationCover>,
    pub affine_allowed: Option<RawAffineAllowed>,
    pub redundant_comparison: Option<RawRedundantComparison>,
    pub etale_descent: Option<RawFiniteEtaleDescent>,
    pub max_syzygy_pairs: Option<usize>,
    pub span: Span,
}

// ---- `shigure lift` 検査済みモデル ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRingParam {
    pub name: String,
    pub value_in_r_prime: Vec<ShigureMemberCoordValue>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRawReadComparison {
    pub label: String,
    pub expr: ShigurePolyExpr,
    pub negated: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRelativeReading {
    pub obs_vars: Vec<String>,
    pub obs_laws: Vec<ShigureNamedPoly>,
    pub reading_map: Vec<(String, ShigurePolyExpr)>,
    pub designated_obs_lift: Vec<(String, Vec<ShigureMemberCoordValue>)>,
    pub raw_read_diff: Option<ShigureRawReadComparison>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureDeclarationContext {
    pub name: String,
    pub vars: Vec<String>,
    pub laws: Vec<String>,
    pub observations: Vec<ShigureNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureTwoContextCech {
    pub left_context: String,
    pub right_context: String,
    pub shared_vars: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureDeclarationCover {
    pub contexts: Vec<ShigureDeclarationContext>,
    pub two_context_cech: Option<ShigureTwoContextCech>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureAffineAllowed {
    pub allowed_vars: Vec<String>,
    pub finite_displacement: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureRedundantComparison {
    pub reference_laws: Vec<ShigureNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureFiniteEtaleDescent {
    pub base_var: String,
    pub cover_var: String,
    pub degree: u32,
    pub base_invertible: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureLiftTask {
    pub name: String,
    pub reading: String,
    pub coeff_domain: ShigureCoeffDomain,
    pub origins: Vec<ShigureOriginRef>,
    pub variables: Vec<String>,
    pub ring_params: Vec<ShigureRingParam>,
    pub laws: Vec<ShigureNamedPoly>,
    pub extension: ShigureSquareZeroSpec,
    pub base_point: Vec<(String, Vec<ShigureMemberCoordValue>)>,
    pub ambient_lift: Option<Vec<(String, Vec<ShigureMemberCoordValue>)>>,
    pub relative_reading: Option<ShigureRelativeReading>,
    pub declaration_cover: Option<ShigureDeclarationCover>,
    pub affine_allowed: Option<ShigureAffineAllowed>,
    pub redundant_comparison: Option<ShigureRedundantComparison>,
    pub etale_descent: Option<ShigureFiniteEtaleDescent>,
    pub max_syzygy_pairs: Option<usize>,
    pub span: Span,
}

// ---- `shigure artin` 未解決 AST ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAuxiliaryDef {
    pub name: Ident,
    pub expr: ShigurePolyExpr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCompositeStage {
    pub aux_defs: Vec<RawAuxiliaryDef>,
    pub extra_laws: Vec<RawNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawArtinBaseChange {
    pub target_domain: RawCoeffDomain,
    pub test_order: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawArtinTask {
    pub name: Ident,
    pub domain: RawCoeffDomain,
    pub origins: Vec<RawOriginRef>,
    pub obs_vars: Vec<Ident>,
    pub obs_relations: Vec<RawNamedPoly>,
    pub aux_defs: Vec<RawAuxiliaryDef>,
    pub extra_laws: Vec<RawNamedPoly>,
    pub base_point: Vec<(Ident, RawMemberCoordValue, Span)>,
    pub max_order: usize,
    pub max_artin_dim: Option<usize>,
    pub composite_stage: Option<RawCompositeStage>,
    pub base_change: Option<RawArtinBaseChange>,
    pub non_noetherian_infinite: bool,
    pub span: Span,
}

// ---- `shigure artin` 検査済みモデル ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureAuxiliaryDef {
    pub name: String,
    pub expr: ShigurePolyExpr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureCompositeStage {
    pub aux_defs: Vec<ShigureAuxiliaryDef>,
    pub extra_laws: Vec<ShigureNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureArtinBaseChange {
    pub target_domain: ShigureCoeffDomain,
    pub test_order: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureArtinTask {
    pub name: String,
    pub reading: String,
    pub coeff_domain: ShigureCoeffDomain,
    pub origins: Vec<ShigureOriginRef>,
    pub obs_vars: Vec<String>,
    pub obs_relations: Vec<ShigureNamedPoly>,
    pub aux_defs: Vec<ShigureAuxiliaryDef>,
    pub extra_laws: Vec<ShigureNamedPoly>,
    pub base_point: Vec<(String, ShigureMemberCoordValue)>,
    pub max_order: usize,
    pub max_artin_dim: Option<usize>,
    pub composite_stage: Option<ShigureCompositeStage>,
    pub base_change: Option<ShigureArtinBaseChange>,
    pub non_noetherian_infinite: bool,
    pub span: Span,
}
