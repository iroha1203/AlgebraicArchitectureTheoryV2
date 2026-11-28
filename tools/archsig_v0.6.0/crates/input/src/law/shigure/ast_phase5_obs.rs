//! `shigure occurrence`・`shigure partial` 宣言の未解決 AST および検査済み入力モデル（Phase 5 / AC2）。

use super::RawCoeffDomain;
use super::ShigureCoeffDomain;
use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::{
    RawMemberCoordValue, RawOriginRef, ShigureMemberCoordValue, ShigureOriginRef,
};
use crate::law::ast::{Ident, QName, Span};

pub type RawSymbol = (String, Span);
pub type RawSortDef = (Ident, Vec<RawSymbol>, Span);
pub type RawIdentityRequest = (Ident, RawSymbol, RawSymbol, Span);
pub type RawOpenOpEntry = (Vec<RawSymbol>, Option<RawSymbol>, Span);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOpenSide {
    pub sorts: Vec<RawSortDef>,
    pub ops: Vec<RawOpenOpTable>,
    pub rels: Vec<RawOpenRelTable>,
}

/// 記号値（識別子・文字列リテラル・整数リテラル）または `observed` / `missing` 参照。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawSymbolicValue {
    Literal(String, Span),
    ObservedField { field: QName, span: Span },
    Missing(Span),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureSymbolicValue {
    Literal(String),
    ObservedField {
        entity: String,
        field: String,
        span: Span,
    },
    Missing,
}

// ---- `shigure occurrence`（第17章）----

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOccurrenceSort {
    pub name: Ident,
    pub elements: Vec<(String, Span)>,
    pub is_fixed_value: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOccurrenceSort {
    pub name: String,
    pub elements: Vec<String>,
    pub is_fixed_value: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOccurrenceOp {
    pub name: Ident,
    pub arg_sorts: Vec<Ident>,
    pub out_sort: Ident,
    pub is_total: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOccurrenceOp {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub out_sort: String,
    pub is_total: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOccurrenceRel {
    pub name: Ident,
    pub arg_sorts: Vec<Ident>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOccurrenceRel {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOccurrenceOpRecord {
    pub op_name: Ident,
    pub args: Vec<(String, Span)>,
    pub output: RawSymbolicValue,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOccurrenceOpRecord {
    pub op_name: String,
    pub arg_sorts: Vec<String>,
    pub out_sort: String,
    pub args: Vec<String>,
    pub output: ShigureSymbolicValue,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OccurrencePredKind {
    Domain,
    Relation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOccurrencePredRecord {
    pub kind: OccurrencePredKind,
    pub name: Ident,
    pub args: Vec<(String, Span)>,
    pub holds: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOccurrencePredRecord {
    pub kind: OccurrencePredKind,
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub args: Vec<String>,
    pub holds: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOccurrenceReading {
    pub name: Ident,
    pub sort: Ident,
    pub values: Vec<((String, Span), Option<RawSymbolicValue>, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOccurrenceReading {
    pub name: String,
    pub sort: String,
    pub values: Vec<(String, Option<ShigureSymbolicValue>)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOccurrenceInitialReadout {
    pub sort: Ident,
    pub values: Vec<((String, Span), RawSymbolicValue, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOccurrenceInitialReadout {
    pub sort: String,
    pub values: Vec<(String, ShigureSymbolicValue)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOccurrenceTask {
    pub name: Ident,
    pub origins: Vec<RawOriginRef>,
    pub sorts: Vec<RawOccurrenceSort>,
    pub operations: Vec<RawOccurrenceOp>,
    pub relations: Vec<RawOccurrenceRel>,
    pub identity_requests: Vec<RawIdentityRequest>,
    pub op_records: Vec<RawOccurrenceOpRecord>,
    pub pred_records: Vec<RawOccurrencePredRecord>,
    pub base_readings: Vec<RawOccurrenceReading>,
    pub context_closed_17_5: Option<bool>,
    pub explicit_contexts: Vec<RawOccurrenceReading>,
    pub preserve_full_domains: Vec<Ident>,
    pub initial_readouts: Vec<RawOccurrenceInitialReadout>,
    pub max_congruence_steps: Option<usize>,
    pub max_partitions: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOccurrenceTask {
    pub name: String,
    pub reading: String,
    pub origins: Vec<ShigureOriginRef>,
    pub sorts: Vec<ShigureOccurrenceSort>,
    pub operations: Vec<ShigureOccurrenceOp>,
    pub relations: Vec<ShigureOccurrenceRel>,
    pub identity_requests: Vec<(String, String, String)>,
    pub op_records: Vec<ShigureOccurrenceOpRecord>,
    pub pred_records: Vec<ShigureOccurrencePredRecord>,
    pub base_readings: Vec<ShigureOccurrenceReading>,
    pub context_closed_17_5: bool,
    pub explicit_contexts: Vec<ShigureOccurrenceReading>,
    pub preserve_full_domains: Vec<String>,
    pub initial_readouts: Vec<ShigureOccurrenceInitialReadout>,
    pub max_congruence_steps: usize,
    pub max_partitions: usize,
    pub span: Span,
}

// ---- `shigure partial`（第18章）----

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawPartialValue {
    Known(RawSymbolicValue),
    ExplicitAbsent,
    UnobservedSlot(Ident),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigurePartialValue {
    Known(ShigureSymbolicValue),
    ExplicitAbsent,
    UnobservedSlot(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawPartialTruth {
    True,
    ExplicitAbsent,
    UnobservedSlot(Ident),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigurePartialTruth {
    True,
    ExplicitAbsent,
    UnobservedSlot(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPartialSlotDecl {
    pub name: Ident,
    pub sort: Ident,
    pub domain_values: Vec<(String, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigurePartialSlotDecl {
    pub name: String,
    pub sort: String,
    pub domain_values: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawBackgroundConstraint {
    SlotEquality(Ident, Ident, Span),
    SlotNotEqual(Ident, Ident, Span),
    OperationInjective(Ident, Span),
    OperationSurjective(Ident, Span),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureBackgroundConstraint {
    SlotEquality(String, String),
    SlotNotEqual(String, String),
    OperationInjective(String),
    OperationSurjective(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPartialRecord {
    pub id: Ident,
    pub kind: RawPartialRecordKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawPartialRecordKind {
    OpValue {
        op_name: Ident,
        args: Vec<(String, Span)>,
        value: RawPartialValue,
    },
    OpDomain {
        op_name: Ident,
        args: Vec<(String, Span)>,
        defined: RawPartialTruth,
    },
    OpGraph {
        op_name: Ident,
        args: Vec<(String, Span)>,
        output: (String, Span),
        present: RawPartialTruth,
    },
    Relation {
        rel_name: Ident,
        args: Vec<(String, Span)>,
        holds: RawPartialTruth,
    },
    SlotAssignment {
        slot: Ident,
        value: (String, Span),
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigurePartialRecord {
    pub id: String,
    pub kind: ShigurePartialRecordKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigurePartialRecordKind {
    OpValue {
        op_name: String,
        args: Vec<String>,
        value: ShigurePartialValue,
    },
    OpDomain {
        op_name: String,
        args: Vec<String>,
        defined: ShigurePartialTruth,
    },
    OpGraph {
        op_name: String,
        args: Vec<String>,
        output: String,
        present: ShigurePartialTruth,
    },
    Relation {
        rel_name: String,
        args: Vec<String>,
        holds: ShigurePartialTruth,
    },
    SlotAssignment {
        slot: String,
        value: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShigurePartialArithOp {
    Add,
    Sub,
    Mul,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawPartialTerm {
    IdentOrConst(Ident),
    ConstLit(String, Span),
    ExplicitConst(String, Span),
    Slot(Ident),
    App {
        op_name: Ident,
        args: Vec<RawPartialTerm>,
        span: Span,
    },
    Let {
        var: Ident,
        bound: Box<RawPartialTerm>,
        body: Box<RawPartialTerm>,
        span: Span,
    },
    BinOp {
        op: ShigurePartialArithOp,
        lhs: Box<RawPartialTerm>,
        rhs: Box<RawPartialTerm>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigurePartialTerm {
    Var(String),
    Const(String),
    Slot(String),
    App {
        op_name: String,
        args: Vec<ShigurePartialTerm>,
    },
    Let {
        var: String,
        bound: Box<ShigurePartialTerm>,
        body: Box<ShigurePartialTerm>,
    },
    BinOp {
        op: ShigurePartialArithOp,
        lhs: Box<ShigurePartialTerm>,
        rhs: Box<ShigurePartialTerm>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawPartialFormula {
    Eq(RawPartialTerm, RawPartialTerm, Span),
    Rel {
        rel_name: Ident,
        args: Vec<RawPartialTerm>,
        span: Span,
    },
    Graph {
        op_name: Ident,
        args: Vec<RawPartialTerm>,
        output: RawPartialTerm,
        span: Span,
    },
    Defined {
        op_name: Ident,
        args: Vec<RawPartialTerm>,
        span: Span,
    },
    Not(Box<RawPartialFormula>, Span),
    And(Vec<RawPartialFormula>, Span),
    Or(Vec<RawPartialFormula>, Span),
    Exists {
        var: Ident,
        sort: Ident,
        restricted_domain: Option<Vec<(String, Span)>>,
        body: Box<RawPartialFormula>,
        span: Span,
    },
    Forall {
        var: Ident,
        sort: Ident,
        restricted_domain: Option<Vec<(String, Span)>>,
        body: Box<RawPartialFormula>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigurePartialFormula {
    Eq(ShigurePartialTerm, ShigurePartialTerm),
    Rel {
        rel_name: String,
        args: Vec<ShigurePartialTerm>,
    },
    Graph {
        op_name: String,
        args: Vec<ShigurePartialTerm>,
        output: ShigurePartialTerm,
    },
    Defined {
        op_name: String,
        args: Vec<ShigurePartialTerm>,
    },
    Not(Box<ShigurePartialFormula>),
    And(Vec<ShigurePartialFormula>),
    Or(Vec<ShigurePartialFormula>),
    Exists {
        var: String,
        sort: String,
        restricted_domain: Option<Vec<String>>,
        body: Box<ShigurePartialFormula>,
    },
    Forall {
        var: String,
        sort: String,
        restricted_domain: Option<Vec<String>>,
        body: Box<ShigurePartialFormula>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPartialEvalLaw {
    pub name: Ident,
    pub antecedent: Option<RawPartialFormula>,
    pub conclusion: RawPartialFormula,
    pub is_required_law: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigurePartialEvalLaw {
    pub name: String,
    pub antecedent: Option<ShigurePartialFormula>,
    pub conclusion: ShigurePartialFormula,
    pub is_required_law: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawFinitePartial {
    pub sorts: Vec<RawSortDef>,
    pub operations: Vec<RawOccurrenceOp>,
    pub relations: Vec<RawOccurrenceRel>,
    pub slots: Vec<RawPartialSlotDecl>,
    pub background_constraints: Vec<RawBackgroundConstraint>,
    pub records: Vec<RawPartialRecord>,
    pub max_completions: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureFinitePartial {
    pub sorts: Vec<(String, Vec<String>)>,
    pub operations: Vec<ShigureOccurrenceOp>,
    pub relations: Vec<ShigureOccurrenceRel>,
    pub slots: Vec<ShigurePartialSlotDecl>,
    pub background_constraints: Vec<ShigureBackgroundConstraint>,
    pub records: Vec<ShigurePartialRecord>,
    pub max_completions: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAffineRow {
    pub id: Ident,
    pub coeffs: Vec<RawMemberCoordValue>,
    pub rhs: RawMemberCoordValue,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureAffineRow {
    pub id: String,
    pub coeffs: Vec<ShigureMemberCoordValue>,
    pub rhs: ShigureMemberCoordValue,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAffinePartial {
    pub domain: RawCoeffDomain,
    pub coord_names: Vec<Ident>,
    pub x0: Vec<RawMemberCoordValue>,
    pub direction_t: Vec<Vec<RawMemberCoordValue>>,
    pub background_rows: Vec<RawAffineRow>,
    pub record_rows: Vec<RawAffineRow>,
    pub eval_equations: Vec<RawAffineRow>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureAffinePartial {
    pub coeff_domain: ShigureCoeffDomain,
    pub coord_names: Vec<String>,
    pub x0: Vec<ShigureMemberCoordValue>,
    pub direction_t: Vec<Vec<ShigureMemberCoordValue>>,
    pub background_rows: Vec<ShigureAffineRow>,
    pub record_rows: Vec<ShigureAffineRow>,
    pub eval_equations: Vec<ShigureAffineRow>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawPartialRepresentation {
    FiniteTable(RawFinitePartial),
    Affine(RawAffinePartial),
    UnsupportedClass { description: String, span: Span },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigurePartialRepresentation {
    FiniteTable(ShigureFinitePartial),
    Affine(ShigureAffinePartial),
    UnsupportedClass { description: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawQuantifierCompletion {
    pub id: Ident,
    pub slot_values: Vec<(Ident, (String, Span), Span)>,
    pub valid_candidates: Vec<Ident>,
    pub output_value: (String, Span),
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureQuantifierCompletion {
    pub id: String,
    pub slot_values: Vec<(String, String)>,
    pub valid_candidates: Vec<String>,
    pub output_value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawQuantifierSpec {
    pub candidates: Vec<Ident>,
    pub completions: Vec<RawQuantifierCompletion>,
    pub max_steps: Option<usize>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureQuantifierSpec {
    pub candidates: Vec<String>,
    pub completions: Vec<ShigureQuantifierCompletion>,
    pub max_steps: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOpenOpTable {
    pub name: Ident,
    pub arg_sorts: Vec<Ident>,
    pub out_sort: Ident,
    pub entries: Vec<RawOpenOpEntry>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOpenOpTable {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub out_sort: String,
    pub entries: Vec<(Vec<String>, Option<String>)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOpenRelTable {
    pub name: Ident,
    pub arg_sorts: Vec<Ident>,
    pub entries: Vec<(Vec<(String, Span)>, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOpenRelTable {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub entries: Vec<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawFiberCoverageCheck {
    pub op_name: Ident,
    pub arg_sort: Ident,
    pub target_sort: Ident,
    pub known_targets: Vec<(String, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureFiberCoverageCheck {
    pub op_name: String,
    pub arg_sort: String,
    pub target_sort: String,
    pub known_targets: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAffineRestriction {
    pub domain: RawCoeffDomain,
    pub m_matrix: Vec<Vec<ShigureScalarLit>>,
    pub b_rhs: Vec<ShigureScalarLit>,
    pub r_matrix: Vec<Vec<ShigureScalarLit>>,
    pub num_vars: usize,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureAffineRestriction {
    pub coeff_domain: ShigureCoeffDomain,
    pub m_matrix: Vec<Vec<ShigureScalarLit>>,
    pub b_rhs: Vec<ShigureScalarLit>,
    pub r_matrix: Vec<Vec<ShigureScalarLit>>,
    pub num_vars: usize,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOpenDomain {
    pub substructure_sorts: Vec<RawSortDef>,
    pub ambient_sorts: Vec<RawSortDef>,
    pub substructure_ops: Vec<RawOpenOpTable>,
    pub ambient_ops: Vec<RawOpenOpTable>,
    pub substructure_rels: Vec<RawOpenRelTable>,
    pub ambient_rels: Vec<RawOpenRelTable>,
    pub fiber_checks: Vec<RawFiberCoverageCheck>,
    pub positive_or_law: RawPartialEvalLaw,
    pub affine_restriction: Option<RawAffineRestriction>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOpenDomain {
    pub substructure_sorts: Vec<(String, Vec<String>)>,
    pub ambient_sorts: Vec<(String, Vec<String>)>,
    pub substructure_ops: Vec<ShigureOpenOpTable>,
    pub ambient_ops: Vec<ShigureOpenOpTable>,
    pub substructure_rels: Vec<ShigureOpenRelTable>,
    pub ambient_rels: Vec<ShigureOpenRelTable>,
    pub fiber_checks: Vec<ShigureFiberCoverageCheck>,
    pub positive_or_law: ShigurePartialEvalLaw,
    pub affine_restriction: Option<ShigureAffineRestriction>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPartialTask {
    pub name: Ident,
    pub origins: Vec<RawOriginRef>,
    pub representation: RawPartialRepresentation,
    pub eval_laws: Vec<RawPartialEvalLaw>,
    pub quantifier_spec: Option<RawQuantifierSpec>,
    pub open_domain: Option<RawOpenDomain>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigurePartialTask {
    pub name: String,
    pub reading: String,
    pub origins: Vec<ShigureOriginRef>,
    pub representation: ShigurePartialRepresentation,
    pub eval_laws: Vec<ShigurePartialEvalLaw>,
    pub quantifier_spec: Option<ShigureQuantifierSpec>,
    pub open_domain: Option<ShigureOpenDomain>,
    pub span: Span,
}
