//! `archsig.law/2` 内の最小 SHIGURE 宣言 AST・検査済み宣言モデル。
//!
//! 既存の `view` / `law` / `local` / `change` / `relation` と独立し、
//! 予約語を追加せず文脈キーワード `shigure` で導入する。
//! 残差 ideal・空性 witness・解・相互作用要約などの結論注入は構文・検査段階で明示拒否する。

pub mod ast_ext;
pub mod check;
mod check_diagram;
mod check_ext_common;
mod check_path;
mod check_relations;
mod check_transfer;
pub mod parser;
mod parser_diagram_path;
mod parser_transfer;

pub use ast_ext::*;

use super::ast::{Ident, QName, Span};
use num_bigint::{BigInt, BigUint};
use std::collections::BTreeMap;

/// 結論注入として入力を明示拒否する予約欄名（R2.3 / Failure Contract #4）。
pub const FORBIDDEN_CONCLUSION_FIELDS: &[&str] = &[
    "residual_ideal",
    "residuals",
    "empty_witness",
    "witness",
    "solution",
    "solutions",
    "interaction",
    "interaction_summary",
    "participating_variables",
    "minimal_failing_subsets",
    "verdict",
    "restored",
    "reeval",
    "groebner_basis",
    "completed_diagram",
    "restored_diagram",
    "diagram_solution",
    "commutativity_residuals",
    "edge_results",
    "computed_path",
    "computed_paths",
    "restored_path",
    "restored_paths",
    "path_solution",
    "path_solutions",
    "rejected_candidates",
    "subdivision_fiber",
    "composite_morphism",
    "composite_is_one_step",
    "associativity_checked",
    "transfer_verdict",
    "transfer_result",
    "restored_transfer",
    "restored_steps",
    "common_domain",
    "common_domains",
    "composed_domain",
    "composed_domain_relation",
    "word_check_results",
    "old_word_lift_results",
    "lift_found",
    "domain_nonempty",
];

pub fn is_forbidden_conclusion_field(name: &str) -> bool {
    FORBIDDEN_CONCLUSION_FIELDS.contains(&name)
}

/// SHIGURE 係数域。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureCoeffDomain {
    Z,
    Q,
    Fp(BigUint),
}

/// SHIGURE 点集合域。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigurePointDomain {
    AlgebraicClosure,
    RationalPoints,
    IntegerPoints,
    FiniteFieldPoints(BigUint),
    UniversalRing,
}

/// 守る意味 Law と編集可能な表示 Law の区別。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShigureLawKind {
    Semantic,
    Representation,
}

/// SHIGURE 宣言内の多項式式。深い木でもスタックを枯渇させないよう、
/// `Clone` / `PartialEq` は `stacker`、解放は反復 `Drop` を用いる。
#[derive(Debug, Eq)]
pub enum ShigurePolyExpr {
    Int(BigInt),
    Rat { num: BigInt, den: BigInt },
    Fp { value: BigUint, modulus: BigUint },
    Var(String),
    Neg(Box<ShigurePolyExpr>),
    Add(Box<ShigurePolyExpr>, Box<ShigurePolyExpr>),
    Sub(Box<ShigurePolyExpr>, Box<ShigurePolyExpr>),
    Mul(Box<ShigurePolyExpr>, Box<ShigurePolyExpr>),
    Pow(Box<ShigurePolyExpr>, u32),
}

const POLY_RED_ZONE: usize = 64 * 1024;
const POLY_STACK_STEP: usize = 1024 * 1024;

impl Clone for ShigurePolyExpr {
    fn clone(&self) -> Self {
        stacker::maybe_grow(POLY_RED_ZONE, POLY_STACK_STEP, || match self {
            ShigurePolyExpr::Int(n) => ShigurePolyExpr::Int(n.clone()),
            ShigurePolyExpr::Rat { num, den } => ShigurePolyExpr::Rat {
                num: num.clone(),
                den: den.clone(),
            },
            ShigurePolyExpr::Fp { value, modulus } => ShigurePolyExpr::Fp {
                value: value.clone(),
                modulus: modulus.clone(),
            },
            ShigurePolyExpr::Var(s) => ShigurePolyExpr::Var(s.clone()),
            ShigurePolyExpr::Neg(a) => ShigurePolyExpr::Neg(Box::new((**a).clone())),
            ShigurePolyExpr::Add(a, b) => {
                ShigurePolyExpr::Add(Box::new((**a).clone()), Box::new((**b).clone()))
            }
            ShigurePolyExpr::Sub(a, b) => {
                ShigurePolyExpr::Sub(Box::new((**a).clone()), Box::new((**b).clone()))
            }
            ShigurePolyExpr::Mul(a, b) => {
                ShigurePolyExpr::Mul(Box::new((**a).clone()), Box::new((**b).clone()))
            }
            ShigurePolyExpr::Pow(a, e) => ShigurePolyExpr::Pow(Box::new((**a).clone()), *e),
        })
    }
}

impl PartialEq for ShigurePolyExpr {
    fn eq(&self, other: &Self) -> bool {
        stacker::maybe_grow(POLY_RED_ZONE, POLY_STACK_STEP, || match (self, other) {
            (ShigurePolyExpr::Int(a), ShigurePolyExpr::Int(b)) => a == b,
            (
                ShigurePolyExpr::Rat { num: n1, den: d1 },
                ShigurePolyExpr::Rat { num: n2, den: d2 },
            ) => n1 == n2 && d1 == d2,
            (
                ShigurePolyExpr::Fp {
                    value: v1,
                    modulus: m1,
                },
                ShigurePolyExpr::Fp {
                    value: v2,
                    modulus: m2,
                },
            ) => v1 == v2 && m1 == m2,
            (ShigurePolyExpr::Var(a), ShigurePolyExpr::Var(b)) => a == b,
            (ShigurePolyExpr::Neg(a), ShigurePolyExpr::Neg(b)) => **a == **b,
            (ShigurePolyExpr::Add(a1, a2), ShigurePolyExpr::Add(b1, b2))
            | (ShigurePolyExpr::Sub(a1, a2), ShigurePolyExpr::Sub(b1, b2))
            | (ShigurePolyExpr::Mul(a1, a2), ShigurePolyExpr::Mul(b1, b2)) => {
                **a1 == **b1 && **a2 == **b2
            }
            (ShigurePolyExpr::Pow(a, e1), ShigurePolyExpr::Pow(b, e2)) => e1 == e2 && **a == **b,
            _ => false,
        })
    }
}

impl Drop for ShigurePolyExpr {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_poly_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            take_poly_children(&mut node, &mut stack);
        }
    }
}

fn take_poly_children(expr: &mut ShigurePolyExpr, stack: &mut Vec<ShigurePolyExpr>) {
    let zero = || ShigurePolyExpr::Int(BigInt::from(0));
    match expr {
        ShigurePolyExpr::Neg(a) | ShigurePolyExpr::Pow(a, _) => {
            stack.push(std::mem::replace(&mut **a, zero()));
        }
        ShigurePolyExpr::Add(a, b) | ShigurePolyExpr::Sub(a, b) | ShigurePolyExpr::Mul(a, b) => {
            stack.push(std::mem::replace(&mut **a, zero()));
            stack.push(std::mem::replace(&mut **b, zero()));
        }
        ShigurePolyExpr::Int(_)
        | ShigurePolyExpr::Rat { .. }
        | ShigurePolyExpr::Fp { .. }
        | ShigurePolyExpr::Var(_) => {}
    }
}

// ---- 未解決 AST ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawCoeffDomain {
    Z(Span),
    Q(Span),
    Fp { modulus: String, span: Span },
}

impl RawCoeffDomain {
    pub fn span(&self) -> Span {
        match self {
            RawCoeffDomain::Z(s) | RawCoeffDomain::Q(s) | RawCoeffDomain::Fp { span: s, .. } => *s,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawPointDomain {
    AlgebraicClosure(Span),
    RationalPoints(Span),
    IntegerPoints(Span),
    FiniteFieldPoints { modulus: String, span: Span },
    UniversalRing(Span),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawCoordBinding {
    Symbolic,
    ObservedField { field: QName, span: Span },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCoordDecl {
    pub name: Ident,
    pub sort: Ident,
    pub binding: RawCoordBinding,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawStateLawDecl {
    pub name: Ident,
    pub kind: ShigureLawKind,
    pub expr: ShigurePolyExpr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPhaseDecl {
    pub name: Ident,
    pub coords: Vec<RawCoordDecl>,
    pub state_laws: Vec<RawStateLawDecl>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSortDecl {
    pub name: Ident,
    pub rank: usize,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawOperationDecl {
    pub name: Ident,
    pub source_phase: Ident,
    pub target_phase: Ident,
    pub args: Vec<(Ident, Ident)>,
    pub domain_laws: Vec<RawStateLawDecl>,
    pub updates: Vec<(Ident, ShigurePolyExpr)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawObservationDecl {
    pub name: Ident,
    pub phase: Ident,
    pub components: Vec<ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawPresentation {
    pub name: Ident,
    pub domain: RawCoeffDomain,
    pub sorts: Vec<RawSortDecl>,
    pub phases: Vec<RawPhaseDecl>,
    pub operations: Vec<RawOperationDecl>,
    pub observations: Vec<RawObservationDecl>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawStateComparison {
    pub after_phase: Ident,
    pub before_phase: Ident,
    pub map: Vec<(Ident, ShigurePolyExpr)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawTranslatedStep {
    pub before_operation: Ident,
    pub arg_exprs: Vec<ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawTranslatedWord {
    pub after_operation: Ident,
    pub steps: Vec<RawTranslatedStep>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawComparison {
    pub name: Ident,
    pub before: QName,
    pub after: QName,
    pub state_comparisons: Vec<RawStateComparison>,
    pub word_translation: Vec<RawTranslatedWord>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawParamDecl {
    pub name: Ident,
    pub domain: RawCoeffDomain,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawFixedTarget {
    SemanticLaw(QName),
    RepresentationLaw(QName),
    OperationExpr(QName),
    ObservationExpr(QName),
    StateComparisonExpr(Ident),
    WordTranslationOp(Ident),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawEditableTarget {
    OperationExpr(QName),
    RepresentationLaw(QName),
    StateComparisonExpr(Ident),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawChangeSpec {
    pub name: Ident,
    pub domain: RawCoeffDomain,
    pub parameters: Vec<RawParamDecl>,
    pub fixed: Vec<(RawFixedTarget, Span)>,
    pub editable: Vec<(RawEditableTarget, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawNamedPoly {
    pub name: Ident,
    pub expr: ShigurePolyExpr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawEvalCondition {
    pub name: Ident,
    pub point_domain: RawPointDomain,
    pub evaluations: Vec<RawNamedPoly>,
    pub equations: Vec<RawNamedPoly>,
    pub invertibles: Vec<RawNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawTask {
    pub name: Ident,
    pub comparison: QName,
    pub change_spec: QName,
    pub eval_condition: Option<QName>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureDeclAst {
    Presentation(RawPresentation),
    Comparison(RawComparison),
    ChangeSpec(RawChangeSpec),
    EvalCondition(RawEvalCondition),
    Task(RawTask),
    Diagram(RawDiagramTask),
    Path(Box<RawPathTask>),
    Transfer(RawTransferTask),
}

impl ShigureDeclAst {
    pub fn name(&self) -> &Ident {
        match self {
            ShigureDeclAst::Presentation(p) => &p.name,
            ShigureDeclAst::Comparison(c) => &c.name,
            ShigureDeclAst::ChangeSpec(h) => &h.name,
            ShigureDeclAst::EvalCondition(e) => &e.name,
            ShigureDeclAst::Task(t) => &t.name,
            ShigureDeclAst::Diagram(d) => &d.name,
            ShigureDeclAst::Path(p) => &p.name,
            ShigureDeclAst::Transfer(t) => &t.name,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            ShigureDeclAst::Presentation(p) => p.span,
            ShigureDeclAst::Comparison(c) => c.span,
            ShigureDeclAst::ChangeSpec(h) => h.span,
            ShigureDeclAst::EvalCondition(e) => e.span,
            ShigureDeclAst::Task(t) => t.span,
            ShigureDeclAst::Diagram(d) => d.span,
            ShigureDeclAst::Path(p) => p.span,
            ShigureDeclAst::Transfer(t) => t.span,
        }
    }
}

// ---- 検査済みモデル ----

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShigureCoordBinding {
    Symbolic,
    /// 共通 Atom 定義の原始 field 完全名（`Namespace.Entity.field`）。
    ObservedField {
        entity: String,
        field: String,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureCoordDecl {
    pub name: String,
    pub sort: String,
    pub binding: ShigureCoordBinding,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureStateLawDecl {
    pub name: String,
    pub kind: ShigureLawKind,
    pub expr: ShigurePolyExpr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigurePhaseDecl {
    pub name: String,
    pub coords: Vec<ShigureCoordDecl>,
    pub state_laws: Vec<ShigureStateLawDecl>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureSortDecl {
    pub name: String,
    pub rank: usize,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureOperationDecl {
    pub name: String,
    pub source_phase: String,
    pub target_phase: String,
    pub args: Vec<(String, String)>,
    pub domain_laws: Vec<ShigureStateLawDecl>,
    pub updates: Vec<(String, ShigurePolyExpr)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureObservationDecl {
    pub name: String,
    pub phase: String,
    pub components: Vec<ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigurePresentation {
    pub name: String,
    pub reading: String,
    pub coeff_domain: ShigureCoeffDomain,
    pub sorts: Vec<ShigureSortDecl>,
    pub phases: Vec<ShigurePhaseDecl>,
    pub operations: Vec<ShigureOperationDecl>,
    pub observations: Vec<ShigureObservationDecl>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureStateComparison {
    pub after_phase: String,
    pub before_phase: String,
    pub map: Vec<(String, ShigurePolyExpr)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureTranslatedStep {
    pub before_operation: String,
    pub arg_exprs: Vec<ShigurePolyExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureTranslatedWord {
    pub after_operation: String,
    pub steps: Vec<ShigureTranslatedStep>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureComparison {
    pub name: String,
    pub reading: String,
    pub before: String,
    pub after: String,
    pub state_comparisons: Vec<ShigureStateComparison>,
    pub word_translation: Vec<ShigureTranslatedWord>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureParamDecl {
    pub name: String,
    pub coeff_domain: ShigureCoeffDomain,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ShigureFixedTarget {
    SemanticLaw {
        presentation: String,
        phase: String,
        law: String,
    },
    RepresentationLaw {
        presentation: String,
        phase: String,
        law: String,
    },
    OperationExpr {
        presentation: String,
        operation: String,
    },
    ObservationExpr {
        presentation: String,
        phase: String,
        observation: String,
    },
    StateComparisonExpr {
        after_phase: String,
    },
    WordTranslationOp {
        operation: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ShigureEditableTarget {
    OperationExpr {
        presentation: String,
        operation: String,
    },
    RepresentationLaw {
        presentation: String,
        phase: String,
        law: String,
    },
    StateComparisonExpr {
        after_phase: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureChangeSpec {
    pub name: String,
    pub reading: String,
    pub coeff_domain: ShigureCoeffDomain,
    pub parameters: Vec<ShigureParamDecl>,
    pub fixed: Vec<(ShigureFixedTarget, Span)>,
    pub editable: Vec<(ShigureEditableTarget, Span)>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureNamedPoly {
    pub name: String,
    pub expr: ShigurePolyExpr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureEvalCondition {
    pub name: String,
    pub reading: String,
    pub point_domain: ShigurePointDomain,
    pub evaluations: Vec<ShigureNamedPoly>,
    pub equations: Vec<ShigureNamedPoly>,
    pub invertibles: Vec<ShigureNamedPoly>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShigureTask {
    pub name: String,
    pub reading: String,
    pub comparison: String,
    pub change_spec: String,
    pub eval_condition: Option<String>,
    pub span: Span,
}

/// `CheckedLaw` に格納される検査済み SHIGURE 宣言表（完全名 `Reading.Name` をキーとする）。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckedShigureDecls {
    pub presentations: BTreeMap<String, ShigurePresentation>,
    pub comparisons: BTreeMap<String, ShigureComparison>,
    pub change_specs: BTreeMap<String, ShigureChangeSpec>,
    pub eval_conditions: BTreeMap<String, ShigureEvalCondition>,
    pub tasks: BTreeMap<String, ShigureTask>,
    pub diagrams: BTreeMap<String, ShigureDiagramTask>,
    pub paths: BTreeMap<String, ShigurePathTask>,
    pub transfers: BTreeMap<String, ShigureTransferTask>,
}

impl CheckedShigureDecls {
    pub fn is_empty(&self) -> bool {
        self.presentations.is_empty()
            && self.comparisons.is_empty()
            && self.change_specs.is_empty()
            && self.eval_conditions.is_empty()
            && self.tasks.is_empty()
            && self.diagrams.is_empty()
            && self.paths.is_empty()
            && self.transfers.is_empty()
    }
}
