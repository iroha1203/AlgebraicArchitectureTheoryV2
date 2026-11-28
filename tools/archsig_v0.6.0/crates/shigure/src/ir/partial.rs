//! AAT 第18章（部分提示・欠測と開領域の確定評価）の検証済み IR
//! （`PartialTaskSpec` / `CheckedPartialTask`）。

use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::ir::validate::{
    ValidationError, require_non_empty, validate_coeff_domain, validate_provenance,
    validate_scalar_lit,
};
use std::collections::{BTreeMap, BTreeSet};

/// 値スロット付き部分提示の値（既知値・明示不在・名前付き未観測スロットを型で分離）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartialValue {
    Known(String),
    ExplicitAbsent,
    UnobservedSlot(String),
}

/// 真偽スロット付き部分提示の値（成立・明示不在・名前付き未観測スロットを型で分離）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartialTruth {
    True,
    ExplicitAbsent,
    UnobservedSlot(String),
}

/// 名前付き未観測スロット宣言 $\xi \in \Xi$。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialSlotDecl {
    pub name: String,
    pub sort: String,
    pub domain_values: Vec<String>,
}

/// 部分提示の背景構造制約（評価対象 Law とは別管理する）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BackgroundConstraint {
    SlotEquality(String, String),
    SlotNotEqual(String, String),
    OperationInjective(String),
    OperationSurjective(String),
}

/// 部分提示記録（定義 18.1）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialRecordSpec {
    pub id: String,
    pub kind: PartialRecordKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartialRecordKind {
    OpValue {
        op_name: String,
        args: Vec<String>,
        value: PartialValue,
    },
    OpDomain {
        op_name: String,
        args: Vec<String>,
        defined: PartialTruth,
    },
    OpGraph {
        op_name: String,
        args: Vec<String>,
        output: String,
        present: PartialTruth,
    },
    Relation {
        rel_name: String,
        args: Vec<String>,
        holds: PartialTruth,
    },
    SlotAssignment {
        slot: String,
        value: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PartialArithOp {
    Add,
    Sub,
    Mul,
}

/// 強 Kleene / 超評価用の項構文木（正格 `let` 束縛を含む）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartialTerm {
    Var(String),
    Const(String),
    Slot(String),
    App {
        op_name: String,
        args: Vec<PartialTerm>,
    },
    Let {
        var: String,
        bound: Box<PartialTerm>,
        body: Box<PartialTerm>,
    },
    BinOp {
        op: PartialArithOp,
        lhs: Box<PartialTerm>,
        rhs: Box<PartialTerm>,
    },
}

/// 強 Kleene / 超評価 / 開領域用の論理式構文木。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartialFormula {
    Eq(PartialTerm, PartialTerm),
    Rel {
        rel_name: String,
        args: Vec<PartialTerm>,
    },
    Graph {
        op_name: String,
        args: Vec<PartialTerm>,
        output: PartialTerm,
    },
    Defined {
        op_name: String,
        args: Vec<PartialTerm>,
    },
    Not(Box<PartialFormula>),
    And(Vec<PartialFormula>),
    Or(Vec<PartialFormula>),
    Exists {
        var: String,
        sort: String,
        restricted_domain: Option<Vec<String>>,
        body: Box<PartialFormula>,
    },
    Forall {
        var: String,
        sort: String,
        restricted_domain: Option<Vec<String>>,
        body: Box<PartialFormula>,
    },
}

/// 評価対象 Law $\ell = (\iota \vdash \chi)$（背景制約から厳密分離）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialEvalLawSpec {
    pub name: String,
    pub antecedent: Option<PartialFormula>,
    pub conclusion: PartialFormula,
    pub is_required_law: bool,
}

/// 有限表補完仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinitePartialPresentation {
    pub sorts: BTreeMap<String, Vec<String>>,
    pub operations: Vec<PartialOpSignature>,
    pub relations: Vec<PartialPredSignature>,
    pub slots: Vec<PartialSlotDecl>,
    pub background_constraints: Vec<BackgroundConstraint>,
    pub records: Vec<PartialRecordSpec>,
    pub max_completions: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialOpSignature {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub out_sort: String,
    pub is_total: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialPredSignature {
    pub name: String,
    pub arg_sorts: Vec<String>,
}

/// アフィン表示 $x = x_0 + T t, C x = d$（定理 18.3・命題 18.9）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffinePartialPresentation {
    pub coeff_domain: CoeffDomain,
    pub coord_names: Vec<String>,
    pub x0: Vec<ScalarLit>,
    /// 各列が生成方向ベクトルとなる行列 $T$（行数 = `coord_names.len()`）。
    pub direction_t: Vec<Vec<ScalarLit>>,
    /// 背景制約行 `(record_id, row_coeffs, rhs)`。
    pub background_rows: Vec<(String, Vec<ScalarLit>, ScalarLit)>,
    /// 個別記録行 `(record_id, row_coeffs, rhs)`（MUS 抽出時に行単位で削除可能）。
    pub record_rows: Vec<(String, Vec<ScalarLit>, ScalarLit)>,
    /// 評価対象のアフィン等式系 $B x = e$（補完条件には混入しない）。
    pub eval_equations: Vec<(String, Vec<ScalarLit>, ScalarLit)>,
}

/// 部分提示の表現クラス。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartialRepresentation {
    FiniteTable(FinitePartialPresentation),
    Affine(AffinePartialPresentation),
    UnsupportedClass { description: String },
}

/// 解の量化 4 階層 $E/U/G/Q$ と必要スロット（定義 18.10・命題 18.11・定理 18.12）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuantifierHierarchySpec {
    pub candidates: Vec<String>,
    /// 各補完ごとの `(completion_id, slot_values, valid_candidates, output_value)`。
    pub completions: Vec<QuantifierCompletionSpec>,
    pub max_steps: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuantifierCompletionSpec {
    pub id: String,
    pub slot_values: BTreeMap<String, String>,
    pub valid_candidates: Vec<String>,
    pub output_value: String,
}

/// 開領域の局所網羅・正の式保存・アフィン制限一意修復仕様（§18.4–18.5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenDomainSpec {
    pub substructure_carriers: BTreeMap<String, Vec<String>>,
    pub ambient_carriers: BTreeMap<String, Vec<String>>,
    pub substructure_ops: Vec<OpenOpTable>,
    pub ambient_ops: Vec<OpenOpTable>,
    pub substructure_rels: Vec<OpenRelTable>,
    pub ambient_rels: Vec<OpenRelTable>,
    /// 参照操作と既知個体集合 $B$ によるファイバー（合併・非空交差で構成する範囲）。
    pub fiber_checks: Vec<FiberCoverageCheckSpec>,
    pub positive_or_law: PartialEvalLawSpec,
    pub affine_restriction: Option<AffineRestrictionSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenOpTable {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub out_sort: String,
    pub entries: BTreeMap<Vec<String>, Option<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenRelTable {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub entries: BTreeSet<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiberCoverageCheckSpec {
    pub op_name: String,
    pub arg_sort: String,
    pub target_sort: String,
    pub known_targets: Vec<String>,
}

/// アフィン制限 $r: S_F \to S_C$ による大域一意修復検査（定理 18.18）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineRestrictionSpec {
    pub coeff_domain: CoeffDomain,
    pub m_matrix: Vec<Vec<ScalarLit>>,
    pub b_rhs: Vec<ScalarLit>,
    pub r_matrix: Vec<Vec<ScalarLit>>,
    pub num_vars: usize,
}

/// 部分提示タスク仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialTaskSpec {
    pub name: String,
    pub representation: PartialRepresentation,
    pub eval_laws: Vec<PartialEvalLawSpec>,
    pub quantifier_spec: Option<QuantifierHierarchySpec>,
    pub open_domain: Option<OpenDomainSpec>,
    pub provenance: Provenance,
    pub undeclared_unobserved_slots: Vec<String>,
}

/// 検証済みの部分提示タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedPartialTask {
    name: String,
    representation: PartialRepresentation,
    eval_laws: Vec<PartialEvalLawSpec>,
    quantifier_spec: Option<QuantifierHierarchySpec>,
    open_domain: Option<OpenDomainSpec>,
    provenance: Provenance,
    undeclared_unobserved_slots: Vec<String>,
}

impl CheckedPartialTask {
    pub fn validate(spec: PartialTaskSpec) -> Result<Self, ValidationError> {
        validate_partial_task(spec)
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn representation(&self) -> &PartialRepresentation {
        &self.representation
    }

    pub fn eval_laws(&self) -> &[PartialEvalLawSpec] {
        &self.eval_laws
    }

    pub fn quantifier_spec(&self) -> Option<&QuantifierHierarchySpec> {
        self.quantifier_spec.as_ref()
    }

    pub fn open_domain(&self) -> Option<&OpenDomainSpec> {
        self.open_domain.as_ref()
    }

    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }

    pub fn undeclared_unobserved_slots(&self) -> &[String] {
        &self.undeclared_unobserved_slots
    }
}

pub fn validate_partial_task(spec: PartialTaskSpec) -> Result<CheckedPartialTask, ValidationError> {
    require_non_empty(&spec.name, "partial.name")?;
    validate_provenance(&spec.provenance, &format!("partial `{}`", spec.name))?;

    match &spec.representation {
        PartialRepresentation::FiniteTable(fin) => validate_finite_partial(fin, &spec.eval_laws)?,
        PartialRepresentation::Affine(aff) => validate_affine_partial(aff)?,
        PartialRepresentation::UnsupportedClass { description } => {
            require_non_empty(description, "partial.unsupported_class.description")?;
        }
    }

    if let Some(q) = &spec.quantifier_spec {
        if q.candidates.is_empty() && q.completions.is_empty() {
            return Err(ValidationError::ConversionError {
                detail: "quantifier_spec cannot have both empty candidates and empty completions"
                    .to_owned(),
            });
        }
        let cand_set: BTreeSet<&str> = q.candidates.iter().map(String::as_str).collect();
        for comp in &q.completions {
            require_non_empty(&comp.id, "partial.quantifier.completion.id")?;
            for vc in &comp.valid_candidates {
                if !cand_set.contains(vc.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "candidate",
                        name: vc.clone(),
                        context: format!("quantifier completion `{}`", comp.id),
                    });
                }
            }
        }
    }

    if let Some(od) = &spec.open_domain {
        validate_open_domain(od)?;
    }

    Ok(CheckedPartialTask {
        name: spec.name,
        representation: spec.representation,
        eval_laws: spec.eval_laws,
        quantifier_spec: spec.quantifier_spec,
        open_domain: spec.open_domain,
        provenance: spec.provenance,
        undeclared_unobserved_slots: spec.undeclared_unobserved_slots,
    })
}

fn validate_finite_partial(
    fin: &FinitePartialPresentation,
    eval_laws: &[PartialEvalLawSpec],
) -> Result<(), ValidationError> {
    let mut slot_names = BTreeSet::new();
    for slot in &fin.slots {
        require_non_empty(&slot.name, "partial.slot.name")?;
        if !slot_names.insert(slot.name.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "partial_slot",
                name: slot.name.clone(),
            });
        }
        if !fin.sorts.contains_key(&slot.sort) {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: slot.sort.clone(),
                context: format!("slot `{}`", slot.name),
            });
        }
        if slot.domain_values.is_empty() {
            return Err(ValidationError::ConversionError {
                detail: format!("slot `{}` has empty domain_values", slot.name),
            });
        }
    }
    let op_names: BTreeSet<&str> = fin.operations.iter().map(|o| o.name.as_str()).collect();
    let rel_names: BTreeSet<&str> = fin.relations.iter().map(|r| r.name.as_str()).collect();

    for op in &fin.operations {
        for s in &op.arg_sorts {
            if !fin.sorts.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: s.clone(),
                    context: format!("partial operation `{}`", op.name),
                });
            }
        }
        if !fin.sorts.contains_key(&op.out_sort) {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: op.out_sort.clone(),
                context: format!("partial operation `{}`", op.name),
            });
        }
    }
    for rel in &fin.relations {
        for s in &rel.arg_sorts {
            if !fin.sorts.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: s.clone(),
                    context: format!("partial relation `{}`", rel.name),
                });
            }
        }
    }

    for bg in &fin.background_constraints {
        match bg {
            BackgroundConstraint::SlotEquality(a, b) | BackgroundConstraint::SlotNotEqual(a, b) => {
                for s in [a, b] {
                    if !slot_names.contains(s) {
                        return Err(ValidationError::UnknownRef {
                            kind: "slot",
                            name: s.clone(),
                            context: "partial.background_constraint".to_owned(),
                        });
                    }
                }
            }
            BackgroundConstraint::OperationInjective(op)
            | BackgroundConstraint::OperationSurjective(op) => {
                if !op_names.contains(op.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "operation",
                        name: op.clone(),
                        context: "partial.background_constraint".to_owned(),
                    });
                }
            }
        }
    }

    let mut rec_ids = BTreeSet::new();
    for rec in &fin.records {
        require_non_empty(&rec.id, "partial.record.id")?;
        if !rec_ids.insert(rec.id.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "partial_record",
                name: rec.id.clone(),
            });
        }
        match &rec.kind {
            PartialRecordKind::OpValue { op_name, value, .. } => {
                if !op_names.contains(op_name.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "operation",
                        name: op_name.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
                if let PartialValue::UnobservedSlot(s) = value
                    && !slot_names.contains(s)
                {
                    return Err(ValidationError::UnknownRef {
                        kind: "slot",
                        name: s.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
            }
            PartialRecordKind::OpDomain {
                op_name, defined, ..
            } => {
                if !op_names.contains(op_name.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "operation",
                        name: op_name.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
                if let PartialTruth::UnobservedSlot(s) = defined
                    && !slot_names.contains(s)
                {
                    return Err(ValidationError::UnknownRef {
                        kind: "slot",
                        name: s.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
            }
            PartialRecordKind::OpGraph {
                op_name, present, ..
            } => {
                if !op_names.contains(op_name.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "operation",
                        name: op_name.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
                if let PartialTruth::UnobservedSlot(s) = present
                    && !slot_names.contains(s)
                {
                    return Err(ValidationError::UnknownRef {
                        kind: "slot",
                        name: s.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
            }
            PartialRecordKind::Relation {
                rel_name, holds, ..
            } => {
                if !rel_names.contains(rel_name.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "relation",
                        name: rel_name.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
                if let PartialTruth::UnobservedSlot(s) = holds
                    && !slot_names.contains(s)
                {
                    return Err(ValidationError::UnknownRef {
                        kind: "slot",
                        name: s.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
            }
            PartialRecordKind::SlotAssignment { slot, .. } => {
                if !slot_names.contains(slot) {
                    return Err(ValidationError::UnknownRef {
                        kind: "slot",
                        name: slot.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
            }
        }
    }

    for law in eval_laws {
        require_non_empty(&law.name, "partial.eval_law.name")?;
        if let Some(ant) = &law.antecedent {
            validate_formula_refs(ant, &op_names, &rel_names, &slot_names)?;
        }
        validate_formula_refs(&law.conclusion, &op_names, &rel_names, &slot_names)?;
    }

    Ok(())
}

fn validate_formula_refs(
    formula: &PartialFormula,
    ops: &BTreeSet<&str>,
    rels: &BTreeSet<&str>,
    slots: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    match formula {
        PartialFormula::Eq(a, b) => {
            validate_term_refs(a, ops, slots)?;
            validate_term_refs(b, ops, slots)
        }
        PartialFormula::Rel { rel_name, args } => {
            if !rels.contains(rel_name.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "relation",
                    name: rel_name.clone(),
                    context: "partial.formula".to_owned(),
                });
            }
            for a in args {
                validate_term_refs(a, ops, slots)?;
            }
            Ok(())
        }
        PartialFormula::Graph {
            op_name,
            args,
            output,
        } => {
            if !ops.contains(op_name.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "operation",
                    name: op_name.clone(),
                    context: "partial.formula".to_owned(),
                });
            }
            for a in args {
                validate_term_refs(a, ops, slots)?;
            }
            validate_term_refs(output, ops, slots)
        }
        PartialFormula::Defined { op_name, args } => {
            if !ops.contains(op_name.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "operation",
                    name: op_name.clone(),
                    context: "partial.formula".to_owned(),
                });
            }
            for a in args {
                validate_term_refs(a, ops, slots)?;
            }
            Ok(())
        }
        PartialFormula::Not(inner)
        | PartialFormula::Exists { body: inner, .. }
        | PartialFormula::Forall { body: inner, .. } => {
            validate_formula_refs(inner, ops, rels, slots)
        }
        PartialFormula::And(list) | PartialFormula::Or(list) => {
            for f in list {
                validate_formula_refs(f, ops, rels, slots)?;
            }
            Ok(())
        }
    }
}

fn validate_term_refs(
    term: &PartialTerm,
    ops: &BTreeSet<&str>,
    slots: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    match term {
        PartialTerm::Var(_) | PartialTerm::Const(_) => Ok(()),
        PartialTerm::Slot(s) => {
            if !slots.contains(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "slot",
                    name: s.clone(),
                    context: "partial.term".to_owned(),
                });
            }
            Ok(())
        }
        PartialTerm::App { op_name, args } => {
            if !ops.contains(op_name.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "operation",
                    name: op_name.clone(),
                    context: "partial.term".to_owned(),
                });
            }
            for a in args {
                validate_term_refs(a, ops, slots)?;
            }
            Ok(())
        }
        PartialTerm::Let { bound, body, .. } => {
            validate_term_refs(bound, ops, slots)?;
            validate_term_refs(body, ops, slots)
        }
        PartialTerm::BinOp { lhs, rhs, .. } => {
            validate_term_refs(lhs, ops, slots)?;
            validate_term_refs(rhs, ops, slots)
        }
    }
}

fn validate_affine_partial(aff: &AffinePartialPresentation) -> Result<(), ValidationError> {
    validate_coeff_domain(&aff.coeff_domain, "partial.affine")?;
    let n = aff.coord_names.len();
    if aff.x0.len() != n || aff.direction_t.len() != n {
        return Err(ValidationError::ArityMismatch {
            context: "partial.affine x0/direction_t rows".to_owned(),
            expected: n,
            actual: aff.x0.len(),
        });
    }
    let t_cols = aff.direction_t.first().map_or(0, Vec::len);
    for row in &aff.direction_t {
        if row.len() != t_cols {
            return Err(ValidationError::ArityMismatch {
                context: "partial.affine direction_t column count".to_owned(),
                expected: t_cols,
                actual: row.len(),
            });
        }
        for v in row {
            validate_scalar_lit(v, &aff.coeff_domain, "partial.affine.T")?;
        }
    }
    for v in &aff.x0 {
        validate_scalar_lit(v, &aff.coeff_domain, "partial.affine.x0")?;
    }
    for (id, row, rhs) in aff
        .background_rows
        .iter()
        .chain(&aff.record_rows)
        .chain(&aff.eval_equations)
    {
        require_non_empty(id, "partial.affine.row.id")?;
        if row.len() != n {
            return Err(ValidationError::ArityMismatch {
                context: format!("partial.affine row `{id}`"),
                expected: n,
                actual: row.len(),
            });
        }
        for v in row {
            validate_scalar_lit(v, &aff.coeff_domain, &format!("partial.affine row `{id}`"))?;
        }
        validate_scalar_lit(
            rhs,
            &aff.coeff_domain,
            &format!("partial.affine rhs `{id}`"),
        )?;
    }
    Ok(())
}

fn validate_open_domain(od: &OpenDomainSpec) -> Result<(), ValidationError> {
    for (s, sub_elems) in &od.substructure_carriers {
        let Some(amb_elems) = od.ambient_carriers.get(s) else {
            return Err(ValidationError::UnknownRef {
                kind: "ambient_sort",
                name: s.clone(),
                context: "open_domain".to_owned(),
            });
        };
        let amb_set: BTreeSet<&str> = amb_elems.iter().map(String::as_str).collect();
        for e in sub_elems {
            if !amb_set.contains(e.as_str()) {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "substructure element `{e}` in sort `{s}` is not contained in ambient carrier"
                    ),
                });
            }
        }
    }
    if let Some(ar) = &od.affine_restriction {
        validate_coeff_domain(&ar.coeff_domain, "open_domain.affine_restriction")?;
        if ar.m_matrix.len() != ar.b_rhs.len() {
            return Err(ValidationError::ArityMismatch {
                context: "affine_restriction m_matrix/b_rhs".to_owned(),
                expected: ar.m_matrix.len(),
                actual: ar.b_rhs.len(),
            });
        }
        for row in &ar.m_matrix {
            if row.len() != ar.num_vars {
                return Err(ValidationError::ArityMismatch {
                    context: "affine_restriction m_matrix cols".to_owned(),
                    expected: ar.num_vars,
                    actual: row.len(),
                });
            }
            for v in row {
                validate_scalar_lit(v, &ar.coeff_domain, "affine_restriction.M")?;
            }
        }
        for v in &ar.b_rhs {
            validate_scalar_lit(v, &ar.coeff_domain, "affine_restriction.b")?;
        }
        for row in &ar.r_matrix {
            if row.len() != ar.num_vars {
                return Err(ValidationError::ArityMismatch {
                    context: "affine_restriction r_matrix cols".to_owned(),
                    expected: ar.num_vars,
                    actual: row.len(),
                });
            }
            for v in row {
                validate_scalar_lit(v, &ar.coeff_domain, "affine_restriction.R")?;
            }
        }
    }
    Ok(())
}
