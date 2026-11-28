//! AAT 第18章（部分提示・欠測と開領域の確定評価）の検証済み IR
//! （`PartialTaskSpec` / `CheckedPartialTask`）。

use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::ir::validate::ValidationError;
use std::collections::{BTreeMap, BTreeSet};

pub use crate::ir::partial_validate::validate_partial_task;

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
    pub(crate) name: String,
    pub(crate) representation: PartialRepresentation,
    pub(crate) eval_laws: Vec<PartialEvalLawSpec>,
    pub(crate) quantifier_spec: Option<QuantifierHierarchySpec>,
    pub(crate) open_domain: Option<OpenDomainSpec>,
    pub(crate) provenance: Provenance,
    pub(crate) undeclared_unobserved_slots: Vec<String>,
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
