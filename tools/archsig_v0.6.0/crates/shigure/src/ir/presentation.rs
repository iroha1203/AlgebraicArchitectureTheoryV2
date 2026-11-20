//! SHIGURE 原始表示 IR（Presentation・Phase・Operation・LawKind・状態比較 h・語翻訳 τ）。

use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use std::collections::BTreeMap;

/// 有限 rank の原始 sort 宣言（G-139 P0–P1 / G-140 P0）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SortDecl {
    pub name: String,
    pub rank: usize,
    pub coeff_domain: CoeffDomain,
    pub provenance: Option<SourceRef>,
}

/// phase に属する状態座標。既知値と未観測（missing）を型で区別する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoordDecl {
    pub name: String,
    pub sort: String,
    pub observed_value: Option<ScalarLit>,
    /// true のとき未観測の座標として扱い、零へ暗黙補完しない。
    pub missing: bool,
    pub provenance: Option<SourceRef>,
}

impl CoordDecl {
    pub fn symbolic(name: impl Into<String>, sort: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            sort: sort.into(),
            observed_value: None,
            missing: false,
            provenance: None,
        }
    }

    pub fn missing(name: impl Into<String>, sort: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            sort: sort.into(),
            observed_value: None,
            missing: true,
            provenance: None,
        }
    }
}

/// 守る意味 Law と編集可能な表示 Law の区別（R1.5 / G-140 P4, P6）。
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LawKind {
    /// 守るべき意味 Law（`required`）。許容変換 H による編集対象にしてはならない。
    Semantic,
    /// 表現に属する状態 Law（`representation`）。H が明示許可した場合のみ編集可能。
    Representation,
}

impl LawKind {
    pub fn wire(self) -> &'static str {
        match self {
            LawKind::Semantic => "semantic",
            LawKind::Representation => "representation",
        }
    }
}

/// phase 上の状態方程式 `polynomial = 0`（例: Busy Law `μ(h - C) = 0`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateLaw {
    pub name: String,
    pub kind: LawKind,
    pub polynomial: PolyExpr,
    pub provenance: Option<SourceRef>,
}

/// phase 宣言（例: Idle `(B, C)`, Busy `(B, C, h)` with Busy Law）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseDecl {
    pub name: String,
    pub coords: Vec<CoordDecl>,
    pub state_laws: Vec<StateLaw>,
    pub provenance: Option<SourceRef>,
}

/// 生成操作宣言（遷移式 `source_phase -> target_phase`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationDecl {
    pub name: String,
    pub source_phase: String,
    pub target_phase: String,
    /// 引数 `(arg_name, sort_name)` の宣言順リスト。
    pub args: Vec<(String, String)>,
    /// 遷移先 phase の各座標名に対する更新式。
    pub updates: BTreeMap<String, PolyExpr>,
    pub provenance: Option<SourceRef>,
}

/// 観測写像宣言（例: `read(B, C) = B + C`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservationDecl {
    pub name: String,
    pub phase: String,
    pub components: Vec<PolyExpr>,
    pub provenance: Option<SourceRef>,
}

/// 原始表示 IR（Presentation）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Presentation {
    pub name: String,
    pub coeff_domain: CoeffDomain,
    pub sorts: Vec<SortDecl>,
    pub phases: Vec<PhaseDecl>,
    pub operations: Vec<OperationDecl>,
    pub observations: Vec<ObservationDecl>,
    pub provenance: Provenance,
}

impl Presentation {
    pub fn phase(&self, name: &str) -> Option<&PhaseDecl> {
        self.phases.iter().find(|p| p.name == name)
    }

    pub fn sort(&self, name: &str) -> Option<&SortDecl> {
        self.sorts.iter().find(|s| s.name == name)
    }

    pub fn operation(&self, name: &str) -> Option<&OperationDecl> {
        self.operations.iter().find(|op| op.name == name)
    }
}

/// 変更前後を結ぶ状態比較射 `h: after_phase -> before_phase`（G-140 P0, E1）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateComparison {
    pub after_phase: String,
    pub before_phase: String,
    /// `before_phase` の各状態座標を `after_phase` の座標（およびパラメータ）の式で表す。
    pub map: BTreeMap<String, PolyExpr>,
    pub provenance: Option<SourceRef>,
}

/// 操作語翻訳 τ の 1 ステップ（変更前の操作名と引数代入式）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranslatedStep {
    pub before_operation: String,
    /// 変更後操作の引数変数・定数・パラメータから構成する引数式（変更前操作の引数順）。
    pub arg_exprs: Vec<PolyExpr>,
}

/// 変更後操作 1 つに対する語翻訳 `after_op |-> [step_1, ..., step_k]`。
/// `steps` が空のときは空語 `[]` への翻訳を表す（例: `compact |-> []`, `begin |-> []`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranslatedWord {
    pub after_operation: String,
    pub steps: Vec<TranslatedStep>,
    pub provenance: Option<SourceRef>,
}

/// 操作語翻訳 τ 全体。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WordTranslation {
    pub entries: Vec<TranslatedWord>,
}

impl WordTranslation {
    pub fn for_operation(&self, after_op: &str) -> Option<&TranslatedWord> {
        self.entries.iter().find(|e| e.after_operation == after_op)
    }
}

/// 変更前表示・変更後表示・状態比較 h・操作語翻訳 τ の組。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComparisonPair {
    pub before: Presentation,
    pub after: Presentation,
    pub state_comparisons: Vec<StateComparison>,
    pub word_translation: WordTranslation,
}
