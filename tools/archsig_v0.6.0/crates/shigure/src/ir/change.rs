//! 許容変換仕様 H（ChangeSpec）と評価条件 P -> T（EvalCondition）。

use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::{CoeffDomain, PolyExpr};
use archsig_common::canonical::Json;
use num_bigint::BigUint;
use std::fmt;

/// 探索・記号パラメータ宣言（例: `a, b, c, d, r, s, delta, mu, rho`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamDecl {
    pub name: String,
    pub coeff_domain: CoeffDomain,
    pub provenance: Option<SourceRef>,
}

/// 許容変換 H において固定する宣言対象（G-140 E1）。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FixedTarget {
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

/// 許容変換 H において編集を許す宣言対象。
/// 守る意味 Law（`LawKind::Semantic`）は編集対象にできない（型と検証で強制）。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EditableTarget {
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

impl EditableTarget {
    /// 同一対象を指す `FixedTarget` が衝突するか判定する。
    pub fn conflicts_with(&self, fixed: &FixedTarget) -> bool {
        match (self, fixed) {
            (
                EditableTarget::OperationExpr {
                    presentation: p1,
                    operation: o1,
                },
                FixedTarget::OperationExpr {
                    presentation: p2,
                    operation: o2,
                },
            ) => p1 == p2 && o1 == o2,
            (
                EditableTarget::RepresentationLaw {
                    presentation: p1,
                    phase: ph1,
                    law: l1,
                },
                FixedTarget::RepresentationLaw {
                    presentation: p2,
                    phase: ph2,
                    law: l2,
                },
            ) => p1 == p2 && ph1 == ph2 && l1 == l2,
            (
                EditableTarget::StateComparisonExpr { after_phase: a1 },
                FixedTarget::StateComparisonExpr { after_phase: a2 },
            ) => a1 == a2,
            _ => false,
        }
    }
}

/// 許容変換仕様 H（G-140 E1）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChangeSpec {
    pub name: String,
    pub coeff_domain: CoeffDomain,
    pub parameters: Vec<ParamDecl>,
    pub fixed: Vec<FixedTarget>,
    pub editable: Vec<EditableTarget>,
    pub provenance: Provenance,
}

/// 名前付き多項式式（評価写像成分・等式条件 V(f)・可逆条件 D(g) に共通利用）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedPoly {
    pub name: String,
    pub expr: PolyExpr,
    pub provenance: Option<SourceRef>,
}

impl NamedPoly {
    pub fn new(name: impl Into<String>, expr: PolyExpr) -> Self {
        Self {
            name: name.into(),
            expr,
            provenance: None,
        }
    }
}

/// 解の存在・空性判定の対象とする点集合の係数域。
/// 代数閉包上の幾何点判定と Q 点・Z 点・F_p 点の判定を混同しない（R3.2 / G-141 D5–D6）。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PointDomain {
    /// 標数 0 の代数閉包（Q-bar）上の幾何点（Nullstellensatz `1 in I` による空性判定、Z -> Q -> Q-bar）。
    AlgebraicClosure,
    /// 有理数点 Q（アフィン系は完全判定、一般非線形は判断不能で沈黙）。
    RationalPoints,
    /// 整数点 Z（整数アフィン Smith 標準形は完全判定、一般非線形は判断不能で沈黙）。
    IntegerPoints,
    /// 有限体 F_p 点（有限全列挙で完全判定）。
    FiniteFieldPoints(BigUint),
    /// 全可換 k-代数上の多項式恒等式（G-141 F11–F12 の座標面支持など）。
    UniversalRing,
}

impl PointDomain {
    pub fn wire(&self) -> Json {
        match self {
            PointDomain::AlgebraicClosure => Json::str("algebraic_closure"),
            PointDomain::RationalPoints => Json::str("Q_points"),
            PointDomain::IntegerPoints => Json::str("Z_points"),
            PointDomain::FiniteFieldPoints(p) => {
                Json::Arr(vec![Json::str("Fp_points"), Json::str(p.to_string())])
            }
            PointDomain::UniversalRing => Json::str("universal_ring"),
        }
    }
}

impl fmt::Display for PointDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PointDomain::AlgebraicClosure => write!(f, "algebraic_closure"),
            PointDomain::RationalPoints => write!(f, "Q_points"),
            PointDomain::IntegerPoints => write!(f, "Z_points"),
            PointDomain::FiniteFieldPoints(p) => write!(f, "Fp({p})_points"),
            PointDomain::UniversalRing => write!(f, "universal_ring"),
        }
    }
}

/// 評価写像 v と評価条件 P -> T（等式 V(f) と可逆条件 D(g)、G-140 E2・P6）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalCondition {
    pub name: String,
    /// 原始式から生成する評価写像 v の成分。
    pub evaluations: Vec<NamedPoly>,
    /// 等式条件 `f = 0`（閉部分 V(f)）。
    pub equations: Vec<NamedPoly>,
    /// 可逆条件 `g` が単元（開部分 D(g)、Rabinowitsch 補助式 `u * g - 1 = 0`）。
    pub invertibles: Vec<NamedPoly>,
    /// 解を問う点の係数域。
    pub point_domain: PointDomain,
    pub provenance: Provenance,
}

impl EvalCondition {
    pub fn is_purely_closed(&self) -> bool {
        self.invertibles.is_empty()
    }
}
