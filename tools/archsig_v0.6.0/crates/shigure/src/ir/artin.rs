//! 定義的補助演算の原始消去・全局所 Artin 試験・検出次数 $\nu$・構文次数上界 $D$・
//! 一般係数冪零商 base change の検証済み IR（G-141 F1–F9・H4–H7・H10）。

use crate::ir::change::NamedPoly;
use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::{ValidationError, validate_coeff_domain, validate_provenance};
use std::collections::BTreeSet;

/// 定義的補助演算 `Y_j = F_j(O, Y_1, ..., Y_{j-1})`（G-141 F1）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuxiliaryDefSpec {
    pub name: String,
    pub expr: PolyExpr,
}

/// 2 段合成 reading `v ∘ u` の第 2 段仕様（G-141 F6）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompositeStageSpec {
    pub aux_defs: Vec<AuxiliaryDefSpec>,
    pub extra_laws: Vec<NamedPoly>,
}

/// 一般係数の冪零商 base change `k_0 -> k_1` 比較仕様（G-141 F8・H6）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BaseChangeSpec {
    pub target_domain: CoeffDomain,
    /// `D_r` を比較する冪零商次数 `r`（省略時は `k_0` 側の初回検出次数 `ν`）。
    pub test_order: Option<usize>,
}

/// Artin 試験タスクの未検証入力仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArtinTaskSpec {
    pub name: String,
    pub coeff_domain: CoeffDomain,
    /// 観測表示 `O` の変数名列。
    pub obs_vars: Vec<String>,
    /// 観測表示 `O` の既存関係 `I_O`（空なら自由観測 chart、非空なら関係付き観測環）。
    pub obs_relations: Vec<NamedPoly>,
    /// 依存順に並べた定義的補助演算 `Y_j = F_j(O, Y_1, ..., Y_{j-1})`。
    pub aux_defs: Vec<AuxiliaryDefSpec>,
    /// 追加 Law `G_α = 0`（`O` と `Y_1, ..., Y_m` の多項式）。
    pub extra_laws: Vec<NamedPoly>,
    /// 基点 `a ∈ Sem_P(k)` の観測座標値（定数式または未観測スロット）。
    pub base_point: Vec<(String, PolyExpr)>,
    /// 探索する Artin 商の最大次数上限（超過時は誤判定せず `undetermined`）。
    pub max_order: usize,
    /// 局所 Artin 商の次元上限（省略時は `DEFAULT_MAX_ARTIN_DIM`）。
    pub max_artin_dim: Option<usize>,
    /// 任意: 2 段合成 reading `v ∘ u` の第 2 段仕様（F6）。
    pub composite_stage: Option<CompositeStageSpec>,
    /// 任意: 一般係数の冪零商 base change 比較仕様（F8・H6）。
    pub base_change: Option<BaseChangeSpec>,
    /// 非 Noetherian 無限表示（例: H7 の `T_i = T_{i+1}^2`）であることを明示する印。
    /// `true` の場合は全 Artin 試験一致から局所同型を主張せず `non_noetherian_infinite_presentation` で沈黙する。
    pub non_noetherian_infinite: bool,
    pub provenance: Provenance,
}

/// 型・参照・非循環依存を検証済みの Artin 試験タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedArtinTask {
    spec: ArtinTaskSpec,
}

impl CheckedArtinTask {
    pub fn spec(&self) -> &ArtinTaskSpec {
        &self.spec
    }

    pub fn is_free_observation_chart(&self) -> bool {
        self.spec.obs_relations.is_empty()
    }
}

/// `ArtinTaskSpec` を検証して `CheckedArtinTask` を構築する。
pub fn validate_artin_task(spec: ArtinTaskSpec) -> Result<CheckedArtinTask, ValidationError> {
    if spec.name.trim().is_empty() {
        return Err(ValidationError::EmptyName {
            context: "artin_task".to_owned(),
        });
    }
    let ctx = format!("artin_task `{}`", spec.name);
    validate_coeff_domain(&spec.coeff_domain, &ctx)?;
    if spec.provenance.origins.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: format!("missing provenance in {ctx}"),
        });
    }
    validate_provenance(&spec.provenance, &ctx)?;
    if spec.max_order == 0 {
        return Err(ValidationError::ConversionError {
            detail: "artin_task max_order must be >= 1".to_owned(),
        });
    }

    let mut obs_set = BTreeSet::new();
    for v in &spec.obs_vars {
        if v.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "obs_var".to_owned(),
            });
        }
        if !obs_set.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "obs_var",
                name: v.clone(),
            });
        }
    }

    // 既存関係 I_O は重複名を禁じ、obs_vars のみ参照可能
    let mut rel_seen = BTreeSet::new();
    for rel in &spec.obs_relations {
        if rel.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "obs_relation".to_owned(),
            });
        }
        if !rel_seen.insert(rel.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "obs_relation",
                name: rel.name.clone(),
            });
        }
        check_expr_refs(&rel.expr, &obs_set, &format!("obs_relation `{}`", rel.name))?;
    }

    // 定義的補助演算 Y_j = F_j(O, Y_1, ..., Y_{j-1}) の非循環依存順を厳密検査する（F1）。
    let mut available: BTreeSet<&str> = obs_set.clone();
    let mut aux_seen = BTreeSet::new();
    for aux in &spec.aux_defs {
        if aux.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "aux_def".to_owned(),
            });
        }
        if obs_set.contains(aux.name.as_str()) || !aux_seen.insert(aux.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "aux_def",
                name: aux.name.clone(),
            });
        }
        check_expr_refs(
            &aux.expr,
            &available,
            &format!("aux_def `{}` (must depend only on earlier vars)", aux.name),
        )?;
        available.insert(aux.name.as_str());
    }

    let mut law_seen = BTreeSet::new();
    for law in &spec.extra_laws {
        if law.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "extra_law".to_owned(),
            });
        }
        if !law_seen.insert(law.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "extra_law",
                name: law.name.clone(),
            });
        }
        check_expr_refs(&law.expr, &available, &format!("extra_law `{}`", law.name))?;
    }

    // base_point 検査（全観測変数を網羅し、自由変数を含まない定数式／未観測スロットのみ許可）
    let empty_vars = BTreeSet::new();
    let mut bp_seen = BTreeSet::new();
    for (v, expr) in &spec.base_point {
        if !obs_set.contains(v.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "obs_var",
                name: v.clone(),
                context: format!("{ctx} base_point"),
            });
        }
        if !bp_seen.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "base_point_var",
                name: v.clone(),
            });
        }
        check_expr_refs(
            expr,
            &empty_vars,
            &format!("{ctx} base_point `{v}` (must be constant or unobserved)"),
        )?;
    }
    if bp_seen.len() != obs_set.len() {
        return Err(ValidationError::ConversionError {
            detail: format!("{ctx} base_point must assign every observation variable"),
        });
    }

    // 2 段合成 reading（F6: A_0 -> A_1 = A_0/J_u -> A_2 = A_1/J_v）の非循環依存検査:
    // 第 1 段 u の obs_vars + aux_defs（`available`）を引き継ぎ、同名シャドーイングを禁止する。
    if let Some(stage) = &spec.composite_stage {
        let mut stage_avail: BTreeSet<&str> = available.clone();
        let mut stage_aux_seen = BTreeSet::new();
        for aux in &stage.aux_defs {
            if aux.name.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "composite_aux_def".to_owned(),
                });
            }
            if available.contains(aux.name.as_str()) || !stage_aux_seen.insert(aux.name.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "composite_aux_def",
                    name: aux.name.clone(),
                });
            }
            check_expr_refs(
                &aux.expr,
                &stage_avail,
                &format!("composite aux_def `{}`", aux.name),
            )?;
            stage_avail.insert(aux.name.as_str());
        }
        let mut stage_law_seen = BTreeSet::new();
        for law in &stage.extra_laws {
            if law.name.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "composite_extra_law".to_owned(),
                });
            }
            if !stage_law_seen.insert(law.name.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "composite_extra_law",
                    name: law.name.clone(),
                });
            }
            check_expr_refs(
                &law.expr,
                &stage_avail,
                &format!("composite extra_law `{}`", law.name),
            )?;
        }
    }

    if let Some(bc) = &spec.base_change {
        validate_coeff_domain(&bc.target_domain, &format!("{ctx} base_change"))?;
    }

    Ok(CheckedArtinTask { spec })
}

pub(crate) fn check_expr_refs(
    expr: &PolyExpr,
    allowed: &BTreeSet<&str>,
    context: &str,
) -> Result<(), ValidationError> {
    match expr {
        PolyExpr::Const(_) | PolyExpr::Unobserved { .. } => Ok(()),
        PolyExpr::StateVar(v) | PolyExpr::ArgVar(v) | PolyExpr::ParamVar(v) => {
            if !allowed.contains(v.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "variable",
                    name: v.clone(),
                    context: context.to_owned(),
                });
            }
            Ok(())
        }
        PolyExpr::Neg(a) | PolyExpr::Pow(a, _) => check_expr_refs(a, allowed, context),
        PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) | PolyExpr::Mul(a, b) => {
            check_expr_refs(a, allowed, context)?;
            check_expr_refs(b, allowed, context)
        }
    }
}
