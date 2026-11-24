//! 有限連結単純グラフ上の実 adapter・SAGA 比較・制約付き全修復（$H_V, H_E$）・
//! 指定診断類 $\kappa_b$・Atlas 細分化 Condition C0–C6 と評価条件付き全修復 fiber 比較の検証済み IR
//! （G-141 G1–G5・H8・H12 / G-142 E1–E6・F1–F7・W3）。

use crate::ir::change::NamedPoly;
use crate::ir::diagnostics::{SupportedNerveSpec, validate_supported_nerve};
use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::{ValidationError, validate_coeff_domain};
use std::collections::{BTreeMap, BTreeSet};

/// 有限有向単純グラフの 1 辺仕様（`from -> to`, offset `b_e`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphEdgeSpec {
    pub name: String,
    pub from: String,
    pub to: String,
    pub offset: PolyExpr,
}

/// 評価条件 `v_c: F_c -> T` および `P ↪ T`（G-142 F5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtlasEvalConditionSpec {
    pub evaluations: Vec<NamedPoly>,
    pub equations: Vec<NamedPoly>,
    pub invertibles: Vec<NamedPoly>,
}

/// 情報を落とす reading 反例仕様（G-142 F7: adequacy + C0–C6 成立下で忘却係数 `t` に対する評価・条件が降下しない）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForgetfulReadingSpec {
    pub forgotten_var: String,
    pub eval_expr: PolyExpr,
    pub condition_eq: PolyExpr,
    pub sample_values: Vec<PolyExpr>,
}

/// Atlas 細分化仕様（粗/細グラフ・粗/細 nerve・`TargetSupportedNerveMorphism`・C0–C6・F5・F7）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtlasRefinementSpec {
    pub fine_vertices: Vec<String>,
    pub fine_edges: Vec<GraphEdgeSpec>,
    /// 細頂点 -> 粗頂点の射 `φ: V_f -> V_c`。
    pub vertex_map: Vec<(String, String)>,
    /// 細辺 -> `Some(粗辺)` または `None`（内部退化辺）。
    pub edge_map: Vec<(String, Option<String>)>,
    /// 共通の有限 Source 集合（F4）。
    pub common_sources: Vec<String>,
    /// 粗 reading `q_c: Source -> T_c`（全射）。
    pub coarse_reading: Vec<(String, String)>,
    /// 細 reading `q_f: Source -> T_f`（全射）。
    pub fine_reading: Vec<(String, String)>,
    pub coarse_nerve: SupportedNerveSpec,
    pub fine_nerve: SupportedNerveSpec,
    pub nerve_chart_map: Vec<(String, String)>,
    pub nerve_edge_map: Vec<(String, Option<String>)>,
    pub nerve_face_map: Vec<(String, Option<String>)>,
    pub eval_condition: Option<AtlasEvalConditionSpec>,
    pub forgetful_reading: Option<ForgetfulReadingSpec>,
}

/// 原子操作 adapter の拡張操作言語非移送検査仕様（G-141 H12）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtendedLanguageCheckSpec {
    pub adapter_offset: PolyExpr,
    pub lambda_before: PolyExpr,
    pub mu_before: PolyExpr,
    pub check_snapshot_protocol: bool,
    pub check_compact_all: bool,
}

/// 有限グラフ実 adapter・制約付き修復・Atlas 細分化タスクの未検証入力仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtlasTaskSpec {
    pub name: String,
    pub coeff_domain: CoeffDomain,
    pub vertices: Vec<String>,
    pub edges: Vec<GraphEdgeSpec>,
    pub mu: PolyExpr,
    /// 各頂点の基準 `λ_i`。
    pub base_lambdas: Vec<(String, PolyExpr)>,
    /// 頂点許容変更集合 `A_V ⊆ V`（`H_V` を生成）。
    pub allowed_vertices: Vec<String>,
    /// 辺許容変更集合 `A_E ⊆ E`（`H_E` を生成）。
    pub allowed_edges: Vec<String>,
    /// `R = Z` のとき `Z -> Q` への零性反映（spanning tree `Φ_R`）を併せて検証する。
    pub compare_to_q: bool,
    pub refinement: Option<AtlasRefinementSpec>,
    pub extended_language_check: Option<ExtendedLanguageCheckSpec>,
    pub provenance: Provenance,
}

/// グラフ単純性・参照・細分化写像・K1 nerve を検証済みの Atlas タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedAtlasTask {
    spec: AtlasTaskSpec,
}

impl CheckedAtlasTask {
    pub fn spec(&self) -> &AtlasTaskSpec {
        &self.spec
    }
}

/// `AtlasTaskSpec` を検証して `CheckedAtlasTask` を構築する。
/// 注意: グラフ連結性は計算核側で適用条件検査し、非連結グラフは沈黙（`disconnected_graph_out_of_scope`）を返す。
pub fn validate_atlas_task(spec: AtlasTaskSpec) -> Result<CheckedAtlasTask, ValidationError> {
    if spec.name.trim().is_empty() {
        return Err(ValidationError::EmptyName { context: "atlas_task".to_owned() });
    }
    validate_coeff_domain(&spec.coeff_domain, "phase4_ir")?;
    if spec.provenance.origins.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: format!("missing provenance in atlas_task `{}`", spec.name),
        });
    }

    let (v_set, e_set) = validate_simple_graph(&spec.vertices, &spec.edges, &format!("atlas `{}`", spec.name))?;

    let mut lam_seen = BTreeSet::new();
    for (v, _) in &spec.base_lambdas {
        if !v_set.contains(v.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "vertex",
                name: v.clone(),
                context: format!("atlas `{}` base_lambdas", spec.name),
            });
        }
        if !lam_seen.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "base_lambda_vertex",
                name: v.clone(),
            });
        }
    }
    if lam_seen.len() != v_set.len() {
        return Err(ValidationError::ConversionError {
            detail: format!("atlas `{}` base_lambdas must assign every vertex", spec.name),
        });
    }

    for v in &spec.allowed_vertices {
        if !v_set.contains(v.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "vertex",
                name: v.clone(),
                context: "allowed_vertices".to_owned(),
            });
        }
    }
    for e in &spec.allowed_edges {
        if !e_set.contains(e.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "edge",
                name: e.clone(),
                context: "allowed_edges".to_owned(),
            });
        }
    }

    if let Some(ref_spec) = &spec.refinement {
        validate_refinement(ref_spec, &v_set, &e_set, &spec.name)?;
    }

    Ok(CheckedAtlasTask { spec })
}

fn validate_simple_graph<'a>(
    vertices: &'a [String],
    edges: &'a [GraphEdgeSpec],
    context: &str,
) -> Result<(BTreeSet<&'a str>, BTreeSet<&'a str>), ValidationError> {
    if vertices.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: format!("{context} must have at least one vertex"),
        });
    }
    if edges.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: format!("{context} must have at least one edge (G-141 G1)"),
        });
    }
    let mut v_set = BTreeSet::new();
    for v in vertices {
        if v.trim().is_empty() {
            return Err(ValidationError::EmptyName { context: "vertex".to_owned() });
        }
        if !v_set.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "vertex",
                name: v.clone(),
            });
        }
    }
    let mut e_set = BTreeSet::new();
    let mut undirected_pairs = BTreeSet::new();
    for e in edges {
        if e.name.trim().is_empty() {
            return Err(ValidationError::EmptyName { context: "edge".to_owned() });
        }
        if !e_set.insert(e.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "edge",
                name: e.name.clone(),
            });
        }
        if !v_set.contains(e.from.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "vertex",
                name: e.from.clone(),
                context: format!("{context} edge `{}` from", e.name),
            });
        }
        if !v_set.contains(e.to.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "vertex",
                name: e.to.clone(),
                context: format!("{context} edge `{}` to", e.name),
            });
        }
        if e.from == e.to {
            return Err(ValidationError::ConversionError {
                detail: format!("{context} simple graph forbids self-loop edge `{}`", e.name),
            });
        }
        let pair = if e.from < e.to {
            (e.from.as_str(), e.to.as_str())
        } else {
            (e.to.as_str(), e.from.as_str())
        };
        if !undirected_pairs.insert(pair) {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "{context} simple graph forbids parallel edges between `{}` and `{}`",
                    pair.0, pair.1
                ),
            });
        }
    }
    Ok((v_set, e_set))
}

fn validate_refinement(
    r: &AtlasRefinementSpec,
    coarse_v: &BTreeSet<&str>,
    coarse_e: &BTreeSet<&str>,
    task_name: &str,
) -> Result<(), ValidationError> {
    let (fine_v, fine_e) = validate_simple_graph(
        &r.fine_vertices,
        &r.fine_edges,
        &format!("atlas `{task_name}` fine_graph"),
    )?;

    let mut vm_seen = BTreeSet::new();
    for (fv, cv) in &r.vertex_map {
        if !fine_v.contains(fv.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "fine_vertex",
                name: fv.clone(),
                context: "refinement.vertex_map".to_owned(),
            });
        }
        if !coarse_v.contains(cv.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "coarse_vertex",
                name: cv.clone(),
                context: "refinement.vertex_map".to_owned(),
            });
        }
        if !vm_seen.insert(fv.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "vertex_map_fine",
                name: fv.clone(),
            });
        }
    }
    if vm_seen.len() != fine_v.len() {
        return Err(ValidationError::ConversionError {
            detail: "refinement.vertex_map must assign every fine vertex".to_owned(),
        });
    }

    let mut em_seen = BTreeSet::new();
    for (fe, ce_opt) in &r.edge_map {
        if !fine_e.contains(fe.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "fine_edge",
                name: fe.clone(),
                context: "refinement.edge_map".to_owned(),
            });
        }
        if let Some(ce) = ce_opt
            && !coarse_e.contains(ce.as_str())
        {
            return Err(ValidationError::UnknownRef {
                kind: "coarse_edge",
                name: ce.clone(),
                context: "refinement.edge_map".to_owned(),
            });
        }
        if !em_seen.insert(fe.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "edge_map_fine",
                name: fe.clone(),
            });
        }
    }
    if em_seen.len() != fine_e.len() {
        return Err(ValidationError::ConversionError {
            detail: "refinement.edge_map must assign every fine edge".to_owned(),
        });
    }

    let src_set: BTreeSet<&str> = r.common_sources.iter().map(String::as_str).collect();
    if src_set.len() != r.common_sources.len() || src_set.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: "refinement.common_sources must be nonempty and duplicate-free".to_owned(),
        });
    }
    let coarse_t = validate_reading_map(&r.coarse_reading, &src_set, "coarse_reading")?;
    let fine_t = validate_reading_map(&r.fine_reading, &src_set, "fine_reading")?;
    validate_supported_nerve(&r.coarse_nerve, &coarse_t, "refinement.coarse_nerve")?;
    validate_supported_nerve(&r.fine_nerve, &fine_t, "refinement.fine_nerve")?;

    let c_charts: BTreeSet<&str> = r
        .coarse_nerve
        .charts
        .iter()
        .map(|c| c.name.as_str())
        .collect();
    let f_charts: BTreeSet<&str> = r.fine_nerve.charts.iter().map(|c| c.name.as_str()).collect();
    let mut cm_map = BTreeMap::new();
    for (fc, cc) in &r.nerve_chart_map {
        if !f_charts.contains(fc.as_str()) || !c_charts.contains(cc.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "nerve_chart",
                name: format!("{fc} -> {cc}"),
                context: "refinement.nerve_chart_map".to_owned(),
            });
        }
        if cm_map.insert(fc.as_str(), cc.as_str()).is_some() {
            return Err(ValidationError::DuplicateDecl {
                kind: "nerve_chart_map",
                name: fc.clone(),
            });
        }
    }
    if cm_map.len() != f_charts.len() {
        return Err(ValidationError::ConversionError {
            detail: "refinement.nerve_chart_map must assign every fine chart".to_owned(),
        });
    }
    Ok(())
}

fn validate_reading_map<'a>(
    reading: &'a [(String, String)],
    sources: &BTreeSet<&str>,
    context: &str,
) -> Result<BTreeSet<&'a str>, ValidationError> {
    let mut seen = BTreeSet::new();
    let mut targets = BTreeSet::new();
    for (s, t) in reading {
        if !sources.contains(s.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "source",
                name: s.clone(),
                context: context.to_owned(),
            });
        }
        if !seen.insert(s.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "reading_source",
                name: s.clone(),
            });
        }
        targets.insert(t.as_str());
    }
    if seen.len() != sources.len() {
        return Err(ValidationError::ConversionError {
            detail: format!("{context} must assign every common source"),
        });
    }
    Ok(targets)
}
