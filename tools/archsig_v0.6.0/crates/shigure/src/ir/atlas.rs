//! 有限連結単純グラフ上の実 adapter・SAGA 比較・制約付き全修復（$H_V, H_E$）・
//! 指定診断類 $\kappa_b$・Atlas 細分化 Condition C0–C6 と評価条件付き全修復 fiber 比較の検証済み IR
//! （G-141 G1–G5・H8・H12 / G-142 E1–E6・F1–F7・W3）。

use crate::ir::artin::check_expr_refs;
use crate::ir::change::NamedPoly;
use crate::ir::diagnostics::{SupportedNerveSpec, validate_supported_nerve};
use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::{ValidationError, validate_coeff_domain, validate_provenance};
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

/// 原子操作の adapter 可換性検査対象（`g ∘ op_before == op_after ∘ g` を一般多項式恒等式で検算）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicOpCompareSpec {
    pub name: String,
    pub arg_vars: Vec<String>,
    pub before_updates: Vec<(String, PolyExpr)>,
    pub after_updates: Vec<(String, PolyExpr)>,
}

/// 一般の拡張プロトコル語または実行時引数操作の非移送検査ケース（G-141 H12 の一般表現）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtendedOperationCheckSpec {
    /// 多段プロトコル語評価（拡張状態変数・初期状態・前後ステップ列・観測式・中間 Law 残差）。
    ProtocolSequence {
        name: String,
        extended_state_vars: Vec<String>,
        initial_state: Vec<(String, PolyExpr)>,
        before_steps: Vec<Vec<(String, PolyExpr)>>,
        after_steps: Vec<Vec<(String, PolyExpr)>>,
        before_read: Box<PolyExpr>,
        after_read: Box<PolyExpr>,
        /// 各ステップ後に検査する中間状態 Law 式（零であるべき式）。
        intermediate_laws: Vec<NamedPoly>,
    },
    /// 状態依存（実行時引数）操作の adapter 可換性評価（`g(op_before(x))` vs `op_after(g(x))`）。
    RuntimeArgOp {
        name: String,
        before_updates: Vec<(String, PolyExpr)>,
        after_updates: Vec<(String, PolyExpr)>,
        sample_state: Vec<(String, PolyExpr)>,
    },
}

/// 原子操作 adapter の一般拡張操作言語非移送検査仕様（G-141 H12）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtendedLanguageCheckSpec {
    pub state_vars: Vec<String>,
    /// adapter 状態写像 `g: R^n -> R^n`（各状態変数の変換後多項式）。
    pub adapter_map: Vec<(String, PolyExpr)>,
    /// 原子操作の可換性比較一覧。
    pub atomic_ops: Vec<AtomicOpCompareSpec>,
    /// 拡張操作・拡張プロトコル語の検査ケース一覧。
    pub extended_checks: Vec<ExtendedOperationCheckSpec>,
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
        return Err(ValidationError::EmptyName {
            context: "atlas_task".to_owned(),
        });
    }
    let ctx = format!("atlas_task `{}`", spec.name);
    validate_coeff_domain(&spec.coeff_domain, &ctx)?;
    if spec.provenance.origins.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: format!("missing provenance in {ctx}"),
        });
    }
    validate_provenance(&spec.provenance, &ctx)?;

    let empty_vars = BTreeSet::new();
    check_expr_refs(&spec.mu, &empty_vars, &format!("{ctx} mu"))?;

    let (v_set, e_set) = validate_simple_graph(&spec.vertices, &spec.edges, &ctx)?;

    let mut lam_seen = BTreeSet::new();
    for (v, expr) in &spec.base_lambdas {
        if !v_set.contains(v.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "vertex",
                name: v.clone(),
                context: format!("{ctx} base_lambdas"),
            });
        }
        if !lam_seen.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "base_lambda_vertex",
                name: v.clone(),
            });
        }
        check_expr_refs(expr, &empty_vars, &format!("{ctx} base_lambda `{v}`"))?;
    }
    if lam_seen.len() != v_set.len() {
        return Err(ValidationError::ConversionError {
            detail: format!("{ctx} base_lambdas must assign every vertex"),
        });
    }

    let mut av_seen = BTreeSet::new();
    for v in &spec.allowed_vertices {
        if !v_set.contains(v.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "vertex",
                name: v.clone(),
                context: "allowed_vertices".to_owned(),
            });
        }
        if !av_seen.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "allowed_vertex",
                name: v.clone(),
            });
        }
    }
    let mut ae_seen = BTreeSet::new();
    for e in &spec.allowed_edges {
        if !e_set.contains(e.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "edge",
                name: e.clone(),
                context: "allowed_edges".to_owned(),
            });
        }
        if !ae_seen.insert(e.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "allowed_edge",
                name: e.clone(),
            });
        }
    }

    if let Some(ref_spec) = &spec.refinement {
        validate_refinement(ref_spec, &v_set, &e_set, &spec.name)?;
    }

    if let Some(ext) = &spec.extended_language_check {
        validate_extended_language_check(ext, &ctx)?;
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
            return Err(ValidationError::EmptyName {
                context: "vertex".to_owned(),
            });
        }
        if !v_set.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "vertex",
                name: v.clone(),
            });
        }
    }
    let empty_vars = BTreeSet::new();
    let mut e_set = BTreeSet::new();
    let mut undirected_pairs = BTreeSet::new();
    for e in edges {
        if e.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "edge".to_owned(),
            });
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
        check_expr_refs(
            &e.offset,
            &empty_vars,
            &format!("{context} edge `{}` offset", e.name),
        )?;
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

    // nerve_edge_map 検証
    let c_edges: BTreeSet<&str> = r
        .coarse_nerve
        .edges
        .iter()
        .map(|e| e.name.as_str())
        .collect();
    let f_edges: BTreeSet<&str> = r.fine_nerve.edges.iter().map(|e| e.name.as_str()).collect();
    validate_partial_nerve_map(
        &r.nerve_edge_map,
        &f_edges,
        &c_edges,
        "nerve_edge",
        "refinement.nerve_edge_map",
    )?;

    // nerve_face_map 検証
    let c_faces: BTreeSet<&str> = r
        .coarse_nerve
        .faces
        .iter()
        .map(|f| f.name.as_str())
        .collect();
    let f_faces: BTreeSet<&str> = r.fine_nerve.faces.iter().map(|f| f.name.as_str()).collect();
    validate_partial_nerve_map(
        &r.nerve_face_map,
        &f_faces,
        &c_faces,
        "nerve_face",
        "refinement.nerve_face_map",
    )?;

    if let Some(ec) = &r.eval_condition {
        let mut allowed_vars: BTreeSet<&str> = BTreeSet::new();
        allowed_vars.extend(coarse_v.iter().copied());
        allowed_vars.extend(coarse_e.iter().copied());
        for (kind, list) in [
            ("eval_condition.evaluation", &ec.evaluations),
            ("eval_condition.equation", &ec.equations),
            ("eval_condition.invertible", &ec.invertibles),
        ] {
            let mut seen = BTreeSet::new();
            for item in list {
                if item.name.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: kind.to_owned(),
                    });
                }
                if !seen.insert(item.name.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind,
                        name: item.name.clone(),
                    });
                }
                check_expr_refs(&item.expr, &allowed_vars, &format!("{kind} `{}`", item.name))?;
            }
        }
    }

    if let Some(fg) = &r.forgetful_reading {
        if fg.forgotten_var.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "forgetful_reading.forgotten_var".to_owned(),
            });
        }
        if fg.sample_values.is_empty() {
            return Err(ValidationError::ConversionError {
                detail: "forgetful_reading.sample_values must be nonempty".to_owned(),
            });
        }
        let fg_vars: BTreeSet<&str> = [fg.forgotten_var.as_str()].into_iter().collect();
        check_expr_refs(&fg.eval_expr, &fg_vars, "forgetful_reading.eval_expr")?;
        check_expr_refs(
            &fg.condition_eq,
            &fg_vars,
            "forgetful_reading.condition_eq",
        )?;
        let empty = BTreeSet::new();
        for sv in &fg.sample_values {
            check_expr_refs(sv, &empty, "forgetful_reading.sample_values")?;
        }
    }
    Ok(())
}

fn validate_partial_nerve_map(
    entries: &[(String, Option<String>)],
    fine_set: &BTreeSet<&str>,
    coarse_set: &BTreeSet<&str>,
    kind: &'static str,
    context: &str,
) -> Result<(), ValidationError> {
    let mut seen = BTreeSet::new();
    for (f_name, c_opt) in entries {
        if !fine_set.contains(f_name.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind,
                name: f_name.clone(),
                context: context.to_owned(),
            });
        }
        if let Some(c_name) = c_opt
            && !coarse_set.contains(c_name.as_str())
        {
            return Err(ValidationError::UnknownRef {
                kind,
                name: c_name.clone(),
                context: context.to_owned(),
            });
        }
        if !seen.insert(f_name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind,
                name: f_name.clone(),
            });
        }
    }
    if seen.len() != fine_set.len() {
        return Err(ValidationError::ConversionError {
            detail: format!("{context} must assign every fine {kind}"),
        });
    }
    Ok(())
}

fn validate_extended_language_check(
    ext: &ExtendedLanguageCheckSpec,
    context: &str,
) -> Result<(), ValidationError> {
    if ext.state_vars.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: format!("{context} extended_language_check.state_vars must be nonempty"),
        });
    }
    let mut s_set = BTreeSet::new();
    for v in &ext.state_vars {
        if v.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "extended_language_check.state_var".to_owned(),
            });
        }
        if !s_set.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "state_var",
                name: v.clone(),
            });
        }
    }
    validate_total_var_map(&ext.adapter_map, &s_set, &s_set, "adapter_map")?;

    let mut op_names = BTreeSet::new();
    for op in &ext.atomic_ops {
        if op.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "atomic_op".to_owned(),
            });
        }
        if !op_names.insert(op.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "atomic_op",
                name: op.name.clone(),
            });
        }
        let mut allowed = s_set.clone();
        for a in &op.arg_vars {
            if a.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "atomic_op.arg_var".to_owned(),
                });
            }
            if !allowed.insert(a.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "atomic_op_arg",
                    name: a.clone(),
                });
            }
        }
        validate_total_var_map(&op.before_updates, &s_set, &allowed, "atomic_op.before")?;
        validate_total_var_map(&op.after_updates, &s_set, &allowed, "atomic_op.after")?;
    }

    let empty = BTreeSet::new();
    let mut chk_names = BTreeSet::new();
    for chk in &ext.extended_checks {
        match chk {
            ExtendedOperationCheckSpec::ProtocolSequence {
                name,
                extended_state_vars,
                initial_state,
                before_steps,
                after_steps,
                before_read,
                after_read,
                intermediate_laws,
            } => {
                if name.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "extended_check".to_owned(),
                    });
                }
                if !chk_names.insert(name.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "extended_check",
                        name: name.clone(),
                    });
                }
                let mut ext_set = BTreeSet::new();
                for v in extended_state_vars {
                    if v.trim().is_empty() || !ext_set.insert(v.as_str()) {
                        return Err(ValidationError::ConversionError {
                            detail: format!("invalid or duplicate extended_state_var `{v}`"),
                        });
                    }
                }
                validate_total_var_map(initial_state, &ext_set, &empty, "protocol.initial_state")?;
                for st in before_steps.iter().chain(after_steps) {
                    validate_total_var_map(st, &ext_set, &ext_set, "protocol.step")?;
                }
                check_expr_refs(before_read, &ext_set, "protocol.before_read")?;
                check_expr_refs(after_read, &ext_set, "protocol.after_read")?;
                for law in intermediate_laws {
                    check_expr_refs(&law.expr, &ext_set, "protocol.intermediate_law")?;
                }
            }
            ExtendedOperationCheckSpec::RuntimeArgOp {
                name,
                before_updates,
                after_updates,
                sample_state,
            } => {
                if name.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "extended_check".to_owned(),
                    });
                }
                if !chk_names.insert(name.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "extended_check",
                        name: name.clone(),
                    });
                }
                validate_total_var_map(before_updates, &s_set, &s_set, "runtime_op.before")?;
                validate_total_var_map(after_updates, &s_set, &s_set, "runtime_op.after")?;
                validate_total_var_map(sample_state, &s_set, &empty, "runtime_op.sample_state")?;
            }
        }
    }
    Ok(())
}

fn validate_total_var_map(
    entries: &[(String, PolyExpr)],
    targets: &BTreeSet<&str>,
    allowed_refs: &BTreeSet<&str>,
    context: &str,
) -> Result<(), ValidationError> {
    let mut seen = BTreeSet::new();
    for (v, expr) in entries {
        if !targets.contains(v.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "state_var",
                name: v.clone(),
                context: context.to_owned(),
            });
        }
        if !seen.insert(v.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "state_var_assignment",
                name: v.clone(),
            });
        }
        check_expr_refs(expr, allowed_refs, context)?;
    }
    if seen.len() != targets.len() {
        return Err(ValidationError::ConversionError {
            detail: format!("{context} must assign every target state variable"),
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
