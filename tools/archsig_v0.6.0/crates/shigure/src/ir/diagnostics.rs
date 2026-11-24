//! 固定 label の整数診断複体 $C_\Lambda$・係数変更 vs 値域再生成・
//! 診断層 $B_\pi$ 層別・値合流 Mayer–Vietoris・診断次元実現の検証済み IR
//! （G-142 A1–A3・B1–B6・C1–C4・D1–D3・W1–W2）。

use crate::ir::artin::check_expr_refs;
use crate::ir::change::NamedPoly;
use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::{
    ValidationError, validate_coeff_domain, validate_provenance, validate_scalar_lit,
};
use std::collections::{BTreeMap, BTreeSet};

/// `TargetSupportedNerve` の 1 chart 支持仕様（G-142 A1・B1）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartSupportSpec {
    pub name: String,
    pub support: Vec<String>,
}

/// `TargetSupportedNerve` の 1 edge 仕様（支持は `S_left ∩ S_right` で生成）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NerveEdgeSpec {
    pub name: String,
    pub left: String,
    pub right: String,
}

/// `TargetSupportedNerve` の 1 face 仕様（K1 端点等式 `l(e0)=l(e1), r(e0)=l(e2), r(e1)=r(e2)` を検査）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NerveFaceSpec {
    pub name: String,
    pub e0: String,
    pub e1: String,
    pub e2: String,
}

/// K1 `TargetSupportedNerve` 仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupportedNerveSpec {
    pub charts: Vec<ChartSupportSpec>,
    pub edges: Vec<NerveEdgeSpec>,
    pub faces: Vec<NerveFaceSpec>,
}

/// 静的 Law 値 readout（1 つの Law が各 source へ定数値を割り当てる）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StaticLawReadoutSpec {
    pub law_name: String,
    pub values: Vec<(String, ScalarLit)>,
}

/// 多項式 Law readout（1 つの Law が各 source へ基底変数上の多項式 `f_{ℓ, s}` を割り当てる）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolyLawReadoutSpec {
    pub law_name: String,
    pub values: Vec<(String, PolyExpr)>,
}

/// 診断タスクの readout 入力種別（固定値 vs 多項式族）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiagnosticsReadoutSpec {
    Static {
        sources: Vec<String>,
        targets: Vec<String>,
        /// 全射 reading `q: Source -> T`（全 source を target へ全射に割り当てる）。
        reading: Vec<(String, String)>,
        laws: Vec<StaticLawReadoutSpec>,
    },
    Polynomial {
        base_domain: CoeffDomain,
        base_vars: Vec<String>,
        base_relations: Vec<NamedPoly>,
        sources: Vec<String>,
        laws: Vec<PolyLawReadoutSpec>,
    },
}

/// 係数変更 `Λ -> Λ'` 比較仕様（G-142 A2–A3・W1）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoeffChangeComparisonSpec {
    pub target_domain: CoeffDomain,
    /// `true` のとき、固定 label tensor と値域再生成（例: `0, 2 ∈ Z` の `F_2` 再評価）を比較する。
    pub compare_codomain_regeneration: bool,
    /// 任意: 一般の整数 2 項複体 `[Z^n --d0--> Z^m]`（例: W1 の `Z --2--> Z`）と指定 1-cocycle。
    pub explicit_z_complex: Option<ExplicitZComplexSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExplicitZComplexSpec {
    pub dim0: usize,
    pub dim1: usize,
    pub d0: Vec<Vec<i64>>,
    pub designated_cocycle: Option<Vec<i64>>,
}

/// 値合流比較仕様（G-142 C2–C4・W2）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CollisionComparisonSpec {
    pub label: String,
    pub law_name: String,
    /// 合流前（細）partition（source 集合の互いに素な分割）。
    pub fine_partition: Vec<Vec<String>>,
    /// 合流後（粗）partition（`fine_partition` の粗化）。
    pub coarse_partition: Vec<Vec<String>>,
    /// 任意: 多段二値合流の中間 partition 列（複数経路で順序独立性を検算する、C2）。
    pub alternative_merge_paths: Vec<Vec<Vec<Vec<String>>>>,
}

/// `R`-点プローブ仕様（例: W2 の `Q[ε]/(ε²)` 上の `(0, 0)` vs `(0, ε)`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RPointProbeSpec {
    pub ring_var: String,
    pub ring_max_deg: usize,
    pub points: Vec<NamedRPointSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedRPointSpec {
    pub label: String,
    pub coords: Vec<(String, Vec<PolyExpr>)>,
}

/// 診断次元実現仕様（G-142 D1–D2: `V(g_1, ..., g_r) ∩ D(h)`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DimensionRealizationSpec {
    pub base_domain: CoeffDomain,
    pub base_vars: Vec<String>,
    pub vanishing_polys: Vec<NamedPoly>,
    pub invertible_poly: NamedPoly,
    pub probe_points: Vec<NamedBasePointSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedBasePointSpec {
    pub label: String,
    pub coords: Vec<(String, PolyExpr)>,
}

/// 診断層・整数診断タスクの未検証入力仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagnosticsTaskSpec {
    pub name: String,
    /// 診断複体の係数環 `Λ ∈ {Z, Q, F_p}`。
    pub diagnostic_coeff: CoeffDomain,
    pub nerve: SupportedNerveSpec,
    pub readout: DiagnosticsReadoutSpec,
    pub coeff_change: Option<CoeffChangeComparisonSpec>,
    pub collisions: Vec<CollisionComparisonSpec>,
    pub r_point_probe: Option<RPointProbeSpec>,
    pub dimension_realization: Option<DimensionRealizationSpec>,
    /// partition 層別の安全上限（超過時は誤判定せず `undetermined`）。
    pub max_partitions: Option<usize>,
    pub provenance: Provenance,
}

/// 型・参照・K1 nerve 端点・全射 reading・partition 粗化整合を検証済みの診断タスク。
/// （注意: `Static` reading の adequacy 自体は計算核で判定し、`reading_adequate` と沈黙契約へ反映する。）
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedDiagnosticsTask {
    spec: DiagnosticsTaskSpec,
}

impl CheckedDiagnosticsTask {
    pub fn spec(&self) -> &DiagnosticsTaskSpec {
        &self.spec
    }
}

/// K1 `TargetSupportedNerve` の chart・edge・face 端点整合を独立検証する（Atlas 細分化でも共用）。
pub fn validate_supported_nerve(
    nerve: &SupportedNerveSpec,
    valid_targets: &BTreeSet<&str>,
    context: &str,
) -> Result<(), ValidationError> {
    let mut chart_names = BTreeSet::new();
    for ch in &nerve.charts {
        if ch.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "nerve_chart".to_owned(),
            });
        }
        if !chart_names.insert(ch.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "nerve_chart",
                name: ch.name.clone(),
            });
        }
        for s in &ch.support {
            if !valid_targets.contains(s.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "target",
                    name: s.clone(),
                    context: format!("{context} chart `{}`", ch.name),
                });
            }
        }
    }

    let mut edge_map: BTreeMap<&str, (&str, &str)> = BTreeMap::new();
    for e in &nerve.edges {
        if e.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "nerve_edge".to_owned(),
            });
        }
        if !chart_names.contains(e.left.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "nerve_chart",
                name: e.left.clone(),
                context: format!("{context} edge `{}` left", e.name),
            });
        }
        if !chart_names.contains(e.right.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "nerve_chart",
                name: e.right.clone(),
                context: format!("{context} edge `{}` right", e.name),
            });
        }
        if edge_map
            .insert(e.name.as_str(), (e.left.as_str(), e.right.as_str()))
            .is_some()
        {
            return Err(ValidationError::DuplicateDecl {
                kind: "nerve_edge",
                name: e.name.clone(),
            });
        }
    }

    let mut face_names = BTreeSet::new();
    for f in &nerve.faces {
        if f.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "nerve_face".to_owned(),
            });
        }
        if !face_names.insert(f.name.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "nerve_face",
                name: f.name.clone(),
            });
        }
        let Some(&(l0, r0)) = edge_map.get(f.e0.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "nerve_edge",
                name: f.e0.clone(),
                context: format!("{context} face `{}` e0", f.name),
            });
        };
        let Some(&(l1, r1)) = edge_map.get(f.e1.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "nerve_edge",
                name: f.e1.clone(),
                context: format!("{context} face `{}` e1", f.name),
            });
        };
        let Some(&(l2, r2)) = edge_map.get(f.e2.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "nerve_edge",
                name: f.e2.clone(),
                context: format!("{context} face `{}` e2", f.name),
            });
        };
        if l0 != l1 || r0 != l2 || r1 != r2 {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "{context} face `{}` violates K1 endpoint equations: e0=({l0},{r0}), e1=({l1},{r1}), e2=({l2},{r2})",
                    f.name
                ),
            });
        }
    }
    Ok(())
}

/// `DiagnosticsTaskSpec` を検証して `CheckedDiagnosticsTask` を構築する。
pub fn validate_diagnostics_task(
    spec: DiagnosticsTaskSpec,
) -> Result<CheckedDiagnosticsTask, ValidationError> {
    if spec.name.trim().is_empty() {
        return Err(ValidationError::EmptyName {
            context: "diagnostics_task".to_owned(),
        });
    }
    let ctx = format!("diagnostics_task `{}`", spec.name);
    validate_coeff_domain(&spec.diagnostic_coeff, &ctx)?;
    if spec.provenance.origins.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: format!("missing provenance in {ctx}"),
        });
    }
    validate_provenance(&spec.provenance, &ctx)?;

    let (source_set, target_set, law_names, poly_base_vars) = match &spec.readout {
        DiagnosticsReadoutSpec::Static {
            sources,
            targets,
            reading,
            laws,
        } => {
            let mut s_set = BTreeSet::new();
            for s in sources {
                if s.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "source".to_owned(),
                    });
                }
                if !s_set.insert(s.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "source",
                        name: s.clone(),
                    });
                }
            }
            let mut t_set = BTreeSet::new();
            for t in targets {
                if t.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "target".to_owned(),
                    });
                }
                if !t_set.insert(t.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "target",
                        name: t.clone(),
                    });
                }
            }
            let mut q_seen = BTreeSet::new();
            let mut q_img = BTreeSet::new();
            for (s, t) in reading {
                if !s_set.contains(s.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "source",
                        name: s.clone(),
                        context: "diagnostics reading".to_owned(),
                    });
                }
                if !t_set.contains(t.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "target",
                        name: t.clone(),
                        context: "diagnostics reading".to_owned(),
                    });
                }
                if !q_seen.insert(s.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "reading_source",
                        name: s.clone(),
                    });
                }
                q_img.insert(t.as_str());
            }
            if q_seen.len() != s_set.len() {
                return Err(ValidationError::ConversionError {
                    detail: "reading q: Source -> T must assign every source".to_owned(),
                });
            }
            if q_img.len() != t_set.len() {
                return Err(ValidationError::ConversionError {
                    detail: "reading q: Source -> T must be surjective onto targets".to_owned(),
                });
            }
            let mut l_names = BTreeSet::new();
            for law in laws {
                if law.law_name.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "law".to_owned(),
                    });
                }
                if !l_names.insert(law.law_name.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "law",
                        name: law.law_name.clone(),
                    });
                }
                let mut v_seen = BTreeSet::new();
                for (s, lit) in &law.values {
                    if !s_set.contains(s.as_str()) {
                        return Err(ValidationError::UnknownRef {
                            kind: "source",
                            name: s.clone(),
                            context: format!("law `{}` readout", law.law_name),
                        });
                    }
                    if !v_seen.insert(s.as_str()) {
                        return Err(ValidationError::DuplicateDecl {
                            kind: "law_source_value",
                            name: s.clone(),
                        });
                    }
                    let lit_dom = lit.domain();
                    validate_coeff_domain(&lit_dom, &format!("law `{}` value `{s}`", law.law_name))?;
                    validate_scalar_lit(lit, &lit_dom, &format!("law `{}` value `{s}`", law.law_name))?;
                }
                if v_seen.len() != s_set.len() {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "law `{}` must assign a value to every source",
                            law.law_name
                        ),
                    });
                }
            }
            (s_set, t_set, l_names, None)
        }
        DiagnosticsReadoutSpec::Polynomial {
            base_domain,
            base_vars,
            base_relations,
            sources,
            laws,
        } => {
            validate_coeff_domain(base_domain, &format!("{ctx} base_domain"))?;
            let mut bv_set = BTreeSet::new();
            for v in base_vars {
                if v.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "base_var".to_owned(),
                    });
                }
                if !bv_set.insert(v.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "base_var",
                        name: v.clone(),
                    });
                }
            }
            let mut br_seen = BTreeSet::new();
            for rel in base_relations {
                if rel.name.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "base_relation".to_owned(),
                    });
                }
                if !br_seen.insert(rel.name.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "base_relation",
                        name: rel.name.clone(),
                    });
                }
                check_expr_refs(
                    &rel.expr,
                    &bv_set,
                    &format!("base_relation `{}`", rel.name),
                )?;
            }
            let mut s_set = BTreeSet::new();
            for s in sources {
                if s.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "source".to_owned(),
                    });
                }
                if !s_set.insert(s.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "source",
                        name: s.clone(),
                    });
                }
            }
            let mut l_names = BTreeSet::new();
            for law in laws {
                if law.law_name.trim().is_empty() {
                    return Err(ValidationError::EmptyName {
                        context: "law".to_owned(),
                    });
                }
                if !l_names.insert(law.law_name.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "law",
                        name: law.law_name.clone(),
                    });
                }
                let mut v_seen = BTreeSet::new();
                for (s, expr) in &law.values {
                    if !s_set.contains(s.as_str()) {
                        return Err(ValidationError::UnknownRef {
                            kind: "source",
                            name: s.clone(),
                            context: format!("poly law `{}` readout", law.law_name),
                        });
                    }
                    if !v_seen.insert(s.as_str()) {
                        return Err(ValidationError::DuplicateDecl {
                            kind: "poly_law_source",
                            name: s.clone(),
                        });
                    }
                    check_expr_refs(
                        expr,
                        &bv_set,
                        &format!("poly law `{}` source `{s}`", law.law_name),
                    )?;
                }
                if v_seen.len() != s_set.len() {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "poly law `{}` must assign a readout polynomial to every source",
                            law.law_name
                        ),
                    });
                }
            }
            (s_set.clone(), s_set, l_names, Some(bv_set))
        }
    };

    validate_supported_nerve(&spec.nerve, &target_set, &ctx)?;

    if let Some(cc) = &spec.coeff_change {
        validate_coeff_domain(&cc.target_domain, &format!("{ctx} coeff_change"))?;
        if let Some(zc) = &cc.explicit_z_complex {
            if zc.d0.len() != zc.dim1 || zc.d0.iter().any(|r| r.len() != zc.dim0) {
                return Err(ValidationError::ConversionError {
                    detail: "explicit_z_complex d0 matrix shape mismatch".to_owned(),
                });
            }
            if let Some(coc) = &zc.designated_cocycle
                && coc.len() != zc.dim1
            {
                return Err(ValidationError::ConversionError {
                    detail: "explicit_z_complex designated_cocycle length mismatch".to_owned(),
                });
            }
        }
    }

    for col in &spec.collisions {
        if col.label.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "collision.label".to_owned(),
            });
        }
        if !law_names.contains(col.law_name.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "law",
                name: col.law_name.clone(),
                context: format!("collision `{}`", col.label),
            });
        }
        validate_partition(
            &col.fine_partition,
            &source_set,
            &format!("collision `{}` fine", col.label),
        )?;
        validate_partition(
            &col.coarse_partition,
            &source_set,
            &format!("collision `{}` coarse", col.label),
        )?;
        check_coarsening(
            &col.fine_partition,
            &col.coarse_partition,
            &format!("collision `{}`", col.label),
        )?;
        for (p_idx, path) in col.alternative_merge_paths.iter().enumerate() {
            let mut prev: &[Vec<String>] = &col.fine_partition;
            for (s_idx, step) in path.iter().enumerate() {
                let p_ctx = format!("collision `{}` path[{p_idx}][{s_idx}]", col.label);
                validate_partition(step, &source_set, &p_ctx)?;
                check_coarsening(prev, step, &p_ctx)?;
                prev = step;
            }
            check_coarsening(
                prev,
                &col.coarse_partition,
                &format!("collision `{}` path[{p_idx}] -> coarse", col.label),
            )?;
        }
    }

    if let Some(rp) = &spec.r_point_probe {
        let Some(bv_set) = &poly_base_vars else {
            return Err(ValidationError::ConversionError {
                detail: "r_point_probe requires Polynomial readout".to_owned(),
            });
        };
        if rp.ring_var.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "r_point_probe.ring_var".to_owned(),
            });
        }
        let expected_len = rp.ring_max_deg + 1;
        let empty = BTreeSet::new();
        let mut pt_labels = BTreeSet::new();
        for pt in &rp.points {
            if pt.label.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "r_point_probe.point".to_owned(),
                });
            }
            if !pt_labels.insert(pt.label.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "r_point",
                    name: pt.label.clone(),
                });
            }
            let mut seen_vars = BTreeSet::new();
            for (v, coords) in &pt.coords {
                if !bv_set.contains(v.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "base_var",
                        name: v.clone(),
                        context: format!("r_point `{}`", pt.label),
                    });
                }
                if !seen_vars.insert(v.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "r_point_coord",
                        name: v.clone(),
                    });
                }
                if coords.len() != expected_len {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "r_point `{}` coord `{v}` has length {}, expected {expected_len}",
                            pt.label,
                            coords.len()
                        ),
                    });
                }
                for c in coords {
                    check_expr_refs(c, &empty, &format!("r_point `{}` coord `{v}`", pt.label))?;
                }
            }
            if seen_vars.len() != bv_set.len() {
                return Err(ValidationError::ConversionError {
                    detail: format!("r_point `{}` must assign every base_var", pt.label),
                });
            }
        }
    }

    if let Some(dr) = &spec.dimension_realization {
        validate_coeff_domain(&dr.base_domain, &format!("{ctx} dimension_realization"))?;
        let mut dr_vars = BTreeSet::new();
        for v in &dr.base_vars {
            if v.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "dimension_realization.base_var".to_owned(),
                });
            }
            if !dr_vars.insert(v.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "dimension_realization_var",
                    name: v.clone(),
                });
            }
        }
        let mut vp_seen = BTreeSet::new();
        for vp in &dr.vanishing_polys {
            if vp.name.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "dimension_realization.vanishing_poly".to_owned(),
                });
            }
            if !vp_seen.insert(vp.name.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "vanishing_poly",
                    name: vp.name.clone(),
                });
            }
            check_expr_refs(
                &vp.expr,
                &dr_vars,
                &format!("dimension_realization vanishing `{}`", vp.name),
            )?;
        }
        if dr.invertible_poly.name.trim().is_empty() {
            return Err(ValidationError::EmptyName {
                context: "dimension_realization.invertible_poly".to_owned(),
            });
        }
        check_expr_refs(
            &dr.invertible_poly.expr,
            &dr_vars,
            "dimension_realization.invertible_poly",
        )?;
        let empty = BTreeSet::new();
        let mut probe_seen = BTreeSet::new();
        for pt in &dr.probe_points {
            if pt.label.trim().is_empty() {
                return Err(ValidationError::EmptyName {
                    context: "dimension_realization.probe_point".to_owned(),
                });
            }
            if !probe_seen.insert(pt.label.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "probe_point",
                    name: pt.label.clone(),
                });
            }
            let mut seen_vars = BTreeSet::new();
            for (v, expr) in &pt.coords {
                if !dr_vars.contains(v.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "base_var",
                        name: v.clone(),
                        context: format!("probe_point `{}`", pt.label),
                    });
                }
                if !seen_vars.insert(v.as_str()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "probe_point_coord",
                        name: v.clone(),
                    });
                }
                check_expr_refs(expr, &empty, &format!("probe_point `{}` `{v}`", pt.label))?;
            }
            if seen_vars.len() != dr_vars.len() {
                return Err(ValidationError::ConversionError {
                    detail: format!("probe_point `{}` must assign every base_var", pt.label),
                });
            }
        }
    }

    Ok(CheckedDiagnosticsTask { spec })
}

fn validate_partition(
    blocks: &[Vec<String>],
    source_set: &BTreeSet<&str>,
    context: &str,
) -> Result<(), ValidationError> {
    let mut seen = BTreeSet::new();
    for block in blocks {
        if block.is_empty() {
            return Err(ValidationError::ConversionError {
                detail: format!("{context} partition contains an empty block"),
            });
        }
        for s in block {
            if !source_set.contains(s.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "source",
                    name: s.clone(),
                    context: context.to_owned(),
                });
            }
            if !seen.insert(s.as_str()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "partition_source",
                    name: s.clone(),
                });
            }
        }
    }
    if seen.len() != source_set.len() {
        return Err(ValidationError::ConversionError {
            detail: format!("{context} partition does not cover all sources"),
        });
    }
    Ok(())
}

/// `coarse` が `fine` の粗化（各細ブロックが単一の粗ブロックに含まれる）であることを検査する。
fn check_coarsening(
    fine: &[Vec<String>],
    coarse: &[Vec<String>],
    context: &str,
) -> Result<(), ValidationError> {
    let mut elem_to_coarse: BTreeMap<&str, usize> = BTreeMap::new();
    for (idx, block) in coarse.iter().enumerate() {
        for s in block {
            elem_to_coarse.insert(s.as_str(), idx);
        }
    }
    for block in fine {
        let first_idx = elem_to_coarse.get(block[0].as_str()).copied();
        for s in block.iter().skip(1) {
            if elem_to_coarse.get(s.as_str()).copied() != first_idx {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "{context}: coarse partition is not a coarsening of fine partition"
                    ),
                });
            }
        }
    }
    Ok(())
}
