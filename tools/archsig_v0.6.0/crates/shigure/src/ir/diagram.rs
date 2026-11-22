//! 固定図式の全補完 IR（`DiagramSpec` / `CheckedDiagramTask`、G-140 F1・F1.1–F1.2）。

use crate::ir::change::{ChangeSpec, EditableTarget, EvalCondition, FixedTarget};
use crate::ir::morphism::{
    MorphismDirection, StateMorphism, validate_state_morphism_checked_endpoints,
};
use crate::ir::presentation::{LawKind, Presentation};
use crate::ir::provenance::Provenance;
use crate::ir::validate::{
    CheckedChangeSpec, CheckedEvalCondition, ValidationError, collect_eval_unobserved,
    collect_morphism_unobserved, collect_presentation_unobserved, require_non_empty,
    validate_opt_source_ref, validate_presentation_ref_checked_params, validate_provenance,
};
use crate::ir::validate_change::{
    collect_and_check_param_names, validate_change_spec_struct_only,
    validate_eval_condition_checked_params,
};
use std::collections::{BTreeMap, BTreeSet};

/// 図式 $J$ の頂点（固定部分圏 $K$ に属するかどうかを `is_fixed` で区別する）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagramVertex {
    pub name: String,
    pub presentation: Presentation,
    /// `true` のとき $K \hookrightarrow J$ に属する固定頂点（探索パラメータ不可・編集不可）。
    pub is_fixed: bool,
    pub provenance: Option<crate::ir::provenance::SourceRef>,
}

/// 図式 $J$ の生成辺（実状態比較射・操作語翻訳を保持）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagramEdge {
    pub name: String,
    pub source: String,
    pub target: String,
    pub morphism: StateMorphism,
    /// `true` のとき $K \hookrightarrow J$ に属する固定辺（両端点とも固定頂点でパラメータ不可）。
    pub is_fixed: bool,
    pub provenance: Option<crate::ir::provenance::SourceRef>,
}

/// 図式 $J$ の生成関係 `lhs = rhs`（生成辺名の合成列同士の可換条件）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagramRelation {
    pub name: String,
    pub lhs: Vec<String>,
    pub rhs: Vec<String>,
    pub provenance: Option<crate::ir::provenance::SourceRef>,
}

/// 固定図式の補完問題仕様（図式形 $J$・固定部分圏 $K$・許容変換 $H$・評価条件 $P$）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagramSpec {
    pub name: String,
    pub direction: MorphismDirection,
    pub vertices: Vec<DiagramVertex>,
    pub edges: Vec<DiagramEdge>,
    pub relations: Vec<DiagramRelation>,
    pub change_spec: ChangeSpec,
    pub eval_condition: Option<EvalCondition>,
    pub edge_eval_conditions: BTreeMap<String, EvalCondition>,
    pub provenance: Provenance,
}

/// 検証済みの図式補完タスク。構築時に頂点・辺・固定部分圏・射向き・関係合成・係数域の整合を保証する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedDiagramTask {
    spec: DiagramSpec,
    checked_change_spec: CheckedChangeSpec,
    checked_eval_condition: Option<CheckedEvalCondition>,
    checked_edge_evals: BTreeMap<String, CheckedEvalCondition>,
}

impl CheckedDiagramTask {
    pub fn validate(spec: DiagramSpec) -> Result<Self, ValidationError> {
        require_non_empty(&spec.name, "diagram.name")?;
        validate_provenance(&spec.provenance, &format!("diagram `{}`", spec.name))?;
        let param_names = collect_and_check_param_names(&spec.change_spec)?;
        let checked_change_spec = validate_change_spec_struct_only(spec.change_spec.clone())?;
        let domain = &checked_change_spec.inner().coeff_domain;

        let mut vertices_by_name: BTreeMap<&str, &DiagramVertex> = BTreeMap::new();
        let mut vertices_by_pres: BTreeMap<&str, Vec<(&Presentation, bool)>> = BTreeMap::new();
        let empty_params = BTreeSet::new();

        for v in &spec.vertices {
            require_non_empty(&v.name, "diagram.vertex.name")?;
            validate_opt_source_ref(
                v.provenance.as_ref(),
                &format!("diagram vertex `{}`", v.name),
            )?;
            if vertices_by_name.insert(v.name.as_str(), v).is_some() {
                return Err(ValidationError::DuplicateDecl {
                    kind: "diagram vertex",
                    name: v.name.clone(),
                });
            }
            if &v.presentation.coeff_domain != domain {
                return Err(ValidationError::DomainMismatch {
                    expected: domain.clone(),
                    actual: v.presentation.coeff_domain.clone(),
                    context: format!("diagram vertex `{}`", v.name),
                });
            }
            let allowed = if v.is_fixed {
                &empty_params
            } else {
                &param_names
            };
            validate_presentation_ref_checked_params(&v.presentation, allowed)?;
            let bucket = vertices_by_pres
                .entry(v.presentation.name.as_str())
                .or_default();
            if let Some((existing_pres, _)) = bucket.first()
                && *existing_pres != &v.presentation
            {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "diagram vertex `{}` reuses presentation name `{}` with differing definition",
                        v.name, v.presentation.name
                    ),
                });
            }
            bucket.push((&v.presentation, v.is_fixed));
        }

        let mut edges_by_name: BTreeMap<&str, &DiagramEdge> = BTreeMap::new();
        for e in &spec.edges {
            require_non_empty(&e.name, "diagram.edge.name")?;
            validate_opt_source_ref(e.provenance.as_ref(), &format!("diagram edge `{}`", e.name))?;
            if edges_by_name.insert(e.name.as_str(), e).is_some() {
                return Err(ValidationError::DuplicateDecl {
                    kind: "diagram edge",
                    name: e.name.clone(),
                });
            }
            let src_v = vertices_by_name.get(e.source.as_str()).ok_or_else(|| {
                ValidationError::UnknownRef {
                    kind: "diagram vertex",
                    name: e.source.clone(),
                    context: format!("diagram edge `{}` source", e.name),
                }
            })?;
            let tgt_v = vertices_by_name.get(e.target.as_str()).ok_or_else(|| {
                ValidationError::UnknownRef {
                    kind: "diagram vertex",
                    name: e.target.clone(),
                    context: format!("diagram edge `{}` target", e.name),
                }
            })?;

            // 部分圏 K ↪ J の閉性: 固定辺は両端点とも固定頂点であり、パラメータを許さない。
            if e.is_fixed && (!src_v.is_fixed || !tgt_v.is_fixed) {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "fixed diagram edge `{}` must connect two fixed vertices in K (got `{}` fixed={}, `{}` fixed={})",
                        e.name, src_v.name, src_v.is_fixed, tgt_v.name, tgt_v.is_fixed
                    ),
                });
            }

            let (morph_src_v, morph_tgt_v) = match spec.direction {
                MorphismDirection::StateMap => (src_v, tgt_v),
                MorphismDirection::TimeOrder => (tgt_v, src_v),
            };
            let allowed = if e.is_fixed {
                &empty_params
            } else {
                &param_names
            };
            validate_state_morphism_checked_endpoints(
                &e.morphism,
                &morph_src_v.presentation,
                &morph_tgt_v.presentation,
                allowed,
                &format!("diagram edge `{}`", e.name),
            )?;
        }

        validate_diagram_relations(&spec, &edges_by_name)?;
        let morphs: Vec<(&StateMorphism, bool)> = spec
            .edges
            .iter()
            .map(|e| (&e.morphism, e.is_fixed))
            .collect();
        validate_scoped_change_targets(&spec.change_spec, &vertices_by_pres, &morphs, "diagram")?;

        let checked_eval_condition = spec
            .eval_condition
            .clone()
            .map(|c| validate_eval_condition_checked_params(c, domain, &param_names))
            .transpose()?;

        let mut checked_edge_evals = BTreeMap::new();
        for (edge_name, cond) in &spec.edge_eval_conditions {
            if !edges_by_name.contains_key(edge_name.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "diagram edge",
                    name: edge_name.clone(),
                    context: "diagram edge_eval_conditions".to_owned(),
                });
            }
            let checked =
                validate_eval_condition_checked_params(cond.clone(), domain, &param_names)?;
            checked_edge_evals.insert(edge_name.clone(), checked);
        }

        Ok(Self {
            spec,
            checked_change_spec,
            checked_eval_condition,
            checked_edge_evals,
        })
    }

    pub fn spec(&self) -> &DiagramSpec {
        &self.spec
    }

    pub fn change_spec(&self) -> &ChangeSpec {
        self.checked_change_spec.inner()
    }

    pub fn eval_condition(&self) -> Option<&EvalCondition> {
        self.checked_eval_condition
            .as_ref()
            .map(CheckedEvalCondition::inner)
    }

    pub fn edge_eval_condition(&self, edge: &str) -> Option<&EvalCondition> {
        self.checked_edge_evals
            .get(edge)
            .map(CheckedEvalCondition::inner)
    }

    pub fn vertex(&self, name: &str) -> Option<&DiagramVertex> {
        self.spec.vertices.iter().find(|v| v.name == name)
    }

    pub fn edge(&self, name: &str) -> Option<&DiagramEdge> {
        self.spec.edges.iter().find(|e| e.name == name)
    }

    /// 図式タスク全体に含まれる未観測 slot を収集する。
    pub fn unobserved_slots(&self) -> Vec<String> {
        let mut slots = BTreeSet::new();
        for v in &self.spec.vertices {
            collect_presentation_unobserved(&v.presentation, &mut slots);
        }
        for e in &self.spec.edges {
            collect_morphism_unobserved(
                &e.morphism.state_comparisons,
                &e.morphism.word_translation,
                &mut slots,
            );
        }
        if let Some(ec) = self.eval_condition() {
            collect_eval_unobserved(ec, &mut slots);
        }
        for ec in self.checked_edge_evals.values() {
            collect_eval_unobserved(ec.inner(), &mut slots);
        }
        slots.into_iter().collect()
    }
}

fn validate_diagram_relations(
    spec: &DiagramSpec,
    edges_by_name: &BTreeMap<&str, &DiagramEdge>,
) -> Result<(), ValidationError> {
    let mut seen = BTreeSet::new();
    for rel in &spec.relations {
        require_non_empty(&rel.name, "diagram.relation.name")?;
        validate_opt_source_ref(
            rel.provenance.as_ref(),
            &format!("diagram relation `{}`", rel.name),
        )?;
        if !seen.insert(rel.name.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "diagram relation",
                name: rel.name.clone(),
            });
        }
        let check_chain = |chain: &[String],
                           side: &str|
         -> Result<(String, String), ValidationError> {
            if chain.is_empty() {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "diagram relation `{}` {side} edge chain must be non-empty",
                        rel.name
                    ),
                });
            }
            let first_e = edges_by_name.get(chain[0].as_str()).ok_or_else(|| {
                ValidationError::UnknownRef {
                    kind: "diagram edge",
                    name: chain[0].clone(),
                    context: format!("diagram relation `{}` ({side})", rel.name),
                }
            })?;
            let start = first_e.source.clone();
            let mut cur_end = first_e.target.as_str();
            for name in &chain[1..] {
                let edge = edges_by_name.get(name.as_str()).ok_or_else(|| {
                    ValidationError::UnknownRef {
                        kind: "diagram edge",
                        name: name.clone(),
                        context: format!("diagram relation `{}` ({side})", rel.name),
                    }
                })?;
                if edge.source != cur_end {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "diagram relation `{}` {side} chain is not composable at edge `{}`: expected source `{cur_end}`, got `{}`",
                            rel.name, edge.name, edge.source
                        ),
                    });
                }
                cur_end = edge.target.as_str();
            }
            Ok((start, cur_end.to_owned()))
        };
        let (l_start, l_end) = check_chain(&rel.lhs, "lhs")?;
        let (r_start, r_end) = check_chain(&rel.rhs, "rhs")?;
        if l_start != r_start || l_end != r_end {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "diagram relation `{}` endpoints mismatch: lhs `{l_start} -> {l_end}` vs rhs `{r_start} -> {r_end}`",
                    rel.name
                ),
            });
        }
    }
    Ok(())
}

/// 図式・経路・移送にわたる許容変換 `change_spec` の固定/編集ターゲット参照・種別・固定部分圏制約を検査する。
pub(crate) fn validate_scoped_change_targets(
    change_spec: &ChangeSpec,
    presentations: &BTreeMap<&str, Vec<(&Presentation, bool)>>,
    morphisms: &[(&StateMorphism, bool)],
    label: &str,
) -> Result<(), ValidationError> {
    let find_pres_phase_law_kinds = |pres_name: &str, phase: &str, law: &str| {
        presentations.get(pres_name).map(|vs| {
            let kinds: Vec<LawKind> = vs
                .iter()
                .filter_map(|(pres, _)| {
                    pres.phase(phase)
                        .and_then(|ph| ph.state_laws.iter().find(|l| l.name == law))
                        .map(|l| l.kind)
                })
                .collect();
            (vs, kinds)
        })
    };

    for target in &change_spec.fixed {
        match target {
            FixedTarget::SemanticLaw {
                presentation,
                phase,
                law,
            } => {
                let Some((_, kinds)) = find_pres_phase_law_kinds(presentation, phase, law) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "semantic_law",
                        name: format!("{presentation}.{phase}.{law}"),
                        context: format!("{label} change_spec fixed"),
                    });
                };
                if kinds.is_empty() {
                    return Err(ValidationError::UnknownRef {
                        kind: "semantic_law",
                        name: format!("{presentation}.{phase}.{law}"),
                        context: format!("{label} change_spec fixed"),
                    });
                }
                if !kinds.contains(&LawKind::Semantic) {
                    return Err(ValidationError::ConversionError {
                        detail: format!("`{presentation}.{phase}.{law}` is not a semantic law"),
                    });
                }
            }
            FixedTarget::RepresentationLaw {
                presentation,
                phase,
                law,
            } => {
                let Some((_, kinds)) = find_pres_phase_law_kinds(presentation, phase, law) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "representation_law",
                        name: format!("{presentation}.{phase}.{law}"),
                        context: format!("{label} change_spec fixed"),
                    });
                };
                if kinds.is_empty() {
                    return Err(ValidationError::UnknownRef {
                        kind: "representation_law",
                        name: format!("{presentation}.{phase}.{law}"),
                        context: format!("{label} change_spec fixed"),
                    });
                }
                if !kinds.contains(&LawKind::Representation) {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "`{presentation}.{phase}.{law}` is not a representation law"
                        ),
                    });
                }
            }
            FixedTarget::OperationExpr {
                presentation,
                operation,
            } => {
                let Some(vs) = presentations.get(presentation.as_str()) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "presentation",
                        name: presentation.clone(),
                        context: format!("{label} change_spec fixed"),
                    });
                };
                if !vs.iter().any(|(p, _)| p.operation(operation).is_some()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "operation",
                        name: format!("{presentation}.{operation}"),
                        context: format!("{label} change_spec fixed"),
                    });
                }
            }
            FixedTarget::ObservationExpr {
                presentation,
                phase,
                observation,
            } => {
                let Some(vs) = presentations.get(presentation.as_str()) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "presentation",
                        name: presentation.clone(),
                        context: format!("{label} change_spec fixed"),
                    });
                };
                if !vs.iter().any(|(p, _)| {
                    p.observations
                        .iter()
                        .any(|o| o.phase == *phase && o.name == *observation)
                }) {
                    return Err(ValidationError::UnknownRef {
                        kind: "observation",
                        name: format!("{presentation}.{phase}.{observation}"),
                        context: format!("{label} change_spec fixed"),
                    });
                }
            }
            FixedTarget::StateComparisonExpr { after_phase } => {
                let exists = morphisms.iter().any(|(m, _)| {
                    m.state_comparisons
                        .iter()
                        .any(|sc| sc.after_phase == *after_phase)
                });
                if !exists {
                    return Err(ValidationError::UnknownRef {
                        kind: "state_comparison",
                        name: after_phase.clone(),
                        context: format!("{label} change_spec fixed"),
                    });
                }
            }
            FixedTarget::WordTranslationOp { operation } => {
                let exists = morphisms
                    .iter()
                    .any(|(m, _)| m.word_translation.for_operation(operation).is_some());
                if !exists {
                    return Err(ValidationError::UnknownRef {
                        kind: "word_translation",
                        name: operation.clone(),
                        context: format!("{label} change_spec fixed"),
                    });
                }
            }
        }
    }

    for target in &change_spec.editable {
        match target {
            EditableTarget::OperationExpr {
                presentation,
                operation,
            } => {
                let Some(vs) = presentations.get(presentation.as_str()) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "presentation",
                        name: presentation.clone(),
                        context: format!("{label} change_spec editable"),
                    });
                };
                if !vs.iter().any(|(p, _)| p.operation(operation).is_some()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "operation",
                        name: format!("{presentation}.{operation}"),
                        context: format!("{label} change_spec editable"),
                    });
                }
                if vs.iter().any(|(_, is_fixed)| *is_fixed) {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "editable target `{presentation}.{operation}` cannot belong to a fixed vertex"
                        ),
                    });
                }
            }
            EditableTarget::RepresentationLaw {
                presentation,
                phase,
                law,
            } => {
                let Some((vs, kinds)) = find_pres_phase_law_kinds(presentation, phase, law) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "representation_law",
                        name: format!("{presentation}.{phase}.{law}"),
                        context: format!("{label} change_spec editable"),
                    });
                };
                if kinds.is_empty() {
                    return Err(ValidationError::UnknownRef {
                        kind: "representation_law",
                        name: format!("{presentation}.{phase}.{law}"),
                        context: format!("{label} change_spec editable"),
                    });
                }
                if kinds.contains(&LawKind::Semantic) {
                    return Err(ValidationError::SemanticLawEditable {
                        presentation: presentation.clone(),
                        phase: phase.clone(),
                        law: law.clone(),
                    });
                }
                if vs.iter().any(|(_, is_fixed)| *is_fixed) {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "editable target `{presentation}.{phase}.{law}` cannot belong to a fixed vertex"
                        ),
                    });
                }
            }
            EditableTarget::StateComparisonExpr { after_phase } => {
                let any_exists = morphisms.iter().any(|(m, _)| {
                    m.state_comparisons
                        .iter()
                        .any(|sc| sc.after_phase == *after_phase)
                });
                if !any_exists {
                    return Err(ValidationError::UnknownRef {
                        kind: "state_comparison",
                        name: after_phase.clone(),
                        context: format!("{label} change_spec editable"),
                    });
                }
                let exists_editable = morphisms.iter().any(|(m, is_fixed)| {
                    !*is_fixed
                        && m.state_comparisons
                            .iter()
                            .any(|sc| sc.after_phase == *after_phase)
                });
                if !exists_editable {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "editable state_comparison `{after_phase}` cannot belong only to fixed edges"
                        ),
                    });
                }
            }
        }
    }
    Ok(())
}
