//! 一段変更経路・連結・細分化 IR（`PathSpec` / `CheckedPathTask`、G-140 F2–F3・F3.1・P5.1–P5.2）。

use crate::ir::change::{ChangeSpec, EvalCondition};
use crate::ir::diagram::validate_scoped_change_targets;
use crate::ir::morphism::{MorphismDirection, StateMorphism, validate_state_morphism};
use crate::ir::presentation::{ComparisonPair, Presentation, StateLaw};
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::{PolyExpr, ScalarLit};
use crate::ir::validate::{
    CheckedChangeSpec, CheckedComparisonPair, CheckedEvalCondition, ValidationError,
    collect_eval_unobserved, collect_presentation_unobserved, require_non_empty,
    validate_opt_source_ref, validate_poly_expr, validate_presentation_checked_params,
    validate_provenance, validate_scalar_lit,
};
use crate::ir::validate_change::{
    collect_and_check_param_names, validate_change_spec_checked_params,
    validate_change_spec_struct_only, validate_comparison_pair_checked_params,
    validate_eval_condition_checked_params,
};
use std::collections::{BTreeMap, BTreeSet};

/// 経路探索の対象種別（P5.2: 固定 protocol 間変更経路 vs 拡大 protocol 内実行経路の区別）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathKind {
    FixedProtocolChangePath,
    EnlargedProtocolExecutionPath,
}

/// 一段変更経路タスクの問いモード（F2・F3）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathQueryMode {
    /// 明示段数 `length` の経路族 `Path_{n,H}(start, end)` を探索する。
    Find,
    /// 指定した 2 経路列の連結と結合則・一段規則閉性を検査する。
    Concatenate {
        first: Vec<String>,
        second: Vec<String>,
    },
    /// 指定辺 `target_edge` の `length` 段細分化 fiber を計算する。
    Subdivide { target_edge: StateMorphism },
}

/// 経路の端点指定（対象頂点と任意の固定パラメータ点）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelEndpoint {
    pub vertex: String,
    pub param_values: BTreeMap<String, ScalarLit>,
}

/// 許容一段変更規則 $\mathcal{E}_{1,H}$ の生成規則 1 件（F3.1: 実射と翻訳を必須とする）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OneStepRule {
    pub name: String,
    pub from_vertex: String,
    pub to_vertex: String,
    /// この一段規則を適用する前に現在パラメータが満たすべき等式条件 `g(params) = 0`。
    pub param_guards: Vec<crate::ir::change::NamedPoly>,
    /// 適用後のパラメータ更新規則 `param -> expr(current_params)`。
    pub param_updates: BTreeMap<String, PolyExpr>,
    /// 必ず伴う実際の状態比較射と操作語翻訳（F3.1）。
    pub morphism: StateMorphism,
    /// 一段規則ごとの追加評価条件（例: 非零環条件・可逆条件）。
    pub eval_condition: Option<EvalCondition>,
    pub provenance: Option<SourceRef>,
}

/// 拡大 protocol 内実行経路の指定（P5.2）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtocolExecutionSpec {
    pub comparison: ComparisonPair,
    pub start_phase: String,
    pub start_laws: Vec<StateLaw>,
    pub end_phase: String,
    pub end_laws: Vec<StateLaw>,
    pub allowed_ops: Vec<String>,
}

/// 一段変更経路・細分化タスク仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathSpec {
    pub name: String,
    pub kind: PathKind,
    pub direction: MorphismDirection,
    pub query_mode: PathQueryMode,
    /// 明示された経路長 $n \ge 0$。`Find` / `Subdivide` で `None` の場合は無界探索として計算時に沈黙する。
    pub length: Option<usize>,
    pub vertices: BTreeMap<String, Presentation>,
    pub rules: Vec<OneStepRule>,
    pub start: Option<ModelEndpoint>,
    pub end: Option<ModelEndpoint>,
    pub protocol: Option<ProtocolExecutionSpec>,
    pub change_spec: ChangeSpec,
    pub eval_condition: Option<EvalCondition>,
    pub provenance: Provenance,
}

/// 検証済みの一段変更経路タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedPathTask {
    spec: PathSpec,
    checked_change_spec: CheckedChangeSpec,
    checked_eval_condition: Option<CheckedEvalCondition>,
    checked_protocol_cmp: Option<CheckedComparisonPair>,
}

impl CheckedPathTask {
    pub fn validate(spec: PathSpec) -> Result<Self, ValidationError> {
        require_non_empty(&spec.name, "path.name")?;
        validate_provenance(&spec.provenance, &format!("path `{}`", spec.name))?;
        let param_names = collect_and_check_param_names(&spec.change_spec)?;
        let domain = spec.change_spec.coeff_domain.clone();

        let checked_eval_condition = spec
            .eval_condition
            .clone()
            .map(|c| validate_eval_condition_checked_params(c, &domain, &param_names))
            .transpose()?;

        let (checked_change_spec, checked_protocol_cmp) = match spec.kind {
            PathKind::FixedProtocolChangePath => {
                if spec.protocol.is_some() {
                    return Err(ValidationError::ConversionError {
                        detail: "fixed_protocol_change_path must not specify `protocol`".to_owned(),
                    });
                }
                let start =
                    spec.start
                        .as_ref()
                        .ok_or_else(|| ValidationError::ConversionError {
                            detail: "fixed_protocol_change_path requires `start` endpoint"
                                .to_owned(),
                        })?;
                let end = spec
                    .end
                    .as_ref()
                    .ok_or_else(|| ValidationError::ConversionError {
                        detail: "fixed_protocol_change_path requires `end` endpoint".to_owned(),
                    })?;
                let checked_cs = validate_change_spec_struct_only(spec.change_spec.clone())?;
                validate_fixed_change_path(&spec, start, end, &domain, &param_names)?;
                let mut pres_map: BTreeMap<&str, Vec<(&Presentation, bool)>> = BTreeMap::new();
                for pres in spec.vertices.values() {
                    pres_map
                        .entry(pres.name.as_str())
                        .or_default()
                        .push((pres, false));
                }
                let mut morphs: Vec<(&StateMorphism, bool)> =
                    spec.rules.iter().map(|r| (&r.morphism, false)).collect();
                if let PathQueryMode::Subdivide { target_edge } = &spec.query_mode {
                    morphs.push((target_edge, false));
                }
                validate_scoped_change_targets(&spec.change_spec, &pres_map, &morphs, "path")?;
                (checked_cs, None)
            }
            PathKind::EnlargedProtocolExecutionPath => {
                if !matches!(spec.query_mode, PathQueryMode::Find) {
                    return Err(ValidationError::ConversionError {
                        detail: "enlarged_protocol_execution_path only supports `find` query mode"
                            .to_owned(),
                    });
                }
                if !spec.rules.is_empty() {
                    return Err(ValidationError::ConversionError {
                        detail: "enlarged_protocol_execution_path uses protocol `allowed_ops`, not one-step change rules".to_owned(),
                    });
                }
                let proto =
                    spec.protocol
                        .as_ref()
                        .ok_or_else(|| ValidationError::ConversionError {
                            detail:
                                "enlarged_protocol_execution_path requires `protocol` specification"
                                    .to_owned(),
                        })?;
                let checked_pair = validate_comparison_pair_checked_params(
                    proto.comparison.clone(),
                    &param_names,
                )?;
                let checked_cs =
                    validate_change_spec_checked_params(spec.change_spec.clone(), &checked_pair)?;
                validate_protocol_spec(proto, &domain, &param_names)?;
                (checked_cs, Some(checked_pair))
            }
        };

        Ok(Self {
            spec,
            checked_change_spec,
            checked_eval_condition,
            checked_protocol_cmp,
        })
    }

    pub fn spec(&self) -> &PathSpec {
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

    pub fn protocol_pair(&self) -> Option<&ComparisonPair> {
        self.checked_protocol_cmp
            .as_ref()
            .map(CheckedComparisonPair::inner)
    }

    /// 経路タスク全体に含まれる未観測 slot を収集する。
    pub fn unobserved_slots(&self) -> Vec<String> {
        let mut slots = BTreeSet::new();
        for pres in self.spec.vertices.values() {
            collect_presentation_unobserved(pres, &mut slots);
        }
        for rule in &self.spec.rules {
            for g in &rule.param_guards {
                g.expr.collect_unobserved(&mut slots);
            }
            for u in rule.param_updates.values() {
                u.collect_unobserved(&mut slots);
            }
            for sc in &rule.morphism.state_comparisons {
                for e in sc.map.values() {
                    e.collect_unobserved(&mut slots);
                }
            }
            for tw in &rule.morphism.word_translation.entries {
                for st in &tw.steps {
                    for e in &st.arg_exprs {
                        e.collect_unobserved(&mut slots);
                    }
                }
            }
            if let Some(ec) = &rule.eval_condition {
                collect_eval_unobserved(ec, &mut slots);
            }
        }
        if let PathQueryMode::Subdivide { target_edge } = &self.spec.query_mode {
            for sc in &target_edge.state_comparisons {
                for e in sc.map.values() {
                    e.collect_unobserved(&mut slots);
                }
            }
            for tw in &target_edge.word_translation.entries {
                for st in &tw.steps {
                    for e in &st.arg_exprs {
                        e.collect_unobserved(&mut slots);
                    }
                }
            }
        }
        if let Some(proto) = &self.spec.protocol {
            collect_presentation_unobserved(&proto.comparison.before, &mut slots);
            collect_presentation_unobserved(&proto.comparison.after, &mut slots);
            for l in proto.start_laws.iter().chain(&proto.end_laws) {
                l.polynomial.collect_unobserved(&mut slots);
            }
        }
        if let Some(ec) = self.eval_condition() {
            collect_eval_unobserved(ec, &mut slots);
        }
        slots.into_iter().collect()
    }
}

fn validate_endpoint(
    ep: &ModelEndpoint,
    vertices: &BTreeMap<String, Presentation>,
    domain: &crate::ir::term::CoeffDomain,
    param_names: &BTreeSet<String>,
    label: &str,
) -> Result<(), ValidationError> {
    if !vertices.contains_key(&ep.vertex) {
        return Err(ValidationError::UnknownRef {
            kind: "path vertex",
            name: ep.vertex.clone(),
            context: format!("path {label} endpoint"),
        });
    }
    for (p, lit) in &ep.param_values {
        if !param_names.contains(p) {
            return Err(ValidationError::UnknownRef {
                kind: "parameter",
                name: p.clone(),
                context: format!("path {label} endpoint"),
            });
        }
        validate_scalar_lit(lit, domain, &format!("path {label} param `{p}`"))?;
    }
    Ok(())
}

fn validate_fixed_change_path(
    spec: &PathSpec,
    start: &ModelEndpoint,
    end: &ModelEndpoint,
    domain: &crate::ir::term::CoeffDomain,
    param_names: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    for (v_name, pres) in &spec.vertices {
        require_non_empty(v_name, "path.vertex")?;
        if &pres.coeff_domain != domain {
            return Err(ValidationError::DomainMismatch {
                expected: domain.clone(),
                actual: pres.coeff_domain.clone(),
                context: format!("path vertex `{v_name}`"),
            });
        }
        let _ = validate_presentation_checked_params(pres.clone(), param_names)?;
    }

    validate_endpoint(start, &spec.vertices, domain, param_names, "start")?;
    validate_endpoint(end, &spec.vertices, domain, param_names, "end")?;

    let empty = BTreeSet::new();
    let mut rules_by_name: BTreeMap<&str, &OneStepRule> = BTreeMap::new();
    for rule in &spec.rules {
        require_non_empty(&rule.name, "path.rule.name")?;
        validate_opt_source_ref(
            rule.provenance.as_ref(),
            &format!("path rule `{}`", rule.name),
        )?;
        if rules_by_name.insert(rule.name.as_str(), rule).is_some() {
            return Err(ValidationError::DuplicateDecl {
                kind: "one-step rule",
                name: rule.name.clone(),
            });
        }
        let from_pres =
            spec.vertices
                .get(&rule.from_vertex)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "path vertex",
                    name: rule.from_vertex.clone(),
                    context: format!("path rule `{}` from_vertex", rule.name),
                })?;
        let to_pres =
            spec.vertices
                .get(&rule.to_vertex)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "path vertex",
                    name: rule.to_vertex.clone(),
                    context: format!("path rule `{}` to_vertex", rule.name),
                })?;

        for g in &rule.param_guards {
            require_non_empty(&g.name, &format!("path rule `{}` guard", rule.name))?;
            validate_poly_expr(
                &g.expr,
                domain,
                &empty,
                &empty,
                param_names,
                &format!("path rule `{}` guard `{}`", rule.name, g.name),
            )?;
        }
        for (p, expr) in &rule.param_updates {
            if !param_names.contains(p) {
                return Err(ValidationError::UnknownRef {
                    kind: "parameter",
                    name: p.clone(),
                    context: format!("path rule `{}` param_updates", rule.name),
                });
            }
            validate_poly_expr(
                expr,
                domain,
                &empty,
                &empty,
                param_names,
                &format!("path rule `{}` param_update `{p}`", rule.name),
            )?;
        }

        let (m_src, m_tgt) = match spec.direction {
            MorphismDirection::StateMap => (from_pres, to_pres),
            MorphismDirection::TimeOrder => (to_pres, from_pres),
        };
        validate_state_morphism(
            &rule.morphism,
            m_src,
            m_tgt,
            param_names,
            &format!("path rule `{}`", rule.name),
        )?;

        if let Some(ec) = &rule.eval_condition {
            let _ = validate_eval_condition_checked_params(ec.clone(), domain, param_names)?;
        }
    }

    match &spec.query_mode {
        PathQueryMode::Find => {}
        PathQueryMode::Concatenate { first, second } => {
            let check_seq = |seq: &[String],
                             expected_start: &str,
                             label: &str|
             -> Result<String, ValidationError> {
                let mut cur = expected_start.to_owned();
                for name in seq {
                    let rule = rules_by_name.get(name.as_str()).ok_or_else(|| {
                        ValidationError::UnknownRef {
                            kind: "one-step rule",
                            name: name.clone(),
                            context: format!("path concatenate `{label}`"),
                        }
                    })?;
                    if rule.from_vertex != cur {
                        return Err(ValidationError::ConversionError {
                            detail: format!(
                                "path concatenate `{label}` rule `{}` expects vertex `{cur}`, got `{}`",
                                rule.name, rule.from_vertex
                            ),
                        });
                    }
                    cur = rule.to_vertex.clone();
                }
                Ok(cur)
            };
            let mid = check_seq(first, &start.vertex, "first")?;
            let final_v = check_seq(second, &mid, "second")?;
            if final_v != end.vertex {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "path concatenate ends at vertex `{final_v}`, expected `{}`",
                        end.vertex
                    ),
                });
            }
        }
        PathQueryMode::Subdivide { target_edge } => {
            let start_pres = &spec.vertices[&start.vertex];
            let end_pres = &spec.vertices[&end.vertex];
            let (m_src, m_tgt) = match spec.direction {
                MorphismDirection::StateMap => (start_pres, end_pres),
                MorphismDirection::TimeOrder => (end_pres, start_pres),
            };
            validate_state_morphism(
                target_edge,
                m_src,
                m_tgt,
                param_names,
                "path subdivide target_edge",
            )?;
        }
    }

    Ok(())
}

fn validate_protocol_spec(
    proto: &ProtocolExecutionSpec,
    domain: &crate::ir::term::CoeffDomain,
    param_names: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    let after = &proto.comparison.after;
    let start_ph = after
        .phase(&proto.start_phase)
        .ok_or_else(|| ValidationError::UnknownRef {
            kind: "after phase",
            name: proto.start_phase.clone(),
            context: "protocol start_phase".to_owned(),
        })?;
    let end_ph = after
        .phase(&proto.end_phase)
        .ok_or_else(|| ValidationError::UnknownRef {
            kind: "after phase",
            name: proto.end_phase.clone(),
            context: "protocol end_phase".to_owned(),
        })?;

    let empty = BTreeSet::new();
    let start_coords: BTreeSet<String> = start_ph.coords.iter().map(|c| c.name.clone()).collect();
    for law in &proto.start_laws {
        require_non_empty(&law.name, "protocol.start_law")?;
        validate_opt_source_ref(
            law.provenance.as_ref(),
            &format!("protocol start_law `{}`", law.name),
        )?;
        validate_poly_expr(
            &law.polynomial,
            domain,
            &start_coords,
            &empty,
            param_names,
            &format!("protocol start_law `{}`", law.name),
        )?;
    }

    let end_coords: BTreeSet<String> = end_ph.coords.iter().map(|c| c.name.clone()).collect();
    for law in &proto.end_laws {
        require_non_empty(&law.name, "protocol.end_law")?;
        validate_opt_source_ref(
            law.provenance.as_ref(),
            &format!("protocol end_law `{}`", law.name),
        )?;
        validate_poly_expr(
            &law.polynomial,
            domain,
            &end_coords,
            &empty,
            param_names,
            &format!("protocol end_law `{}`", law.name),
        )?;
    }

    if proto.allowed_ops.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: "protocol execution requires at least one allowed operation".to_owned(),
        });
    }
    let mut seen_ops = BTreeSet::new();
    for op_name in &proto.allowed_ops {
        if !seen_ops.insert(op_name) {
            return Err(ValidationError::DuplicateDecl {
                kind: "protocol allowed_op",
                name: op_name.clone(),
            });
        }
        if after.operation(op_name).is_none() {
            return Err(ValidationError::UnknownRef {
                kind: "after operation",
                name: op_name.clone(),
                context: "protocol allowed_ops".to_owned(),
            });
        }
    }
    Ok(())
}
