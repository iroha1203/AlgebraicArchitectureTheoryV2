//! 射の向きの型レベル統一（状態比較射 $\mathcal{C}_R$ と時間順 $\mathcal{C}_R^{\mathrm{op}}$）および合成・検証。

use crate::ir::presentation::{
    ComparisonPair, ObservationDecl, OperationDecl, Presentation, StateComparison, TranslatedStep,
    TranslatedWord, WordTranslation,
};
use crate::ir::provenance::SourceRef;
use crate::ir::term::PolyExpr;
use crate::ir::validate::{
    ValidationError, require_non_empty, validate_opt_source_ref, validate_poly_expr,
};
use std::collections::{BTreeMap, BTreeSet};

/// 射の向きの規約（G-140 共通規約）。
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MorphismDirection {
    /// 状態比較射の向き $\mathcal{C}_R$: 変更後 `source` から変更前 `target` への写像。
    /// 合成は `outer ∘ inner`（`outer.source == inner.target`）。
    StateMap,
    /// 時間順の向き $\mathcal{C}_R^{\mathrm{op}}$: 変更前 `before` から変更後 `after` への遷移。
    /// 実体として逆向きの状態比較射 `after -> before` を保持する。
    TimeOrder,
}

impl MorphismDirection {
    pub fn wire(self) -> &'static str {
        match self {
            MorphismDirection::StateMap => "state_map",
            MorphismDirection::TimeOrder => "time_order",
        }
    }
}

/// 状態比較射の向き $\mathcal{C}_R$ で表現される実射 `source -> target`（状態写像 $h$ と操作語翻訳 $\tau$）。
///
/// 変更前後を比較するときは `source = after`、`target = before` となる。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateMorphism {
    pub source: String,
    pub target: String,
    pub state_comparisons: Vec<StateComparison>,
    pub word_translation: WordTranslation,
    pub provenance: Option<SourceRef>,
}

impl StateMorphism {
    /// `ComparisonPair` から `after -> before` 向きの `StateMorphism` を取り出す。
    pub fn from_comparison_pair(pair: &ComparisonPair) -> Self {
        Self {
            source: pair.after.name.clone(),
            target: pair.before.name.clone(),
            state_comparisons: pair.state_comparisons.clone(),
            word_translation: pair.word_translation.clone(),
            provenance: None,
        }
    }

    /// 始点・終点 `Presentation` を添えて既存の `ComparisonPair`（`before = target`, `after = source`）へ変換する。
    pub fn to_comparison_pair(
        &self,
        source: &Presentation,
        target: &Presentation,
    ) -> ComparisonPair {
        ComparisonPair {
            before: target.clone(),
            after: source.clone(),
            state_comparisons: self.state_comparisons.clone(),
            word_translation: self.word_translation.clone(),
        }
    }
}

/// 時間順 $\mathcal{C}_R^{\mathrm{op}}$ で表現される一段変更 `before -> after`。
///
/// 内部に逆向きの状態比較射 `state_map: after -> before` を保持し、合成順を型で保証する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimeStepMorphism {
    before: String,
    after: String,
    state_map: StateMorphism,
}

impl TimeStepMorphism {
    /// `before -> after` の時間順と逆向き `state_map: after -> before` の整合を検査して構築する。
    pub fn new(
        before: impl Into<String>,
        after: impl Into<String>,
        state_map: StateMorphism,
    ) -> Result<Self, ValidationError> {
        let before = before.into();
        let after = after.into();
        if state_map.source != after || state_map.target != before {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "TimeStepMorphism `{before} -> {after}` requires state_map orientation `{after} -> {before}`, got `{} -> {}`",
                    state_map.source, state_map.target
                ),
            });
        }
        Ok(Self {
            before,
            after,
            state_map,
        })
    }

    pub fn before(&self) -> &str {
        &self.before
    }

    pub fn after(&self) -> &str {
        &self.after
    }

    pub fn state_map(&self) -> &StateMorphism {
        &self.state_map
    }
}

/// 任意の `Presentation` に対する恒等射 `id_X: X -> X` を構成する。
pub fn identity_state_morphism(pres: &Presentation) -> StateMorphism {
    let state_comparisons = pres
        .phases
        .iter()
        .map(|ph| {
            let map = ph
                .coords
                .iter()
                .map(|c| (c.name.clone(), PolyExpr::StateVar(c.name.clone())))
                .collect();
            StateComparison {
                after_phase: ph.name.clone(),
                before_phase: ph.name.clone(),
                map,
                provenance: ph.provenance.clone(),
            }
        })
        .collect();

    let entries = pres
        .operations
        .iter()
        .map(|op| {
            let arg_exprs = op
                .args
                .iter()
                .map(|(arg_name, _)| PolyExpr::ArgVar(arg_name.clone()))
                .collect();
            TranslatedWord {
                after_operation: op.name.clone(),
                steps: vec![TranslatedStep {
                    before_operation: op.name.clone(),
                    arg_exprs,
                }],
                provenance: op.provenance.clone(),
            }
        })
        .collect();

    StateMorphism {
        source: pres.name.clone(),
        target: pres.name.clone(),
        state_comparisons,
        word_translation: WordTranslation { entries },
        provenance: pres.provenance.origins.first().cloned(),
    }
}

/// 深い木でもスタックを消費しない反復 `PolyExpr` 同時置換。
pub(crate) fn substitute_poly_expr_iter(
    expr: &PolyExpr,
    state_map: &BTreeMap<String, PolyExpr>,
    arg_map: &BTreeMap<String, PolyExpr>,
    param_map: &BTreeMap<String, PolyExpr>,
) -> PolyExpr {
    enum Frame<'a> {
        Visit(&'a PolyExpr),
        Neg,
        Add,
        Sub,
        Mul,
        Pow(u32),
    }
    let mut work = vec![Frame::Visit(expr)];
    let mut out: Vec<PolyExpr> = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            Frame::Visit(node) => match node {
                PolyExpr::Const(c) => out.push(PolyExpr::Const(c.clone())),
                PolyExpr::StateVar(v) => out.push(
                    state_map
                        .get(v)
                        .cloned()
                        .unwrap_or_else(|| PolyExpr::StateVar(v.clone())),
                ),
                PolyExpr::ArgVar(v) => out.push(
                    arg_map
                        .get(v)
                        .cloned()
                        .unwrap_or_else(|| PolyExpr::ArgVar(v.clone())),
                ),
                PolyExpr::ParamVar(v) => out.push(
                    param_map
                        .get(v)
                        .cloned()
                        .unwrap_or_else(|| PolyExpr::ParamVar(v.clone())),
                ),
                PolyExpr::Unobserved { slot, origin } => out.push(PolyExpr::Unobserved {
                    slot: slot.clone(),
                    origin: origin.clone(),
                }),
                PolyExpr::Neg(a) => {
                    work.push(Frame::Neg);
                    work.push(Frame::Visit(a));
                }
                PolyExpr::Add(a, b) => {
                    work.push(Frame::Add);
                    work.push(Frame::Visit(b));
                    work.push(Frame::Visit(a));
                }
                PolyExpr::Sub(a, b) => {
                    work.push(Frame::Sub);
                    work.push(Frame::Visit(b));
                    work.push(Frame::Visit(a));
                }
                PolyExpr::Mul(a, b) => {
                    work.push(Frame::Mul);
                    work.push(Frame::Visit(b));
                    work.push(Frame::Visit(a));
                }
                PolyExpr::Pow(a, e) => {
                    work.push(Frame::Pow(*e));
                    work.push(Frame::Visit(a));
                }
            },
            Frame::Neg => {
                let a = out.pop().expect("sub neg");
                out.push(PolyExpr::negate(a));
            }
            Frame::Add => {
                let b = out.pop().expect("sub add rhs");
                let a = out.pop().expect("sub add lhs");
                out.push(PolyExpr::sum(a, b));
            }
            Frame::Sub => {
                let b = out.pop().expect("sub sub rhs");
                let a = out.pop().expect("sub sub lhs");
                out.push(PolyExpr::diff(a, b));
            }
            Frame::Mul => {
                let b = out.pop().expect("sub mul rhs");
                let a = out.pop().expect("sub mul lhs");
                out.push(PolyExpr::prod(a, b));
            }
            Frame::Pow(e) => {
                let a = out.pop().expect("sub pow");
                out.push(PolyExpr::pow(a, e));
            }
        }
    }
    out.pop().expect("substituted root")
}

/// 状態比較射の向き $\mathcal{C}_R$ での合成 `outer ∘ inner : source -> outer.target`。
///
/// `inner: source -> middle` と `outer: middle -> target` に対し、状態写像の合成と、
/// `middle` 上の操作実行に伴う中間状態を追跡した操作語翻訳の合成を行う。
pub fn compose_state_order(
    outer: &StateMorphism,
    inner: &StateMorphism,
    source: &Presentation,
    middle: &Presentation,
) -> Result<StateMorphism, ValidationError> {
    if inner.source != source.name {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "compose_state_order: inner morphism source `{}` does not match presentation `{}`",
                inner.source, source.name
            ),
        });
    }
    if outer.source != inner.target || middle.name != inner.target {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "compose_state_order mismatch: inner target `{}` (middle `{}`) != outer source `{}`",
                inner.target, middle.name, outer.source
            ),
        });
    }

    let empty = BTreeMap::new();
    let mut outer_sc_by_phase: BTreeMap<&str, &StateComparison> = BTreeMap::new();
    for sc in &outer.state_comparisons {
        if outer_sc_by_phase
            .insert(sc.after_phase.as_str(), sc)
            .is_some()
        {
            return Err(ValidationError::DuplicateDecl {
                kind: "state_comparison",
                name: format!("{}.{}", outer.source, sc.after_phase),
            });
        }
    }
    let mut inner_sc_by_phase: BTreeMap<&str, &StateComparison> = BTreeMap::new();
    for sc in &inner.state_comparisons {
        if inner_sc_by_phase
            .insert(sc.after_phase.as_str(), sc)
            .is_some()
        {
            return Err(ValidationError::DuplicateDecl {
                kind: "state_comparison",
                name: format!("{}.{}", inner.source, sc.after_phase),
            });
        }
    }
    for ph in &source.phases {
        if !inner_sc_by_phase.contains_key(ph.name.as_str()) {
            return Err(ValidationError::MissingStateComparison {
                after_phase: ph.name.clone(),
            });
        }
    }

    let mut composed_scs = Vec::with_capacity(inner.state_comparisons.len());
    for sc_in in &inner.state_comparisons {
        let sc_out = outer_sc_by_phase
            .get(sc_in.before_phase.as_str())
            .ok_or_else(|| ValidationError::MissingStateComparison {
                after_phase: sc_in.before_phase.clone(),
            })?;
        let mut map = BTreeMap::new();
        for (coord, expr) in &sc_out.map {
            map.insert(
                coord.clone(),
                substitute_poly_expr_iter(expr, &sc_in.map, &empty, &empty),
            );
        }
        composed_scs.push(StateComparison {
            after_phase: sc_in.after_phase.clone(),
            before_phase: sc_out.before_phase.clone(),
            map,
            provenance: sc_in
                .provenance
                .clone()
                .or_else(|| outer.provenance.clone()),
        });
    }

    let source_ops: BTreeMap<&str, &OperationDecl> = source
        .operations
        .iter()
        .map(|op| (op.name.as_str(), op))
        .collect();
    let middle_ops: BTreeMap<&str, &OperationDecl> = middle
        .operations
        .iter()
        .map(|op| (op.name.as_str(), op))
        .collect();

    let mut seen_src_ops = BTreeSet::new();
    let mut composed_entries = Vec::with_capacity(inner.word_translation.entries.len());
    for tw_in in &inner.word_translation.entries {
        if !seen_src_ops.insert(tw_in.after_operation.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "word_translation",
                name: format!("{}.{}", source.name, tw_in.after_operation),
            });
        }
        let src_op = source_ops
            .get(tw_in.after_operation.as_str())
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "operation",
                name: tw_in.after_operation.clone(),
                context: format!("compose_state_order on `{}`", source.name),
            })?;
        let sc_in = inner_sc_by_phase
            .get(src_op.source_phase.as_str())
            .ok_or_else(|| ValidationError::MissingStateComparison {
                after_phase: src_op.source_phase.clone(),
            })?;
        let sc_end = inner_sc_by_phase
            .get(src_op.target_phase.as_str())
            .ok_or_else(|| ValidationError::MissingStateComparison {
                after_phase: src_op.target_phase.clone(),
            })?;

        let mut mid_state: BTreeMap<String, PolyExpr> = sc_in.map.clone();
        let mut cur_mid_phase = sc_in.before_phase.as_str();
        let mut steps = Vec::new();
        for (step_idx, step_in) in tw_in.steps.iter().enumerate() {
            let mid_op = middle_ops
                .get(step_in.before_operation.as_str())
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "middle operation",
                    name: step_in.before_operation.clone(),
                    context: format!("compose_state_order word `{}`", tw_in.after_operation),
                })?;
            if mid_op.source_phase != cur_mid_phase {
                return Err(ValidationError::PhasePathMismatch {
                    after_operation: tw_in.after_operation.clone(),
                    detail: format!(
                        "compose_state_order step {step_idx} (`{}`) expects middle phase `{cur_mid_phase}`, got `{}`",
                        mid_op.name, mid_op.source_phase
                    ),
                });
            }
            let tw_out = outer
                .word_translation
                .for_operation(&mid_op.name)
                .ok_or_else(|| ValidationError::MissingWordTranslation {
                    after_operation: mid_op.name.clone(),
                })?;

            if mid_op.args.len() != step_in.arg_exprs.len() {
                return Err(ValidationError::ArityMismatch {
                    context: format!(
                        "compose_state_order step `{}` in `{}`",
                        mid_op.name, tw_in.after_operation
                    ),
                    expected: mid_op.args.len(),
                    actual: step_in.arg_exprs.len(),
                });
            }
            let arg_map: BTreeMap<String, PolyExpr> = mid_op
                .args
                .iter()
                .zip(&step_in.arg_exprs)
                .map(|((a_name, _), expr)| (a_name.clone(), expr.clone()))
                .collect();

            for step_out in &tw_out.steps {
                let arg_exprs = step_out
                    .arg_exprs
                    .iter()
                    .map(|e| substitute_poly_expr_iter(e, &mid_state, &arg_map, &empty))
                    .collect();
                steps.push(TranslatedStep {
                    before_operation: step_out.before_operation.clone(),
                    arg_exprs,
                });
            }

            let mut next_mid_state = BTreeMap::new();
            for (coord, upd) in &mid_op.updates {
                next_mid_state.insert(
                    coord.clone(),
                    substitute_poly_expr_iter(upd, &mid_state, &arg_map, &empty),
                );
            }
            mid_state = next_mid_state;
            cur_mid_phase = mid_op.target_phase.as_str();
        }
        if cur_mid_phase != sc_end.before_phase.as_str() {
            return Err(ValidationError::PhasePathMismatch {
                after_operation: tw_in.after_operation.clone(),
                detail: format!(
                    "compose_state_order ends at middle phase `{cur_mid_phase}`, expected `{}`",
                    sc_end.before_phase
                ),
            });
        }

        composed_entries.push(TranslatedWord {
            after_operation: tw_in.after_operation.clone(),
            steps,
            provenance: tw_in.provenance.clone(),
        });
    }
    for op in &source.operations {
        if !seen_src_ops.contains(op.name.as_str()) {
            return Err(ValidationError::MissingWordTranslation {
                after_operation: op.name.clone(),
            });
        }
    }

    Ok(StateMorphism {
        source: inner.source.clone(),
        target: outer.target.clone(),
        state_comparisons: composed_scs,
        word_translation: WordTranslation {
            entries: composed_entries,
        },
        provenance: inner
            .provenance
            .clone()
            .or_else(|| outer.provenance.clone()),
    })
}

/// 時間順 $\mathcal{C}_R^{\mathrm{op}}$ での合成 `first ; second : first.before -> second.after`。
///
/// 内部の状態比較射は逆向き `h_{02} = first.state_map ∘ second.state_map` として合成される。
pub fn compose_time_order(
    first: &TimeStepMorphism,
    second: &TimeStepMorphism,
    middle: &Presentation,
    after: &Presentation,
) -> Result<TimeStepMorphism, ValidationError> {
    if first.after != second.before {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "compose_time_order mismatch: first after `{}` != second before `{}`",
                first.after, second.before
            ),
        });
    }
    if first.after != middle.name {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "compose_time_order mismatch: middle vertex `{}` != presentation `{}`",
                first.after, middle.name
            ),
        });
    }
    if second.after != after.name {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "compose_time_order mismatch: after vertex `{}` != presentation `{}`",
                second.after, after.name
            ),
        });
    }
    let composed_map = compose_state_order(&first.state_map, &second.state_map, after, middle)?;
    TimeStepMorphism::new(first.before.clone(), second.after.clone(), composed_map)
}

/// 端点表示を事前に検証済みの状態で `StateMorphism`（`source == target` の自己射含む）を検査する。
pub(crate) fn validate_state_morphism_checked_endpoints(
    m: &StateMorphism,
    source: &Presentation,
    target: &Presentation,
    allowed_params: &BTreeSet<String>,
    context: &str,
) -> Result<(), ValidationError> {
    if m.source != source.name {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "{context}: morphism source `{}` != presentation `{}`",
                m.source, source.name
            ),
        });
    }
    if m.target != target.name {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "{context}: morphism target `{}` != presentation `{}`",
                m.target, target.name
            ),
        });
    }
    if source.coeff_domain != target.coeff_domain {
        return Err(ValidationError::DomainMismatch {
            expected: target.coeff_domain.clone(),
            actual: source.coeff_domain.clone(),
            context: context.to_owned(),
        });
    }
    validate_morphism_correspondence(
        &m.state_comparisons,
        &m.word_translation,
        m.provenance.as_ref(),
        source,
        target,
        allowed_params,
        context,
    )
}

/// 状態比較 `state_comparisons`・観測対応・操作語翻訳 `word_translation` の共通整合検査本体。
pub(crate) fn validate_morphism_correspondence(
    state_comparisons: &[StateComparison],
    word_translation: &WordTranslation,
    provenance: Option<&SourceRef>,
    source: &Presentation,
    target: &Presentation,
    allowed_params: &BTreeSet<String>,
    context: &str,
) -> Result<(), ValidationError> {
    validate_opt_source_ref(provenance, context)?;

    let domain = &source.coeff_domain;
    let source_phase_coords: BTreeMap<&str, BTreeSet<String>> = source
        .phases
        .iter()
        .map(|p| {
            (
                p.name.as_str(),
                p.coords.iter().map(|c| c.name.clone()).collect(),
            )
        })
        .collect();
    let target_phase_coords: BTreeMap<&str, BTreeSet<String>> = target
        .phases
        .iter()
        .map(|p| {
            (
                p.name.as_str(),
                p.coords.iter().map(|c| c.name.clone()).collect(),
            )
        })
        .collect();

    let mut h_by_src_phase: BTreeMap<String, String> = BTreeMap::new();
    let empty_args = BTreeSet::new();
    for sc in state_comparisons {
        validate_opt_source_ref(
            sc.provenance.as_ref(),
            &format!("{context}.state_comparison `{}`", sc.after_phase),
        )?;
        let Some(src_coords) = source_phase_coords.get(sc.after_phase.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "source phase",
                name: sc.after_phase.clone(),
                context: context.to_owned(),
            });
        };
        let Some(tgt_coords) = target_phase_coords.get(sc.before_phase.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "target phase",
                name: sc.before_phase.clone(),
                context: context.to_owned(),
            });
        };
        if h_by_src_phase
            .insert(sc.after_phase.clone(), sc.before_phase.clone())
            .is_some()
        {
            return Err(ValidationError::DuplicateDecl {
                kind: "state_comparison",
                name: format!("{context}.{}", sc.after_phase),
            });
        }
        for tc in tgt_coords {
            if !sc.map.contains_key(tc) {
                return Err(ValidationError::MissingCoordUpdate {
                    operation: format!("{context}.state_comparison({})", sc.after_phase),
                    coord: tc.clone(),
                });
            }
        }
        for (coord, expr) in &sc.map {
            if !tgt_coords.contains(coord) {
                return Err(ValidationError::UnknownCoordUpdate {
                    operation: format!("{context}.state_comparison({})", sc.after_phase),
                    coord: coord.clone(),
                });
            }
            validate_poly_expr(
                expr,
                domain,
                src_coords,
                &empty_args,
                allowed_params,
                &format!("{context}.state_comparison `{}.{coord}`", sc.after_phase),
            )?;
        }
    }
    for ph in &source.phases {
        if !h_by_src_phase.contains_key(&ph.name) {
            return Err(ValidationError::MissingStateComparison {
                after_phase: ph.name.clone(),
            });
        }
    }

    check_observation_correspondence(source, target, &h_by_src_phase)?;
    validate_word_translations(
        word_translation,
        source,
        target,
        &h_by_src_phase,
        &source_phase_coords,
        allowed_params,
        context,
    )
}

fn check_observation_correspondence(
    source: &Presentation,
    target: &Presentation,
    h_by_src_phase: &BTreeMap<String, String>,
) -> Result<(), ValidationError> {
    let mut tgt_obs_by_phase: BTreeMap<&str, Vec<&ObservationDecl>> = BTreeMap::new();
    for obs in &target.observations {
        tgt_obs_by_phase
            .entry(obs.phase.as_str())
            .or_default()
            .push(obs);
    }
    let src_obs_arities: BTreeMap<(&str, &str), usize> = source
        .observations
        .iter()
        .map(|o| ((o.phase.as_str(), o.name.as_str()), o.components.len()))
        .collect();
    for (src_ph, tgt_ph) in h_by_src_phase {
        if let Some(list) = tgt_obs_by_phase.get(tgt_ph.as_str()) {
            for t_obs in list {
                let Some(&actual_arity) =
                    src_obs_arities.get(&(src_ph.as_str(), t_obs.name.as_str()))
                else {
                    return Err(ValidationError::MissingObservation {
                        after_phase: src_ph.clone(),
                        before_phase: tgt_ph.clone(),
                        observation: t_obs.name.clone(),
                    });
                };
                if actual_arity != t_obs.components.len() {
                    return Err(ValidationError::ArityMismatch {
                        context: format!(
                            "observation `{}` between `{src_ph}` and `{tgt_ph}`",
                            t_obs.name
                        ),
                        expected: t_obs.components.len(),
                        actual: actual_arity,
                    });
                }
            }
        }
    }
    Ok(())
}

fn validate_word_translations(
    word_translation: &WordTranslation,
    source: &Presentation,
    target: &Presentation,
    h_by_src_phase: &BTreeMap<String, String>,
    source_phase_coords: &BTreeMap<&str, BTreeSet<String>>,
    allowed_params: &BTreeSet<String>,
    context: &str,
) -> Result<(), ValidationError> {
    let src_ops: BTreeMap<&str, &OperationDecl> = source
        .operations
        .iter()
        .map(|op| (op.name.as_str(), op))
        .collect();
    let tgt_ops: BTreeMap<&str, &OperationDecl> = target
        .operations
        .iter()
        .map(|op| (op.name.as_str(), op))
        .collect();

    let mut seen = BTreeSet::new();
    for tw in &word_translation.entries {
        validate_opt_source_ref(
            tw.provenance.as_ref(),
            &format!("{context}.word_translation `{}`", tw.after_operation),
        )?;
        let Some(&src_op) = src_ops.get(tw.after_operation.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "source operation",
                name: tw.after_operation.clone(),
                context: context.to_owned(),
            });
        };
        if !seen.insert(tw.after_operation.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "word_translation",
                name: format!("{context}.{}", tw.after_operation),
            });
        }
        let expected_start = &h_by_src_phase[&src_op.source_phase];
        let expected_end = &h_by_src_phase[&src_op.target_phase];
        let src_coords = &source_phase_coords[src_op.source_phase.as_str()];
        let src_args: BTreeSet<String> = src_op.args.iter().map(|(a, _)| a.clone()).collect();

        if tw.steps.is_empty() {
            if expected_start != expected_end {
                return Err(ValidationError::PhasePathMismatch {
                    after_operation: tw.after_operation.clone(),
                    detail: format!(
                        "empty word requires same target phase, got `{expected_start}` -> `{expected_end}`"
                    ),
                });
            }
        } else {
            let mut cur_phase = expected_start.as_str();
            for (idx, step) in tw.steps.iter().enumerate() {
                require_non_empty(
                    &step.before_operation,
                    &format!("{context}.word_translation"),
                )?;
                let Some(&tgt_op) = tgt_ops.get(step.before_operation.as_str()) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "target operation",
                        name: step.before_operation.clone(),
                        context: format!("{context}.word_translation `{}`", tw.after_operation),
                    });
                };
                if tgt_op.source_phase != cur_phase {
                    return Err(ValidationError::PhasePathMismatch {
                        after_operation: tw.after_operation.clone(),
                        detail: format!(
                            "step {idx} (`{}`) expects phase `{cur_phase}`, got `{}`",
                            tgt_op.name, tgt_op.source_phase
                        ),
                    });
                }
                if step.arg_exprs.len() != tgt_op.args.len() {
                    return Err(ValidationError::ArityMismatch {
                        context: format!(
                            "{context}.word_translation `{}` step {idx} (`{}`)",
                            tw.after_operation, tgt_op.name
                        ),
                        expected: tgt_op.args.len(),
                        actual: step.arg_exprs.len(),
                    });
                }
                for (a_idx, expr) in step.arg_exprs.iter().enumerate() {
                    validate_poly_expr(
                        expr,
                        &source.coeff_domain,
                        src_coords,
                        &src_args,
                        allowed_params,
                        &format!(
                            "{context}.word_translation `{}` step {idx} arg {a_idx}",
                            tw.after_operation
                        ),
                    )?;
                }
                cur_phase = tgt_op.target_phase.as_str();
            }
            if cur_phase != expected_end.as_str() {
                return Err(ValidationError::PhasePathMismatch {
                    after_operation: tw.after_operation.clone(),
                    detail: format!("word ends at phase `{cur_phase}`, expected `{expected_end}`"),
                });
            }
        }
    }
    for op in &source.operations {
        if !seen.contains(&op.name) {
            return Err(ValidationError::MissingWordTranslation {
                after_operation: op.name.clone(),
            });
        }
    }
    Ok(())
}
