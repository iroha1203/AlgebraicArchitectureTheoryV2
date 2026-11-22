//! 合法状態の移送・共通操作語保存・移送合成 IR（`TransferSpec` / `CheckedTransferTask`、G-140 G1–G3・P5.3）。

use crate::ir::change::{ChangeSpec, EvalCondition};
use crate::ir::diagram::validate_scoped_change_targets;
use crate::ir::morphism::{StateMorphism, validate_state_morphism_checked_endpoints};
use crate::ir::presentation::{ComparisonPair, Presentation, StateLaw};
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::PolyExpr;
use crate::ir::validate::{
    CheckedChangeSpec, CheckedEvalCondition, ValidationError, collect_eval_unobserved,
    collect_morphism_unobserved, collect_presentation_unobserved, require_non_empty,
    validate_opt_source_ref, validate_poly_expr, validate_presentation_ref_checked_params,
    validate_provenance,
};
use crate::ir::validate_change::{
    collect_and_check_param_names, validate_change_spec_struct_only,
    validate_eval_condition_checked_params,
};
use std::collections::{BTreeMap, BTreeSet};

/// 操作語内の 1 ステップ（操作名と実引数式列）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordStepExpr {
    pub operation: String,
    pub arg_exprs: Vec<PolyExpr>,
}

/// 移送後の共通定義域 $D_w$ 上で保存を検算する新側許可語 $w$（G-140 G2）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordCheckSpec {
    pub name: String,
    /// この語検査で全称束縛する引数変数名（具体定数のみなら空）。
    pub args: Vec<String>,
    pub steps: Vec<WordStepExpr>,
    pub provenance: Option<SourceRef>,
}

/// 旧側指定語 $v$ を移送後にも実行できる新語 $w$（$\tau w = v$ かつ開始域経由）の独立探索要求（G-140 G2）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OldWordLiftSpec {
    pub name: String,
    /// 旧側操作語が参照する引数変数名（具体定数のみなら空）。
    pub args: Vec<String>,
    pub target_steps: Vec<WordStepExpr>,
    /// 探索する新側操作語長の有限上界。`None` の場合は無界探索として計算時に沈黙する。
    pub max_length: Option<usize>,
    pub provenance: Option<SourceRef>,
}

/// 状態移送の 1 段（意味保存射 $h_{j,j+1}: X_{j+1} \to X_j$・開始域 $\iota_j: D_j \hookrightarrow X_j$・移送規則 $m_{j,j+1}: D_j \to X_{j+1}$）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransferStepSpec {
    pub name: String,
    pub comparison: ComparisonPair,
    pub source_phase: String,
    pub domain_laws: Vec<StateLaw>,
    pub target_phase: String,
    pub lift_map: BTreeMap<String, PolyExpr>,
    pub provenance: Option<SourceRef>,
}

/// 合法状態の移送・共通操作語保存・合成タスク仕様（1 段以上）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransferSpec {
    pub name: String,
    pub steps: Vec<TransferStepSpec>,
    pub word_checks: Vec<WordCheckSpec>,
    pub old_word_lifts: Vec<OldWordLiftSpec>,
    pub change_spec: ChangeSpec,
    pub eval_condition: Option<EvalCondition>,
    /// `true` のとき、合成定義域 $D_{0k}$ が開始域 $D_0$ と同型（$D_{0k} \cong D_0$）であることを要求する（G3）。
    pub require_full_domain: bool,
    pub provenance: Provenance,
}

/// 検証済みの状態移送タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedTransferTask {
    spec: TransferSpec,
    checked_change_spec: CheckedChangeSpec,
    checked_eval_condition: Option<CheckedEvalCondition>,
}

impl CheckedTransferTask {
    pub fn validate(spec: TransferSpec) -> Result<Self, ValidationError> {
        require_non_empty(&spec.name, "transfer.name")?;
        validate_provenance(&spec.provenance, &format!("transfer `{}`", spec.name))?;
        if spec.steps.is_empty() {
            return Err(ValidationError::ConversionError {
                detail: format!("transfer `{}` requires at least one step", spec.name),
            });
        }

        let param_names = collect_and_check_param_names(&spec.change_spec)?;
        let checked_change_spec = validate_change_spec_struct_only(spec.change_spec.clone())?;
        let domain = checked_change_spec.inner().coeff_domain.clone();
        let empty = BTreeSet::new();

        let mut step_names = BTreeSet::new();
        let mut step_morphs = Vec::with_capacity(spec.steps.len());
        for (idx, step) in spec.steps.iter().enumerate() {
            require_non_empty(&step.name, &format!("transfer.step[{idx}].name"))?;
            validate_opt_source_ref(
                step.provenance.as_ref(),
                &format!("transfer step `{}`", step.name),
            )?;
            if !step_names.insert(step.name.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "transfer step",
                    name: step.name.clone(),
                });
            }
            if step.comparison.before.coeff_domain != domain {
                return Err(ValidationError::DomainMismatch {
                    expected: domain.clone(),
                    actual: step.comparison.before.coeff_domain.clone(),
                    context: format!("transfer step `{}`", step.name),
                });
            }

            validate_presentation_ref_checked_params(
                &step.comparison.before,
                if idx == 0 { &empty } else { &param_names },
            )?;
            validate_presentation_ref_checked_params(&step.comparison.after, &param_names)?;
            let morph = StateMorphism::from_comparison_pair(&step.comparison);
            validate_state_morphism_checked_endpoints(
                &morph,
                &step.comparison.after,
                &step.comparison.before,
                &param_names,
                &format!("transfer step `{}`", step.name),
            )?;

            let src_ph = step
                .comparison
                .before
                .phase(&step.source_phase)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "before phase",
                    name: step.source_phase.clone(),
                    context: format!("transfer step `{}` source_phase", step.name),
                })?;
            let tgt_ph = step
                .comparison
                .after
                .phase(&step.target_phase)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "after phase",
                    name: step.target_phase.clone(),
                    context: format!("transfer step `{}` target_phase", step.name),
                })?;

            // h: target_phase -> source_phase の整合確認（h ∘ m = ι_D の型一致）
            let sc = step
                .comparison
                .state_comparisons
                .iter()
                .find(|s| s.after_phase == step.target_phase)
                .ok_or_else(|| ValidationError::MissingStateComparison {
                    after_phase: step.target_phase.clone(),
                })?;
            if sc.before_phase != step.source_phase {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "transfer step `{}`: comparison maps target phase `{}` to `{}`, expected source phase `{}`",
                        step.name, step.target_phase, sc.before_phase, step.source_phase
                    ),
                });
            }

            let src_coords: BTreeSet<String> =
                src_ph.coords.iter().map(|c| c.name.clone()).collect();
            let tgt_coords: BTreeSet<String> =
                tgt_ph.coords.iter().map(|c| c.name.clone()).collect();

            let mut law_names = BTreeSet::new();
            for law in &step.domain_laws {
                require_non_empty(
                    &law.name,
                    &format!("transfer step `{}` domain_law", step.name),
                )?;
                validate_opt_source_ref(
                    law.provenance.as_ref(),
                    &format!("transfer step `{}` domain_law `{}`", step.name, law.name),
                )?;
                if !law_names.insert(law.name.clone()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "domain_law",
                        name: format!("{}.{}", step.name, law.name),
                    });
                }
                validate_poly_expr(
                    &law.polynomial,
                    &domain,
                    &src_coords,
                    &empty,
                    &param_names,
                    &format!("transfer step `{}` domain_law `{}`", step.name, law.name),
                )?;
            }

            for tc in &tgt_coords {
                if !step.lift_map.contains_key(tc) {
                    return Err(ValidationError::MissingCoordUpdate {
                        operation: format!("transfer step `{}` lift", step.name),
                        coord: tc.clone(),
                    });
                }
            }
            for (coord, expr) in &step.lift_map {
                if !tgt_coords.contains(coord) {
                    return Err(ValidationError::UnknownCoordUpdate {
                        operation: format!("transfer step `{}` lift", step.name),
                        coord: coord.clone(),
                    });
                }
                validate_poly_expr(
                    expr,
                    &domain,
                    &src_coords,
                    &empty,
                    &param_names,
                    &format!("transfer step `{}` lift `{coord}`", step.name),
                )?;
            }

            if idx > 0 {
                let prev = &spec.steps[idx - 1];
                if step.comparison.before.name != prev.comparison.after.name
                    || step.comparison.before != prev.comparison.after
                {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "transfer chain discontinuity at step `{}`: before presentation `{}` does not match previous step after presentation `{}`",
                            step.name, step.comparison.before.name, prev.comparison.after.name
                        ),
                    });
                }
                if step.source_phase != prev.target_phase {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "transfer chain phase discontinuity at step `{}`: source_phase `{}` != previous target_phase `{}`",
                            step.name, step.source_phase, prev.target_phase
                        ),
                    });
                }
            }
            step_morphs.push(morph);
        }

        let mut pres_map: BTreeMap<&str, Vec<(&Presentation, bool)>> = BTreeMap::new();
        for (idx, step) in spec.steps.iter().enumerate() {
            pres_map
                .entry(step.comparison.before.name.as_str())
                .or_default()
                .push((&step.comparison.before, idx == 0));
            pres_map
                .entry(step.comparison.after.name.as_str())
                .or_default()
                .push((&step.comparison.after, false));
        }
        let morph_refs: Vec<(&StateMorphism, bool)> =
            step_morphs.iter().map(|m| (m, false)).collect();
        validate_scoped_change_targets(&spec.change_spec, &pres_map, &morph_refs, "transfer")?;

        let first_step = &spec.steps[0];
        let last_step = spec.steps.last().expect("non-empty steps");

        let mut wc_names = BTreeSet::new();
        for wc in &spec.word_checks {
            require_non_empty(&wc.name, "transfer.word_check.name")?;
            validate_opt_source_ref(wc.provenance.as_ref(), &format!("word_check `{}`", wc.name))?;
            if !wc_names.insert(wc.name.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "word_check",
                    name: wc.name.clone(),
                });
            }
            validate_word_steps(
                &wc.args,
                &wc.steps,
                &last_step.comparison.after,
                &last_step.target_phase,
                &domain,
                &param_names,
                &format!("word_check `{}`", wc.name),
            )?;
        }

        let mut ol_names = BTreeSet::new();
        for ol in &spec.old_word_lifts {
            require_non_empty(&ol.name, "transfer.old_word_lift.name")?;
            validate_opt_source_ref(
                ol.provenance.as_ref(),
                &format!("old_word_lift `{}`", ol.name),
            )?;
            if !ol_names.insert(ol.name.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "old_word_lift",
                    name: ol.name.clone(),
                });
            }
            validate_word_steps(
                &ol.args,
                &ol.target_steps,
                &first_step.comparison.before,
                &first_step.source_phase,
                &domain,
                &param_names,
                &format!("old_word_lift `{}`", ol.name),
            )?;
        }

        let checked_eval_condition = spec
            .eval_condition
            .clone()
            .map(|c| validate_eval_condition_checked_params(c, &domain, &param_names))
            .transpose()?;

        Ok(Self {
            spec,
            checked_change_spec,
            checked_eval_condition,
        })
    }

    pub fn spec(&self) -> &TransferSpec {
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

    /// 移送タスク全体に含まれる未観測 slot を収集する。
    pub fn unobserved_slots(&self) -> Vec<String> {
        let mut slots = BTreeSet::new();
        for step in &self.spec.steps {
            collect_presentation_unobserved(&step.comparison.before, &mut slots);
            collect_presentation_unobserved(&step.comparison.after, &mut slots);
            collect_morphism_unobserved(
                &step.comparison.state_comparisons,
                &step.comparison.word_translation,
                &mut slots,
            );
            for l in &step.domain_laws {
                l.polynomial.collect_unobserved(&mut slots);
            }
            for e in step.lift_map.values() {
                e.collect_unobserved(&mut slots);
            }
        }
        for wc in &self.spec.word_checks {
            for st in &wc.steps {
                for e in &st.arg_exprs {
                    e.collect_unobserved(&mut slots);
                }
            }
        }
        for ol in &self.spec.old_word_lifts {
            for st in &ol.target_steps {
                for e in &st.arg_exprs {
                    e.collect_unobserved(&mut slots);
                }
            }
        }
        if let Some(ec) = self.eval_condition() {
            collect_eval_unobserved(ec, &mut slots);
        }
        slots.into_iter().collect()
    }
}

fn validate_word_steps(
    args: &[String],
    steps: &[WordStepExpr],
    pres: &Presentation,
    start_phase: &str,
    domain: &crate::ir::term::CoeffDomain,
    allowed_params: &BTreeSet<String>,
    context: &str,
) -> Result<(), ValidationError> {
    let mut allowed_args = BTreeSet::new();
    for a in args {
        require_non_empty(a, &format!("{context} arg"))?;
        if !allowed_args.insert(a.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "word argument",
                name: format!("{context}.{a}"),
            });
        }
    }
    let empty = BTreeSet::new();
    let mut cur_phase = start_phase;
    for (idx, st) in steps.iter().enumerate() {
        let op = pres
            .operation(&st.operation)
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "operation",
                name: st.operation.clone(),
                context: format!("{context} step {idx}"),
            })?;
        if op.source_phase != cur_phase {
            return Err(ValidationError::PhasePathMismatch {
                after_operation: st.operation.clone(),
                detail: format!(
                    "{context} step {idx}: operation `{}` expects source phase `{cur_phase}`, got `{}`",
                    op.name, op.source_phase
                ),
            });
        }
        if st.arg_exprs.len() != op.args.len() {
            return Err(ValidationError::ArityMismatch {
                context: format!("{context} step {idx} (`{}`)", op.name),
                expected: op.args.len(),
                actual: st.arg_exprs.len(),
            });
        }
        for (a_idx, expr) in st.arg_exprs.iter().enumerate() {
            validate_poly_expr(
                expr,
                domain,
                &empty,
                &allowed_args,
                allowed_params,
                &format!("{context} step {idx} arg {a_idx}"),
            )?;
        }
        cur_phase = op.target_phase.as_str();
    }
    Ok(())
}
