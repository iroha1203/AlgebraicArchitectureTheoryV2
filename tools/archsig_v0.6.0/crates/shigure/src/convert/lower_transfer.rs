//! `CheckedInputs` から `CheckedTransferTask` への厳密な lowering。

use super::lower::{
    lower_change_spec, lower_comparison_pair, lower_eval_condition, lower_law_kind,
    lower_presentation,
};
use super::lower_expr::{conv_err, law_source_ref, lower_poly_expr};
use super::lower_morphism::{
    collect_eval_origins, ensure_snapshot_exists, lower_morphism_body, resolve_decl,
    select_named_decl,
};
use crate::ir::presentation::StateLaw;
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::transfer::{
    CheckedTransferTask, OldWordLiftSpec, TransferSpec, TransferStepSpec, WordCheckSpec,
    WordStepExpr,
};
use crate::ir::validate::ValidationError;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{ShigureTransferStepSource, ShigureWordStep};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn convert_transfer_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedTransferTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let (_, decl) = select_named_decl(&shigure.transfers, task_name, "shigure transfer")?;
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let spec_decl = resolve_decl(
        &shigure.change_specs,
        &decl.change_spec,
        "shigure change_spec",
        &decl.name,
    )?;
    let change_spec = lower_change_spec(spec_decl);
    let param_names: BTreeSet<String> = change_spec
        .parameters
        .iter()
        .map(|p| p.name.clone())
        .collect();
    let empty = BTreeSet::new();

    let tr_ref = law_source_ref(&decl.name);
    let mut origins: BTreeSet<SourceRef> = BTreeSet::from([tr_ref.clone()]);
    for o in &change_spec.provenance.origins {
        origins.insert(o.clone());
    }

    let eval_condition = decl
        .eval_condition
        .as_ref()
        .map(|ec_name| {
            let ec = resolve_decl(
                &shigure.eval_conditions,
                ec_name,
                "eval_condition",
                &decl.name,
            )?;
            lower_eval_condition(ec, &change_spec.coeff_domain, &param_names)
        })
        .transpose()?;
    collect_eval_origins(eval_condition.as_ref(), &mut origins);

    let mut steps = Vec::with_capacity(decl.steps.len());
    for (idx, st) in decl.steps.iter().enumerate() {
        let comparison = match &st.source {
            ShigureTransferStepSource::Comparison(cmp_name) => {
                let cmp = resolve_decl(
                    &shigure.comparisons,
                    cmp_name,
                    "shigure comparison",
                    &decl.name,
                )?;
                let b_decl = resolve_decl(
                    &shigure.presentations,
                    &cmp.before,
                    "presentation",
                    &cmp.name,
                )?;
                let a_decl = resolve_decl(
                    &shigure.presentations,
                    &cmp.after,
                    "presentation",
                    &cmp.name,
                )?;
                let before =
                    lower_presentation(b_decl, archmap, snapshot_id, &empty, Some(&param_names))?;
                let after = lower_presentation(a_decl, archmap, snapshot_id, &param_names, None)?;
                lower_comparison_pair(cmp, before, after, &param_names)?
            }
            ShigureTransferStepSource::Inline {
                before: b_name,
                after: a_name,
                morphism,
            } => {
                let b_decl =
                    resolve_decl(&shigure.presentations, b_name, "presentation", &decl.name)?;
                let a_decl =
                    resolve_decl(&shigure.presentations, a_name, "presentation", &decl.name)?;
                let before = if idx == 0 {
                    lower_presentation(b_decl, archmap, snapshot_id, &empty, Some(&param_names))?
                } else {
                    lower_presentation(b_decl, archmap, snapshot_id, &param_names, None)?
                };
                let after = lower_presentation(a_decl, archmap, snapshot_id, &param_names, None)?;
                let morph = lower_morphism_body(
                    morphism,
                    &shigure.comparisons,
                    &after,
                    &before,
                    &param_names,
                    None,
                    &tr_ref,
                    &format!("{}.step.{}", decl.name, st.name),
                )?;
                morph.to_comparison_pair(&after, &before)
            }
        };
        for o in comparison
            .before
            .provenance
            .origins
            .iter()
            .chain(&comparison.after.provenance.origins)
        {
            origins.insert(o.clone());
        }

        let src_ph = comparison.before.phase(&st.source_phase).ok_or_else(|| {
            ValidationError::UnknownRef {
                kind: "before phase",
                name: st.source_phase.clone(),
                context: format!("{}.step.{}", decl.name, st.name),
            }
        })?;
        let src_coords: BTreeSet<String> = src_ph.coords.iter().map(|c| c.name.clone()).collect();

        let mut domain_laws = Vec::with_capacity(st.domain_laws.len());
        for dl in &st.domain_laws {
            let ctx = format!("{}.step.{}.domain_law.{}", decl.name, st.name, dl.name);
            let polynomial = lower_poly_expr(
                &dl.expr,
                &change_spec.coeff_domain,
                &src_coords,
                &empty,
                &param_names,
                None,
                &ctx,
            )?;
            domain_laws.push(StateLaw {
                name: dl.name.clone(),
                kind: lower_law_kind(dl.kind),
                polynomial,
                provenance: Some(tr_ref.clone()),
            });
        }

        let mut lift_map = BTreeMap::new();
        for (coord, expr) in &st.lift_map {
            let ctx = format!("{}.step.{}.lift.{coord}", decl.name, st.name);
            let lowered = lower_poly_expr(
                expr,
                &change_spec.coeff_domain,
                &src_coords,
                &empty,
                &param_names,
                None,
                &ctx,
            )?;
            lift_map.insert(coord.clone(), lowered);
        }

        steps.push(TransferStepSpec {
            name: st.name.clone(),
            comparison,
            source_phase: st.source_phase.clone(),
            domain_laws,
            target_phase: st.target_phase.clone(),
            lift_map,
            provenance: Some(tr_ref.clone()),
        });
    }

    let lower_word_step_list = |raw_args: &[String],
                                raw_steps: &[ShigureWordStep],
                                ctx_prefix: &str|
     -> Result<Vec<WordStepExpr>, ValidationError> {
        let arg_set: BTreeSet<String> = raw_args.iter().cloned().collect();
        let mut out = Vec::with_capacity(raw_steps.len());
        for (s_idx, st) in raw_steps.iter().enumerate() {
            let mut arg_exprs = Vec::with_capacity(st.arg_exprs.len());
            for (a_idx, expr) in st.arg_exprs.iter().enumerate() {
                let ctx = format!("{ctx_prefix}.step{s_idx}.arg{a_idx}");
                arg_exprs.push(lower_poly_expr(
                    expr,
                    &change_spec.coeff_domain,
                    &empty,
                    &arg_set,
                    &param_names,
                    None,
                    &ctx,
                )?);
            }
            out.push(WordStepExpr {
                operation: st.operation.clone(),
                arg_exprs,
            });
        }
        Ok(out)
    };

    let mut word_checks = Vec::with_capacity(decl.word_checks.len());
    for wc in &decl.word_checks {
        let steps_ir = lower_word_step_list(
            &wc.args,
            &wc.steps,
            &format!("{}.word_check.{}", decl.name, wc.name),
        )?;
        word_checks.push(WordCheckSpec {
            name: wc.name.clone(),
            args: wc.args.clone(),
            steps: steps_ir,
            provenance: Some(tr_ref.clone()),
        });
    }

    let mut old_word_lifts = Vec::with_capacity(decl.old_word_lifts.len());
    for ol in &decl.old_word_lifts {
        let target_steps = lower_word_step_list(
            &ol.args,
            &ol.target_steps,
            &format!("{}.old_word_lift.{}", decl.name, ol.name),
        )?;
        old_word_lifts.push(OldWordLiftSpec {
            name: ol.name.clone(),
            args: ol.args.clone(),
            target_steps,
            max_length: ol.max_length,
            provenance: Some(tr_ref.clone()),
        });
    }

    CheckedTransferTask::validate(TransferSpec {
        name: decl.name.clone(),
        steps,
        word_checks,
        old_word_lifts,
        change_spec,
        eval_condition,
        require_full_domain: decl.require_full_domain,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: vec![],
        },
    })
}
