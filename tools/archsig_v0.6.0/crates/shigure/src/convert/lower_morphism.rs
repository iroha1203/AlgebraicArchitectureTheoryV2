//! 図式・経路・移送変換層の共通宣言選択・射 lowering ヘルパ。

use super::lower_expr::{conv_err, law_source_ref, lower_poly_expr};
use crate::ir::change::EvalCondition;
use crate::ir::morphism::{MorphismDirection, StateMorphism};
use crate::ir::presentation::{
    Presentation, StateComparison, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::provenance::SourceRef;
use crate::ir::term::PolyExpr;
use crate::ir::validate::ValidationError;
use archsig_input::archmap::CheckedArchMap;
use archsig_input::law::shigure::{
    ShigureComparison, ShigureDirection, ShigureMorphismBody, ShigureStateComparison,
    ShigureTranslatedWord,
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn ensure_snapshot_exists(
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    context: &str,
) -> Result<(), ValidationError> {
    if let Some(sid) = snapshot_id
        && !archmap.snapshots().iter().any(|s| s.id == sid)
    {
        return Err(ValidationError::UnknownRef {
            kind: "snapshot",
            name: sid.to_owned(),
            context: context.to_owned(),
        });
    }
    Ok(())
}

pub(super) fn select_named_decl<'a, T>(
    map: &'a BTreeMap<String, T>,
    name: Option<&str>,
    kind: &'static str,
) -> Result<(&'a str, &'a T), ValidationError> {
    if let Some(target) = name {
        if let Some((k, v)) = map.get_key_value(target) {
            return Ok((k.as_str(), v));
        }
        let suffix = format!(".{target}");
        let matches: Vec<(&str, &T)> = map
            .iter()
            .filter(|(k, _)| k.ends_with(&suffix))
            .map(|(k, v)| (k.as_str(), v))
            .collect();
        return match matches.as_slice() {
            [only] => Ok(*only),
            [] => Err(ValidationError::UnknownRef {
                kind,
                name: target.to_owned(),
                context: "ShigureConverter".to_owned(),
            }),
            _ => Err(conv_err(format!(
                "ambiguous short {kind} name `{target}`; specify full `Reading.Name` name"
            ))),
        };
    }

    match map.len() {
        0 => Err(conv_err(format!(
            "no `{kind}` declarations found in CheckedLaw input"
        ))),
        1 => {
            let (k, v) = map.iter().next().expect("len == 1");
            Ok((k.as_str(), v))
        }
        _ => Err(conv_err(format!(
            "multiple `{kind}` declarations exist ({}); specify a name explicitly",
            map.keys().cloned().collect::<Vec<_>>().join(", ")
        ))),
    }
}

pub(super) fn resolve_decl<'a, T>(
    map: &'a BTreeMap<String, T>,
    full_name: &str,
    kind: &'static str,
    context: &str,
) -> Result<&'a T, ValidationError> {
    map.get(full_name)
        .ok_or_else(|| ValidationError::UnknownRef {
            kind,
            name: full_name.to_owned(),
            context: context.to_owned(),
        })
}

pub(super) fn lower_direction(d: ShigureDirection) -> MorphismDirection {
    match d {
        ShigureDirection::StateMap => MorphismDirection::StateMap,
        ShigureDirection::TimeOrder => MorphismDirection::TimeOrder,
    }
}

pub(super) fn identity_state_morphism_between(
    src: &Presentation,
    tgt: &Presentation,
    provenance: Option<SourceRef>,
) -> Result<StateMorphism, ValidationError> {
    let mut state_comparisons = Vec::with_capacity(src.phases.len());
    for ph in &src.phases {
        let tgt_ph = tgt
            .phase(&ph.name)
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "target phase",
                name: ph.name.clone(),
                context: format!("identity morphism `{} -> {}`", src.name, tgt.name),
            })?;
        let map = tgt_ph
            .coords
            .iter()
            .map(|c| (c.name.clone(), PolyExpr::StateVar(c.name.clone())))
            .collect();
        state_comparisons.push(StateComparison {
            after_phase: ph.name.clone(),
            before_phase: ph.name.clone(),
            map,
            provenance: provenance.clone().or_else(|| ph.provenance.clone()),
        });
    }
    let entries = src
        .operations
        .iter()
        .map(|op| TranslatedWord {
            after_operation: op.name.clone(),
            steps: vec![TranslatedStep {
                before_operation: op.name.clone(),
                arg_exprs: op
                    .args
                    .iter()
                    .map(|(a, _)| PolyExpr::ArgVar(a.clone()))
                    .collect(),
            }],
            provenance: provenance.clone().or_else(|| op.provenance.clone()),
        })
        .collect();
    Ok(StateMorphism {
        source: src.name.clone(),
        target: tgt.name.clone(),
        state_comparisons,
        word_translation: WordTranslation { entries },
        provenance,
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_morphism_body(
    body: &ShigureMorphismBody,
    comparisons: &BTreeMap<String, ShigureComparison>,
    morph_src: &Presentation,
    morph_tgt: &Presentation,
    allowed_params: &BTreeSet<String>,
    forbidden_params: Option<&BTreeSet<String>>,
    fallback_ref: &SourceRef,
    context: &str,
) -> Result<StateMorphism, ValidationError> {
    match body {
        ShigureMorphismBody::Comparison(cmp_name) => {
            let cmp = resolve_decl(comparisons, cmp_name, "shigure comparison", context)?;
            if cmp.after != morph_src.name || cmp.before != morph_tgt.name {
                return Err(conv_err(format!(
                    "{context}: comparison `{}` maps `{} -> {}`, expected `{} -> {}`",
                    cmp.name, cmp.after, cmp.before, morph_src.name, morph_tgt.name
                )));
            }
            let cmp_ref = law_source_ref(&cmp.name);
            let (scs, wt) = lower_scs_and_wt(
                &cmp.state_comparisons,
                &cmp.word_translation,
                morph_src,
                allowed_params,
                forbidden_params,
                &cmp_ref,
                &cmp.name,
            )?;
            Ok(StateMorphism {
                source: morph_src.name.clone(),
                target: morph_tgt.name.clone(),
                state_comparisons: scs,
                word_translation: wt,
                provenance: Some(cmp_ref),
            })
        }
        ShigureMorphismBody::Identity => {
            if morph_src.coeff_domain != morph_tgt.coeff_domain {
                return Err(ValidationError::DomainMismatch {
                    expected: morph_tgt.coeff_domain.clone(),
                    actual: morph_src.coeff_domain.clone(),
                    context: context.to_owned(),
                });
            }
            identity_state_morphism_between(morph_src, morph_tgt, Some(fallback_ref.clone()))
        }
        ShigureMorphismBody::Inline {
            state_comparisons,
            word_translation,
        } => {
            let (scs, wt) = lower_scs_and_wt(
                state_comparisons,
                word_translation,
                morph_src,
                allowed_params,
                forbidden_params,
                fallback_ref,
                context,
            )?;
            Ok(StateMorphism {
                source: morph_src.name.clone(),
                target: morph_tgt.name.clone(),
                state_comparisons: scs,
                word_translation: wt,
                provenance: Some(fallback_ref.clone()),
            })
        }
    }
}

fn lower_scs_and_wt(
    raw_scs: &[ShigureStateComparison],
    raw_wt: &[ShigureTranslatedWord],
    morph_src: &Presentation,
    allowed_params: &BTreeSet<String>,
    forbidden_params: Option<&BTreeSet<String>>,
    prov_ref: &SourceRef,
    context: &str,
) -> Result<(Vec<StateComparison>, WordTranslation), ValidationError> {
    let domain = &morph_src.coeff_domain;
    let empty_args = BTreeSet::new();
    let mut state_comparisons = Vec::with_capacity(raw_scs.len());
    for sc in raw_scs {
        let src_ph =
            morph_src
                .phase(&sc.after_phase)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "source phase",
                    name: sc.after_phase.clone(),
                    context: context.to_owned(),
                })?;
        let state_vars: BTreeSet<String> = src_ph.coords.iter().map(|c| c.name.clone()).collect();
        let mut map = BTreeMap::new();
        for (coord, expr) in &sc.map {
            let ctx = format!("{context}.state_map.{}.{coord}", sc.after_phase);
            let lowered = lower_poly_expr(
                expr,
                domain,
                &state_vars,
                &empty_args,
                allowed_params,
                forbidden_params,
                &ctx,
            )?;
            map.insert(coord.clone(), lowered);
        }
        state_comparisons.push(StateComparison {
            after_phase: sc.after_phase.clone(),
            before_phase: sc.before_phase.clone(),
            map,
            provenance: Some(prov_ref.clone()),
        });
    }

    let mut entries = Vec::with_capacity(raw_wt.len());
    for tw in raw_wt {
        let src_op = morph_src.operation(&tw.after_operation).ok_or_else(|| {
            ValidationError::UnknownRef {
                kind: "source operation",
                name: tw.after_operation.clone(),
                context: context.to_owned(),
            }
        })?;
        let src_ph =
            morph_src
                .phase(&src_op.source_phase)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "source phase",
                    name: src_op.source_phase.clone(),
                    context: context.to_owned(),
                })?;
        let state_vars: BTreeSet<String> = src_ph.coords.iter().map(|c| c.name.clone()).collect();
        let arg_vars: BTreeSet<String> = src_op.args.iter().map(|(a, _)| a.clone()).collect();
        let mut steps = Vec::with_capacity(tw.steps.len());
        for st in &tw.steps {
            let mut arg_exprs = Vec::with_capacity(st.arg_exprs.len());
            for (idx, expr) in st.arg_exprs.iter().enumerate() {
                let ctx = format!(
                    "{context}.translate.{}.{}[{idx}]",
                    tw.after_operation, st.before_operation
                );
                arg_exprs.push(lower_poly_expr(
                    expr,
                    domain,
                    &state_vars,
                    &arg_vars,
                    allowed_params,
                    forbidden_params,
                    &ctx,
                )?);
            }
            steps.push(TranslatedStep {
                before_operation: st.before_operation.clone(),
                arg_exprs,
            });
        }
        entries.push(TranslatedWord {
            after_operation: tw.after_operation.clone(),
            steps,
            provenance: Some(prov_ref.clone()),
        });
    }
    Ok((state_comparisons, WordTranslation { entries }))
}

pub(super) fn collect_eval_origins(ec: Option<&EvalCondition>, origins: &mut BTreeSet<SourceRef>) {
    if let Some(cond) = ec {
        for o in &cond.provenance.origins {
            origins.insert(o.clone());
        }
    }
}
