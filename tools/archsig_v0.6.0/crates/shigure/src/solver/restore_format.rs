//! 復元後の `ComparisonPair` へのパラメータ代入と表示文字列生成。

use crate::algebra::{ExprBindings, MonomialOrder, Poly, VarOrder};
use crate::ir::presentation::{
    ComparisonPair, CoordValue, ObservationDecl, OperationDecl, PhaseDecl, Presentation,
    StateComparison, StateLaw, TranslatedStep, TranslatedWord, WordTranslation,
};
use crate::ir::result::SilenceReason;
use crate::ir::term::PolyExpr;
use crate::solver::preservation::{map_algebra_silence, substitute_poly_expr};
use num_bigint::BigUint;
use std::collections::BTreeMap;

pub type FormattedRestoredMaps = (
    BTreeMap<String, BTreeMap<String, String>>,
    BTreeMap<String, Vec<String>>,
    BTreeMap<String, BTreeMap<String, String>>,
    BTreeMap<String, Vec<String>>,
);

pub fn substitute_comparison_pair(
    pair: &ComparisonPair,
    param_subst: &BTreeMap<String, PolyExpr>,
) -> ComparisonPair {
    let empty = BTreeMap::new();
    let sub_pres = |pres: &Presentation| -> Presentation {
        let phases = pres
            .phases
            .iter()
            .map(|ph| PhaseDecl {
                name: ph.name.clone(),
                coords: ph.coords.clone(),
                state_laws: ph
                    .state_laws
                    .iter()
                    .map(|l| StateLaw {
                        name: l.name.clone(),
                        kind: l.kind,
                        polynomial: substitute_poly_expr(
                            &l.polynomial,
                            &empty,
                            &empty,
                            param_subst,
                        ),
                        provenance: l.provenance.clone(),
                    })
                    .collect(),
                provenance: ph.provenance.clone(),
            })
            .collect();
        let operations = pres
            .operations
            .iter()
            .map(|op| OperationDecl {
                name: op.name.clone(),
                source_phase: op.source_phase.clone(),
                target_phase: op.target_phase.clone(),
                args: op.args.clone(),
                domain_laws: op
                    .domain_laws
                    .iter()
                    .map(|l| StateLaw {
                        name: l.name.clone(),
                        kind: l.kind,
                        polynomial: substitute_poly_expr(
                            &l.polynomial,
                            &empty,
                            &empty,
                            param_subst,
                        ),
                        provenance: l.provenance.clone(),
                    })
                    .collect(),
                updates: op
                    .updates
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            substitute_poly_expr(v, &empty, &empty, param_subst),
                        )
                    })
                    .collect(),
                provenance: op.provenance.clone(),
            })
            .collect();
        let observations = pres
            .observations
            .iter()
            .map(|obs| ObservationDecl {
                name: obs.name.clone(),
                phase: obs.phase.clone(),
                components: obs
                    .components
                    .iter()
                    .map(|e| substitute_poly_expr(e, &empty, &empty, param_subst))
                    .collect(),
                provenance: obs.provenance.clone(),
            })
            .collect();
        Presentation {
            name: pres.name.clone(),
            coeff_domain: pres.coeff_domain.clone(),
            sorts: pres.sorts.clone(),
            phases,
            operations,
            observations,
            provenance: pres.provenance.clone(),
        }
    };

    ComparisonPair {
        before: sub_pres(&pair.before),
        after: sub_pres(&pair.after),
        state_comparisons: pair
            .state_comparisons
            .iter()
            .map(|sc| StateComparison {
                after_phase: sc.after_phase.clone(),
                before_phase: sc.before_phase.clone(),
                map: sc
                    .map
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            substitute_poly_expr(v, &empty, &empty, param_subst),
                        )
                    })
                    .collect(),
                provenance: sc.provenance.clone(),
            })
            .collect(),
        word_translation: WordTranslation {
            entries: pair
                .word_translation
                .entries
                .iter()
                .map(|tw| TranslatedWord {
                    after_operation: tw.after_operation.clone(),
                    steps: tw
                        .steps
                        .iter()
                        .map(|st| TranslatedStep {
                            before_operation: st.before_operation.clone(),
                            arg_exprs: st
                                .arg_exprs
                                .iter()
                                .map(|e| substitute_poly_expr(e, &empty, &empty, param_subst))
                                .collect(),
                        })
                        .collect(),
                    provenance: tw.provenance.clone(),
                })
                .collect(),
        },
    }
}

pub fn format_restored_pair_q(
    pair: &ComparisonPair,
    free_params: &[String],
) -> Result<FormattedRestoredMaps, SilenceReason> {
    format_restored_pair_with(pair, free_params, |expr, bind, order| {
        Ok(Poly::from_expr_q(expr, bind)
            .map_err(map_algebra_silence)?
            .display(order, MonomialOrder::Grevlex))
    })
}

pub fn format_restored_pair_z(
    pair: &ComparisonPair,
) -> Result<FormattedRestoredMaps, SilenceReason> {
    format_restored_pair_with(pair, &[], |expr, bind, order| {
        Ok(Poly::from_expr_z(expr, bind)
            .map_err(map_algebra_silence)?
            .display(order, MonomialOrder::Grevlex))
    })
}

pub fn format_restored_pair_fp(
    pair: &ComparisonPair,
    modulus: &BigUint,
) -> Result<FormattedRestoredMaps, SilenceReason> {
    format_restored_pair_with(pair, &[], |expr, bind, order| {
        Ok(Poly::from_expr_fp(expr, bind, modulus)
            .map_err(map_algebra_silence)?
            .display(order, MonomialOrder::Grevlex))
    })
}

fn format_restored_pair_with<F>(
    pair: &ComparisonPair,
    free_params: &[String],
    fmt_expr: F,
) -> Result<FormattedRestoredMaps, SilenceReason>
where
    F: Fn(&PolyExpr, &ExprBindings, &VarOrder) -> Result<String, SilenceReason>,
{
    let empty = BTreeMap::new();
    let phase_map: BTreeMap<&str, &PhaseDecl> = pair
        .after
        .phases
        .iter()
        .map(|p| (p.name.as_str(), p))
        .collect();

    let mut operations = BTreeMap::new();
    for op in &pair.after.operations {
        let src = *phase_map.get(op.source_phase.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "after_source_phase_present".to_owned(),
                detail: format!("missing after phase `{}`", op.source_phase),
            }
        })?;
        let (state_vars, obs_map) = symbolic_and_observed(src);
        let arg_vars: Vec<String> = op.args.iter().map(|(a, _)| a.clone()).collect();
        let (order, bind) = ExprBindings::from_slices(&state_vars, &arg_vars, free_params)
            .map_err(map_algebra_silence)?;
        let mut updates = BTreeMap::new();
        for (coord, expr) in &op.updates {
            let sub = substitute_poly_expr(expr, &obs_map, &empty, &empty);
            updates.insert(coord.clone(), fmt_expr(&sub, &bind, &order)?);
        }
        operations.insert(op.name.clone(), updates);
    }

    let mut state_laws = BTreeMap::new();
    for ph in &pair.after.phases {
        let (state_vars, obs_map) = symbolic_and_observed(ph);
        let (order, bind) = ExprBindings::from_slices(&state_vars, &[], free_params)
            .map_err(map_algebra_silence)?;
        let mut laws = Vec::new();
        for l in &ph.state_laws {
            let sub = substitute_poly_expr(&l.polynomial, &obs_map, &empty, &empty);
            laws.push(fmt_expr(&sub, &bind, &order)?);
        }
        state_laws.insert(ph.name.clone(), laws);
    }

    let mut state_comparisons = BTreeMap::new();
    for sc in &pair.state_comparisons {
        let ph = *phase_map.get(sc.after_phase.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "after_phase_present".to_owned(),
                detail: format!("missing after phase `{}`", sc.after_phase),
            }
        })?;
        let (state_vars, obs_map) = symbolic_and_observed(ph);
        let (order, bind) = ExprBindings::from_slices(&state_vars, &[], free_params)
            .map_err(map_algebra_silence)?;
        let mut comp = BTreeMap::new();
        for (coord, expr) in &sc.map {
            let sub = substitute_poly_expr(expr, &obs_map, &empty, &empty);
            comp.insert(coord.clone(), fmt_expr(&sub, &bind, &order)?);
        }
        state_comparisons.insert(sc.after_phase.clone(), comp);
    }

    let op_map: BTreeMap<&str, &OperationDecl> = pair
        .after
        .operations
        .iter()
        .map(|o| (o.name.as_str(), o))
        .collect();
    let mut word_translation = BTreeMap::new();
    for tw in &pair.word_translation.entries {
        let op = *op_map.get(tw.after_operation.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "after_operation_present".to_owned(),
                detail: format!("missing after operation `{}`", tw.after_operation),
            }
        })?;
        let src = *phase_map.get(op.source_phase.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "after_source_phase_present".to_owned(),
                detail: format!("missing after phase `{}`", op.source_phase),
            }
        })?;
        let (state_vars, obs_map) = symbolic_and_observed(src);
        let arg_vars: Vec<String> = op.args.iter().map(|(a, _)| a.clone()).collect();
        let (order, bind) = ExprBindings::from_slices(&state_vars, &arg_vars, free_params)
            .map_err(map_algebra_silence)?;
        let mut steps = Vec::new();
        for st in &tw.steps {
            let mut arg_strs = Vec::new();
            for ae in &st.arg_exprs {
                let sub = substitute_poly_expr(ae, &obs_map, &empty, &empty);
                arg_strs.push(fmt_expr(&sub, &bind, &order)?);
            }
            if arg_strs.is_empty() {
                steps.push(st.before_operation.clone());
            } else {
                steps.push(format!("{}({})", st.before_operation, arg_strs.join(", ")));
            }
        }
        word_translation.insert(tw.after_operation.clone(), steps);
    }

    Ok((operations, state_laws, state_comparisons, word_translation))
}

fn symbolic_and_observed(phase: &PhaseDecl) -> (Vec<String>, BTreeMap<String, PolyExpr>) {
    let mut symbolic = Vec::new();
    let mut observed = BTreeMap::new();
    for c in &phase.coords {
        match &c.value {
            CoordValue::Symbolic => symbolic.push(c.name.clone()),
            CoordValue::Observed(lit) => {
                observed.insert(c.name.clone(), PolyExpr::Const(lit.clone()));
            }
            CoordValue::Missing => {}
        }
    }
    (symbolic, observed)
}
