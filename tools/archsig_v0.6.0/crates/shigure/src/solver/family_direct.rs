//! 複数解釈族の直接型良否 $E_{\mathrm{dir}}$（等式・可逆条件・保存義務・生操作列評価 P7）の評価器。

use crate::algebra::{MonomialOrder, VarOrder};
use crate::ir::change::{EditableTarget, PointDomain};
use crate::ir::family::{
    CheckedFamilySpec, GoodnessSpec, PreservationGoodnessSource, RawSequenceCheck, RealizationSpace,
};
use crate::ir::presentation::{ComparisonPair, CoordValue, PhaseDecl, Presentation};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, EmptyWitness, SilenceReason};
use crate::ir::result_phase3::PairEvaluationWitness;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::context::{collect_presentation_params, display_polys};
use crate::solver::family_eval::{EnumCandidate, EnumRealization, ScalarVal, eval_expr_at};
use crate::solver::family_existential::evaluate_existential_point;
use crate::solver::preservation::{
    build_preservation_obligations, compute_preservation_locus_q, extract_closed_residuals_fp,
    extract_closed_residuals_z, substitute_poly_expr,
};
use crate::solver::restore_format::substitute_comparison_pair;
use std::collections::{BTreeMap, BTreeSet};

/// 単一組 $(u, c)$ 上で `GoodnessSpec`（`Direct` / `Existential`、raw 列評価含む）を実行する。
pub(crate) fn evaluate_goodness_at_point(
    family: &CheckedFamilySpec,
    realization: &EnumRealization,
    candidate: &EnumCandidate,
    point_domain: &PointDomain,
) -> Result<PairEvaluationWitness, SilenceReason> {
    let domain = family.coeff_domain();
    let u_names = family.u_vars();
    let c_names = family.c_vars();
    let w_names = family.witness_vars();

    let mut uc_subst: BTreeMap<String, PolyExpr> = BTreeMap::new();
    for (name, sv) in u_names.iter().zip(&realization.values) {
        uc_subst.insert(name.clone(), sv.to_expr());
    }
    for (name, sv) in c_names.iter().zip(&candidate.values) {
        uc_subst.insert(name.clone(), sv.to_expr());
    }

    let empty = BTreeMap::new();
    match &family.inner().goodness {
        GoodnessSpec::Direct {
            equations,
            invertibles,
            preservation,
            raw_sequence,
        } => {
            let mut passed = true;
            let mut legal_execution_exists = None;
            let mut residuals = Vec::new();
            let zero_vars =
                VarOrder::new(vec![]).map_err(crate::solver::preservation::map_algebra_silence)?;

            for eq in equations {
                let sub = substitute_poly_expr(&eq.expr, &empty, &empty, &uc_subst);
                let val = eval_expr_at(&sub, &zero_vars, &[], domain)?;
                if !val.is_zero() {
                    passed = false;
                    residuals.push(format!("{} = {}", eq.name, val.to_display()));
                }
            }
            for inv in invertibles {
                let sub = substitute_poly_expr(&inv.expr, &empty, &empty, &uc_subst);
                let val = eval_expr_at(&sub, &zero_vars, &[], domain)?;
                let ok = match point_domain {
                    PointDomain::IntegerPoints => val.is_unit(),
                    _ => !val.is_zero(),
                };
                if !ok {
                    passed = false;
                    residuals.push(format!(
                        "not_invertible({} = {})",
                        inv.name,
                        val.to_display()
                    ));
                }
            }
            if let Some(raw_seq) = raw_sequence {
                let pres = realization.presentation.as_ref().ok_or_else(|| {
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "realization_presentation_required".to_owned(),
                        detail: "raw_sequence evaluation requires concrete presentation on member"
                            .to_owned(),
                    }
                })?;
                let (raw_ok, raw_legal, raw_res) =
                    evaluate_raw_sequence_on_presentation(raw_seq, pres, domain)?;
                legal_execution_exists = Some(raw_legal);
                if !raw_ok {
                    passed = false;
                }
                residuals.extend(raw_res);
            }
            let mut ew_out = None;
            if let Some(pres_src) = preservation {
                let (pres_ok, pres_res, pres_ew) =
                    eval_direct_preservation(pres_src, &uc_subst, domain, point_domain)?;
                if !pres_ok {
                    passed = false;
                }
                residuals.extend(pres_res);
                if pres_ew.is_some() {
                    ew_out = pres_ew;
                }
            }
            Ok(PairEvaluationWitness {
                realization: realization.to_witness(),
                candidate_id: candidate.candidate_id.clone(),
                candidate_assignments: candidate.assignments.clone(),
                passed,
                legal_execution_exists,
                residuals,
                empty_witness: ew_out,
                restored_completion: None,
            })
        }
        GoodnessSpec::Existential {
            equations,
            invertibles,
            preservation,
            ..
        } => evaluate_existential_point(
            equations,
            invertibles,
            preservation.as_ref(),
            w_names,
            &uc_subst,
            realization,
            candidate,
            domain,
            point_domain,
        ),
    }
}

fn evaluate_raw_sequence_on_presentation(
    seq: &RawSequenceCheck,
    pres: &Presentation,
    domain: &CoeffDomain,
) -> Result<(bool, bool, Vec<String>), SilenceReason> {
    let mut cur_phase = pres.phase(&seq.start_phase).ok_or_else(|| {
        SilenceReason::ApplicabilityConditionNotMet {
            condition: "raw_sequence_phase_exists".to_owned(),
            detail: format!("unknown phase `{}`", seq.start_phase),
        }
    })?;
    let mut state: BTreeMap<String, ScalarVal> = BTreeMap::new();
    for c in &cur_phase.coords {
        if let CoordValue::Observed(lit) = &c.value {
            state.insert(c.name.clone(), ScalarVal::from_lit(lit, domain)?);
        }
    }
    for (k, lit) in &seq.start_state {
        state.insert(k.clone(), ScalarVal::from_lit(lit, domain)?);
    }

    let empty = BTreeMap::new();
    let zero_vars =
        VarOrder::new(vec![]).map_err(crate::solver::preservation::map_algebra_silence)?;
    let mut residuals = Vec::new();
    let mut any_law_failed = false;

    let check_phase_laws = |ph: &PhaseDecl,
                            st: &BTreeMap<String, ScalarVal>,
                            law_failed: &mut bool,
                            res: &mut Vec<String>|
     -> Result<(), SilenceReason> {
        let st_expr: BTreeMap<String, PolyExpr> =
            st.iter().map(|(k, v)| (k.clone(), v.to_expr())).collect();
        for law in &ph.state_laws {
            let sub = substitute_poly_expr(&law.polynomial, &st_expr, &empty, &empty);
            let val = eval_expr_at(&sub, &zero_vars, &[], domain)?;
            if !val.is_zero() {
                *law_failed = true;
                res.push(format!("{}.{} = {}", ph.name, law.name, val.to_display()));
            }
        }
        Ok(())
    };

    check_phase_laws(cur_phase, &state, &mut any_law_failed, &mut residuals)?;

    let effective_base_idx = seq
        .baseline_step_index
        .unwrap_or_else(|| seq.steps.len().saturating_sub(2));
    let mut baseline_obs: Option<Vec<ScalarVal>> =
        if seq.baseline_step_index.is_none() && seq.steps.len() == 1 {
            Some(eval_phase_observation(
                pres,
                cur_phase,
                &seq.observation_name,
                &state,
                domain,
            )?)
        } else {
            None
        };

    for (idx, (op_name, arg_lits)) in seq.steps.iter().enumerate() {
        let op =
            pres.operation(op_name)
                .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                    condition: "raw_sequence_op_exists".to_owned(),
                    detail: format!("unknown operation `{op_name}`"),
                })?;
        let st_expr: BTreeMap<String, PolyExpr> = state
            .iter()
            .map(|(k, v)| (k.clone(), v.to_expr()))
            .collect();
        let mut arg_expr = BTreeMap::new();
        for ((arg_name, _), lit) in op.args.iter().zip(arg_lits) {
            arg_expr.insert(
                arg_name.clone(),
                ScalarVal::from_lit(lit, domain)?.to_expr(),
            );
        }
        for dlaw in &op.domain_laws {
            let sub = substitute_poly_expr(&dlaw.polynomial, &st_expr, &arg_expr, &empty);
            let val = eval_expr_at(&sub, &zero_vars, &[], domain)?;
            if !val.is_zero() {
                any_law_failed = true;
                residuals.push(format!("{}.{} = {}", op.name, dlaw.name, val.to_display()));
            }
        }
        let next_phase = pres.phase(&op.target_phase).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "raw_sequence_target_phase_exists".to_owned(),
                detail: format!("unknown target phase `{}`", op.target_phase),
            }
        })?;
        let mut next_state = BTreeMap::new();
        for c in &next_phase.coords {
            if let Some(up_expr) = op.updates.get(&c.name) {
                let sub = substitute_poly_expr(up_expr, &st_expr, &arg_expr, &empty);
                next_state.insert(c.name.clone(), eval_expr_at(&sub, &zero_vars, &[], domain)?);
            } else if let CoordValue::Observed(lit) = &c.value {
                next_state.insert(c.name.clone(), ScalarVal::from_lit(lit, domain)?);
            }
        }
        cur_phase = next_phase;
        state = next_state;
        check_phase_laws(cur_phase, &state, &mut any_law_failed, &mut residuals)?;
        if baseline_obs.is_none() && idx == effective_base_idx {
            baseline_obs = Some(eval_phase_observation(
                pres,
                cur_phase,
                &seq.observation_name,
                &state,
                domain,
            )?);
        }
    }

    let final_obs = eval_phase_observation(pres, cur_phase, &seq.observation_name, &state, domain)?;
    let base_obs = baseline_obs.unwrap_or_else(|| final_obs.clone());
    let mut obs_matched = true;
    for (i, (f_val, b_val)) in final_obs.iter().zip(&base_obs).enumerate() {
        let diff_expr = PolyExpr::diff(f_val.to_expr(), b_val.to_expr());
        let diff = eval_expr_at(&diff_expr, &zero_vars, &[], domain)?;
        if !diff.is_zero() {
            obs_matched = false;
            residuals.push(format!(
                "{}[{i}]_diff = {}",
                seq.observation_name,
                diff.to_display()
            ));
        }
    }
    let legal = !any_law_failed;
    Ok((legal && obs_matched, legal, residuals))
}

fn eval_phase_observation(
    pres: &Presentation,
    phase: &PhaseDecl,
    obs_name: &str,
    state: &BTreeMap<String, ScalarVal>,
    domain: &CoeffDomain,
) -> Result<Vec<ScalarVal>, SilenceReason> {
    let obs = pres
        .observations
        .iter()
        .find(|o| o.name == obs_name && o.phase == phase.name)
        .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
            condition: "raw_sequence_observation_exists".to_owned(),
            detail: format!("observation `{obs_name}` missing at phase `{}`", phase.name),
        })?;
    let empty = BTreeMap::new();
    let zero_vars =
        VarOrder::new(vec![]).map_err(crate::solver::preservation::map_algebra_silence)?;
    let st_expr: BTreeMap<String, PolyExpr> = state
        .iter()
        .map(|(k, v)| (k.clone(), v.to_expr()))
        .collect();
    obs.components
        .iter()
        .map(|comp| {
            let sub = substitute_poly_expr(comp, &st_expr, &empty, &empty);
            eval_expr_at(&sub, &zero_vars, &[], domain)
        })
        .collect()
}

pub(crate) fn substitute_preservation_pair(
    src: &PreservationGoodnessSource,
    ucw_subst: &BTreeMap<String, PolyExpr>,
) -> Result<(ComparisonPair, Vec<String>), SilenceReason> {
    let empty = BTreeMap::new();
    let mut param_map = BTreeMap::new();
    for p in &src.change_spec.parameters {
        let bound = if let Some(expr) = src.param_bindings.get(&p.name) {
            substitute_poly_expr(expr, &empty, &empty, ucw_subst)
        } else if let Some(expr) = ucw_subst.get(&p.name) {
            expr.clone()
        } else {
            PolyExpr::param(&p.name)
        };
        param_map.insert(p.name.clone(), bound);
    }
    let pair = substitute_comparison_pair(&src.pair, &param_map);
    if !collect_presentation_params(&pair.before).is_empty() {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "before_presentation_must_be_parameter_free".to_owned(),
            detail: "substituted fixed reference presentation still contains parameters".to_owned(),
        });
    }
    let remaining: BTreeSet<String> = collect_presentation_params(&pair.after)
        .into_iter()
        .collect();
    Ok((pair, remaining.into_iter().collect()))
}

fn eval_direct_preservation(
    src: &PreservationGoodnessSource,
    uc_subst: &BTreeMap<String, PolyExpr>,
    domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<(bool, Vec<String>, Option<EmptyWitness>), SilenceReason> {
    let (pair, rem) = substitute_preservation_pair(src, uc_subst)?;
    if !rem.is_empty() {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "direct_preservation_parameters_bound".to_owned(),
            detail: format!(
                "unbound parameters in direct preservation: {}",
                rem.join(", ")
            ),
        });
    }
    let obligations = build_preservation_obligations(&pair)?;
    let empty_vars =
        VarOrder::new(vec![]).map_err(crate::solver::preservation::map_algebra_silence)?;
    match domain {
        CoeffDomain::Fp(m) => {
            let Some(res) = extract_closed_residuals_fp(&obligations, &[], m)? else {
                return Err(SilenceReason::QuotientIdealOutOfScope {
                    detail: "quotient state-law reduction over Fp in family preservation is out of scope".to_owned(),
                });
            };
            let nonzero: Vec<String> = res
                .into_iter()
                .filter(|p| !p.is_zero())
                .map(|p| p.display(&empty_vars, MonomialOrder::Grevlex))
                .collect();
            Ok((nonzero.is_empty(), nonzero, None))
        }
        CoeffDomain::Z if *point_domain == PointDomain::IntegerPoints => {
            let Some(res) = extract_closed_residuals_z(&obligations, &[])? else {
                return Err(SilenceReason::QuotientIdealOutOfScope {
                    detail:
                        "quotient state-law reduction over Z in family preservation is out of scope"
                            .to_owned(),
                });
            };
            let nonzero: Vec<String> = res
                .into_iter()
                .filter(|p| !p.is_zero())
                .map(|p| p.display(&empty_vars, MonomialOrder::Grevlex))
                .collect();
            Ok((nonzero.is_empty(), nonzero, None))
        }
        CoeffDomain::Q | CoeffDomain::Z => {
            let locus = compute_preservation_locus_q(&obligations, &empty_vars)?;
            let disp = display_polys(&locus.closure_ideal, &empty_vars);
            Ok((!locus.strata.is_empty(), disp, locus.empty_witness))
        }
    }
}

/// Phase 3 タスクに埋め込まれた全 Presentation / Preservation の共通適用条件検査（M7）。
pub(crate) fn check_family_presentations_applicability(
    family: &CheckedFamilySpec,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<(), SilenceReason> {
    if let RealizationSpace::FiniteMembers(ms) = &family.inner().realizations.space {
        for m in ms {
            if let Some(pres) = &m.presentation {
                for s in &pres.sorts {
                    if s.rank != 1 {
                        let detail = format!("sort `{}` in `{}` has rank != 1", s.name, pres.name);
                        checks.push(ApplicabilityCheck::failed(
                            "sort_rank_one_required",
                            MathClause::G139P0P1,
                            detail.clone(),
                        ));
                        return Err(SilenceReason::ApplicabilityConditionNotMet {
                            condition: "sort_rank_one_required".to_owned(),
                            detail,
                        });
                    }
                }
            }
        }
    }
    if let GoodnessSpec::Direct {
        preservation: Some(src),
        ..
    }
    | GoodnessSpec::Existential {
        preservation: Some(src),
        ..
    } = &family.inner().goodness
    {
        for pres in [&src.pair.before, &src.pair.after] {
            for s in &pres.sorts {
                if s.rank != 1 {
                    let detail = format!("sort `{}` in `{}` has rank != 1", s.name, pres.name);
                    checks.push(ApplicabilityCheck::failed(
                        "sort_rank_one_required",
                        MathClause::G139P0P1,
                        detail.clone(),
                    ));
                    return Err(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "sort_rank_one_required".to_owned(),
                        detail,
                    });
                }
            }
        }
        if !collect_presentation_params(&src.pair.before).is_empty() {
            let detail =
                "reference presentation `before` must not contain search parameters".to_owned();
            checks.push(ApplicabilityCheck::failed(
                "before_presentation_must_be_parameter_free",
                MathClause::G140E1E2,
                detail.clone(),
            ));
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "before_presentation_must_be_parameter_free".to_owned(),
                detail,
            });
        }
        for target in &src.change_spec.editable {
            let target_pres = match target {
                EditableTarget::OperationExpr { presentation, .. }
                | EditableTarget::RepresentationLaw { presentation, .. } => {
                    Some(presentation.as_str())
                }
                EditableTarget::StateComparisonExpr { .. } => None,
            };
            if target_pres == Some(src.pair.before.name.as_str()) {
                let detail = format!(
                    "editable target references fixed reference presentation `{}`",
                    src.pair.before.name
                );
                checks.push(ApplicabilityCheck::failed(
                    "editable_target_must_be_after",
                    MathClause::G140E1E2,
                    detail.clone(),
                ));
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "editable_target_must_be_after".to_owned(),
                    detail,
                });
            }
        }
    }
    checks.push(ApplicabilityCheck::passed(
        "family_presentations_well_formed",
        MathClause::G139P0P1,
    ));
    Ok(())
}
