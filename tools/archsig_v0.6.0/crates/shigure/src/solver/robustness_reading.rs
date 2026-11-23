//! Coarse vs fine reading comparison (`E5.1` / `G4`) and P7 raw sequence residuals
//! extracted from `robustness.rs` to keep every module compact.

use crate::algebra::{ExprBindings, Poly, VarOrder};
use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::family::{CandidateSpace, CheckedFamilySpec, FamilySpec, RealizationSpace};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase3::{
    CommonQuantifierResult, DesignatedValidityResult, RawCandidateEvaluationSummary,
    ReadingComparisonResult,
};
use crate::ir::robustness::CheckedRobustnessTask;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::chevalley::build_family_constructible_sets;
use crate::solver::family_direct::evaluate_goodness_at_point;
use crate::solver::family_eval::{
    CandidateFiberEnum, EnumCandidate, RealizationFiberEnum, ScalarVal, eval_expr_at,
    map_scalar_assignments,
};
use crate::solver::preservation::{map_algebra_silence, substitute_poly_expr};
use std::collections::BTreeMap;

#[allow(clippy::too_many_arguments)]
pub(super) fn compute_reading_comparison(
    task: &CheckedRobustnessTask,
    family: &CheckedFamilySpec,
    real_enum: &RealizationFiberEnum,
    cand_enum: &CandidateFiberEnum,
    designated: Option<&EnumCandidate>,
    valid_des: &Option<DesignatedValidityResult>,
    common: &Option<CommonQuantifierResult>,
    point_domain: &PointDomain,
) -> Result<Option<ReadingComparisonResult>, SilenceReason> {
    let Some(rc) = family.reading_comparison() else {
        return Ok(None);
    };
    let domain = family.coeff_domain();
    let u_names = family.u_vars();
    let u_vars = VarOrder::new(u_names.to_vec()).map_err(map_algebra_silence)?;
    let fine_vars = VarOrder::new(rc.fine_b_vars.clone()).map_err(map_algebra_silence)?;

    let fine_b_vals = if let Some(fv) = task.fine_base_value() {
        fv.to_vec()
    } else {
        Vec::new()
    };

    let empty = BTreeMap::new();
    let q_subst: BTreeMap<String, PolyExpr> = rc
        .fine_b_vars
        .iter()
        .zip(&rc.fine_q)
        .map(|(n, e)| (n.clone(), e.clone()))
        .collect();
    let mut commutativity_verified = true;
    match &family.inner().realizations.space {
        RealizationSpace::FiniteMembers(ms) => {
            for m in ms {
                let (vals, _) = map_scalar_assignments(u_names, &m.assignments, domain)?;
                for (q_expr, r_expr) in family
                    .inner()
                    .realizations
                    .reading_q
                    .iter()
                    .zip(&rc.coarsen_r)
                {
                    let comp = substitute_poly_expr(r_expr, &empty, &empty, &q_subst);
                    let lhs = eval_expr_at(&comp, &u_vars, &vals, domain)?;
                    let rhs = eval_expr_at(q_expr, &u_vars, &vals, domain)?;
                    if lhs != rhs {
                        commutativity_verified = false;
                        break;
                    }
                }
            }
        }
        RealizationSpace::PolynomialScheme { .. } => {
            let u_bind = ExprBindings::params_only(&u_vars);
            for (q_expr, r_expr) in family
                .inner()
                .realizations
                .reading_q
                .iter()
                .zip(&rc.coarsen_r)
            {
                let comp = substitute_poly_expr(r_expr, &empty, &empty, &q_subst);
                let diff = PolyExpr::diff(comp, q_expr.clone());
                let is_zero_diff = match domain {
                    CoeffDomain::Fp(p) => Poly::from_expr_fp(&diff, &u_bind, p)
                        .map_err(map_algebra_silence)?
                        .is_zero(),
                    CoeffDomain::Q | CoeffDomain::Z => Poly::from_expr_q(&diff, &u_bind)
                        .map_err(map_algebra_silence)?
                        .is_zero(),
                };
                if !is_zero_diff {
                    commutativity_verified = false;
                }
            }
        }
    }
    if !commutativity_verified {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "reading_comparison_commutes".to_owned(),
            detail: "coarse/fine reading diagram r o q' != q on realization space".to_owned(),
        });
    }

    let coarse_b_str: Vec<String> = task
        .base_value()
        .iter()
        .map(|l| ScalarVal::from_lit(l, domain).map(|v| v.to_display()))
        .collect::<Result<Vec<_>, _>>()?;
    let fine_b_str: Vec<String> = fine_b_vals
        .iter()
        .map(|l| ScalarVal::from_lit(l, domain).map(|v| v.to_display()))
        .collect::<Result<Vec<_>, _>>()?;

    if !fine_b_vals.is_empty() {
        let fv_scalar: Vec<ScalarVal> = fine_b_vals
            .iter()
            .map(|l| ScalarVal::from_lit(l, domain))
            .collect::<Result<Vec<_>, _>>()?;
        let target_b: Vec<ScalarVal> = task
            .base_value()
            .iter()
            .map(|l| ScalarVal::from_lit(l, domain))
            .collect::<Result<Vec<_>, _>>()?;
        for (r_expr, b_val) in rc.coarsen_r.iter().zip(&target_b) {
            if &eval_expr_at(r_expr, &fine_vars, &fv_scalar, domain)? != b_val {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "reading_comparison_base_commutes".to_owned(),
                    detail: "r(fine_base_value) does not match coarse base_value".to_owned(),
                });
            }
        }
    }

    let mut raw_evals = Vec::new();
    let mut coarse_ce = None;
    if let RealizationFiberEnum::Finite(u_list) = real_enum {
        let eval_cand = designated.cloned().or_else(|| match cand_enum {
            CandidateFiberEnum::Finite(cs) if !cs.is_empty() => Some(cs[0].clone()),
            _ => None,
        });
        if let Some(c_use) = &eval_cand {
            for u in u_list {
                let qv = family
                    .inner()
                    .realizations
                    .reading_q
                    .iter()
                    .map(|q| eval_expr_at(q, &u_vars, &u.values, domain).map(|s| s.to_display()))
                    .collect::<Result<Vec<_>, _>>()?;
                let w = evaluate_goodness_at_point(family, u, c_use, point_domain)?;
                if !w.passed && coarse_ce.is_none() {
                    coarse_ce = Some(w.clone());
                }
                raw_evals.push(RawCandidateEvaluationSummary {
                    member_id: u
                        .member_id
                        .clone()
                        .unwrap_or_else(|| "scheme_pt".to_owned()),
                    origin: u.origin.clone(),
                    q_value: qv,
                    passed: w.passed,
                    legal_execution_exists: w.legal_execution_exists,
                    residuals: w.residuals,
                });
            }
        }
    }

    let coarse_robust = valid_des
        .as_ref()
        .map(|v| v.satisfied)
        .or_else(|| common.as_ref().map(|c| c.satisfied))
        .unwrap_or(false);

    let fine_robust = if fine_b_vals.is_empty() {
        coarse_robust
    } else if let RealizationFiberEnum::Finite(u_list) = real_enum {
        let target_f: Vec<ScalarVal> = fine_b_vals
            .iter()
            .map(|l| ScalarVal::from_lit(l, domain))
            .collect::<Result<Vec<_>, _>>()?;
        let mut fine_us = Vec::new();
        for u in u_list {
            let mut eq_all = true;
            for (fq, fv) in rc.fine_q.iter().zip(&target_f) {
                if &eval_expr_at(fq, &u_vars, &u.values, domain)? != fv {
                    eq_all = false;
                    break;
                }
            }
            if eq_all {
                fine_us.push(u);
            }
        }
        if fine_us.is_empty() {
            false
        } else if let Some(dc) = designated {
            let mut ok = true;
            for u in &fine_us {
                if !evaluate_goodness_at_point(family, u, dc, point_domain)?.passed {
                    ok = false;
                    break;
                }
            }
            ok
        } else if let CandidateFiberEnum::Finite(c_list) = cand_enum {
            let mut found_common = false;
            for c in c_list {
                let mut all_ok = true;
                for u in &fine_us {
                    if !evaluate_goodness_at_point(family, u, c, point_domain)?.passed {
                        all_ok = false;
                        break;
                    }
                }
                if all_ok {
                    found_common = true;
                    break;
                }
            }
            found_common
        } else {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "fine_reading_comparison_scheme_candidates".to_owned(),
                detail: "fine_base_value comparison with FiniteMembers realizations and NonFiniteScheme candidates requires AlgebraicClosure constructible path".to_owned(),
            });
        }
    } else {
        if *point_domain != PointDomain::AlgebraicClosure || matches!(domain, CoeffDomain::Fp(_)) {
            return Err(SilenceReason::FiniteEnumerationOutOfScope {
                detail: "fine_base_value comparison on non-finite realization scheme requires AlgebraicClosure over Q/Z".to_owned(),
            });
        }
        let mut fine_spec: FamilySpec = family.inner().clone();
        fine_spec.reading_comparison = None;
        if let RealizationSpace::PolynomialScheme { equations, .. } =
            &mut fine_spec.realizations.space
        {
            for (i, (fq, fl)) in rc.fine_q.iter().zip(&fine_b_vals).enumerate() {
                equations.push(NamedPoly::new(
                    format!("fine_fiber_{i}"),
                    PolyExpr::diff(fq.clone(), PolyExpr::Const(fl.clone())),
                ));
            }
        }
        let c_vars_ord = VarOrder::new(family.c_vars().to_vec()).map_err(map_algebra_silence)?;
        let target_b: Vec<ScalarVal> = task
            .base_value()
            .iter()
            .map(|l| ScalarVal::from_lit(l, domain))
            .collect::<Result<Vec<_>, _>>()?;
        match &mut fine_spec.candidates.space {
            CandidateSpace::PolynomialScheme { equations, .. } => {
                for (i, (pe, bl)) in family
                    .inner()
                    .candidates
                    .pi
                    .iter()
                    .zip(task.base_value())
                    .enumerate()
                {
                    equations.push(NamedPoly::new(
                        format!("cand_fiber_{i}"),
                        PolyExpr::diff(pe.clone(), PolyExpr::Const(bl.clone())),
                    ));
                }
            }
            CandidateSpace::FiniteMembers(ms) => {
                let mut filtered = Vec::with_capacity(ms.len());
                for m in ms.drain(..) {
                    let (vals, _) =
                        map_scalar_assignments(family.c_vars(), &m.assignments, domain)?;
                    let mut ok = true;
                    for (pe, bv) in family.inner().candidates.pi.iter().zip(&target_b) {
                        if &eval_expr_at(pe, &c_vars_ord, &vals, domain)? != bv {
                            ok = false;
                            break;
                        }
                    }
                    if ok {
                        filtered.push(m);
                    }
                }
                *ms = filtered;
            }
        }
        fine_spec.realizations.b_vars.clear();
        fine_spec.realizations.reading_q.clear();
        fine_spec.candidates.pi.clear();
        let checked_fine = CheckedFamilySpec::validate(fine_spec).map_err(|e| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "fine_reading_family_valid".to_owned(),
                detail: e.to_string(),
            }
        })?;
        let fine_sets = build_family_constructible_sets(&checked_fine, None)?;
        if let Some(dc) = designated {
            let pt: Vec<_> = dc.values.iter().map(ScalarVal::as_rat).collect();
            fine_sets.robust_all_pass.contains_point(&pt)?
        } else {
            !fine_sets.robust_all_pass.is_empty()
        }
    };

    let preserved = !coarse_robust || fine_robust;
    let fine_only_ce = if !coarse_robust && fine_robust {
        coarse_ce
    } else {
        None
    };
    Ok(Some(ReadingComparisonResult {
        name: rc.name.clone(),
        coarse_b: coarse_b_str,
        fine_b: fine_b_str,
        commutativity_verified,
        coarse_robust,
        fine_robust,
        coarse_implies_fine_preserved: preserved,
        reverse_implication_not_claimed: true,
        fine_only_counterexample: fine_only_ce,
        raw_candidate_evaluations: raw_evals,
    }))
}
