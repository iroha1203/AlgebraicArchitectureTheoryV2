//! AAT 第18章 アフィン表示（$x = x_0 + T t$）・命題 18.9 アフィン正規化・MUS 抽出ヘルパ。

use crate::algebra::artin::{AffineSolutionField, rref_field, solve_affine_field};
use crate::algebra::linear::{AffineSolutionQ, AffineSolutionZ, solve_affine_q, solve_affine_z};
use crate::algebra::poly::AlgebraError;
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::algebra::syzygy::FieldCoeff;
use crate::ir::partial::AffinePartialPresentation;
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, SilenceReason};
use crate::ir::result_phase5_obs::PartialLawEvalSummary;
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::solver::partial_completions::CompletionEvalOutput;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{Signed, Zero};

const MAX_AFFINE_MUS_RECORDS: usize = 16;

type AffineBasisResult<C> = Result<Option<(Vec<C>, Vec<Vec<C>>)>, SilenceReason>;

pub(super) fn analyze_affine_partial(
    aff: &AffinePartialPresentation,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<CompletionEvalOutput, SilenceReason> {
    checks.push(ApplicabilityCheck::passed(
        "affine_normalization_checked",
        MathClause::AatCh18Prop18Dot9,
    ));
    match &aff.coeff_domain {
        CoeffDomain::Q => solve_affine_generic_field(aff, scalar_to_rat, |m, b, k| {
            match solve_affine_q(m, b, k) {
                Ok(AffineSolutionQ::Consistent {
                    particular,
                    kernel_basis,
                    ..
                }) => Ok(Some((particular, kernel_basis))),
                Ok(AffineSolutionQ::Inconsistent { .. }) => Ok(None),
                Err(e) => Err(e),
            }
        }),
        CoeffDomain::Fp(p) => {
            let p_clone = p.clone();
            let zero_fp = FpElem::from_checked_prime(BigInt::zero(), p.clone());
            solve_affine_generic_field(
                aff,
                move |lit| scalar_to_fp(lit, &p_clone),
                move |m, b, k| match solve_affine_field(m, b, k, &zero_fp) {
                    Ok(AffineSolutionField::Consistent {
                        particular,
                        kernel_basis,
                        ..
                    }) => Ok(Some((particular, kernel_basis))),
                    Ok(AffineSolutionField::Inconsistent { .. }) => Ok(None),
                    Err(e) => Err(e),
                },
            )
        }
        CoeffDomain::Z => solve_affine_z_partial(aff),
    }
}

fn solve_affine_generic_field<C, FConv, FSolve>(
    aff: &AffinePartialPresentation,
    conv: FConv,
    solve_fn: FSolve,
) -> Result<CompletionEvalOutput, SilenceReason>
where
    C: FieldCoeff + std::fmt::Display,
    FConv: Fn(&ScalarLit) -> C,
    FSolve: Fn(&[Vec<C>], &[C], usize) -> Result<Option<(Vec<C>, Vec<Vec<C>>)>, AlgebraError>,
{
    let t_cols = aff.direction_t.first().map_or(0, Vec::len);
    let num_vars = if t_cols > 0 {
        t_cols
    } else {
        aff.coord_names.len()
    };
    let x0_vec: Vec<C> = aff.x0.iter().map(&conv).collect();
    let t_mat: Vec<Vec<C>> = aff
        .direction_t
        .iter()
        .map(|row| row.iter().map(&conv).collect())
        .collect();

    let to_substituted_row = |coeffs: &[ScalarLit], rhs_lit: &ScalarLit| -> (Vec<C>, C) {
        let a_row: Vec<C> = coeffs.iter().map(&conv).collect();
        let rhs_c = conv(rhs_lit);
        if t_cols == 0 {
            return (a_row, rhs_c);
        }
        let mut a_x0 = C::zero_like(&rhs_c);
        for (a, x) in a_row.iter().zip(&x0_vec) {
            a_x0 = a_x0.add_ref(&a.mul_ref(x));
        }
        let mut new_row = vec![C::zero_like(&rhs_c); t_cols];
        for (a, t_row) in a_row.iter().zip(&t_mat) {
            for (dst, t_ij) in new_row.iter_mut().zip(t_row) {
                *dst = dst.add_ref(&a.mul_ref(t_ij));
            }
        }
        (new_row, rhs_c.sub_ref(&a_x0))
    };

    let bg: Vec<(Vec<C>, C)> = aff
        .background_rows
        .iter()
        .map(|(_, row, rhs)| to_substituted_row(row, rhs))
        .collect();
    let rec_rows: Vec<(&str, Vec<C>, C)> = aff
        .record_rows
        .iter()
        .map(|(id, row, rhs)| {
            let (nr, nb) = to_substituted_row(row, rhs);
            (id.as_str(), nr, nb)
        })
        .collect();

    let check_subset = |mask: usize| -> AffineBasisResult<C> {
        let mut m = Vec::new();
        let mut b = Vec::new();
        for (r, rhs) in &bg {
            m.push(r.clone());
            b.push(rhs.clone());
        }
        for (idx, (_, r, rhs)) in rec_rows.iter().enumerate() {
            if (mask & (1usize << idx)) != 0 {
                m.push(r.clone());
                b.push(rhs.clone());
            }
        }
        solve_fn(&m, &b, num_vars).map_err(|e| SilenceReason::FiniteEnumerationOutOfScope {
            detail: format!("{e:?}"),
        })
    };

    let Some((part_t, ker_t)) = (if rec_rows.len() > MAX_AFFINE_MUS_RECORDS {
        let mut m = Vec::new();
        let mut b = Vec::new();
        for (r, rhs) in &bg {
            m.push(r.clone());
            b.push(rhs.clone());
        }
        for (_, r, rhs) in &rec_rows {
            m.push(r.clone());
            b.push(rhs.clone());
        }
        solve_fn(&m, &b, num_vars).map_err(|e| SilenceReason::FiniteEnumerationOutOfScope {
            detail: format!("{e:?}"),
        })?
    } else {
        let full_mask = (1usize << rec_rows.len()) - 1;
        check_subset(full_mask)?
    }) else {
        let (mus, mus_verified) = extract_affine_mus(&rec_rows, &check_subset)?;
        let evals = aff
            .eval_equations
            .iter()
            .map(|(name, _, _)| PartialLawEvalSummary {
                law_name: name.clone(),
                strong_kleene: "unknown".to_owned(),
                supervaluation: "vacuously_true".to_owned(),
                antecedent_regime: None,
                conditional_conclusion_eval: None,
                affine_normalized_eval: Some("empty_solution_space".to_owned()),
            })
            .collect();
        return Ok(CompletionEvalOutput {
            consistent: false,
            completion_count: Some(0),
            minimal_inconsistent_subsets: mus,
            mus_verified,
            law_evaluations: evals,
            kleene_soundness_verified: true,
        });
    };

    let evals = aff
        .eval_equations
        .iter()
        .map(|(name, b_row, e_rhs)| {
            let (nr, nb) = to_substituted_row(b_row, e_rhs);
            let mut lhs_at_p = C::zero_like(&nb);
            for (c, x) in nr.iter().zip(&part_t) {
                lhs_at_p = lhs_at_p.add_ref(&c.mul_ref(x));
            }
            let diff = nb.sub_ref(&lhs_at_p);
            let dir_coeffs: Vec<C> = ker_t
                .iter()
                .map(|kv| {
                    let mut sum = C::zero_like(&nb);
                    for (c, k) in nr.iter().zip(kv) {
                        sum = sum.add_ref(&c.mul_ref(k));
                    }
                    sum
                })
                .collect();
            let all_zero_dir = dir_coeffs.iter().all(RingCoeff::coeff_is_zero);
            let (superval, kleene, norm_desc) = if all_zero_dir {
                if diff.coeff_is_zero() {
                    ("true", "true", "0 = 0 (always_true)".to_owned())
                } else {
                    ("false", "false", format!("0 = {diff} (contradiction)"))
                }
            } else {
                let terms: Vec<String> = dir_coeffs
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| !c.coeff_is_zero())
                    .map(|(j, c)| format!("{c}*s{j}"))
                    .collect();
                (
                    "indeterminate",
                    "unknown",
                    format!("{} = {diff}", terms.join(" + ")),
                )
            };
            PartialLawEvalSummary {
                law_name: name.clone(),
                strong_kleene: kleene.to_owned(),
                supervaluation: superval.to_owned(),
                antecedent_regime: None,
                conditional_conclusion_eval: None,
                affine_normalized_eval: Some(norm_desc),
            }
        })
        .collect();

    Ok(CompletionEvalOutput {
        consistent: true,
        completion_count: if ker_t.is_empty() { Some(1) } else { None },
        minimal_inconsistent_subsets: vec![],
        mus_verified: true,
        law_evaluations: evals,
        kleene_soundness_verified: true,
    })
}

fn solve_affine_z_partial(
    aff: &AffinePartialPresentation,
) -> Result<CompletionEvalOutput, SilenceReason> {
    let t_cols = aff.direction_t.first().map_or(0, Vec::len);
    let num_vars = if t_cols > 0 {
        t_cols
    } else {
        aff.coord_names.len()
    };
    let to_z = |lit: &ScalarLit| -> BigInt {
        match lit {
            ScalarLit::Z(n) => n.clone(),
            _ => BigInt::zero(),
        }
    };
    let x0_vec: Vec<BigInt> = aff.x0.iter().map(to_z).collect();
    let t_mat: Vec<Vec<BigInt>> = aff
        .direction_t
        .iter()
        .map(|row| row.iter().map(to_z).collect())
        .collect();

    let to_sub_z = |coeffs: &[ScalarLit], rhs_lit: &ScalarLit| -> (Vec<BigInt>, BigInt) {
        let a_row: Vec<BigInt> = coeffs.iter().map(to_z).collect();
        let rhs = to_z(rhs_lit);
        if t_cols == 0 {
            return (a_row, rhs);
        }
        let a_x0: BigInt = a_row.iter().zip(&x0_vec).map(|(a, x)| a * x).sum();
        let mut new_row = vec![BigInt::zero(); t_cols];
        for (a, t_row) in a_row.iter().zip(&t_mat) {
            for (dst, t_ij) in new_row.iter_mut().zip(t_row) {
                *dst += a * t_ij;
            }
        }
        (new_row, rhs - a_x0)
    };

    let bg: Vec<(Vec<BigInt>, BigInt)> = aff
        .background_rows
        .iter()
        .map(|(_, row, rhs)| to_sub_z(row, rhs))
        .collect();
    let rec_rows: Vec<(&str, Vec<BigInt>, BigInt)> = aff
        .record_rows
        .iter()
        .map(|(id, row, rhs)| {
            let (nr, nb) = to_sub_z(row, rhs);
            (id.as_str(), nr, nb)
        })
        .collect();

    let check_subset = |mask: usize| -> AffineBasisResult<BigInt> {
        let mut m = Vec::new();
        let mut b = Vec::new();
        for (r, rhs) in &bg {
            m.push(r.clone());
            b.push(rhs.clone());
        }
        for (idx, (_, r, rhs)) in rec_rows.iter().enumerate() {
            if (mask & (1usize << idx)) != 0 {
                m.push(r.clone());
                b.push(rhs.clone());
            }
        }
        match solve_affine_z(&m, &b, num_vars) {
            Ok(AffineSolutionZ::Consistent {
                particular,
                kernel_basis,
                ..
            }) => Ok(Some((particular, kernel_basis))),
            Ok(AffineSolutionZ::Inconsistent { .. }) => Ok(None),
            Err(e) => Err(SilenceReason::FiniteEnumerationOutOfScope {
                detail: format!("{e:?}"),
            }),
        }
    };

    let Some((part_t, ker_t)) = (if rec_rows.len() > MAX_AFFINE_MUS_RECORDS {
        let mut m = Vec::new();
        let mut b = Vec::new();
        for (r, rhs) in &bg {
            m.push(r.clone());
            b.push(rhs.clone());
        }
        for (_, r, rhs) in &rec_rows {
            m.push(r.clone());
            b.push(rhs.clone());
        }
        match solve_affine_z(&m, &b, num_vars) {
            Ok(AffineSolutionZ::Consistent {
                particular,
                kernel_basis,
                ..
            }) => Some((particular, kernel_basis)),
            Ok(AffineSolutionZ::Inconsistent { .. }) => None,
            Err(e) => {
                return Err(SilenceReason::FiniteEnumerationOutOfScope {
                    detail: format!("{e:?}"),
                });
            }
        }
    } else {
        let full_mask = (1usize << rec_rows.len()) - 1;
        check_subset(full_mask)?
    }) else {
        let (mus, mus_verified) = extract_affine_mus(&rec_rows, &check_subset)?;
        let evals = aff
            .eval_equations
            .iter()
            .map(|(name, _, _)| PartialLawEvalSummary {
                law_name: name.clone(),
                strong_kleene: "unknown".to_owned(),
                supervaluation: "vacuously_true".to_owned(),
                antecedent_regime: None,
                conditional_conclusion_eval: None,
                affine_normalized_eval: Some("empty_solution_space".to_owned()),
            })
            .collect();
        return Ok(CompletionEvalOutput {
            consistent: false,
            completion_count: Some(0),
            minimal_inconsistent_subsets: mus,
            mus_verified,
            law_evaluations: evals,
            kleene_soundness_verified: true,
        });
    };

    let evals =
        aff.eval_equations
            .iter()
            .map(|(name, b_row, e_rhs)| {
                let (nr, nb) = to_sub_z(b_row, e_rhs);
                let lhs_at_p: BigInt = nr.iter().zip(&part_t).map(|(c, x)| c * x).sum();
                let diff = nb - lhs_at_p;
                let dir_coeffs: Vec<BigInt> = ker_t
                    .iter()
                    .map(|kv| nr.iter().zip(kv).map(|(c, k)| c * k).sum())
                    .collect();
                let all_zero_dir = dir_coeffs.iter().all(Zero::is_zero);
                let (superval, kleene, norm_desc) = if all_zero_dir {
                    if diff.is_zero() {
                        ("true", "true", "0 = 0 (always_true)".to_owned())
                    } else {
                        ("false", "false", format!("0 = {diff} (contradiction)"))
                    }
                } else {
                    let g = dir_coeffs.iter().filter(|c| !c.is_zero()).fold(
                        BigInt::zero(),
                        |acc, c| {
                            if acc.is_zero() {
                                c.abs()
                            } else {
                                acc.gcd(&c.abs())
                            }
                        },
                    );
                    if !g.is_zero() && !(diff.clone() % g.clone()).is_zero() {
                        (
                            "false",
                            "false",
                            format!("unsolvable_mod_{g} (diff={diff})"),
                        )
                    } else {
                        let terms: Vec<String> = dir_coeffs
                            .iter()
                            .enumerate()
                            .filter(|(_, c)| !c.is_zero())
                            .map(|(j, c)| format!("{c}*s{j}"))
                            .collect();
                        (
                            "indeterminate",
                            "unknown",
                            format!("{} = {diff}", terms.join(" + ")),
                        )
                    }
                };
                PartialLawEvalSummary {
                    law_name: name.clone(),
                    strong_kleene: kleene.to_owned(),
                    supervaluation: superval.to_owned(),
                    antecedent_regime: None,
                    conditional_conclusion_eval: None,
                    affine_normalized_eval: Some(norm_desc),
                }
            })
            .collect();

    Ok(CompletionEvalOutput {
        consistent: true,
        completion_count: if ker_t.is_empty() { Some(1) } else { None },
        minimal_inconsistent_subsets: vec![],
        mus_verified: true,
        law_evaluations: evals,
        kleene_soundness_verified: true,
    })
}

fn extract_affine_mus<T, S, FCheck>(
    rec_rows: &[(&str, Vec<T>, T)],
    check_subset: &FCheck,
) -> Result<(Vec<Vec<String>>, bool), SilenceReason>
where
    FCheck: Fn(usize) -> Result<Option<S>, SilenceReason>,
{
    let n = rec_rows.len();
    if n > MAX_AFFINE_MUS_RECORDS {
        return Err(SilenceReason::FiniteEnumerationOutOfScope {
            detail: format!(
                "affine record count ({n}) exceeds MUS bound ({MAX_AFFINE_MUS_RECORDS})"
            ),
        });
    }
    let mut mus_masks: Vec<usize> = Vec::new();
    for size in 0..=n {
        for mask in 0usize..(1usize << n) {
            if mask.count_ones() as usize != size {
                continue;
            }
            if mus_masks.iter().copied().any(|m| (m & mask) == m) {
                continue;
            }
            if check_subset(mask)?.is_none() {
                mus_masks.push(mask);
            }
        }
    }
    let mut verified = !mus_masks.is_empty();
    let mut mus = Vec::with_capacity(mus_masks.len());
    for mask in mus_masks {
        if check_subset(mask)?.is_some() {
            verified = false;
        }
        for i in 0..n {
            if (mask & (1usize << i)) != 0 && check_subset(mask & !(1usize << i))?.is_none() {
                verified = false;
            }
        }
        let mut ids: Vec<String> = (0..n)
            .filter(|i| (mask & (1usize << i)) != 0)
            .map(|i| rec_rows[i].0.to_owned())
            .collect();
        ids.sort();
        mus.push(ids);
    }
    mus.sort();
    Ok((mus, verified))
}

pub(super) fn scalar_to_rat(lit: &ScalarLit) -> Rat {
    match lit {
        ScalarLit::Q { num, den } => {
            Rat::new(num.clone(), den.clone()).expect("validated rational")
        }
        ScalarLit::Z(n) => Rat::from_int(n.clone()),
        ScalarLit::Fp { .. } => Rat::zero(),
    }
}

pub(super) fn scalar_to_fp(lit: &ScalarLit, p: &BigUint) -> FpElem {
    match lit {
        ScalarLit::Fp { value, modulus } => {
            FpElem::from_checked_prime(BigInt::from(value.clone()), modulus.clone())
        }
        ScalarLit::Z(n) => FpElem::from_checked_prime(n.clone(), p.clone()),
        ScalarLit::Q { .. } => FpElem::from_checked_prime(BigInt::zero(), p.clone()),
    }
}

pub(super) fn rank_over_field<C: FieldCoeff>(
    cols: &[Vec<C>],
    num_rows: usize,
    zero: &C,
) -> Result<usize, AlgebraError> {
    if cols.is_empty() || num_rows == 0 {
        return Ok(0);
    }
    let rref = rref_field(cols, num_rows, zero)?;
    Ok(rref.rank)
}
