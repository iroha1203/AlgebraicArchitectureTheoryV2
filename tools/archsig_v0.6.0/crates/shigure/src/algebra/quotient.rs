//! 商環上の ideal 所属判定（G-141 D5 の有限層別、AC5(a)）。
//!
//! 状態変数 `y` とパラメータ変数 `c` の多項式環 `Q[c, y]` において、
//! 状態 ideal への所属条件を ambient 多項式零へ暗黙に強めず、
//! 先頭 `y` 係数の零化／可逆分岐によって局所閉層 `⋃ (V(eqs) ∩ D(invs))` を計算する。

use crate::algebra::MonomialOrder;
use crate::algebra::groebner::{GroebnerBasis, rabinowitsch_solve};
use crate::algebra::poly::{AlgebraError, Monomial, Poly, VarOrder};
use crate::algebra::scalar::Rat;
use crate::ir::result::SilenceReason;
use std::collections::BTreeMap;

/// 層別分岐の安全上限（超過時は誤判定せず `SilenceReason::QuotientIdealOutOfScope` を返す）。
pub const DEFAULT_MAX_QUOTIENT_BRANCHES: usize = 64;
/// 単一枝上の `y` 方向 Gröbner 補完における S-pair 処理上限。
pub const DEFAULT_MAX_QUOTIENT_Y_PAIRS: usize = 256;

/// 商環上の ideal 所属が成立する局所閉層 `V(equations) ∩ D(invertibles)`（G-141 D5）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuotientStratum {
    pub equations: Vec<Poly<Rat>>,
    pub invertibles: Vec<Poly<Rat>>,
}

/// 状態単項式ごとのパラメータ多項式係数 `sum_alpha c_alpha(c) * y^alpha`。
type StatePoly = BTreeMap<Monomial, Poly<Rat>>;

/// 商環上の ideal 所属判定（G-141 D5 有限層別、AC5(a)）。
///
/// 変数順序は先頭 `state_count` 個が状態変数 `y`、残りが `param_vars` の変数 `c` であるとする。
pub fn quotient_membership_locus(
    target: &Poly<Rat>,
    source_ideal: &[Poly<Rat>],
    state_count: usize,
    param_vars: &VarOrder,
) -> Result<Vec<QuotientStratum>, SilenceReason> {
    let total_vars = state_count + param_vars.len();
    if target.num_vars() != total_vars || source_ideal.iter().any(|g| g.num_vars() != total_vars) {
        return Err(SilenceReason::QuotientIdealOutOfScope {
            detail: "variable count mismatch between state/parameter ring and quotient polynomials"
                .to_owned(),
        });
    }

    let mut strata = Vec::new();
    let mut visited_branches = 0usize;
    let target_y = split_to_state_poly(target, state_count, param_vars.len());
    let gens_y: Vec<StatePoly> = source_ideal
        .iter()
        .map(|g| split_to_state_poly(g, state_count, param_vars.len()))
        .collect();

    stratify_quotient_branch(
        &target_y,
        &gens_y,
        vec![],
        vec![],
        param_vars,
        &mut strata,
        &mut visited_branches,
    )?;

    Ok(strata)
}

fn split_to_state_poly(poly: &Poly<Rat>, state_count: usize, param_count: usize) -> StatePoly {
    let mut out: StatePoly = BTreeMap::new();
    for (mono, coeff) in poly.terms() {
        let y_mono = Monomial::from_exps(mono.exps()[..state_count].to_vec());
        let c_mono = Monomial::from_exps(mono.exps()[state_count..].to_vec());
        let entry = out
            .entry(y_mono)
            .or_insert_with(|| Poly::zero(param_count, Rat::zero()));
        entry.add_term(c_mono, coeff.clone());
    }
    out.retain(|_, c| !c.is_zero());
    out
}

fn reduce_state_poly(sp: &StatePoly, param_gb: &GroebnerBasis) -> Result<StatePoly, AlgebraError> {
    let mut out = BTreeMap::new();
    for (y_mono, c_poly) in sp {
        let red = param_gb.normal_form(c_poly)?;
        if !red.is_zero() {
            out.insert(y_mono.clone(), red);
        }
    }
    Ok(out)
}

fn leading_state_term(sp: &StatePoly) -> Option<(&Monomial, &Poly<Rat>)> {
    sp.iter()
        .max_by(|(m1, _), (m2, _)| m1.cmp_order(m2, MonomialOrder::Grevlex))
}

fn state_poly_scale(sp: &StatePoly, factor: &Poly<Rat>) -> StatePoly {
    if factor.is_zero() {
        return BTreeMap::new();
    }
    let mut out = BTreeMap::new();
    for (m, c) in sp {
        let prod = c.mul(factor);
        if !prod.is_zero() {
            out.insert(m.clone(), prod);
        }
    }
    out
}

fn state_poly_sub_mul(
    lhs: &StatePoly,
    rhs: &StatePoly,
    y_shift: &Monomial,
    c_factor: &Poly<Rat>,
    param_count: usize,
) -> StatePoly {
    let mut out = lhs.clone();
    if c_factor.is_zero() {
        return out;
    }
    for (m, c) in rhs {
        let shifted = m.mul(y_shift);
        let sub_val = c.mul(c_factor);
        let entry = out
            .entry(shifted)
            .or_insert_with(|| Poly::zero(param_count, Rat::zero()));
        *entry = entry.sub(&sub_val);
    }
    out.retain(|_, c| !c.is_zero());
    out
}

/// 現在の枝上で多項式 `p(c)` が零になり得るか（`V(eqs, p) ∩ D(invs)` が非空か）を判定する。
fn can_vanish_on_branch(
    p: &Poly<Rat>,
    eqs: &[Poly<Rat>],
    invs: &[Poly<Rat>],
    param_vars: &VarOrder,
) -> Result<bool, AlgebraError> {
    if p.is_constant() {
        return Ok(p.is_zero());
    }
    let mut with_p = eqs.to_vec();
    with_p.push(p.clone());
    let rab = rabinowitsch_solve(&with_p, invs, param_vars)?;
    Ok(!rab.is_empty_over_closure)
}

fn map_out_of_scope(e: AlgebraError) -> SilenceReason {
    SilenceReason::QuotientIdealOutOfScope {
        detail: e.to_string(),
    }
}

fn stratify_quotient_branch(
    target: &StatePoly,
    gens: &[StatePoly],
    eqs: Vec<Poly<Rat>>,
    invs: Vec<Poly<Rat>>,
    param_vars: &VarOrder,
    out: &mut Vec<QuotientStratum>,
    visited: &mut usize,
) -> Result<(), SilenceReason> {
    *visited += 1;
    if *visited > DEFAULT_MAX_QUOTIENT_BRANCHES {
        return Err(SilenceReason::QuotientIdealOutOfScope {
            detail: format!(
                "parametric quotient stratification exceeded branch limit ({DEFAULT_MAX_QUOTIENT_BRANCHES})"
            ),
        });
    }

    let rab = rabinowitsch_solve(&eqs, &invs, param_vars).map_err(map_out_of_scope)?;
    if rab.is_empty_over_closure {
        return Ok(());
    }
    let clean_eqs = rab.parameter_equations;
    let param_gb = GroebnerBasis::compute(&clean_eqs, param_vars.clone(), MonomialOrder::Grevlex)
        .map_err(map_out_of_scope)?;

    let red_target = reduce_state_poly(target, &param_gb).map_err(map_out_of_scope)?;
    let mut red_gens: Vec<StatePoly> = Vec::new();
    for g in gens {
        let rg = reduce_state_poly(g, &param_gb).map_err(map_out_of_scope)?;
        if !rg.is_empty() {
            red_gens.push(rg);
        }
    }

    if red_target.is_empty() {
        out.push(QuotientStratum {
            equations: clean_eqs,
            invertibles: invs,
        });
        return Ok(());
    }

    if red_gens.is_empty() {
        let mut final_eqs = clean_eqs;
        final_eqs.extend(red_target.into_values());
        let final_rab =
            rabinowitsch_solve(&final_eqs, &invs, param_vars).map_err(map_out_of_scope)?;
        if !final_rab.is_empty_over_closure {
            out.push(QuotientStratum {
                equations: final_rab.parameter_equations,
                invertibles: invs,
            });
        }
        return Ok(());
    }

    // 先頭 y 係数がこの枝上で消え得る生成元があれば、閉枝 V(lc) と開枝 D(lc) に分岐する。
    for g in &red_gens {
        if let Some((_, lc)) = leading_state_term(g)
            && can_vanish_on_branch(lc, &clean_eqs, &invs, param_vars).map_err(map_out_of_scope)?
        {
            let mut closed_eqs = clean_eqs.clone();
            closed_eqs.push(lc.clone());
            stratify_quotient_branch(
                &red_target,
                &red_gens,
                closed_eqs,
                invs.clone(),
                param_vars,
                out,
                visited,
            )?;
            let mut open_invs = invs;
            open_invs.push(lc.clone());
            return stratify_quotient_branch(
                &red_target,
                &red_gens,
                clean_eqs,
                open_invs,
                param_vars,
                out,
                visited,
            );
        }
    }

    // 全生成元の先頭 y 係数がこの枝上で可逆。y 方向の S 多項式補完を行う。
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for i in 0..red_gens.len() {
        for j in (i + 1)..red_gens.len() {
            pairs.push((i, j));
        }
    }
    let mut pair_steps = 0usize;
    while let Some((i, j)) = pairs.pop() {
        pair_steps += 1;
        if pair_steps > DEFAULT_MAX_QUOTIENT_Y_PAIRS {
            return Err(SilenceReason::QuotientIdealOutOfScope {
                detail: format!(
                    "parametric y-Groebner completion exceeded pair limit ({DEFAULT_MAX_QUOTIENT_Y_PAIRS})"
                ),
            });
        }
        let Some((lm_i, lc_i)) = leading_state_term(&red_gens[i]) else {
            continue;
        };
        let Some((lm_j, lc_j)) = leading_state_term(&red_gens[j]) else {
            continue;
        };
        if lm_i.gcd_is_one(lm_j) {
            continue;
        }
        let lcm = lm_i.lcm(lm_j);
        let shift_i = lcm.div_exact(lm_i).expect("lcm divisible by lm_i");
        let shift_j = lcm.div_exact(lm_j).expect("lcm divisible by lm_j");
        let s_lhs = state_poly_sub_mul(
            &BTreeMap::new(),
            &red_gens[i],
            &shift_i,
            &lc_j.neg(),
            param_vars.len(),
        );
        let s_raw = state_poly_sub_mul(&s_lhs, &red_gens[j], &shift_j, lc_i, param_vars.len());
        let s_red = pseudo_reduce_state_poly(&s_raw, &red_gens, &param_gb, param_vars.len())
            .map_err(map_out_of_scope)?;
        if !s_red.is_empty() {
            if let Some((_, new_lc_ref)) = leading_state_term(&s_red) {
                let new_lc = new_lc_ref.clone();
                if can_vanish_on_branch(&new_lc, &clean_eqs, &invs, param_vars)
                    .map_err(map_out_of_scope)?
                {
                    red_gens.push(s_red);
                    let mut closed_eqs = clean_eqs.clone();
                    closed_eqs.push(new_lc.clone());
                    stratify_quotient_branch(
                        &red_target,
                        &red_gens,
                        closed_eqs,
                        invs.clone(),
                        param_vars,
                        out,
                        visited,
                    )?;
                    let mut open_invs = invs;
                    open_invs.push(new_lc);
                    return stratify_quotient_branch(
                        &red_target,
                        &red_gens,
                        clean_eqs,
                        open_invs,
                        param_vars,
                        out,
                        visited,
                    );
                }
            }
            let new_idx = red_gens.len();
            for prev in 0..new_idx {
                pairs.push((prev, new_idx));
            }
            red_gens.push(s_red);
        }
    }

    // 完成した y-Gröbner 基底で target を疑似簡約し、残った全 y 単項式係数を 0 に等置する。
    let rem = pseudo_reduce_state_poly(&red_target, &red_gens, &param_gb, param_vars.len())
        .map_err(map_out_of_scope)?;
    let mut final_eqs = clean_eqs;
    final_eqs.extend(rem.into_values());
    let final_rab = rabinowitsch_solve(&final_eqs, &invs, param_vars).map_err(map_out_of_scope)?;
    if !final_rab.is_empty_over_closure {
        out.push(QuotientStratum {
            equations: final_rab.parameter_equations,
            invertibles: invs,
        });
    }
    Ok(())
}

fn pseudo_reduce_state_poly(
    target: &StatePoly,
    basis: &[StatePoly],
    param_gb: &GroebnerBasis,
    param_count: usize,
) -> Result<StatePoly, AlgebraError> {
    let mut cur = reduce_state_poly(target, param_gb)?;
    let mut rem = BTreeMap::new();
    while let Some((lm_cur, lc_cur)) = leading_state_term(&cur) {
        let lm_cur = lm_cur.clone();
        let lc_cur = lc_cur.clone();
        let mut divided = false;
        for g in basis {
            if let Some((lm_g, lc_g)) = leading_state_term(g)
                && let Some(shift) = lm_cur.div_exact(lm_g)
            {
                let scaled = state_poly_scale(&cur, lc_g);
                let next = state_poly_sub_mul(&scaled, g, &shift, &lc_cur, param_count);
                cur = reduce_state_poly(&next, param_gb)?;
                // 不変条件 `u * target ≡ cur + rem (mod basis)` を保つため、
                // `cur` を `lc_g` 倍したときは退避済みの `rem` も同じ単元 `lc_g` 倍する。
                if !rem.is_empty() {
                    rem = reduce_state_poly(&state_poly_scale(&rem, lc_g), param_gb)?;
                }
                divided = true;
                break;
            }
        }
        if !divided {
            cur.remove(&lm_cur);
            rem.insert(lm_cur, lc_cur);
        }
    }
    Ok(rem)
}
