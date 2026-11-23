//! 構成可能集合の射影による正確な構成可能像の計算（G-141 D6）。
//!
//! 消去 ideal による Zariski 閉包ではなく、パラメータ空間上の先頭係数零化／可逆分岐による
//! Gröbner 層別を用いて `v: X -> C` の実像 `⋃_i (V(I_i) ∩ D(g_i))` を計算する。

use crate::algebra::MonomialOrder;
use crate::algebra::constructible::{
    ConstructibleSet, LocallyClosedStratum, map_constructible_silence,
};
use crate::algebra::groebner::{GroebnerBasis, rabinowitsch_solve};
use crate::algebra::poly::{AlgebraError, Monomial, Poly, VarOrder};
use crate::algebra::scalar::Rat;
use crate::ir::result::SilenceReason;
use std::collections::BTreeMap;

/// 射影層別分岐の安全上限（超過時は誤判定せず沈黙する）。
pub const DEFAULT_MAX_IMAGE_BRANCHES: usize = 64;
/// 単一枝上の fiber 方向 Gröbner 補完における S-pair 処理上限。
pub const DEFAULT_MAX_IMAGE_Y_PAIRS: usize = 256;

/// fiber 単項式ごとのパラメータ多項式係数 `sum_alpha c_alpha(c) * y^alpha`。
type FiberPoly = BTreeMap<Monomial, Poly<Rat>>;

/// 変数順序 `[fiber_vars..., param_vars...]` を持つ単一局所閉層を `param_vars` へ射影した
/// 正確な構成可能像（G-141 D6）を計算する。
pub fn project_stratum_image(
    stratum: &LocallyClosedStratum,
    fiber_var_count: usize,
    param_vars: &VarOrder,
) -> Result<ConstructibleSet, SilenceReason> {
    let total_vars = fiber_var_count + param_vars.len();
    for p in stratum.equations.iter().chain(&stratum.invertibles) {
        if p.num_vars() != total_vars {
            return Err(SilenceReason::ConstructibleStratificationOutOfScope {
                detail: format!(
                    "projection stratum arity mismatch: expected {total_vars}, got {}",
                    p.num_vars()
                ),
            });
        }
    }

    if fiber_var_count == 0 {
        return ConstructibleSet::from_strata(param_vars.clone(), vec![stratum.clone()]);
    }

    let mut base_eqs: Vec<Poly<Rat>> = Vec::new();
    let mut base_invs: Vec<Poly<Rat>> = Vec::new();
    let mut fiber_eqs: Vec<Poly<Rat>> = Vec::new();
    let mut fiber_invs: Vec<Poly<Rat>> = Vec::new();

    for eq in &stratum.equations {
        if eq.is_zero() {
            continue;
        }
        if let Some(param_only) = eq.drop_prefix_vars(fiber_var_count) {
            base_eqs.push(param_only);
        } else {
            fiber_eqs.push(eq.clone());
        }
    }
    for inv in &stratum.invertibles {
        if inv.is_zero() {
            return Ok(ConstructibleSet::empty(param_vars.clone()));
        }
        if let Some(param_only) = inv.drop_prefix_vars(fiber_var_count) {
            base_invs.push(param_only);
        } else {
            fiber_invs.push(inv.clone());
        }
    }

    // fiber 変数に依存する可逆条件 D(g(y, c)) は補助 fiber 変数 u_j と u_j * g(y, c) - 1 = 0 で保持する。
    let aux_count = fiber_invs.len();
    let ext_fiber_count = aux_count + fiber_var_count;
    let ext_total_vars = ext_fiber_count + param_vars.len();
    let mut gens: Vec<FiberPoly> = Vec::with_capacity(fiber_eqs.len() + aux_count);

    for eq in &fiber_eqs {
        let lifted = eq.lift_vars(aux_count);
        let fp = split_to_fiber_poly(&lifted, ext_fiber_count, param_vars.len());
        if !fp.is_empty() {
            gens.push(fp);
        }
    }
    let one = Poly::one(ext_total_vars, Rat::zero());
    for (j, g) in fiber_invs.iter().enumerate() {
        let u_j = Poly::var(ext_total_vars, j, Rat::zero());
        let g_lifted = g.lift_vars(aux_count);
        let rab_eq = u_j
            .checked_mul(&g_lifted)
            .map_err(map_constructible_silence)?
            .sub(&one);
        let fp = split_to_fiber_poly(&rab_eq, ext_fiber_count, param_vars.len());
        if !fp.is_empty() {
            gens.push(fp);
        }
    }

    let mut strata = Vec::new();
    let mut visited_branches = 0usize;
    stratify_projection_branch(
        &gens,
        base_eqs,
        base_invs,
        param_vars,
        &mut strata,
        &mut visited_branches,
    )?;

    ConstructibleSet::from_strata(param_vars.clone(), strata)
}

/// 構成可能集合全体を `param_vars` へ射影した正確な構成可能像（各層の射影の和集合）を計算する。
pub fn project_constructible_set(
    set: &ConstructibleSet,
    fiber_var_count: usize,
    param_vars: &VarOrder,
) -> Result<ConstructibleSet, SilenceReason> {
    let expected = fiber_var_count + param_vars.len();
    if set.vars().len() != expected {
        return Err(SilenceReason::ConstructibleStratificationOutOfScope {
            detail: format!(
                "projection set variable count mismatch: expected {expected}, got {}",
                set.vars().len()
            ),
        });
    }
    let mut acc = ConstructibleSet::empty(param_vars.clone());
    for st in set.strata() {
        let img = project_stratum_image(st, fiber_var_count, param_vars)?;
        acc = acc.union(&img)?;
    }
    Ok(acc)
}

fn split_to_fiber_poly(poly: &Poly<Rat>, fiber_var_count: usize, param_count: usize) -> FiberPoly {
    let mut out: FiberPoly = BTreeMap::new();
    for (mono, coeff) in poly.terms() {
        let y_mono = Monomial::from_exps(mono.exps()[..fiber_var_count].to_vec());
        let c_mono = Monomial::from_exps(mono.exps()[fiber_var_count..].to_vec());
        let entry = out
            .entry(y_mono)
            .or_insert_with(|| Poly::zero(param_count, Rat::zero()));
        entry.add_term(c_mono, coeff.clone());
    }
    out.retain(|_, c| !c.is_zero());
    out
}

fn reduce_fiber_poly(sp: &FiberPoly, param_gb: &GroebnerBasis) -> Result<FiberPoly, AlgebraError> {
    let mut out = BTreeMap::new();
    for (y_mono, c_poly) in sp {
        let red = param_gb.normal_form(c_poly)?;
        if !red.is_zero() {
            out.insert(y_mono.clone(), red);
        }
    }
    Ok(out)
}

fn leading_fiber_term(sp: &FiberPoly) -> Option<(&Monomial, &Poly<Rat>)> {
    sp.iter()
        .max_by(|(m1, _), (m2, _)| m1.cmp_order(m2, MonomialOrder::Grevlex))
}

fn fiber_poly_scale(sp: &FiberPoly, factor: &Poly<Rat>) -> Result<FiberPoly, AlgebraError> {
    if factor.is_zero() {
        return Ok(BTreeMap::new());
    }
    let mut out = BTreeMap::new();
    for (m, c) in sp {
        let prod = c.checked_mul(factor)?;
        if !prod.is_zero() {
            out.insert(m.clone(), prod);
        }
    }
    Ok(out)
}

fn fiber_poly_sub_mul(
    lhs: &FiberPoly,
    rhs: &FiberPoly,
    y_shift: &Monomial,
    c_factor: &Poly<Rat>,
    param_count: usize,
) -> Result<FiberPoly, AlgebraError> {
    let mut out = lhs.clone();
    if c_factor.is_zero() {
        return Ok(out);
    }
    for (m, c) in rhs {
        let shifted = m
            .checked_mul(y_shift)
            .ok_or_else(|| AlgebraError::OutOfScope {
                detail: "fiber monomial exponent addition overflowed u32".to_owned(),
            })?;
        let sub_val = c.checked_mul(c_factor)?;
        let entry = out
            .entry(shifted)
            .or_insert_with(|| Poly::zero(param_count, Rat::zero()));
        *entry = entry.sub(&sub_val);
    }
    out.retain(|_, c| !c.is_zero());
    Ok(out)
}

fn can_vanish_on_branch(
    p: &Poly<Rat>,
    eqs: &[Poly<Rat>],
    invs: &[Poly<Rat>],
    param_vars: &VarOrder,
) -> Result<bool, SilenceReason> {
    if p.is_constant() {
        return Ok(p.is_zero());
    }
    let mut with_p = eqs.to_vec();
    with_p.push(p.clone());
    let rab = rabinowitsch_solve(&with_p, invs, param_vars).map_err(map_constructible_silence)?;
    Ok(!rab.is_empty_over_closure)
}

fn can_be_nonzero_on_branch(
    p: &Poly<Rat>,
    eqs: &[Poly<Rat>],
    invs: &[Poly<Rat>],
    param_vars: &VarOrder,
) -> Result<bool, SilenceReason> {
    if p.is_constant() {
        return Ok(!p.is_zero());
    }
    let mut with_inv = invs.to_vec();
    with_inv.push(p.clone());
    let rab = rabinowitsch_solve(eqs, &with_inv, param_vars).map_err(map_constructible_silence)?;
    Ok(!rab.is_empty_over_closure)
}

fn stratify_projection_branch(
    gens: &[FiberPoly],
    eqs: Vec<Poly<Rat>>,
    invs: Vec<Poly<Rat>>,
    param_vars: &VarOrder,
    out: &mut Vec<LocallyClosedStratum>,
    visited: &mut usize,
) -> Result<(), SilenceReason> {
    *visited += 1;
    if *visited > DEFAULT_MAX_IMAGE_BRANCHES {
        return Err(SilenceReason::ConstructibleStratificationOutOfScope {
            detail: format!(
                "constructible projection stratification exceeded branch limit ({DEFAULT_MAX_IMAGE_BRANCHES})"
            ),
        });
    }

    let rab = rabinowitsch_solve(&eqs, &invs, param_vars).map_err(map_constructible_silence)?;
    if rab.is_empty_over_closure {
        return Ok(());
    }
    let clean_eqs = rab.parameter_equations;
    let param_gb = GroebnerBasis::compute(&clean_eqs, param_vars.clone(), MonomialOrder::Grevlex)
        .map_err(map_constructible_silence)?;

    let mut red_gens: Vec<FiberPoly> = Vec::new();
    let mut pure_param_eqs: Vec<Poly<Rat>> = Vec::new();
    for g in gens {
        let rg = reduce_fiber_poly(g, &param_gb).map_err(map_constructible_silence)?;
        if rg.is_empty() {
            continue;
        }
        if let Some((lm, c_poly)) = leading_fiber_term(&rg)
            && lm.is_one()
        {
            pure_param_eqs.push(c_poly.clone());
        } else {
            red_gens.push(rg);
        }
    }

    // fiber 変数を含まない純粋なパラメータ制約 c_poly(c) = 0 が生じた場合は即座にパラメータ理想へ移す。
    if !pure_param_eqs.is_empty() {
        for cp in &pure_param_eqs {
            if !can_vanish_on_branch(cp, &clean_eqs, &invs, param_vars)? {
                return Ok(());
            }
        }
        let mut next_eqs = clean_eqs;
        next_eqs.extend(pure_param_eqs);
        return stratify_projection_branch(&red_gens, next_eqs, invs, param_vars, out, visited);
    }

    if red_gens.is_empty() {
        out.push(LocallyClosedStratum {
            equations: clean_eqs,
            invertibles: invs,
        });
        return Ok(());
    }

    // 先頭 fiber 係数が枝上で消え得るなら分岐する（非 reduced 理想で全域零なら閉枝のみへ進む）。
    for g in &red_gens {
        if let Some((_, lc)) = leading_fiber_term(g)
            && can_vanish_on_branch(lc, &clean_eqs, &invs, param_vars)?
        {
            let mut closed_eqs = clean_eqs.clone();
            closed_eqs.push(lc.clone());
            stratify_projection_branch(
                &red_gens,
                closed_eqs,
                invs.clone(),
                param_vars,
                out,
                visited,
            )?;
            if can_be_nonzero_on_branch(lc, &clean_eqs, &invs, param_vars)? {
                let mut open_invs = invs;
                open_invs.push(lc.clone());
                return stratify_projection_branch(
                    &red_gens, clean_eqs, open_invs, param_vars, out, visited,
                );
            }
            return Ok(());
        }
    }

    // 全生成元の先頭係数がこの枝上の全幾何点で可逆。fiber 方向の S 多項式補完を実行する。
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for i in 0..red_gens.len() {
        for j in (i + 1)..red_gens.len() {
            pairs.push((i, j));
        }
    }
    let mut pair_steps = 0usize;
    while let Some((i, j)) = pairs.pop() {
        pair_steps += 1;
        if pair_steps > DEFAULT_MAX_IMAGE_Y_PAIRS {
            return Err(SilenceReason::ConstructibleStratificationOutOfScope {
                detail: format!(
                    "constructible projection fiber S-pair computation exceeded limit ({DEFAULT_MAX_IMAGE_Y_PAIRS})"
                ),
            });
        }
        let Some((lm_i, lc_i)) = leading_fiber_term(&red_gens[i]) else {
            continue;
        };
        let Some((lm_j, lc_j)) = leading_fiber_term(&red_gens[j]) else {
            continue;
        };
        if lm_i.gcd_is_one(lm_j) {
            continue;
        }
        let lcm = lm_i.lcm(lm_j);
        let shift_i = lcm.div_exact(lm_i).expect("lcm divisible by lm_i");
        let shift_j = lcm.div_exact(lm_j).expect("lcm divisible by lm_j");
        let s_lhs = fiber_poly_sub_mul(
            &BTreeMap::new(),
            &red_gens[i],
            &shift_i,
            &lc_j.neg(),
            param_vars.len(),
        )
        .map_err(map_constructible_silence)?;
        let s_raw = fiber_poly_sub_mul(&s_lhs, &red_gens[j], &shift_j, lc_i, param_vars.len())
            .map_err(map_constructible_silence)?;
        let s_red = pseudo_reduce_fiber_poly(&s_raw, &red_gens, &param_gb, param_vars.len())
            .map_err(map_constructible_silence)?;

        if let Some((new_lm, new_lc_ref)) = leading_fiber_term(&s_red) {
            let new_lc = new_lc_ref.clone();
            if new_lm.is_one() {
                if can_vanish_on_branch(&new_lc, &clean_eqs, &invs, param_vars)? {
                    let mut closed_eqs = clean_eqs;
                    closed_eqs.push(new_lc);
                    return stratify_projection_branch(
                        &red_gens, closed_eqs, invs, param_vars, out, visited,
                    );
                }
                return Ok(());
            }
            if can_vanish_on_branch(&new_lc, &clean_eqs, &invs, param_vars)? {
                let can_nz = can_be_nonzero_on_branch(&new_lc, &clean_eqs, &invs, param_vars)?;
                red_gens.push(s_red);
                let mut closed_eqs = clean_eqs.clone();
                closed_eqs.push(new_lc.clone());
                stratify_projection_branch(
                    &red_gens,
                    closed_eqs,
                    invs.clone(),
                    param_vars,
                    out,
                    visited,
                )?;
                if can_nz {
                    let mut open_invs = invs;
                    open_invs.push(new_lc);
                    return stratify_projection_branch(
                        &red_gens, clean_eqs, open_invs, param_vars, out, visited,
                    );
                }
                return Ok(());
            }
            let new_idx = red_gens.len();
            for prev in 0..new_idx {
                pairs.push((prev, new_idx));
            }
            red_gens.push(s_red);
        }
    }

    // どの生成元も先頭単項式 1 を持たないため、この枝上の全幾何点で fiber は非空。
    out.push(LocallyClosedStratum {
        equations: clean_eqs,
        invertibles: invs,
    });
    Ok(())
}

fn pseudo_reduce_fiber_poly(
    target: &FiberPoly,
    basis: &[FiberPoly],
    param_gb: &GroebnerBasis,
    param_count: usize,
) -> Result<FiberPoly, AlgebraError> {
    let mut cur = reduce_fiber_poly(target, param_gb)?;
    let mut rem = BTreeMap::new();
    while let Some((lm_cur, lc_cur)) = leading_fiber_term(&cur) {
        let lm_cur = lm_cur.clone();
        let lc_cur = lc_cur.clone();
        let mut divided = false;
        for g in basis {
            if let Some((lm_g, lc_g)) = leading_fiber_term(g)
                && let Some(shift) = lm_cur.div_exact(lm_g)
            {
                let scaled = fiber_poly_scale(&cur, lc_g)?;
                let next = fiber_poly_sub_mul(&scaled, g, &shift, &lc_cur, param_count)?;
                cur = reduce_fiber_poly(&next, param_gb)?;
                if !rem.is_empty() {
                    rem = reduce_fiber_poly(&fiber_poly_scale(&rem, lc_g)?, param_gb)?;
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
