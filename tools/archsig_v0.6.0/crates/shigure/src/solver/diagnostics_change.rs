//! 診断係数変更 $\Lambda \to \Lambda'$（固定 label tensor vs 値域再生成・
//! flat / faithfully flat 判定・一般整数 2 項複体の比較、G-142 A2–A3・W1）。

use crate::algebra::cochain::{CochainComplex, CohomologyGroup};
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::ir::diagnostics::{CoeffChangeComparisonSpec, ExplicitZComplexSpec};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, SilenceReason};
use crate::ir::result_phase4::{CoeffChangeResult, ExplicitComplexChangeResult};
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::solver::diagnostics::{
    ComputedNerve, DiagnosticComplexData, build_diagnostic_complex, evaluate_complex_over_domain,
    lift_mat_z_to_fp, lift_mat_z_to_q, map_diag_alg_err,
};
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};

/// 係数環射 `source -> target` の存在・flat 性・faithfully flat 性を判定する（G-142 A3）。
fn classify_ring_hom(
    source: &CoeffDomain,
    target: &CoeffDomain,
) -> Result<(bool, bool), SilenceReason> {
    if let CoeffDomain::Fp(p) = target
        && !archsig_common::prime::is_prime(p)
    {
        return Err(SilenceReason::UnsupportedCoeffRing {
            domain: target.clone(),
            detail: format!("target modulus {p} is not prime"),
        });
    }
    match (source, target) {
        (CoeffDomain::Z, CoeffDomain::Z) | (CoeffDomain::Q, CoeffDomain::Q) => Ok((true, true)),
        (CoeffDomain::Fp(p), CoeffDomain::Fp(q)) if p == q => Ok((true, true)),
        // 局所化 Z -> Q は flat だが faithfully flat ではない（torsion を消す、W1）。
        (CoeffDomain::Z, CoeffDomain::Q) => Ok((true, false)),
        // 商環射 Z -> F_p は非 flat かつ非 faithfully flat（W1）。
        (CoeffDomain::Z, CoeffDomain::Fp(_)) => Ok((false, false)),
        _ => Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "ring_homomorphism_exists".to_owned(),
            detail: format!("no canonical ring homomorphism from {source} to {target}"),
        }),
    }
}

/// 係数変更比較（固定 label tensor・値域再生成・任意明示 Z 複体）を計算する。
pub(crate) fn compute_coeff_change(
    source_domain: &CoeffDomain,
    cc: &CoeffChangeComparisonSpec,
    nerve: &ComputedNerve,
    fixed_complex: &DiagnosticComplexData,
    target_law_lits: Option<&BTreeMap<String, BTreeMap<String, ScalarLit>>>,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<CoeffChangeResult, SilenceReason> {
    let (is_flat, is_faithfully_flat) = classify_ring_hom(source_domain, &cc.target_domain)?;
    checks.push(ApplicabilityCheck::passed(
        "coeff_change_ring_hom_valid",
        MathClause::G142A3,
    ));

    // A2: 固定 label のまま対象環へ tensor した複体。
    let fixed_target = evaluate_complex_over_domain(fixed_complex, &cc.target_domain)?;

    // W1: 値域再生成との比較（Static readout のみ。多項式族では幾何基底変更として別管理）。
    let (regenerated_c0_dim, regenerated_h0_summary, regenerated_h1_summary, label_collision_map) =
        if cc.compare_codomain_regeneration {
            let Some(lits) = target_law_lits else {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "codomain_regeneration_requires_static_readout".to_owned(),
                    detail: "codomain regeneration comparison requires Static readout".to_owned(),
                });
            };
            let regen_values = regenerate_law_values(lits, &cc.target_domain)?;
            let regen_complex = build_diagnostic_complex(nerve, &regen_values);
            let regen_sum = evaluate_complex_over_domain(&regen_complex, &cc.target_domain)?;
            let map_desc = describe_label_collision_map(
                fixed_complex,
                &regen_complex,
                lits,
                &cc.target_domain,
            )?;
            (
                Some(regen_complex.coords0.len()),
                Some(regen_sum.h0_summary),
                Some(regen_sum.h1_summary),
                Some(map_desc),
            )
        } else {
            (None, None, None, None)
        };

    let explicit_complex_check = if let Some(ex) = &cc.explicit_z_complex {
        if !matches!(source_domain, CoeffDomain::Z) {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "explicit_z_complex_requires_z_source".to_owned(),
                detail: format!(
                    "explicit_z_complex requires diagnostic_coeff = Z, got `{source_domain}`"
                ),
            });
        }
        Some(check_explicit_z_complex(ex, &cc.target_domain)?)
    } else {
        None
    };

    Ok(CoeffChangeResult {
        source_domain: source_domain.to_string(),
        target_domain: cc.target_domain.to_string(),
        is_flat,
        is_faithfully_flat,
        fixed_label_c0_dim: fixed_complex.coords0.len(),
        fixed_label_h0_summary: fixed_target.h0_summary,
        fixed_label_h1_summary: fixed_target.h1_summary,
        regenerated_c0_dim,
        regenerated_h0_summary,
        regenerated_h1_summary,
        label_collision_map_description: label_collision_map,
        explicit_complex_check,
    })
}

fn map_scalar_lit_to_domain(
    lit: &ScalarLit,
    target: &CoeffDomain,
) -> Result<String, SilenceReason> {
    match (lit, target) {
        (ScalarLit::Z(n), CoeffDomain::Z) => Ok(n.to_string()),
        (ScalarLit::Z(n), CoeffDomain::Q) => Ok(n.to_string()),
        (ScalarLit::Z(n), CoeffDomain::Fp(p)) => {
            let elem = FpElem::from_checked_prime(n.clone(), p.clone());
            Ok(elem.to_string())
        }
        (ScalarLit::Q { num, den }, CoeffDomain::Q) => Ok(ScalarLit::Q {
            num: num.clone(),
            den: den.clone(),
        }
        .to_string()),
        (ScalarLit::Q { num, den }, CoeffDomain::Fp(p)) => {
            let p_int = BigInt::from(p.clone());
            if (den % &p_int).is_zero() {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "codomain_regeneration_reduction".to_owned(),
                    detail: format!("denominator {den} is not invertible mod {p}"),
                });
            }
            let num_fp = FpElem::from_checked_prime(num.clone(), p.clone());
            let den_fp = FpElem::from_checked_prime(den.clone(), p.clone());
            let inv = den_fp
                .inv()
                .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                    condition: "codomain_regeneration_reduction".to_owned(),
                    detail: format!("denominator {den} has no inverse mod {p}"),
                })?;
            Ok(num_fp.mul_ref(&inv).to_string())
        }
        (ScalarLit::Fp { value, modulus }, CoeffDomain::Fp(p)) if modulus == p => {
            Ok(value.to_string())
        }
        _ => Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "codomain_regeneration_ring_hom".to_owned(),
            detail: format!(
                "cannot map value `{lit}` (domain {}) into target domain {target}",
                lit.domain()
            ),
        }),
    }
}

fn regenerate_law_values(
    lits: &BTreeMap<String, BTreeMap<String, ScalarLit>>,
    target: &CoeffDomain,
) -> Result<BTreeMap<String, BTreeMap<String, String>>, SilenceReason> {
    let mut out = BTreeMap::new();
    for (law, m) in lits {
        let mut inner = BTreeMap::new();
        for (tgt, lit) in m {
            inner.insert(tgt.clone(), map_scalar_lit_to_domain(lit, target)?);
        }
        out.insert(law.clone(), inner);
    }
    Ok(out)
}

/// 値域再生成後の座標から固定 label 座標への単射比較写像を一般構成から記述する（W1: 例 `a -> (a, a)`）。
fn describe_label_collision_map(
    fixed: &DiagnosticComplexData,
    regen: &DiagnosticComplexData,
    lits: &BTreeMap<String, BTreeMap<String, ScalarLit>>,
    target: &CoeffDomain,
) -> Result<String, SilenceReason> {
    // 各 `(law, fixed_val_str)` が再生成後にどの `regen_val_str` へ写るかを記録する。
    let mut fixed_to_regen: BTreeMap<(String, String), String> = BTreeMap::new();
    for (law, m) in lits {
        for lit in m.values() {
            let r = map_scalar_lit_to_domain(lit, target)?;
            fixed_to_regen.insert((law.clone(), lit.to_string()), r);
        }
    }

    // 0-cochain 座標で、各再生成座標がいくつの固定座標へ複製されるかを計算する。
    let mut regen_images: Vec<Vec<usize>> = vec![Vec::new(); regen.coords0.len()];
    let mut regen_idx: BTreeMap<(usize, String, String), usize> = BTreeMap::new();
    for (ri, key) in regen.coords0.iter().enumerate() {
        regen_idx.insert(key.clone(), ri);
    }
    for (fi, (ci, law, fval)) in fixed.coords0.iter().enumerate() {
        if let Some(rval) = fixed_to_regen.get(&(law.clone(), fval.clone()))
            && let Some(&ri) = regen_idx.get(&(*ci, law.clone(), rval.clone()))
        {
            regen_images[ri].push(fi);
        }
    }

    if regen.coords0.len() == 1 && !regen_images[0].is_empty() {
        let copies = vec!["a"; regen_images[0].len()].join(", ");
        return Ok(format!("a -> ({copies})"));
    }

    // 一般の場合: 各固定座標がどの再生成座標 `a_k` を読むか並べる。
    let mut slot_expr = vec!["0".to_owned(); fixed.coords0.len()];
    let mut collided = BTreeSet::new();
    for (ri, imgs) in regen_images.iter().enumerate() {
        if imgs.len() > 1 {
            collided.insert(ri);
        }
        let var = format!("a_{ri}");
        for &fi in imgs {
            slot_expr[fi] = var.clone();
        }
    }
    let vars: Vec<String> = (0..regen.coords0.len()).map(|i| format!("a_{i}")).collect();
    Ok(format!(
        "({}) -> ({}) [collided_blocks={}]",
        vars.join(", "),
        slot_expr.join(", "),
        collided.len()
    ))
}

/// 明示整数 2 項複体 `[Z^{dim0} --d0--> Z^{dim1}]` への係数変更比較（W1）。
fn check_explicit_z_complex(
    ex: &ExplicitZComplexSpec,
    target: &CoeffDomain,
) -> Result<ExplicitComplexChangeResult, SilenceReason> {
    let d0_z: Vec<Vec<BigInt>> = ex
        .d0
        .iter()
        .map(|row| row.iter().map(|&v| BigInt::from(v)).collect())
        .collect();
    let d1_z: Vec<Vec<BigInt>> = Vec::new();
    let cpx_z = CochainComplex::new(ex.dim0, ex.dim1, 0, d0_z.clone(), d1_z, BigInt::zero())
        .map_err(map_diag_alg_err)?;
    let coh_z = cpx_z.cohomology_z().map_err(map_diag_alg_err)?;

    let (
        target_h0,
        target_h1,
        target_h0_rank,
        target_h1_rank,
        zero_in_src,
        zero_in_tgt,
        is_torsion_in_src,
    ) = match target {
        CoeffDomain::Z => {
            let (zs, zt, tors) = if let Some(coc) = &ex.designated_cocycle {
                let v: Vec<BigInt> = coc.iter().map(|&x| BigInt::from(x)).collect();
                let chk = cpx_z.check_h1_cocycle_z(&v).map_err(map_diag_alg_err)?;
                (
                    Some(chk.is_zero_in_z),
                    Some(chk.is_zero_in_z),
                    Some(chk.torsion_order.is_some()),
                )
            } else {
                (None, None, None)
            };
            (
                coh_z.h0.display("Z"),
                coh_z.h1.display("Z"),
                coh_z.h0.free_rank,
                coh_z.h1.free_rank,
                zs,
                zt,
                tors,
            )
        }
        CoeffDomain::Q => {
            let d0_q = lift_mat_z_to_q(&d0_z);
            let cpx_q = CochainComplex::new(ex.dim0, ex.dim1, 0, d0_q, Vec::new(), Rat::zero())
                .map_err(map_diag_alg_err)?;
            let coh_q = cpx_q.cohomology_field().map_err(map_diag_alg_err)?;
            let (zs, zt, tors) = if let Some(coc) = &ex.designated_cocycle {
                let vz: Vec<BigInt> = coc.iter().map(|&x| BigInt::from(x)).collect();
                let chkz = cpx_z.check_h1_cocycle_z(&vz).map_err(map_diag_alg_err)?;
                let vq: Vec<Rat> = coc
                    .iter()
                    .map(|&x| Rat::from_int(BigInt::from(x)))
                    .collect();
                let chkq = cpx_q
                    .check_h1_cocycle_field(&coh_q, &vq)
                    .map_err(map_diag_alg_err)?;
                (
                    Some(chkz.is_zero_in_z),
                    Some(chkq.is_zero_class),
                    Some(chkz.torsion_order.is_some()),
                )
            } else {
                (None, None, None)
            };
            (
                CohomologyGroup::free(coh_q.h0_dim).display("Q"),
                CohomologyGroup::free(coh_q.h1_dim).display("Q"),
                coh_q.h0_dim,
                coh_q.h1_dim,
                zs,
                zt,
                tors,
            )
        }
        CoeffDomain::Fp(p) => {
            let Some(zero_fp) = FpElem::zero(p.clone()) else {
                return Err(SilenceReason::UnsupportedCoeffRing {
                    domain: target.clone(),
                    detail: format!("modulus {p} is not prime"),
                });
            };
            let d0_fp = lift_mat_z_to_fp(&d0_z, p);
            let cpx_fp = CochainComplex::new(ex.dim0, ex.dim1, 0, d0_fp, Vec::new(), zero_fp)
                .map_err(map_diag_alg_err)?;
            let coh_fp = cpx_fp.cohomology_field().map_err(map_diag_alg_err)?;
            let label = format!("F_{p}");
            let (zs, zt, tors) = if let Some(coc) = &ex.designated_cocycle {
                let vz: Vec<BigInt> = coc.iter().map(|&x| BigInt::from(x)).collect();
                let chkz = cpx_z.check_h1_cocycle_z(&vz).map_err(map_diag_alg_err)?;
                let vfp: Vec<FpElem> = coc
                    .iter()
                    .map(|&x| FpElem::from_checked_prime(BigInt::from(x), p.clone()))
                    .collect();
                let chkfp = cpx_fp
                    .check_h1_cocycle_field(&coh_fp, &vfp)
                    .map_err(map_diag_alg_err)?;
                (
                    Some(chkz.is_zero_in_z),
                    Some(chkfp.is_zero_class),
                    Some(chkz.torsion_order.is_some()),
                )
            } else {
                (None, None, None)
            };
            (
                CohomologyGroup::free(coh_fp.h0_dim).display(&label),
                CohomologyGroup::free(coh_fp.h1_dim).display(&label),
                coh_fp.h0_dim,
                coh_fp.h1_dim,
                zs,
                zt,
                tors,
            )
        }
    };

    // H^i(C_Z) ⊗_Z target と H^i(C_Z ⊗_Z target) が一致するか比較する（A3）。
    let flat_preservation_holds = match target {
        CoeffDomain::Z => true,
        CoeffDomain::Q => {
            coh_z.h0.free_rank == target_h0_rank && coh_z.h1.free_rank == target_h1_rank
        }
        CoeffDomain::Fp(p) => {
            let p_int = BigInt::from(p.clone());
            let h0_tensor_dim = coh_z.h0.free_rank
                + coh_z
                    .h0
                    .torsion_invariants
                    .iter()
                    .filter(|d| (*d % &p_int).is_zero())
                    .count();
            let h1_tensor_dim = coh_z.h1.free_rank
                + coh_z
                    .h1
                    .torsion_invariants
                    .iter()
                    .filter(|d| (*d % &p_int).is_zero())
                    .count();
            h0_tensor_dim == target_h0_rank && h1_tensor_dim == target_h1_rank
        }
    };

    let torsion_vanished_in_target = match (is_torsion_in_src, zero_in_tgt) {
        (Some(is_tors), Some(zt)) => Some(is_tors && zt),
        _ => None,
    };

    Ok(ExplicitComplexChangeResult {
        source_h0: coh_z.h0.display("Z"),
        source_h1: coh_z.h1.display("Z"),
        target_h0,
        target_h1,
        flat_preservation_holds,
        designated_class_zero_in_source: zero_in_src,
        designated_class_zero_in_target: zero_in_tgt,
        torsion_vanished_in_target,
    })
}
