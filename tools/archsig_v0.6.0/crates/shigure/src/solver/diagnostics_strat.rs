//! 多項式 readout 族上の診断層 $B_\pi$ 層別（G-142 B1–B5）・
//! 特殊化下降による上半連続性反証（D3・W2）・$R$-点 vs 幾何点 stalk 対照（W2）。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::FiniteAlgebra;
use crate::algebra::constructible::normalize_and_prune_stratum;
use crate::algebra::groebner::rabinowitsch_solve;
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::algebra::syzygy::{DEFAULT_MAX_SYZYGY_PAIRS, FieldCoeff, ideal_membership_field};
use crate::ir::diagnostics::{DiagnosticsReadoutSpec, DiagnosticsTaskSpec, RPointProbeSpec};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase4::{
    LawValueBlockSummary, PartitionStratumSummary, RPointContrastResult,
    UpperSemicontinuityRefutation,
};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::diagnostics::{
    ComputedNerve, DiagCohomologySummary, DiagnosticComplexData, build_diagnostic_complex,
    compute_block_decomposition, evaluate_complex_over_domain, map_diag_alg_err,
};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

pub const DEFAULT_MAX_DIAGNOSTIC_PARTITIONS: usize = 128;

type LawPolyGroup<C> = (String, Vec<(String, Poly<C>)>);
type PartitionBlocks<C> = Vec<Vec<(String, Poly<C>)>>;

pub(crate) struct StratificationOutput {
    pub(crate) strata: Vec<PartitionStratumSummary>,
    pub(crate) closure_data: Vec<StratumClosureData>,
    pub(crate) generic_complex: DiagnosticComplexData,
    pub(crate) generic_summary: DiagCohomologySummary,
    pub(crate) generic_blocks: Vec<LawValueBlockSummary>,
}

pub(crate) enum StratumClosureData {
    Q {
        vars: VarOrder,
        /// `rabinowitsch_solve` が返す Zariski 閉包イデアル `I(\overline{B_\pi})`。
        closure_eqs: Vec<Poly<Rat>>,
        equations: Vec<Poly<Rat>>,
        invertibles: Vec<Poly<Rat>>,
    },
    Fp {
        modulus: BigUint,
        vars: VarOrder,
        equations: Vec<Poly<FpElem>>,
        invertibles: Vec<Poly<FpElem>>,
    },
}

/// 多項式 readout 族の全等値 partition 層別 `B_π` を枝刈り探索する（G-142 B5）。
pub(crate) fn compute_polynomial_stratification(
    spec: &DiagnosticsTaskSpec,
    nerve: &ComputedNerve,
    diag_coeff: &CoeffDomain,
) -> Result<StratificationOutput, SilenceReason> {
    let DiagnosticsReadoutSpec::Polynomial {
        base_domain,
        base_vars,
        base_relations,
        sources,
        laws,
    } = &spec.readout
    else {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "polynomial_readout_expected".to_owned(),
            detail: "expected Polynomial readout".to_owned(),
        });
    };

    let max_partitions = spec
        .max_partitions
        .unwrap_or(DEFAULT_MAX_DIAGNOSTIC_PARTITIONS);
    let (var_order, bindings) =
        ExprBindings::from_slices(base_vars, &[], &[]).map_err(map_diag_alg_err)?;

    match base_domain {
        CoeffDomain::Q => stratify_over_q(
            &var_order,
            &bindings,
            base_relations,
            sources,
            laws,
            nerve,
            diag_coeff,
            max_partitions,
        ),
        CoeffDomain::Fp(p) => {
            if !archsig_common::prime::is_prime(p) {
                return Err(SilenceReason::UnsupportedCoeffRing {
                    domain: base_domain.clone(),
                    detail: format!("base_domain modulus {p} is not prime"),
                });
            }
            stratify_over_fp(
                p,
                &var_order,
                &bindings,
                base_relations,
                sources,
                laws,
                nerve,
                diag_coeff,
                max_partitions,
            )
        }
        CoeffDomain::Z => Err(SilenceReason::DiagnosticsStratificationOutOfScope {
            detail: "polynomial readout stratification B_pi requires a field base_domain (Q or F_p); Z base scheme stratification is out of scope".to_owned(),
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn stratify_over_q(
    var_order: &VarOrder,
    bindings: &ExprBindings,
    base_relations: &[crate::ir::change::NamedPoly],
    sources: &[String],
    laws: &[crate::ir::diagnostics::PolyLawReadoutSpec],
    nerve: &ComputedNerve,
    diag_coeff: &CoeffDomain,
    max_partitions: usize,
) -> Result<StratificationOutput, SilenceReason> {
    let mut base_eqs = Vec::with_capacity(base_relations.len());
    for rel in base_relations {
        base_eqs.push(Poly::from_expr_q(&rel.expr, bindings).map_err(map_diag_alg_err)?);
    }

    let mut law_polys: Vec<LawPolyGroup<Rat>> = Vec::with_capacity(laws.len());
    for law in laws {
        let map: BTreeMap<&str, &PolyExpr> =
            law.values.iter().map(|(s, e)| (s.as_str(), e)).collect();
        let mut entries = Vec::with_capacity(sources.len());
        for s in sources {
            let expr = map[s.as_str()];
            let p = Poly::from_expr_q(expr, bindings).map_err(map_diag_alg_err)?;
            entries.push((s.clone(), p));
        }
        law_polys.push((law.law_name.clone(), entries));
    }

    // 初期基底 B が空なら空層別を返す。
    let Some(init_st) = normalize_and_prune_stratum(&base_eqs, &[], var_order)? else {
        return empty_stratification(diag_coeff);
    };

    // 状態: (law ごとの blocks: Vec<Vec<(source_name, poly)>>, equations, invertibles)
    type BlockEntry = (String, Poly<Rat>);
    type State = (Vec<Vec<Vec<BlockEntry>>>, Vec<Poly<Rat>>, Vec<Poly<Rat>>);

    let mut active: Vec<State> = vec![(
        vec![Vec::new(); law_polys.len()],
        init_st.equations,
        init_st.invertibles,
    )];
    let mut visited_candidates = 1usize;

    for (li, (_law_name, entries)) in law_polys.iter().enumerate() {
        for (src, poly) in entries {
            let mut next_active = Vec::new();
            for (parts, eqs, invs) in active {
                let cur_blocks = &parts[li];
                // 枝 1: 既存 block へ合流
                for (bi, block) in cur_blocks.iter().enumerate() {
                    visited_candidates += 1;
                    if visited_candidates > max_partitions {
                        return Err(SilenceReason::DiagnosticsStratificationOutOfScope {
                            detail: format!(
                                "partition stratification exceeded max_partitions ({max_partitions})"
                            ),
                        });
                    }
                    let diff = poly.sub(&block[0].1);
                    let mut new_eqs = eqs.clone();
                    if !diff.is_zero() {
                        new_eqs.push(diff);
                    }
                    if let Some(norm) = normalize_and_prune_stratum(&new_eqs, &invs, var_order)? {
                        let mut new_parts = parts.clone();
                        new_parts[li][bi].push((src.clone(), poly.clone()));
                        next_active.push((new_parts, norm.equations, norm.invertibles));
                    }
                }
                // 枝 2: 新規 block を生成
                visited_candidates += 1;
                if visited_candidates > max_partitions {
                    return Err(SilenceReason::DiagnosticsStratificationOutOfScope {
                        detail: format!(
                            "partition stratification exceeded max_partitions ({max_partitions})"
                        ),
                    });
                }
                let mut new_invs = invs.clone();
                let mut trivial_zero = false;
                for block in cur_blocks {
                    let diff = poly.sub(&block[0].1);
                    if diff.is_zero() {
                        trivial_zero = true;
                        break;
                    }
                    new_invs.push(diff);
                }
                if !trivial_zero
                    && let Some(norm) = normalize_and_prune_stratum(&eqs, &new_invs, var_order)?
                {
                    let mut new_parts = parts.clone();
                    new_parts[li].push(vec![(src.clone(), poly.clone())]);
                    next_active.push((new_parts, norm.equations, norm.invertibles));
                }
            }
            if next_active.len() > max_partitions {
                return Err(SilenceReason::DiagnosticsStratificationOutOfScope {
                    detail: format!(
                        "nonempty strata count {} exceeded max_partitions ({max_partitions})",
                        next_active.len()
                    ),
                });
            }
            active = next_active;
        }
    }

    if active.is_empty() {
        return empty_stratification(diag_coeff);
    }

    let mut strata = Vec::with_capacity(active.len());
    let mut closure_data = Vec::with_capacity(active.len());
    let mut best_generic: Option<(
        usize,
        usize,
        DiagnosticComplexData,
        DiagCohomologySummary,
        Vec<LawValueBlockSummary>,
    )> = None;

    for (parts, eqs, invs) in active {
        let target_law_values = partition_to_law_values(&law_polys, &parts);
        let cpx_data = build_diagnostic_complex(nerve, &target_law_values);
        let sum = evaluate_complex_over_domain(&cpx_data, diag_coeff)?;
        let partition_display = format_partition_display(&law_polys, &parts);
        let eq_strs: Vec<String> = eqs
            .iter()
            .map(|p| p.display(var_order, MonomialOrder::Grevlex))
            .collect();
        let inv_strs: Vec<String> = invs
            .iter()
            .map(|p| p.display(var_order, MonomialOrder::Grevlex))
            .collect();
        let total_blocks: usize = parts.iter().map(Vec::len).sum();
        let eq_count = eqs.len();
        let is_better = match &best_generic {
            None => true,
            Some((best_eqs, best_blocks, ..)) => {
                (eq_count < *best_eqs) || (eq_count == *best_eqs && total_blocks > *best_blocks)
            }
        };
        if is_better {
            let blocks = compute_block_decomposition(nerve, &target_law_values, diag_coeff)?;
            best_generic = Some((eq_count, total_blocks, cpx_data, sum.clone(), blocks));
        }

        strata.push(PartitionStratumSummary {
            partition: partition_display,
            equations: eq_strs,
            invertibles: inv_strs,
            h0_free_rank: sum.h0_free_rank,
            h1_free_rank: sum.h1_free_rank,
            h2_free_rank: sum.h2_free_rank,
        });
        // `eqs` は既に `normalize_and_prune_stratum` が飽和済みの Zariski 閉包基底へ正規化している。
        closure_data.push(StratumClosureData::Q {
            vars: var_order.clone(),
            closure_eqs: eqs.clone(),
            equations: eqs,
            invertibles: invs,
        });
    }

    let (_, _, generic_complex, generic_summary, generic_blocks) =
        best_generic.expect("active is non-empty");
    Ok(StratificationOutput {
        strata,
        closure_data,
        generic_complex,
        generic_summary,
        generic_blocks,
    })
}

#[allow(clippy::too_many_arguments)]
fn stratify_over_fp(
    modulus: &BigUint,
    var_order: &VarOrder,
    bindings: &ExprBindings,
    base_relations: &[crate::ir::change::NamedPoly],
    sources: &[String],
    laws: &[crate::ir::diagnostics::PolyLawReadoutSpec],
    nerve: &ComputedNerve,
    diag_coeff: &CoeffDomain,
    max_partitions: usize,
) -> Result<StratificationOutput, SilenceReason> {
    let mut base_eqs = Vec::with_capacity(base_relations.len());
    for rel in base_relations {
        base_eqs.push(Poly::from_expr_fp(&rel.expr, bindings, modulus).map_err(map_diag_alg_err)?);
    }
    let mut law_polys: Vec<LawPolyGroup<FpElem>> = Vec::with_capacity(laws.len());
    for law in laws {
        let map: BTreeMap<&str, &PolyExpr> =
            law.values.iter().map(|(s, e)| (s.as_str(), e)).collect();
        let mut entries = Vec::with_capacity(sources.len());
        for s in sources {
            let p =
                Poly::from_expr_fp(map[s.as_str()], bindings, modulus).map_err(map_diag_alg_err)?;
            entries.push((s.clone(), p));
        }
        law_polys.push((law.law_name.clone(), entries));
    }

    if !is_nonempty_fp(&base_eqs, &[], var_order, modulus)? {
        return empty_stratification(diag_coeff);
    }

    type BlockEntry = (String, Poly<FpElem>);
    type State = (
        Vec<Vec<Vec<BlockEntry>>>,
        Vec<Poly<FpElem>>,
        Vec<Poly<FpElem>>,
    );
    let mut active: Vec<State> = vec![(vec![Vec::new(); law_polys.len()], base_eqs, Vec::new())];
    let mut visited = 1usize;

    for (li, (_law_name, entries)) in law_polys.iter().enumerate() {
        for (src, poly) in entries {
            let mut next_active = Vec::new();
            for (parts, eqs, invs) in active {
                let cur_blocks = &parts[li];
                for (bi, block) in cur_blocks.iter().enumerate() {
                    visited += 1;
                    if visited > max_partitions {
                        return Err(SilenceReason::DiagnosticsStratificationOutOfScope {
                            detail: format!(
                                "partition stratification exceeded max_partitions ({max_partitions})"
                            ),
                        });
                    }
                    let diff = poly.sub(&block[0].1);
                    let mut new_eqs = eqs.clone();
                    if !diff.is_zero() {
                        new_eqs.push(diff);
                    }
                    if is_nonempty_fp(&new_eqs, &invs, var_order, modulus)? {
                        let mut new_parts = parts.clone();
                        new_parts[li][bi].push((src.clone(), poly.clone()));
                        next_active.push((new_parts, new_eqs, invs.clone()));
                    }
                }
                visited += 1;
                if visited > max_partitions {
                    return Err(SilenceReason::DiagnosticsStratificationOutOfScope {
                        detail: format!(
                            "partition stratification exceeded max_partitions ({max_partitions})"
                        ),
                    });
                }
                let mut new_invs = invs.clone();
                let mut trivial_zero = false;
                for block in cur_blocks {
                    let diff = poly.sub(&block[0].1);
                    if diff.is_zero() {
                        trivial_zero = true;
                        break;
                    }
                    new_invs.push(diff);
                }
                if !trivial_zero && is_nonempty_fp(&eqs, &new_invs, var_order, modulus)? {
                    let mut new_parts = parts.clone();
                    new_parts[li].push(vec![(src.clone(), poly.clone())]);
                    next_active.push((new_parts, eqs.clone(), new_invs));
                }
            }
            if next_active.len() > max_partitions {
                return Err(SilenceReason::DiagnosticsStratificationOutOfScope {
                    detail: format!(
                        "nonempty strata count {} exceeded max_partitions ({max_partitions})",
                        next_active.len()
                    ),
                });
            }
            active = next_active;
        }
    }

    if active.is_empty() {
        return empty_stratification(diag_coeff);
    }

    let mut strata = Vec::with_capacity(active.len());
    let mut closure_data = Vec::with_capacity(active.len());
    let mut best_generic: Option<(
        usize,
        usize,
        DiagnosticComplexData,
        DiagCohomologySummary,
        Vec<LawValueBlockSummary>,
    )> = None;

    for (parts, eqs, invs) in active {
        let target_law_values = partition_to_law_values(&law_polys, &parts);
        let cpx_data = build_diagnostic_complex(nerve, &target_law_values);
        let sum = evaluate_complex_over_domain(&cpx_data, diag_coeff)?;
        let partition_display = format_partition_display(&law_polys, &parts);
        let eq_strs: Vec<String> = eqs
            .iter()
            .map(|p| p.display(var_order, MonomialOrder::Grevlex))
            .collect();
        let inv_strs: Vec<String> = invs
            .iter()
            .map(|p| p.display(var_order, MonomialOrder::Grevlex))
            .collect();
        let total_blocks: usize = parts.iter().map(Vec::len).sum();
        let eq_count = eqs.len();
        let is_better = match &best_generic {
            None => true,
            Some((best_eqs, best_blocks, ..)) => {
                (eq_count < *best_eqs) || (eq_count == *best_eqs && total_blocks > *best_blocks)
            }
        };
        if is_better {
            let blocks = compute_block_decomposition(nerve, &target_law_values, diag_coeff)?;
            best_generic = Some((eq_count, total_blocks, cpx_data, sum.clone(), blocks));
        }

        strata.push(PartitionStratumSummary {
            partition: partition_display,
            equations: eq_strs,
            invertibles: inv_strs,
            h0_free_rank: sum.h0_free_rank,
            h1_free_rank: sum.h1_free_rank,
            h2_free_rank: sum.h2_free_rank,
        });
        closure_data.push(StratumClosureData::Fp {
            modulus: modulus.clone(),
            vars: var_order.clone(),
            equations: eqs,
            invertibles: invs,
        });
    }

    let (_, _, generic_complex, generic_summary, generic_blocks) =
        best_generic.expect("active is non-empty");
    Ok(StratificationOutput {
        strata,
        closure_data,
        generic_complex,
        generic_summary,
        generic_blocks,
    })
}

/// F_p の代数閉包上で `V(eqs) ∩ D(invs)` が非空かを Rabinowitsch + 理想所属判定で厳密判定する。
fn is_nonempty_fp(
    eqs: &[Poly<FpElem>],
    invs: &[Poly<FpElem>],
    vars: &VarOrder,
    modulus: &BigUint,
) -> Result<bool, SilenceReason> {
    let zero_fp = FpElem::from_checked_prime(num_bigint::BigInt::zero(), modulus.clone());
    let one_fp = FpElem::from_checked_prime(num_bigint::BigInt::one(), modulus.clone());
    let n = vars.len();
    let total_vars = n + invs.len();
    let mut gens = Vec::with_capacity(eqs.len() + invs.len());
    for eq in eqs {
        gens.push(embed_poly_vars(eq, total_vars, zero_fp.clone()));
    }
    let one_poly = Poly::constant(total_vars, one_fp);
    for (j, inv) in invs.iter().enumerate() {
        let inv_emb = embed_poly_vars(inv, total_vars, zero_fp.clone());
        let u_var = Poly::var(total_vars, n + j, zero_fp.clone());
        let prod_poly = inv_emb.mul(&u_var).sub(&one_poly);
        gens.push(prod_poly);
    }
    let mut all_var_names: Vec<String> = vars.vars().to_vec();
    let mut existing: BTreeSet<String> = all_var_names.iter().cloned().collect();
    let mut aux_seq = 0usize;
    for _ in 0..invs.len() {
        loop {
            let cand = format!("__rab_u_{aux_seq}");
            aux_seq += 1;
            if existing.insert(cand.clone()) {
                all_var_names.push(cand);
                break;
            }
        }
    }
    let all_vars = VarOrder::new(all_var_names).map_err(map_diag_alg_err)?;
    let mem = ideal_membership_field(
        &one_poly,
        &gens,
        &all_vars,
        MonomialOrder::Grevlex,
        DEFAULT_MAX_SYZYGY_PAIRS,
    )
    .map_err(map_diag_alg_err)?;
    Ok(mem.is_none())
}

fn embed_poly_vars<C: RingCoeff>(p: &Poly<C>, new_num_vars: usize, zero: C) -> Poly<C> {
    let mut out = Poly::zero(new_num_vars, zero);
    for (m, c) in p.terms() {
        let mut exps = m.exps().to_vec();
        exps.resize(new_num_vars, 0);
        out.add_term(crate::algebra::poly::Monomial::from_exps(exps), c.clone());
    }
    out
}

/// 特殊化下降対 `(\bar\eta -> \bar s)` を検出し、上半連続性による pseudo-coherent 複体非存在証拠を構成する（D3）。
pub(crate) fn detect_upper_semicontinuity(
    strat: &StratificationOutput,
) -> Result<Option<UpperSemicontinuityRefutation>, SilenceReason> {
    for (gi, gen_st) in strat.strata.iter().enumerate() {
        for (si, spec_st) in strat.strata.iter().enumerate() {
            if gi == si || gen_st.h1_free_rank <= spec_st.h1_free_rank {
                continue;
            }
            if !is_strict_coarsening(&gen_st.partition, &spec_st.partition) {
                continue;
            }
            if stratum_meets_closure(&strat.closure_data[gi], &strat.closure_data[si])? {
                return Ok(Some(UpperSemicontinuityRefutation {
                    generic_partition: gen_st.partition.clone(),
                    special_partition: spec_st.partition.clone(),
                    generic_h1_dim: gen_st.h1_free_rank,
                    special_h1_dim: spec_st.h1_free_rank,
                    pseudo_coherent_complex_excluded: true,
                    reason: format!(
                        "specialization drops H^1 dimension from {} to {}, contradicting upper semicontinuity of derived fiber Betti numbers for pseudo-coherent (and perfect) O_B-complexes (Stacks 0BDI / G-142 D3)",
                        gen_st.h1_free_rank, spec_st.h1_free_rank
                    ),
                }));
            }
        }
    }
    Ok(None)
}

fn stratum_meets_closure(
    gen_data: &StratumClosureData,
    spec_data: &StratumClosureData,
) -> Result<bool, SilenceReason> {
    match (gen_data, spec_data) {
        (
            StratumClosureData::Q {
                vars, closure_eqs, ..
            },
            StratumClosureData::Q {
                equations,
                invertibles,
                ..
            },
        ) => {
            let mut eqs = closure_eqs.clone();
            eqs.extend(equations.iter().cloned());
            let rab = rabinowitsch_solve(&eqs, invertibles, vars).map_err(map_diag_alg_err)?;
            Ok(!rab.is_empty_over_closure)
        }
        (
            StratumClosureData::Fp {
                modulus,
                vars,
                equations: gen_eqs,
                invertibles: gen_invs,
            },
            StratumClosureData::Fp {
                equations: spec_eqs,
                invertibles: spec_invs,
                ..
            },
        ) => {
            // 線形イデアル（素イデアル）または空可逆条件なら gen_eqs は飽和済み。
            // F_p 上の非線形イデアル飽和は偽陽性を防ぐため fail-closed 沈黙する。
            if !gen_invs.is_empty() && !gen_eqs.iter().all(Poly::is_affine) {
                return Err(SilenceReason::DiagnosticsStratificationOutOfScope {
                    detail: "nonlinear ideal saturation over F_p for Zariski closure check is out of scope".to_owned(),
                });
            }
            let mut eqs = gen_eqs.clone();
            eqs.extend(spec_eqs.iter().cloned());
            is_nonempty_fp(&eqs, spec_invs, vars, modulus)
        }
        _ => Ok(false),
    }
}

fn is_strict_coarsening(fine: &[Vec<String>], coarse: &[Vec<String>]) -> bool {
    if coarse.len() >= fine.len() {
        return false;
    }
    let coarse_sets: Vec<BTreeSet<&str>> = coarse
        .iter()
        .map(|b| b.iter().map(String::as_str).collect())
        .collect();
    for fb in fine {
        if !coarse_sets
            .iter()
            .any(|cb| fb.iter().all(|s| cb.contains(s.as_str())))
        {
            return false;
        }
    }
    true
}

/// R-点（双対数 `k[ε]/(ε^{d+1})` 等）での readout 値相違と幾何点 stalk 一致を対照する（B5・W2）。
pub(crate) fn compute_r_point_contrast(
    spec: &DiagnosticsTaskSpec,
    rp: &RPointProbeSpec,
    nerve: &ComputedNerve,
    diag_coeff: &CoeffDomain,
) -> Result<RPointContrastResult, SilenceReason> {
    let DiagnosticsReadoutSpec::Polynomial {
        base_domain,
        base_vars,
        base_relations,
        sources,
        laws,
    } = &spec.readout
    else {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "r_point_probe_requires_polynomial".to_owned(),
            detail: "r_point_probe requires Polynomial readout".to_owned(),
        });
    };

    let (_var_order, bindings) =
        ExprBindings::from_slices(base_vars, &[], &[]).map_err(map_diag_alg_err)?;
    let (_, empty_bindings) = ExprBindings::from_slices(&[], &[], &[]).map_err(map_diag_alg_err)?;

    match base_domain {
        CoeffDomain::Q => r_point_contrast_field(
            base_vars,
            base_relations,
            sources,
            laws,
            rp,
            nerve,
            diag_coeff,
            Rat::zero(),
            "Q",
            &bindings,
            &empty_bindings,
            &|e, b| Poly::from_expr_q(e, b),
        ),
        CoeffDomain::Fp(p) => {
            let Some(zero_fp) = FpElem::zero(p.clone()) else {
                return Err(SilenceReason::UnsupportedCoeffRing {
                    domain: base_domain.clone(),
                    detail: format!("modulus {p} is not prime"),
                });
            };
            let p1 = p.clone();
            let ring_base = format!("F_{p}");
            r_point_contrast_field(
                base_vars,
                base_relations,
                sources,
                laws,
                rp,
                nerve,
                diag_coeff,
                zero_fp,
                &ring_base,
                &bindings,
                &empty_bindings,
                &move |e, b| Poly::from_expr_fp(e, b, &p1),
            )
        }
        CoeffDomain::Z => Err(SilenceReason::DiagnosticsStratificationOutOfScope {
            detail: "r_point_probe requires field base_domain (Q or F_p)".to_owned(),
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn r_point_contrast_field<C, FE>(
    base_vars: &[String],
    base_relations: &[crate::ir::change::NamedPoly],
    sources: &[String],
    laws: &[crate::ir::diagnostics::PolyLawReadoutSpec],
    rp: &RPointProbeSpec,
    nerve: &ComputedNerve,
    diag_coeff: &CoeffDomain,
    zero: C,
    base_ring_label: &str,
    bindings: &ExprBindings,
    empty_bindings: &ExprBindings,
    expand: &FE,
) -> Result<RPointContrastResult, SilenceReason>
where
    C: FieldCoeff,
    FE: Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>,
{
    let alg = FiniteAlgebra::truncated_univariate(&rp.ring_var, rp.ring_max_deg, zero.clone())
        .map_err(map_diag_alg_err)?;
    let ring_label = format!(
        "{base_ring_label}[{}]/({}^{})",
        rp.ring_var,
        rp.ring_var,
        rp.ring_max_deg + 1
    );

    let mut rel_polys = Vec::with_capacity(base_relations.len());
    for rel in base_relations {
        rel_polys.push((
            rel.name.as_str(),
            expand(&rel.expr, bindings).map_err(map_diag_alg_err)?,
        ));
    }

    let mut law_polys: Vec<LawPolyGroup<C>> = Vec::with_capacity(laws.len());
    for law in laws {
        let map: BTreeMap<&str, &PolyExpr> =
            law.values.iter().map(|(s, e)| (s.as_str(), e)).collect();
        let mut entries = Vec::with_capacity(sources.len());
        for s in sources {
            let p = expand(map[s.as_str()], bindings).map_err(map_diag_alg_err)?;
            entries.push((s.clone(), p));
        }
        law_polys.push((law.law_name.clone(), entries));
    }

    let mut r_values_by_point: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    let mut geometric_stalk_h1_dims: BTreeMap<String, usize> = BTreeMap::new();
    let mut geom_partitions: Vec<BTreeMap<String, BTreeMap<String, String>>> = Vec::new();
    let single_law = law_polys.len() == 1;

    for pt in &rp.points {
        let coord_map: BTreeMap<&str, &[PolyExpr]> = pt
            .coords
            .iter()
            .map(|(v, cs)| (v.as_str(), cs.as_slice()))
            .collect();
        let mut r_coords: Vec<Vec<C>> = Vec::with_capacity(base_vars.len());
        let mut geom_coords: Vec<C> = Vec::with_capacity(base_vars.len());
        for v in base_vars {
            let cs = coord_map[v.as_str()];
            let mut elem = Vec::with_capacity(cs.len());
            for c_expr in cs {
                let cp = expand(c_expr, empty_bindings).map_err(map_diag_alg_err)?;
                let val = cp.eval_at(&[]).map_err(map_diag_alg_err)?;
                elem.push(val);
            }
            geom_coords.push(elem[0].clone());
            r_coords.push(elem);
        }

        // base_relations の R での成立を検証する。
        for (rname, rpoly) in &rel_polys {
            let val = alg.eval_poly(rpoly, &r_coords).map_err(map_diag_alg_err)?;
            if !alg.is_zero_elem(&val) {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "r_point_satisfies_base_relations".to_owned(),
                    detail: format!(
                        "R-point `{}` violates base_relation `{rname}`: {} != 0",
                        pt.label,
                        alg.format_elem(&val)
                    ),
                });
            }
        }

        let mut pt_r_vals = BTreeMap::new();
        let mut geom_target_vals: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
        for (law_name, entries) in &law_polys {
            let mut g_inner = BTreeMap::new();
            for (src, poly) in entries {
                let rv = alg.eval_poly(poly, &r_coords).map_err(map_diag_alg_err)?;
                let key = if single_law {
                    src.clone()
                } else {
                    format!("{law_name}:{src}")
                };
                pt_r_vals.insert(key, alg.format_elem(&rv));

                let gv = poly.eval_at(&geom_coords).map_err(map_diag_alg_err)?;
                g_inner.insert(src.clone(), gv.to_string());
            }
            geom_target_vals.insert(law_name.clone(), g_inner);
        }

        let stalk_cpx = build_diagnostic_complex(nerve, &geom_target_vals);
        let stalk_sum = evaluate_complex_over_domain(&stalk_cpx, diag_coeff)?;
        geometric_stalk_h1_dims.insert(pt.label.clone(), stalk_sum.h1_free_rank);
        r_values_by_point.insert(pt.label.clone(), pt_r_vals);
        geom_partitions.push(canonicalize_geom_partition(&geom_target_vals));
    }

    let r_vals_list: Vec<&BTreeMap<String, String>> = r_values_by_point.values().collect();
    let r_values_differ = r_vals_list.windows(2).any(|w| w[0] != w[1])
        || r_vals_list
            .iter()
            .any(|m| Some(*m) != r_vals_list.first().copied());
    let geometric_stalks_agree = geom_partitions
        .first()
        .is_none_or(|first| geom_partitions.iter().all(|g| g == first));

    Ok(RPointContrastResult {
        ring_label,
        r_values_by_point,
        r_values_differ,
        geometric_stalk_h1_dims,
        geometric_stalks_agree,
    })
}

fn canonicalize_geom_partition(
    vals: &BTreeMap<String, BTreeMap<String, String>>,
) -> BTreeMap<String, BTreeMap<String, String>> {
    // 同じ値を持つ source 群へ正規化ラベルを付与（幾何 stalk 複体の同型比較用）。
    let mut out = BTreeMap::new();
    for (law, m) in vals {
        let mut by_val: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for (s, v) in m {
            by_val.entry(v.as_str()).or_default().push(s.as_str());
        }
        let mut inner = BTreeMap::new();
        for (_v, group) in by_val {
            let tag = group.join(",");
            for s in group {
                inner.insert(s.to_owned(), tag.clone());
            }
        }
        out.insert(law.clone(), inner);
    }
    out
}

fn partition_to_law_values<C: RingCoeff>(
    law_polys: &[LawPolyGroup<C>],
    parts: &[PartitionBlocks<C>],
) -> BTreeMap<String, BTreeMap<String, String>> {
    let mut out = BTreeMap::new();
    for ((law_name, _), blocks) in law_polys.iter().zip(parts) {
        let mut inner = BTreeMap::new();
        for (bi, block) in blocks.iter().enumerate() {
            let label = format!("b{bi}");
            for (src, _) in block {
                inner.insert(src.clone(), label.clone());
            }
        }
        out.insert(law_name.clone(), inner);
    }
    out
}

fn format_partition_display<C: RingCoeff>(
    law_polys: &[LawPolyGroup<C>],
    parts: &[PartitionBlocks<C>],
) -> Vec<Vec<String>> {
    let single = law_polys.len() == 1;
    let mut out = Vec::new();
    for ((law_name, _), blocks) in law_polys.iter().zip(parts) {
        for block in blocks {
            let mut names: Vec<String> = block
                .iter()
                .map(|(s, _)| {
                    if single {
                        s.clone()
                    } else {
                        format!("{law_name}:{s}")
                    }
                })
                .collect();
            names.sort();
            out.push(names);
        }
    }
    out
}

fn empty_stratification(diag_coeff: &CoeffDomain) -> Result<StratificationOutput, SilenceReason> {
    let empty_cpx = DiagnosticComplexData {
        coords0: Vec::new(),
        coords1: Vec::new(),
        coords2: Vec::new(),
        d0_z: Vec::new(),
        d1_z: Vec::new(),
    };
    let sum = evaluate_complex_over_domain(&empty_cpx, diag_coeff)?;
    Ok(StratificationOutput {
        strata: Vec::new(),
        closure_data: Vec::new(),
        generic_complex: empty_cpx,
        generic_summary: sum,
        generic_blocks: Vec::new(),
    })
}
