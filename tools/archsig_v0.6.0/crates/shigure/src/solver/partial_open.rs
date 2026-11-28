//! AAT 第18章後半（解の量化 4 階層 $E/U/G/Q$・必要スロットの極小横断集合・開領域局所網羅・
//! 正の存在式保存・アフィン制限一意修復）の計算核ヘルパ。

use crate::algebra::artin::{AffineSolutionField, solve_affine_field};
use crate::algebra::hitting_set::{
    HittingSetInput, HittingSetOutcome, enumerate_minimal_hitting_sets, verify_minimal_hitting_sets,
};
use crate::algebra::linear::{AffineSolutionQ, AffineSolutionZ, solve_affine_q, solve_affine_z};
use crate::algebra::scalar::{FpElem, Rat};
use crate::algebra::syzygy::FieldCoeff;
use crate::ir::partial::{AffineRestrictionSpec, OpenDomainSpec, QuantifierHierarchySpec};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, ReevalCheck, SilenceReason};
use crate::ir::result_phase5_obs::{OpenDomainResultDetail, QuantifierHierarchyDetail};
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::solver::partial_affine::{rank_over_field, scalar_to_fp, scalar_to_rat};
use crate::solver::partial_kleene::{
    CompleteFiniteWorld, eval_formula_complete, eval_law_complete_via_kleene,
};
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};

/// 定義 18.10・命題 18.11・定理 18.12: 解の量化 4 階層 $E/U/G/Q$ と必要スロット極小横断集合を計算する。
pub(super) fn analyze_quantifier_hierarchy(
    q: &QuantifierHierarchySpec,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<QuantifierHierarchyDetail, SilenceReason> {
    if q.completions.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "quantifier_hierarchy_nonempty_completions",
            MathClause::AatCh18Prop18Dot11,
            "quantifier hierarchy requires non-empty completion family (A != empty)",
        ));
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "quantifier_hierarchy_nonempty_completions".to_owned(),
            detail: "quantifier hierarchy requires non-empty completion family (A != empty)"
                .to_owned(),
        });
    }

    let sets: Vec<BTreeSet<&str>> = q
        .completions
        .iter()
        .map(|c| c.valid_candidates.iter().map(String::as_str).collect())
        .collect();
    // E: ∀A ∈ A, ∃c ∈ C, Valid(A, c)
    let e_holds = sets.iter().all(|s| !s.is_empty());
    // U: ∀A ∈ A, ∃!c ∈ C, Valid(A, c)
    let u_holds = sets.iter().all(|s| s.len() == 1);
    // 共通候補 ∩_A C_A
    let mut common = sets[0].clone();
    for s in sets.iter().skip(1) {
        common.retain(|c| s.contains(c));
    }
    // Q: ∃!c ∈ C, ∀A ∈ A, Valid(A, c)
    let q_holds = common.len() == 1;
    // G: ∃c ∈ C, ∀A ∈ A, C_A = {c}
    let g_holds = sets.iter().all(|s| s.len() == 1) && sets.windows(2).all(|w| w[0] == w[1]);
    let g_iff_u_and_q_verified = g_holds == (u_holds && q_holds);

    checks.push(ApplicabilityCheck::passed(
        "quantifier_hierarchy_g_iff_u_and_q_checked",
        MathClause::AatCh18Prop18Dot11,
    ));

    // 定理 18.12: 異なる `(可解性, output_value)` をもつ補完ペアごとに、値を分けるスロット集合を超辺にする。
    let mut slot_names = BTreeSet::new();
    for c in &q.completions {
        for s in c.slot_values.keys() {
            slot_names.insert(s.clone());
        }
    }
    let universe: Vec<String> = slot_names.into_iter().collect();
    let mut hyperedges: Vec<Vec<String>> = Vec::new();
    let mut insufficiency_witness: Option<String> = None;

    for i in 0..q.completions.len() {
        for j in (i + 1)..q.completions.len() {
            let c1 = &q.completions[i];
            let c2 = &q.completions[j];
            let status1 = (!sets[i].is_empty(), &c1.output_value);
            let status2 = (!sets[j].is_empty(), &c2.output_value);
            if status1 != status2 {
                let edge: Vec<String> = universe
                    .iter()
                    .filter(|s| c1.slot_values.get(*s) != c2.slot_values.get(*s))
                    .cloned()
                    .collect();
                if edge.is_empty() && insufficiency_witness.is_none() {
                    insufficiency_witness = Some(format!(
                        "completions `{}` (out=`{}`) and `{}` (out=`{}`) share identical observed slots yet disagree",
                        c1.id, c1.output_value, c2.id, c2.output_value
                    ));
                }
                hyperedges.push(edge);
            }
        }
    }

    let hs = enumerate_minimal_hitting_sets(&HittingSetInput {
        universe,
        hyperedges: hyperedges.clone(),
        weights: None,
        max_steps: q.max_steps,
        max_results: crate::limits::active_limits().max_hitting_set_results,
    })
    .map_err(|e| SilenceReason::FiniteEnumerationOutOfScope {
        detail: format!("{e:?}"),
    })?;

    let required_slot_sets = match hs {
        HittingSetOutcome::EmptyHyperedge { .. } => {
            if insufficiency_witness.is_none() {
                insufficiency_witness = Some(
                    "empty separating hyperedge prevents any slot set from resolving ambiguity"
                        .to_owned(),
                );
            }
            vec![]
        }
        HittingSetOutcome::Enumerated {
            minimal_sets,
            verified,
            ..
        } => {
            if !verified || !verify_minimal_hitting_sets(&hyperedges, &minimal_sets) {
                checks.push(ApplicabilityCheck::failed(
                    "required_slots_minimal_hitting_sets_verified",
                    MathClause::AatCh18Thm18Dot12,
                    "minimal hitting sets runtime verification failed",
                ));
                return Err(SilenceReason::FiniteEnumerationOutOfScope {
                    detail: "minimal hitting sets verification failed for required slots"
                        .to_owned(),
                });
            }
            minimal_sets
        }
    };

    checks.push(ApplicabilityCheck::passed(
        "required_slots_minimal_hitting_sets_computed",
        MathClause::AatCh18Thm18Dot12,
    ));

    Ok(QuantifierHierarchyDetail {
        e_holds,
        u_holds,
        g_holds,
        q_holds,
        g_iff_u_and_q_verified,
        required_slot_sets,
        insufficiency_witness,
    })
}

/// 例 18.15・定理 18.16・定理 18.18: 開領域の充満部分構造・局所網羅・正の式保存・アフィン制限一意修復。
pub(super) fn analyze_open_domain(
    od: &OpenDomainSpec,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<OpenDomainResultDetail, SilenceReason> {
    let sub_carriers: BTreeMap<String, BTreeSet<String>> = od
        .substructure_carriers
        .iter()
        .map(|(s, elems)| (s.clone(), elems.iter().cloned().collect()))
        .collect();

    let is_full_substructure = check_full_substructure(od, &sub_carriers);

    // 参照操作によるファイバー局所網羅検査（式 18.5: p_A^{-1}(B) ⊆ X_s(A_0)）
    let mut uncovered_fibers = Vec::new();
    for fc in &od.fiber_checks {
        let known_set: BTreeSet<&str> = fc.known_targets.iter().map(String::as_str).collect();
        let sub_set = &sub_carriers[&fc.arg_sort];
        let amb_op = od
            .ambient_ops
            .iter()
            .find(|o| o.name == fc.op_name)
            .expect("validated ambient op");
        for elem in &od.ambient_carriers[&fc.arg_sort] {
            let maps_into_known = amb_op
                .entries
                .get(&vec![elem.clone()])
                .and_then(|opt| opt.as_deref())
                .is_some_and(|y| known_set.contains(y));
            if maps_into_known && !sub_set.contains(elem) {
                uncovered_fibers.push(format!("{}({elem})", fc.op_name));
            }
        }
    }
    let all_fibers_locally_exhaustive = uncovered_fibers.is_empty();

    checks.push(ApplicabilityCheck::passed(
        "open_domain_fiber_coverage_checked",
        MathClause::AatCh18Thm18Dot16,
    ));

    let is_positive_syntax = od
        .positive_or_law
        .antecedent
        .as_ref()
        .is_none_or(is_positive_existential_formula)
        && is_positive_existential_formula(&od.positive_or_law.conclusion);
    if is_positive_syntax {
        checks.push(ApplicabilityCheck::passed(
            "open_domain_positive_existential_formula",
            MathClause::AatCh18Thm18Dot16,
        ));
    } else {
        checks.push(ApplicabilityCheck::failed(
            "open_domain_positive_existential_formula",
            MathClause::AatCh18Thm18Dot16,
            "formula uses negation, implication, or universal quantifier outside Theorem 18.16 positive fragment",
        ));
    }

    let sub_world = CompleteFiniteWorld {
        slots: BTreeMap::new(),
        op_tables: od
            .substructure_ops
            .iter()
            .map(|o| (o.name.clone(), o.entries.clone()))
            .collect(),
        rel_tables: od
            .substructure_rels
            .iter()
            .map(|r| (r.name.clone(), r.entries.clone()))
            .collect(),
    };
    let amb_world = CompleteFiniteWorld {
        slots: BTreeMap::new(),
        op_tables: od
            .ambient_ops
            .iter()
            .map(|o| (o.name.clone(), o.entries.clone()))
            .collect(),
        rel_tables: od
            .ambient_rels
            .iter()
            .map(|r| (r.name.clone(), r.entries.clone()))
            .collect(),
    };

    let env = BTreeMap::new();
    let sub_holds = eval_law_complete(
        &od.positive_or_law,
        &od.substructure_carriers,
        &sub_world,
        &env,
    );
    let amb_holds = eval_law_complete(&od.positive_or_law, &od.ambient_carriers, &amb_world, &env);
    let sub_law_eval = bool_str(sub_holds).to_owned();
    let ambient_law_eval = bool_str(amb_holds).to_owned();
    let positive_preserved = !sub_holds || amb_holds;
    let law_evaluations_match = sub_holds == amb_holds;

    // 独立再評価検算（完全構造評価器と強 Kleene 評価器の独立一致を確認）
    let sub_op_arities: Vec<(&str, &[String])> = od
        .substructure_ops
        .iter()
        .map(|o| (o.name.as_str(), o.arg_sorts.as_slice()))
        .collect();
    let amb_op_arities: Vec<(&str, &[String])> = od
        .ambient_ops
        .iter()
        .map(|o| (o.name.as_str(), o.arg_sorts.as_slice()))
        .collect();
    let sub_rel_arities: Vec<(&str, &[String])> = od
        .substructure_rels
        .iter()
        .map(|r| (r.name.as_str(), r.arg_sorts.as_slice()))
        .collect();
    let amb_rel_arities: Vec<(&str, &[String])> = od
        .ambient_rels
        .iter()
        .map(|r| (r.name.as_str(), r.arg_sorts.as_slice()))
        .collect();
    let sub_re = eval_law_complete_via_kleene(
        &od.positive_or_law,
        &od.substructure_carriers,
        &sub_world,
        &sub_op_arities,
        &sub_rel_arities,
    );
    let amb_re = eval_law_complete_via_kleene(
        &od.positive_or_law,
        &od.ambient_carriers,
        &amb_world,
        &amb_op_arities,
        &amb_rel_arities,
    );
    let reeval = ReevalCheck {
        checked: true,
        matched: sub_re == sub_holds && amb_re == amb_holds,
        detail: format!(
            "substructure eval={sub_law_eval}, ambient eval={ambient_law_eval}, positive_preserved={positive_preserved}"
        ),
    };

    let (affine_unique_repair_exists, affine_image_dim, affine_fiber_dim) =
        if let Some(ar) = &od.affine_restriction {
            checks.push(ApplicabilityCheck::passed(
                "affine_restriction_unique_repair_checked",
                MathClause::AatCh18Thm18Dot18,
            ));
            let (uniq, img_dim, fib_dim) = analyze_affine_restriction(ar)?;
            (Some(uniq), img_dim, fib_dim)
        } else {
            (None, None, None)
        };

    Ok(OpenDomainResultDetail {
        is_full_substructure,
        all_fibers_locally_exhaustive,
        uncovered_fibers,
        sub_law_eval,
        ambient_law_eval,
        positive_preserved,
        law_evaluations_match,
        affine_unique_repair_exists,
        affine_image_dim,
        affine_fiber_dim,
        reevaluation: Some(reeval),
    })
}

fn eval_law_complete(
    law: &crate::ir::partial::PartialEvalLawSpec,
    sorts: &BTreeMap<String, Vec<String>>,
    world: &CompleteFiniteWorld,
    env: &BTreeMap<&str, String>,
) -> bool {
    let ant = law
        .antecedent
        .as_ref()
        .and_then(|f| eval_formula_complete(f, sorts, world, env))
        .unwrap_or(true);
    let conc = eval_formula_complete(&law.conclusion, sorts, world, env).unwrap_or(false);
    !ant || conc
}

fn check_full_substructure(
    od: &OpenDomainSpec,
    sub_carriers: &BTreeMap<String, BTreeSet<String>>,
) -> bool {
    let all_in_sub = |sorts: &[String], args: &[String]| -> bool {
        sorts
            .iter()
            .zip(args)
            .all(|(s, a)| sub_carriers.get(s).is_some_and(|set| set.contains(a)))
    };

    for sub_op in &od.substructure_ops {
        let amb_op = od
            .ambient_ops
            .iter()
            .find(|o| o.name == sub_op.name)
            .expect("validated ambient op");
        for (args, out_opt) in &sub_op.entries {
            if amb_op.entries.get(args) != Some(out_opt) {
                return false;
            }
        }
        for (args, out_opt) in &amb_op.entries {
            if all_in_sub(&amb_op.arg_sorts, args) {
                if let Some(out) = out_opt
                    && !sub_carriers[&amb_op.out_sort].contains(out)
                {
                    return false;
                }
                if sub_op.entries.get(args) != Some(out_opt) {
                    return false;
                }
            }
        }
    }

    for sub_rel in &od.substructure_rels {
        let amb_rel = od
            .ambient_rels
            .iter()
            .find(|r| r.name == sub_rel.name)
            .expect("validated ambient rel");
        if !sub_rel.entries.is_subset(&amb_rel.entries) {
            return false;
        }
        for args in &amb_rel.entries {
            if all_in_sub(&amb_rel.arg_sorts, args) && !sub_rel.entries.contains(args) {
                return false;
            }
        }
    }
    true
}

fn analyze_affine_restriction(
    ar: &AffineRestrictionSpec,
) -> Result<(bool, Option<usize>, Option<usize>), SilenceReason> {
    match &ar.coeff_domain {
        CoeffDomain::Q => {
            let zero = Rat::zero();
            let m: Vec<Vec<Rat>> = ar
                .m_matrix
                .iter()
                .map(|r| r.iter().map(scalar_to_rat).collect())
                .collect();
            let b: Vec<Rat> = ar.b_rhs.iter().map(scalar_to_rat).collect();
            let r_mat: Vec<Vec<Rat>> = ar
                .r_matrix
                .iter()
                .map(|r| r.iter().map(scalar_to_rat).collect())
                .collect();
            match solve_affine_q(&m, &b, ar.num_vars) {
                Ok(AffineSolutionQ::Inconsistent { .. }) => Ok((false, None, None)),
                Ok(AffineSolutionQ::Consistent { kernel_basis, .. }) => {
                    compute_restriction_dims(&r_mat, &kernel_basis, &zero)
                }
                Err(e) => Err(SilenceReason::from_algebra_with(e, |err| {
                    SilenceReason::FiniteEnumerationOutOfScope {
                        detail: format!("{err:?}"),
                    }
                })),
            }
        }
        CoeffDomain::Fp(p) => {
            let zero = FpElem::from_checked_prime(BigInt::zero(), p.clone());
            let m: Vec<Vec<FpElem>> = ar
                .m_matrix
                .iter()
                .map(|r| r.iter().map(|v| scalar_to_fp(v, p)).collect())
                .collect();
            let b: Vec<FpElem> = ar.b_rhs.iter().map(|v| scalar_to_fp(v, p)).collect();
            let r_mat: Vec<Vec<FpElem>> = ar
                .r_matrix
                .iter()
                .map(|r| r.iter().map(|v| scalar_to_fp(v, p)).collect())
                .collect();
            match solve_affine_field(&m, &b, ar.num_vars, &zero) {
                Ok(AffineSolutionField::Inconsistent { .. }) => Ok((false, None, None)),
                Ok(AffineSolutionField::Consistent { kernel_basis, .. }) => {
                    compute_restriction_dims(&r_mat, &kernel_basis, &zero)
                }
                Err(e) => Err(SilenceReason::from_algebra_with(e, |err| {
                    SilenceReason::FiniteEnumerationOutOfScope {
                        detail: format!("{err:?}"),
                    }
                })),
            }
        }
        CoeffDomain::Z => {
            let to_z = |lit: &ScalarLit| -> BigInt {
                match lit {
                    ScalarLit::Z(n) => n.clone(),
                    _ => BigInt::zero(),
                }
            };
            let m: Vec<Vec<BigInt>> = ar
                .m_matrix
                .iter()
                .map(|r| r.iter().map(to_z).collect())
                .collect();
            let b: Vec<BigInt> = ar.b_rhs.iter().map(to_z).collect();
            let r_mat: Vec<Vec<Rat>> = ar
                .r_matrix
                .iter()
                .map(|r| r.iter().map(scalar_to_rat).collect())
                .collect();
            match solve_affine_z(&m, &b, ar.num_vars) {
                Ok(AffineSolutionZ::Inconsistent { .. }) => Ok((false, None, None)),
                Ok(AffineSolutionZ::Consistent { kernel_basis, .. }) => {
                    let ker_rat: Vec<Vec<Rat>> = kernel_basis
                        .iter()
                        .map(|kv| kv.iter().map(|x| Rat::from_int(x.clone())).collect())
                        .collect();
                    compute_restriction_dims(&r_mat, &ker_rat, &Rat::zero())
                }
                Err(e) => Err(SilenceReason::from_algebra_with(e, |err| {
                    SilenceReason::FiniteEnumerationOutOfScope {
                        detail: format!("{err:?}"),
                    }
                })),
            }
        }
    }
}

fn compute_restriction_dims<C: FieldCoeff>(
    r_mat: &[Vec<C>],
    kernel_basis: &[Vec<C>],
    zero: &C,
) -> Result<(bool, Option<usize>, Option<usize>), SilenceReason> {
    let ker_dim = kernel_basis.len();
    let sc_rows = r_mat.len();
    let image_cols: Vec<Vec<C>> = kernel_basis
        .iter()
        .map(|k_vec| {
            r_mat
                .iter()
                .map(|r_row| {
                    let mut sum = C::zero_like(zero);
                    for (r, k) in r_row.iter().zip(k_vec) {
                        sum = sum.add_ref(&r.mul_ref(k));
                    }
                    sum
                })
                .collect()
        })
        .collect();
    let img_dim = rank_over_field(&image_cols, sc_rows, zero).map_err(|e| {
        SilenceReason::FiniteEnumerationOutOfScope {
            detail: format!("{e:?}"),
        }
    })?;
    let fiber_dim = ker_dim.saturating_sub(img_dim);
    // 定理 18.18: |im r| = 1 (img_dim == 0) かつ唯一ファイバーが一元集合 (fiber_dim == 0) のとき大域一意修復存在。
    Ok((
        img_dim == 0 && fiber_dim == 0,
        Some(img_dim),
        Some(fiber_dim),
    ))
}

fn is_positive_existential_formula(f: &crate::ir::partial::PartialFormula) -> bool {
    use crate::ir::partial::PartialFormula;
    match f {
        PartialFormula::Eq(_, _)
        | PartialFormula::Rel { .. }
        | PartialFormula::Graph { .. }
        | PartialFormula::Defined { .. } => true,
        PartialFormula::And(list) | PartialFormula::Or(list) => {
            list.iter().all(is_positive_existential_formula)
        }
        PartialFormula::Exists { body, .. } => is_positive_existential_formula(body),
        PartialFormula::Not(_) | PartialFormula::Forall { .. } => false,
    }
}

fn bool_str(b: bool) -> &'static str {
    if b { "true" } else { "false" }
}
