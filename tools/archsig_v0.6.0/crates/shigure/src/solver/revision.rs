//! AAT 第19章前半（追記単調性・改訂スパン・無効化錐 $\operatorname{Cone}(\Delta)$・錐外射影不変性・
//! 作用素/右辺分離 SNF 再利用）の計算核（`shigure_revision`）。

use crate::algebra::poly::AlgebraError;
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::algebra::snf::{SnfFactorizationQ, SnfFactorizationZ};
use crate::ir::change::PointDomain;
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ReevalCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase5_rev::{RevisionOutcomeDetail, RevisionProbeResult, SnfReuseDetail};
use crate::ir::revision::{
    CheckedRevisionTask, RevisionConstraintSpec, RevisionCoordSpec, RevisionEvalProbe,
    RevisionKind, RevisionPredicate, SnfRevisionSpec,
};
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::solver::partial_affine::{scalar_to_fp, scalar_to_rat};
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};

/// 係数域ごとの正規化済みスカラー値（未約分有理数や $\mathbb{F}_p$ 剰余を正規表現で比較する）。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum NormScalar {
    Z(BigInt),
    Q(Rat),
    Fp(FpElem),
}

impl NormScalar {
    pub(super) fn from_lit(lit: &ScalarLit, domain: &CoeffDomain) -> Result<Self, SilenceReason> {
        match domain {
            CoeffDomain::Z => match lit {
                ScalarLit::Z(n) => Ok(NormScalar::Z(n.clone())),
                _ => Err(SilenceReason::UnsupportedCoeffRing {
                    domain: domain.clone(),
                    detail: format!("non-integer literal in Z domain: {lit:?}"),
                }),
            },
            CoeffDomain::Q => match lit {
                ScalarLit::Z(_) | ScalarLit::Q { .. } => Ok(NormScalar::Q(scalar_to_rat(lit))),
                ScalarLit::Fp { .. } => Err(SilenceReason::UnsupportedCoeffRing {
                    domain: domain.clone(),
                    detail: format!("finite-field literal in Q domain: {lit:?}"),
                }),
            },
            CoeffDomain::Fp(p) => match lit {
                ScalarLit::Z(_) | ScalarLit::Fp { .. } => Ok(NormScalar::Fp(scalar_to_fp(lit, p))),
                ScalarLit::Q { .. } => Err(SilenceReason::UnsupportedCoeffRing {
                    domain: domain.clone(),
                    detail: format!("rational literal in Fp domain: {lit:?}"),
                }),
            },
        }
    }

    pub(super) fn zero(domain: &CoeffDomain) -> Self {
        match domain {
            CoeffDomain::Z => NormScalar::Z(BigInt::zero()),
            CoeffDomain::Q => NormScalar::Q(Rat::zero()),
            CoeffDomain::Fp(p) => {
                NormScalar::Fp(FpElem::from_checked_prime(BigInt::zero(), p.clone()))
            }
        }
    }

    pub(super) fn add_ref(&self, rhs: &Self) -> Self {
        match (self, rhs) {
            (NormScalar::Z(a), NormScalar::Z(b)) => NormScalar::Z(a + b),
            (NormScalar::Q(a), NormScalar::Q(b)) => NormScalar::Q(a.add_ref(b)),
            (NormScalar::Fp(a), NormScalar::Fp(b)) => NormScalar::Fp(a.add_ref(b)),
            _ => self.clone(),
        }
    }

    pub(super) fn mul_ref(&self, rhs: &Self) -> Self {
        match (self, rhs) {
            (NormScalar::Z(a), NormScalar::Z(b)) => NormScalar::Z(a * b),
            (NormScalar::Q(a), NormScalar::Q(b)) => NormScalar::Q(a.mul_ref(b)),
            (NormScalar::Fp(a), NormScalar::Fp(b)) => NormScalar::Fp(a.mul_ref(b)),
            _ => self.clone(),
        }
    }

    pub(super) fn is_zero(&self) -> bool {
        match self {
            NormScalar::Z(n) => n.is_zero(),
            NormScalar::Q(q) => q.coeff_is_zero(),
            NormScalar::Fp(f) => f.coeff_is_zero(),
        }
    }

    pub(super) fn display_str(&self) -> String {
        match self {
            NormScalar::Z(n) => n.to_string(),
            NormScalar::Q(q) => q.to_string(),
            NormScalar::Fp(f) => format!("{} mod {}", f.value(), f.modulus()),
        }
    }
}

pub(super) fn constraint_holds(
    con: &RevisionConstraintSpec,
    env: &BTreeMap<String, NormScalar>,
    domain: &CoeffDomain,
) -> Result<bool, SilenceReason> {
    match &con.predicate {
        RevisionPredicate::Equality(a, b) => Ok(env.get(a) == env.get(b)),
        RevisionPredicate::LinearZero { terms } => {
            let mut sum = NormScalar::zero(domain);
            for (coeff, var) in terms {
                let nc = NormScalar::from_lit(coeff, domain)?;
                let nv = env
                    .get(var)
                    .expect("validated coord present in completion env");
                sum = sum.add_ref(&nc.mul_ref(nv));
            }
            Ok(sum.is_zero())
        }
        RevisionPredicate::AllowedTuples { coords, tuples } => {
            for tup in tuples {
                let mut all_eq = true;
                for (c, v) in coords.iter().zip(tup) {
                    let nv = NormScalar::from_lit(v, domain)?;
                    if env.get(c) != Some(&nv) {
                        all_eq = false;
                        break;
                    }
                }
                if all_eq {
                    return Ok(true);
                }
            }
            Ok(false)
        }
    }
}

/// 共通座標と制約集合上の有限補完を早期枝刈り付きで列挙する（`assignments` は上書きせず矛盾を即 0 補完へ落とす）。
pub(super) fn enumerate_coord_completions(
    coords: &[RevisionCoordSpec],
    fixed_assignments: &[(String, NormScalar)],
    forbidden_values: &[(String, NormScalar)],
    constraints: &[&RevisionConstraintSpec],
    domain: &CoeffDomain,
    max_completions: usize,
) -> Result<Vec<BTreeMap<String, NormScalar>>, SilenceReason> {
    let mut allowed_by_coord: Vec<(String, Vec<NormScalar>)> = Vec::with_capacity(coords.len());
    for c in coords {
        let mut domain_vals = Vec::with_capacity(c.domain_values.len());
        for v in &c.domain_values {
            domain_vals.push(NormScalar::from_lit(v, domain)?);
        }
        let fixed_for_c: Vec<&NormScalar> = fixed_assignments
            .iter()
            .filter(|(k, _)| k == &c.id)
            .map(|(_, v)| v)
            .collect();
        if let Some(&first) = fixed_for_c.first() {
            if fixed_for_c.iter().any(|&v| v != first) || !domain_vals.contains(first) {
                return Ok(vec![]);
            }
            if forbidden_values
                .iter()
                .any(|(k, fv)| k == &c.id && fv == first)
            {
                return Ok(vec![]);
            }
            allowed_by_coord.push((c.id.clone(), vec![first.clone()]));
        } else {
            let filtered: Vec<NormScalar> = domain_vals
                .into_iter()
                .filter(|v| !forbidden_values.iter().any(|(k, fv)| k == &c.id && fv == v))
                .collect();
            if filtered.is_empty() {
                return Ok(vec![]);
            }
            allowed_by_coord.push((c.id.clone(), filtered));
        }
    }

    let mut cur = BTreeMap::new();
    let mut out = Vec::new();
    backtrack_coords(
        0,
        &allowed_by_coord,
        constraints,
        domain,
        max_completions,
        &mut cur,
        &mut out,
    )?;
    Ok(out)
}

fn backtrack_coords(
    idx: usize,
    allowed_by_coord: &[(String, Vec<NormScalar>)],
    constraints: &[&RevisionConstraintSpec],
    domain: &CoeffDomain,
    max_completions: usize,
    cur: &mut BTreeMap<String, NormScalar>,
    out: &mut Vec<BTreeMap<String, NormScalar>>,
) -> Result<(), SilenceReason> {
    if !constraints
        .iter()
        .filter(|con| con.support.iter().all(|s| cur.contains_key(s)))
        .try_fold(true, |acc, con| {
            Ok::<bool, SilenceReason>(acc && constraint_holds(con, cur, domain)?)
        })?
    {
        return Ok(());
    }

    if idx == allowed_by_coord.len() {
        if out.len() >= max_completions {
            return Err(SilenceReason::FiniteEnumerationOutOfScope {
                detail: format!("completion count exceeds max_completions ({max_completions})"),
            });
        }
        out.push(cur.clone());
        return Ok(());
    }

    let (coord, candidates) = &allowed_by_coord[idx];
    for val in candidates {
        cur.insert(coord.clone(), val.clone());
        backtrack_coords(
            idx + 1,
            allowed_by_coord,
            constraints,
            domain,
            max_completions,
            cur,
            out,
        )?;
        cur.remove(coord);
    }
    Ok(())
}

/// `shigure_revision`（第19章前半）の計算核入口。
pub fn solve_revision_task(task: &CheckedRevisionTask) -> ShigureOutcome {
    let provenance = with_ch19_rev_clauses(task.provenance());
    let coeff_domain = task.coeff_domain().clone();
    let point_domain = point_domain_for(&coeff_domain);
    let mut checks = Vec::new();

    let missing = task.undeclared_unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::AatCh19Thm19Dot4,
            format!("undeclared unobserved slots: {}", missing.join(", ")),
        ));
        return build_outcome(
            Verdict::Undetermined(SilenceReason::UnobservedDependency {
                slots: missing.to_vec(),
            }),
            coeff_domain,
            point_domain,
            checks,
            provenance,
            None,
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::AatCh19Thm19Dot4,
    ));

    match solve_revision_inner(task, &coeff_domain, &mut checks) {
        Ok((verdict, detail)) => build_outcome(
            verdict,
            coeff_domain,
            point_domain,
            checks,
            provenance,
            Some(detail),
        ),
        Err(reason) => build_outcome(
            Verdict::Undetermined(reason),
            coeff_domain,
            point_domain,
            checks,
            provenance,
            None,
        ),
    }
}

fn solve_revision_inner(
    task: &CheckedRevisionTask,
    domain: &CoeffDomain,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<(Verdict, RevisionOutcomeDetail), SilenceReason> {
    let before_assign: Vec<(String, NormScalar)> = task
        .before()
        .assignments
        .iter()
        .map(|(k, v)| Ok((k.clone(), NormScalar::from_lit(v, domain)?)))
        .collect::<Result<_, SilenceReason>>()?;
    let after_assign: Vec<(String, NormScalar)> = task
        .after()
        .assignments
        .iter()
        .map(|(k, v)| Ok((k.clone(), NormScalar::from_lit(v, domain)?)))
        .collect::<Result<_, SilenceReason>>()?;

    // 定義 19.1: Extension は条件を削除せず追記のみの包含 P_1 ↪ P_2 を要求する
    if task.kind() == RevisionKind::Extension {
        let mut inclusion_ok = true;
        for (k, vb) in &before_assign {
            if !after_assign.iter().any(|(ak, av)| ak == k && av == vb) {
                inclusion_ok = false;
                break;
            }
        }
        if inclusion_ok {
            for c in &task.before().extra_constraints {
                if !task.after().extra_constraints.contains(c) {
                    inclusion_ok = false;
                    break;
                }
            }
        }
        if !inclusion_ok {
            checks.push(ApplicabilityCheck::failed(
                "revision_extension_inclusion",
                MathClause::AatCh19Prop19Dot2,
                "Extension requires P_1 ↪ P_2 without removing or overwriting records/constraints",
            ));
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "revision_extension_inclusion".to_owned(),
                detail:
                    "Extension requires P_1 ↪ P_2 without removing or overwriting prior records"
                        .to_owned(),
            });
        }
        checks.push(ApplicabilityCheck::passed(
            "revision_extension_inclusion",
            MathClause::AatCh19Prop19Dot2,
        ));
    }

    let before_cons: Vec<&RevisionConstraintSpec> = task
        .shared_constraints()
        .iter()
        .chain(&task.before().extra_constraints)
        .collect();
    let after_cons: Vec<&RevisionConstraintSpec> = task
        .shared_constraints()
        .iter()
        .chain(&task.after().extra_constraints)
        .collect();

    let comp_before = enumerate_coord_completions(
        task.coords(),
        &before_assign,
        &[],
        &before_cons,
        domain,
        task.max_completions(),
    )?;
    let comp_after = enumerate_coord_completions(
        task.coords(),
        &after_assign,
        &[],
        &after_cons,
        domain,
        task.max_completions(),
    )?;

    let before_consistent = !comp_before.is_empty();
    let after_consistent = !comp_after.is_empty();
    let both_consistent = before_consistent && after_consistent;

    // 命題 19.2: 非空追記での確定評価・条件付き適用区分保存
    let monotonicity_applicable = task.kind() == RevisionKind::Extension && both_consistent;
    let monotonicity_preserved = if monotonicity_applicable {
        let comp_before_set: BTreeSet<BTreeMap<String, NormScalar>> =
            comp_before.iter().cloned().collect();
        let comp_subset = comp_after.iter().all(|c| comp_before_set.contains(c));
        let mut probes_monotone = true;
        for p in task.probes() {
            let b_eval = eval_probe_on_completions(p, &comp_before, domain)?;
            let a_eval = eval_probe_on_completions(p, &comp_after, domain)?;
            if !probe_eval_monotone(&b_eval, &a_eval) {
                probes_monotone = false;
            }
        }
        Some(comp_subset && probes_monotone)
    } else {
        None
    };

    // 設定 19.3・定理 19.4: Δ と無効化錐 Cone(Δ) の最小不動点閉包
    let mut delta: BTreeSet<String> = task.explicit_delta_coords().iter().cloned().collect();
    for c in task.coords() {
        let b_norm = task
            .before()
            .assignments
            .get(&c.id)
            .map(|v| NormScalar::from_lit(v, domain))
            .transpose()?;
        let a_norm = task
            .after()
            .assignments
            .get(&c.id)
            .map(|v| NormScalar::from_lit(v, domain))
            .transpose()?;
        if b_norm != a_norm {
            delta.insert(c.id.clone());
        }
    }
    for bc in &task.before().extra_constraints {
        if !task.after().extra_constraints.contains(bc) {
            for s in &bc.support {
                delta.insert(s.clone());
            }
        }
    }
    for ac in &task.after().extra_constraints {
        if !task.before().extra_constraints.contains(ac) {
            for s in &ac.support {
                delta.insert(s.clone());
            }
        }
    }

    let mut cone = delta.clone();
    let all_cons: Vec<&RevisionConstraintSpec> = task
        .shared_constraints()
        .iter()
        .chain(&task.before().extra_constraints)
        .chain(&task.after().extra_constraints)
        .collect();
    loop {
        let mut changed = false;
        for con in &all_cons {
            if con.support.iter().any(|s| cone.contains(s)) {
                for s in &con.support {
                    if cone.insert(s.clone()) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    let delta_coords: Vec<String> = delta.into_iter().collect();
    let invalidation_cone: Vec<String> = cone.iter().cloned().collect();
    let outside_cone_coords: Vec<String> = task
        .coords()
        .iter()
        .filter(|c| !cone.contains(&c.id))
        .map(|c| c.id.clone())
        .collect();

    let outside_projection_equal = if both_consistent {
        let pr_b: BTreeSet<Vec<NormScalar>> = comp_before
            .iter()
            .map(|m| {
                outside_cone_coords
                    .iter()
                    .map(|k| m[k].clone())
                    .collect::<Vec<_>>()
            })
            .collect();
        let pr_a: BTreeSet<Vec<NormScalar>> = comp_after
            .iter()
            .map(|m| {
                outside_cone_coords
                    .iter()
                    .map(|k| m[k].clone())
                    .collect::<Vec<_>>()
            })
            .collect();
        Some(pr_b == pr_a)
    } else {
        None
    };

    checks.push(ApplicabilityCheck::passed(
        "invalidation_cone_computed",
        MathClause::AatCh19Thm19Dot4,
    ));

    let mut probe_results = Vec::new();
    for p in task.probes() {
        let outside_cone = p.support.iter().all(|s| !cone.contains(s));
        let before_eval = eval_probe_on_completions(p, &comp_before, domain)?;
        let after_eval = eval_probe_on_completions(p, &comp_after, domain)?;
        let invariant_satisfied = if !both_consistent || !outside_cone {
            true
        } else {
            before_eval == after_eval
        };
        probe_results.push(RevisionProbeResult {
            probe_name: p.name.clone(),
            outside_cone,
            before_eval,
            after_eval,
            invariant_satisfied,
        });
    }

    let snf_reuse = match task.snf_spec() {
        Some(snf) => Some(solve_snf_revision(snf, checks)?),
        None => None,
    };

    let probe_cone_violated = probe_results
        .iter()
        .any(|pr| pr.outside_cone && both_consistent && !pr.invariant_satisfied);
    let snf_failed = snf_reuse
        .as_ref()
        .is_some_and(|s| !s.after_solvable || !s.umv_verified || !s.reeval.matched);

    let verdict = if !after_consistent
        || monotonicity_preserved == Some(false)
        || outside_projection_equal == Some(false)
        || probe_cone_violated
        || snf_failed
    {
        Verdict::Refuted
    } else {
        Verdict::Established
    };

    Ok((
        verdict,
        RevisionOutcomeDetail {
            kind: match task.kind() {
                RevisionKind::Extension => "extension".to_owned(),
                RevisionKind::Span => "span".to_owned(),
            },
            before_consistent,
            after_consistent,
            monotonicity_applicable,
            monotonicity_preserved,
            delta_coords,
            invalidation_cone,
            outside_cone_coords,
            outside_projection_equal,
            probe_results,
            snf_reuse,
        },
    ))
}

fn eval_probe_on_completions(
    p: &RevisionEvalProbe,
    completions: &[BTreeMap<String, NormScalar>],
    domain: &CoeffDomain,
) -> Result<String, SilenceReason> {
    if completions.is_empty() {
        return Ok("empty".to_owned());
    }
    let expected = NormScalar::from_lit(&p.expected_value, domain)?;
    if let (Some(ac), Some(av)) = (&p.antecedent_coord, &p.antecedent_value) {
        let ant_val = NormScalar::from_lit(av, domain)?;
        let matching: Vec<&BTreeMap<String, NormScalar>> =
            completions.iter().filter(|m| m[ac] == ant_val).collect();
        if matching.is_empty() {
            return Ok("inapplicable".to_owned());
        }
        if matching.len() != completions.len() {
            return Ok("mixed_applicability".to_owned());
        }
        let all_t = matching.iter().all(|m| m[&p.target_coord] == expected);
        let all_f = matching.iter().all(|m| m[&p.target_coord] != expected);
        return Ok(match (all_t, all_f) {
            (true, false) => "applicable:true".to_owned(),
            (false, true) => "applicable:false".to_owned(),
            _ => "applicable:indeterminate".to_owned(),
        });
    }
    let all_t = completions.iter().all(|m| m[&p.target_coord] == expected);
    let all_f = completions.iter().all(|m| m[&p.target_coord] != expected);
    Ok(match (all_t, all_f) {
        (true, false) => "true".to_owned(),
        (false, true) => "false".to_owned(),
        _ => "indeterminate".to_owned(),
    })
}

fn probe_eval_monotone(before: &str, after: &str) -> bool {
    match before {
        "true" | "false" | "inapplicable" | "applicable:true" | "applicable:false" => {
            before == after
        }
        _ => true,
    }
}

fn solve_snf_revision(
    snf: &SnfRevisionSpec,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<SnfReuseDetail, SilenceReason> {
    if !snf.op_uniquely_determined {
        checks.push(ApplicabilityCheck::failed(
            "snf_operator_uniquely_determined",
            MathClause::AatCh19Thm19Dot7,
            "repair operator M not uniquely determined from common P_0",
        ));
        return Err(SilenceReason::OperatorNotUniquelyDetermined {
            detail: "repair operator M is not uniquely determined on common P_0".to_owned(),
        });
    }

    let same_op = normalized_matrix_equal(&snf.m_before, &snf.m_after, &snf.coeff_domain)?;
    let reuse_permitted = snf.op_in_common_p0 && snf.op_uniquely_determined && same_op;
    if !reuse_permitted && snf.force_reuse_existing_snf {
        checks.push(ApplicabilityCheck::failed(
            "snf_operator_reuse_allowed",
            MathClause::AatCh19Thm19Dot7,
            "cannot reuse prior SNF when operator M changed or left common P_0",
        ));
        return Err(SilenceReason::OperatorRevisionReuseRejected {
            detail: "forced reuse of SNF rejected after operator revision".to_owned(),
        });
    }

    checks.push(ApplicabilityCheck::passed(
        "snf_factorization_and_reuse_checked",
        MathClause::AatCh19Thm19Dot7,
    ));

    let map_alg_err = |e: AlgebraError| SilenceReason::FiniteEnumerationOutOfScope {
        detail: format!("{e:?}"),
    };

    match snf.coeff_domain {
        CoeffDomain::Z => {
            let m_b = to_bigint_matrix(&snf.m_before)?;
            let m_a = to_bigint_matrix(&snf.m_after)?;
            let r_b = to_bigint_vec(&snf.rhs_before)?;
            let r_a = to_bigint_vec(&snf.rhs_after)?;
            let target_m = if reuse_permitted { &m_b } else { &m_a };
            let factor = SnfFactorizationZ::compute(target_m, snf.num_cols).map_err(map_alg_err)?;
            let sol_a = factor.solve_rhs(&m_a, &r_a).map_err(map_alg_err)?;
            let origin_ok = if snf.origin_label_only {
                let sol_b = factor.solve_rhs(&m_b, &r_b).map_err(map_alg_err)?;
                sol_b == sol_a
            } else {
                true
            };
            let matched = factor.umv_verified
                && factor.unimodular_verified
                && factor.divisibility_verified
                && sol_a.reeval_verified
                && origin_ok;
            Ok(SnfReuseDetail {
                coeff_domain_label: "Z".to_owned(),
                rank: factor.rank,
                diagonals: factor.diagonals.iter().map(ToString::to_string).collect(),
                cokernel_torsion: factor
                    .cokernel_torsion
                    .iter()
                    .map(|d| format!("Z/{d}Z"))
                    .collect(),
                cokernel_free_rank: factor.cokernel_free_rank,
                umv_verified: factor.umv_verified,
                reused_snf: reuse_permitted,
                after_solvable: sol_a.solvable,
                after_particular: sol_a
                    .particular
                    .as_ref()
                    .map(|v| v.iter().map(ToString::to_string).collect()),
                kernel_basis: factor
                    .kernel_basis
                    .iter()
                    .map(|col| col.iter().map(ToString::to_string).collect())
                    .collect(),
                inconsistency_cert_row: sol_a.failing_row_index,
                reeval: ReevalCheck {
                    checked: true,
                    matched,
                    detail: format!(
                        "SNF(Z) rank={}, umv={}, unimod={}, div={}, rhs_reeval={}",
                        factor.rank,
                        factor.umv_verified,
                        factor.unimodular_verified,
                        factor.divisibility_verified,
                        sol_a.reeval_verified
                    ),
                },
            })
        }
        CoeffDomain::Q => {
            let m_b: Vec<Vec<Rat>> = snf
                .m_before
                .iter()
                .map(|r| r.iter().map(scalar_to_rat).collect())
                .collect();
            let m_a: Vec<Vec<Rat>> = snf
                .m_after
                .iter()
                .map(|r| r.iter().map(scalar_to_rat).collect())
                .collect();
            let r_b: Vec<Rat> = snf.rhs_before.iter().map(scalar_to_rat).collect();
            let r_a: Vec<Rat> = snf.rhs_after.iter().map(scalar_to_rat).collect();
            let target_m = if reuse_permitted { &m_b } else { &m_a };
            let factor = SnfFactorizationQ::compute(target_m, snf.num_cols).map_err(map_alg_err)?;
            let sol_a = factor.solve_rhs(&m_a, &r_a).map_err(map_alg_err)?;
            let origin_ok = if snf.origin_label_only {
                let sol_b = factor.solve_rhs(&m_b, &r_b).map_err(map_alg_err)?;
                sol_b == sol_a
            } else {
                true
            };
            let matched = factor.umv_verified
                && factor.invertible_verified
                && sol_a.reeval_verified
                && origin_ok;
            Ok(SnfReuseDetail {
                coeff_domain_label: "Q".to_owned(),
                rank: factor.rank,
                diagonals: vec!["1".to_owned(); factor.rank],
                cokernel_torsion: vec![],
                cokernel_free_rank: factor.cokernel_rank,
                umv_verified: factor.umv_verified,
                reused_snf: reuse_permitted,
                after_solvable: sol_a.solvable,
                after_particular: sol_a
                    .particular
                    .as_ref()
                    .map(|v| v.iter().map(ToString::to_string).collect()),
                kernel_basis: factor
                    .kernel_basis
                    .iter()
                    .map(|col| col.iter().map(ToString::to_string).collect())
                    .collect(),
                inconsistency_cert_row: sol_a.failing_row_index,
                reeval: ReevalCheck {
                    checked: true,
                    matched,
                    detail: format!(
                        "SNF(Q) rank={}, umv={}, inv={}, rhs_reeval={}",
                        factor.rank,
                        factor.umv_verified,
                        factor.invertible_verified,
                        sol_a.reeval_verified
                    ),
                },
            })
        }
        CoeffDomain::Fp(_) => Err(SilenceReason::UnsupportedCoeffRing {
            domain: snf.coeff_domain.clone(),
            detail: "SNF revision spec requires Z or Q coefficient domain".to_owned(),
        }),
    }
}

fn normalized_matrix_equal(
    a: &[Vec<ScalarLit>],
    b: &[Vec<ScalarLit>],
    domain: &CoeffDomain,
) -> Result<bool, SilenceReason> {
    if a.len() != b.len() {
        return Ok(false);
    }
    for (ra, rb) in a.iter().zip(b) {
        if ra.len() != rb.len() {
            return Ok(false);
        }
        for (va, vb) in ra.iter().zip(rb) {
            if NormScalar::from_lit(va, domain)? != NormScalar::from_lit(vb, domain)? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

fn to_bigint_vec(row: &[ScalarLit]) -> Result<Vec<BigInt>, SilenceReason> {
    row.iter()
        .map(|lit| match lit {
            ScalarLit::Z(n) => Ok(n.clone()),
            _ => Err(SilenceReason::UnsupportedCoeffRing {
                domain: CoeffDomain::Z,
                detail: format!("expected integer literal in Z SNF, got {lit:?}"),
            }),
        })
        .collect()
}

fn to_bigint_matrix(mat: &[Vec<ScalarLit>]) -> Result<Vec<Vec<BigInt>>, SilenceReason> {
    mat.iter().map(|r| to_bigint_vec(r)).collect()
}

pub(super) fn point_domain_for(domain: &CoeffDomain) -> PointDomain {
    match domain {
        CoeffDomain::Q => PointDomain::RationalPoints,
        CoeffDomain::Z => PointDomain::IntegerPoints,
        CoeffDomain::Fp(p) => PointDomain::FiniteFieldPoints(p.clone()),
    }
}

fn with_ch19_rev_clauses(base: &Provenance) -> Provenance {
    let mut prov = base.clone();
    for clause in [
        MathClause::AatCh19Prop19Dot2,
        MathClause::AatCh19Thm19Dot4,
        MathClause::AatCh19Thm19Dot7,
    ] {
        if !prov.clauses.contains(&clause) {
            prov.clauses.push(clause);
        }
    }
    prov
}

fn build_outcome(
    verdict: Verdict,
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    revision: Option<RevisionOutcomeDetail>,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict,
        coeff_domain,
        point_domain,
        applicability,
        provenance,
        residual_ideal: vec![],
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: None,
        occurrence: None,
        partial: None,
        revision,
        multisource: None,
    }
}
