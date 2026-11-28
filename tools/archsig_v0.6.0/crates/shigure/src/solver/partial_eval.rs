//! AAT 第18章（部分提示・欠測と開領域の確定評価）の計算核入口
//! （`shigure_partial`）。

use crate::ir::change::PointDomain;
use crate::ir::partial::{CheckedPartialTask, PartialRepresentation};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase5_obs::PartialOutcomeDetail;
use crate::ir::term::CoeffDomain;
use crate::solver::partial_affine::analyze_affine_partial;
use crate::solver::partial_completions::analyze_finite_partial;
use crate::solver::partial_open::{analyze_open_domain, analyze_quantifier_hierarchy};

/// `shigure_partial`（第18章）の計算核入口。
pub fn solve_partial_task(task: &CheckedPartialTask) -> ShigureOutcome {
    let provenance = with_ch18_clauses(task.provenance());
    let mut checks = Vec::new();
    let (coeff_domain, point_domain) = match task.representation() {
        PartialRepresentation::Affine(aff) => {
            let pd = match &aff.coeff_domain {
                CoeffDomain::Q => PointDomain::RationalPoints,
                CoeffDomain::Z => PointDomain::IntegerPoints,
                CoeffDomain::Fp(p) => PointDomain::FiniteFieldPoints(p.clone()),
            };
            (aff.coeff_domain.clone(), pd)
        }
        _ => (CoeffDomain::Z, PointDomain::RationalPoints),
    };

    let missing = task.undeclared_unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::AatCh18Def18Dot1,
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
        MathClause::AatCh18Def18Dot1,
    ));

    let comp_res = match task.representation() {
        PartialRepresentation::FiniteTable(fin) => {
            analyze_finite_partial(fin, task.eval_laws(), &mut checks)
        }
        PartialRepresentation::Affine(aff) => analyze_affine_partial(aff, &mut checks),
        PartialRepresentation::UnsupportedClass { description } => {
            checks.push(ApplicabilityCheck::failed(
                "supported_completion_class",
                MathClause::AatCh18Def18Dot4,
                description.clone(),
            ));
            return build_outcome(
                Verdict::Undetermined(SilenceReason::UnsupportedCompletionClass {
                    detail: description.clone(),
                }),
                coeff_domain,
                point_domain,
                checks,
                provenance,
                None,
            );
        }
    };

    let comp = match comp_res {
        Ok(c) => c,
        Err(reason) => {
            return build_outcome(
                Verdict::Undetermined(reason),
                coeff_domain,
                point_domain,
                checks,
                provenance,
                None,
            );
        }
    };

    let quantifier_hierarchy = match task.quantifier_spec() {
        Some(q) => match analyze_quantifier_hierarchy(q, &mut checks) {
            Ok(detail) => Some(detail),
            Err(reason) => {
                return build_outcome(
                    Verdict::Undetermined(reason),
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    None,
                );
            }
        },
        None => None,
    };

    let open_domain = match task.open_domain() {
        Some(od) => match analyze_open_domain(od, &mut checks) {
            Ok(detail) => Some(detail),
            Err(reason) => {
                return build_outcome(
                    Verdict::Undetermined(reason),
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    None,
                );
            }
        },
        None => None,
    };

    let required_law_refuted = task.eval_laws().iter().any(|law| {
        if !law.is_required_law {
            return false;
        }
        comp.law_evaluations
            .iter()
            .find(|s| s.law_name == law.name)
            .is_some_and(|s| {
                s.supervaluation == "false"
                    || s.conditional_conclusion_eval.as_deref()
                        == Some("refuted_on_antecedent_domain")
            })
    });

    let affine_equation_refuted = matches!(task.representation(), PartialRepresentation::Affine(_))
        && comp
            .law_evaluations
            .iter()
            .any(|s| s.supervaluation == "false");

    let verdict = if !comp.consistent || required_law_refuted || affine_equation_refuted {
        Verdict::Refuted
    } else {
        Verdict::Established
    };

    let detail = PartialOutcomeDetail {
        completion_consistent: comp.consistent,
        completion_count: comp.completion_count,
        minimal_inconsistent_subsets: comp.minimal_inconsistent_subsets,
        mus_verified: comp.mus_verified,
        law_evaluations: comp.law_evaluations,
        kleene_soundness_verified: comp.kleene_soundness_verified,
        quantifier_hierarchy,
        open_domain,
    };

    build_outcome(
        verdict,
        coeff_domain,
        point_domain,
        checks,
        provenance,
        Some(detail),
    )
}

fn with_ch18_clauses(base: &Provenance) -> Provenance {
    let mut prov = base.clone();
    for clause in [
        MathClause::AatCh18Def18Dot1,
        MathClause::AatCh18Thm18Dot3,
        MathClause::AatCh18Def18Dot4,
        MathClause::AatCh18Thm18Dot6,
        MathClause::AatCh18Prop18Dot9,
        MathClause::AatCh18Prop18Dot11,
        MathClause::AatCh18Thm18Dot12,
        MathClause::AatCh18Prop18Dot14,
        MathClause::AatCh18Thm18Dot16,
        MathClause::AatCh18Thm18Dot18,
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
    partial: Option<PartialOutcomeDetail>,
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
        partial,
        revision: None,
        multisource: None,
    }
}
