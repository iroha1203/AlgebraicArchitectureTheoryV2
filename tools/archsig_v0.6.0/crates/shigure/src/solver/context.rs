//! SHIGURE solver の実行コンテキスト・適用条件検査・由来構築ヘルパ。

use crate::algebra::{
    ExprBindings, MonomialOrder, Poly, Rat, RingCoeff, VarOrder, require_closed_for_interaction,
};
use crate::ir::change::{EditableTarget, EvalCondition, PointDomain};
use crate::ir::presentation::Presentation;
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{
    ApplicabilityCheck, EmptyWitness, InteractionSummary, RestoredArtifact, ShigureOutcome,
    SilenceReason, Verdict,
};
use crate::ir::term::CoeffDomain;
use crate::ir::validate::CheckedShigureTask;
use crate::solver::ShigureQueryKind;
use crate::solver::preservation::{collect_all_provenance_origins, map_algebra_silence};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};
use std::collections::BTreeSet;

/// 実行中の共通メタデータ（係数域・点集合域・適用条件検査・由来）を束ねるコンテキスト。
#[derive(Clone)]
pub(crate) struct SolveCtx {
    pub coeff_domain: CoeffDomain,
    pub point_domain: PointDomain,
    pub checks: Vec<ApplicabilityCheck>,
    pub provenance: Provenance,
}

impl SolveCtx {
    pub(crate) fn established(
        self,
        residual_ideal: Vec<String>,
        restored: Option<RestoredArtifact>,
        interaction: Option<InteractionSummary>,
    ) -> ShigureOutcome {
        ShigureOutcome {
            verdict: Verdict::Established,
            coeff_domain: self.coeff_domain,
            point_domain: self.point_domain,
            applicability: self.checks,
            provenance: self.provenance,
            residual_ideal,
            empty_witness: None,
            restored,
            interaction,
            diagram: None,
            path: None,
            transfer: None,
        }
    }

    pub(crate) fn refuted(
        self,
        residual_ideal: Vec<String>,
        empty_witness: Option<EmptyWitness>,
    ) -> ShigureOutcome {
        ShigureOutcome {
            verdict: Verdict::Refuted,
            coeff_domain: self.coeff_domain,
            point_domain: self.point_domain,
            applicability: self.checks,
            provenance: self.provenance,
            residual_ideal,
            empty_witness,
            restored: None,
            interaction: None,
            diagram: None,
            path: None,
            transfer: None,
        }
    }

    pub(crate) fn undetermined(
        self,
        residual_ideal: Vec<String>,
        reason: SilenceReason,
    ) -> ShigureOutcome {
        ShigureOutcome {
            verdict: Verdict::Undetermined(reason),
            coeff_domain: self.coeff_domain,
            point_domain: self.point_domain,
            applicability: self.checks,
            provenance: self.provenance,
            residual_ideal,
            empty_witness: None,
            restored: None,
            interaction: None,
            diagram: None,
            path: None,
            transfer: None,
        }
    }
}

pub(crate) fn resolve_point_domain(
    task: &CheckedShigureTask,
    query: ShigureQueryKind,
) -> PointDomain {
    if query != ShigureQueryKind::SemanticPreservation
        && let Some(cond) = task.eval_condition()
    {
        return cond.point_domain.clone();
    }
    if query == ShigureQueryKind::InteractionAnalysis {
        return PointDomain::UniversalRing;
    }
    match &task.change_spec().coeff_domain {
        CoeffDomain::Q | CoeffDomain::Z => PointDomain::AlgebraicClosure,
        CoeffDomain::Fp(p) => PointDomain::FiniteFieldPoints(p.clone()),
    }
}

pub(crate) fn build_outcome_provenance(
    task: &CheckedShigureTask,
    query: ShigureQueryKind,
) -> Provenance {
    let eval_origins: Vec<_> = if query == ShigureQueryKind::SemanticPreservation {
        Vec::new()
    } else {
        task.eval_condition()
            .map(|c| {
                let mut out = c.provenance.origins.clone();
                for item in c
                    .evaluations
                    .iter()
                    .chain(&c.equations)
                    .chain(&c.invertibles)
                {
                    if let Some(o) = &item.provenance {
                        out.push(o.clone());
                    }
                }
                out
            })
            .unwrap_or_default()
    };
    let mut change_origins = task.change_spec().provenance.origins.clone();
    for p in &task.change_spec().parameters {
        if let Some(o) = &p.provenance {
            change_origins.push(o.clone());
        }
    }
    let origins = collect_all_provenance_origins(task.pair(), &change_origins, &eval_origins);
    let clauses = match query {
        ShigureQueryKind::SemanticPreservation => vec![
            MathClause::G139P0P1,
            MathClause::G140P0Dot1,
            MathClause::G140A2,
            MathClause::G140P1,
            MathClause::G140P3P5,
            MathClause::G141D5,
        ],
        ShigureQueryKind::ConditionalSolutionSpace => vec![
            MathClause::G139P0P1,
            MathClause::G140A2,
            MathClause::G140E1E2,
            MathClause::G140P6,
            MathClause::G141D1,
            MathClause::G141D4,
            MathClause::G141D5,
        ],
        ShigureQueryKind::InteractionAnalysis => vec![
            MathClause::G139P0P1,
            MathClause::G140A2,
            MathClause::G141D1,
            MathClause::G141F10F12,
        ],
    };
    Provenance::new(origins, clauses)
}

pub(crate) fn check_common_applicability(
    task: &CheckedShigureTask,
    query: ShigureQueryKind,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<(), SilenceReason> {
    let missing = task.unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::G140P0Dot1,
            format!("missing slots: {}", missing.join(", ")),
        ));
        return Err(SilenceReason::UnobservedDependency { slots: missing });
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::G140P0Dot1,
    ));

    for pres in [&task.pair().before, &task.pair().after] {
        for sort in &pres.sorts {
            if sort.rank != 1 {
                let detail = format!(
                    "sort `{}` in `{}` has rank {}, but scalar polynomial engine requires rank == 1",
                    sort.name, pres.name, sort.rank
                );
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
    checks.push(ApplicabilityCheck::passed(
        "sort_rank_one_required",
        MathClause::G139P0P1,
    ));

    // 固定参照表示 `before` は探索パラメータを含まないこと（G-140 E1）。
    let before_params = collect_presentation_params(&task.pair().before);
    if !before_params.is_empty() {
        let detail = format!(
            "fixed reference presentation `{}` must not depend on search parameters: {}",
            task.pair().before.name,
            before_params.into_iter().collect::<Vec<_>>().join(", ")
        );
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
    checks.push(ApplicabilityCheck::passed(
        "before_presentation_must_be_parameter_free",
        MathClause::G140E1E2,
    ));

    for target in &task.change_spec().editable {
        let target_pres = match target {
            EditableTarget::OperationExpr { presentation, .. }
            | EditableTarget::RepresentationLaw { presentation, .. } => Some(presentation.as_str()),
            EditableTarget::StateComparisonExpr { .. } => None,
        };
        if target_pres == Some(task.pair().before.name.as_str()) {
            let detail = format!(
                "editable target references fixed reference presentation `{}`",
                task.pair().before.name
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
    checks.push(ApplicabilityCheck::passed(
        "editable_target_must_be_after",
        MathClause::G140E1E2,
    ));

    if query == ShigureQueryKind::InteractionAnalysis
        && let Some(cond) = task.eval_condition()
    {
        if let Err(reason) = require_closed_for_interaction(!cond.is_purely_closed()) {
            checks.push(ApplicabilityCheck::failed(
                "closed_condition_for_interaction",
                MathClause::G141F10F12,
                reason.code(),
            ));
            return Err(reason);
        }
        // F4: G-141 F11 の相互作用解析は UniversalRing（全可換環上の多項式恒等式）専用。
        if cond.point_domain != PointDomain::UniversalRing {
            let detail = format!(
                "coordinate-plane interaction analysis (G-141 F11) requires point_domain `universal_ring`, got `{}`",
                cond.point_domain
            );
            checks.push(ApplicabilityCheck::failed(
                "universal_ring_required_for_interaction",
                MathClause::G141F10F12,
                detail.clone(),
            ));
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "universal_ring_required_for_interaction".to_owned(),
                detail,
            });
        }
    }

    Ok(())
}

pub(crate) fn guard_z_quotient_or_universal(
    has_source_laws: bool,
    eval_cond: Option<&EvalCondition>,
    ctx: &SolveCtx,
) -> Option<ShigureOutcome> {
    if ctx.coeff_domain == CoeffDomain::Z
        && has_source_laws
        && ctx.point_domain != PointDomain::AlgebraicClosure
    {
        let mut c = ctx.clone();
        let reason = SilenceReason::QuotientIdealOutOfScope {
            detail: "parametric quotient state-law membership over Z (with possible Z-torsion) is out of scope; use Q or algebraic_closure".to_owned(),
        };
        c.checks.push(ApplicabilityCheck::failed(
            "z_quotient_out_of_scope",
            MathClause::G141D5,
            reason.code(),
        ));
        return Some(c.undetermined(vec![], reason));
    }
    if ctx.point_domain == PointDomain::UniversalRing {
        if ctx.coeff_domain == CoeffDomain::Z {
            let mut c = ctx.clone();
            let reason = SilenceReason::ApplicabilityConditionNotMet {
                condition: "universal_ring_solution_space_out_of_scope".to_owned(),
                detail: "UniversalRing solution-space restoration over Z cannot be approximated by rational Q-sections".to_owned(),
            };
            c.checks.push(ApplicabilityCheck::failed(
                "universal_ring_solution_space_out_of_scope",
                MathClause::G141D1,
                reason.code(),
            ));
            return Some(c.undetermined(vec![], reason));
        }
        if has_source_laws {
            let mut c = ctx.clone();
            let reason = SilenceReason::QuotientIdealOutOfScope {
                detail: "quotient ideal membership over arbitrary non-reduced commutative rings (UniversalRing) is out of scope; use algebraic_closure".to_owned(),
            };
            c.checks.push(ApplicabilityCheck::failed(
                "universal_ring_quotient_out_of_scope",
                MathClause::G141D5,
                reason.code(),
            ));
            return Some(c.undetermined(vec![], reason));
        }
        if eval_cond.is_some_and(|cond| !cond.is_purely_closed()) {
            let mut c = ctx.clone();
            let reason = SilenceReason::ApplicabilityConditionNotMet {
                condition: "universal_ring_closed_equations_only".to_owned(),
                detail: "open/invertible conditions cannot be evaluated uniformly over all rings including the zero ring".to_owned(),
            };
            c.checks.push(ApplicabilityCheck::failed(
                "universal_ring_closed_equations_only",
                MathClause::G141D1,
                reason.code(),
            ));
            return Some(c.undetermined(vec![], reason));
        }
    }
    None
}

pub(crate) fn validate_eval_map_expressions(
    cond: &EvalCondition,
    param_bind: &ExprBindings,
    domain: &CoeffDomain,
) -> Result<(), SilenceReason> {
    for item in &cond.evaluations {
        match domain {
            CoeffDomain::Q => {
                Poly::from_expr_q(&item.expr, param_bind).map_err(map_algebra_silence)?;
            }
            CoeffDomain::Z => {
                Poly::from_expr_z(&item.expr, param_bind).map_err(map_algebra_silence)?;
            }
            CoeffDomain::Fp(m) => {
                Poly::from_expr_fp(&item.expr, param_bind, m).map_err(map_algebra_silence)?;
            }
        }
    }
    Ok(())
}

pub(crate) fn clear_denominators_to_z(polys: &[Poly<Rat>]) -> Vec<Poly<BigInt>> {
    polys
        .iter()
        .map(|p| {
            let mut lcm = BigInt::one();
            for coeff in p.terms().values() {
                lcm = lcm.lcm(coeff.den());
            }
            let mut out = Poly::zero(p.num_vars(), BigInt::zero());
            for (mono, coeff) in p.terms() {
                let scaled = coeff.num() * (&lcm / coeff.den());
                out.add_term(mono.clone(), scaled);
            }
            out
        })
        .collect()
}

pub(crate) fn display_polys<C: RingCoeff>(polys: &[Poly<C>], vars: &VarOrder) -> Vec<String> {
    polys
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| p.display(vars, MonomialOrder::Grevlex))
        .collect()
}

fn collect_presentation_params(pres: &Presentation) -> BTreeSet<String> {
    let mut params = BTreeSet::new();
    for ph in &pres.phases {
        for l in &ph.state_laws {
            l.polynomial.collect_params(&mut params);
        }
    }
    for op in &pres.operations {
        for dlaw in &op.domain_laws {
            dlaw.polynomial.collect_params(&mut params);
        }
        for expr in op.updates.values() {
            expr.collect_params(&mut params);
        }
    }
    for obs in &pres.observations {
        for expr in &obs.components {
            expr.collect_params(&mut params);
        }
    }
    params
}
