//! 一段変更経路探索・連結・細分化ソルバ入口（`CheckedPathTask` -> `ShigureOutcome`）。

use crate::ir::change::EvalCondition;
use crate::ir::morphism::MorphismDirection;
use crate::ir::path::{CheckedPathTask, PathKind, PathQueryMode};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, EmptyWitness, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_ext::{
    PathOutcomeDetail, PathOutcomeKind, RejectedPathCandidate, RestoredPath,
};
use crate::ir::term::CoeffDomain;
use crate::solver::common_format::{
    collect_change_and_eval_origins, collect_morphism_origins, collect_presentation_origins,
};
use crate::solver::common_solve::resolve_consistent_point_domain;
use crate::solver::path_fixed::solve_fixed_change_path;
use crate::solver::path_protocol::solve_enlarged_protocol_path;
use std::collections::BTreeSet;

/// 有限経路候補列挙の探索予算（超過時は無界／予算超過として沈黙する）。
pub(crate) const MAX_PATH_CANDIDATES: usize = 512;

/// 検証済み経路タスク `CheckedPathTask` を解き、`PathOutcomeDetail` 付き `ShigureOutcome` を返す。
pub fn solve_path_task(task: &CheckedPathTask) -> ShigureOutcome {
    let spec = task.spec();
    let coeff_domain = &spec.change_spec.coeff_domain;
    let mut all_evals: Vec<&EvalCondition> = Vec::new();
    if let Some(ec) = task.eval_condition() {
        all_evals.push(ec);
    }
    for r in &spec.rules {
        if let Some(rec) = &r.eval_condition {
            all_evals.push(rec);
        }
    }

    let provenance = build_path_provenance(task, &all_evals);
    let path_kind = match spec.kind {
        PathKind::FixedProtocolChangePath => PathOutcomeKind::FixedProtocolChangePath,
        PathKind::EnlargedProtocolExecutionPath => PathOutcomeKind::EnlargedProtocolExecutionPath,
    };
    let mode_wire = path_query_mode_wire(&spec.query_mode).to_owned();

    let point_domain = match resolve_consistent_point_domain(coeff_domain, &all_evals) {
        Ok(pd) => pd,
        Err(reason) => {
            return undetermined_path(
                coeff_domain,
                &crate::ir::change::PointDomain::AlgebraicClosure,
                vec![ApplicabilityCheck::failed(
                    "consistent_point_domain",
                    MathClause::G140F2,
                    reason.code(),
                )],
                provenance,
                vec![],
                path_kind,
                spec.direction,
                mode_wire,
                spec.length,
                None,
                vec![],
                vec![],
                reason,
            );
        }
    };

    let mut checks = Vec::new();
    let missing = task.unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::G140P0Dot1,
            format!("missing slots: {}", missing.join(", ")),
        ));
        return undetermined_path(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            vec![],
            path_kind,
            spec.direction,
            mode_wire,
            spec.length,
            None,
            vec![],
            vec![],
            SilenceReason::UnobservedDependency { slots: missing },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::G140P0Dot1,
    ));

    let sort_err = spec
        .vertices
        .values()
        .chain(
            spec.protocol
                .iter()
                .flat_map(|p| [&p.comparison.before, &p.comparison.after]),
        )
        .find_map(|pres| {
            pres.sorts
                .iter()
                .find(|s| s.rank != 1)
                .map(|s| (pres.name.as_str(), s.name.as_str(), s.rank))
        });
    if let Some((pname, sname, rank)) = sort_err {
        let detail = format!("sort `{sname}` in `{pname}` has rank {rank}, expected 1");
        checks.push(ApplicabilityCheck::failed(
            "sort_rank_one_required",
            MathClause::G139P0P1,
            detail.clone(),
        ));
        return undetermined_path(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            vec![],
            path_kind,
            spec.direction,
            mode_wire,
            spec.length,
            None,
            vec![],
            vec![],
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "sort_rank_one_required".to_owned(),
                detail,
            },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "sort_rank_one_required",
        MathClause::G139P0P1,
    ));

    if matches!(
        spec.query_mode,
        PathQueryMode::Find | PathQueryMode::Subdivide { .. }
    ) && spec.length.is_none()
    {
        let reason = SilenceReason::UnboundedSearchOutOfScope {
            detail: "path search/subdivision requires an explicit finite `length` bound".to_owned(),
        };
        checks.push(ApplicabilityCheck::failed(
            "explicit_finite_path_length",
            MathClause::G140F2,
            reason.code(),
        ));
        return undetermined_path(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            vec![],
            path_kind,
            spec.direction,
            mode_wire,
            None,
            None,
            vec![],
            vec![],
            reason,
        );
    }

    match spec.kind {
        PathKind::EnlargedProtocolExecutionPath => {
            solve_enlarged_protocol_path(task, &point_domain, checks, provenance)
        }
        PathKind::FixedProtocolChangePath => {
            solve_fixed_change_path(task, &point_domain, checks, provenance)
        }
    }
}

pub(crate) fn path_query_mode_wire(mode: &PathQueryMode) -> &'static str {
    match mode {
        PathQueryMode::Find => "find",
        PathQueryMode::Concatenate { .. } => "concatenate",
        PathQueryMode::Subdivide { .. } => "subdivide",
    }
}

pub(crate) fn build_path_provenance(
    task: &CheckedPathTask,
    eval_conds: &[&EvalCondition],
) -> Provenance {
    let spec = task.spec();
    let mut set = BTreeSet::new();
    for o in &spec.provenance.origins {
        set.insert(o.clone());
    }
    for pres in spec.vertices.values() {
        collect_presentation_origins(pres, &mut set);
    }
    for r in &spec.rules {
        if let Some(o) = &r.provenance {
            set.insert(o.clone());
        }
        for g in &r.param_guards {
            if let Some(o) = &g.provenance {
                set.insert(o.clone());
            }
        }
        collect_morphism_origins(&r.morphism, &mut set);
    }
    if let PathQueryMode::Subdivide { target_edge } = &spec.query_mode {
        collect_morphism_origins(target_edge, &mut set);
    }
    if let Some(proto) = &spec.protocol {
        collect_presentation_origins(&proto.comparison.before, &mut set);
        collect_presentation_origins(&proto.comparison.after, &mut set);
        for sc in &proto.comparison.state_comparisons {
            if let Some(o) = &sc.provenance {
                set.insert(o.clone());
            }
        }
        for tw in &proto.comparison.word_translation.entries {
            if let Some(o) = &tw.provenance {
                set.insert(o.clone());
            }
        }
        for l in proto.start_laws.iter().chain(&proto.end_laws) {
            if let Some(o) = &l.provenance {
                set.insert(o.clone());
            }
        }
    }
    collect_change_and_eval_origins(&spec.change_spec, eval_conds, &mut set);
    Provenance::new(
        set.into_iter().collect(),
        vec![
            MathClause::G139P0P1,
            MathClause::G140P0Dot1,
            MathClause::G140A2,
            MathClause::G140F2,
            MathClause::G140F3,
            MathClause::G140F3Dot1,
            MathClause::G140P5Dot1,
            MathClause::G140P5Dot2,
            MathClause::G141D1,
            MathClause::G141D4,
            MathClause::G141D5,
        ],
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn undetermined_path(
    coeff_domain: &CoeffDomain,
    point_domain: &crate::ir::change::PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    residual_ideal: Vec<String>,
    path_kind: PathOutcomeKind,
    direction: MorphismDirection,
    query_mode: String,
    length: Option<usize>,
    protocol_preservation_verified: Option<bool>,
    valid_paths: Vec<RestoredPath>,
    rejected_candidates: Vec<RejectedPathCandidate>,
    reason: SilenceReason,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict: Verdict::Undetermined(reason),
        coeff_domain: coeff_domain.clone(),
        point_domain: point_domain.clone(),
        applicability,
        provenance,
        residual_ideal,
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: Some(PathOutcomeDetail {
            path_kind,
            direction,
            query_mode,
            length,
            protocol_preservation_verified,
            valid_paths,
            rejected_candidates,
        }),
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn refuted_path(
    coeff_domain: &CoeffDomain,
    point_domain: &crate::ir::change::PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    residual_ideal: Vec<String>,
    empty_witness: Option<EmptyWitness>,
    path_kind: PathOutcomeKind,
    direction: MorphismDirection,
    query_mode: String,
    length: Option<usize>,
    protocol_preservation_verified: Option<bool>,
    rejected_candidates: Vec<RejectedPathCandidate>,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict: Verdict::Refuted,
        coeff_domain: coeff_domain.clone(),
        point_domain: point_domain.clone(),
        applicability,
        provenance,
        residual_ideal,
        empty_witness,
        restored: None,
        interaction: None,
        diagram: None,
        path: Some(PathOutcomeDetail {
            path_kind,
            direction,
            query_mode,
            length,
            protocol_preservation_verified,
            valid_paths: vec![],
            rejected_candidates,
        }),
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn established_path(
    coeff_domain: &CoeffDomain,
    point_domain: &crate::ir::change::PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    residual_ideal: Vec<String>,
    path_kind: PathOutcomeKind,
    direction: MorphismDirection,
    query_mode: String,
    length: Option<usize>,
    protocol_preservation_verified: Option<bool>,
    valid_paths: Vec<RestoredPath>,
    rejected_candidates: Vec<RejectedPathCandidate>,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict: Verdict::Established,
        coeff_domain: coeff_domain.clone(),
        point_domain: point_domain.clone(),
        applicability,
        provenance,
        residual_ideal,
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: Some(PathOutcomeDetail {
            path_kind,
            direction,
            query_mode,
            length,
            protocol_preservation_verified,
            valid_paths,
            rejected_candidates,
        }),
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
    }
}
