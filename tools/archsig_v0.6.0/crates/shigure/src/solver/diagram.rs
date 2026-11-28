//! 固定図式補完ソルバ（`CheckedDiagramTask` -> `ShigureOutcome`、G-140 F1・F1.1–F1.2）。

use crate::algebra::VarOrder;
use crate::ir::change::EvalCondition;
use crate::ir::diagram::{CheckedDiagramTask, DiagramEdge, DiagramRelation, DiagramVertex};
use crate::ir::morphism::MorphismDirection;
use crate::ir::presentation::Presentation;
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, EmptyWitness, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_ext::{DiagramOutcomeDetail, RestoredDiagram, RestoredEdge, RestoredVertex};
use crate::ir::term::CoeffDomain;
use crate::solver::common_format::{
    collect_change_and_eval_origins, collect_morphism_origins, collect_presentation_origins,
    format_presentation, format_state_morphism, reeval_obligations_and_constraints,
    substitute_eval_condition, substitute_presentation, substitute_state_morphism,
};
use crate::solver::common_morph::{compare_morphisms, compose_morphism_chain};
use crate::solver::common_solve::{resolve_consistent_point_domain, solve_obligations_and_evals};
use crate::solver::preservation::{
    PreservationObligation, build_presentation_closure_obligations, build_preservation_obligations,
    map_algebra_silence,
};
use std::collections::{BTreeMap, BTreeSet};

/// 検証済み図式タスク `CheckedDiagramTask` を解き、`DiagramOutcomeDetail` 付き `ShigureOutcome` を返す。
pub fn solve_diagram_task(task: &CheckedDiagramTask) -> ShigureOutcome {
    let spec = task.spec();
    let coeff_domain = &spec.change_spec.coeff_domain;
    let mut eval_conds: Vec<&EvalCondition> = Vec::new();
    if let Some(ec) = task.eval_condition() {
        eval_conds.push(ec);
    }
    for ec in spec.edge_eval_conditions.values() {
        eval_conds.push(ec);
    }

    let provenance = build_diagram_provenance(task, &eval_conds);
    let point_domain = match resolve_consistent_point_domain(coeff_domain, &eval_conds) {
        Ok(pd) => pd,
        Err(reason) => {
            return undetermined_diagram(
                coeff_domain,
                &crate::ir::change::PointDomain::AlgebraicClosure,
                vec![ApplicabilityCheck::failed(
                    "consistent_point_domain",
                    MathClause::G140F1,
                    reason.code(),
                )],
                provenance,
                vec![],
                spec.direction,
                BTreeMap::new(),
                BTreeMap::new(),
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
        return undetermined_diagram(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            vec![],
            spec.direction,
            BTreeMap::new(),
            BTreeMap::new(),
            SilenceReason::UnobservedDependency { slots: missing },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::G140P0Dot1,
    ));

    for v in &spec.vertices {
        for s in &v.presentation.sorts {
            if s.rank != 1 {
                let detail = format!(
                    "sort `{}` in diagram vertex `{}` has rank {}, expected 1",
                    s.name, v.name, s.rank
                );
                checks.push(ApplicabilityCheck::failed(
                    "sort_rank_one_required",
                    MathClause::G139P0P1,
                    detail.clone(),
                ));
                return undetermined_diagram(
                    coeff_domain,
                    &point_domain,
                    checks,
                    provenance,
                    vec![],
                    spec.direction,
                    BTreeMap::new(),
                    BTreeMap::new(),
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "sort_rank_one_required".to_owned(),
                        detail,
                    },
                );
            }
        }
    }
    checks.push(ApplicabilityCheck::passed(
        "sort_rank_one_required",
        MathClause::G139P0P1,
    ));

    let param_names: Vec<String> = spec
        .change_spec
        .parameters
        .iter()
        .map(|p| p.name.clone())
        .collect();
    let param_vars = match VarOrder::new(param_names) {
        Ok(v) => v,
        Err(e) => {
            return undetermined_diagram(
                coeff_domain,
                &point_domain,
                checks,
                provenance,
                vec![],
                spec.direction,
                BTreeMap::new(),
                BTreeMap::new(),
                map_algebra_silence(e),
            );
        }
    };

    let (obligations, commutativity_residuals, structural_mismatches) =
        match collect_diagram_obligations(
            &spec.vertices,
            &spec.edges,
            &spec.relations,
            spec.direction,
            &param_vars,
            coeff_domain,
        ) {
            Ok(data) => data,
            Err(reason) => {
                return undetermined_diagram(
                    coeff_domain,
                    &point_domain,
                    checks,
                    provenance,
                    vec![],
                    spec.direction,
                    BTreeMap::new(),
                    BTreeMap::new(),
                    reason,
                );
            }
        };

    if !structural_mismatches.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "diagram_relation_structure_matched",
            MathClause::G140F1,
            "structural mismatch between relation lhs and rhs",
        ));
        return refuted_diagram(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            vec![],
            None,
            spec.direction,
            commutativity_residuals,
            structural_mismatches,
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "diagram_relation_structure_matched",
        MathClause::G140F1,
    ));

    let solve_res = solve_obligations_and_evals(
        &obligations,
        &[],
        &eval_conds,
        coeff_domain,
        &point_domain,
        &param_vars,
    );
    checks.extend(solve_res.checks);

    match solve_res.verdict {
        Verdict::Undetermined(reason) => undetermined_diagram(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            solve_res.residual_display,
            spec.direction,
            commutativity_residuals,
            BTreeMap::new(),
            reason,
        ),
        Verdict::Refuted => refuted_diagram(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            solve_res.residual_display,
            solve_res.empty_witness,
            spec.direction,
            commutativity_residuals,
            BTreeMap::new(),
        ),
        Verdict::Established => {
            let Some(witness) = solve_res.witness else {
                return undetermined_diagram(
                    coeff_domain,
                    &point_domain,
                    checks,
                    provenance,
                    solve_res.residual_display,
                    spec.direction,
                    commutativity_residuals,
                    BTreeMap::new(),
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "witness_present".to_owned(),
                        detail: "missing witness on established diagram".to_owned(),
                    },
                );
            };
            let param_subst = witness.to_param_subst(&param_vars);
            let free_names = witness.unassigned_parameters();
            let free_order = match VarOrder::new(free_names.clone()) {
                Ok(v) => v,
                Err(e) => {
                    return undetermined_diagram(
                        coeff_domain,
                        &point_domain,
                        checks,
                        provenance,
                        solve_res.residual_display,
                        spec.direction,
                        commutativity_residuals,
                        BTreeMap::new(),
                        map_algebra_silence(e),
                    );
                }
            };

            let restored_vertices_ir: Vec<DiagramVertex> = spec
                .vertices
                .iter()
                .map(|v| DiagramVertex {
                    name: v.name.clone(),
                    presentation: if v.is_fixed {
                        v.presentation.clone()
                    } else {
                        substitute_presentation(&v.presentation, &param_subst)
                    },
                    is_fixed: v.is_fixed,
                    provenance: v.provenance.clone(),
                })
                .collect();
            let restored_edges_ir: Vec<DiagramEdge> = spec
                .edges
                .iter()
                .map(|e| DiagramEdge {
                    name: e.name.clone(),
                    source: e.source.clone(),
                    target: e.target.clone(),
                    morphism: if e.is_fixed {
                        e.morphism.clone()
                    } else {
                        substitute_state_morphism(&e.morphism, &param_subst)
                    },
                    is_fixed: e.is_fixed,
                    provenance: e.provenance.clone(),
                })
                .collect();

            let (re_obs, re_resids, re_mismatches) = match collect_diagram_obligations(
                &restored_vertices_ir,
                &restored_edges_ir,
                &spec.relations,
                spec.direction,
                &free_order,
                coeff_domain,
            ) {
                Ok(data) => data,
                Err(reason) => {
                    return undetermined_diagram(
                        coeff_domain,
                        &point_domain,
                        checks,
                        provenance,
                        solve_res.residual_display,
                        spec.direction,
                        commutativity_residuals,
                        BTreeMap::new(),
                        reason,
                    );
                }
            };

            let re_eval_owned: Vec<EvalCondition> = eval_conds
                .iter()
                .map(|ec| substitute_eval_condition(ec, &param_subst))
                .collect();
            let re_eval_refs: Vec<&EvalCondition> = re_eval_owned.iter().collect();
            let reeval = match reeval_obligations_and_constraints(
                &re_obs,
                &[],
                &re_eval_refs,
                &witness,
                coeff_domain,
                &point_domain,
                "diagram",
            ) {
                Ok(mut r) => {
                    if !re_mismatches.is_empty() {
                        r.matched = false;
                        r.detail = "restored diagram relation structure mismatched".to_owned();
                    }
                    r
                }
                Err(reason) => {
                    return undetermined_diagram(
                        coeff_domain,
                        &point_domain,
                        checks,
                        provenance,
                        solve_res.residual_display,
                        spec.direction,
                        commutativity_residuals,
                        BTreeMap::new(),
                        reason,
                    );
                }
            };

            if !reeval.matched {
                return undetermined_diagram(
                    coeff_domain,
                    &point_domain,
                    checks,
                    provenance,
                    solve_res.residual_display,
                    spec.direction,
                    re_resids,
                    re_mismatches,
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "restored_model_reevaluation_matched".to_owned(),
                        detail: reeval.detail,
                    },
                );
            }

            let vertices_by_name: BTreeMap<&str, &DiagramVertex> = restored_vertices_ir
                .iter()
                .map(|v| (v.name.as_str(), v))
                .collect();
            let mut formatted_vertices = Vec::with_capacity(restored_vertices_ir.len());
            for v in &restored_vertices_ir {
                let (ops, laws) = match format_presentation(&v.presentation, &free_names) {
                    Ok(fl) => fl,
                    Err(reason) => {
                        return undetermined_diagram(
                            coeff_domain,
                            &point_domain,
                            checks,
                            provenance,
                            solve_res.residual_display,
                            spec.direction,
                            re_resids,
                            BTreeMap::new(),
                            reason,
                        );
                    }
                };
                formatted_vertices.push(RestoredVertex {
                    name: v.name.clone(),
                    is_fixed: v.is_fixed,
                    operations: ops,
                    state_laws: laws,
                });
            }
            let mut formatted_edges = Vec::with_capacity(restored_edges_ir.len());
            for e in &restored_edges_ir {
                let morph_src_name = match spec.direction {
                    MorphismDirection::StateMap => e.source.as_str(),
                    MorphismDirection::TimeOrder => e.target.as_str(),
                };
                let src_pres = &vertices_by_name[morph_src_name].presentation;
                let (scs, wt) = match format_state_morphism(&e.morphism, src_pres, &free_names) {
                    Ok(fl) => fl,
                    Err(reason) => {
                        return undetermined_diagram(
                            coeff_domain,
                            &point_domain,
                            checks,
                            provenance,
                            solve_res.residual_display,
                            spec.direction,
                            re_resids,
                            BTreeMap::new(),
                            reason,
                        );
                    }
                };
                formatted_edges.push(RestoredEdge {
                    name: e.name.clone(),
                    source: e.source.clone(),
                    target: e.target.clone(),
                    is_fixed: e.is_fixed,
                    state_comparisons: scs,
                    word_translation: wt,
                });
            }

            let restored = RestoredDiagram {
                parameter_assignments: witness.display_assignments(),
                free_parameters: witness.free_parameters(),
                vertices: formatted_vertices,
                edges: formatted_edges,
                reeval,
            };

            checks.push(ApplicabilityCheck::passed(
                "restored_model_reevaluation_matched",
                MathClause::G140F1,
            ));
            ShigureOutcome {
                verdict: Verdict::Established,
                coeff_domain: coeff_domain.clone(),
                point_domain,
                applicability: checks,
                provenance,
                residual_ideal: solve_res.residual_display,
                empty_witness: None,
                restored: None,
                interaction: None,
                diagram: Some(DiagramOutcomeDetail {
                    direction: spec.direction,
                    commutativity_residuals: re_resids,
                    structural_mismatches: BTreeMap::new(),
                    restored_diagram: Some(restored),
                }),
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
                revision: None,
                multisource: None,
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn undetermined_diagram(
    coeff_domain: &CoeffDomain,
    point_domain: &crate::ir::change::PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    residual_ideal: Vec<String>,
    direction: MorphismDirection,
    commutativity_residuals: BTreeMap<String, Vec<String>>,
    structural_mismatches: BTreeMap<String, String>,
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
        diagram: Some(DiagramOutcomeDetail {
            direction,
            commutativity_residuals,
            structural_mismatches,
            restored_diagram: None,
        }),
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
        revision: None,
        multisource: None,
    }
}

#[allow(clippy::too_many_arguments)]
fn refuted_diagram(
    coeff_domain: &CoeffDomain,
    point_domain: &crate::ir::change::PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    residual_ideal: Vec<String>,
    empty_witness: Option<EmptyWitness>,
    direction: MorphismDirection,
    commutativity_residuals: BTreeMap<String, Vec<String>>,
    structural_mismatches: BTreeMap<String, String>,
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
        diagram: Some(DiagramOutcomeDetail {
            direction,
            commutativity_residuals,
            structural_mismatches,
            restored_diagram: None,
        }),
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
        revision: None,
        multisource: None,
    }
}

fn build_diagram_provenance(
    task: &CheckedDiagramTask,
    eval_conds: &[&EvalCondition],
) -> Provenance {
    let spec = task.spec();
    let mut set = BTreeSet::new();
    for o in &spec.provenance.origins {
        set.insert(o.clone());
    }
    for v in &spec.vertices {
        if let Some(o) = &v.provenance {
            set.insert(o.clone());
        }
        collect_presentation_origins(&v.presentation, &mut set);
    }
    for e in &spec.edges {
        if let Some(o) = &e.provenance {
            set.insert(o.clone());
        }
        collect_morphism_origins(&e.morphism, &mut set);
    }
    for r in &spec.relations {
        if let Some(o) = &r.provenance {
            set.insert(o.clone());
        }
    }
    collect_change_and_eval_origins(&spec.change_spec, eval_conds, &mut set);
    Provenance::new(
        set.into_iter().collect(),
        vec![
            MathClause::G139P0P1,
            MathClause::G140P0Dot1,
            MathClause::G140A2,
            MathClause::G140F1,
            MathClause::G140F1Dot1,
            MathClause::G140F1Dot2,
            MathClause::G141D1,
            MathClause::G141D4,
            MathClause::G141D5,
        ],
    )
}

#[allow(clippy::type_complexity)]
fn collect_diagram_obligations(
    vertices: &[DiagramVertex],
    edges: &[DiagramEdge],
    relations: &[DiagramRelation],
    direction: MorphismDirection,
    param_vars: &VarOrder,
    coeff_domain: &CoeffDomain,
) -> Result<
    (
        Vec<PreservationObligation>,
        BTreeMap<String, Vec<String>>,
        BTreeMap<String, String>,
    ),
    SilenceReason,
> {
    let pres_by_name: BTreeMap<&str, &Presentation> = vertices
        .iter()
        .map(|v| (v.name.as_str(), &v.presentation))
        .collect();
    let edges_by_name: BTreeMap<&str, &DiagramEdge> =
        edges.iter().map(|e| (e.name.as_str(), e)).collect();

    let mut obligations = Vec::new();
    for v in vertices {
        obligations.extend(build_presentation_closure_obligations(&v.presentation)?);
    }
    for e in edges {
        let src_pres = pres_by_name[e.source.as_str()];
        let tgt_pres = pres_by_name[e.target.as_str()];
        let pair = match direction {
            MorphismDirection::StateMap => e.morphism.to_comparison_pair(src_pres, tgt_pres),
            MorphismDirection::TimeOrder => e.morphism.to_comparison_pair(tgt_pres, src_pres),
        };
        obligations.extend(build_preservation_obligations(&pair)?);
    }

    let mut commutativity_residuals = BTreeMap::new();
    let mut structural_mismatches = BTreeMap::new();
    for rel in relations {
        let collect_chain =
            |names: &[String]| -> Vec<(&str, &str, &crate::ir::morphism::StateMorphism)> {
                names
                    .iter()
                    .map(|n| {
                        let e = edges_by_name[n.as_str()];
                        (e.source.as_str(), e.target.as_str(), &e.morphism)
                    })
                    .collect()
            };
        let (lhs_m, dom_pres) =
            compose_morphism_chain(&collect_chain(&rel.lhs), &pres_by_name, direction)?;
        let (rhs_m, _) =
            compose_morphism_chain(&collect_chain(&rel.rhs), &pres_by_name, direction)?;
        let (rel_obs, rel_resids, mismatch) =
            compare_morphisms(&lhs_m, &rhs_m, dom_pres, param_vars, coeff_domain)?;
        commutativity_residuals.insert(rel.name.clone(), rel_resids);
        if let Some(mm) = mismatch {
            structural_mismatches.insert(rel.name.clone(), mm);
        } else {
            obligations.extend(rel_obs);
        }
    }

    Ok((obligations, commutativity_residuals, structural_mismatches))
}
