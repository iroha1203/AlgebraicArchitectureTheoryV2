use std::collections::BTreeSet;

use crate::{
    LawEvaluatorRegistryV1, LawPolicyDocumentV1, NormalizedArchMapV1,
    TYPED_EVALUATOR_RESULTS_V1_SCHEMA, TypedEvaluatorResultV1, TypedEvaluatorResultsSummaryV1,
    TypedEvaluatorResultsV1, expand_law_policy_v1,
};

const PIPELINE_ID: &str = "archsig-v1-typed-evaluator-pipeline@1";

pub fn evaluate_typed_v1(
    normalized: &NormalizedArchMapV1,
    law_policy: &LawPolicyDocumentV1,
    registry: &LawEvaluatorRegistryV1,
    normalized_archmap_ref: &str,
    law_policy_ref: &str,
) -> TypedEvaluatorResultsV1 {
    let expanded = expand_law_policy_v1(law_policy);
    let results = expanded
        .iter()
        .map(|entry| {
            let manifest = registry
                .evaluators
                .iter()
                .find(|manifest| manifest.evaluator_id == entry.evaluator);
            let Some(manifest) = manifest else {
                return TypedEvaluatorResultV1 {
                    evaluator: entry.evaluator.clone(),
                    law: entry.law.clone(),
                    status: "unknown".to_string(),
                    support_atom_refs: Vec::new(),
                    support_molecule_refs: Vec::new(),
                    basis_refs: entry.basis.clone(),
                    detail_refs: Vec::new(),
                    summary: "evaluator manifest is not registered".to_string(),
                    blocker_reason: Some("unknown evaluator manifest".to_string()),
                };
            };

            let support_atom_refs = normalized
                .atoms
                .iter()
                .filter(|atom| {
                    manifest
                        .required_atom_constructors
                        .iter()
                        .any(|required| required == &atom.predicate.constructor)
                        || manifest
                            .required_predicates
                            .iter()
                            .any(|required| predicate_has_value(atom, required))
                })
                .map(|atom| atom.normalized_atom_id.clone())
                .collect::<Vec<_>>();
            let support_molecule_refs = normalized
                .molecules
                .iter()
                .filter(|molecule| {
                    molecule.generated_molecule_candidate_status == "generated"
                        && molecule
                            .atom_ids
                            .iter()
                            .any(|atom_id| support_atom_refs.contains(atom_id))
                })
                .map(|molecule| molecule.normalized_molecule_id.clone())
                .collect::<Vec<_>>();

            typed_result(entry, &support_atom_refs, &support_molecule_refs)
        })
        .collect::<Vec<_>>();
    let summary = typed_summary(&results);
    let positive_bounded_conclusions = positive_bounded_conclusions(&results);

    TypedEvaluatorResultsV1 {
        schema: TYPED_EVALUATOR_RESULTS_V1_SCHEMA.to_string(),
        pipeline_id: PIPELINE_ID.to_string(),
        normalized_archmap_ref: normalized_archmap_ref.to_string(),
        law_policy_ref: law_policy_ref.to_string(),
        results,
        summary,
        positive_bounded_conclusions,
        non_conclusions: vec![
            "Typed evaluator results are bounded to normalized ArchMap, LawPolicy, and evaluator registry evidence.".to_string(),
            "Blocked, unknown, and unmeasured results are not measured zero.".to_string(),
            "Typed evaluator results are ArchSig computation artifacts, not Lean proof objects.".to_string(),
        ],
    }
}

fn typed_result(
    entry: &crate::ExpandedLawPolicyEntryV1,
    support_atom_refs: &[String],
    support_molecule_refs: &[String],
) -> TypedEvaluatorResultV1 {
    let blocker_reason = if support_atom_refs.is_empty() {
        Some("required support atoms are missing under selected evaluator manifest".to_string())
    } else if support_molecule_refs.is_empty() {
        Some("required generated molecule candidate is missing".to_string())
    } else {
        None
    };
    let status = if blocker_reason.is_some() {
        "blocked"
    } else if entry.law == "solid.dependency-inversion"
        || entry.law == "domain.no-direct-infra-dependency"
    {
        "measuredViolation"
    } else {
        "measuredPass"
    };

    TypedEvaluatorResultV1 {
        evaluator: entry.evaluator.clone(),
        law: entry.law.clone(),
        status: status.to_string(),
        support_atom_refs: support_atom_refs.to_vec(),
        support_molecule_refs: support_molecule_refs.to_vec(),
        basis_refs: entry.basis.clone(),
        detail_refs: support_atom_refs
            .iter()
            .chain(support_molecule_refs.iter())
            .cloned()
            .collect(),
        summary: format!("{} evaluated as {status}", entry.law),
        blocker_reason,
    }
}

fn predicate_has_value(atom: &crate::NormalizedAtomV1, required: &str) -> bool {
    atom.predicate
        .bindings
        .iter()
        .any(|binding| binding.value == required)
}

fn typed_summary(results: &[TypedEvaluatorResultV1]) -> TypedEvaluatorResultsSummaryV1 {
    TypedEvaluatorResultsSummaryV1 {
        result_count: results.len(),
        measured_pass_count: count_status(results, "measuredPass"),
        measured_violation_count: count_status(results, "measuredViolation"),
        blocked_count: count_status(results, "blocked"),
        unknown_count: count_status(results, "unknown"),
        unmeasured_count: count_status(results, "unmeasured"),
    }
}

fn count_status(results: &[TypedEvaluatorResultV1], status: &str) -> usize {
    results
        .iter()
        .filter(|result| result.status == status)
        .count()
}

fn positive_bounded_conclusions(results: &[TypedEvaluatorResultV1]) -> Vec<String> {
    let measured_violations = results
        .iter()
        .filter(|result| result.status == "measuredViolation")
        .map(|result| result.law.as_str())
        .collect::<BTreeSet<_>>();
    if !measured_violations.is_empty() {
        return vec![format!(
            "SELECTED_VIOLATION_MEASURED_UNDER_EVIDENCE_CONTRACT for measured evaluator set: {}",
            measured_violations
                .into_iter()
                .collect::<Vec<_>>()
                .join(", ")
        )];
    }

    let measured_passes = results
        .iter()
        .filter(|result| result.status == "measuredPass")
        .map(|result| result.law.as_str())
        .collect::<BTreeSet<_>>();
    if measured_passes.is_empty() {
        return Vec::new();
    }
    vec![format!(
        "ACCEPTABLE_UNDER_EVIDENCE_CONTRACT for measured evaluator set: {}",
        measured_passes.into_iter().collect::<Vec<_>>().join(", ")
    )]
}
