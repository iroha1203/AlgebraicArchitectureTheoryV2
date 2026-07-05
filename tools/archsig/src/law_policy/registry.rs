use crate::{
    ExpandedLawPolicyEntryV1, LawEvaluatorManifestV1, LawEvaluatorRegistryV1,
    LawPolicyBasisManifestV1, LawPolicyDocumentV1, LawPolicyPackEntryV1, LawPolicyPackManifestV1,
    ReplacementEvaluatorManifestV1,
};

pub mod ag;

const REGISTRY_SCHEMA: &str = "law-evaluator-registry/v0.5.0";
pub const REPLACEMENT_REGISTRY_REF: &str = "removed-schema050-field-replacement-registry";

pub fn static_law_evaluator_registry_v1() -> LawEvaluatorRegistryV1 {
    LawEvaluatorRegistryV1 {
        schema: REGISTRY_SCHEMA.to_string(),
        registry_id: "archsig-law-evaluator-registry".to_string(),
        evaluators: evaluator_manifests(),
        replacement_registry: replacement_manifests(),
        policy_packs: vec![LawPolicyPackManifestV1 {
            pack_id: "solid".to_string(),
            entries: solid_pack_entries(),
        }],
        basis_refs: vec![
            LawPolicyBasisManifestV1 {
                basis_ref: "policy-basis:solid".to_string(),
                title: "SOLID design principle basis".to_string(),
            },
            LawPolicyBasisManifestV1 {
                basis_ref: "policy-basis:layering".to_string(),
                title: "Layered architecture dependency basis".to_string(),
            },
        ],
    }
}

pub fn expand_law_policy_v1(policy: &LawPolicyDocumentV1) -> Vec<ExpandedLawPolicyEntryV1> {
    policy
        .policies
        .iter()
        .enumerate()
        .flat_map(|(index, entry)| {
            if let Some(pack) = entry.pack.as_deref() {
                pack_entries(pack)
                    .into_iter()
                    .map(|pack_entry| ExpandedLawPolicyEntryV1 {
                        source_policy_index: index,
                        source_selector: pack.to_string(),
                        law: pack_entry.law,
                        evaluator: pack_entry.evaluator,
                        basis: entry.basis.clone(),
                        scope: entry.scope.clone(),
                        severity: entry.severity.clone(),
                    })
                    .collect::<Vec<_>>()
            } else if let (Some(law), Some(evaluator)) =
                (entry.law.as_deref(), entry.evaluator.as_deref())
            {
                vec![ExpandedLawPolicyEntryV1 {
                    source_policy_index: index,
                    source_selector: law.to_string(),
                    law: law.to_string(),
                    evaluator: evaluator.to_string(),
                    basis: entry.basis.clone(),
                    scope: entry.scope.clone(),
                    severity: entry.severity.clone(),
                }]
            } else {
                Vec::new()
            }
        })
        .collect()
}

pub fn is_known_v1_pack(pack: &str) -> bool {
    pack_entries(pack).len() > 0
}

pub fn is_known_evaluator(evaluator: &str) -> bool {
    evaluator_manifests()
        .iter()
        .any(|manifest| manifest.evaluator_id == evaluator)
}

pub fn is_known_v1_basis(basis: &str) -> bool {
    matches!(basis, "policy-basis:solid" | "policy-basis:layering")
}

pub fn is_known_v1_distance_profile(profile_ref: &str) -> bool {
    matches!(
        profile_ref,
        "distance-profile:architecture-default@1" | "distance-profile:practical-rust-service@1"
    )
}

pub fn replacement_manifests() -> Vec<ReplacementEvaluatorManifestV1> {
    vec![
        replacement_manifest(
            "semantic.interpretation",
            "semanticObservations",
            "semantic.interpretation",
            "replacement.semantic-interpretation",
            &["semantic"],
            "semantic atom must belong to an explicit generated molecule candidate",
            &["/replacementEvaluatorResultsById/semantic.interpretation"],
            &["examples/practical-rust-service/archmap/archmap.json"],
            &["tests/fixtures/archmap_v1/replacement_negative/archmap_label_only_semantic.json"],
            "missing semantic atoms or generated molecule membership become blocked, not label-derived measured results",
        ),
        replacement_manifest(
            "projection.reading",
            "projectionInfo",
            "projection.reading",
            "replacement.projection-reading",
            &["component", "relation", "capability"],
            "projection reading is computed from normalized static atoms in explicit generated molecule candidates",
            &["/replacementEvaluatorResultsById/projection.reading"],
            &["tests/fixtures/archmap_v1/archmap.json"],
            &[
                "tests/fixtures/archmap_v1/replacement_negative/archmap_projection_only_v0_field.json",
            ],
            "missing normalized static atom support becomes blocked, not projection-only input evidence",
        ),
        replacement_manifest(
            "operation-square.reading",
            "operationSquareEvidence",
            "operation-square.reading",
            "replacement.operation-square-reading",
            &["relation", "effect", "runtime"],
            "square / commutation reading is computed from normalized relation with effect or runtime atoms in generated molecule candidates",
            &["/replacementEvaluatorResultsById/operation-square.reading"],
            &["examples/practical-rust-service/archmap/archmap.json"],
            &[
                "tests/fixtures/archmap_v1/replacement_negative/archmap_operation_square_only_v0_field.json",
            ],
            "missing relation plus effect/runtime support becomes blocked, not square-only input evidence",
        ),
        replacement_manifest(
            "missing-evidence.reading",
            "observationGaps",
            "missing-evidence.reading",
            "replacement.missing-evidence-reading",
            &[],
            "missing evidence is derived from selected evaluator requirements and typed evaluator blocked statuses",
            &["/replacementEvaluatorResultsById/missing-evidence.reading"],
            &["tests/fixtures/archmap_v1/archmap_blocked_molecule.json"],
            &[
                "tests/fixtures/archmap_v1/replacement_negative/archmap_observation_gaps_only_v0_field.json",
            ],
            "blocked selected evaluator requirements become missing-evidence readings; authored gap lists cannot become measured zero",
        ),
        replacement_manifest(
            "concern.boundary",
            "concernHints",
            "concern.boundary",
            "replacement.concern-boundary",
            &[],
            "concern notes are outside ArchMap primary input and never diagnostic support",
            &["/replacementEvaluatorResultsById/concern.boundary"],
            &["tests/fixtures/archmap_v1/archmap.json"],
            &["tests/fixtures/archmap_v1/replacement_negative/archmap_concern_only_v0_field.json"],
            "concern-only artifacts remain unmeasured review notes, never measured evaluator results",
        ),
        replacement_manifest(
            "non-conclusion.boundary",
            "nonConclusions",
            "non-conclusion.boundary",
            "replacement.non-conclusion-boundary",
            &[],
            "non-conclusion prose is carried by schemas and output manifests, not by ArchMap diagnostic input",
            &["/replacementEvaluatorResultsById/non-conclusion.boundary"],
            &["tests/fixtures/archmap_v1/archmap.json"],
            &[
                "tests/fixtures/archmap_v1/replacement_negative/archmap_non_conclusion_only_v0_field.json",
            ],
            "nonConclusion prose cannot create blockers, safe results, or measured zero",
        ),
    ]
}

fn pack_entries(pack: &str) -> Vec<LawPolicyPackEntryV1> {
    match pack {
        "solid" => solid_pack_entries(),
        _ => Vec::new(),
    }
}

fn solid_pack_entries() -> Vec<LawPolicyPackEntryV1> {
    vec![
        LawPolicyPackEntryV1 {
            law: "solid.single-responsibility".to_string(),
            evaluator: "solid.single-responsibility".to_string(),
        },
        LawPolicyPackEntryV1 {
            law: "solid.open-closed".to_string(),
            evaluator: "solid.open-closed".to_string(),
        },
        LawPolicyPackEntryV1 {
            law: "solid.liskov-substitution".to_string(),
            evaluator: "solid.liskov-substitution".to_string(),
        },
        LawPolicyPackEntryV1 {
            law: "solid.interface-segregation".to_string(),
            evaluator: "solid.interface-segregation".to_string(),
        },
        LawPolicyPackEntryV1 {
            law: "solid.dependency-inversion".to_string(),
            evaluator: "solid.dependency-inversion".to_string(),
        },
    ]
}

fn evaluator_manifests() -> Vec<LawEvaluatorManifestV1> {
    let mut manifests = vec![
        solid_manifest(
            "solid.single-responsibility",
            "solid.single-responsibility",
            &["component", "capability", "semantic"],
            &["placesOrder"],
        ),
        solid_manifest(
            "solid.open-closed",
            "solid.open-closed",
            &["component", "contract", "effect"],
            &["implements"],
        ),
        solid_manifest(
            "solid.liskov-substitution",
            "solid.liskov-substitution",
            &["contract", "relation", "runtime"],
            &["dependsOn"],
        ),
        solid_manifest(
            "solid.interface-segregation",
            "solid.interface-segregation",
            &["component", "capability", "relation"],
            &["calls"],
        ),
        solid_manifest(
            "solid.dependency-inversion",
            "solid.dependency-inversion",
            &["relation", "authority", "contract"],
            &["dependsOn"],
        ),
        LawEvaluatorManifestV1 {
            evaluator_id: "domain.no-direct-infra-dependency".to_string(),
            law_id: "domain.no-direct-infra-dependency".to_string(),
            required_atom_constructors: vec!["relation".to_string(), "authority".to_string()],
            required_predicates: vec!["dependsOn".to_string(), "calls".to_string()],
            required_molecule_condition:
                "explicit membership containing a domain-to-infra relation candidate".to_string(),
            scope_filtering_rule: "filter normalized atoms by LawPolicy scope source prefixes"
                .to_string(),
            missing_blocker_rule:
                "missing relation or authority atoms become blocked, not measured zero".to_string(),
            pass_criteria: "no selected domain-to-infra relation is present under scoped atoms"
                .to_string(),
            violation_criteria:
                "selected relation crosses from domain scope into infrastructure scope".to_string(),
            typed_result_schema: "typed-evaluator-result/v0.5.0".to_string(),
            distance_contribution: "registry-owned structural-pressure contribution".to_string(),
            summary_output_refs: vec!["typedResults[].summary".to_string()],
            detail_output_refs: vec!["typedResults[].evidenceRefs".to_string()],
            negative_fixtures: vec!["law_policy_unknown_evaluator.json".to_string()],
        },
    ];
    manifests.extend(ag::ag_evaluator_manifests());
    manifests
}

fn replacement_manifest(
    replacement_id: &str,
    replaced_v0_field: &str,
    evaluator_id: &str,
    law_id: &str,
    required_atom_constructors: &[&str],
    required_molecule_membership: &str,
    typed_output_packet_refs: &[&str],
    positive_fixtures: &[&str],
    negative_fixtures: &[&str],
    missing_blocker_rule: &str,
) -> ReplacementEvaluatorManifestV1 {
    ReplacementEvaluatorManifestV1 {
        replacement_id: replacement_id.to_string(),
        replaced_v0_field: replaced_v0_field.to_string(),
        evaluator_id: evaluator_id.to_string(),
        law_id: law_id.to_string(),
        required_atom_constructors: required_atom_constructors
            .iter()
            .map(|value| (*value).to_string())
            .collect(),
        required_molecule_membership: required_molecule_membership.to_string(),
        typed_output_packet_refs: typed_output_packet_refs
            .iter()
            .map(|value| (*value).to_string())
            .collect(),
        positive_fixtures: positive_fixtures
            .iter()
            .map(|value| (*value).to_string())
            .collect(),
        negative_fixtures: negative_fixtures
            .iter()
            .map(|value| (*value).to_string())
            .collect(),
        missing_blocker_rule: missing_blocker_rule.to_string(),
    }
}

fn solid_manifest(
    evaluator_id: &str,
    law_id: &str,
    required_atom_constructors: &[&str],
    required_predicates: &[&str],
) -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: evaluator_id.to_string(),
        law_id: law_id.to_string(),
        required_atom_constructors: required_atom_constructors
            .iter()
            .map(|value| (*value).to_string())
            .collect(),
        required_predicates: required_predicates
            .iter()
            .map(|value| (*value).to_string())
            .collect(),
        required_molecule_condition:
            "explicit molecule membership with required normalized atom constructors".to_string(),
        scope_filtering_rule: "filter normalized atoms by LawPolicy scope source prefixes"
            .to_string(),
        missing_blocker_rule:
            "missing required atoms or molecule condition become blocked, not measured zero"
                .to_string(),
        pass_criteria: "scoped normalized atoms satisfy evaluator-specific law condition"
            .to_string(),
        violation_criteria: "scoped normalized atoms violate evaluator-specific law condition"
            .to_string(),
        typed_result_schema: "typed-evaluator-result/v0.5.0".to_string(),
        distance_contribution: "registry-owned structural-pressure contribution".to_string(),
        summary_output_refs: vec!["typedResults[].summary".to_string()],
        detail_output_refs: vec!["typedResults[].evidenceRefs".to_string()],
        negative_fixtures: vec!["law_policy_dsl_field.json".to_string()],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_keeps_ag_evaluator_vocabulary_after_module_split() {
        assert!(is_known_evaluator("ag.cech-obstruction"));
        assert!(is_known_evaluator("ag.section-factorization"));
        assert!(!is_known_evaluator("ag.unknown-evaluator"));

        let registry = static_law_evaluator_registry_v1();
        let section_manifest = registry
            .evaluators
            .iter()
            .find(|manifest| manifest.evaluator_id == "ag.section-factorization")
            .expect("section-factorization manifest remains registered");

        assert_eq!(section_manifest.law_id, "ag.section-factorization");
        assert_eq!(
            section_manifest.required_predicates,
            vec![
                "section-factorization.obstructionGenerator".to_string(),
                "section-factorization.witnessAssignment".to_string(),
            ]
        );
        assert_eq!(
            section_manifest.typed_result_schema,
            "archsig-measurement-packet/v0.5.0"
        );
    }
}
