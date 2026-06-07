use crate::{
    ExpandedLawPolicyEntryV1, LawEvaluatorManifestV1, LawEvaluatorRegistryV1,
    LawPolicyBasisManifestV1, LawPolicyDocumentV1, LawPolicyPackEntryV1, LawPolicyPackManifestV1,
};

const REGISTRY_SCHEMA: &str = "law-evaluator-registry/v1";

pub fn static_law_evaluator_registry_v1() -> LawEvaluatorRegistryV1 {
    LawEvaluatorRegistryV1 {
        schema: REGISTRY_SCHEMA.to_string(),
        registry_id: "archsig-law-evaluator-registry@1".to_string(),
        evaluators: evaluator_manifests(),
        policy_packs: vec![LawPolicyPackManifestV1 {
            pack_id: "solid@1".to_string(),
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

pub fn is_known_v1_evaluator(evaluator: &str) -> bool {
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

fn pack_entries(pack: &str) -> Vec<LawPolicyPackEntryV1> {
    match pack {
        "solid@1" => solid_pack_entries(),
        _ => Vec::new(),
    }
}

fn solid_pack_entries() -> Vec<LawPolicyPackEntryV1> {
    vec![
        LawPolicyPackEntryV1 {
            law: "solid.single-responsibility".to_string(),
            evaluator: "solid.single-responsibility@1".to_string(),
        },
        LawPolicyPackEntryV1 {
            law: "solid.open-closed".to_string(),
            evaluator: "solid.open-closed@1".to_string(),
        },
        LawPolicyPackEntryV1 {
            law: "solid.liskov-substitution".to_string(),
            evaluator: "solid.liskov-substitution@1".to_string(),
        },
        LawPolicyPackEntryV1 {
            law: "solid.interface-segregation".to_string(),
            evaluator: "solid.interface-segregation@1".to_string(),
        },
        LawPolicyPackEntryV1 {
            law: "solid.dependency-inversion".to_string(),
            evaluator: "solid.dependency-inversion@1".to_string(),
        },
    ]
}

fn evaluator_manifests() -> Vec<LawEvaluatorManifestV1> {
    vec![
        solid_manifest(
            "solid.single-responsibility@1",
            "solid.single-responsibility",
            &["component", "capability", "semantic"],
            &["placesOrder"],
        ),
        solid_manifest(
            "solid.open-closed@1",
            "solid.open-closed",
            &["component", "contract", "effect"],
            &["implements"],
        ),
        solid_manifest(
            "solid.liskov-substitution@1",
            "solid.liskov-substitution",
            &["contract", "relation", "runtime"],
            &["dependsOn"],
        ),
        solid_manifest(
            "solid.interface-segregation@1",
            "solid.interface-segregation",
            &["component", "capability", "relation"],
            &["calls"],
        ),
        solid_manifest(
            "solid.dependency-inversion@1",
            "solid.dependency-inversion",
            &["relation", "authority", "contract"],
            &["dependsOn"],
        ),
        LawEvaluatorManifestV1 {
            evaluator_id: "domain.no-direct-infra-dependency@1".to_string(),
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
            typed_result_schema: "typed-evaluator-result/v1".to_string(),
            distance_contribution: "registry-owned structural-pressure contribution".to_string(),
            summary_output_refs: vec!["typedResults[].summary".to_string()],
            detail_output_refs: vec!["typedResults[].evidenceRefs".to_string()],
            negative_fixtures: vec!["law_policy_unknown_evaluator.json".to_string()],
        },
    ]
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
        typed_result_schema: "typed-evaluator-result/v1".to_string(),
        distance_contribution: "registry-owned structural-pressure contribution".to_string(),
        summary_output_refs: vec!["typedResults[].summary".to_string()],
        detail_output_refs: vec!["typedResults[].evidenceRefs".to_string()],
        negative_fixtures: vec!["law_policy_dsl_field.json".to_string()],
    }
}
