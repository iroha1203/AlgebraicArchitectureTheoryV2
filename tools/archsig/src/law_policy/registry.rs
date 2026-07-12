use crate::{
    ExpandedLawPolicyEntryV1, LawEvaluatorManifestV1, LawEvaluatorRegistryV1,
    LawPolicyBasisManifestV1, LawPolicyDocumentV1,
};

pub mod ag;

const REGISTRY_SCHEMA: &str = "law-evaluator-registry/v0.5.0";

pub fn static_law_evaluator_registry_v1() -> LawEvaluatorRegistryV1 {
    LawEvaluatorRegistryV1 {
        schema: REGISTRY_SCHEMA.to_string(),
        registry_id: "archsig-law-evaluator-registry".to_string(),
        evaluators: evaluator_manifests(),
        policy_packs: vec![],
        basis_refs: vec![LawPolicyBasisManifestV1 {
            basis_ref: "policy-basis:layering".to_string(),
            title: "Layered architecture dependency basis".to_string(),
        }],
    }
}

pub fn expand_law_policy_v1(policy: &LawPolicyDocumentV1) -> Vec<ExpandedLawPolicyEntryV1> {
    policy
        .policies
        .iter()
        .enumerate()
        .filter_map(|(index, entry)| {
            let (law, evaluator) = (entry.law.as_deref()?, entry.evaluator.as_deref()?);
            Some(ExpandedLawPolicyEntryV1 {
                source_policy_index: index,
                source_selector: law.to_string(),
                law: law.to_string(),
                evaluator: evaluator.to_string(),
                basis: entry.basis.clone(),
                scope: entry.scope.clone(),
                severity: entry.severity.clone(),
            })
        })
        .collect()
}

pub fn is_known_evaluator(evaluator: &str) -> bool {
    evaluator_manifests()
        .iter()
        .any(|manifest| manifest.evaluator_id == evaluator)
}

pub fn is_compatible_evaluator_condition(evaluator: &str, condition_type: &str) -> bool {
    evaluator_manifests()
        .iter()
        .find(|manifest| manifest.evaluator_id == evaluator)
        .is_some_and(|manifest| {
            manifest
                .condition_types
                .iter()
                .any(|candidate| candidate == condition_type)
        })
}

fn evaluator_manifests() -> Vec<LawEvaluatorManifestV1> {
    let mut manifests = Vec::new();
    manifests.extend(ag::ag_evaluator_manifests());
    manifests
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
                "section-factorization.support".to_string(),
                "section-factorization.witnessAssignment".to_string(),
            ]
        );
        assert!(is_compatible_evaluator_condition(
            "ag.section-factorization",
            "open"
        ));
        assert!(!is_compatible_evaluator_condition(
            "ag.section-factorization",
            "temporal"
        ));
        assert_eq!(
            section_manifest.typed_result_schema,
            "archsig-measurement-packet/v0.5.0"
        );
    }

    #[test]
    fn expansion_ignores_retired_pack_selectors() {
        let policy = LawPolicyDocumentV1 {
            schema: "law-policy/v0.5.0".to_string(),
            id: "policy:test".to_string(),
            law_surface_ref: None,
            measurement_profile_ref: None,
            basis_ledger: vec![],
            policies: vec![
                crate::LawPolicyEntryV1 {
                    pack: Some("retired-pack".to_string()),
                    law: None,
                    evaluator: None,
                    basis: vec![],
                    profile_ref: None,
                    scope: vec![],
                    severity: "warning".to_string(),
                },
                crate::LawPolicyEntryV1 {
                    pack: None,
                    law: Some("ag.cech-obstruction".to_string()),
                    evaluator: Some("ag.cech-obstruction".to_string()),
                    basis: vec![],
                    profile_ref: None,
                    scope: vec!["context:test".to_string()],
                    severity: "warning".to_string(),
                },
            ],
        };

        let expanded = expand_law_policy_v1(&policy);
        assert_eq!(expanded.len(), 1);
        assert_eq!(expanded[0].source_policy_index, 1);
        assert_eq!(expanded[0].source_selector, "ag.cech-obstruction");
    }
}
