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
        .flat_map(|(index, entry)| {
            if let Some(pack) = entry.pack.as_deref() {
                let _ = pack;
                Vec::new()
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
    let _ = pack;
    false
}

pub fn is_known_evaluator(evaluator: &str) -> bool {
    evaluator_manifests()
        .iter()
        .any(|manifest| manifest.evaluator_id == evaluator)
}

pub fn is_known_v1_basis(basis: &str) -> bool {
    matches!(basis, "policy-basis:layering")
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
