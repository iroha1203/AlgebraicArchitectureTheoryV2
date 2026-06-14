use crate::{
    ExpandedLawPolicyEntryV1, LawEvaluatorManifestV1, LawEvaluatorRegistryV1,
    LawPolicyBasisManifestV1, LawPolicyDocumentV1, LawPolicyPackEntryV1, LawPolicyPackManifestV1,
    ReplacementEvaluatorManifestV1,
};

const REGISTRY_SCHEMA: &str = "law-evaluator-registry/v1";
pub const REPLACEMENT_REGISTRY_REF: &str = "removed-v0-field-replacement-registry@1";

pub fn static_law_evaluator_registry_v1() -> LawEvaluatorRegistryV1 {
    LawEvaluatorRegistryV1 {
        schema: REGISTRY_SCHEMA.to_string(),
        registry_id: "archsig-law-evaluator-registry@1".to_string(),
        evaluators: evaluator_manifests(),
        replacement_registry: replacement_manifests(),
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

pub fn replacement_manifests() -> Vec<ReplacementEvaluatorManifestV1> {
    vec![
        replacement_manifest(
            "semantic.interpretation@1",
            "semanticObservations",
            "semantic.interpretation@1",
            "replacement.semantic-interpretation",
            &["semantic"],
            "semantic atom must belong to an explicit generated molecule candidate",
            &["/replacementEvaluatorResultsById/semantic.interpretation@1"],
            &["examples/practical-rust-service/archmap/archmap.json"],
            &["tests/fixtures/archmap_v1/replacement_negative/archmap_label_only_semantic.json"],
            "missing semantic atoms or generated molecule membership become blocked, not label-derived measured results",
        ),
        replacement_manifest(
            "projection.reading@1",
            "projectionInfo",
            "projection.reading@1",
            "replacement.projection-reading",
            &["component", "relation", "capability"],
            "projection reading is computed from normalized static atoms in explicit generated molecule candidates",
            &["/replacementEvaluatorResultsById/projection.reading@1"],
            &["tests/fixtures/archmap_v1/archmap.json"],
            &[
                "tests/fixtures/archmap_v1/replacement_negative/archmap_projection_only_v0_field.json",
            ],
            "missing normalized static atom support becomes blocked, not projection-only input evidence",
        ),
        replacement_manifest(
            "operation-square.reading@1",
            "operationSquareEvidence",
            "operation-square.reading@1",
            "replacement.operation-square-reading",
            &["relation", "effect", "runtime"],
            "square / commutation reading is computed from normalized relation with effect or runtime atoms in generated molecule candidates",
            &["/replacementEvaluatorResultsById/operation-square.reading@1"],
            &["examples/practical-rust-service/archmap/archmap.json"],
            &[
                "tests/fixtures/archmap_v1/replacement_negative/archmap_operation_square_only_v0_field.json",
            ],
            "missing relation plus effect/runtime support becomes blocked, not square-only input evidence",
        ),
        replacement_manifest(
            "missing-evidence.reading@1",
            "observationGaps",
            "missing-evidence.reading@1",
            "replacement.missing-evidence-reading",
            &[],
            "missing evidence is derived from selected evaluator requirements and typed evaluator blocked statuses",
            &["/replacementEvaluatorResultsById/missing-evidence.reading@1"],
            &["tests/fixtures/archmap_v1/archmap_blocked_molecule.json"],
            &[
                "tests/fixtures/archmap_v1/replacement_negative/archmap_observation_gaps_only_v0_field.json",
            ],
            "blocked selected evaluator requirements become missing-evidence readings; authored gap lists cannot become measured zero",
        ),
        replacement_manifest(
            "concern.boundary@1",
            "concernHints",
            "concern.boundary@1",
            "replacement.concern-boundary",
            &[],
            "concern notes are outside ArchMap primary input and never diagnostic support",
            &["/replacementEvaluatorResultsById/concern.boundary@1"],
            &["tests/fixtures/archmap_v1/archmap.json"],
            &["tests/fixtures/archmap_v1/replacement_negative/archmap_concern_only_v0_field.json"],
            "concern-only artifacts remain unmeasured review notes, never measured evaluator results",
        ),
        replacement_manifest(
            "non-conclusion.boundary@1",
            "nonConclusions",
            "non-conclusion.boundary@1",
            "replacement.non-conclusion-boundary",
            &[],
            "non-conclusion prose is carried by schemas and output manifests, not by ArchMap diagnostic input",
            &["/replacementEvaluatorResultsById/non-conclusion.boundary@1"],
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
    let mut manifests = vec![
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
    ];
    manifests.extend([
        ag_manifest("ag.cech-obstruction@1", "ag.cech-obstruction"),
        ag_coherence_manifest(),
        ag_restriction_manifest(),
        ag_section_manifest(),
        ag_boundary_residue_manifest(),
        ag_manifest("ag.square-free-repair@1", "ag.square-free-repair"),
        ag_manifest("ag.law-conflict-tor@1", "ag.law-conflict-tor"),
        ag_manifest("ag.sheaf-laplacian@1", "ag.sheaf-laplacian"),
        ag_manifest("ag.period-stokes@1", "ag.period-stokes"),
        ag_period_stokes_audit_manifest(),
        ag_manifest("ag.support-transfer@1", "ag.support-transfer"),
    ]);
    manifests
}

fn ag_coherence_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.coherence-obstruction@1".to_string(),
        law_id: "ag.coherence-obstruction".to_string(),
        required_atom_constructors: Vec::new(),
        required_predicates: vec!["coherence.tripleMismatch".to_string()],
        required_molecule_condition:
            "archmap/v2 contexts and selected cover triple-overlap 2-skeleton".to_string(),
        scope_filtering_rule:
            "selected finite poset site and cover from MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing coherence witness atoms are unmeasured; incomplete 2-skeleton is not_computed"
                .to_string(),
        pass_criteria:
            "selected-cover banded abelian F2 H2 coherence cocycle is a coboundary"
                .to_string(),
        violation_criteria:
            "selected-cover banded abelian F2 H2 coherence cocycle has a representative outside im d1"
                .to_string(),
        typed_result_schema: "archsig-measurement-packet/v1".to_string(),
        distance_contribution: "structural H2 coherence verdict remains cover-relative and F2-banded"
            .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: vec!["ag_coherence_obstruction_negative.json".to_string()],
    }
}

fn ag_boundary_residue_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.boundary-residue@1".to_string(),
        law_id: "ag.boundary-residue".to_string(),
        required_atom_constructors: Vec::new(),
        required_predicates: vec![
            "boundary-residue.patchRole".to_string(),
            "boundary-residue.restrictionColumn".to_string(),
            "boundary-residue.mismatchSection".to_string(),
        ],
        required_molecule_condition:
            "archmap/v2 selected cover with core, feature, and boundary patch roles plus finite F2 restriction columns"
                .to_string(),
        scope_filtering_rule:
            "selected finite cover and witnessFamily from MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing patch classification, mismatch section, or restriction matrix is not_computed"
                .to_string(),
        pass_criteria:
            "selected boundary mismatch section lies in the F2 image of Mayer-Vietoris d0"
                .to_string(),
        violation_criteria:
            "selected boundary mismatch section is outside the F2 image of Mayer-Vietoris d0"
                .to_string(),
        typed_result_schema: "archsig-measurement-packet/v1".to_string(),
        distance_contribution:
            "structural boundary residue verdict remains selected-cover and F2-relative"
                .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: Vec::new(),
    }
}

fn ag_period_stokes_audit_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.period-stokes-audit@1".to_string(),
        law_id: "ag.period-stokes-audit".to_string(),
        required_atom_constructors: Vec::new(),
        required_predicates: vec![
            "period.dOmegaIntegral".to_string(),
            "period.boundaryPeriod".to_string(),
        ],
        required_molecule_condition:
            "archmap/v2 selected cover with supplied dOmegaIntegral and boundaryPeriod audit values"
                .to_string(),
        scope_filtering_rule:
            "selected finite cover and fixed coefficient MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing audit pairs or unresolved strict coefficient data yields unknown/not_computed, not a crash"
                .to_string(),
        pass_criteria:
            "all supplied fixed-coefficient Stokes audit residuals are zero".to_string(),
        violation_criteria:
            "at least one supplied fixed-coefficient Stokes audit residual is nonzero".to_string(),
        typed_result_schema: "archsig-measurement-packet/v1".to_string(),
        distance_contribution:
            "structural verdict is scoped to supplied independent Stokes accounting values only"
                .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/computedInvariants".to_string(),
            "/analyticReadings".to_string(),
            "/assumptions".to_string(),
        ],
        negative_fixtures: Vec::new(),
    }
}

fn ag_section_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.section-factorization@1".to_string(),
        law_id: "ag.section-factorization".to_string(),
        required_atom_constructors: Vec::new(),
        required_predicates: vec![
            "section-factorization.obstructionGenerator".to_string(),
            "section-factorization.witnessAssignment".to_string(),
        ],
        required_molecule_condition:
            "archmap/v2 selected cover, finite forbidden supports, and one selected Boolean section"
                .to_string(),
        scope_filtering_rule:
            "selected finite poset site and witness family from MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing witnessAssignment or obstructionGenerator atoms are not_computed; partial undecidable assignment is unknown"
                .to_string(),
        pass_criteria:
            "selected total section avoids every minimal forbidden support, so s^* I_Ob^U=0"
                .to_string(),
        violation_criteria: "selected section active support contains a minimal forbidden support"
            .to_string(),
        typed_result_schema: "archsig-measurement-packet/v1".to_string(),
        distance_contribution:
            "structural section factorization verdict remains selected-section relative".to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: vec!["ag_section_factorization_negative.json".to_string()],
    }
}

fn ag_restriction_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.restriction-compatibility@1".to_string(),
        law_id: "ag.restriction-compatibility".to_string(),
        required_atom_constructors: Vec::new(),
        required_predicates: vec![
            "restriction-compatibility.restrictionIdealGenerator".to_string(),
        ],
        required_molecule_condition:
            "archmap/v2 contexts, selected cover restriction edges, and finite ideal generator supports"
                .to_string(),
        scope_filtering_rule:
            "selected finite poset site and cover from MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing restriction edges or endpoint generator contracts are not_computed".to_string(),
        pass_criteria:
            "every selected restriction edge carries source ideal generators into the target ideal"
                .to_string(),
        violation_criteria:
            "some selected restriction edge has a source generator with no target generator dividing its support"
                .to_string(),
        typed_result_schema: "archsig-measurement-packet/v1".to_string(),
        distance_contribution:
            "structural restriction compatibility verdict remains selected-cover and presentation-relative"
                .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: vec!["ag_restriction_compatibility_negative.json".to_string()],
    }
}

fn ag_manifest(evaluator_id: &str, law_id: &str) -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: evaluator_id.to_string(),
        law_id: law_id.to_string(),
        required_atom_constructors: Vec::new(),
        required_predicates: Vec::new(),
        required_molecule_condition:
            "archmap/v2 contexts and covers replace molecule primary input".to_string(),
        scope_filtering_rule: "selected finite poset site from MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing MeasurementProfile fails validation before evaluator execution".to_string(),
        pass_criteria: "schema foundation only; concrete AG evaluator verdicts are follow-up work"
            .to_string(),
        violation_criteria:
            "schema foundation only; concrete AG evaluator verdicts are follow-up work".to_string(),
        typed_result_schema: "archsig-measurement-packet/v1".to_string(),
        distance_contribution: "structural verdict and analytic readings remain separated"
            .to_string(),
        summary_output_refs: vec![
            "/structuralVerdict".to_string(),
            "/analyticReadings".to_string(),
        ],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: vec![
            "tests/fixtures/ag_measurement/law_policy_missing_profile.json".to_string(),
        ],
    }
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
        typed_result_schema: "typed-evaluator-result/v1".to_string(),
        distance_contribution: "registry-owned structural-pressure contribution".to_string(),
        summary_output_refs: vec!["typedResults[].summary".to_string()],
        detail_output_refs: vec!["typedResults[].evidenceRefs".to_string()],
        negative_fixtures: vec!["law_policy_dsl_field.json".to_string()],
    }
}
