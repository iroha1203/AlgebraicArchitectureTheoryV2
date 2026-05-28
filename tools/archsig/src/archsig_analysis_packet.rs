use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    ARCHMAP_SCHEMA_VERSION, ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
    ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION, ArchSigAnalysisArtifactRefV0,
    ArchSigAnalysisPacketV0, ArchSigAnalysisPacketValidationInputV0,
    ArchSigAnalysisPacketValidationReportV0, ArchSigAnalysisPacketValidationSummaryV0,
    ArchSigAtomConfigurationSummaryV0, ArchSigFlatnessReadingV0, ArchSigLayerSplitV0,
    ArchSigMoleculeReadingV0, ArchSigObstructionCircuitV0, ArchSigRepairOperationCandidateV0,
    ArchSigSignatureAxisReadingV0, LAW_POLICY_SCHEMA_VERSION, ValidationCheck, ValidationExample,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 6] = [
    "ArchSig analysis packet is not a Lean theorem proof",
    "ArchSig analysis packet is not global architecture truth",
    "ArchSig analysis packet does not prove source extraction completeness",
    "signature axes are law-policy-relative, not universal quality scores",
    "flatness reading is blocked by coverage gaps and exactness assumptions",
    "repair operation candidates are not automatic safe refactorings",
];

pub fn static_archsig_analysis_packet() -> ArchSigAnalysisPacketV0 {
    ArchSigAnalysisPacketV0 {
        schema_version: ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION.to_string(),
        analysis_id: "archsig-analysis-fixture".to_string(),
        generated_at: "2026-05-23T00:00:00Z".to_string(),
        arch_map_ref: artifact_ref(
            "fixture-archmap-atom-observation",
            "archmap",
            ARCHMAP_SCHEMA_VERSION,
            Some("tools/archsig/tests/fixtures/minimal/archmap.json"),
        ),
        selected_law_policy_ref: artifact_ref(
            "llm-native-aat-law-policy-fixture",
            "law-policy",
            LAW_POLICY_SCHEMA_VERSION,
            Some("tools/archsig/tests/fixtures/minimal/law_policy.json"),
        ),
        atom_configuration_summary: ArchSigAtomConfigurationSummaryV0 {
            atom_observation_count: 4,
            molecule_observation_count: 1,
            semantic_observation_count: 1,
            observation_gap_count: 1,
            concern_hint_count: 1,
            configuration_boundary:
                "counts are read from one bounded ArchMap fixture, not complete architecture enumeration"
                    .to_string(),
            coverage_summary: vec![
                "static source atoms observed".to_string(),
                "semantic contract observation observed".to_string(),
                "runtime trace remains unavailable".to_string(),
            ],
            source_refs: strings(&[
                "atom:component:route-users",
                "atom:component:service-user",
                "atom:relation:route-service",
                "atom:contract:create-user",
                "gap-runtime-user-db-trace",
            ]),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        molecule_readings: vec![ArchSigMoleculeReadingV0 {
            molecule_reading_id: "molecule-reading:user-request-responsibility".to_string(),
            molecule_observation_ref: "molecule:user-request-responsibility".to_string(),
            law_refs: vec!["law:semantic-contract-alignment".to_string()],
            atom_observation_refs: strings(&[
                "atom:relation:route-service",
                "atom:contract:create-user",
            ]),
            reading:
                "observed route/service/contract atoms form one operation-responsibility molecule"
                    .to_string(),
            evidence_summary:
                "molecule reading uses ArchMap atom observations and the selected semantic-contract law"
                    .to_string(),
            evidence_boundary:
                "law-relative reading over observed atoms; not a primitive atom and not theorem evidence"
                    .to_string(),
            source_refs: strings(&["doc-architecture", "test-user-contract"]),
            interpretation_notes_for_llm: vec![
                "Explain this as a responsibility grouping over observed atoms.".to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }],
        obstruction_circuits: vec![ArchSigObstructionCircuitV0 {
            obstruction_circuit_id: "obstruction:semantic-contract-mismatch:create-user"
                .to_string(),
            law_ref: "law:semantic-contract-alignment".to_string(),
            witness_rule_ref: "witness:semantic-contract-mismatch".to_string(),
            circuit_kind: "SemanticMismatchCircuit".to_string(),
            atom_observation_refs: strings(&[
                "atom:relation:route-service",
                "atom:contract:create-user",
            ]),
            molecule_reading_refs: vec![
                "molecule-reading:user-request-responsibility".to_string(),
            ],
            concern_hint_refs: vec!["concern:missing-compensation".to_string()],
            signature_axis_refs: vec!["sig-axis:semantic-inconsistency".to_string()],
            minimality_reading:
                "minimal within the selected operation molecule and semantic contract witness rule"
                    .to_string(),
            evidence_summary:
                "constructed from the concern hint, contract atom, relation atom, and semantic molecule reading"
                    .to_string(),
            evidence_boundary:
                "computed ArchSig witness under selected LawPolicy; not an ArchMap observation"
                    .to_string(),
            interpretation_notes_for_llm: vec![
                "Describe the obstruction as law-relative, not as a universal architecture defect."
                    .to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }],
        signature_axes: vec![
            ArchSigSignatureAxisReadingV0 {
                signature_axis_id: "sig-axis:layer-violation".to_string(),
                law_ref: "law:layer-respecting".to_string(),
                axis_ref: "axis:layer-violation".to_string(),
                value_type: "nat".to_string(),
                value: 0,
                zero_reading:
                    "zero means no selected layer violation witness was constructed under declared coverage"
                        .to_string(),
                coverage_status: "covered-for-selected-static-atoms".to_string(),
                exactness_assumptions: vec![
                    "selected layer law observes only declared route/service relation atoms".to_string(),
                ],
                evidence_summary:
                    "no BoundaryLeakCircuit witness was constructed from the fixture atoms"
                        .to_string(),
                source_refs: strings(&["atom:relation:route-service"]),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            },
            ArchSigSignatureAxisReadingV0 {
                signature_axis_id: "sig-axis:semantic-inconsistency".to_string(),
                law_ref: "law:semantic-contract-alignment".to_string(),
                axis_ref: "axis:semantic-inconsistency".to_string(),
                value_type: "nat".to_string(),
                value: 1,
                zero_reading:
                    "nonzero means one selected semantic mismatch witness was constructed"
                        .to_string(),
                coverage_status: "runtime-gap-blocked".to_string(),
                exactness_assumptions: vec![
                    "runtime trace gap blocks global zero reflection".to_string(),
                ],
                evidence_summary:
                    "one SemanticMismatchCircuit witness is present under the selected LawPolicy"
                        .to_string(),
                source_refs: strings(&[
                    "atom:contract:create-user",
                    "concern:missing-compensation",
                ]),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            },
        ],
        flatness_reading: ArchSigFlatnessReadingV0 {
            reading_id: "flatness:selected-law-policy".to_string(),
            selected_law_policy_ref: "llm-native-aat-law-policy-fixture".to_string(),
            status: "nonflatUnderSelectedPolicy".to_string(),
            zero_signature_axis_refs: vec!["sig-axis:layer-violation".to_string()],
            nonzero_signature_axis_refs: vec!["sig-axis:semantic-inconsistency".to_string()],
            blocked_by_coverage_gaps: vec!["gap-runtime-user-db-trace".to_string()],
            evidence_boundary:
                "flatness is read from selected signature axes; coverage gaps block global zero claims"
                    .to_string(),
            interpretation_notes_for_llm: vec![
                "Report this as selected-policy non-flatness, not global architecture quality."
                    .to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        static_runtime_semantic_layer_split: ArchSigLayerSplitV0 {
            static_observation_refs: strings(&[
                "atom:component:route-users",
                "atom:component:service-user",
                "atom:relation:route-service",
            ]),
            runtime_observation_refs: vec!["gap-runtime-user-db-trace".to_string()],
            semantic_observation_refs: strings(&[
                "atom:contract:create-user",
                "semantic:create-user-flow",
            ]),
            split_boundary:
                "runtime layer is gap-preserved and must not be rounded into measured zero"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        repair_operation_candidates: vec![ArchSigRepairOperationCandidateV0 {
            repair_operation_candidate_id: "repair:add-compensation-path".to_string(),
            operation_kind: "add-compensation-operation".to_string(),
            target_obstruction_refs: vec![
                "obstruction:semantic-contract-mismatch:create-user".to_string(),
            ],
            preserved_invariants: vec![
                "preserve route/service dependency direction".to_string(),
                "preserve create-user contract visibility".to_string(),
            ],
            preconditions: vec![
                "identify authoritative compensation owner".to_string(),
                "supply runtime trace evidence before claiming global zero".to_string(),
            ],
            expected_signature_axis_effects: vec![
                "decrease sig-axis:semantic-inconsistency if compensation semantics are observed"
                    .to_string(),
            ],
            transfer_risks: vec![
                "may transfer complexity into runtime retry or idempotency layer".to_string(),
            ],
            evidence_boundary:
                "repair candidate is an operation hypothesis over the selected packet, not an automatic patch"
                    .to_string(),
            interpretation_notes_for_llm: vec![
                "Explain preserved invariants before proposing implementation work.".to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }],
        evidence_boundary:
            "packet is computed from one ArchMap fixture and one selected LawPolicy fixture"
                .to_string(),
        interpretation_notes_for_llm: vec![
            "Lead with selected LawPolicy scope and evidence gaps.".to_string(),
            "Explain each nonzero signature axis with source refs and non-conclusions.".to_string(),
        ],
        excluded_readings: vec![
            "single architecture quality score".to_string(),
            "global architecture lawfulness".to_string(),
            "automatic repair safety".to_string(),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn validate_archsig_analysis_packet_report(
    packet: &ArchSigAnalysisPacketV0,
    input_path: &str,
) -> ArchSigAnalysisPacketValidationReportV0 {
    let checks = vec![
        check_schema_version(packet),
        check_refs_and_identity(packet),
        check_law_relative_analysis(packet),
        check_signature_and_flatness(packet),
        check_repair_candidates(packet),
        check_llm_interpretation_surface(packet),
        check_non_conclusions(packet),
    ];
    let summary = ArchSigAnalysisPacketValidationSummaryV0 {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        molecule_reading_count: packet.molecule_readings.len(),
        obstruction_circuit_count: packet.obstruction_circuits.len(),
        signature_axis_count: packet.signature_axes.len(),
        repair_operation_candidate_count: packet.repair_operation_candidates.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ArchSigAnalysisPacketValidationReportV0 {
        schema_version: ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ArchSigAnalysisPacketValidationInputV0 {
            schema_version: packet.schema_version.clone(),
            path: input_path.to_string(),
            analysis_id: packet.analysis_id.clone(),
            arch_map_ref: packet.arch_map_ref.artifact_id.clone(),
            selected_law_policy_ref: packet.selected_law_policy_ref.artifact_id.clone(),
        },
        packet: packet.clone(),
        summary,
        checks,
    }
}

fn check_schema_version(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut check = validation_check(
        "archsig-analysis-packet-schema-version-supported",
        "ArchSig analysis packet schema version is supported",
        if packet.schema_version == ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported ArchSig analysis packet schemaVersion: {}",
            packet.schema_version
        ));
    }
    check
}

fn check_refs_and_identity(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    push_blank(&mut examples, "analysisId", &packet.analysis_id);
    push_blank(&mut examples, "generatedAt", &packet.generated_at);
    push_blank(
        &mut examples,
        "archMapRef.artifactId",
        &packet.arch_map_ref.artifact_id,
    );
    push_blank(
        &mut examples,
        "selectedLawPolicyRef.artifactId",
        &packet.selected_law_policy_ref.artifact_id,
    );
    if packet.arch_map_ref.schema_version != ARCHMAP_SCHEMA_VERSION {
        examples.push(generic_validation_example(
            "archMapRef.schemaVersion",
            &packet.arch_map_ref.schema_version,
            "analysis packet must reference the current ArchMap observation schema",
        ));
    }
    if packet.selected_law_policy_ref.schema_version != LAW_POLICY_SCHEMA_VERSION {
        examples.push(generic_validation_example(
            "selectedLawPolicyRef.schemaVersion",
            &packet.selected_law_policy_ref.schema_version,
            "analysis packet must reference a LawPolicy artifact",
        ));
    }
    check_from_examples(
        "archsig-analysis-packet-refs-and-identity",
        "analysis identity and ArchMap / LawPolicy references are recorded",
        examples,
        "fail",
    )
}

fn check_law_relative_analysis(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let axis_ids = set(packet
        .signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let molecule_ids = set(packet
        .molecule_readings
        .iter()
        .map(|reading| reading.molecule_reading_id.as_str()));
    let mut examples = Vec::new();
    examples.extend(duplicate_examples(
        "obstructionCircuits[].obstructionCircuitId",
        duplicates(
            packet
                .obstruction_circuits
                .iter()
                .map(|circuit| circuit.obstruction_circuit_id.as_str()),
        ),
    ));
    for circuit in &packet.obstruction_circuits {
        push_blank(
            &mut examples,
            &circuit.obstruction_circuit_id,
            &circuit.law_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} witnessRuleRef", circuit.obstruction_circuit_id),
            &circuit.witness_rule_ref,
        );
        if circuit.signature_axis_refs.is_empty() {
            examples.push(generic_validation_example(
                &circuit.obstruction_circuit_id,
                "signatureAxisRefs",
                "obstruction circuit must declare affected signature axes",
            ));
        }
        for axis_ref in &circuit.signature_axis_refs {
            if !axis_ids.contains(axis_ref.as_str()) {
                examples.push(generic_validation_example(
                    &circuit.obstruction_circuit_id,
                    axis_ref,
                    "obstruction circuit references an unknown signature axis",
                ));
            }
        }
        for molecule_ref in &circuit.molecule_reading_refs {
            if !molecule_ids.contains(molecule_ref.as_str()) {
                examples.push(generic_validation_example(
                    &circuit.obstruction_circuit_id,
                    molecule_ref,
                    "obstruction circuit references an unknown molecule reading",
                ));
            }
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", circuit.obstruction_circuit_id),
            &circuit.evidence_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceSummary", circuit.obstruction_circuit_id),
            &circuit.evidence_summary,
        );
    }
    check_from_examples(
        "archsig-analysis-packet-law-relative-obstructions",
        "obstruction circuits are LawPolicy-relative and cross-reference molecule and signature readings",
        examples,
        "fail",
    )
}

fn check_signature_and_flatness(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let axis_ids = set(packet
        .signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let mut examples = Vec::new();
    examples.extend(duplicate_examples(
        "signatureAxes[].signatureAxisId",
        duplicates(
            packet
                .signature_axes
                .iter()
                .map(|axis| axis.signature_axis_id.as_str()),
        ),
    ));
    for axis in &packet.signature_axes {
        push_blank(&mut examples, &axis.signature_axis_id, &axis.law_ref);
        push_blank(
            &mut examples,
            &format!("{} axisRef", axis.signature_axis_id),
            &axis.axis_ref,
        );
        if axis.exactness_assumptions.is_empty() || has_blank(&axis.exactness_assumptions) {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                "exactnessAssumptions",
                "signature axis must declare exactness assumptions",
            ));
        }
        if axis.coverage_status.trim().is_empty() {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                "coverageStatus",
                "signature axis must keep coverage status explicit",
            ));
        }
    }
    for axis_ref in packet
        .flatness_reading
        .zero_signature_axis_refs
        .iter()
        .chain(packet.flatness_reading.nonzero_signature_axis_refs.iter())
    {
        if !axis_ids.contains(axis_ref.as_str()) {
            examples.push(generic_validation_example(
                &packet.flatness_reading.reading_id,
                axis_ref,
                "flatness reading references an unknown signature axis",
            ));
        }
    }
    push_blank(
        &mut examples,
        "flatnessReading.evidenceBoundary",
        &packet.flatness_reading.evidence_boundary,
    );
    check_from_examples(
        "archsig-analysis-packet-signature-and-flatness",
        "signature axes and flatness reading preserve coverage and exactness boundaries",
        examples,
        "fail",
    )
}

fn check_repair_candidates(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let obstruction_ids = set(packet
        .obstruction_circuits
        .iter()
        .map(|circuit| circuit.obstruction_circuit_id.as_str()));
    let mut examples = Vec::new();
    for repair in &packet.repair_operation_candidates {
        if repair.target_obstruction_refs.is_empty() {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "targetObstructionRefs",
                "repair operation candidate must name target obstructions",
            ));
        }
        for obstruction_ref in &repair.target_obstruction_refs {
            if !obstruction_ids.contains(obstruction_ref.as_str()) {
                examples.push(generic_validation_example(
                    &repair.repair_operation_candidate_id,
                    obstruction_ref,
                    "repair candidate references an unknown obstruction circuit",
                ));
            }
        }
        if repair.preserved_invariants.is_empty() || has_blank(&repair.preserved_invariants) {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "preservedInvariants",
                "repair candidate must declare preserved invariants",
            ));
        }
        if repair.preconditions.is_empty() || has_blank(&repair.preconditions) {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "preconditions",
                "repair candidate must declare preconditions",
            ));
        }
        if repair.transfer_risks.is_empty() || has_blank(&repair.transfer_risks) {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "transferRisks",
                "repair candidate must retain transfer risks",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", repair.repair_operation_candidate_id),
            &repair.evidence_boundary,
        );
    }
    check_from_examples(
        "archsig-analysis-packet-repair-operation-boundary",
        "repair operation candidates preserve invariant, precondition, transfer risk, and evidence boundaries",
        examples,
        "fail",
    )
}

fn check_llm_interpretation_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    push_blank(&mut examples, "evidenceBoundary", &packet.evidence_boundary);
    if packet.interpretation_notes_for_llm.is_empty()
        || has_blank(&packet.interpretation_notes_for_llm)
    {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "interpretationNotesForLLM",
            "packet must retain LLM-facing interpretation notes",
        ));
    }
    if packet.excluded_readings.is_empty() || has_blank(&packet.excluded_readings) {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "excludedReadings",
            "packet must retain excluded readings",
        ));
    }
    check_from_examples(
        "archsig-analysis-packet-llm-interpretation-surface",
        "packet carries evidence boundary, excluded readings, and LLM interpretation notes",
        examples,
        "fail",
    )
}

fn check_non_conclusions(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let present = packet
        .non_conclusions
        .iter()
        .map(|value| value.as_str())
        .collect::<BTreeSet<_>>();
    let examples = REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| !present.contains(**required))
        .map(|required| {
            generic_validation_example(
                &packet.analysis_id,
                required,
                "missing required ArchSig analysis packet non-conclusion",
            )
        })
        .collect();
    check_from_examples(
        "archsig-analysis-packet-non-conclusion-boundary",
        "packet keeps theorem, global truth, completeness, score, flatness, and repair boundaries explicit",
        examples,
        "fail",
    )
}

fn artifact_ref(
    artifact_id: &str,
    artifact_kind: &str,
    schema_version: &str,
    path: Option<&str>,
) -> ArchSigAnalysisArtifactRefV0 {
    ArchSigAnalysisArtifactRefV0 {
        artifact_id: artifact_id.to_string(),
        artifact_kind: artifact_kind.to_string(),
        schema_version: schema_version.to_string(),
        path: path.map(|value| value.to_string()),
        content_hash: None,
    }
}

fn check_from_examples(
    id: &str,
    title: &str,
    examples: Vec<ValidationExample>,
    failure_result: &str,
) -> ValidationCheck {
    let mut check = validation_check(
        id,
        title,
        if examples.is_empty() {
            "pass"
        } else {
            failure_result
        },
    );
    check.count = Some(examples.len());
    check.examples = examples;
    check
}

fn duplicate_examples(field: &str, duplicates: Vec<String>) -> Vec<ValidationExample> {
    duplicates
        .into_iter()
        .map(|id| generic_validation_example(field, &id, "duplicate id"))
        .collect()
}

fn push_blank(examples: &mut Vec<ValidationExample>, field: &str, value: &str) {
    if value.trim().is_empty() {
        examples.push(generic_validation_example(
            field,
            value,
            "field must be non-empty",
        ));
    }
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn set<'a>(values: impl Iterator<Item = &'a str>) -> BTreeSet<&'a str> {
    values.collect()
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_archsig_analysis_packet_validates() {
        let packet = static_archsig_analysis_packet();
        let report = validate_archsig_analysis_packet_report(&packet, "archsig-analysis.json");
        assert_eq!(
            report.schema_version,
            ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.summary.result, "pass");
        assert_eq!(report.summary.obstruction_circuit_count, 1);
        assert!(report.checks.iter().any(|check| {
            check.id == "archsig-analysis-packet-non-conclusion-boundary" && check.result == "pass"
        }));
    }

    #[test]
    fn missing_packet_non_conclusion_fails() {
        let mut packet = static_archsig_analysis_packet();
        packet.non_conclusions.clear();
        let report = validate_archsig_analysis_packet_report(&packet, "bad-analysis.json");
        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| {
            check.id == "archsig-analysis-packet-non-conclusion-boundary" && check.result == "fail"
        }));
    }

    #[test]
    fn repair_without_preconditions_fails() {
        let mut packet = static_archsig_analysis_packet();
        packet.repair_operation_candidates[0].preconditions.clear();
        let report = validate_archsig_analysis_packet_report(&packet, "bad-analysis.json");
        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| {
            check.id == "archsig-analysis-packet-repair-operation-boundary"
                && check.result == "fail"
        }));
    }

    #[test]
    fn canonical_fixture_matches_static_analysis_packet() {
        let fixture: ArchSigAnalysisPacketV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/archsig_analysis_packet.json"
        ))
        .expect("ArchSig analysis packet fixture parses");
        assert_eq!(fixture, static_archsig_analysis_packet());
    }
}
