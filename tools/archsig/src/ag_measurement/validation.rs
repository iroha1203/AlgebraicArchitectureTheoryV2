#[cfg(test)]
fn validate_measurement_packet_v1(packet: &ArchSigMeasurementPacketV1) -> Vec<ValidationCheck> {
    let packet_value = serde_json::to_value(packet).unwrap_or_else(|_| json!({}));
    validate_measurement_packet_components(packet, &packet_value)
}

pub fn validate_measurement_packet_value_v1(packet_value: &Value) -> Vec<ValidationCheck> {
    let typed_packet =
        match serde_json::from_value::<ArchSigMeasurementPacketV1>(packet_value.clone()) {
            Ok(packet) => packet,
            Err(error) => {
                let mut check = validation_check(
                    "measurement-packet-schema052-typed-shape",
                    "measurement packet parses as ArchSigMeasurementPacketV1",
                    "fail",
                );
                check.reason = Some(format!("measurement packet shape is invalid: {error}"));
                return vec![check];
            }
        };
    validate_measurement_packet_components(&typed_packet, packet_value)
}

fn validate_measurement_packet_components(
    packet: &ArchSigMeasurementPacketV1,
    packet_value: &Value,
) -> Vec<ValidationCheck> {
    vec![
        check_packet_unknown_fields(packet_value),
        check_packet_schema(packet),
        check_structural_verdict_values(packet),
        check_structural_verdict_evaluators(packet),
        check_structural_verdict_data(packet),
        check_structural_verdict_new_shape_value(packet_value),
        check_computed_invariant_shape_value(packet_value),
        check_analytic_regime_boundary(packet, packet_value),
        check_assumption_ledger_value(packet, packet_value),
        check_supplied_data_shape(packet),
        check_boundary_statements(packet),
    ]
}

fn check_packet_unknown_fields(packet_value: &Value) -> ValidationCheck {
    let mut examples = Vec::new();
    check_object_keys(
        packet_value,
        "measurementPacket",
        &[
            "schema",
            "packetId",
            "profile",
            "profiles",
            "structuralVerdict",
            "computedInvariants",
            "analyticReadings",
            "assumptions",
            "suppliedData",
            "boundaryStatements",
            "nonConclusions",
            "toolVersion",
            "runId",
            "inputDigests",
            "componentFingerprints",
        ],
        &mut examples,
    );
    check_object_keys(
        &packet_value["profile"],
        "profile",
        &[
            "schema",
            "profileId",
            "siteRef",
            "coverRef",
            "coefficient",
            "effCoeff",
            "resolutionSelector",
            "domain",
            "zeroPredicate",
            "nonZeroPredicate",
            "certSelector",
            "verdictDiscipline",
            "diagnosticCeiling",
            "analytic",
            "finiteBounds",
        ],
        &mut examples,
    );
    check_object_keys(
        &packet_value["profile"]["finiteBounds"],
        "profile.finiteBounds",
        &[
            "maxSquareFreeWitnessVariables",
            "maxCoherenceContexts",
            "maxTorWitnessVariables",
            "maxBoundaryResidueVariables",
            "maxLaplacianCells",
            "maxPeriodCycles",
            "maxTransferTargets",
        ],
        &mut examples,
    );
    // This is the union of the normalized schema fields and the evaluator-specific
    // fields emitted by the current measurement packet producers.
    const COMPUTED_INVARIANT_FIELDS: &[&str] = &[
        "invariantId",
        "id",
        "readingId",
        "computedInvariantId",
        "kind",
        "evaluator",
        "value",
        "representation",
        "classVocabulary",
        "archmapRef",
        "atomCount",
        "contextCount",
        "coverCount",
        "doctrineFingerprint",
        "boundaryNote",
        "claimScope",
        "conclusionCode",
        "contract",
        "classSupport",
        "coefficient",
        "coverNerveProjection",
        "dimensions",
        "method",
        "methodStatus",
        "nerveShape",
        "observedCocycle",
        "rankD0",
        "reason",
        "restrictionEdgeCount",
        "selectedCoverRef",
        "selectedH2",
        "status",
        "whatNext",
        "theorem12_4Discharge",
        "b1NerveReading",
        "capacityFormula",
        "capacityLowerBound",
        "eulerCharacteristic",
        "eulerFormula",
        "measuredCechVerdictEcho",
        "structuralVerdictRef",
        "selectedSectionRef",
        "sectionFactorization",
        "restrictionCompatibility",
        "boundaryMembership",
        "minimalForbiddenSupports",
        "alexanderDualRepair",
        "transferTargets",
        "residue",
        "pairings",
        "periods",
        "laplacian",
        "cochainCells",
        "sagaConclusionCode",
        "displayedRequiredLawsHold",
        "generatedQuotient",
        "detectorFindings",
        "detectorCount",
        "groundedSurfaceRef",
        "diagnosticCeiling",
        "residualKind",
        "commonAmbient",
        "lawConflicts",
        "lawIdeals",
        "nonConclusions",
        "proxyComparison",
        "resolution",
        "resolutionSelectorEffective",
        "torByDegree",
        "witnessVariables",
        "analyticReadingRef",
        "assumptionBoundary",
        "boundarySection",
        "cellRefs",
        "cocycleGate",
        "coherenceWitnesses",
        "cohomologyQuotient",
        "components",
        "cycleBasis",
        "d2RowCount",
        "deltaComplex",
        "dimension",
        "edgeChecks",
        "edgeCount",
        "faceCount",
        "faces",
        "facetDimensionReading",
        "facets",
        "failureCode",
        "forms",
        "h2Dimension",
        "imageMembership",
        "irreducibleComponentCount",
        "isPure",
        "laplacianMatrix",
        "linkBoundaryReading",
        "linkReducedBetti",
        "locusSymbol",
        "nsdepthCertificate",
        "obstructionIdeal",
        "pairingAtomRefs",
        "patchRoles",
        "periodPairingMatrix",
        "rankD1",
        "rankKerD2",
        "repairPathAtomRefs",
        "representative",
        "residualClassSupport",
        "residualDerivation",
        "derivedComplexRef",
        "derivedFrom",
        "suppliedCochainMap",
        "presentationGenerated",
        "measuredClassDivergence",
        "generatedQuotientTransfer",
        "resolutionSelector",
        "restrictionMatrix",
        "sectionAssignment",
        "sourceRefs",
        "stokesAudit",
        "supportLocalizedPremise",
        "tetrahedra",
        "tetrahedronCount",
        "transferMeasurementPairing",
        "transferResidue",
        "violatedForbiddenSupports",
        "wassersteinTransferCost",
        "schema",
        "groundedSurfaceRef",
        "theoremRef",
        "generatedQuotient",
        "detectorFindings",
        "detectorCount",
        "observedEdgeCount",
        "unobservedEdgeRefs",
        "sectionObservation",
        "harmonicDebtNorm",
        "essentialRepairLowerBound",
        "lowerBoundStatus",
        "sourceProxyReading",
        "nonConclusion",
    ];
    for (index, invariant) in packet_value["computedInvariants"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            invariant,
            &format!("computedInvariants[{index}]"),
            COMPUTED_INVARIANT_FIELDS,
            &mut examples,
        );
        if invariant.get("contract").is_some() {
            let contract_label = format!("computedInvariants[{index}].contract");
            examples.push(generic_validation_example(
                &contract_label,
                "contract",
                "contract is retired with the saga comparison slot",
            ));
        }
    }
    for (index, row) in packet_value["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let prefix = format!("structuralVerdict[{index}]");
        check_object_keys(
            row,
            &prefix,
            &[
                "verdictRef",
                "evaluator",
                "law",
                "target",
                "verdict",
                "verdictData",
                "dependsOnAssumptions",
                "evidence",
                "reason",
            ],
            &mut examples,
        );
        check_object_keys(
            &row["target"],
            &format!("{prefix}.target"),
            &["kind", "coverRef", "coefficient", "scopeSize", "classRef"],
            &mut examples,
        );
        check_object_keys(
            &row["target"]["scopeSize"],
            &format!("{prefix}.target.scopeSize"),
            &["contexts", "edges", "triangles"],
            &mut examples,
        );
        check_object_keys(
            &row["verdictData"],
            &format!("{prefix}.verdictData"),
            &["inScope", "zero", "nonZero", "methodStatus", "certRef"],
            &mut examples,
        );
        check_object_keys(
            &row["evidence"],
            &format!("{prefix}.evidence"),
            &["computedInvariantRefs", "sourceRefs"],
            &mut examples,
        );
    }
    for (index, reading) in packet_value["analyticReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            reading,
            &format!("analyticReadings[{index}]"),
            &[
                "readingId",
                "evaluator",
                "claimStatus",
                "fidelity",
                "value",
                "regime",
                "structuralVerdictRef",
            ],
            &mut examples,
        );
    }
    for (index, assumption) in packet_value["assumptions"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            assumption,
            &format!("assumptions[{index}]"),
            &[
                "assumptionId",
                "theoremRef",
                "assumption",
                "status",
                "checkedBy",
                "assumedBy",
                "scopeRefs",
            ],
            &mut examples,
        );
    }
    for (index, supplied) in packet_value["suppliedData"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            supplied,
            &format!("suppliedData[{index}]"),
            &["suppliedId", "kind", "sourceArtifactRef", "conformance"],
            &mut examples,
        );
        check_object_keys(
            &supplied["conformance"],
            &format!("suppliedData[{index}].conformance"),
            &["status", "checkRef", "boundary"],
            &mut examples,
        );
    }
    for (index, boundary) in packet_value["boundaryStatements"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        check_object_keys(
            boundary,
            &format!("boundaryStatements[{index}]"),
            &["id", "kind", "scopeRefs", "reason", "text"],
            &mut examples,
        );
    }
    check_examples(
        "measurement-packet-schema052-unknown-fields",
        "measurement packet objects reject unknown fields",
        examples,
    )
}

fn check_object_keys(
    value: &Value,
    path: &str,
    allowed: &[&str],
    examples: &mut Vec<ValidationExample>,
) {
    let Some(object) = value.as_object() else {
        return;
    };
    for key in object.keys() {
        if !allowed.contains(&key.as_str()) {
            examples.push(generic_validation_example(
                &format!("{path}.{key}"),
                "unknown",
                "unknown measurement packet fields are rejected",
            ));
        }
    }
}

fn check_packet_schema(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let mut check = validation_check(
        "measurement-packet-schema052-schema",
        "measurement packet uses archsig-measurement-packet/v0.5.4",
        if packet.schema == ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "expected {ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA}, found {}",
            packet.schema
        ));
    }
    check
}

fn check_structural_verdict_values(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let examples = packet
        .structural_verdict
        .iter()
        .filter(|row| !VERDICTS.contains(&row.verdict.as_str()))
        .map(|row| {
            generic_validation_example(
                &row.evaluator,
                &row.verdict,
                "structural verdict must be one of the five AG verdict values",
            )
        })
        .collect::<Vec<_>>();
    check_examples(
        "measurement-packet-schema052-five-verdict-values",
        "structural verdicts are limited to the five v0.5.4 values",
        examples,
    )
}

fn check_structural_verdict_evaluators(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let examples = packet
        .structural_verdict
        .iter()
        .filter(|row| !STRUCTURAL_VERDICT_EVALUATORS.contains(&row.evaluator.as_str()))
        .map(|row| {
            generic_validation_example(
                &row.evaluator,
                &row.law,
                "structural verdict evaluators must stay within the registered AG measurement surface",
            )
        })
        .collect::<Vec<_>>();
    check_examples(
        "measurement-packet-schema052-structural-verdict-evaluators",
        "structural verdict rows are limited to registered AG measurement evaluators",
        examples,
    )
}

fn check_structural_verdict_data(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for row in &packet.structural_verdict {
        if row.verdict_data.zero && row.verdict_data.non_zero {
            examples.push(generic_validation_example(
                &row.evaluator,
                "zero+nonZero",
                "Zero_M and NonZero_M verdict data must not both be true",
            ));
        }
        if row.verdict == "measured_zero" && !row.verdict_data.zero {
            examples.push(generic_validation_example(
                &row.evaluator,
                "measured_zero",
                "measured_zero requires zero=true in VerdictData",
            ));
        }
        if row.verdict == "measured_zero" && row.verdict_data.non_zero {
            examples.push(generic_validation_example(
                &row.evaluator,
                "measured_zero",
                "measured_zero requires nonZero=false in VerdictData",
            ));
        }
        if row.verdict == "measured_zero" && !row.verdict_data.in_scope {
            examples.push(generic_validation_example(
                &row.evaluator,
                "measured_zero",
                "measured_zero requires inScope=true in VerdictData",
            ));
        }
        if row.verdict == "measured_nonzero" && !row.verdict_data.non_zero {
            examples.push(generic_validation_example(
                &row.evaluator,
                "measured_nonzero",
                "measured_nonzero requires nonZero=true in VerdictData",
            ));
        }
        if matches!(
            row.verdict.as_str(),
            "unmeasured" | "unknown" | "not_computed"
        ) && (row.verdict_data.zero || row.verdict_data.non_zero)
        {
            examples.push(generic_validation_example(
                &row.evaluator,
                &row.verdict,
                "unmeasured, unknown, and not_computed are not zero or nonzero results",
            ));
        }
    }
    check_examples(
        "measurement-packet-schema052-verdict-data-boundary",
        "VerdictData keeps zero, nonzero, unmeasured, unknown, and not_computed separate",
        examples,
    )
}

fn check_structural_verdict_new_shape_value(packet_value: &Value) -> ValidationCheck {
    let invariant_ids = packet_value["computedInvariants"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|invariant| invariant["invariantId"].as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    let mut verdict_refs = BTreeSet::new();
    for (index, row) in packet_value["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let row_label = format!("structuralVerdict[{index}]");
        if let Some(verdict_ref) = row["verdictRef"].as_str() {
            if !verdict_refs.insert(verdict_ref) {
                examples.push(generic_validation_example(
                    &row_label,
                    verdict_ref,
                    "structural verdict verdictRef values must be unique",
                ));
            }
        }
        if row["verdictRef"].as_str().is_none_or(str::is_empty) {
            examples.push(generic_validation_example(
                &row_label,
                "verdictRef",
                "structural verdict rows must carry a non-empty verdictRef",
            ));
        } else {
            let expected_verdict_ref = format!(
                "structuralVerdict/{}/{}/{}",
                measurement_ref_segment(row["evaluator"].as_str().unwrap_or_default()),
                measurement_ref_segment(row["law"].as_str().unwrap_or_default()),
                measurement_ref_segment(
                    row["verdictData"]["methodStatus"]
                        .as_str()
                        .or_else(|| row["methodStatus"].as_str())
                        .unwrap_or_default(),
                )
            );
            if row["verdictRef"].as_str() != Some(expected_verdict_ref.as_str()) {
                examples.push(generic_validation_example(
                    &row_label,
                    "verdictRef",
                    "verdictRef must be derived from evaluator, law, and methodStatus",
                ));
            }
        }
        let target = &row["target"];
        if !target.is_object() {
            examples.push(generic_validation_example(
                &row_label,
                "target",
                "structural verdict rows must carry target block",
            ));
            continue;
        }
        for field in ["kind", "coverRef", "coefficient"] {
            if target[field].as_str().is_none_or(str::is_empty) {
                examples.push(generic_validation_example(
                    &row_label,
                    field,
                    "target kind / coverRef / coefficient must be non-empty",
                ));
            }
        }
        if target["coverRef"].as_str() != packet_value["profile"]["coverRef"].as_str() {
            examples.push(generic_validation_example(
                &row_label,
                "target.coverRef",
                "structural verdict target.coverRef must equal profile.coverRef",
            ));
        }
        if target["coefficient"].as_str() != packet_value["profile"]["coefficient"].as_str() {
            examples.push(generic_validation_example(
                &row_label,
                "target.coefficient",
                "structural verdict target.coefficient must equal profile.coefficient",
            ));
        }
        if !target["scopeSize"].is_object() {
            examples.push(generic_validation_example(
                &row_label,
                "target.scopeSize",
                "target.scopeSize must be an object",
            ));
        }
        let Some(evidence) = row.get("evidence").and_then(Value::as_object) else {
            examples.push(generic_validation_example(
                &row_label,
                "evidence",
                "structural verdict rows must carry evidence block",
            ));
            continue;
        };
        let Some(computed_refs_value) = evidence.get("computedInvariantRefs") else {
            examples.push(generic_validation_example(
                &row_label,
                "evidence.computedInvariantRefs",
                "structural verdict evidence must carry computedInvariantRefs array",
            ));
            continue;
        };
        let Some(computed_refs_array) = computed_refs_value.as_array() else {
            examples.push(generic_validation_example(
                &row_label,
                "evidence.computedInvariantRefs",
                "structural verdict evidence computedInvariantRefs must be an array",
            ));
            continue;
        };
        let mut computed_refs = Vec::new();
        for (ref_index, invariant_ref) in computed_refs_array.iter().enumerate() {
            let Some(invariant_ref) = invariant_ref.as_str().filter(|value| !value.is_empty())
            else {
                examples.push(generic_validation_example(
                    &row_label,
                    &format!("evidence.computedInvariantRefs[{ref_index}]"),
                    "computed invariant refs must be non-empty strings",
                ));
                continue;
            };
            computed_refs.push(invariant_ref);
        }
        match evidence.get("sourceRefs").and_then(Value::as_array) {
            None => examples.push(generic_validation_example(
                &row_label,
                "evidence.sourceRefs",
                "structural verdict evidence must carry sourceRefs array",
            )),
            Some(source_refs) => {
                for (ref_index, source_ref) in source_refs.iter().enumerate() {
                    if source_ref.as_str().is_none_or(str::is_empty) {
                        examples.push(generic_validation_example(
                            &row_label,
                            &format!("evidence.sourceRefs[{ref_index}]"),
                            "source refs must be non-empty strings",
                        ));
                    }
                }
            }
        }
        if matches!(
            row["verdict"].as_str(),
            Some("measured_zero" | "measured_nonzero")
        ) && computed_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &row_label,
                "evidence.computedInvariantRefs",
                "measured verdicts must name supporting computed invariants",
            ));
        }
        for invariant_ref in computed_refs {
            if !invariant_ids.contains(invariant_ref) {
                examples.push(generic_validation_example(
                    &row_label,
                    invariant_ref,
                    "evidence.computedInvariantRefs must resolve to computedInvariants[].invariantId",
                ));
            } else if let Some(invariant_evaluator) = packet_value["computedInvariants"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|invariant| invariant["invariantId"].as_str() == Some(invariant_ref))
                .and_then(|invariant| invariant["evaluator"].as_str())
            {
                let row_evaluator = row["evaluator"].as_str().unwrap_or_default();
                if invariant_evaluator != row_evaluator {
                    examples.push(generic_validation_example(
                        &row_label,
                        invariant_ref,
                        &format!(
                            "computed invariant evaluator {invariant_evaluator} must match structural verdict evaluator {row_evaluator}"
                        ),
                        ));
                }
            } else {
                examples.push(generic_validation_example(
                    &row_label,
                    invariant_ref,
                    "referenced computed invariant must carry evaluator provenance",
                ));
            }
        }
        if row["verdict"].as_str() == Some("measured_zero")
            && !scope_size_has_positive_component(&target["scopeSize"])
        {
            examples.push(generic_validation_example(
                &row_label,
                "target.scopeSize",
                "measured_zero requires a non-vacuous positive target scopeSize",
            ));
        }
        if row["verdict"].as_str() == Some("measured_nonzero") {
            let Some(class_ref) = target["classRef"]
                .as_str()
                .filter(|value| !value.is_empty())
            else {
                examples.push(generic_validation_example(
                    &row_label,
                    "target.classRef",
                    "measured_nonzero requires target.classRef",
                ));
                continue;
            };
            if !invariant_ids.contains(class_ref)
                && !class_ref
                    .strip_prefix("computedInvariants/")
                    .is_some_and(|id| invariant_ids.contains(id))
            {
                examples.push(generic_validation_example(
                    &row_label,
                    class_ref,
                    "measured_nonzero target.classRef must resolve to computed invariant evidence",
                ));
            }
            let class_id = class_ref
                .strip_prefix("computedInvariants/")
                .unwrap_or(class_ref);
            if let Some(invariant_evaluator) = packet_value["computedInvariants"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|invariant| invariant["invariantId"].as_str() == Some(class_id))
                .and_then(|invariant| invariant["evaluator"].as_str())
            {
                let row_evaluator = row["evaluator"].as_str().unwrap_or_default();
                if invariant_evaluator != row_evaluator {
                    examples.push(generic_validation_example(
                        &row_label,
                        class_ref,
                        &format!(
                            "target.classRef evaluator {invariant_evaluator} must match structural verdict evaluator {row_evaluator}"
                        ),
                        ));
                }
            } else {
                examples.push(generic_validation_example(
                    &row_label,
                    class_ref,
                    "measured_nonzero classRef invariant must carry evaluator provenance",
                ));
            }
        }
    }
    check_examples(
        "measurement-packet-schema052-structural-verdict-new-shape",
        "structural verdict rows carry target and computed invariant evidence",
        examples,
    )
}

fn scope_size_has_positive_component(scope_size: &Value) -> bool {
    scope_size
        .as_object()
        .into_iter()
        .flat_map(|object| object.values())
        .any(|value| value.as_u64().is_some_and(|count| count > 0))
}

fn measurement_ref_segment(value: &str) -> String {
    value
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '-' })
        .collect()
}

fn check_computed_invariant_shape_value(packet_value: &Value) -> ValidationCheck {
    let mut examples = Vec::new();
    let mut invariant_ids = BTreeSet::new();
    for (index, invariant) in packet_value["computedInvariants"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let label = format!("computedInvariants[{index}]");
        if let Some(invariant_id) = invariant["invariantId"].as_str() {
            if !invariant_ids.insert(invariant_id) {
                examples.push(generic_validation_example(
                    &label,
                    invariant_id,
                    "computed invariant invariantId values must be unique",
                ));
            }
        }
        for field in ["invariantId", "kind"] {
            if invariant[field].as_str().is_none_or(str::is_empty) {
                examples.push(generic_validation_example(
                    &label,
                    field,
                    "computed invariant must carry invariantId and closed kind",
                ));
            }
        }
        if invariant["evaluator"].as_str().is_none_or(str::is_empty) {
            examples.push(generic_validation_example(
                &label,
                "evaluator",
                "computed invariant must carry evaluator provenance",
            ));
        }
        if let Some(kind) = invariant["kind"].as_str() {
            if !COMPUTED_INVARIANT_KINDS.contains(&kind) {
                examples.push(generic_validation_example(
                    &label,
                    kind,
                    "computed invariant kind must be one of the closed measurement packet v0.5.4 kinds",
                ));
            }
            if let Some((_, owner)) = COMPUTED_INVARIANT_KIND_OWNERS
                .iter()
                .find(|(owned_kind, _)| *owned_kind == kind)
                && invariant["evaluator"].as_str() != Some(owner)
            {
                examples.push(generic_validation_example(
                    &label,
                    "evaluator",
                    &format!("computed invariant kind {kind} must be owned by {owner}"),
                ));
            }
        }
        if invariant["evaluator"].as_str() == Some("ag.saga-grounded")
            && invariant["kind"].as_str() == Some("saga-grounded-defect-quotient")
            && invariant["status"].as_str() != Some("not_computed")
        {
            validate_saga_grounded_packet_shape(invariant, &label, &mut examples);
        }
        if invariant.get("value").is_none() || invariant.get("representation").is_none() {
            examples.push(generic_validation_example(
                &label,
                "value/representation",
                "computed invariant must carry typed value and representation",
            ));
        }
        // `representation` は invariant 本体のミラーであり、viewer はミラーがあれば
        // そちらを優先する。両方に在る key が食い違うと、本体を再計算する validator を
        // 素通りしたまま表示だけ別の結論になる。共通 key の一致を要求する。
        if let (Some(invariant_object), Some(representation)) = (
            invariant.as_object(),
            invariant["representation"].as_object(),
        ) {
            // 共有欄の食い違いだけを咎める。ミラー側にしか無い欄を違反にすると、summary 形式の
            // representation を持つ authored packet を巻き込む。欄ごと削除する改竄や、本体と
            // ミラーを同じ値に揃える改竄はこの検査では捕まらない。完全性の錨は run manifest の
            // digest 連鎖であり、この検査はその手前で不整合な改竄を落とすためのもの。
            for (key, mirrored) in representation {
                if let Some(actual) = invariant_object.get(key)
                    && actual != mirrored
                {
                    examples.push(generic_validation_example(
                        &format!("{label}.representation.{key}"),
                        "mirror-divergence",
                        "computed invariant representation must agree with the invariant it mirrors",
                    ));
                }
            }
        }
        if invariant["evaluator"].as_str() == Some("ag.square-free-repair")
            && invariant.get("obstructionIdeal").is_some()
        {
            let obstruction_label = format!("{label}.obstructionIdeal");
            check_object_keys(
                &invariant["obstructionIdeal"],
                &obstruction_label,
                &["id", "generators"],
                &mut examples,
            );
            let Some(generators) = invariant["obstructionIdeal"]["generators"].as_array() else {
                examples.push(generic_validation_example(
                    &obstruction_label,
                    "generators",
                    "square-free obstructionIdeal.generators must be an array",
                ));
                continue;
            };
            for (generator_index, generator) in generators.iter().enumerate() {
                let generator_label = format!("{obstruction_label}.generators[{generator_index}]");
                check_object_keys(
                    generator,
                    &generator_label,
                    &["generatorId", "support", "supportAtomRefs"],
                    &mut examples,
                );
                for field in ["generatorId", "support", "supportAtomRefs"] {
                    if field == "generatorId" {
                        if generator[field].as_str().is_none_or(str::is_empty) {
                            examples.push(generic_validation_example(
                                &generator_label,
                                field,
                                "square-free generators must carry a generatorId",
                            ));
                        }
                    } else if generator[field]
                        .as_array()
                        .is_none_or(|items| items.iter().any(|item| item.as_str().is_none()))
                    {
                        examples.push(generic_validation_example(
                            &generator_label,
                            field,
                            "square-free generator support fields must be arrays of strings",
                        ));
                    }
                }
            }
            if let Some(certificate) = invariant.get("nsdepthCertificate") {
                if !certificate.is_null() {
                    let certificate_label = format!("{label}.nsdepthCertificate");
                    check_object_keys(
                        certificate,
                        &certificate_label,
                        &[
                            "status",
                            "certificateRef",
                            "nsdepth",
                            "supportAtomRefs",
                            "verifiedMinimalForbiddenSupports",
                            "effect",
                        ],
                        &mut examples,
                    );
                    if certificate["status"].as_str() != Some("missing")
                        && certificate["supportAtomRefs"]
                            .as_array()
                            .is_none_or(|items| items.iter().any(|item| item.as_str().is_none()))
                    {
                        examples.push(generic_validation_example(
                            &certificate_label,
                            "supportAtomRefs",
                            "square-free NSdepth certificate supportAtomRefs must be an array of strings",
                        ));
                    }
                    if certificate["status"].as_str() == Some("computed")
                        && certificate["certificateRef"]
                            .as_str()
                            .is_none_or(|reference| !reference.starts_with("computedInvariants/"))
                    {
                        examples.push(generic_validation_example(
                            &certificate_label,
                            "certificateRef",
                            "computed square-free NSdepth certificates must reference their computed invariant",
                        ));
                    }
                }
            }
        }
    }
    check_examples(
        "measurement-packet-schema052-computed-invariants-typed",
        "computed invariants expose invariantId, kind, value, and representation",
        examples,
    )
}

fn validate_saga_grounded_packet_shape(
    invariant: &Value,
    label: &str,
    examples: &mut Vec<ValidationExample>,
) {
    for field in [
        "groundedSurfaceRef",
        "displayedRequiredLawsHold",
        "generatedQuotient",
        "detectorFindings",
        "detectorCount",
    ] {
        if invariant.get(field).is_none() {
            examples.push(generic_validation_example(
                label,
                field,
                "saga-grounded defect-quotient invariant requires all typed top-level sections",
            ));
        }
    }
    let detector_count = invariant["detectorCount"].as_u64();
    let findings_len = invariant["detectorFindings"].as_array().map(Vec::len);
    if detector_count.map(|count| count as usize) != findings_len {
        examples.push(generic_validation_example(
            &format!("{label}.detectorCount"),
            &detector_count.unwrap_or_default().to_string(),
            "saga-grounded detectorCount must equal detectorFindings length",
        ));
    }
}

fn check_analytic_regime_boundary(
    packet: &ArchSigMeasurementPacketV1,
    packet_value: &Value,
) -> ValidationCheck {
    let structural_evaluators = packet
        .structural_verdict
        .iter()
        .map(|row| row.evaluator.as_str())
        .collect::<BTreeSet<_>>();
    let structural_refs = packet_value["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|row| row["verdictRef"].as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    for (index, reading_value) in packet_value["analyticReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let label = format!("analyticReadings[{index}]");
        let claim_status = reading_value["claimStatus"].as_str().unwrap_or_default();
        if !matches!(claim_status, "certified" | "candidate") {
            examples.push(generic_validation_example(
                &label,
                claim_status,
                "analytic reading claimStatus must be certified or candidate",
            ));
        }
        let fidelity = reading_value["fidelity"].as_str().unwrap_or_default();
        if !matches!(fidelity, "faithful" | "proxy") {
            examples.push(generic_validation_example(
                &label,
                fidelity,
                "analytic reading fidelity must be faithful or proxy",
            ));
        }
        if let Some(reading) = packet.analytic_readings.get(index) {
            let expected_claim_status = analytic_claim_status(reading);
            if claim_status != expected_claim_status {
                examples.push(generic_validation_example(
                    &label,
                    claim_status,
                    &format!(
                        "authored analytic reading claimStatus must match derived value {expected_claim_status}"
                    ),
                ));
            }
            let expected_fidelity = analytic_fidelity(reading);
            if fidelity != expected_fidelity {
                examples.push(generic_validation_example(
                    &label,
                    fidelity,
                    &format!(
                        "authored analytic reading fidelity must match derived value {expected_fidelity}"
                    ),
                ));
            }
        }
        if claim_status == "candidate" && !reading_value["structuralVerdictRef"].is_null() {
            examples.push(generic_validation_example(
                &label,
                "structuralVerdictRef",
                "candidate readings must remain analytic-only",
            ));
        }
        if claim_status != "candidate"
            && let Some(structural_ref) = reading_value["structuralVerdictRef"].as_str()
            && !structural_refs.contains(structural_ref)
        {
            examples.push(generic_validation_example(
                &label,
                structural_ref,
                "certified analytic reading structuralVerdictRef must resolve to a structural verdict",
            ));
        }
        if reading_value["evaluator"] == "ag.harmonic-debt"
            && reading_value["value"]["lowerBoundStatus"] == "cost_model_not_supplied"
        {
            let next_input = reading_value["value"]["whatNext"].as_str();
            if next_input.is_none_or(|text| text.trim().is_empty()) {
                examples.push(generic_validation_example(
                    &label,
                    "value.whatNext",
                    "harmonic cost-model silence must expose the next required input",
                ));
            }
            let matching_invariant = packet_value["computedInvariants"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|invariant| invariant["evaluator"] == "ag.harmonic-debt");
            if matching_invariant.is_none_or(|invariant| {
                invariant["status"] != "silence_by_design"
                    || invariant["whatNext"].as_str() != next_input
            }) {
                examples.push(generic_validation_example(
                    &label,
                    "value.whatNext",
                    "harmonic cost-model silence must match the computed invariant whatNext guidance",
                ));
            }
        }
    }
    for reading in &packet.analytic_readings {
        if reading
            .regime
            .as_deref()
            .is_some_and(|regime| regime.contains("candidate"))
            && reading.structural_verdict_ref.is_some()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "structuralVerdictRef",
                "theorem-candidate readings must remain analytic-only",
            ));
        }
        if reading
            .regime
            .as_deref()
            .is_some_and(|regime| regime.contains("candidate"))
            && structural_evaluators.contains(reading.evaluator.as_str())
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.evaluator,
                "theorem-candidate reading must not reuse a structural verdict evaluator id",
            ));
        }
    }
    check_examples(
        "measurement-packet-schema052-theorem-candidate-analytic-only",
        "theorem-candidate readings are flagged analytic readings and do not generate structural verdicts",
        examples,
    )
}

fn check_supplied_data_shape(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let packet_value = serde_json::to_value(packet).unwrap_or_else(|_| json!({}));
    let mut examples = Vec::new();
    if !packet_value["suppliedData"].is_array() {
        examples.push(generic_validation_example(
            "suppliedData",
            "missing",
            "measurement packet must expose suppliedData ledger",
        ));
    } else if packet_value["suppliedData"]
        .as_array()
        .is_some_and(Vec::is_empty)
    {
        examples.push(generic_validation_example(
            "suppliedData",
            "empty",
            "measurement packet must record supplied input artifacts",
        ));
    }
    let mut supplied_kinds = BTreeSet::new();
    let mut supplied_ids = BTreeSet::new();
    for (index, supplied) in packet_value["suppliedData"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let label = format!("suppliedData[{index}]");
        if let Some(supplied_id) = supplied["suppliedId"].as_str() {
            if !supplied_ids.insert(supplied_id) {
                examples.push(generic_validation_example(
                    &label,
                    supplied_id,
                    "suppliedData suppliedId values must be unique",
                ));
            }
        }
        for field in ["suppliedId", "kind", "sourceArtifactRef"] {
            if supplied[field].as_str().is_none_or(str::is_empty) {
                examples.push(generic_validation_example(
                    &label,
                    field,
                    "suppliedData entries must carry suppliedId / kind / sourceArtifactRef",
                ));
            }
        }
        if let Some(kind) = supplied["kind"].as_str() {
            if !supplied_kinds.insert(kind) {
                examples.push(generic_validation_example(
                    &label,
                    kind,
                    "suppliedData kind values must be unique",
                ));
            }
            if !matches!(
                kind,
                "archmap" | "law-policy" | "law-equation-surface" | "measurement-profile"
            ) {
                examples.push(generic_validation_example(
                    &label,
                    kind,
                    "suppliedData kind must be one of the input artifact ledger kinds",
                ));
            }
        }
        if !supplied["conformance"].is_object() {
            examples.push(generic_validation_example(
                &label,
                "conformance",
                "suppliedData entries must carry conformance object",
            ));
        } else if supplied["conformance"]["status"]
            .as_str()
            .is_none_or(|status| !matches!(status, "validated" | "assumed" | "derived"))
        {
            examples.push(generic_validation_example(
                &label,
                "conformance.status",
                "suppliedData conformance status must be validated, assumed, or derived",
            ));
        } else if supplied["conformance"]["checkRef"]
            .as_str()
            .is_none_or(str::is_empty)
        {
            examples.push(generic_validation_example(
                &label,
                "conformance.checkRef",
                "suppliedData conformance must carry a non-empty checkRef",
            ));
        }
    }
    for required_kind in ["archmap", "law-policy", "measurement-profile"] {
        if !supplied_kinds.contains(required_kind) {
            examples.push(generic_validation_example(
                "suppliedData",
                required_kind,
                "measurement packet suppliedData must ledger archmap, law-policy, and measurement-profile inputs",
            ));
        }
    }
    check_examples(
        "measurement-packet-schema052-supplied-data-ledger",
        "suppliedData ledger is present and typed when entries exist",
        examples,
    )
}

fn check_assumption_ledger(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let assumption_refs = packet
        .assumptions
        .iter()
        .map(assumption_id_for_schema)
        .collect::<BTreeSet<_>>();
    let violated = packet
        .assumptions
        .iter()
        .filter(|entry| entry.status == "violated")
        .map(assumption_id_for_schema)
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    let mut authored_assumption_ids = BTreeSet::new();
    for entry in &packet.assumptions {
        let derived_id = assumption_id_for_schema(entry);
        if !authored_assumption_ids.insert(derived_id.clone()) {
            examples.push(generic_validation_example(
                &entry.theorem_ref,
                &derived_id,
                "assumptionId values must be unique",
            ));
        }
        if !matches!(entry.status.as_str(), "checked" | "assumed" | "violated") {
            examples.push(generic_validation_example(
                &entry.theorem_ref,
                &entry.status,
                "assumption status must be checked, assumed, or violated",
            ));
        }
        if entry.status == "checked" && entry.checked_by.is_none() {
            examples.push(generic_validation_example(
                &entry.theorem_ref,
                &entry.assumption,
                "checked assumptions must record checkedBy",
            ));
        }
        if entry.status == "assumed" && entry.assumed_by.is_none() {
            examples.push(generic_validation_example(
                &entry.theorem_ref,
                &entry.assumption,
                "assumed assumptions must record assumedBy",
            ));
        }
    }
    for row in &packet.structural_verdict {
        for theorem_ref in &row.depends_on_assumptions {
            if !assumption_refs.contains(theorem_ref) {
                examples.push(generic_validation_example(
                    &row.evaluator,
                    theorem_ref,
                    "dependsOnAssumptions entries must resolve to assumptionId values",
                ));
            }
        }
        if is_measured_verdict(&row.verdict)
            && row
                .depends_on_assumptions
                .iter()
                .any(|theorem_ref| violated.contains(theorem_ref))
        {
            examples.push(generic_validation_example(
                &row.evaluator,
                &row.verdict,
                "measured structural verdicts must not depend on violated assumptions",
            ));
        }
    }
    check_examples(
        "measurement-packet-schema052-assumption-ledger",
        "assumption ledger records checked / assumed / violated and row-level verdict dependencies",
        examples,
    )
}

fn check_assumption_ledger_value(
    packet: &ArchSigMeasurementPacketV1,
    packet_value: &Value,
) -> ValidationCheck {
    let mut check = check_assumption_ledger(packet);
    let mut raw_examples = Vec::new();
    for (index, assumption) in packet_value["assumptions"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
    {
        let label = format!("assumptions[{index}]");
        let expected_id = packet
            .assumptions
            .get(index)
            .map(assumption_id_for_schema)
            .unwrap_or_default();
        let authored_id = assumption["assumptionId"].as_str();
        if authored_id.is_none_or(str::is_empty) {
            raw_examples.push(generic_validation_example(
                &label,
                "assumptionId",
                "assumption entries must carry authored assumptionId; theoremRef is not a fallback",
            ));
        } else if authored_id != Some(expected_id.as_str()) {
            raw_examples.push(generic_validation_example(
                &label,
                authored_id.unwrap_or_default(),
                &format!("authored assumptionId must match derived value {expected_id}"),
            ));
        }
    }
    if !raw_examples.is_empty() {
        check.result = "fail".to_string();
        check.examples.extend(raw_examples);
        check.count = Some(check.examples.len());
    }
    check
}

fn check_boundary_statements(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let mut examples = Vec::new();
    let mut ids = BTreeSet::new();
    let valid_scope_refs = measurement_packet_scope_refs(packet);
    let boundary_texts = packet
        .boundary_statements
        .iter()
        .map(|statement| statement.text.as_str())
        .collect::<BTreeSet<_>>();

    if packet.boundary_statements.is_empty() {
        examples.push(generic_validation_example(
            "boundaryStatements",
            "empty",
            "measurement packet must expose typed boundary statements",
        ));
    }

    for statement in &packet.boundary_statements {
        if statement.id.trim().is_empty() {
            examples.push(generic_validation_example(
                "boundaryStatements[].id",
                "empty",
                "boundary statement id must be non-empty",
            ));
        } else if !ids.insert(statement.id.as_str()) {
            examples.push(generic_validation_example(
                "boundaryStatements[].id",
                &statement.id,
                "boundary statement id must be unique",
            ));
        }
        if !BOUNDARY_STATEMENT_KINDS.contains(&statement.kind.as_str()) {
            examples.push(generic_validation_example(
                &statement.id,
                &statement.kind,
                "boundary statement kind must be one of the v0.5.4 boundary kinds",
            ));
        }
        if statement.reason.trim().is_empty() {
            examples.push(generic_validation_example(
                &statement.id,
                "reason",
                "boundary statement reason must be non-empty",
            ));
        }
        if statement.text.trim().is_empty() {
            examples.push(generic_validation_example(
                &statement.id,
                "text",
                "boundary statement text must be non-empty",
            ));
        }
        if statement.scope_refs.is_empty() {
            examples.push(generic_validation_example(
                &statement.id,
                "scopeRefs",
                "boundary statement scopeRefs must be non-empty",
            ));
        }
        for scope_ref in &statement.scope_refs {
            if !valid_scope_refs.contains(scope_ref) {
                examples.push(generic_validation_example(
                    &statement.id,
                    scope_ref,
                    "boundary statement scopeRefs must resolve inside the measurement packet",
                ));
            }
        }
        if statement.kind == "violated_assumption"
            && !statement
                .scope_refs
                .iter()
                .any(|scope_ref| blocked_measurement_scope_refs(packet).contains(scope_ref))
        {
            examples.push(generic_validation_example(
                &statement.id,
                "scopeRefs",
                "violated_assumption boundary must scope to a not_computed or unmeasured packet surface",
            ));
        }
        if statement.kind == "silence_by_design"
            && statement.scope_refs.iter().any(|scope_ref| {
                packet.structural_verdict.iter().any(|row| {
                    structural_verdict_ref(row) == *scope_ref && row.verdict == "measured_nonzero"
                })
            })
        {
            examples.push(generic_validation_example(
                &statement.id,
                "scopeRefs",
                "silence_by_design boundary must not scope to a measured_nonzero structural verdict",
            ));
        }
    }

    for invariant in &packet.computed_invariants {
        let invariant_id = invariant["invariantId"].as_str().unwrap_or_default();
        let status = invariant["status"].as_str();
        if invariant.get("whatNext").is_some() && status != Some("silence_by_design") {
            examples.push(generic_validation_example(
                invariant_id,
                "whatNext",
                "whatNext is reserved for silence_by_design invariants",
            ));
        }
        if status.is_some() && status != Some("silence_by_design") {
            if packet.boundary_statements.iter().any(|statement| {
                statement.kind == "silence_by_design"
                    && statement
                        .scope_refs
                        .iter()
                        .any(|scope_ref| scope_ref == invariant_id)
            }) {
                examples.push(generic_validation_example(
                    invariant_id,
                    "boundaryStatements",
                    "typed silence boundaries must not scope to a non-silence invariant",
                ));
            }
        }
        if invariant.get("whatNext").is_some() {
            let Some(what_next) = invariant["whatNext"].as_str() else {
                examples.push(generic_validation_example(
                    invariant["invariantId"]
                        .as_str()
                        .unwrap_or("computed-invariant"),
                    "whatNext",
                    "whatNext must be a non-empty string when supplied",
                ));
                continue;
            };
            if what_next.trim().is_empty() {
                examples.push(generic_validation_example(
                    invariant["invariantId"]
                        .as_str()
                        .unwrap_or("computed-invariant"),
                    "whatNext",
                    "whatNext must be a non-empty string when supplied",
                ));
            }
        }
        if invariant["status"].as_str() == Some("silence_by_design") {
            if invariant["whatNext"]
                .as_str()
                .is_none_or(|text| text.trim().is_empty())
            {
                examples.push(generic_validation_example(
                    invariant_id,
                    "whatNext",
                    "silence_by_design invariants must explain the next required input",
                ));
            }
            if !packet.boundary_statements.iter().any(|statement| {
                statement.kind == "silence_by_design"
                    && statement
                        .scope_refs
                        .iter()
                        .any(|scope_ref| scope_ref == invariant_id)
            }) {
                examples.push(generic_validation_example(
                    invariant_id,
                    "boundaryStatements",
                    "silence_by_design invariants must have a typed boundary scoped to the invariant",
                ));
            } else if let Some(statement) = packet.boundary_statements.iter().find(|statement| {
                statement.kind == "silence_by_design"
                    && statement
                        .scope_refs
                        .iter()
                        .any(|scope_ref| scope_ref == invariant_id)
            }) {
                let what_next = invariant["whatNext"].as_str().unwrap_or_default();
                if !statement.text.contains(what_next) {
                    examples.push(generic_validation_example(
                        invariant_id,
                        "boundaryStatements.text",
                        "typed silence boundary text must include the invariant whatNext guidance",
                    ));
                }
            }
        }
    }

    for text in &packet.non_conclusions {
        if !boundary_texts.contains(text.as_str()) {
            examples.push(generic_validation_example(
                "nonConclusions",
                text,
                "compat nonConclusions text must be reproduced by boundaryStatements[].text",
            ));
        }
    }

    check_examples(
        "measurement-packet-schema052-boundary-statements",
        "boundaryStatements provide typed, scoped non-conclusion qualifiers with nonConclusions compatibility",
        examples,
    )
}

fn measurement_packet_scope_refs(packet: &ArchSigMeasurementPacketV1) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    refs.insert(packet.packet_id.clone());
    refs.extend(
        packet
            .analytic_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    refs.extend(packet.assumptions.iter().map(assumption_id_for_schema));
    refs.extend(
        packet
            .supplied_data
            .iter()
            .map(|entry| entry.supplied_id.clone()),
    );
    for row in &packet.structural_verdict {
        refs.insert(row.evaluator.clone());
        refs.insert(row.law.clone());
        refs.insert(structural_verdict_ref(row));
    }
    for invariant in &packet.computed_invariants {
        for field in ["id", "invariantId", "readingId", "computedInvariantId"] {
            if let Some(value) = invariant.get(field).and_then(Value::as_str) {
                refs.insert(value.to_string());
            }
        }
    }
    refs
}

fn not_computed_scope_refs(packet: &ArchSigMeasurementPacketV1) -> BTreeSet<String> {
    let mut refs = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "not_computed")
        .map(structural_verdict_ref)
        .collect::<BTreeSet<_>>();
    refs.extend(packet.analytic_readings.iter().filter_map(|reading| {
        (reading.value.get("status").and_then(Value::as_str) == Some("not_computed"))
            .then(|| reading.reading_id.clone())
    }));
    for invariant in &packet.computed_invariants {
        if invariant.get("status").and_then(Value::as_str) == Some("not_computed") {
            for field in ["id", "invariantId", "readingId", "computedInvariantId"] {
                if let Some(value) = invariant.get(field).and_then(Value::as_str) {
                    refs.insert(value.to_string());
                    break;
                }
            }
        }
    }
    refs
}

fn blocked_measurement_scope_refs(packet: &ArchSigMeasurementPacketV1) -> BTreeSet<String> {
    let mut refs = not_computed_scope_refs(packet);
    refs.extend(
        packet
            .structural_verdict
            .iter()
            .filter(|row| row.verdict == "unmeasured")
            .map(structural_verdict_ref),
    );
    for invariant in &packet.computed_invariants {
        if invariant.get("status").and_then(Value::as_str) == Some("unmeasured") {
            for field in ["id", "invariantId", "readingId", "computedInvariantId"] {
                if let Some(value) = invariant.get(field).and_then(Value::as_str) {
                    refs.insert(value.to_string());
                    break;
                }
            }
        }
    }
    refs
}

fn dependent_blocked_measurement_scope_refs(
    packet: &ArchSigMeasurementPacketV1,
    theorem_ref: &str,
) -> Vec<String> {
    packet
        .structural_verdict
        .iter()
        .filter(|row| {
            matches!(row.verdict.as_str(), "not_computed" | "unmeasured")
                && row
                    .depends_on_assumptions
                    .iter()
                    .any(|dependency| dependency == theorem_ref)
        })
        .map(structural_verdict_ref)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn check_examples(id: &str, title: &str, examples: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    if !examples.is_empty() {
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}

#[cfg(test)]
mod tests {
    use super::*;

    fn packet_fixture() -> ArchSigMeasurementPacketV1 {
        let mut packet: ArchSigMeasurementPacketV1 = serde_json::from_value(json!({
            "schema": "archsig-measurement-packet/v0.5.4",
            "packetId": "measurement:test",
            "profile": {
                "schema": "measurement-profile/v0.5.4",
                "profileId": "profile:test",
                "siteRef": "archmap:/contexts",
                "coverRef": "cover:test",
                "coefficient": "F2",
                "effCoeff": "finite-linear-algebra@1",
                "resolutionSelector": "taylor@1",
                "domain": "finite-poset-site",
                "zeroPredicate": "rank-zero@1",
                "nonZeroPredicate": "rank-positive@1",
                "certSelector": "finite-certificate@1",
                "verdictDiscipline": "five-valued-structural-verdict@1",
                "finiteBounds": {
                    "maxSquareFreeWitnessVariables": 12,
                    "maxCoherenceContexts": 12,
                    "maxTorWitnessVariables": 12,
                    "maxBoundaryResidueVariables": 16,
                    "maxLaplacianCells": 16,
                    "maxPeriodCycles": 16,
                    "maxTransferTargets": 16
                }
            },
            "structuralVerdict": [{
                "evaluator": "ag.cech-obstruction",
                "law": "ag.cech-obstruction",
                "verdict": "unmeasured",
                "verdictData": {
                    "inScope": true,
                    "zero": false,
                    "nonZero": false,
                    "methodStatus": "schema_foundation_only"
                }
            }],
            "computedInvariants": [],
            "analyticReadings": [{
                "readingId": "candidate:test",
                "evaluator": "ag.foundation",
                "value": {"state": "not_evaluated"},
                "regime": "theorem-candidate",
                "structuralVerdictRef": null
            }],
            "assumptions": [{
                "theoremRef": "part8/4.2",
                "assumption": "finite site",
                "status": "checked",
                "checkedBy": "test"
            }],
            "suppliedData": [{
                "suppliedId": "supplied:archmap",
                "kind": "archmap",
                "sourceArtifactRef": "input:archmap.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "archmap/v0.5.4-validation"
                }
            }, {
                "suppliedId": "supplied:law-policy",
                "kind": "law-policy",
                "sourceArtifactRef": "input:law-policy.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "law-policy/v0.5.4-validation"
                }
            }, {
                "suppliedId": "supplied:measurement-profile",
                "kind": "measurement-profile",
                "sourceArtifactRef": "input:measurement-profile.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "measurement-profile/v0.5.4-validation"
                }
            }],
            "nonConclusions": ["test fixture"]
        }))
        .expect("packet fixture parses");
        packet.boundary_statements = boundary_statements_for_measurement_packet(&packet);
        packet
    }

    fn normalized_fixture() -> NormalizedArchMapV2 {
        serde_json::from_value(json!({
            "schema": "archmap-normalized/v0.5.4",
            "normalizerId": "test-normalizer",
            "sourceArchmapRef": "archmap:test",
            "sourceArchmapId": "archmap:test",
            "extractionDoctrineRef": {
                "doctrineId": "doctrine:aat-canonical@1",
                "fingerprint": "sha256:aat-canonical-doctrine-schema052",
                "components": ["V", "Gamma", "R", "rho", "E", "N"]
            },
            "atoms": [
                {
                    "sourceAtomId": "x_checkout",
                    "normalizedAtomId": "atom:checkout",
                    "atomKind": "component",
                    "subject": "x_checkout",
                    "axis": "semantic",
                    "predicate": "forbidden_obstruction_marker",
                    "object": null,
                    "sourceRefs": ["fixture://checkout"],
                    "contextMemberships": ["ctx:a", "ctx:b", "ctx:c"],
                    "normalizationStatus": "normalized"
                },
                {
                    "sourceAtomId": "x_inventory",
                    "normalizedAtomId": "atom:inventory",
                    "atomKind": "component",
                    "subject": "x_inventory",
                    "axis": "semantic",
                    "predicate": "service",
                    "object": null,
                    "sourceRefs": ["fixture://inventory"],
                    "contextMemberships": ["ctx:a", "ctx:b", "ctx:c"],
                    "normalizationStatus": "normalized"
                },
                {
                    "sourceAtomId": "x_payment",
                    "normalizedAtomId": "atom:payment",
                    "atomKind": "component",
                    "subject": "x_payment",
                    "axis": "semantic",
                    "predicate": "service",
                    "object": null,
                    "sourceRefs": ["fixture://payment"],
                    "contextMemberships": ["ctx:b", "ctx:c"],
                    "normalizationStatus": "normalized"
                }
            ],
            "contexts": [
                {
                    "sourceContextId": "ctx:a",
                    "normalizedContextId": "ctx:a",
                    "atomIds": ["atom:checkout", "atom:inventory"],
                    "restrictsTo": ["ctx:b"],
                    "sourceRefs": ["fixture://a"],
                    "posetStatus": "selected"
                },
                {
                    "sourceContextId": "ctx:b",
                    "normalizedContextId": "ctx:b",
                    "atomIds": ["atom:checkout", "atom:inventory", "atom:payment"],
                    "restrictsTo": ["ctx:c"],
                    "sourceRefs": ["fixture://b"],
                    "posetStatus": "selected"
                },
                {
                    "sourceContextId": "ctx:c",
                    "normalizedContextId": "ctx:c",
                    "atomIds": ["atom:checkout", "atom:inventory", "atom:payment"],
                    "restrictsTo": [],
                    "sourceRefs": ["fixture://c"],
                    "posetStatus": "selected"
                }
            ],
            "covers": [{
                "sourceCoverId": "cover:test",
                "normalizedCoverId": "cover:test",
                "contextIds": ["ctx:a", "ctx:b", "ctx:c"],
                "sourceRefs": ["fixture://cover"],
                "coverageStatus": "selected"
            }],
            "summary": {
                "atomCount": 3,
                "normalizedAtomCount": 3,
                "contextCount": 3,
                "coverCount": 1,
                "doctrineFingerprint": "sha256:aat-canonical-doctrine-schema052"
            },
            "nonConclusions": []
        }))
        .expect("normalized fixture parses")
    }

    #[test]
    fn invalid_structural_verdict_value_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict = "blocked".to_string();
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-five-verdict-values" && check.result == "fail"
        }));
    }

    #[test]
    fn unregistered_structural_verdict_evaluator_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].evaluator = "ag.synthetic-new-verdict".to_string();
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-evaluators"
                && check.result == "fail"
        }));
    }

    #[test]
    fn unknown_computed_invariant_kind_fails_validation() {
        let mut packet = packet_fixture();
        packet.computed_invariants.push(json!({
            "invariantId": "invariant:unknown-kind",
            "kind": "unregistered-freeform-kind",
            "value": 1,
            "representation": {"basis": "test"}
        }));
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-computed-invariants-typed"
                && check.result == "fail"
        }));
    }

    #[test]
    fn empty_supplied_data_ledger_fails_validation() {
        let mut packet = packet_fixture();
        packet.supplied_data.clear();
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-supplied-data-ledger"
                && check.result == "fail"
        }));
    }

    #[test]
    fn zero_and_nonzero_verdict_data_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].verdict_data.non_zero = true;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-verdict-data-boundary"
                && check.result == "fail"
        }));
    }

    #[test]
    fn measured_zero_requires_unhedged_verdict_data() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict = "measured_zero".to_string();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].verdict_data.in_scope = false;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-verdict-data-boundary"
                && check.result == "fail"
        }));

        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict = "measured_zero".to_string();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].verdict_data.non_zero = true;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-verdict-data-boundary"
                && check.result == "fail"
        }));
    }

    #[test]
    fn measured_verdict_depending_on_violated_assumption_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict = "measured_zero".to_string();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].depends_on_assumptions =
            vec![assumption_id_for_schema(&packet.assumptions[0])];
        packet.assumptions[0].status = "violated".to_string();
        packet.assumptions[0].checked_by = None;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-assumption-ledger" && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_measured_zero_with_empty_scope_fails_raw_validation() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["structuralVerdict"][0]["verdict"] = json!("measured_zero");
        raw["structuralVerdict"][0]["verdictData"]["inScope"] = json!(true);
        raw["structuralVerdict"][0]["verdictData"]["zero"] = json!(true);
        raw["structuralVerdict"][0]["target"]["scopeSize"] =
            json!({"contexts": 0, "edges": 0, "triangles": 0});
        raw["structuralVerdict"][0]["evidence"]["computedInvariantRefs"] = json!([]);

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-new-shape"
                && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_structural_evidence_shape_rejects_missing_and_non_string_refs() {
        let packet = packet_fixture();
        let mut missing_evidence = serde_json::to_value(&packet).expect("packet serializes");
        missing_evidence["structuralVerdict"][0]
            .as_object_mut()
            .unwrap()
            .remove("evidence");
        let checks = validate_measurement_packet_value_v1(&missing_evidence);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-new-shape"
                && check.result == "fail"
        }));

        let mut non_string_ref = serde_json::to_value(&packet).expect("packet serializes");
        non_string_ref["structuralVerdict"][0]["evidence"]["computedInvariantRefs"] = json!([123]);
        let checks = validate_measurement_packet_value_v1(&non_string_ref);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-new-shape"
                && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_packet_rejects_unknown_duplicate_and_dangling_fields() {
        let mut raw = serde_json::to_value(packet_fixture()).expect("packet serializes");
        raw["unexpected"] = json!(true);
        raw["computedInvariants"] = json!([
            {
                "invariantId": "duplicate:invariant",
                "kind": "measurement-invariant",
                "evaluator": "ag.foundation",
                "value": 0,
                "representation": {}
            },
            {
                "invariantId": "duplicate:invariant",
                "kind": "measurement-invariant",
                "evaluator": "ag.foundation",
                "value": 0,
                "representation": {}
            }
        ]);
        raw["computedInvariants"][0]["forgedField"] = json!(true);
        raw["analyticReadings"][0]["regime"] = json!("candidate-preview");
        raw["analyticReadings"][0]["claimStatus"] = json!("candidate");
        raw["analyticReadings"][0]["structuralVerdictRef"] = json!("structuralVerdict/missing");
        raw["suppliedData"][1]["suppliedId"] = json!("supplied:archmap");
        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields" && check.result == "fail"
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.examples.iter().any(|example| {
                    example.source.as_deref() == Some("computedInvariants[0].forgedField")
                })
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-computed-invariants-typed"
                && check.result == "fail"
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-supplied-data-ledger"
                && check.result == "fail"
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));
        raw["analyticReadings"][0]["regime"] = json!("certified");
        raw["analyticReadings"][0]["claimStatus"] = json!("certified");
        raw["analyticReadings"][0]["structuralVerdictRef"] = json!("structuralVerdict/missing");
        let certified_checks = validate_measurement_packet_value_v1(&raw);
        assert!(certified_checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));

        let mut retired_vocabulary =
            serde_json::to_value(packet_fixture()).expect("packet serializes");
        retired_vocabulary["computedInvariants"] = json!([{
            "invariantId": "saga-comparison:h1-transfer",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.saga-comparison",
            "status": "not_computed",
            "value": {"status": "not_computed"},
            "representation": {"basis": "test"},
            "contract": {"contractChecked": false}
        }]);
        let retired_checks = validate_measurement_packet_value_v1(&retired_vocabulary);
        assert!(retired_checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-unknown-fields"
                && check.examples.iter().any(|example| {
                    example
                        .source
                        .as_deref()
                        .is_some_and(|source| source.contains("contract"))
                })
        }));
        assert!(retired_checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-computed-invariants-typed"
                && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_candidate_reading_with_structural_ref_fails_raw_validation() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["analyticReadings"][0]["claimStatus"] = json!("candidate");
        raw["analyticReadings"][0]["structuralVerdictRef"] = json!("/structuralVerdict/0");

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_measured_nonzero_class_ref_must_resolve_without_rewrite() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["structuralVerdict"][0]["verdict"] = json!("measured_nonzero");
        raw["structuralVerdict"][0]["verdictData"]["inScope"] = json!(true);
        raw["structuralVerdict"][0]["verdictData"]["zero"] = json!(false);
        raw["structuralVerdict"][0]["verdictData"]["nonZero"] = json!(true);
        raw["structuralVerdict"][0]["target"]["scopeSize"] =
            json!({"contexts": 1, "edges": 1, "triangles": 0});
        raw["structuralVerdict"][0]["target"]["classRef"] = json!("computedInvariants/missing");
        raw["structuralVerdict"][0]["evidence"]["computedInvariantRefs"] =
            json!(["invariant:actual"]);
        raw["computedInvariants"] = json!([{
            "invariantId": "invariant:actual",
            "kind": "measurement-invariant",
            "evaluator": "ag.cech-obstruction",
            "value": 1,
            "representation": {"source": "test"}
        }]);

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-structural-verdict-new-shape"
                && check.result == "fail"
                && check
                    .examples
                    .iter()
                    .any(|example| example.target.as_deref() == Some("computedInvariants/missing"))
        }));
    }

    #[test]
    fn supplied_computed_invariant_empty_object_fails_raw_validation() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["computedInvariants"] = json!([{}]);

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-computed-invariants-typed"
                && check.result == "fail"
        }));
    }

    #[test]
    fn supplied_assumption_without_authored_id_fails_raw_validation() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["assumptions"][0]
            .as_object_mut()
            .unwrap()
            .remove("assumptionId");

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-assumption-ledger"
                && check.result == "fail"
                && check
                    .examples
                    .iter()
                    .any(|example| example.target.as_deref() == Some("assumptionId"))
        }));
    }

    #[test]
    fn supplied_laplacian_reading_must_be_marked_proxy() {
        let packet = packet_fixture();
        let mut raw = serde_json::to_value(&packet).expect("packet serializes");
        raw["analyticReadings"][0]["evaluator"] = json!("ag.sheaf-laplacian");
        raw["analyticReadings"][0]["value"] = json!({
            "readingKind": "graph-laplacian-hodge-proxy@1"
        });
        raw["analyticReadings"][0]["regime"] = json!("analytic-measurement");
        raw["analyticReadings"][0]["claimStatus"] = json!("certified");
        raw["analyticReadings"][0]["fidelity"] = json!("faithful");

        let checks = validate_measurement_packet_value_v1(&raw);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
                && check
                    .examples
                    .iter()
                    .any(|example| example.target.as_deref() == Some("faithful"))
        }));
    }

    #[test]
    fn unresolved_assumption_dependency_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].depends_on_assumptions = vec!["missing/theorem".to_string()];
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-assumption-ledger" && check.result == "fail"
        }));
    }

    #[test]
    fn structural_verdict_dependency_field_is_serde_backward_compatible() {
        let packet = packet_fixture();
        assert!(
            packet.structural_verdict[0]
                .depends_on_assumptions
                .is_empty()
        );

        let serialized = serde_json::to_value(&packet).expect("packet serializes");
        assert!(
            serialized["structuralVerdict"][0]
                .get("dependsOnAssumptions")
                .is_none(),
            "empty dependsOnAssumptions stays additive and omitted from legacy-shaped rows"
        );
    }

    #[test]
    fn assumption_dependency_propagation_only_updates_dependent_measured_rows() {
        let mut packet = packet_fixture();
        let finite_site_assumption = assumption_id_for_schema(&packet.assumptions[0]);
        packet.structural_verdict[0].verdict = "measured_zero".to_string();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].depends_on_assumptions = vec![finite_site_assumption.clone()];
        let square_free_assumption = AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/5.1".to_string(),
            assumption: "square-free witness variables selected by supplied law-equation-surface"
                .to_string(),
            status: "checked".to_string(),
            checked_by: Some("test".to_string()),
            assumed_by: None,
        };
        let square_free_assumption_id = assumption_id_for_schema(&square_free_assumption);
        packet.structural_verdict.push(AgStructuralVerdictV1 {
            evaluator: "ag.square-free-repair".to_string(),
            law: "ag.square-free-repair".to_string(),
            verdict: "measured_zero".to_string(),
            verdict_data: AgVerdictDataV1 {
                in_scope: true,
                zero: true,
                non_zero: false,
                method_status: "square_free_ideal_computed".to_string(),
                cert_ref: None,
            },
            depends_on_assumptions: vec![square_free_assumption_id],
            reason: Some("independent square-free row remains measured zero".to_string()),
        });
        packet.assumptions[0].status = "violated".to_string();
        packet.assumptions[0].checked_by = None;
        packet.assumptions.push(square_free_assumption);

        apply_assumption_dependency_propagation(&mut packet);

        assert_eq!(packet.structural_verdict[0].verdict, "not_computed");
        assert_eq!(
            packet.structural_verdict[0].verdict_data.method_status,
            "depends_on_violated_assumption"
        );
        let expected_reason = format!("depends_on violated {finite_site_assumption}");
        assert_eq!(
            packet.structural_verdict[0].reason.as_deref(),
            Some(expected_reason.as_str())
        );
        assert_eq!(packet.structural_verdict[1].verdict, "measured_zero");
        assert!(packet.structural_verdict[1].verdict_data.zero);
    }

    #[test]
    fn theorem_candidate_reading_cannot_link_structural_verdict() {
        let mut packet = packet_fixture();
        packet.analytic_readings[0].structural_verdict_ref =
            Some("/structuralVerdict/0".to_string());
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));
    }

    #[test]
    fn boundary_statements_reproduce_non_conclusion_compat_text() {
        let packet = packet_fixture();
        let checks = validate_measurement_packet_v1(&packet);

        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "pass"
        }));
        assert!(packet.non_conclusions.iter().all(|text| {
            packet
                .boundary_statements
                .iter()
                .any(|statement| statement.text == *text)
        }));
        assert!(packet.boundary_statements.iter().any(|statement| {
            statement.kind == "unmeasured_support"
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| scope_ref.starts_with("structuralVerdict/"))
        }));
        assert!(packet.boundary_statements.iter().any(|statement| {
            statement.kind == "not_applicable"
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| scope_ref == "candidate:test")
        }));
    }

    #[test]
    fn boundary_statement_empty_scope_refs_fail_validation() {
        let mut packet = packet_fixture();
        packet.boundary_statements[0].scope_refs.clear();
        let checks = validate_measurement_packet_v1(&packet);

        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn boundary_statement_unresolved_scope_refs_fail_validation() {
        let mut packet = packet_fixture();
        packet.boundary_statements[0].scope_refs = vec!["missing:scope".to_string()];
        let checks = validate_measurement_packet_v1(&packet);

        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn comparison_silence_requires_next_input_and_typed_boundary() {
        let mut packet = packet_fixture();
        packet.computed_invariants.push(json!({
            "invariantId": "saga-comparison:h1-transfer",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.saga-comparison",
            "status": "silence_by_design",
            "whatNext": "supply the missing comparison input",
            "value": {"status": "silence_by_design"},
            "representation": {"basis": "typed-silence"},
            "contract": {
                "incidenceBridgeKind": "unknown",
                "h1ComparisonDataKind": "unknown",
                "normalizedComplexFingerprint": "unknown",
                "classPrerequisite": false,
                "targetClassComputed": false,
                "contractChecked": false
            }
        }));
        packet.boundary_statements.push(BoundaryStatementV1 {
            id: "boundary:saga-comparison".to_string(),
            kind: "silence_by_design".to_string(),
            scope_refs: vec!["saga-comparison:h1-transfer".to_string()],
            reason: "comparison_data_not_supplied".to_string(),
            text: "supply the missing comparison input".to_string(),
        });
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "pass"
        }));

        let mut missing_what_next = packet.clone();
        missing_what_next.computed_invariants[0]
            .as_object_mut()
            .unwrap()
            .remove("whatNext");
        let checks = validate_measurement_packet_v1(&missing_what_next);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));

        let mut missing_boundary = packet.clone();
        missing_boundary.boundary_statements.pop();
        let checks = validate_measurement_packet_v1(&missing_boundary);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));

        let mut mismatched_boundary = packet;
        mismatched_boundary
            .boundary_statements
            .last_mut()
            .unwrap()
            .text = "different guidance".to_string();
        let checks = validate_measurement_packet_v1(&mismatched_boundary);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn comparison_contract_kind_owner_cannot_be_bypassed() {
        let mut packet = packet_fixture();
        packet.computed_invariants.push(json!({
            "invariantId": "comparison-owner-bypass",
            "kind": "h1-comparison-transfer",
            "evaluator": "ag.foundation",
            "status": "silence_by_design",
            "whatNext": "supply the missing comparison input",
            "value": {"status": "silence_by_design"},
            "representation": {"basis": "typed-silence"}
        }));
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-computed-invariants-typed"
                && check.result == "fail"
        }));
    }

    #[test]
    fn boundary_statement_unknown_kind_fails_validation() {
        let mut packet = packet_fixture();
        packet.boundary_statements[0].kind = "maybe_conclusion".to_string();
        let checks = validate_measurement_packet_v1(&packet);

        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn violated_assumption_boundary_scopes_to_not_computed_verdict() {
        let mut packet = packet_fixture();
        let finite_site_assumption = assumption_id_for_schema(&packet.assumptions[0]);
        packet.structural_verdict[0].verdict = "not_computed".to_string();
        packet.structural_verdict[0].verdict_data.method_status =
            "empty_selected_scope".to_string();
        packet.structural_verdict[0].depends_on_assumptions = vec![finite_site_assumption.clone()];
        packet.assumptions[0].status = "violated".to_string();
        packet.assumptions[0].checked_by = None;
        packet.boundary_statements = boundary_statements_for_measurement_packet(&packet);

        assert!(packet.boundary_statements.iter().any(|statement| {
            statement.kind == "violated_assumption"
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| scope_ref == &finite_site_assumption)
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| scope_ref.starts_with("structuralVerdict/"))
        }));
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "pass"
        }));

        let mut broken = packet;
        let statement = broken
            .boundary_statements
            .iter_mut()
            .find(|statement| statement.kind == "violated_assumption")
            .expect("violated assumption boundary exists");
        statement.scope_refs = vec!["part8/4.2".to_string()];
        let checks = validate_measurement_packet_v1(&broken);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-schema052-boundary-statements" && check.result == "fail"
        }));
    }

    #[test]
    fn cech_empty_selected_cover_contexts_are_not_computed() {
        let mut normalized = normalized_fixture();
        normalized.covers[0].context_ids.clear();
        let profile = packet_fixture().profile;

        let measurement = evaluate_cech_obstruction_v1(&normalized, &profile);

        assert_eq!(measurement.verdict, "not_computed");
        assert!(!measurement.zero);
        assert!(!measurement.non_zero);
        assert_eq!(measurement.method_status, "empty_selected_scope");
        assert!(measurement.reason.contains("empty_selected_scope"));
        assert!(measurement.assumptions.iter().any(|entry| {
            entry.theorem_ref == "part8/B.8.2-empty-selected-scope"
                && entry.status == "violated"
                && entry.assumption == "U-adequate cover selects a non-empty Cech 1-skeleton"
        }));
    }

    #[test]
    fn gluing_projection_does_not_infer_cover_nerve_without_packet_projection() {
        let normalized = normalized_fixture();
        let packet = packet_fixture();

        let gluing = gluing_geometry_projection_v1(&normalized, &packet);

        assert_eq!(
            gluing["nerve"]["triangles"],
            json!([]),
            "viewer gluing projection must not infer triangle geometry when packet has no coverNerveProjection"
        );
        assert_eq!(
            gluing["nerve"]["triangleSource"],
            "missing packet coverNerveProjection; viewer does not infer cover triangles"
        );
    }

    #[test]
    fn gluing_projection_caps_cocycle_support_edges_and_reports_omissions() {
        let mut normalized = normalized_fixture();
        let mut context_ids = Vec::new();
        let mut contexts = Vec::new();
        let mut atoms = Vec::new();
        for index in 0..=GLUING_COCYCLE_EDGE_RENDER_LIMIT + 1 {
            let context = format!("ctx:{index}");
            let atom_id = format!("atom:section-value:{index}");
            context_ids.push(context.clone());
            contexts.push(NormalizedContextV2 {
                source_context_id: context.clone(),
                normalized_context_id: context.clone(),
                atom_ids: vec![atom_id.clone()],
                restricts_to: if index <= GLUING_COCYCLE_EDGE_RENDER_LIMIT {
                    vec![format!("ctx:{}", index + 1)]
                } else {
                    Vec::new()
                },
                source_refs: vec![format!("fixture://{context}")],
                poset_status: "selected".to_string(),
            });
            atoms.push(NormalizedAtomV2 {
                source_atom_id: atom_id.clone(),
                normalized_atom_id: atom_id,
                atom_kind: "component".to_string(),
                subject: context.clone(),
                axis: "cech".to_string(),
                predicate: "sectionValue".to_string(),
                object: Some(format!("section:{index}")),
                source_refs: vec![format!("fixture://{context}")],
                context_memberships: vec![context],
                normalization_status: "normalized".to_string(),
            });
        }
        normalized.contexts = contexts;
        normalized.atoms = atoms;
        normalized.covers[0].context_ids = context_ids;
        normalized.summary.atom_count = normalized.atoms.len();
        normalized.summary.normalized_atom_count = normalized.atoms.len();
        normalized.summary.context_count = normalized.contexts.len();

        let packet = packet_fixture();
        let gluing = gluing_geometry_projection_v1(&normalized, &packet);

        assert_eq!(
            gluing["cocycleRibbon"]["supportEdges"]
                .as_array()
                .expect("support edges are array")
                .len(),
            GLUING_COCYCLE_EDGE_RENDER_LIMIT,
            "cocycle ribbon support must be capped before entering the viewer projection"
        );
        assert_eq!(
            gluing["renderLimits"]["cocycleSupportEdges"].as_u64(),
            Some(GLUING_COCYCLE_EDGE_RENDER_LIMIT as u64)
        );
        assert_eq!(
            gluing["omittedGeometryCounts"]["cocycleSupportEdges"].as_u64(),
            Some(1),
            "cocycle ribbon omissions must be reported for large H1 support"
        );
    }

    #[test]
    fn forbidden_cages_do_not_fallback_to_predicate_atoms() {
        let normalized = normalized_fixture();
        let packet = packet_fixture();

        let cages = forbidden_cage_projection(&normalized, &packet);

        assert!(
            cages.is_empty(),
            "predicate names alone must not create forbidden support cages without packet support"
        );
    }

    #[test]
    fn repair_morphs_link_related_forbidden_cages() {
        let normalized = normalized_fixture();
        let mut packet = packet_fixture();
        packet.computed_invariants = vec![json!({
            "invariantId": "square-free-repair:test",
            "obstructionIdeal": {
                "generators": [
                    {
                        "generatorId": "g0",
                        "support": ["x_checkout", "x_inventory"],
                        "supportAtomRefs": ["atom:checkout-inventory"]
                    },
                    {
                        "generatorId": "g1",
                        "support": ["x_inventory", "x_payment"],
                        "supportAtomRefs": ["atom:inventory-payment"]
                    }
                ]
            },
            "alexanderDualRepair": {
                "minimalHittingSets": [
                    ["x_inventory"],
                    ["x_checkout", "x_payment"]
                ]
            }
        })];

        let cages = forbidden_cage_projection(&normalized, &packet);
        let morphs = repair_morph_projection(&normalized, &packet, &cages);

        assert_eq!(cages.len(), 2);
        assert_eq!(morphs.len(), 2);
        assert!(morphs.iter().all(|morph| {
            morph["fromCageRefs"]
                .as_array()
                .is_some_and(|refs| refs.len() == 2)
                && morph["fromAtomRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
        }));
        assert_eq!(
            morphs[1]["fromCageRef"], "forbidden-cage:g1",
            "multiple repair morphs must not all start from the first forbidden cage"
        );
    }
}
