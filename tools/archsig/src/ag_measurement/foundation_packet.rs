pub fn build_foundation_measurement_packet_v1(
    normalized: &NormalizedArchMapV2,
    _archmap: &ArchMapDocumentV2,
    policy: &LawPolicyDocumentV1,
    law_surface: Option<&LawEquationSurfaceV1>,
    measurement_profiles: &BTreeMap<String, MeasurementProfileV1>,
    archmap_ref: &str,
    law_policy_ref: &str,
    law_surface_ref: Option<&str>,
    measurement_profile_ref: &str,
) -> Result<ArchSigMeasurementPacketV1, String> {
    if policy.policies.iter().any(|entry| entry.pack.is_some()) {
        return Err(
            "Stage 1 measurement packet builder rejects retired LawPolicy pack selectors; use explicit law/evaluator entries"
                .to_string(),
        );
    }
    let selected_profile = selected_measurement_profile_v1(policy, measurement_profiles)
        .ok_or_else(|| "AG measurement packet requires measurementProfileRef".to_string())?
        .clone();
    let law_surface = law_surface.ok_or_else(|| {
        "AG measurement packet requires --law-surface; witness variables are supplied only by the law surface".to_string()
    })?;
    let law_policy_report = crate::validate_law_policy_v1_report_with_profiles(
        policy,
        law_policy_ref,
        measurement_profiles,
        Some(law_surface),
    );
    if law_policy_report.summary.result == "fail" {
        return Err(
            "AG measurement packet requires a law-policy selector that passes validation"
                .to_string(),
        );
    }
    let profile = profile_with_law_surface_witnesses(policy, &selected_profile, law_surface)?;
    let derived_complex = derive_saga_complex_from_normalized(normalized, &profile);
    let stage3_examples =
        crate::validate_law_surface_stage3_against_archmap_v1(law_surface, &profile, normalized);
    if !stage3_examples.is_empty() {
        return Err(format!(
            "law-equation-surface measurement contract failed: {}",
            stage3_examples
                .iter()
                .map(|example| {
                    format!(
                        "{}={}",
                        example.source.as_deref().unwrap_or("unknown"),
                        example.target.as_deref().unwrap_or("invalid")
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    validate_profile_refs(&profile, normalized)?;
    for candidate in measurement_profiles.values() {
        validate_profile_refs(candidate, normalized)?;
        if candidate.site_ref != selected_profile.site_ref
            || candidate.cover_ref != selected_profile.cover_ref
        {
            return Err(format!(
                "measurement profiles {} and {} must have matching normalized site/cover refs",
                selected_profile.profile_id, candidate.profile_id
            ));
        }
    }
    let mut structural_verdict = Vec::new();
    let mut computed_invariants = vec![json!({
        "invariantId": "finite-poset-site-shape",
        "archmapRef": archmap_ref,
        "atomCount": normalized.summary.atom_count,
        "contextCount": normalized.summary.context_count,
        "coverCount": normalized.summary.cover_count,
        "doctrineFingerprint": normalized.summary.doctrine_fingerprint
    })];
    let mut analytic_readings = vec![AgAnalyticReadingV1 {
        reading_id: "candidate-regime:stability-placeholder".to_string(),
        evaluator: "ag.foundation".to_string(),
        value: json!({
            "state": "not_evaluated",
            "reason": "theorem-candidate readings are analytic-only until a follow-up evaluator computes them"
        }),
        regime: Some("theorem-candidate".to_string()),
        structural_verdict_ref: None,
    }];
    let mut assumptions = vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/4.2".to_string(),
            assumption: "finite site".to_string(),
            status: "checked".to_string(),
            checked_by: Some("archmap-schema052-validation.contexts-finite".to_string()),
            assumed_by: None,
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/4.2".to_string(),
            assumption: "U-adequate cover".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!(
                "measurement-profile:{}",
                policy
                    .measurement_profile_ref
                    .as_deref()
                    .unwrap_or_default()
            )),
        },
    ];

    for entry in policy.policies.iter().filter(|entry| {
        entry
            .evaluator
            .as_deref()
            .is_some_and(|evaluator| evaluator.starts_with("ag."))
    }) {
        let evaluator = entry.evaluator.as_deref().unwrap_or_default();
        let entry_profile = entry
            .profile_ref
            .as_deref()
            .and_then(|profile_ref| measurement_profiles.get(profile_ref))
            .unwrap_or(&selected_profile);
        let profile = profile_with_law_surface_witnesses(policy, entry_profile, law_surface)?;
        validate_profile_refs(&profile, normalized)?;
        if let Some(ceiling) = profile
            .diagnostic_ceiling
            .as_ref()
            .and_then(|value| value.as_ref())
            .and_then(Value::as_str)
        {
            if diagnostic_stage_rank(ceiling)
                .is_some_and(|ceiling_rank| evaluator_stage_rank(evaluator) > ceiling_rank)
            {
                let method_status = "diagnostic_ceiling_not_reached";
                computed_invariants.push(json!({
                    "invariantId": format!("diagnostic-ceiling:{evaluator}:{}", profile.profile_id),
                    "evaluator": evaluator,
                    "status": "not_computed",
                    "methodStatus": method_status,
                    "diagnosticCeiling": ceiling,
                    "reason": format!("{evaluator} is above the declared diagnostic ceiling {ceiling}")
                }));
                structural_verdict.push(AgStructuralVerdictV1 {
                    evaluator: evaluator.to_string(),
                    law: entry.law.clone().unwrap_or_else(|| evaluator.to_string()),
                    verdict: "not_computed".to_string(),
                    verdict_data: AgVerdictDataV1 {
                        in_scope: true,
                        zero: false,
                        non_zero: false,
                        method_status: method_status.to_string(),
                        cert_ref: None,
                    },
                    depends_on_assumptions: Vec::new(),
                    reason: Some(format!(
                        "{evaluator} is above the declared diagnostic ceiling {ceiling}; the evaluator remains silent by design"
                    )),
                });
                continue;
            }
        }
        let execution_plan = build_law_execution_plan(
            normalized,
            Some(law_surface),
            entry.law.as_deref(),
            evaluator,
            &profile,
        )?;
        if evaluator == "ag.cech-obstruction" {
            validate_cech_profile_v1(&profile)?;
            let measurement = evaluate_cech_obstruction_v1(normalized, &profile);
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.cech-obstruction".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.coherence-obstruction" {
            validate_coherence_profile_v1(&profile)?;
            let measurement = evaluate_coherence_obstruction_v1(normalized, &profile);
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.coherence-obstruction".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.restriction-compatibility" {
            validate_restriction_profile_v1(&profile)?;
            let measurement = evaluate_restriction_compatibility_v1(normalized, &profile)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.restriction-compatibility".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.section-factorization" {
            validate_section_profile_v1(&profile)?;
            let measurement =
                evaluate_section_factorization_v1(normalized, &profile, execution_plan.as_ref())?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.section-factorization".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.boundary-residue" {
            validate_boundary_residue_profile_v1(&profile)?;
            let measurement = evaluate_boundary_residue_v1(normalized, &profile)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.boundary-residue".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.square-free-repair" {
            let law_id = entry.law.as_deref().ok_or_else(|| {
                "ag.square-free-repair requires an explicit law selector".to_string()
            })?;
            let law = resolve_closed_law(Some(law_surface), law_id, evaluator)?;
            let (witness_variables, archmap_aliases, binding_axis, binding_predicate) =
                law_witness_bindings(law)?;
            validate_square_free_profile_v1(&profile, &witness_variables)?;
            let measurement = evaluate_square_free_repair_v1(
                normalized,
                &profile,
                law,
                &witness_variables,
                &archmap_aliases,
                &binding_axis,
                &binding_predicate,
            )?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry.law.clone().unwrap_or_else(|| law_id.to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.law-conflict-tor" {
            let tor_laws =
                resolve_tor_laws(Some(law_surface), entry.law_pair.as_deref(), evaluator)?;
            let witness_variables = merged_law_witness_bindings(&tor_laws)?;
            validate_tor_profile_v1(&profile, &witness_variables)?;
            let measurement =
                evaluate_law_conflict_tor_v1(normalized, &profile, &tor_laws, &witness_variables)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.law-conflict-tor".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.sheaf-laplacian" {
            validate_laplacian_profile_v1(&profile)?;
            let measurement = evaluate_sheaf_laplacian_v1(normalized, &profile)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.sheaf-laplacian".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: false,
                    non_zero: false,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.harmonic-debt" {
            let measurement = evaluate_harmonic_debt_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
        } else if evaluator == "ag.period-stokes" {
            validate_period_profile_v1(&profile)?;
            let measurement = evaluate_period_stokes_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
        } else if evaluator == "ag.period-stokes-audit" {
            validate_period_audit_profile_v1(&profile)?;
            let measurement = evaluate_period_stokes_audit_v1(normalized, &profile)?;
            let depends_on_assumptions = assumption_theorem_refs(&measurement.assumptions);
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.period-stokes-audit".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                depends_on_assumptions,
                reason: Some(measurement.reason),
            });
        } else if evaluator == "ag.support-transfer" {
            validate_transfer_profile_v1(&profile)?;
            let measurement = evaluate_support_transfer_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            analytic_readings.extend(measurement.analytic_readings);
            assumptions.extend(measurement.assumptions);
        } else if evaluator == "ag.saga-descent" {
            let measurement = evaluate_saga_descent_v1(
                normalized,
                &profile,
                &derived_complex,
                Some(law_surface),
                execution_plan.as_ref(),
            );
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.extend(measurement.structural_verdict);
        } else if evaluator == "ag.saga-grounded" {
            if let Some(execution_plan) = execution_plan.as_ref() {
                let measurement = evaluate_saga_grounded_v1(
                    normalized,
                    &profile,
                    &derived_complex,
                    law_surface,
                    execution_plan,
                );
                computed_invariants.extend(measurement.computed_invariants);
                assumptions.extend(measurement.assumptions);
                structural_verdict.extend(measurement.structural_verdict);
            } else {
                computed_invariants.push(json!({
                    "invariantId": "saga-generated-end-to-end-packet",
                    "kind": "saga-grounded-defect-quotient",
                    "evaluator": "ag.saga-grounded",
                    "status": "not_computed",
                    "methodStatus": "execution_plan_not_supplied"
                }));
                structural_verdict.push(AgStructuralVerdictV1 {
                    evaluator: evaluator.to_string(),
                    law: entry.law.clone().unwrap_or_else(|| evaluator.to_string()),
                    verdict: "not_computed".to_string(),
                    verdict_data: AgVerdictDataV1 {
                        in_scope: true,
                        zero: false,
                        non_zero: false,
                        method_status: "execution_plan_not_supplied".to_string(),
                        cert_ref: None,
                    },
                    depends_on_assumptions: Vec::new(),
                    reason: Some(
                        "ag.saga-grounded requires a derived grounding execution plan".to_string(),
                    ),
                });
            }
        } else {
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry.law.clone().unwrap_or_else(|| evaluator.to_string()),
                verdict: "unmeasured".to_string(),
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: false,
                    non_zero: false,
                    method_status: "schema_foundation_only".to_string(),
                    cert_ref: None,
                },
                depends_on_assumptions: Vec::new(),
                reason: Some(
                    "AG evaluator schema is registered; mathematical computation is implemented by follow-up evaluator issues".to_string(),
                ),
            });
        }
    }
    let measured_invariant_refs = structural_verdict
        .iter()
        .filter(|row| matches!(row.verdict.as_str(), "measured_zero" | "measured_nonzero"))
        .flat_map(|row| generated_invariant_refs_for_row(row, &computed_invariants, &profile))
        .collect::<BTreeSet<_>>();
    for invariant in &mut computed_invariants {
        if invariant.get("status").is_none()
            && invariant
                .get("invariantId")
                .and_then(Value::as_str)
                .is_some_and(|invariant_id| measured_invariant_refs.contains(invariant_id))
        {
            invariant["status"] = json!("computed");
        }
    }
    let mut non_conclusions = vec![
        format!(
            "ArchSig v0.5.4 foundation packet is computed from {archmap_ref} and {law_policy_ref}; it is not a Lean proof object."
        ),
        "Unmeasured AG evaluator rows are schema handoff rows, not measured zero.".to_string(),
        "Theorem-candidate readings are analytic-only and cannot generate structural verdicts."
            .to_string(),
    ];
    if let Some(ceiling) = profile
        .diagnostic_ceiling
        .as_ref()
        .and_then(|value| value.as_ref())
        .and_then(Value::as_str)
        .filter(|ceiling| *ceiling != "raw-values")
    {
        non_conclusions.push(format!(
            "silence_by_design: diagnostic ceiling {ceiling} is not reached by the foundation evaluator; supply the corresponding SAGA data before emitting that stage"
        ));
    }
    let observation_invariant_refs = structural_verdict
        .iter()
        .map(|row| generated_invariant_refs_for_row(row, &computed_invariants, &profile))
        .collect::<Vec<_>>();
    let observation_source_refs = structural_verdict
        .iter()
        .map(|row| {
            generated_observation_source_refs_for_row(
                normalized,
                row,
                &profile,
                &computed_invariants,
            )
        })
        .collect::<Vec<_>>();
    let observation_scope_sizes = structural_verdict
        .iter()
        .map(|row| {
            generated_observation_scope_size(row, normalized, &profile, &computed_invariants)
        })
        .collect::<Vec<_>>();
    let mut packet = ArchSigMeasurementPacketV1 {
        schema: ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA.to_string(),
        packet_id: format!("measurement:{}", normalized.source_archmap_id),
        profile,
        profiles: (measurement_profiles.len() > 1)
            .then(|| measurement_profiles.values().cloned().collect())
            .unwrap_or_default(),
        structural_verdict,
        computed_invariants,
        analytic_readings,
        assumptions,
        supplied_data: supplied_data_ledger(
            archmap_ref,
            law_policy_ref,
            law_surface_ref,
            measurement_profile_ref,
        ),
        boundary_statements: Vec::new(),
        non_conclusions,
        observation_source_refs,
        observation_scope_sizes,
        observation_invariant_refs,
    };
    apply_assumption_dependency_propagation(&mut packet);
    refresh_observation_evidence(&mut packet, normalized);
    packet.boundary_statements = boundary_statements_for_measurement_packet(&packet);
    Ok(packet)
}

fn generated_invariant_refs_for_row(
    row: &AgStructuralVerdictV1,
    invariants: &[Value],
    profile: &MeasurementProfileV1,
) -> Vec<String> {
    if let Some(cert_ref) = row
        .verdict_data
        .cert_ref
        .as_deref()
        .and_then(|cert_ref| cert_ref.strip_prefix("computedInvariants/"))
    {
        if invariants
            .iter()
            .any(|invariant| invariant.get("invariantId").and_then(Value::as_str) == Some(cert_ref))
        {
            return vec![cert_ref.to_string()];
        }
    }
    if !matches!(row.verdict.as_str(), "measured_zero" | "measured_nonzero") {
        return Vec::new();
    }
    invariants
        .iter()
        .filter(|invariant| {
            invariant.get("evaluator").and_then(Value::as_str) == Some(row.evaluator.as_str())
                && invariant
                    .get("selectedCoverRef")
                    .and_then(Value::as_str)
                    .is_none_or(|cover_ref| cover_ref == profile.cover_ref)
        })
        .filter_map(|invariant| invariant.get("invariantId").and_then(Value::as_str))
        .map(str::to_string)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn generated_invariants_for_row<'a>(
    row: &AgStructuralVerdictV1,
    invariants: &'a [Value],
    profile: &MeasurementProfileV1,
) -> Vec<&'a Value> {
    let refs = generated_invariant_refs_for_row(row, invariants, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    invariants
        .iter()
        .filter(|invariant| {
            invariant
                .get("invariantId")
                .and_then(Value::as_str)
                .is_some_and(|invariant_id| refs.contains(invariant_id))
        })
        .collect()
}

fn generated_observation_source_refs_for_row(
    normalized: &NormalizedArchMapV2,
    row: &AgStructuralVerdictV1,
    profile: &MeasurementProfileV1,
    invariants: &[Value],
) -> Vec<String> {
    if !matches!(row.verdict.as_str(), "measured_zero" | "measured_nonzero") {
        return Vec::new();
    }
    let selected_contexts = selected_cover_contexts(normalized, profile);
    let selected_context_aliases = normalized
        .contexts
        .iter()
        .filter(|context| {
            selected_contexts.contains(&context.normalized_context_id)
                || selected_contexts.contains(&context.source_context_id)
        })
        .flat_map(|context| {
            [
                context.normalized_context_id.as_str(),
                context.source_context_id.as_str(),
            ]
        })
        .collect::<BTreeSet<_>>();
    let row_invariants = generated_invariants_for_row(row, invariants, profile);
    let row_invariant_values = row_invariants
        .iter()
        .map(|invariant| (*invariant).clone())
        .collect::<Vec<_>>();
    let mut atom_refs = collect_packet_refs_from_values(
        &row_invariant_values,
        &[
            "supportAtomRefs",
            "mismatchSupportRefs",
            "witnessSupportRefs",
            "atomRefs",
            "atomRef",
        ],
    );
    atom_refs.extend(atom_refs_for_row(normalized, row));
    let atom_refs = normalize_atom_refs(normalized, atom_refs)
        .into_iter()
        .filter(|atom_ref| {
            normalized
                .atoms
                .iter()
                .find(|atom| atom.normalized_atom_id == *atom_ref)
                .is_some_and(|atom| {
                    atom.context_memberships.is_empty()
                        || atom
                            .context_memberships
                            .iter()
                            .any(|context| selected_context_aliases.contains(context.as_str()))
                })
        })
        .collect::<Vec<_>>();
    let mut source_refs = BTreeSet::new();
    if let Some(cover) = normalized.covers.iter().find(|cover| {
        cover.normalized_cover_id == profile.cover_ref || cover.source_cover_id == profile.cover_ref
    }) {
        source_refs.extend(
            cover
                .source_refs
                .iter()
                .map(|source_ref| sanitize_source_ref(source_ref)),
        );
    }
    source_refs.extend(
        normalized
            .contexts
            .iter()
            .filter(|context| {
                selected_context_aliases.contains(context.normalized_context_id.as_str())
            })
            .flat_map(|context| context.source_refs.iter())
            .map(|source_ref| sanitize_source_ref(source_ref)),
    );
    source_refs.extend(source_refs_for_atoms(normalized, &atom_refs));
    let mut invariant_source_refs = BTreeSet::new();
    let source_ref_keys = BTreeSet::from(["sourceRefs", "sourceRef"]);
    for invariant in row_invariants {
        collect_packet_refs(invariant, &source_ref_keys, &mut invariant_source_refs);
    }
    source_refs.extend(
        invariant_source_refs
            .into_iter()
            .map(|source_ref| sanitize_source_ref(&source_ref)),
    );
    source_refs.into_iter().collect()
}

fn generated_observation_scope_size(
    row: &AgStructuralVerdictV1,
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    invariants: &[Value],
) -> Value {
    if !matches!(row.verdict.as_str(), "measured_zero" | "measured_nonzero") {
        return json!({"contexts": 0, "edges": 0, "triangles": 0});
    }
    let row_invariants = generated_invariants_for_row(row, invariants, profile);
    let selected_contexts = selected_cover_contexts(normalized, profile);
    let contexts = row_invariants
        .iter()
        .find_map(|invariant| invariant.get("contextCount").and_then(Value::as_u64))
        .map(|count| count as usize)
        .unwrap_or(selected_contexts.len());
    let edges = row_invariants
        .iter()
        .find_map(|invariant| {
            invariant
                .get("restrictionEdgeCount")
                .and_then(Value::as_u64)
        })
        .map(|count| count as usize)
        .unwrap_or_else(|| cech_edges(normalized, &selected_contexts).len());
    let triangles = row_invariants
        .iter()
        .find_map(|invariant| {
            invariant
                .get("coverNerveProjection")
                .and_then(|projection| projection.get("faces"))
                .and_then(Value::as_array)
                .map(Vec::len)
        })
        .unwrap_or_default();
    json!({"contexts": contexts, "edges": edges, "triangles": triangles})
}

fn supplied_data_ledger(
    archmap_ref: &str,
    law_policy_ref: &str,
    law_surface_ref: Option<&str>,
    measurement_profile_ref: &str,
) -> Vec<SuppliedDataLedgerEntryV1> {
    let mut entries = vec![
        supplied_data_entry(
            "supplied:archmap",
            "archmap",
            archmap_ref,
            "archmap/v0.5.4-validation",
            "validated",
        ),
        supplied_data_entry(
            "supplied:law-policy",
            "law-policy",
            law_policy_ref,
            "law-policy/v0.5.4-validation",
            "validated",
        ),
        supplied_data_entry(
            "supplied:measurement-profile",
            "measurement-profile",
            measurement_profile_ref,
            "measurement-profile/v0.5.4-validation",
            "validated",
        ),
    ];
    if let Some(law_surface_ref) = law_surface_ref {
        entries.push(supplied_data_entry(
            "supplied:law-surface",
            "law-equation-surface",
            law_surface_ref,
            "law-equation-surface/v0.5.4-validation",
            "validated",
        ));
    }
    entries
}

fn supplied_data_entry(
    supplied_id: &str,
    kind: &str,
    source_artifact_ref: &str,
    check_ref: &str,
    status: &str,
) -> SuppliedDataLedgerEntryV1 {
    SuppliedDataLedgerEntryV1 {
        supplied_id: supplied_id.to_string(),
        kind: kind.to_string(),
        source_artifact_ref: source_artifact_ref.to_string(),
        conformance: json!({
            "status": status,
            "checkRef": check_ref,
            "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
        }),
    }
}
