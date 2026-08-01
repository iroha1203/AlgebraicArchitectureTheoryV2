#[derive(Debug, Clone)]
struct SquareFreeMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct CoherenceMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct CoherenceFaceV1 {
    face_id: String,
    context_refs: Vec<String>,
    edge_refs: Vec<String>,
    shared_atom_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct CoherenceTetrahedronV1 {
    tetrahedron_id: String,
    context_refs: Vec<String>,
    face_refs: Vec<String>,
    shared_atom_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct CoherenceWitnessV1 {
    atom_ref: String,
    face_ref: String,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct SquareFreeGeneratorV1 {
    generator_id: String,
    support: Vec<String>,
    support_atom_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct RestrictionMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct RestrictionGeneratorV1 {
    generator_id: String,
    context_ref: String,
    support: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct RestrictionEdgeCheckV1 {
    edge_ref: String,
    source_context: String,
    target_context: String,
    status: String,
    source_generators: Vec<RestrictionGeneratorV1>,
    target_generators: Vec<RestrictionGeneratorV1>,
    violations: Vec<RestrictionViolationV1>,
}

#[derive(Debug, Clone)]
struct RestrictionViolationV1 {
    generator_id: String,
    support: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct SectionMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct SectionForbiddenSupportV1 {
    support_id: String,
    support: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct SectionAssignmentV1 {
    assignment_id: String,
    assigned: BTreeMap<String, bool>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct BoundaryResidueMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct BoundaryResidueRoleV1 {
    atom_ref: String,
    context_ref: String,
    role: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct BoundaryResidueColumnV1 {
    column_id: String,
    source_context: String,
    boundary_context: String,
    support: Vec<String>,
    vector: Vec<u8>,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct BoundaryResidueMismatchV1 {
    atom_refs: Vec<String>,
    support: Vec<String>,
    vector: Vec<u8>,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct SquareFreeCertificateV1 {
    cert_ref: String,
    nsdepth: Option<usize>,
    support_atom_refs: Vec<String>,
    verified_minimal_forbidden_supports: Vec<Vec<String>>,
    status: String,
    effect: String,
}

#[derive(Debug, Clone)]
struct TorMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct TorCommonAmbientV1 {
    ambient_ref: String,
    atom_ref: String,
    law_pair: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TorIdealGeneratorV1 {
    law: String,
    generator_id: String,
    support: Vec<String>,
    square_free: bool,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TorConflictClassV1 {
    conflict_id: String,
    degree: usize,
    support: Vec<String>,
    multidegree: Vec<String>,
    shared_support: Vec<String>,
    left_law: String,
    left_generator_ref: String,
    right_law: String,
    right_generator_ref: String,
    context_refs: Vec<String>,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct LaplacianMeasurementV1 {
    verdict: String,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

struct HarmonicDebtMeasurementV1 {
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct LaplacianCellV1 {
    cell_id: String,
    value: f64,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct LaplacianEdgeV1 {
    source: String,
    target: String,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct PeriodMeasurementV1 {
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct PeriodAuditMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct PeriodIntegralV1 {
    form_id: String,
    cycle_id: String,
    value: f64,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct StokesAuditValueV1 {
    form_id: String,
    chain_id: String,
    value: f64,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TransferMeasurementV1 {
    computed_invariants: Vec<Value>,
    analytic_readings: Vec<AgAnalyticReadingV1>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct TransferPairingV1 {
    path_id: String,
    target_id: String,
    value: f64,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TransferRepairPathV1 {
    path_id: String,
    support_targets: Vec<String>,
    atom_ref: String,
    source_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct TransferGroundCostV1 {
    target_id: String,
    cost: f64,
    atom_ref: String,
    source_refs: Vec<String>,
}

fn evaluate_coherence_obstruction_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> CoherenceMeasurementV1 {
    let selected_contexts = selected_cover_contexts(normalized, profile);
    let selected_context_set = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let mut assumptions = coherence_assumptions(profile, "checked");
    let max_coherence_contexts = profile
        .finite_bounds
        .max_coherence_contexts
        .min(MAX_COHERENCE_CONTEXTS);
    if selected_contexts.len() > max_coherence_contexts {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1-selected-cover-budget".to_string(),
            assumption: format!(
                "selected cover has at most {max_coherence_contexts} contexts for finite H2 coherence enumeration"
            ),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
        return CoherenceMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "selected_cover_too_large".to_string(),
            cert_ref: None,
            reason: format!(
                "selected cover has {} contexts; ag.coherence-obstruction enumerates at most {max_coherence_contexts}",
                selected_contexts.len()
            ),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "not_computed",
                "selected_cover_too_large",
                &selected_contexts,
                &[],
                &[],
                &[],
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }
    let edges = cech_edges(normalized, &selected_contexts);
    let faces = coherence_faces(normalized, &selected_contexts, &edges, &profile.cover_ref);
    let tetrahedra = coherence_tetrahedra(normalized, &selected_contexts, &faces);
    let witness_atoms = coherence_witness_atoms(normalized, &selected_context_set);

    if profile.coefficient != "F2" {
        assumptions = coherence_assumptions(profile, "violated");
        return CoherenceMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "banding_violated".to_string(),
            cert_ref: None,
            reason: "selected coefficient is outside the banded abelian F2 coherence vocabulary"
                .to_string(),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "not_computed",
                "banding_violated",
                &selected_contexts,
                &edges,
                &faces,
                &tetrahedra,
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }

    if faces.is_empty() {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1-empty-selected-2-skeleton".to_string(),
            assumption: "selected cover supplies a non-empty triple-overlap 2-skeleton".to_string(),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
        return CoherenceMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "empty_selected_2_skeleton".to_string(),
            cert_ref: None,
            reason: "selected cover has no triple-overlap 2-skeleton for ag.coherence-obstruction"
                .to_string(),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "not_computed",
                "empty_selected_2_skeleton",
                &selected_contexts,
                &edges,
                &faces,
                &tetrahedra,
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }

    if faces.iter().any(|face| face.edge_refs.len() != 3) {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1-incomplete-selected-2-skeleton".to_string(),
            assumption: "selected triple-overlap faces have all three restriction boundary edges"
                .to_string(),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
        return CoherenceMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "incomplete_selected_2_skeleton".to_string(),
            cert_ref: None,
            reason: "selected triple-overlap 2-skeleton is missing a boundary restriction edge"
                .to_string(),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "not_computed",
                "incomplete_selected_2_skeleton",
                &selected_contexts,
                &edges,
                &faces,
                &tetrahedra,
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }

    if witness_atoms.is_empty() {
        return CoherenceMeasurementV1 {
            verdict: "unmeasured".to_string(),
            zero: false,
            non_zero: false,
            method_status: "coherence_witness_absent".to_string(),
            cert_ref: None,
            reason: "no coherence witness atom is supplied; H2 coherence remains silent"
                .to_string(),
            computed_invariants: vec![coherence_invariant_json(
                profile,
                "unmeasured",
                "coherence_witness_absent",
                &selected_contexts,
                &edges,
                &faces,
                &tetrahedra,
                &[],
                &[],
                0,
                0,
                0,
                0,
                false,
                Vec::new(),
            )],
            assumptions,
        };
    }

    let witnesses = coherence_witnesses_for_faces(&witness_atoms, &faces);
    let h = faces
        .iter()
        .map(|face| {
            (witnesses
                .iter()
                .filter(|witness| witness.face_ref == face.face_id)
                .count()
                % 2) as u8
        })
        .collect::<Vec<_>>();
    let d2_rows = coherence_d2_rows(&faces, &tetrahedra);
    let d2_h = d2_rows
        .iter()
        .map(|row| {
            row.iter()
                .zip(h.iter())
                .fold(0u8, |acc, (entry, value)| acc ^ (entry & value))
        })
        .collect::<Vec<_>>();
    let cocycle_gate_passed = d2_h.iter().all(|value| *value == 0);
    let d1_rows = coherence_d1_rows(&edges, &faces);
    let rank_d1 = matrix_rank_f2(d1_rows.clone());
    let rank_d2 = matrix_rank_f2(d2_rows.clone());
    let rank_ker_d2 = faces.len().saturating_sub(rank_d2);
    let h2_dimension = rank_ker_d2.saturating_sub(rank_d1);
    let selected_representative = cocycle_gate_passed
        .then(|| {
            if vector_in_span_f2(&d1_rows, &h) {
                h2_representative_f2(&d2_rows, &d1_rows, faces.len()).unwrap_or_default()
            } else {
                h.clone()
            }
        })
        .unwrap_or_default();
    let representative = coherence_representative_json(&selected_representative, &faces);

    let (verdict, zero, non_zero, method_status, reason) = if !cocycle_gate_passed {
        (
            "not_computed".to_string(),
            false,
            false,
            "not_2_cocycle".to_string(),
            "coherence 2-cochain fails the d2 h = 0 cocycle gate; im d1 membership is not evaluated".to_string(),
        )
    } else if h2_dimension == 0 {
        (
            "measured_zero".to_string(),
            true,
            false,
            "finite_f2_h2_coherence_computed".to_string(),
            "finite F2 H2 coherence quotient is zero on the selected cover".to_string(),
        )
    } else {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "finite_f2_h2_coherence_computed".to_string(),
            "finite F2 H2 coherence quotient is nonzero on the selected cover".to_string(),
        )
    };
    let cert_ref = (verdict != "not_computed").then(|| {
        format!(
            "computedInvariants/coherence-obstruction:{}",
            profile.profile_id
        )
    });

    CoherenceMeasurementV1 {
        verdict: verdict.to_string(),
        zero,
        non_zero,
        method_status: method_status.to_string(),
        cert_ref,
        reason,
        computed_invariants: vec![coherence_invariant_json(
            profile,
            if verdict == "not_computed" {
                "not_computed"
            } else {
                "computed"
            },
            &method_status,
            &selected_contexts,
            &edges,
            &faces,
            &tetrahedra,
            &witnesses,
            &h,
            rank_d1,
            rank_ker_d2,
            h2_dimension,
            d2_rows.len(),
            cocycle_gate_passed,
            representative,
        )],
        assumptions,
    }
}

fn resolve_closed_law<'a>(
    law_surface: Option<&'a LawEquationSurfaceV1>,
    law_id: &str,
    evaluator: &str,
) -> Result<&'a crate::LawEquationV1, String> {
    let surface = law_surface.ok_or_else(|| {
        format!(
            "{evaluator} requires --law-surface; no registry or MeasurementProfile fallback is permitted"
        )
    })?;
    let law = surface
        .laws
        .iter()
        .find(|law| law.law_id == law_id)
        .ok_or_else(|| {
            format!(
                "{evaluator} law {law_id} is not declared by supplied law surface {}",
                surface.id
            )
        })?;
    if law.condition_type != "closed-equational" {
        return Err(format!(
            "{evaluator} law {law_id} must be closed-equational, found {}",
            law.condition_type
        ));
    }
    Ok(law)
}

fn resolve_tor_laws<'a>(
    law_surface: Option<&'a LawEquationSurfaceV1>,
    law_pair: Option<&[String]>,
    evaluator: &str,
) -> Result<Vec<&'a crate::LawEquationV1>, String> {
    let surface = law_surface.ok_or_else(|| {
        format!(
            "{evaluator} requires --law-surface; no registry or MeasurementProfile fallback is permitted"
        )
    })?;
    let law_pair = law_pair.ok_or_else(|| {
        format!(
            "{evaluator} requires an explicit lawPair declaration; lawId naming conventions are not selectors"
        )
    })?;
    let unique_laws = law_pair.iter().collect::<BTreeSet<_>>();
    if law_pair.len() != 2 || unique_laws.len() != 2 {
        return Err(format!(
            "{evaluator} lawPair must contain exactly two distinct law ids"
        ));
    }
    let laws = law_pair
        .iter()
        .map(|law_id| resolve_closed_law(Some(surface), law_id, evaluator))
        .collect::<Result<Vec<_>, _>>()?;
    if laws.iter().any(|law| {
        law.witness_variables
            .iter()
            .any(|witness| witness.binding.axis.as_deref() != Some("square-free"))
    }) {
        return Err(format!(
            "{evaluator} lawPair declarations must use square-free witness bindings"
        ));
    }
    Ok(laws)
}

fn law_witness_bindings(
    law: &crate::LawEquationV1,
) -> Result<(Vec<String>, BTreeMap<String, String>, String, String), String> {
    let mut witness_variables = Vec::new();
    let mut archmap_aliases = BTreeMap::new();
    let mut binding_pairs = BTreeSet::new();
    for witness in &law.witness_variables {
        let variable = witness.variable.trim();
        if variable.is_empty() {
            return Err(format!(
                "law surface law {} contains an empty witness variable",
                law.law_id
            ));
        }
        let alias = witness
            .binding
            .archmap_variable
            .as_deref()
            .unwrap_or(variable)
            .trim();
        if alias.is_empty() {
            return Err(format!(
                "law surface law {} gives witness {variable} an empty ArchMap alias",
                law.law_id
            ));
        }
        let axis = witness.binding.axis.as_deref().ok_or_else(|| {
            format!(
                "law surface law {} gives witness {variable} no binding axis",
                law.law_id
            )
        })?;
        let predicate = witness.binding.predicate.as_deref().ok_or_else(|| {
            format!(
                "law surface law {} gives witness {variable} no binding predicate",
                law.law_id
            )
        })?;
        binding_pairs.insert((axis.to_string(), predicate.to_string()));
        if archmap_aliases
            .insert(variable.to_string(), alias.to_string())
            .is_some()
        {
            return Err(format!(
                "law surface law {} repeats witness variable {variable}",
                law.law_id
            ));
        }
        witness_variables.push(variable.to_string());
    }
    let mut binding_pairs = binding_pairs.into_iter();
    let (binding_axis, binding_predicate) = binding_pairs.next().ok_or_else(|| {
        format!(
            "law surface law {} must declare at least one witness binding",
            law.law_id
        )
    })?;
    if binding_pairs.next().is_some() {
        return Err(format!(
            "law surface law {} mixes binding axis/predicate pairs across witnesses",
            law.law_id
        ));
    }
    witness_variables.sort();
    Ok((
        witness_variables,
        archmap_aliases,
        binding_axis,
        binding_predicate,
    ))
}

fn merged_law_witness_bindings(laws: &[&crate::LawEquationV1]) -> Result<Vec<String>, String> {
    let mut witness_variables = BTreeSet::new();
    let mut archmap_aliases = BTreeMap::new();
    for law in laws {
        let (law_witnesses, law_aliases, _, _) = law_witness_bindings(law)?;
        witness_variables.extend(law_witnesses);
        for (variable, alias) in law_aliases {
            if let Some(previous) = archmap_aliases.insert(variable.clone(), alias.clone()) {
                if previous != alias {
                    return Err(format!(
                        "Tor law surface witness {variable} has conflicting ArchMap aliases {previous} and {alias}"
                    ));
                }
            }
        }
    }
    Ok(witness_variables.into_iter().collect())
}

fn declared_law_supports(
    law: &crate::LawEquationV1,
    witness_variables: &[String],
) -> Result<Vec<Vec<String>>, String> {
    let witness_set = witness_variables.iter().collect::<BTreeSet<_>>();
    let mut supports = Vec::new();
    for generator in &law.forbidden_support_generators {
        let mut support = generator.support.clone();
        support.sort();
        support.dedup();
        if support.is_empty()
            || support
                .iter()
                .any(|variable| !witness_set.contains(variable))
        {
            return Err(format!(
                "law surface law {} contains a forbidden support outside its declared witnesses",
                law.law_id
            ));
        }
        supports.push(support);
    }
    Ok(supports)
}

fn observed_support_matches(
    atom: &NormalizedAtomV2,
    support: &[String],
    archmap_aliases: &BTreeMap<String, String>,
    observed_axis: &str,
    observed_predicate: &str,
) -> bool {
    if atom.axis != observed_axis || atom.predicate != observed_predicate {
        return false;
    }
    let observed = square_free_atom_variables(atom)
        .into_iter()
        .collect::<BTreeSet<_>>();
    support.iter().all(|variable| {
        archmap_aliases
            .get(variable)
            .is_some_and(|alias| observed.contains(alias))
    })
}

fn observation_selector(
    evaluator_kind: &str,
    binding_axis: &str,
    binding_predicate: &str,
) -> Result<(&'static str, &'static str), String> {
    match evaluator_kind {
        "square-free" if binding_axis == "square-free" => {
            if matches!(binding_predicate, "support" | "cooccurrence") {
                Ok((
                    "square-free",
                    if binding_predicate == "support" {
                        "support"
                    } else {
                        "cooccurrence"
                    },
                ))
            } else {
                Err(format!(
                    "square-free law binding predicate {binding_predicate} is not an observed support predicate"
                ))
            }
        }
        "tor" if binding_axis == "square-free" => {
            if matches!(binding_predicate, "support" | "cooccurrence") {
                Ok(("tor", "lawIdealGenerator"))
            } else {
                Err(format!(
                    "Tor law binding predicate {binding_predicate} is not an accepted support predicate"
                ))
            }
        }
        _ => Err(format!(
            "{evaluator_kind} law binding axis/predicate {binding_axis}/{binding_predicate} is not executable"
        )),
    }
}

fn observed_tor_support_is_square_free(atom: &NormalizedAtomV2) -> bool {
    let raw_variables = atom
        .object
        .as_deref()
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .collect::<Vec<_>>();
    raw_variables.len() == raw_variables.iter().collect::<BTreeSet<_>>().len()
}

fn evaluate_square_free_repair_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    law: &crate::LawEquationV1,
    witness_variables: &[String],
    archmap_aliases: &BTreeMap<String, String>,
    binding_axis: &str,
    binding_predicate: &str,
) -> Result<SquareFreeMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let generators = square_free_generators_from_law_surface(
        normalized,
        &selected_contexts,
        law,
        witness_variables,
        archmap_aliases,
        binding_axis,
        binding_predicate,
    )?;
    let minimal_forbidden_supports = minimal_supports(
        generators
            .iter()
            .map(|generator| generator.support.clone())
            .collect(),
    );
    let delta_faces =
        delta_faces_from_forbidden_supports(&witness_variables, &minimal_forbidden_supports);
    let delta_facets = maximal_faces(&delta_faces);
    let reduced_homology = reduced_simplicial_homology_f2(&delta_faces);
    let repair_hitting_sets = minimal_hitting_sets(&witness_variables, &minimal_forbidden_supports);
    let invariant_id = format!("square-free-repair:{}", profile.profile_id);
    let certificate = square_free_certificate(
        normalized,
        &selected_contexts,
        &minimal_forbidden_supports,
        &repair_hitting_sets,
        &generators,
        witness_variables.len(),
        &invariant_id,
    )?;
    let has_observed_support = generators
        .iter()
        .any(|generator| !generator.support_atom_refs.is_empty());
    let (verdict, zero, non_zero, method_status, cert_ref, reason) = if !has_observed_support {
        (
            "measured_zero".to_string(),
            true,
            false,
            "square_free_observation_empty".to_string(),
            certificate
                .as_ref()
                .map(|certificate| certificate.cert_ref.clone()),
            "no selected square-free support atom realizes any declared obstruction generator"
                .to_string(),
        )
    } else if let Some(certificate) = &certificate {
        if matches!(certificate.status.as_str(), "verified" | "computed") {
            (
                "measured_nonzero".to_string(),
                false,
                true,
                "nsdepth_certificate_computed".to_string(),
                Some(certificate.cert_ref.clone()),
                "observed square-free obstruction support was found and ArchSig computed the finite NSdepth certificate from the selected obstruction ideal".to_string(),
            )
        } else {
            (
                "measured_nonzero".to_string(),
                false,
                true,
                format!(
                    "observed_support_nsdepth_certificate_{}",
                    certificate.status
                ),
                Some(certificate.cert_ref.clone()),
                format!(
                    "observed square-free obstruction support was found; structural verdict follows observed support atoms while the NSdepth certificate is {}",
                    certificate.status
                ),
            )
        }
    } else {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "square_free_observed_support".to_string(),
            None,
            "observed square-free obstruction support was found; structural verdict follows observed support atoms even though the NSdepth certificate was not computed".to_string(),
        )
    };

    let computed_invariants = vec![
        json!({
            "invariantId": format!("square-free-repair:{}", profile.profile_id),
            "evaluator": "ag.square-free-repair",
            "method": "finite-square-free-monomial-repair@1",
            "selectedCoverRef": profile.cover_ref,
            "witnessVariables": witness_variables,
            "obstructionIdeal": {
                "id": "I_Ob^U",
                "generators": generators.iter().map(|generator| {
                    json!({
                        "generatorId": generator.generator_id,
                        "support": generator.support,
                        "supportAtomRefs": generator.support_atom_refs
                    })
                }).collect::<Vec<_>>()
            },
            "minimalForbiddenSupports": minimal_forbidden_supports.clone(),
            "deltaComplex": {
                "id": "Delta_U",
                "faces": delta_faces,
                "reducedHomology": {
                    "field": "F2",
                    "method": "finite-f2-simplicial-boundary@1",
                    "betti": reduced_homology
                }
            },
            "alexanderDualRepair": {
                "minimalHittingSets": repair_hitting_sets.clone(),
                "minimality": "checked_by_finite_support_enumeration"
            },
            "nsdepthCertificate": certificate.as_ref().map(|certificate| json!({
                "status": certificate.status,
                "certificateRef": certificate.cert_ref,
                "nsdepth": certificate.nsdepth,
                "supportAtomRefs": certificate.support_atom_refs,
                "verifiedMinimalForbiddenSupports": certificate.verified_minimal_forbidden_supports,
                "effect": certificate.effect
            })).unwrap_or_else(|| json!({
                "status": "missing",
                "effect": "NSdepth certificate is not computed; structural verdict follows observed support atom occurrence"
            }))
        }),
        lawful_locus_arrangement_invariant(
            profile,
            &witness_variables,
            &delta_facets,
            &minimal_forbidden_supports,
        ),
        delta_facet_link_reading_invariant(
            profile,
            &witness_variables,
            &delta_faces,
            &delta_facets,
        ),
    ];
    let analytic_readings = vec![AgAnalyticReadingV1 {
        reading_id: format!("theorem-candidate:repair-inspection:{}", profile.profile_id),
        evaluator: "ag.foundation".to_string(),
        value: json!({
            "readingKind": "repair-lower-bound-inspection@1",
            "selectedCoverRef": profile.cover_ref,
            "minimalForbiddenSupports": minimal_forbidden_supports,
            "minimalHittingSets": repair_hitting_sets,
            "lowerBoundSource": "alexanderDualRepair.minimalHittingSets",
            "nonClaim": "not automatic repair; not operation semantics",
            "reason": "repair inspection glyphs are viewer lower-bound markers grounded in the packet repair enumeration"
        }),
        regime: Some("theorem-candidate".to_string()),
        structural_verdict_ref: None,
    }];
    Ok(SquareFreeMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status,
        cert_ref,
        reason,
        computed_invariants,
        analytic_readings,
        assumptions: vec![
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/5.1".to_string(),
                assumption: "square-free witness variables selected by supplied law-equation-surface"
                    .to_string(),
                status: "checked".to_string(),
                checked_by: Some(format!(
                    "law-surface:provided-law-equation-surface"
                )),
                assumed_by: None,
            },
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/5.2".to_string(),
                assumption: "finite support family for Alexander dual enumeration".to_string(),
                status: "checked".to_string(),
                checked_by: Some("archmap-schema052-validation.contexts-finite".to_string()),
                assumed_by: None,
            },
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part3/7.2B".to_string(),
                assumption: "NSdepth certificate payload covers the computed square-free obstruction ideal within the selected witness family".to_string(),
                status: certificate
                    .as_ref()
                    .filter(|certificate| {
                        matches!(certificate.status.as_str(), "verified" | "computed")
                    })
                    .map(|_| "checked")
                    .unwrap_or("assumed")
                    .to_string(),
                checked_by: certificate
                    .as_ref()
                    .filter(|certificate| {
                        matches!(certificate.status.as_str(), "verified" | "computed")
                    })
                    .map(|certificate| format!("ag.square-free-repair:{}", certificate.cert_ref)),
                assumed_by: certificate
                    .as_ref()
                    .map(|certificate| {
                        if matches!(certificate.status.as_str(), "verified" | "computed") {
                            None
                        } else {
                            Some(certificate.cert_ref.clone())
                        }
                    })
                    .unwrap_or_else(|| Some(format!("measurement-profile:{}", profile.profile_id))),
            },
        ],
    })
}

fn lawful_locus_arrangement_invariant(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
    facets: &[Vec<String>],
    minimal_forbidden_supports: &[Vec<String>],
) -> Value {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let components = facets
        .iter()
        .enumerate()
        .map(|(index, facet)| {
            let facet_set = facet.iter().cloned().collect::<BTreeSet<_>>();
            let vanishing_coords = witness_set
                .difference(&facet_set)
                .cloned()
                .collect::<Vec<_>>();
            json!({
                "componentId": format!("lawful-locus-component:{}", index + 1),
                "facet": facet,
                "vanishingCoords": vanishing_coords,
                "dimension": facet.len()
            })
        })
        .collect::<Vec<_>>();
    let dimension = facets.iter().map(Vec::len).max().unwrap_or(0);

    json!({
        "invariantId": format!("lawful-locus-arrangement:{}", profile.profile_id),
        "evaluator": "ag.square-free-repair",
        "method": "finite-delta-coordinate-arrangement@1",
        "claimScope": "selected cover and selected witness-family relative finite Delta_U coordinate arrangement",
        "selectedCoverRef": profile.cover_ref,
        "locusSymbol": "Flat_U(X)=V(I_Delta)",
        "witnessVariables": witness_variables,
        "minimalForbiddenSupports": minimal_forbidden_supports,
        "facets": facets,
        "components": components,
        "dimension": dimension,
        "irreducibleComponentCount": facets.len(),
        "nonConclusions": [
            "This invariant does not evaluate section-specific s^* I_Ob^U=0.",
            "The dimension is a finite coordinate-subspace arrangement dimension, not a total-correctness or runtime-safety claim.",
            "irreducibleComponentCount is not a safety score or structural verdict."
        ]
    })
}

fn delta_facet_link_reading_invariant(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
    delta_faces: &[Vec<String>],
    facets: &[Vec<String>],
) -> Value {
    let facet_dimensions = facets
        .iter()
        .enumerate()
        .map(|(index, facet)| {
            json!({
                "facetId": format!("delta-facet:{}", index + 1),
                "facet": facet,
                "dimension": facet.len()
            })
        })
        .collect::<Vec<_>>();
    let min_dimension = facets.iter().map(Vec::len).min().unwrap_or(0);
    let max_dimension = facets.iter().map(Vec::len).max().unwrap_or(0);
    let is_pure = facets
        .first()
        .is_none_or(|first| facets.iter().all(|facet| facet.len() == first.len()));
    let link_readings = witness_variables
        .iter()
        .map(|vertex| {
            let link_faces = delta_link_faces(delta_faces, vertex);
            json!({
                "vertex": vertex,
                "linkFaces": link_faces,
                "boundaryRanks": simplicial_boundary_rank_reading(&link_faces),
                "componentCount": simplicial_component_count(&link_faces)
            })
        })
        .collect::<Vec<_>>();
    let link_reduced_betti = witness_variables
        .iter()
        .map(|vertex| {
            let link_faces = delta_link_faces(delta_faces, vertex);
            json!({
                "vertex": vertex,
                "betti": reduced_simplicial_homology_f2(&link_faces)
            })
        })
        .collect::<Vec<_>>();

    json!({
        "invariantId": format!("delta-facet-link-reading:{}", profile.profile_id),
        "evaluator": "ag.square-free-repair",
        "method": "finite-delta-facet-link-neutral-reading@1",
        "claimScope": "selected cover and selected witness-family relative raw Delta_U combinatorial reading",
        "selectedCoverRef": profile.cover_ref,
        "facetDimensionReading": {
            "facets": facet_dimensions,
            "minDimension": min_dimension,
            "maxDimension": max_dimension
        },
        "linkBoundaryReading": link_readings,
        "linkReducedBetti": link_reduced_betti,
        "isPure": is_pure,
        "nonConclusions": [
            "This invariant reports raw selected Delta_U facet and link quantities only.",
            "linkBoundaryReading does not decide boundary-local lawfulness.",
            "isPure is not a safety score or structural verdict."
        ]
    })
}

fn maximal_faces(faces: &[Vec<String>]) -> Vec<Vec<String>> {
    let mut facets = faces
        .iter()
        .filter(|face| {
            !faces.iter().any(|candidate| {
                face.len() < candidate.len() && is_subset(face.as_slice(), candidate.as_slice())
            })
        })
        .cloned()
        .collect::<Vec<_>>();
    facets.sort();
    facets.dedup();
    facets
}

fn evaluate_restriction_compatibility_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<RestrictionMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile);
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let edges = cech_edges(normalized, &selected_contexts);
    let witness_variables = restriction_witness_variables(profile);
    let generators = restriction_generators(normalized, &selected, &witness_variables)?;
    let generators_by_context = generators.iter().cloned().fold(
        BTreeMap::<String, Vec<RestrictionGeneratorV1>>::new(),
        |mut acc, generator| {
            acc.entry(generator.context_ref.clone())
                .or_default()
                .push(generator);
            acc
        },
    );
    let missing_edges = edges.is_empty();
    let missing_generators = !missing_edges
        && edges.iter().any(|edge| {
            generators_by_context
                .get(&edge.source_context)
                .is_none_or(Vec::is_empty)
                || generators_by_context
                    .get(&edge.target_context)
                    .is_none_or(Vec::is_empty)
        });
    let method_status = if missing_edges {
        "empty_selected_restriction_edges"
    } else if missing_generators {
        "restriction_generator_missing"
    } else {
        "finite_support_inclusion_computed"
    };
    let edge_checks = if missing_edges {
        Vec::new()
    } else {
        edges
            .iter()
            .map(|edge| {
                let source_generators = generators_by_context
                    .get(&edge.source_context)
                    .cloned()
                    .unwrap_or_default();
                let target_generators = generators_by_context
                    .get(&edge.target_context)
                    .cloned()
                    .unwrap_or_default();
                let violations = if source_generators.is_empty() || target_generators.is_empty() {
                    Vec::new()
                } else {
                    source_generators
                        .iter()
                        .filter(|source| {
                            !target_generators
                                .iter()
                                .any(|target| is_subset(&target.support, &source.support))
                        })
                        .map(|source| RestrictionViolationV1 {
                            generator_id: source.generator_id.clone(),
                            support: source.support.clone(),
                            source_refs: source.source_refs.clone(),
                        })
                        .collect::<Vec<_>>()
                };
                RestrictionEdgeCheckV1 {
                    edge_ref: edge.edge_id.clone(),
                    source_context: edge.source_context.clone(),
                    target_context: edge.target_context.clone(),
                    status: if source_generators.is_empty() || target_generators.is_empty() {
                        "not_computed"
                    } else if violations.is_empty() {
                        "compatible"
                    } else {
                        "violated"
                    }
                    .to_string(),
                    source_generators,
                    target_generators,
                    violations,
                }
            })
            .collect::<Vec<_>>()
    };
    let violations = edge_checks
        .iter()
        .flat_map(|edge| edge.violations.iter())
        .collect::<Vec<_>>();
    let (verdict, zero, non_zero, reason) = if missing_edges {
        (
            "not_computed".to_string(),
            false,
            false,
            "selected cover has no restriction edges for ag.restriction-compatibility".to_string(),
        )
    } else if missing_generators {
        (
            "not_computed".to_string(),
            false,
            false,
            "selected restriction edge is missing source or target ideal generator contract"
                .to_string(),
        )
    } else if violations.is_empty() {
        (
            "measured_zero".to_string(),
            true,
            false,
            "all selected restriction edges satisfy finite monomial support inclusion".to_string(),
        )
    } else {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "some selected restriction edge does not carry source ideal generators into the target ideal; this may disappear under sheaf image redefinition and is not a defect of the theory object".to_string(),
        )
    };
    let cert_ref = matches!(verdict.as_str(), "measured_zero" | "measured_nonzero").then(|| {
        format!(
            "computedInvariants/restriction-compatibility:{}",
            profile.profile_id
        )
    });

    Ok(RestrictionMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status: method_status.to_string(),
        cert_ref,
        reason,
        computed_invariants: vec![restriction_invariant_json(
            profile,
            method_status,
            &selected_contexts,
            &edges,
            &witness_variables,
            &edge_checks,
        )],
        assumptions: restriction_assumptions(profile, method_status),
    })
}

fn evaluate_section_factorization_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    execution_plan: Option<&LawExecutionPlanV1>,
) -> Result<SectionMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let witness_variables = if let Some(plan) = execution_plan {
        plan.section_witness_variables.clone().ok_or_else(|| {
            "ag.section-factorization execution plan contains no witness variables".to_string()
        })?
    } else {
        section_witness_variables(profile)
    };
    let forbidden_supports = if let Some(plan) = execution_plan {
        section_forbidden_supports_from_plan(
            normalized,
            &selected_contexts,
            &witness_variables,
            plan,
        )?
    } else {
        section_forbidden_supports(normalized, &selected_contexts, &witness_variables)?
    };
    let minimal_forbidden_supports = minimal_section_forbidden_supports(&forbidden_supports);
    let assignment = section_assignment(normalized, &selected_contexts, &witness_variables)?;
    let assignment_status = if let Some(assignment) = &assignment {
        if assignment.assigned.len() == witness_variables.len() {
            "total"
        } else {
            "partial"
        }
    } else {
        "absent"
    };
    let active_support = assignment
        .as_ref()
        .map(|assignment| {
            assignment
                .assigned
                .iter()
                .filter_map(|(variable, value)| value.then_some(variable.clone()))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let violated_supports = if assignment.is_some() {
        minimal_forbidden_supports
            .iter()
            .filter(|support| {
                support.support.iter().all(|variable| {
                    let assignment_variable = execution_plan
                        .and_then(|plan| plan.section_variable_aliases.as_ref())
                        .and_then(|aliases| aliases.get(variable))
                        .unwrap_or(variable);
                    assignment
                        .as_ref()
                        .unwrap()
                        .assigned
                        .get(assignment_variable)
                        == Some(&true)
                })
            })
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    let method_status = if assignment.is_none() {
        "section_assignment_absent"
    } else if forbidden_supports.is_empty() {
        "obstruction_generators_absent"
    } else if !violated_supports.is_empty() || assignment_status == "total" {
        "finite_section_pullback_computed"
    } else {
        "section_assignment_partial_undecidable"
    };
    let (verdict, zero, non_zero, reason) = if assignment.is_none() {
        (
            "not_computed".to_string(),
            false,
            false,
            "selected section witnessAssignment atom is absent; ag.section-factorization remains silent".to_string(),
        )
    } else if forbidden_supports.is_empty() {
        (
            "not_computed".to_string(),
            false,
            false,
            "selected raw support atoms are absent; ArchSig does not infer an empty I_Ob^U presentation".to_string(),
        )
    } else if !violated_supports.is_empty() {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "selected section active support contains a minimal forbidden support, so s^* I_Ob^U is nonzero".to_string(),
        )
    } else if assignment_status == "total" {
        (
            "measured_zero".to_string(),
            true,
            false,
            "selected total Boolean section avoids all minimal forbidden supports, so s^* I_Ob^U=0 under the finite profile".to_string(),
        )
    } else {
        (
            "unknown".to_string(),
            false,
            false,
            "partial witnessAssignment does not yet decide whether activeSupport contains a minimal forbidden support".to_string(),
        )
    };
    let cert_ref = matches!(verdict.as_str(), "measured_zero" | "measured_nonzero").then(|| {
        format!(
            "computedInvariants/section-factorization:{}",
            profile.profile_id
        )
    });

    Ok(SectionMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status: method_status.to_string(),
        cert_ref,
        reason,
        computed_invariants: vec![section_invariant_json(
            profile,
            method_status,
            &witness_variables,
            &forbidden_supports,
            &minimal_forbidden_supports,
            assignment.as_ref(),
            assignment_status,
            &active_support,
            &violated_supports,
        )],
        assumptions: section_assumptions(profile, method_status, &forbidden_supports),
    })
}

fn evaluate_boundary_residue_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<BoundaryResidueMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let witness_variables = boundary_residue_witness_variables(profile);
    let roles = boundary_residue_roles(normalized, &selected_contexts)?;
    let role_map = boundary_residue_role_map(&roles);
    let roles_complete = boundary_residue_roles_complete(&roles, &selected_contexts);
    let (columns, mismatch) = if roles_complete {
        (
            boundary_residue_columns(
                normalized,
                &selected_contexts,
                &witness_variables,
                &role_map,
            )?,
            boundary_residue_mismatch(
                normalized,
                &selected_contexts,
                &witness_variables,
                &role_map,
            )?,
        )
    } else {
        (Vec::new(), None)
    };
    let coefficient_is_f2 = profile.coefficient == "F2";
    let method_status = if !roles_complete {
        "boundary_classification_absent"
    } else if mismatch.is_none() {
        "boundary_mismatch_section_absent"
    } else if columns.is_empty() {
        "boundary_restriction_matrix_absent"
    } else if coefficient_is_f2 {
        "finite_mayer_vietoris_d0_computed"
    } else {
        "finite_mayer_vietoris_d0_obstruction_only"
    };
    let image_membership = if matches!(
        method_status,
        "finite_mayer_vietoris_d0_computed" | "finite_mayer_vietoris_d0_obstruction_only"
    ) {
        mismatch.as_ref().map(|mismatch| {
            let rows = boundary_residue_matrix_rows(&columns, witness_variables.len());
            vector_in_span_f2(&rows, &mismatch.vector)
        })
    } else {
        None
    };
    let (verdict, zero, non_zero, reason) = match method_status {
        "boundary_classification_absent" => (
            "not_computed".to_string(),
            false,
            false,
            "selected cover lacks core / feature / boundary patch classification atoms for ag.boundary-residue".to_string(),
        ),
        "boundary_mismatch_section_absent" => (
            "not_computed".to_string(),
            false,
            false,
            "selected boundary mismatch section is absent; boundary residue remains silent".to_string(),
        ),
        "boundary_restriction_matrix_absent" => (
            "not_computed".to_string(),
            false,
            false,
            "selected core/feature to boundary restriction matrix columns are absent".to_string(),
        ),
        _ if image_membership == Some(true) && coefficient_is_f2 => (
            "measured_zero".to_string(),
            true,
            false,
            "boundary mismatch section lies in im(d^0), so the selected F2 boundary residue is absorbed".to_string(),
        ),
        _ if image_membership == Some(true) => (
            "unknown".to_string(),
            false,
            false,
            "F2 parity boundary residue lies in im(d^0), but non-F2 coefficient mode only supports one-way obstruction statements".to_string(),
        ),
        _ => (
            "measured_nonzero".to_string(),
            false,
            true,
            if coefficient_is_f2 {
                "boundary mismatch section is outside im(d^0), so the selected F2 boundary residue produces a global H1 class".to_string()
            } else {
                "boundary mismatch section is outside im(d^0) after F2 parity projection, yielding a one-way obstruction statement under the non-F2 coefficient profile".to_string()
            },
        ),
    };
    let cert_ref = matches!(verdict.as_str(), "measured_zero" | "measured_nonzero")
        .then(|| format!("computedInvariants/boundary-residue:{}", profile.profile_id));

    Ok(BoundaryResidueMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status: method_status.to_string(),
        cert_ref,
        reason,
        computed_invariants: vec![boundary_residue_invariant_json(
            profile,
            method_status,
            &witness_variables,
            &roles,
            &columns,
            mismatch.as_ref(),
            image_membership,
        )],
        assumptions: boundary_residue_assumptions(profile, method_status),
    })
}

fn evaluate_law_conflict_tor_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
    laws: &[&crate::LawEquationV1],
    witness_variables: &[String],
) -> Result<TorMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let ambient = tor_common_ambient(normalized, &selected_contexts)?;
    let Some(ambient) = ambient else {
        return Ok(TorMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "no_common_ambient".to_string(),
            cert_ref: None,
            reason: "common ambient pair is not supplied; no LawConflict comparison is computed"
                .to_string(),
            computed_invariants: vec![json!({
                "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
                "evaluator": "ag.law-conflict-tor",
                "method": "finite-monomial-tor-taylor@1",
                "selectedCoverRef": profile.cover_ref,
                "status": "not_computed",
                "reason": "no_common_ambient"
            })],
            analytic_readings: Vec::new(),
            assumptions: tor_assumptions(profile, None, "violated", "checked"),
        });
    };

    let generators = tor_ideal_generators(normalized, &selected_contexts, laws, witness_variables)?;
    let law_order = ambient.law_pair.clone();
    let selected_laws = generators
        .iter()
        .map(|generator| generator.law.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let ambient_laws = law_order.iter().cloned().collect::<BTreeSet<_>>();
    if selected_laws.is_empty() {
        let law_ideals = law_order
            .iter()
            .map(|law| {
                json!({
                    "law": law,
                    "generators": []
                })
            })
            .collect::<Vec<_>>();
        return Ok(TorMeasurementV1 {
            verdict: "not_computed".to_string(),
            zero: false,
            non_zero: false,
            method_status: "law_support_observation_incomplete".to_string(),
            cert_ref: None,
            reason: "no declared law support was observed in the selected common ambient"
                .to_string(),
            computed_invariants: vec![json!({
                "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
                "evaluator": "ag.law-conflict-tor",
                "method": "finite-monomial-tor-taylor@1",
                "claimScope": "degree-1 square-free monomial Tor over the selected common ambient pair",
                "resolution": profile.resolution_selector,
                "resolutionSelectorEffective": true,
                "selectedCoverRef": profile.cover_ref,
                "witnessVariables": witness_variables,
                "commonAmbient": {
                    "ambientRef": ambient.ambient_ref.clone(),
                    "atomRef": ambient.atom_ref.clone(),
                    "lawPair": ambient.law_pair.clone(),
                    "sourceRefs": ambient.source_refs.clone()
                },
                "lawIdeals": law_ideals,
                "lawConflicts": [],
                "torByDegree": [{
                    "degree": 1,
                    "classCount": null,
                    "status": "not_computed",
                    "coefficient": "F2",
                    "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
                }],
                "proxyComparison": {
                    "previousMethod": "finite-degree1-shared-support-conflict@1",
                    "proxyClassCount": 0,
                    "taylorClassCount": null,
                    "comparison": "not_computed"
                },
                "boundaryNote": "Taylor Tor_1 is a field-coefficient F2 reading over the selected common ambient; higher Tor_i and flat base change stability are not concluded."
            })],
            analytic_readings: Vec::new(),
            assumptions: tor_assumptions(profile, Some(&ambient), "violated", "checked"),
        });
    }
    let outside_ambient = selected_laws
        .iter()
        .filter(|law| !ambient_laws.contains(*law))
        .cloned()
        .collect::<Vec<_>>();
    if !outside_ambient.is_empty() {
        return Err(format!(
            "ag.law-conflict-tor selected law generators outside common ambient pair: {}",
            outside_ambient.join(",")
        ));
    }
    if selected_laws.len() != 2
        || selected_laws.iter().cloned().collect::<BTreeSet<_>>() != ambient_laws
    {
        return Ok(tor_partial_observation_measurement(
            profile,
            witness_variables,
            &ambient,
            &format!(
                "not every declared law support was observed in the selected common ambient: expected {}, observed {}",
                law_order.join(","),
                selected_laws.join(",")
            ),
        ));
    }
    let proxy_conflicts =
        tor_shared_support_proxy_classes(&generators, &law_order[0], &law_order[1]);
    let has_non_square_free = generators.iter().any(|generator| !generator.square_free);
    let law_ideals = law_order
        .iter()
        .map(|law| {
            json!({
                "law": law,
                "generators": generators.iter()
                    .filter(|generator| &generator.law == law)
                    .map(|generator| json!({
                        "generatorId": generator.generator_id,
                        "support": generator.support,
                        "squareFree": generator.square_free,
                        "contextRefs": generator.context_refs,
                        "sourceRefs": generator.source_refs
                    }))
                    .collect::<Vec<_>>()
            })
        })
        .collect::<Vec<_>>();
    if has_non_square_free {
        return Ok(TorMeasurementV1 {
            verdict: "unmeasured".to_string(),
            zero: false,
            non_zero: false,
            method_status: "non_square_free_monomial".to_string(),
            cert_ref: Some(tor_certificate_ref(profile)),
            reason: "selected law ideal generator contains a non-square-free monomial; finite square-free Taylor regime is not measured".to_string(),
            computed_invariants: vec![json!({
                "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
                "evaluator": "ag.law-conflict-tor",
                "method": "finite-monomial-tor-taylor@1",
                "status": "unmeasured",
                "methodStatus": "non_square_free_monomial",
                "claimScope": "degree-1 square-free monomial Tor over the selected common ambient pair",
                "selectedCoverRef": profile.cover_ref,
                "resolutionSelector": profile.resolution_selector,
                "witnessVariables": witness_variables,
                "commonAmbient": {
                    "ambientRef": ambient.ambient_ref.clone(),
                    "atomRef": ambient.atom_ref.clone(),
                    "lawPair": ambient.law_pair.clone(),
                    "sourceRefs": ambient.source_refs.clone()
                },
                "lawIdeals": law_ideals,
                "lawConflicts": [],
                "torByDegree": [{
                    "degree": 1,
                    "classCount": Value::Null,
                    "coefficient": "F2",
                    "status": "unmeasured",
                    "reason": "non_square_free_monomial"
                }],
                "proxyComparison": {
                    "previousMethod": "finite-degree1-shared-support-conflict@1",
                    "proxyClassCount": proxy_conflicts.len(),
                    "taylorClassCount": Value::Null,
                    "comparison": "not_computed_outside_square_free_regime"
                },
                "boundaryNote": "Taylor Tor_1 is only measured for selected square-free monomial generators over F2; higher Tor_i and flat base change stability are not concluded."
            })],
            analytic_readings: Vec::new(),
            assumptions: tor_assumptions(profile, Some(&ambient), "checked", "violated"),
        });
    }

    let conflicts = tor_taylor_h1_classes(
        &generators,
        &law_order[0],
        &law_order[1],
        &witness_variables,
    );
    let has_conflict = !conflicts.is_empty();
    let conflict_json = conflicts
        .iter()
        .map(|conflict| {
            json!({
                "conflictId": conflict.conflict_id,
                "degree": conflict.degree,
                "support": conflict.support,
                "multidegree": conflict.multidegree,
                "sharedSupport": conflict.shared_support,
                "leftLaw": conflict.left_law,
                "leftGeneratorRef": conflict.left_generator_ref,
                "rightLaw": conflict.right_law,
                "rightGeneratorRef": conflict.right_generator_ref,
                "contextRefs": conflict.context_refs,
                "sourceRefs": conflict.source_refs
            })
        })
        .collect::<Vec<_>>();

    Ok(TorMeasurementV1 {
        verdict: if has_conflict {
            "measured_nonzero".to_string()
        } else {
            "measured_zero".to_string()
        },
        zero: !has_conflict,
        non_zero: has_conflict,
        method_status: "finite_monomial_tor_taylor_computed".to_string(),
        cert_ref: Some(tor_certificate_ref(profile)),
        reason: if has_conflict {
            "finite monomial Taylor resolution found degree-1 Tor classes under the supplied common ambient"
                .to_string()
        } else {
            "finite monomial Taylor resolution found no degree-1 Tor class under the supplied common ambient"
                .to_string()
        },
        computed_invariants: vec![json!({
                "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
                "evaluator": "ag.law-conflict-tor",
                "method": "finite-monomial-tor-taylor@1",
                "claimScope": "degree-1 square-free monomial Tor over the selected common ambient pair",
                "resolution": profile.resolution_selector,
                "resolutionSelectorEffective": true,
            "selectedCoverRef": profile.cover_ref,
            "witnessVariables": witness_variables,
                "commonAmbient": {
                    "ambientRef": ambient.ambient_ref.clone(),
                    "atomRef": ambient.atom_ref.clone(),
                    "lawPair": ambient.law_pair.clone(),
                    "sourceRefs": ambient.source_refs.clone()
                },
            "lawIdeals": law_ideals,
            "lawConflicts": conflict_json,
            "torByDegree": [{
                "degree": 1,
                "classCount": conflicts.len(),
                "coefficient": "F2",
                "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
            }],
            "proxyComparison": {
                "previousMethod": "finite-degree1-shared-support-conflict@1",
                "proxyClassCount": proxy_conflicts.len(),
                "taylorClassCount": conflicts.len(),
                "comparison": if conflicts.len() <= proxy_conflicts.len() { "taylor_not_above_proxy" } else { "taylor_above_proxy" }
            },
            "boundaryNote": "Taylor Tor_1 is a field-coefficient F2 reading over the selected common ambient; higher Tor_i and flat base change stability are not concluded.",
            "nonConclusions": [
                "This evaluator computes only degree-1 monomial Taylor Tor over the selected square-free finite regime.",
                "Higher Tor_i for i>=2 remain outside this structural verdict.",
                "Flat base change stability is a theorem-candidate reading and is not concluded by this structural verdict."
            ]
        })],
        analytic_readings: vec![hilbert_interference_reading(profile, &ambient, &conflicts)],
        assumptions: tor_assumptions(profile, Some(&ambient), "checked", "checked"),
    })
}

fn tor_partial_observation_measurement(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
    ambient: &TorCommonAmbientV1,
    reason: &str,
) -> TorMeasurementV1 {
    let law_ideals = ambient
        .law_pair
        .iter()
        .map(|law| json!({"law": law, "generators": []}))
        .collect::<Vec<_>>();
    TorMeasurementV1 {
        verdict: "not_computed".to_string(),
        zero: false,
        non_zero: false,
        method_status: "law_support_observation_incomplete".to_string(),
        cert_ref: None,
        reason: reason.to_string(),
        computed_invariants: vec![json!({
            "invariantId": format!("law-conflict-tor:{}", profile.profile_id),
            "evaluator": "ag.law-conflict-tor",
            "method": "finite-monomial-tor-taylor@1",
            "claimScope": "degree-1 square-free monomial Tor over the selected common ambient pair",
            "resolution": profile.resolution_selector,
            "resolutionSelectorEffective": true,
            "selectedCoverRef": profile.cover_ref,
            "witnessVariables": witness_variables,
            "commonAmbient": {
                "ambientRef": ambient.ambient_ref.clone(),
                "atomRef": ambient.atom_ref.clone(),
                "lawPair": ambient.law_pair.clone(),
                "sourceRefs": ambient.source_refs.clone()
            },
            "lawIdeals": law_ideals,
            "lawConflicts": [],
            "torByDegree": [{
                "degree": 1,
                "classCount": null,
                "status": "not_computed",
                "coefficient": "F2",
                "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
            }],
            "proxyComparison": {
                "previousMethod": "finite-degree1-shared-support-conflict@1",
                "proxyClassCount": 0,
                "taylorClassCount": null,
                "comparison": "not_computed"
            },
            "boundaryNote": "Taylor Tor_1 is a field-coefficient F2 reading over the selected common ambient; higher Tor_i and flat base change stability are not concluded."
        })],
        analytic_readings: Vec::new(),
        assumptions: tor_assumptions(profile, Some(ambient), "violated", "checked"),
    }
}

fn tor_certificate_ref(profile: &MeasurementProfileV1) -> String {
    format!("computedInvariants/law-conflict-tor:{}", profile.profile_id)
}

fn hilbert_interference_reading(
    profile: &MeasurementProfileV1,
    ambient: &TorCommonAmbientV1,
    conflicts: &[TorConflictClassV1],
) -> AgAnalyticReadingV1 {
    let mut by_degree = BTreeMap::<usize, usize>::new();
    for conflict in conflicts {
        *by_degree.entry(conflict.degree).or_default() += 1;
    }
    let series = by_degree
        .into_iter()
        .map(|(degree, coefficient)| {
            json!({
                "degree": degree,
                "coefficient": coefficient
            })
        })
        .collect::<Vec<_>>();

    AgAnalyticReadingV1 {
        reading_id: format!("analytic:hilbert-interference:{}", profile.profile_id),
        evaluator: "ag.law-conflict-tor".to_string(),
        value: json!({
            "readingKind": "hilbert-interference-series@1",
            "seriesSymbol": "Int_{U,V}(t)",
            "selectedCoverRef": profile.cover_ref.clone(),
            "lawPair": ambient.law_pair.clone(),
            "commonAmbientRef": ambient.ambient_ref.clone(),
            "regimeBoundary": "audit-only in the selected graded square-free monomial Taylor regime",
            "series": series,
            "sourceRefs": ambient.source_refs.clone(),
            "nonConclusion": "Hilbert interference is an audit reading only; it does not add or change structural verdicts"
        }),
        regime: Some("analytic-measurement".to_string()),
        structural_verdict_ref: None,
    }
}

fn principal_eigenvector_hotspots(matrix: &[Vec<f64>], cell_ids: &[String]) -> Vec<Value> {
    if matrix.is_empty() {
        return Vec::new();
    }
    let n = matrix.len();
    let mut vector = vec![1.0 / (n as f64).sqrt(); n];
    for _ in 0..32 {
        let mut next = vec![0.0; n];
        for (row_index, row) in matrix.iter().enumerate() {
            next[row_index] = row
                .iter()
                .zip(vector.iter())
                .map(|(entry, value)| entry.abs() * value)
                .sum::<f64>();
        }
        let norm = squared_norm(&next).sqrt();
        if norm <= 1.0e-12 {
            break;
        }
        for value in &mut next {
            *value /= norm;
        }
        vector = next;
    }
    let mut hotspots = cell_ids
        .iter()
        .zip(vector.iter())
        .map(|(cell, weight)| (cell.clone(), weight.abs()))
        .collect::<Vec<_>>();
    hotspots.sort_by(|left, right| {
        right
            .1
            .total_cmp(&left.1)
            .then_with(|| left.0.cmp(&right.0))
    });
    hotspots
        .into_iter()
        .map(|(cell, weight)| {
            json!({
                "cell": cell,
                "hotspotWeight": round_f64(weight)
            })
        })
        .collect()
}

fn evaluate_sheaf_laplacian_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<LaplacianMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let witness_variables = laplacian_witness_variables(profile);
    let cells = laplacian_cells(normalized, &selected_contexts, &witness_variables)?;
    let edges = laplacian_edges(normalized, &selected_contexts)?;
    let observed_cells = cells
        .iter()
        .map(|cell| cell.cell_id.clone())
        .collect::<BTreeSet<_>>();
    let missing_cells = witness_variables
        .iter()
        .filter(|cell| !observed_cells.contains(*cell))
        .cloned()
        .collect::<Vec<_>>();
    if cells.is_empty() || edges.is_empty() || !missing_cells.is_empty() {
        let reason = if missing_cells.is_empty() {
            "cellular_model_missing".to_string()
        } else {
            format!("cellular_model_missing:{}", missing_cells.join(","))
        };
        return Ok(LaplacianMeasurementV1 {
            verdict: "not_computed".to_string(),
            method_status: "cellular_model_missing".to_string(),
            cert_ref: None,
            reason: "selected cellular cochains or boundaries are missing; no Laplacian analytic reading is computed".to_string(),
            computed_invariants: vec![json!({
                "invariantId": format!("sheaf-laplacian:{}", profile.profile_id),
                "evaluator": "ag.sheaf-laplacian",
                "status": "not_computed",
                "reason": reason
            })],
            analytic_readings: Vec::new(),
            assumptions: laplacian_assumptions(profile, "violated"),
        });
    }

    let cell_ids = cells
        .iter()
        .map(|cell| cell.cell_id.clone())
        .collect::<Vec<_>>();
    let cell_index = cell_ids
        .iter()
        .enumerate()
        .map(|(index, cell)| (cell.clone(), index))
        .collect::<BTreeMap<_, _>>();
    for edge in &edges {
        if !cell_index.contains_key(&edge.source) || !cell_index.contains_key(&edge.target) {
            return Err(format!(
                "ag.sheaf-laplacian boundary {} references cells outside selected cochain family",
                edge.atom_ref
            ));
        }
    }
    let laplacian = graph_laplacian(&cell_ids, &cell_index, &edges);
    let cochain = cells.iter().map(|cell| cell.value).collect::<Vec<_>>();
    let components = graph_components(cell_ids.len(), &cell_index, &edges);
    let harmonic = harmonic_projection(&cochain, &components);
    let exact = vec![0.0; cochain.len()];
    let coexact = cochain
        .iter()
        .zip(harmonic.iter())
        .map(|(value, harmonic)| value - harmonic)
        .collect::<Vec<_>>();
    let harmonic_mass = squared_norm(&harmonic);
    let distance_to_flatness = squared_norm(&coexact);
    let eigenvalues = jacobi_eigenvalues_symmetric(laplacian.clone());
    let spectral_gap = eigenvalues
        .iter()
        .copied()
        .filter(|value| *value > 1.0e-9)
        .fold(None, |best: Option<f64>, value| {
            Some(best.map_or(value, |best| best.min(value)))
        })
        .unwrap_or(0.0);
    let curvature_transfer = laplacian
        .iter()
        .enumerate()
        .map(|(index, row)| {
            let value = row
                .iter()
                .zip(cochain.iter())
                .map(|(entry, cochain)| entry * cochain)
                .sum::<f64>();
            json!({
                "cell": cell_ids[index],
                "curvature": round_f64(value)
            })
        })
        .collect::<Vec<_>>();
    let curvature_hotspots = principal_eigenvector_hotspots(&laplacian, &cell_ids);
    let source_refs = cells
        .iter()
        .flat_map(|cell| cell.source_refs.iter())
        .chain(edges.iter().flat_map(|edge| edge.source_refs.iter()))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    let analytic_value = json!({
        "readingKind": "graph-laplacian-hodge-proxy@1",
        "modelScope": "finite graph Laplacian over selected cochain cells and boundary edges",
        "selectedCoverRef": profile.cover_ref,
        "cells": cell_ids.clone(),
        "cochain": rounded_vec(&cochain),
        "hodgeDecomposition": {
            "exact": rounded_vec(&exact),
            "harmonic": rounded_vec(&harmonic),
            "coexact": rounded_vec(&coexact)
        },
        "harmonicMass": round_f64(harmonic_mass),
        "distanceToFlatness": round_f64(distance_to_flatness),
        "spectralGap": round_f64(spectral_gap),
        "curvatureTransferSpectrum": curvature_transfer,
        "nonConclusion": "near-flat analytic values are not structural lawfulness verdicts"
    });

    Ok(LaplacianMeasurementV1 {
        verdict: "unknown".to_string(),
        method_status: "finite_laplacian_analytic_reading_computed".to_string(),
        cert_ref: None,
        reason: "finite Laplacian / Hodge values were computed as analytic readings; structural lawfulness is not concluded".to_string(),
        computed_invariants: vec![json!({
            "invariantId": format!("sheaf-laplacian:{}", profile.profile_id),
            "evaluator": "ag.sheaf-laplacian",
            "method": "finite-graph-laplacian@1",
            "claimScope": "graph Laplacian analytic proxy; not a full sheaf chain-complex Hodge theorem",
            "selectedCoverRef": profile.cover_ref,
            "cellRefs": cells.iter().map(|cell| json!({
                "cell": cell.cell_id,
                "cochainAtomRef": cell.atom_ref
            })).collect::<Vec<_>>(),
            "laplacianMatrix": rounded_matrix(&laplacian),
            "sourceRefs": source_refs
        })],
        analytic_readings: vec![
            AgAnalyticReadingV1 {
                reading_id: format!("analytic:sheaf-laplacian:{}", profile.profile_id),
                evaluator: "ag.sheaf-laplacian".to_string(),
                value: analytic_value,
                regime: Some("analytic-measurement".to_string()),
                structural_verdict_ref: None,
            },
            AgAnalyticReadingV1 {
                reading_id: format!("theorem-candidate:harmonic-debt:{}", profile.profile_id),
                evaluator: "ag.foundation".to_string(),
                value: json!({
                    "readingKind": "harmonic-debt-minimality-candidate@1",
                    "essentialRepairLowerBound": round_f64(distance_to_flatness.sqrt()),
                    "reason": "harmonic debt minimality remains theorem-candidate and cannot generate a structural verdict"
                }),
                regime: Some("theorem-candidate".to_string()),
                structural_verdict_ref: None,
            },
            AgAnalyticReadingV1 {
                reading_id: format!("theorem-candidate:curvature-hotspot:{}", profile.profile_id),
                evaluator: "ag.foundation".to_string(),
                value: json!({
                    "readingKind": "curvature-transfer-perron-hotspot@1",
                    "sourceProxyReadingKind": "graph-laplacian-hodge-proxy@1",
                    "modelScope": "finite graph Laplacian absolute-transfer principal eigenvector over selected cochain cells",
                    "hotspots": curvature_hotspots,
                    "nonConclusion": "Perron-Frobenius hotspot ranking is a theorem-candidate analytic reading, not a structural verdict"
                }),
                regime: Some("theorem-candidate".to_string()),
                structural_verdict_ref: None,
            },
        ],
        assumptions: laplacian_assumptions(profile, "checked"),
    })
}

fn evaluate_harmonic_debt_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<HarmonicDebtMeasurementV1, String> {
    let analytic = profile
        .analytic
        .as_ref()
        .and_then(Value::as_object)
        .ok_or_else(|| {
            format!(
                "ag.harmonic-debt requires MeasurementProfile analytic declaration for {}",
                profile.profile_id
            )
        })?;
    let inner_product = analytic
        .get("innerProduct")
        .and_then(Value::as_object)
        .ok_or_else(|| "ag.harmonic-debt analytic.innerProduct is required".to_string())?;
    if inner_product.get("kind").and_then(Value::as_str) != Some("diagonal") {
        return Err("ag.harmonic-debt analytic.innerProduct.kind must be diagonal".to_string());
    }
    let weights = inner_product
        .get("weights")
        .and_then(Value::as_array)
        .ok_or_else(|| "ag.harmonic-debt analytic.innerProduct.weights is required".to_string())?
        .iter()
        .map(|weight| {
            let value = weight
                .as_f64()
                .ok_or_else(|| "harmonic inner-product weights must be numeric".to_string())?;
            if value.is_finite() && value > 0.0 {
                Ok(value)
            } else {
                Err("harmonic inner-product weights must be finite and positive".to_string())
            }
        })
        .collect::<Result<Vec<_>, String>>()?;
    if weights.len() != laplacian_witness_variables(profile).len() {
        return Err(format!(
            "ag.harmonic-debt inner-product weights must match {} witness cells",
            laplacian_witness_variables(profile).len()
        ));
    }
    let laplacian = evaluate_sheaf_laplacian_v1(normalized, profile)?;
    let Some(proxy) = laplacian
        .analytic_readings
        .iter()
        .find(|reading| reading.evaluator == "ag.sheaf-laplacian")
    else {
        return Ok(HarmonicDebtMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("harmonic-debt:{}", profile.profile_id),
                "kind": "harmonic-debt",
                "evaluator": "ag.harmonic-debt",
                "status": "silence_by_design",
                "reason": "cellular_model_missing",
                "whatNext": "supply a validated cellular Laplacian model and witness before evaluating harmonic debt"
            })],
            analytic_readings: Vec::new(),
            assumptions: laplacian.assumptions,
        });
    };
    let harmonic = proxy
        .value
        .get("hodgeDecomposition")
        .and_then(|value| value.get("harmonic"))
        .and_then(Value::as_array)
        .ok_or_else(|| "ag.harmonic-debt requires harmonic decomposition output".to_string())?
        .iter()
        .map(|value| {
            value
                .as_f64()
                .ok_or_else(|| "harmonic values must be numeric".to_string())
        })
        .collect::<Result<Vec<_>, String>>()?;
    if harmonic.len() != weights.len() {
        return Err("harmonic decomposition and inner-product dimensions differ".to_string());
    }
    let harmonic_debt_norm = harmonic
        .iter()
        .zip(weights.iter())
        .map(|(value, weight)| weight * value * value)
        .sum::<f64>()
        .sqrt();
    let cost_model = if let Some(raw_cost_model) = analytic.get("costModel") {
        let model = raw_cost_model
            .as_object()
            .ok_or_else(|| "harmonic costModel must be an object".to_string())?;
        if model.get("kind").and_then(Value::as_str) != Some("lipschitz-harmonic-resolution") {
            return Err(
                "harmonic costModel.kind must be lipschitz-harmonic-resolution".to_string(),
            );
        }
        let lipschitz = model
            .get("lipschitzConstant")
            .and_then(Value::as_f64)
            .ok_or_else(|| "harmonic costModel.lipschitzConstant is required".to_string())?;
        let resolution = model
            .get("harmonicResolution")
            .and_then(Value::as_str)
            .filter(|resolution| !resolution.trim().is_empty())
            .ok_or_else(|| "harmonic costModel.harmonicResolution is required".to_string())?;
        if !lipschitz.is_finite() || lipschitz <= 0.0 {
            return Err(
                "harmonic costModel.lipschitzConstant must be finite and positive".to_string(),
            );
        }
        Some((lipschitz, resolution.to_string()))
    } else {
        None
    };
    let mut assumptions = laplacian.assumptions;
    let (lower_bound, lower_bound_status) = if let Some((lipschitz, resolution)) = cost_model {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/8.7".to_string(),
            assumption: format!("cost model is {lipschitz}-Lipschitz with {resolution}"),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
        (Some(harmonic_debt_norm / lipschitz), "cost_model_supplied")
    } else {
        (None, "cost_model_not_supplied")
    };
    let mut invariant = json!({
        "invariantId": format!("harmonic-debt:{}", profile.profile_id),
        "kind": "harmonic-debt",
        "evaluator": "ag.harmonic-debt",
        "schema": "archsig-measurement-packet/v0.5.4",
        "selectedCoverRef": profile.cover_ref,
        "harmonicDebtNorm": round_f64(harmonic_debt_norm),
        "essentialRepairLowerBound": lower_bound.map(round_f64),
        "lowerBoundStatus": lower_bound_status,
        "sourceProxyReading": proxy.reading_id,
        "nonConclusion": "harmonic debt is an analytic reading and does not establish lawfulness or synthesize a repair"
    });
    let mut reading = json!({
        "readingKind": "harmonic-debt@1",
        "selectedCoverRef": profile.cover_ref,
        "harmonicDebtNorm": round_f64(harmonic_debt_norm),
        "essentialRepairLowerBound": lower_bound.map(round_f64),
        "lowerBoundStatus": lower_bound_status,
        "sourceProxyReadingKind": "graph-laplacian-hodge-proxy@1",
        "certificate": lower_bound.is_some().then(|| "local adjustment cannot reduce repair cost below ||h(g)||/L under the supplied cost model"),
        "nonConclusion": "analytic harmonic debt is not a structural lawfulness verdict"
    });
    if lower_bound.is_none() {
        invariant["status"] = json!("silence_by_design");
        invariant["reason"] = json!("cost_model_not_supplied");
        invariant["whatNext"] = json!(HARMONIC_COST_MODEL_WHAT_NEXT);
        invariant
            .as_object_mut()
            .expect("harmonic debt invariant is object")
            .remove("essentialRepairLowerBound");
        reading
            .as_object_mut()
            .expect("harmonic debt reading is object")
            .remove("essentialRepairLowerBound");
        reading["whatNext"] = json!(HARMONIC_COST_MODEL_WHAT_NEXT);
    }
    Ok(HarmonicDebtMeasurementV1 {
        computed_invariants: vec![invariant],
        analytic_readings: vec![AgAnalyticReadingV1 {
            reading_id: format!("analytic:harmonic-debt:{}", profile.profile_id),
            evaluator: "ag.harmonic-debt".to_string(),
            value: reading,
            regime: Some("analytic-measurement".to_string()),
            structural_verdict_ref: None,
        }],
        assumptions,
    })
}

fn evaluate_period_stokes_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<PeriodMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let cycle_basis = period_witness_cycles(profile);
    let pairings = period_integrals(normalized, &selected_contexts, &cycle_basis)?;
    let d_omega = stokes_audit_values(
        normalized,
        &selected_contexts,
        "dOmegaIntegral",
        "ag.period-stokes d omega audit",
    )?;
    let boundary = stokes_audit_values(
        normalized,
        &selected_contexts,
        "boundaryPeriod",
        "ag.period-stokes boundary audit",
    )?;
    let observed_cycles = pairings
        .iter()
        .map(|pairing| pairing.cycle_id.clone())
        .collect::<BTreeSet<_>>();
    let missing_cycles = cycle_basis
        .iter()
        .filter(|cycle| !observed_cycles.contains(*cycle))
        .cloned()
        .collect::<Vec<_>>();
    if pairings.is_empty()
        || d_omega.is_empty()
        || boundary.is_empty()
        || !missing_cycles.is_empty()
    {
        let reason = if missing_cycles.is_empty() {
            "period_model_missing".to_string()
        } else {
            format!("period_model_missing:{}", missing_cycles.join(","))
        };
        return Ok(PeriodMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("period-stokes:{}", profile.profile_id),
                "evaluator": "ag.period-stokes",
                "status": "not_computed",
                "reason": reason
            })],
            analytic_readings: Vec::new(),
            assumptions: period_assumptions(profile, "violated"),
        });
    }

    let forms = pairings
        .iter()
        .map(|pairing| pairing.form_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let observed_pairings = pairings
        .iter()
        .map(|pairing| (pairing.form_id.clone(), pairing.cycle_id.clone()))
        .collect::<BTreeSet<_>>();
    let mut missing_pairings = Vec::new();
    for form in &forms {
        for cycle in &cycle_basis {
            if !observed_pairings.contains(&(form.clone(), cycle.clone())) {
                missing_pairings.push(format!("{form}/{cycle}"));
            }
        }
    }
    if !missing_pairings.is_empty() {
        return Ok(PeriodMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("period-stokes:{}", profile.profile_id),
                "evaluator": "ag.period-stokes",
                "status": "not_computed",
                "reason": format!("period_model_missing:{}", missing_pairings.join(","))
            })],
            analytic_readings: Vec::new(),
            assumptions: period_assumptions(profile, "violated"),
        });
    }
    let form_index = forms
        .iter()
        .enumerate()
        .map(|(index, form)| (form.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let cycle_index = cycle_basis
        .iter()
        .enumerate()
        .map(|(index, cycle)| (cycle.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut matrix = vec![vec![0.0; cycle_basis.len()]; forms.len()];
    for pairing in &pairings {
        matrix[form_index[&pairing.form_id]][cycle_index[&pairing.cycle_id]] = pairing.value;
    }
    let audit = stokes_audit_report(&d_omega, &boundary)?;
    let source_refs = pairings
        .iter()
        .flat_map(|pairing| pairing.source_refs.iter())
        .chain(d_omega.iter().flat_map(|entry| entry.source_refs.iter()))
        .chain(boundary.iter().flat_map(|entry| entry.source_refs.iter()))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    let analytic_value = json!({
        "readingKind": "strict-period-pairing@1",
        "selectedCoverRef": profile.cover_ref,
        "modelRelative": true,
        "forms": forms,
        "cycleBasis": cycle_basis,
        "periodPairingMatrix": rounded_matrix(&matrix),
        "stokesAudit": audit,
        "nonConclusion": "period pairing is a model-relative analytic reading and is not a structural lawfulness verdict"
    });

    Ok(PeriodMeasurementV1 {
        computed_invariants: vec![json!({
            "invariantId": format!("period-stokes:{}", profile.profile_id),
            "evaluator": "ag.period-stokes",
            "method": "finite-poset-period-stokes@1",
            "selectedCoverRef": profile.cover_ref,
            "pairingAtomRefs": pairings.iter().map(|pairing| json!({
                "form": pairing.form_id,
                "cycle": pairing.cycle_id,
                "atomRef": pairing.atom_ref
            })).collect::<Vec<_>>(),
            "periodPairingMatrix": rounded_matrix(&matrix),
            "stokesAudit": audit,
            "sourceRefs": source_refs
        })],
        analytic_readings: vec![AgAnalyticReadingV1 {
            reading_id: format!("analytic:period-stokes:{}", profile.profile_id),
            evaluator: "ag.period-stokes".to_string(),
            value: analytic_value,
            regime: Some("analytic-measurement".to_string()),
            structural_verdict_ref: None,
        }],
        assumptions: period_assumptions(profile, "checked"),
    })
}

fn evaluate_period_stokes_audit_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<PeriodAuditMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let cycle_basis = period_audit_witness_cycles(profile);
    let pairings = period_integrals(normalized, &selected_contexts, &cycle_basis)?;
    let d_omega = stokes_audit_values(
        normalized,
        &selected_contexts,
        "dOmegaIntegral",
        "ag.period-stokes-audit d omega audit",
    )?;
    let boundary = stokes_audit_values(
        normalized,
        &selected_contexts,
        "boundaryPeriod",
        "ag.period-stokes-audit boundary audit",
    )?;

    let audit = fixed_coefficient_stokes_audit_report(&d_omega, &boundary, &profile.coefficient);
    let (forms, matrix, analytic_reading) =
        period_pairing_analytic_reading(profile, &cycle_basis, &pairings, Some(audit.clone()));
    let source_refs = pairings
        .iter()
        .flat_map(|pairing| pairing.source_refs.iter())
        .chain(d_omega.iter().flat_map(|entry| entry.source_refs.iter()))
        .chain(boundary.iter().flat_map(|entry| entry.source_refs.iter()))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let computed_invariant = json!({
        "invariantId": format!("period-stokes-audit:{}", profile.profile_id),
        "evaluator": "ag.period-stokes-audit",
        "method": "fixed-coefficient-stokes-audit@1",
        "selectedCoverRef": profile.cover_ref,
        "coefficient": profile.coefficient,
        "forms": forms,
        "cycleBasis": cycle_basis,
        "periodPairingMatrix": rounded_matrix(&matrix),
        "stokesAudit": audit,
        "claimScope": "supplied independent dOmega/boundary accounting values under the selected fixed coefficient reading",
        "analyticReadingRef": analytic_reading.reading_id,
        "sourceRefs": source_refs
    });

    let status = computed_invariant["stokesAudit"]["status"]
        .as_str()
        .unwrap_or("unknown");
    let (verdict, zero, non_zero, method_status, cert_ref, reason, assumption_status) =
        match status {
            "checked" => (
                "measured_zero".to_string(),
                true,
                false,
                "fixed_coefficient_stokes_audit_computed".to_string(),
                Some(format!(
                    "computedInvariants/period-stokes-audit:{}",
                    profile.profile_id
                )),
                "all supplied Stokes audit residuals are zero under the selected fixed coefficient reading".to_string(),
                "checked",
            ),
            "residual_nonzero" => (
                "measured_nonzero".to_string(),
                false,
                true,
                "fixed_coefficient_stokes_audit_computed".to_string(),
                Some(format!(
                    "computedInvariants/period-stokes-audit:{}",
                    profile.profile_id
                )),
                "at least one supplied Stokes audit residual is nonzero under the selected fixed coefficient reading".to_string(),
                "checked",
            ),
            "unknown" => (
                "unknown".to_string(),
                false,
                false,
                "strict_coefficient_unresolved".to_string(),
                None,
                computed_invariant["stokesAudit"]["reason"]
                    .as_str()
                    .unwrap_or("strict coefficient Stokes audit is unresolved")
                    .to_string(),
                "assumed",
            ),
            _ => (
                "unknown".to_string(),
                false,
                false,
                "period_audit_model_missing".to_string(),
                None,
                computed_invariant["stokesAudit"]["reason"]
                    .as_str()
                    .unwrap_or("period Stokes audit model is incomplete")
                    .to_string(),
                "violated",
            ),
        };

    Ok(PeriodAuditMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status,
        cert_ref,
        reason,
        computed_invariants: vec![computed_invariant],
        analytic_readings: vec![analytic_reading],
        assumptions: period_audit_assumptions(profile, assumption_status),
    })
}

fn period_pairing_analytic_reading(
    profile: &MeasurementProfileV1,
    cycle_basis: &[String],
    pairings: &[PeriodIntegralV1],
    stokes_audit: Option<Value>,
) -> (Vec<String>, Vec<Vec<f64>>, AgAnalyticReadingV1) {
    let forms = pairings
        .iter()
        .map(|pairing| pairing.form_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let form_index = forms
        .iter()
        .enumerate()
        .map(|(index, form)| (form.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let cycle_index = cycle_basis
        .iter()
        .enumerate()
        .map(|(index, cycle)| (cycle.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut matrix = vec![vec![0.0; cycle_basis.len()]; forms.len()];
    for pairing in pairings {
        if let (Some(form), Some(cycle)) = (
            form_index.get(&pairing.form_id),
            cycle_index.get(&pairing.cycle_id),
        ) {
            matrix[*form][*cycle] = pairing.value;
        }
    }
    let analytic_value = json!({
        "readingKind": "strict-period-pairing@1",
        "selectedCoverRef": profile.cover_ref,
        "modelRelative": true,
        "forms": forms,
        "cycleBasis": cycle_basis,
        "periodPairingMatrix": rounded_matrix(&matrix),
        "stokesAudit": stokes_audit,
        "nonConclusion": "period pairing is a model-relative analytic reading and is not a structural lawfulness verdict"
    });
    (
        form_index.keys().cloned().collect(),
        matrix,
        AgAnalyticReadingV1 {
            reading_id: format!("analytic:period-stokes:{}", profile.profile_id),
            evaluator: "ag.period-stokes".to_string(),
            value: analytic_value,
            regime: Some("analytic-measurement".to_string()),
            structural_verdict_ref: None,
        },
    )
}

fn evaluate_support_transfer_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<TransferMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let targets = transfer_witness_targets(profile);
    let repair_paths = transfer_repair_paths(normalized, &selected_contexts, &targets)?;
    let pairings = transfer_pairings(normalized, &selected_contexts, &targets)?;
    let ground_costs = transfer_ground_costs(normalized, &selected_contexts, &targets)?;
    let observed_targets = pairings
        .iter()
        .map(|pairing| pairing.target_id.clone())
        .collect::<BTreeSet<_>>();
    let missing_targets = targets
        .iter()
        .filter(|target| !observed_targets.contains(*target))
        .cloned()
        .collect::<Vec<_>>();
    let cost_targets = ground_costs
        .iter()
        .map(|cost| cost.target_id.clone())
        .collect::<BTreeSet<_>>();
    let missing_costs = targets
        .iter()
        .filter(|target| !cost_targets.contains(*target))
        .cloned()
        .collect::<Vec<_>>();
    if repair_paths.is_empty()
        || pairings.is_empty()
        || ground_costs.is_empty()
        || !missing_targets.is_empty()
        || !missing_costs.is_empty()
    {
        let mut reasons = Vec::new();
        if repair_paths.is_empty() || pairings.is_empty() || ground_costs.is_empty() {
            reasons.push("transfer_model_missing".to_string());
        }
        if !missing_targets.is_empty() {
            reasons.push(format!("missing_pairings:{}", missing_targets.join(",")));
        }
        if !missing_costs.is_empty() {
            reasons.push(format!("missing_ground_costs:{}", missing_costs.join(",")));
        }
        return Ok(TransferMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("support-transfer:{}", profile.profile_id),
                "evaluator": "ag.support-transfer",
                "status": "not_computed",
                "reason": reasons.join(";")
            })],
            analytic_readings: Vec::new(),
            assumptions: transfer_assumptions(profile, "violated"),
        });
    }

    let paths = repair_paths
        .iter()
        .map(|path| path.path_id.clone())
        .collect::<Vec<_>>();
    let path_set = paths.iter().cloned().collect::<BTreeSet<_>>();
    let outside_paths = pairings
        .iter()
        .filter(|pairing| !path_set.contains(&pairing.path_id))
        .map(|pairing| pairing.path_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if !outside_paths.is_empty() {
        return Err(format!(
            "ag.support-transfer transfer pairings reference paths outside selected repair path model: {}",
            outside_paths.join(",")
        ));
    }
    let observed_pairings = pairings
        .iter()
        .map(|pairing| (pairing.path_id.clone(), pairing.target_id.clone()))
        .collect::<BTreeSet<_>>();
    let support_by_path = repair_paths
        .iter()
        .map(|path| {
            (
                path.path_id.clone(),
                path.support_targets
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let support_disjoint_pairings = pairings
        .iter()
        .filter(|pairing| {
            support_by_path
                .get(&pairing.path_id)
                .is_none_or(|support| !support.contains(&pairing.target_id))
        })
        .map(|pairing| format!("{}/{}", pairing.path_id, pairing.target_id))
        .collect::<Vec<_>>();
    if !support_disjoint_pairings.is_empty() {
        return Ok(TransferMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("support-transfer:{}", profile.profile_id),
                "evaluator": "ag.support-transfer",
                "status": "not_computed",
                "reason": format!("support_localized_premise_violated:{}", support_disjoint_pairings.join(",")),
                "supportLocalizedPremise": {
                    "status": "violated",
                    "repairPathSupports": repair_paths.iter().map(|path| json!({
                        "repairPath": path.path_id.clone(),
                        "supportTargets": path.support_targets.clone(),
                        "atomRef": path.atom_ref.clone()
                    })).collect::<Vec<_>>(),
                    "blockedPairings": support_disjoint_pairings,
                    "nonConclusion": "no transfer matrix is filled for pairings outside the supplied repair-path support"
                }
            })],
            analytic_readings: Vec::new(),
            assumptions: transfer_assumptions(profile, "violated"),
        });
    }
    let mut missing_pairings = Vec::new();
    for path in &paths {
        for target in &targets {
            if !observed_pairings.contains(&(path.clone(), target.clone())) {
                missing_pairings.push(format!("{path}/{target}"));
            }
        }
    }
    if !missing_pairings.is_empty() {
        return Ok(TransferMeasurementV1 {
            computed_invariants: vec![json!({
                "invariantId": format!("support-transfer:{}", profile.profile_id),
                "evaluator": "ag.support-transfer",
                "status": "not_computed",
                "reason": format!("transfer_model_missing:{}", missing_pairings.join(","))
            })],
            analytic_readings: Vec::new(),
            assumptions: transfer_assumptions(profile, "violated"),
        });
    }

    let path_index = paths
        .iter()
        .enumerate()
        .map(|(index, path)| (path.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let target_index = targets
        .iter()
        .enumerate()
        .map(|(index, target)| (target.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut matrix = vec![vec![0.0; targets.len()]; paths.len()];
    for pairing in &pairings {
        matrix[path_index[&pairing.path_id]][target_index[&pairing.target_id]] = pairing.value;
    }
    let cost_by_target = ground_costs
        .iter()
        .map(|cost| (cost.target_id.clone(), cost.cost))
        .collect::<BTreeMap<_, _>>();
    let transfer_residue = matrix
        .iter()
        .flatten()
        .map(|value| value * value)
        .sum::<f64>()
        .sqrt();
    let wasserstein_cost = pairings
        .iter()
        .map(|pairing| pairing.value.abs() * cost_by_target[&pairing.target_id])
        .sum::<f64>();
    let source_refs = pairings
        .iter()
        .flat_map(|pairing| pairing.source_refs.iter())
        .chain(repair_paths.iter().flat_map(|path| path.source_refs.iter()))
        .chain(ground_costs.iter().flat_map(|cost| cost.source_refs.iter()))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let support_localized_premise = json!({
        "status": "checked",
        "repairPathCount": repair_paths.len(),
        "targetCount": targets.len(),
        "observedPairingCount": pairings.len(),
        "requiredPairingCount": repair_paths.len() * targets.len(),
        "repairPathSupports": repair_paths.iter().map(|path| json!({
            "repairPath": path.path_id.clone(),
            "supportTargets": path.support_targets.clone(),
            "atomRef": path.atom_ref.clone()
        })).collect::<Vec<_>>(),
        "matrixCompletion": "only supplied repairPath x target support pairings are admitted; any missing pairing blocks computation",
        "nonConclusion": "no unconditional transfer matrix is inferred for support-disjoint or unobserved paths"
    });

    let analytic_value = json!({
        "readingKind": "support-localized-transfer@1",
        "selectedCoverRef": profile.cover_ref,
        "modelRelative": true,
        "supportLocalizedPremise": support_localized_premise.clone(),
        "repairPaths": paths,
        "transferTargets": targets,
        "transferMeasurementPairing": rounded_matrix(&matrix),
        "transferResidue": round_f64(transfer_residue),
        "wassersteinTransferCost": round_f64(wasserstein_cost),
        "groundCosts": ground_costs.iter().map(|cost| json!({
            "target": cost.target_id,
            "cost": round_f64(cost.cost),
            "atomRef": cost.atom_ref
        })).collect::<Vec<_>>(),
        "nonConclusion": "transfer readings do not prove absence of side effects or global repair safety"
    });

    Ok(TransferMeasurementV1 {
        computed_invariants: vec![json!({
            "invariantId": format!("support-transfer:{}", profile.profile_id),
            "evaluator": "ag.support-transfer",
            "method": "finite-support-localized-transfer@1",
            "selectedCoverRef": profile.cover_ref,
            "repairPathAtomRefs": repair_paths.iter().map(|path| json!({
                "repairPath": path.path_id,
                "atomRef": path.atom_ref
            })).collect::<Vec<_>>(),
            "pairingAtomRefs": pairings.iter().map(|pairing| json!({
                "repairPath": pairing.path_id,
                "target": pairing.target_id,
                "atomRef": pairing.atom_ref
            })).collect::<Vec<_>>(),
            "transferMeasurementPairing": rounded_matrix(&matrix),
            "transferResidue": round_f64(transfer_residue),
            "wassersteinTransferCost": round_f64(wasserstein_cost),
            "supportLocalizedPremise": support_localized_premise,
            "sourceRefs": source_refs
        })],
        analytic_readings: vec![
            AgAnalyticReadingV1 {
                reading_id: format!("analytic:support-transfer:{}", profile.profile_id),
                evaluator: "ag.support-transfer".to_string(),
                value: analytic_value,
                regime: Some("analytic-measurement".to_string()),
                structural_verdict_ref: None,
            },
            AgAnalyticReadingV1 {
                reading_id: format!(
                    "theorem-candidate:transfer-lower-bound:{}",
                    profile.profile_id
                ),
                evaluator: "ag.foundation".to_string(),
                value: json!({
                    "readingKind": "transfer-lower-bound-candidate@1",
                    "transferLowerBound": round_f64(wasserstein_cost),
                    "reason": "transfer lower bound remains theorem-candidate and cannot generate a structural verdict"
                }),
                regime: Some("theorem-candidate".to_string()),
                structural_verdict_ref: None,
            },
        ],
        assumptions: transfer_assumptions(profile, "checked"),
    })
}
