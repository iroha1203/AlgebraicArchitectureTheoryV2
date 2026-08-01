#[derive(Debug, Clone)]
struct CechMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    reason: String,
    cert_ref: Option<String>,
    computed_invariants: Vec<Value>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct CechEdgeV1 {
    edge_id: String,
    source_context: String,
    target_context: String,
    value: u8,
    support_atom_refs: Vec<String>,
    // true only when the edge value comes from recorded observations: an
    // explicit cocycleValue atom, or sectionValue atoms on both endpoints.
    observed: bool,
}

fn evaluate_cech_obstruction_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> CechMeasurementV1 {
    let selected_contexts = selected_cover_contexts(normalized, profile);
    let edges = cech_edges(normalized, &selected_contexts);
    let cover_nerve_projection =
        cover_nerve_projection_v1(normalized, &selected_contexts, &edges, &profile.cover_ref);
    let cover_nerve_face_count = cover_nerve_projection["faces"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let component_count = graph_component_count(&selected_contexts, &edges);
    let h0_dimension = component_count;
    let h1_dimension = edges
        .len()
        .saturating_add(component_count)
        .saturating_sub(selected_contexts.len());
    let empty_selected_scope = selected_contexts.is_empty() || edges.is_empty();
    let nerve_is_forest = !empty_selected_scope
        && edges.len().saturating_add(component_count) == selected_contexts.len();
    let has_triple_overlap_faces = cover_nerve_face_count > 0;
    let restriction_surjectivity_witnesses =
        restriction_surjectivity_witnesses_v1(normalized, &edges);
    let selected_restriction_edges = edges
        .iter()
        .map(|edge| edge.edge_id.as_str())
        .collect::<BTreeSet<_>>();
    let witnessed_restriction_edges = restriction_surjectivity_witnesses
        .iter()
        .filter_map(|witness| witness["edgeRef"].as_str())
        .collect::<BTreeSet<_>>();
    let restriction_surjectivity_checked = !empty_selected_scope
        && !edges.is_empty()
        && witnessed_restriction_edges == selected_restriction_edges;
    let cover_shape_excludes_gluing_obstruction =
        nerve_is_forest && !has_triple_overlap_faces && restriction_surjectivity_checked;
    let observed_edges = edges
        .iter()
        .filter(|edge| edge.observed)
        .cloned()
        .collect::<Vec<_>>();
    let unobserved_edge_refs = edges
        .iter()
        .filter(|edge| !edge.observed)
        .map(|edge| edge.edge_id.clone())
        .collect::<Vec<_>>();
    // The measured cochain is restricted to observed edges: an unobserved edge
    // carries no section evidence, so it must not enter the cocycle as a zero.
    // Shape-level facts (nerve, H1 capacity, forest exclusion) stay on the full
    // selected 1-skeleton because they do not depend on section observations.
    let sections_not_observed = !empty_selected_scope
        && observed_edges.is_empty()
        && !cover_shape_excludes_gluing_obstruction;
    let h1_class_nonzero = !empty_selected_scope
        && !sections_not_observed
        && !edge_cochain_is_coboundary(&selected_contexts, &observed_edges);
    let topological_debt_capacity = topological_debt_capacity_invariant_v1(
        profile,
        &selected_contexts,
        &edges,
        &cover_nerve_projection,
        h1_dimension,
        h1_class_nonzero,
        empty_selected_scope,
    );
    let representative = edges
        .iter()
        .filter(|edge| edge.value == 1)
        .map(|edge| {
            json!({
                "edge": edge.edge_id,
                "sourceContext": edge.source_context,
                "targetContext": edge.target_context,
                "value": 1,
                "supportAtomRefs": edge.support_atom_refs
            })
        })
        .collect::<Vec<_>>();
    let mismatch_support_refs = edges
        .iter()
        .flat_map(|edge| edge.support_atom_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let mut assumptions = vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/B.8.2".to_string(),
            assumption: "F2 finite coefficient field".to_string(),
            status: "checked".to_string(),
            checked_by: Some(format!(
                "measurement-profile:{}.coefficient={}",
                profile.profile_id, profile.coefficient
            )),
            assumed_by: None,
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/B.8.2".to_string(),
            assumption: "cover-relative Cech reading".to_string(),
            status: "checked".to_string(),
            checked_by: Some(format!(
                "measurement-profile:{}.coverRef",
                profile.profile_id
            )),
            assumed_by: None,
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/B.8.2".to_string(),
            assumption: "Leray / acyclicity comparison to sheaf cohomology".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/12.3".to_string(),
            assumption: "constant coefficient nerve b1 comparison".to_string(),
            status: "checked".to_string(),
            checked_by: Some(format!(
                "measurement-profile:{}.coefficient={}",
                profile.profile_id, profile.coefficient
            )),
            assumed_by: None,
        },
    ];
    assumptions.extend(cech_effectivity_assumptions_v1(
        profile,
        nerve_is_forest,
        has_triple_overlap_faces,
        restriction_surjectivity_checked,
    ));
    if empty_selected_scope {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/B.8.2-empty-selected-scope".to_string(),
            assumption: "U-adequate cover selects a non-empty Cech 1-skeleton".to_string(),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
    }
    if sections_not_observed {
        assumptions.push(AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/B.8.2-sections-not-observed".to_string(),
            assumption: "section observations cover at least one selected Cech edge".to_string(),
            status: "violated".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        });
    }

    let (verdict, zero, non_zero, method_status, reason) = if empty_selected_scope {
        (
            "not_computed".to_string(),
            false,
            false,
            "empty_selected_scope".to_string(),
            "empty_selected_scope: selected cover has no non-empty Cech 1-skeleton for ag.cech-obstruction".to_string(),
        )
    } else if sections_not_observed {
        (
            "not_computed".to_string(),
            false,
            false,
            "sections_not_observed".to_string(),
            "sections_not_observed: no sectionValue or cocycleValue observation covers any selected Cech edge; supply section observations on both endpoint contexts of a selected edge (or an explicit cocycleValue for the edge) before the H1 class can be measured".to_string(),
        )
    } else if h1_class_nonzero {
        (
            "measured_nonzero".to_string(),
            false,
            true,
            "finite_f2_cech_computed".to_string(),
            "finite F2 Cech 1-cocycle is not a coboundary on the selected cover".to_string(),
        )
    } else {
        (
            "measured_zero".to_string(),
            true,
            false,
            "finite_f2_cech_computed".to_string(),
            "finite F2 Cech 1-cocycle is zero or a coboundary on the selected cover".to_string(),
        )
    };
    let cert_ref = if empty_selected_scope || sections_not_observed {
        None
    } else {
        Some(format!(
            "computedInvariants/cech-cohomology:{}",
            profile.profile_id
        ))
    };

    CechMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status,
        reason,
        cert_ref,
        computed_invariants: vec![
            json!({
                "invariantId": format!("cech-cohomology:{}", profile.profile_id),
                "evaluator": "ag.cech-obstruction",
                "method": "finite-f2-incidence-graph-cochain@1",
                "status": if empty_selected_scope || sections_not_observed {
                    "not_computed"
                } else {
                    "computed"
                },
                "methodStatus": if empty_selected_scope {
                    "empty_selected_scope"
                } else if sections_not_observed {
                    "sections_not_observed"
                } else {
                    "finite_f2_cech_computed"
                },
                "reason": if empty_selected_scope {
                    "empty_selected_scope: selected cover has no non-empty Cech 1-skeleton for ag.cech-obstruction"
                } else if sections_not_observed {
                    "sections_not_observed: no sectionValue or cocycleValue observation covers any selected Cech edge"
                } else {
                    "selected cover has a non-empty Cech 1-skeleton for ag.cech-obstruction"
                },
                "observedEdgeCount": observed_edges.len(),
                "unobservedEdgeRefs": unobserved_edge_refs,
                "claimScope": "selected-cover 1-skeleton Cech cochain calculation",
                "selectedCoverRef": profile.cover_ref,
                "coefficient": profile.coefficient,
                "contextCount": selected_contexts.len(),
                "restrictionEdgeCount": edges.len(),
                "coverNerveProjection": cover_nerve_projection,
                "rankD0": selected_contexts.len().saturating_sub(component_count),
                "dimensions": {
                    "H0": h0_dimension,
                    "H1": h1_dimension
                },
                "selectedH2": {
                    "dimension": if empty_selected_scope || cover_nerve_face_count > 0 {
                        Value::Null
                    } else {
                        json!(0)
                    },
                    "status": if empty_selected_scope {
                        "not_computed"
                    } else if cover_nerve_face_count == 0 {
                        "computed_for_selected_1_skeleton"
                    } else {
                        "not_measured_for_triple_overlap_faces"
                    },
                    "reason": if empty_selected_scope {
                        "empty_selected_scope: selected cover has no non-empty Cech 1-skeleton for ag.cech-obstruction"
                    } else if cover_nerve_face_count == 0 {
                        "no selected 2-simplices are present in the finite incidence graph complex"
                    } else {
                        "triple-overlap faces are projected for viewer geometry only; H2 coherence remains outside this measurement"
                    }
                },
                "observedCocycle": {
                    "classNonzero": h1_class_nonzero,
                    "representative": representative,
                    "mismatchSupportRefs": mismatch_support_refs
                },
                "classSupport": {
                    "kind": "selected-cover-edge-support",
                    "edgeRefs": edges.iter()
                        .filter(|edge| edge.value == 1)
                        .map(|edge| edge.edge_id.clone())
                        .collect::<Vec<_>>(),
                    "supportAtomRefs": mismatch_support_refs
                },
                "nerveShape": {
                    "b1": if empty_selected_scope {
                        Value::Null
                    } else {
                        json!(nerve_complex_b1_f2(&selected_contexts, &edges, &cover_nerve_projection))
                    },
                    "oneSkeletonB1": if empty_selected_scope {
                        Value::Null
                    } else {
                        json!(h1_dimension)
                    },
                    "capacityLowerBound": topological_debt_capacity["capacityLowerBound"].clone(),
                    "isForest": if empty_selected_scope {
                        Value::Null
                    } else {
                        json!(nerve_is_forest)
                    },
                    "eulerCharacteristic": topological_debt_capacity["eulerCharacteristic"].clone()
                },
                "theorem12_4Discharge": {
                    "theoremRef": "part4/12.4",
                    "isForest": discharged_check_json(nerve_is_forest, "selected-cover graph cycle rank is zero"),
                    "tripleOverlapsEmpty": discharged_check_json(!has_triple_overlap_faces, "selected cover has no projected triple-overlap faces"),
                    "restrictionMapsSurjective": discharged_check_json(restriction_surjectivity_checked, "explicit restrictionSurjectivityWitness atoms cover every selected restriction edge"),
                    "restrictionSurjectivityWitnesses": restriction_surjectivity_witnesses,
                    "coverShapeExcludesGluingObstruction": cover_shape_excludes_gluing_obstruction,
                    "conclusionCode": if cover_shape_excludes_gluing_obstruction {
                        Value::String(ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION.to_string())
                    } else {
                        Value::Null
                    }
                },
                "boundaryNote": "COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION is relative to the selected abelian coefficient sheaf; non-abelian torsor, stacky descent, and gerbe obstructions are not excluded."
            }),
            topological_debt_capacity,
        ],
        assumptions,
    }
}

fn topological_debt_capacity_invariant_v1(
    profile: &MeasurementProfileV1,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    cover_nerve_projection: &Value,
    one_skeleton_b1: usize,
    h1_class_nonzero: bool,
    empty_selected_scope: bool,
) -> Value {
    let dim_c0 = selected_contexts.len();
    let dim_c1 = edges.len();
    let dim_c2 = cover_nerve_projection["faces"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let raw_capacity = dim_c1 as isize - dim_c0 as isize - dim_c2 as isize;
    let capacity_lower_bound = raw_capacity.max(0) as usize;
    let euler_characteristic = dim_c0 as isize - dim_c1 as isize + dim_c2 as isize;
    let nerve_complex_b1 = nerve_complex_b1_f2(selected_contexts, edges, cover_nerve_projection);
    json!({
        "invariantId": format!("topological-debt-capacity:{}", profile.profile_id),
        "evaluator": "ag.cech-obstruction",
        "method": "finite-f2-rank-nullity-nerve-capacity@1",
        "status": if empty_selected_scope {
            "not_computed"
        } else {
            "computed"
        },
        "methodStatus": if empty_selected_scope {
            "empty_selected_scope"
        } else {
            "finite_f2_nerve_capacity_computed"
        },
        "selectedCoverRef": profile.cover_ref,
        "coefficient": profile.coefficient,
        "dimensions": {
            "dimC0": dim_c0,
            "dimC1": dim_c1,
            "dimC2": dim_c2
        },
        "capacityLowerBound": if empty_selected_scope {
            Value::Null
        } else {
            json!(capacity_lower_bound)
        },
        "capacityFormula": "max(0, dimC1 - dimC0 - dimC2)",
        "eulerCharacteristic": if empty_selected_scope {
            Value::Null
        } else {
            json!(euler_characteristic)
        },
        "eulerFormula": "dimC0 - dimC1 + dimC2",
        "b1NerveReading": {
            "oneSkeletonB1": if empty_selected_scope {
                Value::Null
            } else {
                json!(one_skeleton_b1)
            },
            "nerveComplexB1": if empty_selected_scope {
                Value::Null
            } else {
                json!(nerve_complex_b1)
            },
            "oneSkeletonMethod": "graph-cycle-rank@1",
            "nerveComplexMethod": "finite-f2-simplicial-homology-with-selected-2-faces@1",
            "distinction": "oneSkeletonB1 counts graph cycles before selected triple-overlap faces are quotiented; nerveComplexB1 includes those faces and may be smaller.",
            "nonClaim": "capacityLowerBound and b1NerveReading are capacity/accounting readings, not new structural verdicts and not concrete H1 class existence claims."
        },
        "measuredCechVerdictEcho": {
            "evaluator": "ag.cech-obstruction",
            "certRef": if empty_selected_scope {
                Value::Null
            } else {
                json!(format!("computedInvariants/cech-cohomology:{}", profile.profile_id))
            },
            "h1ClassNonzero": h1_class_nonzero,
            "note": "This is an echo of the separate Cech structural verdict, not a capacity-derived class claim."
        },
        "boundaryNote": "Part IV principle 11.3 is referenced only as the Cohomological Non-Claim boundary; this row does not import any Part VII numbering or create a viewer verdict.",
        "structuralVerdictRef": Value::Null
    })
}

fn nerve_complex_b1_f2(
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    cover_nerve_projection: &Value,
) -> usize {
    let mut simplices = selected_contexts
        .iter()
        .map(|context| vec![context.clone()])
        .collect::<Vec<_>>();
    simplices.extend(
        edges
            .iter()
            .map(|edge| sorted_simplex([edge.source_context.clone(), edge.target_context.clone()])),
    );
    if let Some(faces) = cover_nerve_projection["faces"].as_array() {
        for face in faces {
            let contexts = face["contextRefs"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|value| value.as_str().map(ToOwned::to_owned))
                .collect::<Vec<_>>();
            if contexts.len() < 3 {
                continue;
            }
            let edge_refs = face["edgeRefs"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|value| value.as_str())
                .collect::<BTreeSet<_>>();
            if edge_refs.len() == 3 {
                simplices.push(sorted_simplex(contexts));
            }
        }
    }
    simplices.sort();
    simplices.dedup();
    reduced_simplicial_homology_f2(&simplices)
        .into_iter()
        .find(|row| row["degree"] == 1)
        .and_then(|row| row["dimension"].as_u64())
        .unwrap_or(0) as usize
}

fn sorted_simplex(items: impl IntoIterator<Item = String>) -> Vec<String> {
    let mut simplex = items.into_iter().collect::<Vec<_>>();
    simplex.sort();
    simplex.dedup();
    simplex
}

fn cech_effectivity_assumptions_v1(
    profile: &MeasurementProfileV1,
    nerve_is_forest: bool,
    has_triple_overlap_faces: bool,
    restriction_surjectivity_checked: bool,
) -> Vec<AgAssumptionLedgerEntryV1> {
    let profile_ref = format!("measurement-profile:{}", profile.profile_id);
    let forest_checked = nerve_is_forest && !has_triple_overlap_faces;
    let forest_checked_by = forest_checked.then(|| {
        format!(
            "cover-nerve:{}:forest=true:no-triple-overlap-faces=true",
            profile.cover_ref
        )
    });
    let forest_assumed_by = (!forest_checked).then(|| profile_ref.clone());

    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/11.1".to_string(),
            assumption: "local lawful sections form an effective Ob_U-torsor".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(profile_ref.clone()),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/11.1".to_string(),
            assumption: "local adjustment action is fixed and effective".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(profile_ref.clone()),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/11.1".to_string(),
            assumption: "coefficient object satisfies descent".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(profile_ref.clone()),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/12.4".to_string(),
            assumption: "restriction maps are surjective".to_string(),
            status: if restriction_surjectivity_checked {
                "checked"
            } else {
                "assumed"
            }
            .to_string(),
            checked_by: restriction_surjectivity_checked.then(|| {
                format!(
                    "cover-nerve:{}:restrictionSurjectivityWitness=all-selected-edges",
                    profile.cover_ref
                )
            }),
            assumed_by: (!restriction_surjectivity_checked).then(|| profile_ref.clone()),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/12.4".to_string(),
            assumption: "selected Cech nerve is a forest with no triple-overlap faces".to_string(),
            status: if forest_checked { "checked" } else { "assumed" }.to_string(),
            checked_by: forest_checked_by,
            assumed_by: forest_assumed_by,
        },
    ]
}

fn discharged_check_json(holds: bool, checked_by: &str) -> Value {
    json!({
        "holds": holds,
        "status": if holds {
            "discharged_by_check"
        } else {
            "not_discharged"
        },
        "checkedBy": if holds {
            Value::String(checked_by.to_string())
        } else {
            Value::Null
        }
    })
}

fn restriction_surjectivity_witnesses_v1(
    normalized: &NormalizedArchMapV2,
    edges: &[CechEdgeV1],
) -> Vec<Value> {
    let edge_ids = edges
        .iter()
        .map(|edge| edge.edge_id.as_str())
        .collect::<BTreeSet<_>>();
    normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "cech"
                && atom.predicate == "restrictionSurjectivityWitness"
                && edge_ids.contains(atom.subject.as_str())
                && atom.object.as_deref() == Some("finite-preimage-witness")
                && !atom.source_refs.is_empty()
        })
        .map(|atom| {
            json!({
                "edgeRef": atom.subject,
                "atomRef": atom.normalized_atom_id,
                "witnessObject": atom.object,
                "sourceRefs": atom.source_refs
            })
        })
        .collect()
}

fn selected_cover_contexts(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Vec<String> {
    normalized
        .covers
        .iter()
        .find(|cover| {
            cover.normalized_cover_id == profile.cover_ref
                || cover.source_cover_id == profile.cover_ref
        })
        .map(|cover| cover.context_ids.clone())
        .unwrap_or_default()
}

fn validate_cech_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "F2"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "rank-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "rank-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.cech-obstruction requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !profile
        .witness_family
        .iter()
        .any(|witness| witness.law == "ag.cech-obstruction")
    {
        return Err(format!(
            "ag.cech-obstruction requires law-surface witness variables for law ag.cech-obstruction",
        ));
    }
    Ok(())
}

fn validate_restriction_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "F2"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-support-inclusion@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "support-inclusion@1",
        ),
        ("domain", profile.domain.as_str(), "finite-poset-site"),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "all-inclusions-hold@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "some-inclusion-fails@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
        (
            "verdictDiscipline",
            profile.verdict_discipline.as_str(),
            "five-valued-structural-verdict@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.restriction-compatibility requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !profile
        .witness_family
        .iter()
        .any(|witness| witness.law == "ag.restriction-compatibility")
    {
        return Err(
            "ag.restriction-compatibility requires law-surface witness variables for law ag.restriction-compatibility"
                .to_string(),
        );
    }
    Ok(())
}

fn validate_section_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "F2"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-section-evaluation@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "section-factorization@1",
        ),
        ("domain", profile.domain.as_str(), "finite-poset-site"),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "pullback-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "pullback-nonzero@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
        (
            "verdictDiscipline",
            profile.verdict_discipline.as_str(),
            "five-valued-structural-verdict@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.section-factorization requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if section_witness_variables(profile).is_empty() {
        return Err(
            "ag.section-factorization requires law-surface witness variables for law ag.section-factorization"
                .to_string(),
        );
    }
    if section_witness_variables(profile).len() > MAX_SQUARE_FREE_WITNESS_VARIABLES {
        return Err(format!(
            "ag.section-factorization supports at most {MAX_SQUARE_FREE_WITNESS_VARIABLES} witness variables for finite support enumeration"
        ));
    }
    if section_witness_variables(profile).len()
        > profile.finite_bounds.max_square_free_witness_variables
    {
        return Err(format!(
            "ag.section-factorization witness variables exceed MeasurementProfile finiteBounds.maxSquareFreeWitnessVariables={}",
            profile.finite_bounds.max_square_free_witness_variables
        ));
    }
    Ok(())
}

fn validate_coherence_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "h2-coherence@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "rank-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "rank-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.coherence-obstruction requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !profile
        .witness_family
        .iter()
        .any(|witness| witness.law == "ag.coherence-obstruction")
    {
        return Err(format!(
            "ag.coherence-obstruction requires law-surface witness variables for law ag.coherence-obstruction",
        ));
    }
    Ok(())
}

fn validate_boundary_residue_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-mayer-vietoris-d0@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "boundary-residue-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "boundary-residue-nonzero@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
        ("domain", profile.domain.as_str(), "finite-poset-site"),
        (
            "verdictDiscipline",
            profile.verdict_discipline.as_str(),
            "five-valued-structural-verdict@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.boundary-residue requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if profile.resolution_selector != "mayer-vietoris-d0@1" {
        return Err(format!(
            "ag.boundary-residue requires MeasurementProfile resolutionSelector=mayer-vietoris-d0@1, found {}",
            profile.resolution_selector
        ));
    }
    if boundary_residue_witness_variables(profile).is_empty() {
        return Err(format!(
            "ag.boundary-residue requires law-surface witness variables for law ag.boundary-residue",
        ));
    }
    if boundary_residue_witness_variables(profile).len() > MAX_BOUNDARY_RESIDUE_VARIABLES {
        return Err(format!(
            "ag.boundary-residue supports at most {MAX_BOUNDARY_RESIDUE_VARIABLES} witness variables for finite F2 image membership"
        ));
    }
    if boundary_residue_witness_variables(profile).len()
        > profile.finite_bounds.max_boundary_residue_variables
    {
        return Err(format!(
            "ag.boundary-residue witness variables exceed MeasurementProfile finiteBounds.maxBoundaryResidueVariables={}",
            profile.finite_bounds.max_boundary_residue_variables
        ));
    }
    Ok(())
}

fn validate_square_free_profile_v1(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "F2"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "taylor@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "rank-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "rank-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.square-free-repair requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if witness_variables.is_empty() {
        return Err(format!(
            "ag.square-free-repair requires law surface witness variables for {}",
            profile.profile_id,
        ));
    }
    if witness_variables.len() > MAX_SQUARE_FREE_WITNESS_VARIABLES {
        return Err(format!(
            "ag.square-free-repair supports at most {MAX_SQUARE_FREE_WITNESS_VARIABLES} witness variables for finite support enumeration"
        ));
    }
    if witness_variables.len() > profile.finite_bounds.max_square_free_witness_variables {
        return Err(format!(
            "ag.square-free-repair witness variables exceed MeasurementProfile finiteBounds.maxSquareFreeWitnessVariables={}",
            profile.finite_bounds.max_square_free_witness_variables
        ));
    }
    Ok(())
}

fn validate_tor_profile_v1(
    profile: &MeasurementProfileV1,
    witness_variables: &[String],
) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "F2"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "rank-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "rank-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.law-conflict-tor requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if profile.resolution_selector != "taylor@1" {
        return Err(format!(
            "ag.law-conflict-tor requires MeasurementProfile resolutionSelector=taylor@1, found {}",
            profile.resolution_selector
        ));
    }
    if witness_variables.is_empty() {
        return Err(format!(
            "ag.law-conflict-tor requires law surface witness variables for {}",
            profile.profile_id
        ));
    }
    if witness_variables.len() > MAX_TOR_WITNESS_VARIABLES {
        return Err(format!(
            "ag.law-conflict-tor supports at most {MAX_TOR_WITNESS_VARIABLES} witness variables for finite monomial enumeration"
        ));
    }
    if witness_variables.len() > profile.finite_bounds.max_tor_witness_variables {
        return Err(format!(
            "ag.law-conflict-tor witness variables exceed MeasurementProfile finiteBounds.maxTorWitnessVariables={}",
            profile.finite_bounds.max_tor_witness_variables
        ));
    }
    Ok(())
}

fn validate_laplacian_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "R"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "cellular-laplacian@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "analytic-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "analytic-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "analytic-reading@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.sheaf-laplacian requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if laplacian_witness_variables(profile).is_empty() {
        return Err(format!(
            "ag.sheaf-laplacian requires law-surface witness variables for law ag.sheaf-laplacian",
        ));
    }
    if laplacian_witness_variables(profile).len() > MAX_LAPLACIAN_CELLS {
        return Err(format!(
            "ag.sheaf-laplacian supports at most {MAX_LAPLACIAN_CELLS} witness cells for finite Laplacian enumeration"
        ));
    }
    if laplacian_witness_variables(profile).len() > profile.finite_bounds.max_laplacian_cells {
        return Err(format!(
            "ag.sheaf-laplacian witness cells exceed MeasurementProfile finiteBounds.maxLaplacianCells={}",
            profile.finite_bounds.max_laplacian_cells
        ));
    }
    Ok(())
}

fn validate_period_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "R"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "finite-poset-period@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "analytic-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "analytic-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "analytic-reading@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.period-stokes requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if period_witness_cycles(profile).is_empty() {
        return Err(format!(
            "ag.period-stokes requires law-surface witness variables for law ag.period-stokes",
        ));
    }
    if period_witness_cycles(profile).len() > MAX_PERIOD_CYCLES {
        return Err(format!(
            "ag.period-stokes supports at most {MAX_PERIOD_CYCLES} witness cycles for finite period enumeration"
        ));
    }
    if period_witness_cycles(profile).len() > profile.finite_bounds.max_period_cycles {
        return Err(format!(
            "ag.period-stokes witness cycles exceed MeasurementProfile finiteBounds.maxPeriodCycles={}",
            profile.finite_bounds.max_period_cycles
        ));
    }
    Ok(())
}

fn validate_period_audit_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "fixed-coefficient-stokes-audit@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "finite-poset-period-stokes-audit@1",
        ),
        ("domain", profile.domain.as_str(), "finite-poset-site"),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "stokes-residual-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "stokes-residual-nonzero@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
        (
            "verdictDiscipline",
            profile.verdict_discipline.as_str(),
            "five-valued-structural-verdict@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.period-stokes-audit requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !matches!(profile.coefficient.as_str(), "F2" | "Q" | "R") {
        return Err(format!(
            "ag.period-stokes-audit requires MeasurementProfile coefficient F2, Q, or R, found {}",
            profile.coefficient
        ));
    }
    if period_audit_witness_cycles(profile).is_empty() {
        return Err(format!(
            "ag.period-stokes-audit requires law-surface witness variables for law ag.period-stokes-audit",
        ));
    }
    if period_audit_witness_cycles(profile).len() > MAX_PERIOD_CYCLES {
        return Err(format!(
            "ag.period-stokes-audit supports at most {MAX_PERIOD_CYCLES} witness cycles for finite period enumeration"
        ));
    }
    if period_audit_witness_cycles(profile).len() > profile.finite_bounds.max_period_cycles {
        return Err(format!(
            "ag.period-stokes-audit witness cycles exceed MeasurementProfile finiteBounds.maxPeriodCycles={}",
            profile.finite_bounds.max_period_cycles
        ));
    }
    Ok(())
}

fn validate_transfer_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "R"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "support-localized-transfer@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "analytic-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "analytic-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "analytic-reading@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.support-transfer requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if transfer_witness_targets(profile).is_empty() {
        return Err(format!(
            "ag.support-transfer requires law-surface witness variables for law ag.support-transfer",
        ));
    }
    if transfer_witness_targets(profile).len() > MAX_TRANSFER_TARGETS {
        return Err(format!(
            "ag.support-transfer supports at most {MAX_TRANSFER_TARGETS} witness targets for finite transfer enumeration"
        ));
    }
    if transfer_witness_targets(profile).len() > profile.finite_bounds.max_transfer_targets {
        return Err(format!(
            "ag.support-transfer witness targets exceed MeasurementProfile finiteBounds.maxTransferTargets={}",
            profile.finite_bounds.max_transfer_targets
        ));
    }
    Ok(())
}

fn laplacian_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| {
            matches!(
                witness.law.as_str(),
                "ag.sheaf-laplacian" | "ag.harmonic-debt"
            )
        })
        .map(|witness| witness.variable.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn period_witness_cycles(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.period-stokes")
        .map(|witness| witness.variable.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn period_audit_witness_cycles(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.period-stokes-audit")
        .map(|witness| witness.variable.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn transfer_witness_targets(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.support-transfer")
        .map(|witness| witness.variable.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn laplacian_cells(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Vec<LaplacianCellV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let mut cells = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "laplacian" && atom.predicate == "cellularCochain")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if !witness_set.contains(&atom.subject) {
            return Err(format!(
                "ag.sheaf-laplacian cochain {} uses cell outside law-surface witness variables: {}",
                atom.normalized_atom_id, atom.subject
            ));
        }
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.sheaf-laplacian cochain {} requires numeric object",
                atom.normalized_atom_id
            )
        })?;
        let value = raw.parse::<f64>().map_err(|_| {
            format!(
                "ag.sheaf-laplacian cochain {} has non-numeric object {raw}",
                atom.normalized_atom_id
            )
        })?;
        if !value.is_finite() {
            return Err(format!(
                "ag.sheaf-laplacian cochain {} requires finite numeric object",
                atom.normalized_atom_id
            ));
        }
        if cells
            .iter()
            .any(|cell: &LaplacianCellV1| cell.cell_id == atom.subject)
        {
            return Err(format!(
                "ag.sheaf-laplacian duplicate cellular cochain for {}",
                atom.subject
            ));
        }
        cells.push(LaplacianCellV1 {
            cell_id: atom.subject.clone(),
            value,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    cells.sort_by(|left, right| left.cell_id.cmp(&right.cell_id));
    Ok(cells)
}

fn laplacian_edges(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Result<Vec<LaplacianEdgeV1>, String> {
    let mut edges = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "laplacian" && atom.predicate == "cellularBoundary")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let target = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.sheaf-laplacian boundary {} requires target cell object",
                atom.normalized_atom_id
            )
        })?;
        edges.push(LaplacianEdgeV1 {
            source: atom.subject.clone(),
            target: target.to_string(),
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    edges.sort_by(|left, right| {
        left.source
            .cmp(&right.source)
            .then_with(|| left.target.cmp(&right.target))
            .then_with(|| left.atom_ref.cmp(&right.atom_ref))
    });
    Ok(edges)
}

fn period_integrals(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    cycle_basis: &[String],
) -> Result<Vec<PeriodIntegralV1>, String> {
    let cycle_set = cycle_basis.iter().cloned().collect::<BTreeSet<_>>();
    let mut pairings = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "period" && atom.predicate == "periodIntegral")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.period-stokes period integral {} requires object cycle=value",
                atom.normalized_atom_id
            )
        })?;
        let (cycle_id, value) = parse_numeric_assignment(
            raw,
            "ag.period-stokes period integral",
            &atom.normalized_atom_id,
        )?;
        if !cycle_set.contains(&cycle_id) {
            return Err(format!(
                "ag.period-stokes period integral {} uses cycle outside law-surface witness variables: {}",
                atom.normalized_atom_id, cycle_id
            ));
        }
        if pairings.iter().any(|pairing: &PeriodIntegralV1| {
            pairing.form_id == atom.subject && pairing.cycle_id == cycle_id
        }) {
            return Err(format!(
                "ag.period-stokes duplicate period integral for form {} and cycle {}",
                atom.subject, cycle_id
            ));
        }
        pairings.push(PeriodIntegralV1 {
            form_id: atom.subject.clone(),
            cycle_id,
            value,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    pairings.sort_by(|left, right| {
        left.form_id
            .cmp(&right.form_id)
            .then_with(|| left.cycle_id.cmp(&right.cycle_id))
    });
    Ok(pairings)
}

fn stokes_audit_values(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    predicate: &str,
    label: &str,
) -> Result<Vec<StokesAuditValueV1>, String> {
    let mut values = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "period" && atom.predicate == predicate)
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "{label} {} requires object chain=value",
                atom.normalized_atom_id
            )
        })?;
        let (chain_id, value) = parse_numeric_assignment(raw, label, &atom.normalized_atom_id)?;
        if values.iter().any(|entry: &StokesAuditValueV1| {
            entry.form_id == atom.subject && entry.chain_id == chain_id
        }) {
            return Err(format!(
                "{label} duplicate audit value for form {} and chain {}",
                atom.subject, chain_id
            ));
        }
        values.push(StokesAuditValueV1 {
            form_id: atom.subject.clone(),
            chain_id,
            value,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    values.sort_by(|left, right| {
        left.form_id
            .cmp(&right.form_id)
            .then_with(|| left.chain_id.cmp(&right.chain_id))
    });
    Ok(values)
}

fn parse_numeric_assignment(
    raw: &str,
    label: &str,
    atom_ref: &str,
) -> Result<(String, f64), String> {
    let (key, value) = raw.split_once('=').ok_or_else(|| {
        format!("{label} {atom_ref} requires assignment object in key=value form")
    })?;
    let key = key.trim();
    if key.is_empty() {
        return Err(format!(
            "{label} {atom_ref} requires non-empty assignment key"
        ));
    }
    let value = value.trim().parse::<f64>().map_err(|_| {
        format!(
            "{label} {atom_ref} has non-numeric assignment value {}",
            value.trim()
        )
    })?;
    if !value.is_finite() {
        return Err(format!(
            "{label} {atom_ref} requires finite numeric assignment value"
        ));
    }
    Ok((key.to_string(), value))
}

fn stokes_audit_report(
    d_omega: &[StokesAuditValueV1],
    boundary: &[StokesAuditValueV1],
) -> Result<Value, String> {
    let d_map = d_omega
        .iter()
        .map(|entry| ((entry.form_id.clone(), entry.chain_id.clone()), entry))
        .collect::<BTreeMap<_, _>>();
    let boundary_map = boundary
        .iter()
        .map(|entry| ((entry.form_id.clone(), entry.chain_id.clone()), entry))
        .collect::<BTreeMap<_, _>>();
    if d_map.keys().collect::<Vec<_>>() != boundary_map.keys().collect::<Vec<_>>() {
        return Err(
            "ag.period-stokes Stokes audit requires matching dOmegaIntegral and boundaryPeriod keys"
                .to_string(),
        );
    }
    let mut max_abs_residual: f64 = 0.0;
    let mut pairs = Vec::new();
    for (key, left) in d_map {
        let right = boundary_map[&key];
        let residual = left.value - right.value;
        max_abs_residual = max_abs_residual.max(residual.abs());
        pairs.push(json!({
            "form": left.form_id,
            "chain": left.chain_id,
            "dOmegaIntegral": round_f64(left.value),
            "boundaryPeriod": round_f64(right.value),
            "residual": round_f64(residual),
            "dOmegaAtomRef": left.atom_ref,
            "boundaryAtomRef": right.atom_ref
        }));
    }
    Ok(json!({
        "identity": "<d omega, gamma> = <omega, boundary gamma>",
        "status": if max_abs_residual > 1.0e-9 {
            "residual_nonzero"
        } else {
            "checked"
        },
        "maxAbsoluteResidual": round_f64(max_abs_residual),
        "pairs": pairs
    }))
}

fn fixed_coefficient_stokes_audit_report(
    d_omega: &[StokesAuditValueV1],
    boundary: &[StokesAuditValueV1],
    coefficient: &str,
) -> Value {
    if !matches!(coefficient, "F2" | "Q") {
        return json!({
            "identity": "<d omega, gamma> = <omega, boundary gamma>",
            "status": "unknown",
            "methodStatus": "strict_coefficient_unresolved",
            "coefficient": coefficient,
            "reason": "strict coefficient ring is unresolved; float/model-relative period data remains analytic-only",
            "pairs": []
        });
    }
    if d_omega.is_empty() || boundary.is_empty() {
        return json!({
            "identity": "<d omega, gamma> = <omega, boundary gamma>",
            "status": "not_computed",
            "methodStatus": "period_audit_model_missing",
            "coefficient": coefficient,
            "reason": "period Stokes audit requires non-empty dOmegaIntegral and boundaryPeriod values",
            "pairs": []
        });
    }
    let d_map = d_omega
        .iter()
        .map(|entry| ((entry.form_id.clone(), entry.chain_id.clone()), entry))
        .collect::<BTreeMap<_, _>>();
    let boundary_map = boundary
        .iter()
        .map(|entry| ((entry.form_id.clone(), entry.chain_id.clone()), entry))
        .collect::<BTreeMap<_, _>>();
    if d_map.keys().collect::<Vec<_>>() != boundary_map.keys().collect::<Vec<_>>() {
        return json!({
            "identity": "<d omega, gamma> = <omega, boundary gamma>",
            "status": "not_computed",
            "methodStatus": "period_audit_key_mismatch",
            "coefficient": coefficient,
            "reason": "period Stokes audit requires matching dOmegaIntegral and boundaryPeriod keys",
            "pairs": []
        });
    }

    let mut nonzero_count = 0usize;
    let mut max_abs_residual = 0.0f64;
    let mut pairs = Vec::new();
    for (key, left) in d_map {
        let right = boundary_map[&key];
        let Some(residual) = fixed_coefficient_residual(left.value, right.value, coefficient)
        else {
            return json!({
                "identity": "<d omega, gamma> = <omega, boundary gamma>",
                "status": "unknown",
                "methodStatus": "strict_coefficient_unresolved",
                "coefficient": coefficient,
                "reason": "fixed coefficient Stokes audit requires exact Q values or integer F2 representatives",
                "pairs": []
            });
        };
        if residual.abs() > 1.0e-9 {
            nonzero_count += 1;
        }
        max_abs_residual = max_abs_residual.max(residual.abs());
        pairs.push(json!({
            "form": left.form_id,
            "chain": left.chain_id,
            "dOmegaIntegral": fixed_coefficient_value(left.value, coefficient),
            "boundaryPeriod": fixed_coefficient_value(right.value, coefficient),
            "residual": fixed_coefficient_value(residual, coefficient),
            "dOmegaAtomRef": left.atom_ref,
            "boundaryAtomRef": right.atom_ref
        }));
    }
    json!({
        "identity": "<d omega, gamma> = <omega, boundary gamma>",
        "status": if nonzero_count == 0 {
            "checked"
        } else {
            "residual_nonzero"
        },
        "methodStatus": "fixed_coefficient_stokes_audit_computed",
        "coefficient": coefficient,
        "maxAbsoluteResidual": fixed_coefficient_value(max_abs_residual, coefficient),
        "nonzeroPairCount": nonzero_count,
        "pairs": pairs
    })
}

fn fixed_coefficient_residual(left: f64, right: f64, coefficient: &str) -> Option<f64> {
    match coefficient {
        "F2" => {
            let left_int = f2_integer_representative(left)?;
            let right_int = f2_integer_representative(right)?;
            Some(((left_int - right_int).rem_euclid(2)) as f64)
        }
        "Q" => Some(round_f64(left - right)),
        _ => None,
    }
}

fn f2_integer_representative(value: f64) -> Option<i64> {
    if !value.is_finite() {
        return None;
    }
    let rounded = value.round();
    ((value - rounded).abs() < 1.0e-9).then_some(rounded as i64)
}

fn fixed_coefficient_value(value: f64, coefficient: &str) -> Value {
    if coefficient == "F2" {
        json!(f2_integer_representative(value).unwrap_or(0).rem_euclid(2))
    } else {
        json!(round_f64(value))
    }
}

fn transfer_pairings(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    targets: &[String],
) -> Result<Vec<TransferPairingV1>, String> {
    let target_set = targets.iter().cloned().collect::<BTreeSet<_>>();
    let mut pairings = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "transfer" && atom.predicate == "transferPairing")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.support-transfer transfer pairing {} requires object target=value",
                atom.normalized_atom_id
            )
        })?;
        let (target_id, value) = parse_numeric_assignment(
            raw,
            "ag.support-transfer transfer pairing",
            &atom.normalized_atom_id,
        )?;
        if !target_set.contains(&target_id) {
            return Err(format!(
                "ag.support-transfer transfer pairing {} uses target outside law-surface witness variables: {}",
                atom.normalized_atom_id, target_id
            ));
        }
        if pairings.iter().any(|pairing: &TransferPairingV1| {
            pairing.path_id == atom.subject && pairing.target_id == target_id
        }) {
            return Err(format!(
                "ag.support-transfer duplicate transfer pairing for path {} and target {}",
                atom.subject, target_id
            ));
        }
        pairings.push(TransferPairingV1 {
            path_id: atom.subject.clone(),
            target_id,
            value,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    pairings.sort_by(|left, right| {
        left.path_id
            .cmp(&right.path_id)
            .then_with(|| left.target_id.cmp(&right.target_id))
    });
    Ok(pairings)
}

fn transfer_repair_paths(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    targets: &[String],
) -> Result<Vec<TransferRepairPathV1>, String> {
    let target_set = targets.iter().cloned().collect::<BTreeSet<_>>();
    let mut paths = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "transfer" && atom.predicate == "repairPath")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if paths
            .iter()
            .any(|path: &TransferRepairPathV1| path.path_id == atom.subject)
        {
            return Err(format!(
                "ag.support-transfer duplicate repair path {}",
                atom.subject
            ));
        }
        let support_targets = atom
            .object
            .as_deref()
            .map(parse_csv_values)
            .unwrap_or_default()
            .into_iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let unknown_support_targets = support_targets
            .iter()
            .filter(|target| !target_set.contains(*target))
            .cloned()
            .collect::<Vec<_>>();
        if !unknown_support_targets.is_empty() {
            return Err(format!(
                "ag.support-transfer repair path {} uses support targets outside law-surface witness variables: {}",
                atom.normalized_atom_id,
                unknown_support_targets.join(",")
            ));
        }
        paths.push(TransferRepairPathV1 {
            path_id: atom.subject.clone(),
            support_targets,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    paths.sort_by(|left, right| left.path_id.cmp(&right.path_id));
    Ok(paths)
}

fn transfer_ground_costs(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    targets: &[String],
) -> Result<Vec<TransferGroundCostV1>, String> {
    let target_set = targets.iter().cloned().collect::<BTreeSet<_>>();
    let mut costs = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "transfer" && atom.predicate == "groundCost")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if !target_set.contains(&atom.subject) {
            return Err(format!(
                "ag.support-transfer ground cost {} uses target outside law-surface witness variables: {}",
                atom.normalized_atom_id, atom.subject
            ));
        }
        let raw = atom.object.as_deref().ok_or_else(|| {
            format!(
                "ag.support-transfer ground cost {} requires numeric object",
                atom.normalized_atom_id
            )
        })?;
        let cost = raw.parse::<f64>().map_err(|_| {
            format!(
                "ag.support-transfer ground cost {} has non-numeric object {raw}",
                atom.normalized_atom_id
            )
        })?;
        if !cost.is_finite() || cost < 0.0 {
            return Err(format!(
                "ag.support-transfer ground cost {} requires finite non-negative object",
                atom.normalized_atom_id
            ));
        }
        if costs
            .iter()
            .any(|cost_entry: &TransferGroundCostV1| cost_entry.target_id == atom.subject)
        {
            return Err(format!(
                "ag.support-transfer duplicate ground cost for target {}",
                atom.subject
            ));
        }
        costs.push(TransferGroundCostV1 {
            target_id: atom.subject.clone(),
            cost,
            atom_ref: atom.normalized_atom_id.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    costs.sort_by(|left, right| left.target_id.cmp(&right.target_id));
    Ok(costs)
}

fn graph_laplacian(
    cell_ids: &[String],
    cell_index: &BTreeMap<String, usize>,
    edges: &[LaplacianEdgeV1],
) -> Vec<Vec<f64>> {
    let mut matrix = vec![vec![0.0; cell_ids.len()]; cell_ids.len()];
    for edge in edges {
        let source = cell_index[&edge.source];
        let target = cell_index[&edge.target];
        if source == target {
            continue;
        }
        matrix[source][source] += 1.0;
        matrix[target][target] += 1.0;
        matrix[source][target] -= 1.0;
        matrix[target][source] -= 1.0;
    }
    matrix
}

fn graph_components(
    cell_count: usize,
    cell_index: &BTreeMap<String, usize>,
    edges: &[LaplacianEdgeV1],
) -> Vec<Vec<usize>> {
    let mut adjacency = vec![Vec::<usize>::new(); cell_count];
    for edge in edges {
        let source = cell_index[&edge.source];
        let target = cell_index[&edge.target];
        adjacency[source].push(target);
        adjacency[target].push(source);
    }
    let mut seen = vec![false; cell_count];
    let mut components = Vec::new();
    for start in 0..cell_count {
        if seen[start] {
            continue;
        }
        let mut stack = vec![start];
        let mut component = Vec::new();
        seen[start] = true;
        while let Some(node) = stack.pop() {
            component.push(node);
            for next in &adjacency[node] {
                if !seen[*next] {
                    seen[*next] = true;
                    stack.push(*next);
                }
            }
        }
        component.sort();
        components.push(component);
    }
    components
}

fn harmonic_projection(values: &[f64], components: &[Vec<usize>]) -> Vec<f64> {
    let mut harmonic = vec![0.0; values.len()];
    for component in components {
        let average =
            component.iter().map(|index| values[*index]).sum::<f64>() / component.len() as f64;
        for index in component {
            harmonic[*index] = average;
        }
    }
    harmonic
}

fn squared_norm(values: &[f64]) -> f64 {
    values.iter().map(|value| value * value).sum()
}

fn jacobi_eigenvalues_symmetric(mut matrix: Vec<Vec<f64>>) -> Vec<f64> {
    let n = matrix.len();
    if n == 0 {
        return Vec::new();
    }
    for _ in 0..64 {
        let mut p = 0;
        let mut q = 0;
        let mut max_value = 0.0;
        for i in 0..n {
            for j in (i + 1)..n {
                let value = matrix[i][j].abs();
                if value > max_value {
                    max_value = value;
                    p = i;
                    q = j;
                }
            }
        }
        if max_value < 1.0e-10 {
            break;
        }
        let tau = (matrix[q][q] - matrix[p][p]) / (2.0 * matrix[p][q]);
        let t = if tau >= 0.0 {
            1.0 / (tau + (1.0 + tau * tau).sqrt())
        } else {
            -1.0 / (-tau + (1.0 + tau * tau).sqrt())
        };
        let c = 1.0 / (1.0 + t * t).sqrt();
        let s = t * c;
        let app = matrix[p][p];
        let aqq = matrix[q][q];
        let apq = matrix[p][q];
        matrix[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq;
        matrix[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq;
        matrix[p][q] = 0.0;
        matrix[q][p] = 0.0;
        for r in 0..n {
            if r == p || r == q {
                continue;
            }
            let arp = matrix[r][p];
            let arq = matrix[r][q];
            matrix[r][p] = c * arp - s * arq;
            matrix[p][r] = matrix[r][p];
            matrix[r][q] = s * arp + c * arq;
            matrix[q][r] = matrix[r][q];
        }
    }
    let mut eigenvalues = (0..n)
        .map(|index| round_f64(matrix[index][index]))
        .collect::<Vec<_>>();
    eigenvalues.sort_by(|left, right| left.total_cmp(right));
    eigenvalues
}

fn rounded_vec(values: &[f64]) -> Vec<Value> {
    values
        .iter()
        .map(|value| json!(round_f64(*value)))
        .collect()
}

fn rounded_matrix(values: &[Vec<f64>]) -> Vec<Vec<Value>> {
    values.iter().map(|row| rounded_vec(row)).collect()
}

fn round_f64(value: f64) -> f64 {
    if value.abs() < 1.0e-9 {
        0.0
    } else {
        (value * 1_000_000.0).round() / 1_000_000.0
    }
}

fn laplacian_assumptions(
    profile: &MeasurementProfileV1,
    cellular_model_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/8.1".to_string(),
            assumption:
                "finite cellular measurement model selected by supplied law-equation-surface"
                    .to_string(),
            status: cellular_model_status.to_string(),
            checked_by: (cellular_model_status == "checked")
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
            assumed_by: (cellular_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/8.5".to_string(),
            assumption: "finite Hodge decomposition is analytic reading only".to_string(),
            status: "checked".to_string(),
            checked_by: Some("finite-graph-laplacian@1".to_string()),
            assumed_by: None,
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/8.6".to_string(),
            assumption: "harmonic debt minimality remains theorem-candidate".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn period_assumptions(
    profile: &MeasurementProfileV1,
    period_model_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part7/5.2A".to_string(),
            assumption: "finite poset period model selected by supplied law-equation-surface"
                .to_string(),
            status: period_model_status.to_string(),
            checked_by: (period_model_status == "checked")
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
            assumed_by: (period_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part12/12.3".to_string(),
            assumption: "Stokes audit identity checked on supplied finite model".to_string(),
            status: period_model_status.to_string(),
            checked_by: (period_model_status == "checked")
                .then(|| "finite-poset-period-stokes@1".to_string()),
            assumed_by: (period_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part7/5.2A".to_string(),
            assumption: "period_comparison".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn period_audit_assumptions(
    profile: &MeasurementProfileV1,
    fixed_coefficient_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/13.2".to_string(),
            assumption:
                "supplied finite Stokes accounting values share a fixed coefficient reading"
                    .to_string(),
            status: fixed_coefficient_status.to_string(),
            checked_by: (fixed_coefficient_status == "checked").then(|| {
                format!(
                    "measurement-profile:{}.coefficient={}",
                    profile.profile_id, profile.coefficient
                )
            }),
            assumed_by: (fixed_coefficient_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part7/5.2A".to_string(),
            assumption: "strict-period-pairing remains analytic and model-relative".to_string(),
            status: "checked".to_string(),
            checked_by: Some("strict-period-pairing@1".to_string()),
            assumed_by: None,
        },
    ]
}

fn transfer_assumptions(
    profile: &MeasurementProfileV1,
    transfer_model_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/10.1".to_string(),
            assumption:
                "finite support-localized transfer model selected by supplied law-equation-surface"
                    .to_string(),
            status: transfer_model_status.to_string(),
            checked_by: (transfer_model_status == "checked")
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
            assumed_by: (transfer_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/10.6".to_string(),
            assumption: "finite Wasserstein transfer cost computed on supplied ground costs"
                .to_string(),
            status: transfer_model_status.to_string(),
            checked_by: (transfer_model_status == "checked")
                .then(|| "finite-support-localized-transfer@1".to_string()),
            assumed_by: (transfer_model_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/10.4".to_string(),
            assumption: "transfer_lower_bound".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn coherence_assumptions(
    profile: &MeasurementProfileV1,
    coefficient_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1".to_string(),
            assumption: "banded abelian F2 coefficient object for selected H2 coherence"
                .to_string(),
            status: coefficient_status.to_string(),
            checked_by: (coefficient_status == "checked").then(|| {
                format!(
                    "measurement-profile:{}.coefficient={}",
                    profile.profile_id, profile.coefficient
                )
            }),
            assumed_by: (coefficient_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part4/10.1".to_string(),
            assumption: "selected cover supplies a finite triple-overlap 2-skeleton".to_string(),
            status: "checked".to_string(),
            checked_by: Some(format!(
                "measurement-profile:{}.coverRef",
                profile.profile_id
            )),
            assumed_by: None,
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/B.8.2".to_string(),
            assumption:
                "Leray / acyclicity comparison from selected Cech complex to sheaf cohomology"
                    .to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn tor_common_ambient(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Result<Option<TorCommonAmbientV1>, String> {
    let ambients = normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "tor" && atom.predicate == "commonAmbient")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .map(|atom| {
            let raw_pair = atom.object.as_deref().ok_or_else(|| {
                format!(
                    "ag.law-conflict-tor common ambient {} requires object law pair",
                    atom.normalized_atom_id
                )
            })?;
            let law_pair = raw_pair
                .split(',')
                .map(str::trim)
                .filter(|law| !law.is_empty())
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            let unique_laws = law_pair.iter().cloned().collect::<BTreeSet<_>>();
            if law_pair.len() != 2 || unique_laws.len() != 2 {
                return Err(format!(
                    "ag.law-conflict-tor common ambient {} requires exactly two laws in object",
                    atom.normalized_atom_id
                ));
            }
            Ok(TorCommonAmbientV1 {
                ambient_ref: atom.subject.clone(),
                atom_ref: atom.normalized_atom_id.clone(),
                law_pair,
                source_refs: atom.source_refs.clone(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    if ambients.len() > 1 {
        return Err(format!(
            "ag.law-conflict-tor expected at most one selected common ambient, found {}",
            ambients.len()
        ));
    }

    Ok(ambients.into_iter().next())
}

fn tor_ideal_generators(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    laws: &[&crate::LawEquationV1],
    witness_variables: &[String],
) -> Result<Vec<TorIdealGeneratorV1>, String> {
    let observations = normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "tor" && atom.predicate == "lawIdealGenerator")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .collect::<Vec<_>>();
    let observed_laws = observations
        .iter()
        .map(|atom| atom.subject.clone())
        .collect::<BTreeSet<_>>();
    let declared_law_ids = laws
        .iter()
        .map(|law| law.law_id.as_str())
        .collect::<BTreeSet<_>>();
    let outside_laws = observed_laws
        .iter()
        .filter(|law| !declared_law_ids.contains(law.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    if !outside_laws.is_empty() {
        return Err(format!(
            "ag.law-conflict-tor observed law generators outside supplied law surface: {}",
            outside_laws.join(",")
        ));
    }
    let mut generators = Vec::new();
    for law in laws {
        let (_, law_aliases, binding_axis, binding_predicate) = law_witness_bindings(law)?;
        let (observed_axis, observed_predicate) =
            observation_selector("tor", &binding_axis, &binding_predicate)?;
        let declared_supports = declared_law_supports(law, witness_variables)?;
        if !observed_laws.contains(&law.law_id) {
            continue;
        }
        for (index, support) in declared_supports.iter().enumerate() {
            let matching_atoms = observations
                .iter()
                .filter(|atom| atom.subject == law.law_id)
                .filter(|atom| {
                    observed_support_matches(
                        atom,
                        support,
                        &law_aliases,
                        observed_axis,
                        observed_predicate,
                    )
                })
                .collect::<Vec<_>>();
            if matching_atoms.is_empty() {
                continue;
            }
            let context_refs = matching_atoms
                .iter()
                .flat_map(|atom| atom.context_memberships.iter().cloned())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let source_refs = matching_atoms
                .iter()
                .flat_map(|atom| atom.source_refs.iter().cloned())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let square_free = matching_atoms
                .iter()
                .all(|atom| observed_tor_support_is_square_free(atom));
            generators.push(TorIdealGeneratorV1 {
                law: law.law_id.clone(),
                generator_id: format!("law-surface:{}:{}", law.law_id, index + 1),
                support: support.clone(),
                square_free,
                context_refs,
                source_refs,
            });
        }
    }
    generators.sort_by(|left, right| {
        left.law
            .cmp(&right.law)
            .then_with(|| left.generator_id.cmp(&right.generator_id))
    });
    Ok(generators)
}

fn tor_shared_support_proxy_classes(
    generators: &[TorIdealGeneratorV1],
    left_law: &str,
    right_law: &str,
) -> Vec<TorConflictClassV1> {
    let left_generators = generators
        .iter()
        .filter(|generator| generator.law == left_law)
        .collect::<Vec<_>>();
    let right_generators = generators
        .iter()
        .filter(|generator| generator.law == right_law)
        .collect::<Vec<_>>();
    let mut classes = Vec::new();
    for left in &left_generators {
        for right in &right_generators {
            let shared_support = left
                .support
                .iter()
                .filter(|variable| right.support.contains(*variable))
                .cloned()
                .collect::<Vec<_>>();
            if shared_support.is_empty() {
                continue;
            }
            let mut support = left
                .support
                .iter()
                .chain(right.support.iter())
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            support.sort();
            let context_refs = left
                .context_refs
                .iter()
                .chain(right.context_refs.iter())
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            let source_refs = left
                .source_refs
                .iter()
                .chain(right.source_refs.iter())
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            classes.push(TorConflictClassV1 {
                conflict_id: format!("LawConflict_1:{}", classes.len() + 1),
                degree: 1,
                multidegree: support.clone(),
                support,
                shared_support,
                left_law: left.law.clone(),
                left_generator_ref: left.generator_id.clone(),
                right_law: right.law.clone(),
                right_generator_ref: right.generator_id.clone(),
                context_refs,
                source_refs,
            });
        }
    }
    classes
}

fn tor_taylor_h1_classes(
    generators: &[TorIdealGeneratorV1],
    left_law: &str,
    right_law: &str,
    witness_variables: &[String],
) -> Vec<TorConflictClassV1> {
    let left_generators = generators
        .iter()
        .filter(|generator| generator.law == left_law)
        .collect::<Vec<_>>();
    let right_generators = generators
        .iter()
        .filter(|generator| generator.law == right_law)
        .collect::<Vec<_>>();
    let mut classes = Vec::new();

    for multidegree in all_subsets(witness_variables)
        .into_iter()
        .filter(|degree| !degree.is_empty())
    {
        let f1_basis = left_generators
            .iter()
            .filter(|generator| is_subset(&generator.support, &multidegree))
            .filter(|generator| {
                let factor = support_difference(&multidegree, &generator.support);
                !monomial_zero_in_quotient(&factor, &right_generators)
            })
            .copied()
            .collect::<Vec<_>>();
        if f1_basis.is_empty() {
            continue;
        }

        let target_zero = monomial_zero_in_quotient(&multidegree, &right_generators);
        let rank_d1 = if target_zero { 0 } else { 1 };
        let kernel_dim = f1_basis.len().saturating_sub(rank_d1);
        if kernel_dim == 0 {
            continue;
        }

        let f1_index = f1_basis
            .iter()
            .enumerate()
            .map(|(index, generator)| (generator.generator_id.clone(), index))
            .collect::<BTreeMap<_, _>>();
        let mut d2_columns = Vec::new();
        for left_index in 0..left_generators.len() {
            for right_index in (left_index + 1)..left_generators.len() {
                let first = left_generators[left_index];
                let second = left_generators[right_index];
                let lcm = support_union(&first.support, &second.support);
                if !is_subset(&lcm, &multidegree) {
                    continue;
                }
                let lcm_factor = support_difference(&multidegree, &lcm);
                if monomial_zero_in_quotient(&lcm_factor, &right_generators) {
                    continue;
                }
                let mut column = vec![0u8; f1_basis.len()];
                if let Some(index) = f1_index.get(&first.generator_id) {
                    column[*index] ^= 1;
                }
                if let Some(index) = f1_index.get(&second.generator_id) {
                    column[*index] ^= 1;
                }
                if column.iter().any(|value| *value == 1) {
                    d2_columns.push(column);
                }
            }
        }
        let rank_d2 = matrix_rank_f2(d2_columns).min(kernel_dim);
        let h1_dim = kernel_dim.saturating_sub(rank_d2);
        if h1_dim == 0 {
            continue;
        }

        let right_witness = right_generators
            .iter()
            .find(|generator| is_subset(&generator.support, &multidegree))
            .copied()
            .or_else(|| right_generators.first().copied());
        let Some(right_witness) = right_witness else {
            continue;
        };
        let left_witnesses = f1_basis
            .iter()
            .map(|generator| generator.generator_id.clone())
            .collect::<Vec<_>>();
        let context_refs = f1_basis
            .iter()
            .flat_map(|generator| generator.context_refs.iter())
            .chain(right_witness.context_refs.iter())
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let source_refs = f1_basis
            .iter()
            .flat_map(|generator| generator.source_refs.iter())
            .chain(right_witness.source_refs.iter())
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let shared_support = f1_basis
            .iter()
            .flat_map(|generator| {
                generator
                    .support
                    .iter()
                    .filter(|variable| right_witness.support.contains(*variable))
                    .cloned()
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();

        for class_index in 0..h1_dim {
            classes.push(TorConflictClassV1 {
                conflict_id: format!("LawConflict_1:{}", classes.len() + 1),
                degree: 1,
                support: multidegree.clone(),
                multidegree: multidegree.clone(),
                shared_support: shared_support.clone(),
                left_law: left_law.to_string(),
                left_generator_ref: left_witnesses
                    .get(class_index)
                    .cloned()
                    .unwrap_or_else(|| left_witnesses.join("+")),
                right_law: right_law.to_string(),
                right_generator_ref: right_witness.generator_id.clone(),
                context_refs: context_refs.clone(),
                source_refs: source_refs.clone(),
            });
        }
    }

    classes.sort_by(|left, right| {
        left.multidegree
            .cmp(&right.multidegree)
            .then_with(|| left.conflict_id.cmp(&right.conflict_id))
    });
    for (index, class) in classes.iter_mut().enumerate() {
        class.conflict_id = format!("LawConflict_1:{}", index + 1);
    }
    classes
}

fn support_union(left: &[String], right: &[String]) -> Vec<String> {
    left.iter()
        .chain(right.iter())
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn support_difference(left: &[String], right: &[String]) -> Vec<String> {
    left.iter()
        .filter(|value| !right.contains(*value))
        .cloned()
        .collect()
}

fn monomial_zero_in_quotient(
    monomial_support: &[String],
    quotient_generators: &[&TorIdealGeneratorV1],
) -> bool {
    quotient_generators
        .iter()
        .any(|generator| is_subset(&generator.support, monomial_support))
}

fn tor_assumptions(
    profile: &MeasurementProfileV1,
    ambient: Option<&TorCommonAmbientV1>,
    ambient_status: &str,
    square_free_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    let coefficient_status = if ambient_status == "checked" {
        "checked"
    } else {
        "violated"
    };

    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/9.1".to_string(),
            assumption: "common ambient pair supplied by ArchMap under MeasurementProfile"
                .to_string(),
            status: ambient_status.to_string(),
            checked_by: ambient.map(|ambient| ambient.atom_ref.clone()),
            assumed_by: (ambient_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/9.1-coefficient-compatibility".to_string(),
            assumption:
                "common ambient coefficient compatibility under the selected single F2 coefficient model"
                    .to_string(),
            status: coefficient_status.to_string(),
            checked_by: (coefficient_status == "checked").then(|| {
                format!("measurement-profile:{}.coefficient:F2", profile.profile_id)
            }),
            assumed_by: (coefficient_status != "checked")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part5/5.5".to_string(),
            assumption: "finite square-free monomial law ideals selected for degree-1 Taylor Tor"
                .to_string(),
            status: square_free_status.to_string(),
            checked_by: match square_free_status {
                "checked" => Some(format!(
                    "law-surface:provided-law-equation-surface"
                )),
                "violated" => Some("ag.law-conflict-tor.squareFreeGeneratorCheck".to_string()),
                _ => None,
            },
            assumed_by: (square_free_status == "assumed")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part5/5.5-field".to_string(),
            assumption: "Taylor H1 is computed as an F2 field-coefficient reading".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/9.2".to_string(),
            assumption: "flat base change stability is theorem-candidate only".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn restriction_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    let mut variables = profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.restriction-compatibility")
        .map(|witness| witness.variable.clone())
        .collect::<Vec<_>>();
    variables.sort();
    variables.dedup();
    variables
}

fn restriction_generators(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Vec<RestrictionGeneratorV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let mut generators = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "restriction-compatibility"
                && atom.predicate == "restrictionIdealGenerator"
        })
        .filter(|atom| selected_contexts.contains(&atom.subject))
    {
        if !atom
            .context_memberships
            .iter()
            .any(|context| context == &atom.subject)
        {
            return Err(format!(
                "ag.restriction-compatibility generator {} must belong to its subject context {}",
                atom.normalized_atom_id, atom.subject
            ));
        }
        let support = restriction_generator_support(atom);
        if support.is_empty() {
            return Err(format!(
                "ag.restriction-compatibility generator {} has no finite support variables",
                atom.normalized_atom_id
            ));
        }
        let unknown = support
            .iter()
            .filter(|variable| !witness_set.contains(*variable))
            .cloned()
            .collect::<Vec<_>>();
        if !unknown.is_empty() {
            return Err(format!(
                "ag.restriction-compatibility generator {} contains variables outside law-surface witness variables: {}",
                atom.normalized_atom_id,
                unknown.join(",")
            ));
        }
        generators.push(RestrictionGeneratorV1 {
            generator_id: atom.normalized_atom_id.clone(),
            context_ref: atom.subject.clone(),
            support,
            source_refs: atom.source_refs.clone(),
        });
    }
    generators.sort_by(|left, right| left.generator_id.cmp(&right.generator_id));
    Ok(generators)
}

fn restriction_generator_support(atom: &NormalizedAtomV2) -> Vec<String> {
    let mut support = atom
        .object
        .as_deref()
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    support.sort();
    support.dedup();
    support
}

fn restriction_invariant_json(
    profile: &MeasurementProfileV1,
    method_status: &str,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    witness_variables: &[String],
    edge_checks: &[RestrictionEdgeCheckV1],
) -> Value {
    json!({
        "invariantId": format!("restriction-compatibility:{}", profile.profile_id),
        "evaluator": "ag.restriction-compatibility",
        "method": "finite-support-inclusion@1",
        "status": if method_status == "finite_support_inclusion_computed" { "computed" } else { "not_computed" },
        "methodStatus": method_status,
        "claimScope": "selected-cover separated presheaf restriction compatibility over finite monomial supports",
        "selectedCoverRef": profile.cover_ref,
        "witnessVariables": witness_variables,
        "contextCount": selected_contexts.len(),
        "restrictionEdgeCount": edges.len(),
        "edgeChecks": edge_checks.iter().map(|edge| json!({
            "edgeRef": edge.edge_ref,
            "sourceContextRef": edge.source_context,
            "targetContextRef": edge.target_context,
            "status": edge.status,
            "sourceGenerators": edge.source_generators.iter().map(restriction_generator_json).collect::<Vec<_>>(),
            "targetGenerators": edge.target_generators.iter().map(restriction_generator_json).collect::<Vec<_>>(),
            "violations": edge.violations.iter().map(|violation| json!({
                "generatorRef": violation.generator_id,
                "support": violation.support,
                "sourceRefs": violation.source_refs
            })).collect::<Vec<_>>()
        })).collect::<Vec<_>>(),
        "boundaryNote": "A measured_nonzero row means the selected local-sum presentation does not flow into the target ideal; sheaf image 再定義で消えうる、理論対象の defect ではない.",
        "nonConclusions": [
            "This is a selected-cover separated presheaf check, not a global sheaf or semantic safety proof.",
            "H1 Cech and H2 coherence verdict rows are not changed by this evaluator."
        ]
    })
}

fn restriction_generator_json(generator: &RestrictionGeneratorV1) -> Value {
    json!({
        "generatorId": generator.generator_id,
        "contextRef": generator.context_ref,
        "support": generator.support,
        "sourceRefs": generator.source_refs
    })
}

fn restriction_assumptions(
    profile: &MeasurementProfileV1,
    method_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "Lean/ObstructionIdeal.RestrictionCompatible.maps_selected".to_string(),
            assumption: "selected finite support generator family for restriction compatibility"
                .to_string(),
            status: if method_status == "restriction_generator_missing" {
                "violated"
            } else {
                "checked"
            }
            .to_string(),
            checked_by: (method_status != "restriction_generator_missing")
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
            assumed_by: (method_status == "restriction_generator_missing")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P0-2".to_string(),
            assumption: "selected cover supplies finite restriction edges for support inclusion"
                .to_string(),
            status: if method_status == "empty_selected_restriction_edges" {
                "violated"
            } else {
                "checked"
            }
            .to_string(),
            checked_by: (method_status != "empty_selected_restriction_edges")
                .then(|| format!("measurement-profile:{}.coverRef", profile.profile_id)),
            assumed_by: (method_status == "empty_selected_restriction_edges")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P0-2-boundary".to_string(),
            assumption: "measured nonzero restriction incompatibility is presentation-relative"
                .to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn section_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    let mut variables = profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.section-factorization")
        .map(|witness| witness.variable.clone())
        .collect::<Vec<_>>();
    variables.sort();
    variables.dedup();
    variables
}

fn section_forbidden_supports(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Vec<SectionForbiddenSupportV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let mut supports = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "section-factorization" && is_raw_support_predicate(atom))
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let support = parse_csv_values(atom.object.as_deref().unwrap_or_default());
        if support.is_empty() {
            return Err(format!(
                "ag.section-factorization raw support {} has no finite support variables",
                atom.normalized_atom_id
            ));
        }
        let unknown = support
            .iter()
            .filter(|variable| !witness_set.contains(*variable))
            .cloned()
            .collect::<Vec<_>>();
        if !unknown.is_empty() {
            return Err(format!(
                "ag.section-factorization raw support {} contains variables outside law-surface witness variables: {}",
                atom.normalized_atom_id,
                unknown.join(",")
            ));
        }
        supports.push(SectionForbiddenSupportV1 {
            support_id: atom.normalized_atom_id.clone(),
            support,
            source_refs: atom.source_refs.clone(),
        });
    }
    supports.sort_by(|left, right| left.support_id.cmp(&right.support_id));
    Ok(supports)
}

fn section_forbidden_supports_from_plan(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
    plan: &LawExecutionPlanV1,
) -> Result<Vec<SectionForbiddenSupportV1>, String> {
    let observed = section_forbidden_supports(normalized, selected_contexts, witness_variables)?;
    let declared = plan
        .section_forbidden_supports
        .as_ref()
        .ok_or_else(|| "section execution plan has no forbidden supports".to_string())?;
    let mut supports = Vec::new();
    for (index, support) in declared.iter().enumerate() {
        let mut observed_support_variables = support
            .iter()
            .map(|variable| {
                plan.section_variable_aliases
                    .as_ref()
                    .and_then(|aliases| aliases.get(variable))
                    .cloned()
                    .unwrap_or_else(|| variable.clone())
            })
            .collect::<Vec<_>>();
        observed_support_variables.sort();
        let mut declared_support = support.clone();
        declared_support.sort();
        let Some(observed_support) = observed
            .iter()
            .find(|candidate| candidate.support == observed_support_variables)
        else {
            return Ok(Vec::new());
        };
        let mut source_refs = observed_support.source_refs.clone();
        source_refs.push(format!("law-surface:{}", plan.surface_id));
        supports.push(SectionForbiddenSupportV1 {
            support_id: format!(
                "law-surface:{}:{}:forbidden:{}",
                plan.surface_id, plan.selected_law_id, index
            ),
            support: declared_support,
            source_refs,
        });
    }
    Ok(supports)
}

fn minimal_section_forbidden_supports(
    supports: &[SectionForbiddenSupportV1],
) -> Vec<SectionForbiddenSupportV1> {
    let minimal = minimal_supports(
        supports
            .iter()
            .map(|support| support.support.clone())
            .collect(),
    );
    minimal
        .into_iter()
        .map(|support| {
            supports
                .iter()
                .filter(|candidate| candidate.support == support)
                .min_by(|left, right| left.support_id.cmp(&right.support_id))
                .cloned()
                .unwrap_or_else(|| SectionForbiddenSupportV1 {
                    support_id: format!("support:{}", support.join("+")),
                    support,
                    source_refs: Vec::new(),
                })
        })
        .collect()
}

fn section_assignment(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Option<SectionAssignmentV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let atoms = normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "section-factorization" && atom.predicate == "witnessAssignment"
        })
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .collect::<Vec<_>>();
    if atoms.is_empty() {
        return Ok(None);
    }
    if atoms.len() > 1 {
        return Err(format!(
            "ag.section-factorization expects one selected witnessAssignment atom, found {}",
            atoms.len()
        ));
    }
    let atom = atoms[0];
    let mut assigned = BTreeMap::new();
    for field in atom
        .object
        .as_deref()
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|field| !field.is_empty())
    {
        let Some((variable, raw_value)) = field.split_once('=') else {
            return Err(format!(
                "ag.section-factorization witnessAssignment {} segment must be variable=value: {}",
                atom.normalized_atom_id, field
            ));
        };
        let variable = variable.trim().to_string();
        if !witness_set.contains(&variable) {
            return Err(format!(
                "ag.section-factorization witnessAssignment {} contains variable outside law-surface witness variables: {}",
                atom.normalized_atom_id, variable
            ));
        }
        let value = match raw_value.trim() {
            "1" | "true" | "True" => true,
            "0" | "false" | "False" => false,
            other => {
                return Err(format!(
                    "ag.section-factorization witnessAssignment {} has non-Boolean value for {}: {}",
                    atom.normalized_atom_id, variable, other
                ));
            }
        };
        if assigned.insert(variable.clone(), value).is_some() {
            return Err(format!(
                "ag.section-factorization witnessAssignment {} repeats variable {}",
                atom.normalized_atom_id, variable
            ));
        }
    }
    if assigned.is_empty() {
        return Err(format!(
            "ag.section-factorization witnessAssignment {} has no Boolean assignments",
            atom.normalized_atom_id
        ));
    }
    Ok(Some(SectionAssignmentV1 {
        assignment_id: atom.normalized_atom_id.clone(),
        assigned,
        source_refs: atom.source_refs.clone(),
    }))
}

fn section_invariant_json(
    profile: &MeasurementProfileV1,
    method_status: &str,
    witness_variables: &[String],
    forbidden_supports: &[SectionForbiddenSupportV1],
    minimal_forbidden_supports: &[SectionForbiddenSupportV1],
    assignment: Option<&SectionAssignmentV1>,
    assignment_status: &str,
    active_support: &[String],
    violated_supports: &[SectionForbiddenSupportV1],
) -> Value {
    json!({
        "invariantId": format!("section-factorization:{}", profile.profile_id),
        "evaluator": "ag.section-factorization",
        "method": "finite-section-pullback@1",
        "status": if method_status == "finite_section_pullback_computed" { "computed" } else { method_status },
        "methodStatus": method_status,
        "claimScope": "selected Boolean section only; finite s^* I_Ob^U pullback check over the chosen witness family",
        "selectedCoverRef": profile.cover_ref,
        "witnessVariables": witness_variables,
        "obstructionIdeal": {
            "id": "I_Ob^U",
            "generators": forbidden_supports.iter().map(section_support_json).collect::<Vec<_>>()
        },
        "minimalForbiddenSupports": minimal_forbidden_supports.iter().map(section_support_json).collect::<Vec<_>>(),
        "sectionAssignment": assignment.map(|assignment| json!({
            "assignmentRef": assignment.assignment_id,
            "assignmentStatus": assignment_status,
            "assigned": assignment.assigned,
            "activeSupport": active_support,
            "sourceRefs": assignment.source_refs
        })).unwrap_or_else(|| json!({
            "assignmentStatus": "absent",
            "activeSupport": [],
            "sourceRefs": []
        })),
        "violatedForbiddenSupports": violated_supports.iter().map(section_support_json).collect::<Vec<_>>(),
        "boundaryNote": "section-relative lawful only: this finite check does not prove all sections lawful, exactness without No-Cancellation, runtime safety, or semantic safety.",
        "assumptionBoundary": [
            "No-Cancellation/exactness is recorded as assumed, not discharged by ArchSig.",
            "The evaluator reuses measured_zero, measured_nonzero, unknown, and not_computed from the existing five-valued structural verdict vocabulary."
        ]
    })
}

fn section_support_json(support: &SectionForbiddenSupportV1) -> Value {
    json!({
        "supportRef": support.support_id,
        "support": support.support,
        "sourceRefs": support.source_refs
    })
}

fn section_assumptions(
    profile: &MeasurementProfileV1,
    method_status: &str,
    forbidden_supports: &[SectionForbiddenSupportV1],
) -> Vec<AgAssumptionLedgerEntryV1> {
    let support_refs = forbidden_supports
        .iter()
        .map(|support| support.support_id.clone())
        .collect::<Vec<_>>();
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "Lean/FiniteExamples.lawful_iff_factorsThroughLawfulLocus".to_string(),
            assumption: "selected witnessAssignment atom supplies the Boolean section for finite pullback evaluation".to_string(),
            status: if method_status == "section_assignment_absent" {
                "violated"
            } else {
                "checked"
            }
            .to_string(),
            checked_by: (method_status != "section_assignment_absent")
                .then(|| "section-factorization.witnessAssignment".to_string()),
            assumed_by: (method_status == "section_assignment_absent")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P0-3".to_string(),
            assumption: "selected raw support atoms supply the finite I_Ob^U presentation within the selected witness family".to_string(),
            status: if method_status == "obstruction_generators_absent" {
                "violated"
            } else {
                "checked"
            }
            .to_string(),
            checked_by: (!support_refs.is_empty()).then(|| {
                format!(
                    "ag.section-factorization:{}:{}",
                    profile.profile_id,
                    support_refs.join(",")
                )
            }),
            assumed_by: (method_status == "obstruction_generators_absent")
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P0-3-boundary".to_string(),
            assumption: "No-Cancellation/exactness boundary for reading s^* I_Ob^U=0 as section-relative lawful".to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn boundary_residue_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    let mut variables = profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.boundary-residue")
        .map(|witness| witness.variable.clone())
        .collect::<Vec<_>>();
    variables.sort();
    variables.dedup();
    variables
}

fn boundary_residue_roles(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Result<Vec<BoundaryResidueRoleV1>, String> {
    let mut roles = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "boundary-residue")
        .filter(|atom| matches!(atom.predicate.as_str(), "patchRole" | "patchClassification"))
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if !selected_contexts.contains(&atom.subject) {
            return Err(format!(
                "ag.boundary-residue patch role {} subject must be a selected context",
                atom.normalized_atom_id
            ));
        }
        let role = atom.object.as_deref().unwrap_or_default().trim();
        if !matches!(role, "core" | "feature" | "boundary") {
            return Err(format!(
                "ag.boundary-residue patch role {} must be core, feature, or boundary",
                atom.normalized_atom_id
            ));
        }
        roles.push(BoundaryResidueRoleV1 {
            atom_ref: atom.normalized_atom_id.clone(),
            context_ref: atom.subject.clone(),
            role: role.to_string(),
            source_refs: atom.source_refs.clone(),
        });
    }
    roles.sort_by(|left, right| {
        left.role
            .cmp(&right.role)
            .then_with(|| left.context_ref.cmp(&right.context_ref))
    });
    Ok(roles)
}

fn boundary_residue_role_map(roles: &[BoundaryResidueRoleV1]) -> BTreeMap<String, String> {
    let mut role_map = BTreeMap::new();
    for role in roles {
        role_map
            .entry(role.context_ref.clone())
            .and_modify(|existing| {
                if existing != &role.role {
                    *existing = "conflicted".to_string();
                }
            })
            .or_insert_with(|| role.role.clone());
    }
    role_map
}

fn boundary_residue_roles_complete(
    roles: &[BoundaryResidueRoleV1],
    selected_contexts: &BTreeSet<String>,
) -> bool {
    if roles.len() != selected_contexts.len() {
        return false;
    }
    if selected_contexts.iter().any(|context| {
        roles
            .iter()
            .filter(|role| role.context_ref == *context)
            .count()
            != 1
    }) {
        return false;
    }
    let role_set = roles
        .iter()
        .map(|role| role.role.as_str())
        .collect::<BTreeSet<_>>();
    ["core", "feature", "boundary"]
        .iter()
        .all(|role| role_set.contains(role))
}

fn boundary_residue_columns(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
    role_map: &BTreeMap<String, String>,
) -> Result<Vec<BoundaryResidueColumnV1>, String> {
    let mut columns = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "boundary-residue" && atom.predicate == "restrictionColumn")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        if !selected_contexts.contains(&atom.subject) {
            return Err(format!(
                "ag.boundary-residue restrictionColumn {} subject must be a selected source context",
                atom.normalized_atom_id
            ));
        }
        let source_role = role_map.get(&atom.subject).map(String::as_str);
        if !matches!(source_role, Some("core" | "feature")) {
            return Err(format!(
                "ag.boundary-residue restrictionColumn {} source context must be core or feature",
                atom.normalized_atom_id
            ));
        }
        let boundary_contexts = atom
            .context_memberships
            .iter()
            .filter(|context| role_map.get(*context).map(String::as_str) == Some("boundary"))
            .cloned()
            .collect::<Vec<_>>();
        if boundary_contexts.len() != 1 {
            return Err(format!(
                "ag.boundary-residue restrictionColumn {} must target exactly one boundary context",
                atom.normalized_atom_id
            ));
        }
        let support = boundary_residue_atom_support(atom, witness_variables)?;
        columns.push(BoundaryResidueColumnV1 {
            column_id: atom.normalized_atom_id.clone(),
            source_context: atom.subject.clone(),
            boundary_context: boundary_contexts[0].clone(),
            vector: boundary_residue_vector(&support, witness_variables),
            support,
            context_refs: atom.context_memberships.clone(),
            source_refs: atom.source_refs.clone(),
        });
    }
    columns.sort_by(|left, right| left.column_id.cmp(&right.column_id));
    Ok(columns)
}

fn boundary_residue_mismatch(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
    role_map: &BTreeMap<String, String>,
) -> Result<Option<BoundaryResidueMismatchV1>, String> {
    let mut atom_refs = Vec::new();
    let mut context_refs = BTreeSet::new();
    let mut source_refs = BTreeSet::new();
    let mut vector = vec![0u8; witness_variables.len()];
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "boundary-residue" && atom.predicate == "boundarySection")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let selected_memberships = atom
            .context_memberships
            .iter()
            .filter(|context| selected_contexts.contains(*context))
            .collect::<Vec<_>>();
        if selected_memberships.is_empty()
            || selected_memberships
                .iter()
                .any(|context| role_map.get(*context).map(String::as_str) != Some("boundary"))
        {
            return Err(format!(
                "ag.boundary-residue boundarySection {} must belong only to selected boundary contexts",
                atom.normalized_atom_id
            ));
        }
        let support = boundary_residue_atom_support(atom, witness_variables)?;
        let atom_vector = boundary_residue_vector(&support, witness_variables);
        for (target, value) in vector.iter_mut().zip(atom_vector.iter()) {
            *target ^= *value;
        }
        atom_refs.push(atom.normalized_atom_id.clone());
        context_refs.extend(atom.context_memberships.iter().cloned());
        source_refs.extend(atom.source_refs.iter().cloned());
    }
    if atom_refs.is_empty() {
        return Ok(None);
    }
    let support = witness_variables
        .iter()
        .zip(vector.iter())
        .filter_map(|(variable, value)| (*value == 1).then_some(variable.clone()))
        .collect::<Vec<_>>();
    Ok(Some(BoundaryResidueMismatchV1 {
        atom_refs,
        support,
        vector,
        context_refs: context_refs.into_iter().collect(),
        source_refs: source_refs.into_iter().collect(),
    }))
}

fn boundary_residue_atom_support(
    atom: &NormalizedAtomV2,
    witness_variables: &[String],
) -> Result<Vec<String>, String> {
    let support = parse_csv_values(atom.object.as_deref().unwrap_or_default())
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let unknown = support
        .iter()
        .filter(|variable| !witness_set.contains(*variable))
        .cloned()
        .collect::<Vec<_>>();
    if !unknown.is_empty() {
        return Err(format!(
            "ag.boundary-residue atom {} contains variables outside law-surface witness variables: {}",
            atom.normalized_atom_id,
            unknown.join(",")
        ));
    }
    Ok(support)
}

fn boundary_residue_vector(support: &[String], witness_variables: &[String]) -> Vec<u8> {
    witness_variables
        .iter()
        .map(|variable| support.contains(variable) as u8)
        .collect()
}

fn boundary_residue_matrix_rows(
    columns: &[BoundaryResidueColumnV1],
    row_count: usize,
) -> Vec<Vec<u8>> {
    (0..row_count)
        .map(|row| columns.iter().map(|column| column.vector[row]).collect())
        .collect()
}

fn boundary_residue_invariant_json(
    profile: &MeasurementProfileV1,
    method_status: &str,
    witness_variables: &[String],
    roles: &[BoundaryResidueRoleV1],
    columns: &[BoundaryResidueColumnV1],
    mismatch: Option<&BoundaryResidueMismatchV1>,
    image_membership: Option<bool>,
) -> Value {
    let matrix_rows = boundary_residue_matrix_rows(columns, witness_variables.len());
    json!({
        "invariantId": format!("boundary-residue:{}", profile.profile_id),
        "evaluator": "ag.boundary-residue",
        "method": "finite-mayer-vietoris-d0@1",
        "claimScope": "selected-cover core/feature/boundary F2 Mayer-Vietoris boundary residue",
        "selectedCoverRef": profile.cover_ref,
        "coefficient": profile.coefficient,
        "methodStatus": method_status,
        "patchRoles": roles.iter().map(|role| json!({
            "atomRef": role.atom_ref,
            "contextRef": role.context_ref,
            "role": role.role,
            "sourceRefs": role.source_refs
        })).collect::<Vec<_>>(),
        "restrictionMatrix": {
            "rowBasis": witness_variables,
            "columnCount": columns.len(),
            "rank": matrix_rank_f2(matrix_rows),
            "columns": columns.iter().map(|column| json!({
                "columnId": column.column_id,
                "sourceContext": column.source_context,
                "boundaryContext": column.boundary_context,
                "support": column.support,
                "vector": column.vector,
                "contextRefs": column.context_refs,
                "sourceRefs": column.source_refs
            })).collect::<Vec<_>>()
        },
        "boundarySection": mismatch.map(|mismatch| json!({
            "atomRefs": mismatch.atom_refs,
            "support": mismatch.support,
            "vector": mismatch.vector,
            "contextRefs": mismatch.context_refs,
            "sourceRefs": mismatch.source_refs
        })),
        "imageMembership": image_membership,
        "boundaryNote": "Boundary residue is measured only as an F2 Mayer-Vietoris d0 image-membership reading over the selected finite cover; Z-zero lifting is assumed, and no pi1 or monodromy verdict is generated.",
        "nonConclusions": [
            "This evaluator does not generate a period-Stokes or modelRelative reading.",
            "This evaluator does not generate a pi1 or monodromy verdict.",
            "Z-zero holonomy lifting is recorded only as an assumption over the F2 parity reading."
        ]
    })
}

fn boundary_residue_assumptions(
    profile: &MeasurementProfileV1,
    method_status: &str,
) -> Vec<AgAssumptionLedgerEntryV1> {
    let classification_checked = method_status != "boundary_classification_absent";
    let matrix_checked = matches!(
        method_status,
        "finite_mayer_vietoris_d0_computed" | "finite_mayer_vietoris_d0_obstruction_only"
    );
    let coefficient_checked = profile.coefficient == "F2";
    vec![
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-classification".to_string(),
            assumption:
                "selected cover supplies core, feature, and boundary patch classification atoms"
                    .to_string(),
            status: if classification_checked {
                "checked"
            } else {
                "violated"
            }
            .to_string(),
            checked_by: classification_checked
                .then(|| format!("measurement-profile:{}.coverRef", profile.profile_id)),
            assumed_by: (!classification_checked)
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-d0".to_string(),
            assumption:
                "selected boundary mismatch section and finite core/feature restriction columns define Mayer-Vietoris d0 over F2"
                    .to_string(),
            status: if matrix_checked { "checked" } else { "violated" }.to_string(),
            checked_by: matrix_checked
                .then(|| "law-surface:provided-law-equation-surface".to_string()),
            assumed_by: (!matrix_checked).then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-coefficient".to_string(),
            assumption: "F2 parity coefficient reading is fixed or explicitly projected for boundary residue".to_string(),
            status: if coefficient_checked { "checked" } else { "assumed" }.to_string(),
            checked_by: coefficient_checked.then(|| {
                format!(
                    "measurement-profile:{}.coefficient=F2",
                    profile.profile_id
                )
            }),
            assumed_by: (!coefficient_checked)
                .then(|| format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-z-zero".to_string(),
            assumption: "Z-zero holonomy lifting is assumed from the F2 parity reading only"
                .to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
        AgAssumptionLedgerEntryV1 {
            theorem_ref: "part8/P1-2-pi1-boundary".to_string(),
            assumption:
                "boundary residue is a finite restriction-structure reading, not a pi1 or monodromy verdict"
                    .to_string(),
            status: "assumed".to_string(),
            checked_by: None,
            assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
        },
    ]
}

fn square_free_generators_from_law_surface(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    law: &crate::LawEquationV1,
    witness_variables: &[String],
    archmap_aliases: &BTreeMap<String, String>,
    binding_axis: &str,
    binding_predicate: &str,
) -> Result<Vec<SquareFreeGeneratorV1>, String> {
    let (observed_axis, observed_predicate) =
        observation_selector("square-free", binding_axis, binding_predicate)?;
    let declared_supports = declared_law_supports(law, witness_variables)?;
    let support_atoms = normalized
        .atoms
        .iter()
        .filter(|atom| is_raw_support_predicate(atom))
        .filter(|atom| atom.axis == observed_axis && atom.predicate == observed_predicate)
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .collect::<Vec<_>>();
    let mut generators = Vec::new();
    for (index, support) in declared_supports.iter().enumerate() {
        let support_atom_refs = support_atoms
            .iter()
            .filter(|atom| {
                observed_support_matches(
                    atom,
                    support,
                    archmap_aliases,
                    observed_axis,
                    observed_predicate,
                )
            })
            .map(|atom| atom.normalized_atom_id.clone())
            .collect::<Vec<_>>();
        generators.push(SquareFreeGeneratorV1 {
            generator_id: format!("law-surface:{}:generator:{}", law.law_id, index + 1),
            support: support.clone(),
            support_atom_refs,
        });
    }
    Ok(generators)
}

fn square_free_atom_variables(atom: &crate::NormalizedAtomV2) -> Vec<String> {
    let mut support = Vec::new();
    for value in std::iter::once(atom.subject.as_str()).chain(atom.object.as_deref()) {
        for variable in value
            .split(',')
            .map(str::trim)
            .filter(|value| !value.is_empty())
        {
            support.push(variable.to_string());
        }
    }
    support.sort();
    support.dedup();
    support
}

fn square_free_certificate(
    _normalized: &NormalizedArchMapV2,
    _selected_contexts: &BTreeSet<String>,
    minimal_forbidden_supports: &[Vec<String>],
    repair_hitting_sets: &[Vec<String>],
    generators: &[SquareFreeGeneratorV1],
    witness_variable_count: usize,
    invariant_id: &str,
) -> Result<Option<SquareFreeCertificateV1>, String> {
    if minimal_forbidden_supports.is_empty() {
        return Ok(None);
    }
    let verification = compute_square_free_nsdepth_certificate(
        minimal_forbidden_supports,
        repair_hitting_sets,
        generators,
        witness_variable_count,
    );
    Ok(Some(SquareFreeCertificateV1 {
        cert_ref: format!("computedInvariants/{invariant_id}"),
        nsdepth: verification.nsdepth,
        support_atom_refs: verification.support_atom_refs,
        verified_minimal_forbidden_supports: verification.verified_minimal_forbidden_supports,
        status: verification.status,
        effect: verification.effect,
    }))
}

#[derive(Debug, Clone)]
struct SquareFreeCertificateVerificationV1 {
    nsdepth: Option<usize>,
    support_atom_refs: Vec<String>,
    verified_minimal_forbidden_supports: Vec<Vec<String>>,
    status: String,
    effect: String,
}

fn compute_square_free_nsdepth_certificate(
    minimal_forbidden_supports: &[Vec<String>],
    repair_hitting_sets: &[Vec<String>],
    generators: &[SquareFreeGeneratorV1],
    witness_variable_count: usize,
) -> SquareFreeCertificateVerificationV1 {
    let nsdepth = repair_hitting_sets.iter().map(Vec::len).max().unwrap_or(0);
    if nsdepth > witness_variable_count {
        return square_free_certificate_unverified(
            Some(nsdepth),
            "not_computed",
            "computed NSdepth exceeds selected witness family size; structural verdict follows observed support atom occurrence",
        );
    }
    let support_atom_refs = generators
        .iter()
        .flat_map(|generator| generator.support_atom_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    SquareFreeCertificateVerificationV1 {
        nsdepth: Some(nsdepth),
        support_atom_refs,
        verified_minimal_forbidden_supports: minimal_forbidden_supports.to_vec(),
        status: "computed".to_string(),
        effect:
            "ArchSig computed NSdepth from selected raw supports, minimal forbidden supports, and the finite Alexander-dual hitting-set depth rule; structural verdict follows observed support atom occurrence"
                .to_string(),
    }
}

fn is_raw_support_predicate(atom: &NormalizedAtomV2) -> bool {
    matches!(atom.predicate.as_str(), "support" | "cooccurrence")
}

fn square_free_certificate_unverified(
    nsdepth: Option<usize>,
    status: &str,
    effect: &str,
) -> SquareFreeCertificateVerificationV1 {
    SquareFreeCertificateVerificationV1 {
        nsdepth,
        support_atom_refs: Vec::new(),
        verified_minimal_forbidden_supports: Vec::new(),
        status: status.to_string(),
        effect: effect.to_string(),
    }
}

fn parse_csv_values(raw: &str) -> Vec<String> {
    let mut values = raw
        .split(',')
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    values.sort();
    values.dedup();
    values
}

fn atom_belongs_to_selected_context(
    atom: &crate::NormalizedAtomV2,
    selected_contexts: &BTreeSet<String>,
) -> bool {
    atom.context_memberships
        .iter()
        .any(|membership| selected_contexts.contains(membership))
}

fn minimal_supports(mut supports: Vec<Vec<String>>) -> Vec<Vec<String>> {
    for support in &mut supports {
        support.sort();
        support.dedup();
    }
    supports.sort();
    supports.dedup();
    supports
        .iter()
        .filter(|support| {
            !supports.iter().any(|candidate| {
                candidate.len() < support.len()
                    && is_subset(candidate.as_slice(), support.as_slice())
            })
        })
        .cloned()
        .collect()
}

fn delta_faces_from_forbidden_supports(
    witness_variables: &[String],
    minimal_forbidden_supports: &[Vec<String>],
) -> Vec<Vec<String>> {
    all_subsets(witness_variables)
        .into_iter()
        .filter(|face| {
            !minimal_forbidden_supports
                .iter()
                .any(|forbidden| is_subset(forbidden.as_slice(), face.as_slice()))
        })
        .collect()
}

fn delta_link_faces(delta_faces: &[Vec<String>], vertex: &str) -> Vec<Vec<String>> {
    let face_set = delta_faces.iter().cloned().collect::<BTreeSet<_>>();
    let mut link_faces = delta_faces
        .iter()
        .filter(|face| !face.iter().any(|entry| entry == vertex))
        .filter_map(|face| {
            let mut with_vertex = face.clone();
            with_vertex.push(vertex.to_string());
            with_vertex.sort();
            face_set.contains(&with_vertex).then(|| face.clone())
        })
        .collect::<Vec<_>>();
    link_faces.sort();
    link_faces.dedup();
    link_faces
}

fn simplicial_boundary_rank_reading(faces: &[Vec<String>]) -> Vec<Value> {
    let mut simplices_by_degree = BTreeMap::<usize, Vec<Vec<String>>>::new();
    for face in faces.iter().filter(|face| !face.is_empty()) {
        simplices_by_degree
            .entry(face.len() - 1)
            .or_default()
            .push(face.clone());
    }
    for simplices in simplices_by_degree.values_mut() {
        simplices.sort();
        simplices.dedup();
    }

    let max_degree = simplices_by_degree.keys().next_back().copied().unwrap_or(0);
    (1..=max_degree)
        .map(|degree| {
            json!({
                "domainDegree": degree,
                "codomainDegree": degree - 1,
                "rank": boundary_rank_f2(&simplices_by_degree, degree)
            })
        })
        .collect()
}

fn simplicial_component_count(faces: &[Vec<String>]) -> usize {
    let vertices = faces
        .iter()
        .filter(|face| face.len() == 1)
        .map(|face| face[0].clone())
        .collect::<BTreeSet<_>>();
    if vertices.is_empty() {
        return 0;
    }

    let mut adjacency = vertices
        .iter()
        .map(|vertex| (vertex.clone(), BTreeSet::<String>::new()))
        .collect::<BTreeMap<_, _>>();
    for edge in faces.iter().filter(|face| face.len() == 2) {
        if let [left, right] = edge.as_slice() {
            adjacency
                .entry(left.clone())
                .or_default()
                .insert(right.clone());
            adjacency
                .entry(right.clone())
                .or_default()
                .insert(left.clone());
        }
    }

    let mut seen = BTreeSet::<String>::new();
    let mut count = 0;
    for vertex in vertices {
        if !seen.insert(vertex.clone()) {
            continue;
        }
        count += 1;
        let mut stack = vec![vertex];
        while let Some(current) = stack.pop() {
            if let Some(neighbors) = adjacency.get(&current) {
                for neighbor in neighbors {
                    if seen.insert(neighbor.clone()) {
                        stack.push(neighbor.clone());
                    }
                }
            }
        }
    }
    count
}

fn reduced_simplicial_homology_f2(faces: &[Vec<String>]) -> Vec<Value> {
    let mut simplices_by_degree = BTreeMap::<usize, Vec<Vec<String>>>::new();
    for face in faces.iter().filter(|face| !face.is_empty()) {
        simplices_by_degree
            .entry(face.len() - 1)
            .or_default()
            .push(face.clone());
    }
    for simplices in simplices_by_degree.values_mut() {
        simplices.sort();
        simplices.dedup();
    }

    let max_degree = simplices_by_degree.keys().next_back().copied().unwrap_or(0);
    let mut betti = Vec::new();
    for degree in 0..=max_degree {
        let dim_chain = simplices_by_degree
            .get(&degree)
            .map_or(0, std::vec::Vec::len);
        let boundary_rank = if degree == 0 {
            usize::from(dim_chain > 0)
        } else {
            boundary_rank_f2(&simplices_by_degree, degree)
        };
        let next_boundary_rank = boundary_rank_f2(&simplices_by_degree, degree + 1);
        let dimension = dim_chain.saturating_sub(boundary_rank + next_boundary_rank);
        betti.push(json!({
            "degree": degree,
            "dimension": dimension
        }));
    }
    betti
}

fn boundary_rank_f2(
    simplices_by_degree: &BTreeMap<usize, Vec<Vec<String>>>,
    degree: usize,
) -> usize {
    if degree == 0 {
        return 0;
    }
    let Some(domain) = simplices_by_degree.get(&degree) else {
        return 0;
    };
    let Some(codomain) = simplices_by_degree.get(&(degree - 1)) else {
        return 0;
    };
    let row_index = codomain
        .iter()
        .enumerate()
        .map(|(index, simplex)| (simplex.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut rows = vec![vec![0u8; domain.len()]; codomain.len()];
    for (column, simplex) in domain.iter().enumerate() {
        for omitted in 0..simplex.len() {
            let mut facet = simplex.clone();
            facet.remove(omitted);
            if let Some(row) = row_index.get(&facet) {
                rows[*row][column] ^= 1;
            }
        }
    }
    matrix_rank_f2(rows)
}

fn matrix_rank_f2(mut rows: Vec<Vec<u8>>) -> usize {
    if rows.is_empty() {
        return 0;
    }
    let column_count = rows[0].len();
    let mut rank = 0;
    for column in 0..column_count {
        let Some(pivot) = (rank..rows.len()).find(|row| rows[*row][column] == 1) else {
            continue;
        };
        rows.swap(rank, pivot);
        for row in 0..rows.len() {
            if row != rank && rows[row][column] == 1 {
                for next_column in column..column_count {
                    rows[row][next_column] ^= rows[rank][next_column];
                }
            }
        }
        rank += 1;
        if rank == rows.len() {
            break;
        }
    }
    rank
}

fn minimal_hitting_sets(
    witness_variables: &[String],
    minimal_forbidden_supports: &[Vec<String>],
) -> Vec<Vec<String>> {
    if minimal_forbidden_supports.is_empty() {
        return Vec::new();
    }
    let hitting_sets = all_subsets(witness_variables)
        .into_iter()
        .filter(|candidate| !candidate.is_empty())
        .filter(|candidate| {
            minimal_forbidden_supports
                .iter()
                .all(|support| candidate.iter().any(|variable| support.contains(variable)))
        })
        .collect::<Vec<_>>();
    let mut minimal = minimal_supports(hitting_sets);
    minimal.sort_by(|left, right| left.len().cmp(&right.len()).then_with(|| left.cmp(right)));
    minimal
}

fn all_subsets(items: &[String]) -> Vec<Vec<String>> {
    let mut subsets = Vec::new();
    let limit = 1usize << items.len();
    for mask in 0..limit {
        let mut subset = Vec::new();
        for (index, item) in items.iter().enumerate() {
            if mask & (1usize << index) != 0 {
                subset.push(item.clone());
            }
        }
        subsets.push(subset);
    }
    subsets.sort();
    subsets
}

fn is_subset(left: &[String], right: &[String]) -> bool {
    left.iter().all(|item| right.contains(item))
}

/// 1 本の cech edge の観測値。cech evaluator と saga descent の両方が同じ規則で読む:
/// `cech/cocycleValue` atom があればそれを優先し、無ければ両端 `cech/sectionValue` の集合比較。
#[derive(Debug, Clone)]
pub(crate) struct CechEdgeObservationV1 {
    pub value: u8,
    pub support_atom_refs: Vec<String>,
    pub observed: bool,
}

pub(crate) fn observe_cech_edge(
    normalized: &NormalizedArchMapV2,
    left: &str,
    right: &str,
) -> CechEdgeObservationV1 {
    let left_atoms = normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "cech" && atom.predicate == "sectionValue" && atom.subject == left
        })
        .collect::<Vec<_>>();
    let right_atoms = normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "cech" && atom.predicate == "sectionValue" && atom.subject == right
        })
        .collect::<Vec<_>>();
    let forward_edge_id = format!("{left}->{right}");
    let reverse_edge_id = format!("{right}->{left}");
    let explicit_support = normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "cech"
                && atom.predicate == "cocycleValue"
                && (atom.subject == forward_edge_id || atom.subject == reverse_edge_id)
        })
        .collect::<Vec<_>>();
    if !explicit_support.is_empty() {
        if explicit_support
            .iter()
            .any(|atom| atom.source_refs.is_empty())
        {
            return CechEdgeObservationV1 {
                value: 0,
                support_atom_refs: Vec::new(),
                observed: false,
            };
        }
        let value = explicit_support.iter().any(|atom| {
            atom.object
                .as_deref()
                .is_some_and(|object| matches!(object.trim(), "1" | "true" | "nonzero"))
        });
        let support_atom_refs = if value {
            explicit_support
                .iter()
                .map(|atom| atom.normalized_atom_id.clone())
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        return CechEdgeObservationV1 {
            value: u8::from(value),
            support_atom_refs,
            observed: true,
        };
    }
    let section_values = |atoms: &[&NormalizedAtomV2]| {
        atoms
            .iter()
            .filter(|atom| !atom.source_refs.is_empty())
            .filter_map(|atom| atom.object.as_deref())
            .map(str::trim)
            .filter(|value| !value.is_empty())
            .map(str::to_string)
            .collect::<BTreeSet<_>>()
    };
    let source_values = section_values(&left_atoms);
    let target_values = section_values(&right_atoms);
    let observed = !source_values.is_empty() && !target_values.is_empty();
    let mismatch = observed && source_values != target_values;
    let support_atom_refs = if mismatch {
        normalized
            .atoms
            .iter()
            .filter(|atom| {
                atom.axis == "cech"
                    && atom.predicate == "sectionValue"
                    && !atom.source_refs.is_empty()
                    && (atom.subject == left || atom.subject == right)
            })
            .map(|atom| atom.normalized_atom_id.clone())
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    CechEdgeObservationV1 {
        value: u8::from(mismatch),
        support_atom_refs,
        observed,
    }
}

fn cech_edges(normalized: &NormalizedArchMapV2, selected_contexts: &[String]) -> Vec<CechEdgeV1> {
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let mut seen_edges = BTreeSet::new();
    let mut edges = Vec::new();
    for context in &normalized.contexts {
        if !selected.contains(&context.normalized_context_id) {
            continue;
        }
        for target in context
            .restricts_to
            .iter()
            .filter(|target| selected.contains(*target))
        {
            let edge_key = if context.normalized_context_id < *target {
                (
                    context.normalized_context_id.clone(),
                    target.clone(),
                    context.normalized_context_id.clone(),
                    target.clone(),
                )
            } else {
                (
                    target.clone(),
                    context.normalized_context_id.clone(),
                    context.normalized_context_id.clone(),
                    target.clone(),
                )
            };
            if !seen_edges.insert((edge_key.0.clone(), edge_key.1.clone())) {
                continue;
            }
            let edge_id = format!("{}->{}", edge_key.2, edge_key.3);
            let observation = observe_cech_edge(normalized, &edge_key.2, &edge_key.3);
            edges.push(CechEdgeV1 {
                edge_id,
                source_context: edge_key.2,
                target_context: edge_key.3,
                value: observation.value,
                support_atom_refs: observation.support_atom_refs,
                observed: observation.observed,
            });
        }
    }
    edges.sort_by(|left, right| left.edge_id.cmp(&right.edge_id));
    edges
}

fn coherence_faces(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    cover_ref: &str,
) -> Vec<CoherenceFaceV1> {
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let mut edge_by_pair = BTreeMap::new();
    for edge in edges {
        edge_by_pair.insert(
            sorted_pair(&edge.source_context, &edge.target_context),
            edge.edge_id.clone(),
        );
    }
    let atom_refs_by_context = normalized
        .contexts
        .iter()
        .filter(|context| selected.contains(&context.normalized_context_id))
        .map(|context| {
            (
                context.normalized_context_id.clone(),
                context.atom_ids.iter().cloned().collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut faces = Vec::new();
    for left in 0..selected_contexts.len() {
        for middle in left + 1..selected_contexts.len() {
            for right in middle + 1..selected_contexts.len() {
                let contexts = vec![
                    selected_contexts[left].clone(),
                    selected_contexts[middle].clone(),
                    selected_contexts[right].clone(),
                ];
                let Some(left_atoms) = atom_refs_by_context.get(&contexts[0]) else {
                    continue;
                };
                let Some(middle_atoms) = atom_refs_by_context.get(&contexts[1]) else {
                    continue;
                };
                let Some(right_atoms) = atom_refs_by_context.get(&contexts[2]) else {
                    continue;
                };
                let shared_atom_refs = left_atoms
                    .intersection(middle_atoms)
                    .cloned()
                    .collect::<BTreeSet<_>>()
                    .intersection(right_atoms)
                    .cloned()
                    .collect::<Vec<_>>();
                if shared_atom_refs.is_empty() {
                    continue;
                }
                let edge_refs = [
                    edge_by_pair.get(&sorted_pair(&contexts[0], &contexts[1])),
                    edge_by_pair.get(&sorted_pair(&contexts[0], &contexts[2])),
                    edge_by_pair.get(&sorted_pair(&contexts[1], &contexts[2])),
                ]
                .into_iter()
                .flatten()
                .cloned()
                .collect::<Vec<_>>();
                faces.push(CoherenceFaceV1 {
                    face_id: format!(
                        "coherence-face:{}:{}:{}:{}",
                        cover_ref, contexts[0], contexts[1], contexts[2]
                    ),
                    context_refs: contexts,
                    edge_refs,
                    shared_atom_refs,
                });
            }
        }
    }
    faces.sort_by(|left, right| left.face_id.cmp(&right.face_id));
    faces
}

fn coherence_tetrahedra(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &[String],
    faces: &[CoherenceFaceV1],
) -> Vec<CoherenceTetrahedronV1> {
    let face_by_contexts = faces
        .iter()
        .map(|face| {
            (
                face.context_refs.iter().cloned().collect::<BTreeSet<_>>(),
                face.face_id.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let atom_refs_by_context = normalized
        .contexts
        .iter()
        .filter(|context| selected.contains(&context.normalized_context_id))
        .map(|context| {
            (
                context.normalized_context_id.clone(),
                context.atom_ids.iter().cloned().collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut tetrahedra = Vec::new();
    for first in 0..selected_contexts.len() {
        for second in first + 1..selected_contexts.len() {
            for third in second + 1..selected_contexts.len() {
                for fourth in third + 1..selected_contexts.len() {
                    let contexts = vec![
                        selected_contexts[first].clone(),
                        selected_contexts[second].clone(),
                        selected_contexts[third].clone(),
                        selected_contexts[fourth].clone(),
                    ];
                    let Some(shared_atom_refs) =
                        shared_atoms_for_contexts(&atom_refs_by_context, &contexts)
                    else {
                        continue;
                    };
                    if shared_atom_refs.is_empty() {
                        continue;
                    }
                    let mut face_refs = Vec::new();
                    for omitted in 0..contexts.len() {
                        let face_contexts = contexts
                            .iter()
                            .enumerate()
                            .filter(|(index, _)| *index != omitted)
                            .map(|(_, context)| context.clone())
                            .collect::<BTreeSet<_>>();
                        let Some(face_ref) = face_by_contexts.get(&face_contexts) else {
                            face_refs.clear();
                            break;
                        };
                        face_refs.push(face_ref.clone());
                    }
                    if face_refs.len() != 4 {
                        continue;
                    }
                    tetrahedra.push(CoherenceTetrahedronV1 {
                        tetrahedron_id: format!(
                            "coherence-tetrahedron:{}:{}:{}:{}",
                            contexts[0], contexts[1], contexts[2], contexts[3]
                        ),
                        context_refs: contexts,
                        face_refs,
                        shared_atom_refs,
                    });
                }
            }
        }
    }
    tetrahedra.sort_by(|left, right| left.tetrahedron_id.cmp(&right.tetrahedron_id));
    tetrahedra
}

fn shared_atoms_for_contexts(
    atom_refs_by_context: &BTreeMap<String, BTreeSet<String>>,
    contexts: &[String],
) -> Option<Vec<String>> {
    let mut iter = contexts.iter();
    let first = iter.next()?;
    let mut shared = atom_refs_by_context.get(first)?.clone();
    for context in iter {
        let atoms = atom_refs_by_context.get(context)?;
        shared = shared.intersection(atoms).cloned().collect();
    }
    Some(shared.into_iter().collect())
}

fn coherence_witness_atoms<'a>(
    normalized: &'a NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Vec<&'a NormalizedAtomV2> {
    normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "coherence")
        .filter(|atom| {
            matches!(
                atom.predicate.as_str(),
                "tripleSection" | "coherenceSection" | "h2Section"
            )
        })
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .collect()
}

fn coherence_witnesses_for_faces(
    witness_atoms: &[&NormalizedAtomV2],
    faces: &[CoherenceFaceV1],
) -> Vec<CoherenceWitnessV1> {
    let mut witnesses = Vec::new();
    for atom in witness_atoms {
        for face in faces {
            if coherence_atom_marks_face(atom, face) {
                witnesses.push(CoherenceWitnessV1 {
                    atom_ref: atom.normalized_atom_id.clone(),
                    face_ref: face.face_id.clone(),
                    context_refs: face.context_refs.clone(),
                    source_refs: atom.source_refs.clone(),
                });
            }
        }
    }
    witnesses.sort_by(|left, right| {
        left.face_ref
            .cmp(&right.face_ref)
            .then_with(|| left.atom_ref.cmp(&right.atom_ref))
    });
    witnesses
}

fn coherence_atom_marks_face(atom: &NormalizedAtomV2, face: &CoherenceFaceV1) -> bool {
    let mut refs = atom.source_refs.iter().cloned().collect::<BTreeSet<_>>();
    refs.extend(atom.context_memberships.iter().cloned());
    refs.insert(atom.subject.clone());
    if let Some(object) = atom.object.as_deref() {
        refs.extend(parse_csv_values(object));
    }
    refs.contains(&face.face_id)
        || face.context_refs.iter().all(|context| {
            refs.contains(context)
                || refs.contains(unprefixed(context))
                || refs.contains(&format!("ctx:{}", unprefixed(context)))
        })
}

fn coherence_d1_rows(edges: &[CechEdgeV1], faces: &[CoherenceFaceV1]) -> Vec<Vec<u8>> {
    let edge_index = edges
        .iter()
        .enumerate()
        .map(|(index, edge)| (edge.edge_id.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut rows = vec![vec![0u8; edges.len()]; faces.len()];
    for (row, face) in faces.iter().enumerate() {
        for edge_ref in &face.edge_refs {
            if let Some(column) = edge_index.get(edge_ref) {
                rows[row][*column] ^= 1;
            }
        }
    }
    rows
}

fn coherence_d2_rows(
    faces: &[CoherenceFaceV1],
    tetrahedra: &[CoherenceTetrahedronV1],
) -> Vec<Vec<u8>> {
    let face_index = faces
        .iter()
        .enumerate()
        .map(|(index, face)| (face.face_id.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut rows = vec![vec![0u8; faces.len()]; tetrahedra.len()];
    for (row, tetrahedron) in tetrahedra.iter().enumerate() {
        for face_ref in &tetrahedron.face_refs {
            if let Some(column) = face_index.get(face_ref) {
                rows[row][*column] ^= 1;
            }
        }
    }
    rows
}

fn vector_in_span_f2(rows: &[Vec<u8>], vector: &[u8]) -> bool {
    if rows.len() != vector.len() {
        return false;
    }
    if vector.iter().all(|value| *value == 0) {
        return true;
    }
    let rank = matrix_rank_f2(rows.to_vec());
    let mut augmented = rows.to_vec();
    for (row, value) in augmented.iter_mut().zip(vector.iter()) {
        row.push(*value);
    }
    matrix_rank_f2(augmented) == rank
}

fn h2_representative_f2(
    d2_rows: &[Vec<u8>],
    d1_rows: &[Vec<u8>],
    face_count: usize,
) -> Option<Vec<u8>> {
    nullspace_basis_f2(d2_rows, face_count)
        .into_iter()
        .find(|candidate| !vector_in_span_f2(d1_rows, candidate))
}

fn nullspace_basis_f2(rows: &[Vec<u8>], columns: usize) -> Vec<Vec<u8>> {
    let mut rref = rows
        .iter()
        .map(|row| {
            let mut normalized = vec![0u8; columns];
            for (column, value) in row.iter().take(columns).enumerate() {
                normalized[column] = value & 1;
            }
            normalized
        })
        .collect::<Vec<_>>();
    let mut pivot_columns = Vec::new();
    let mut pivot_row = 0usize;

    for column in 0..columns {
        let Some(row) = (pivot_row..rref.len()).find(|row| rref[*row][column] == 1) else {
            continue;
        };
        rref.swap(pivot_row, row);
        for row in 0..rref.len() {
            if row != pivot_row && rref[row][column] == 1 {
                for entry in column..columns {
                    rref[row][entry] ^= rref[pivot_row][entry];
                }
            }
        }
        pivot_columns.push(column);
        pivot_row += 1;
        if pivot_row == rref.len() {
            break;
        }
    }

    let pivot_set = pivot_columns.iter().copied().collect::<BTreeSet<_>>();
    (0..columns)
        .filter(|column| !pivot_set.contains(column))
        .map(|free_column| {
            let mut vector = vec![0u8; columns];
            vector[free_column] = 1;
            for (row, pivot_column) in pivot_columns.iter().enumerate() {
                if rref[row][free_column] == 1 {
                    vector[*pivot_column] = 1;
                }
            }
            vector
        })
        .collect()
}

fn coherence_representative_json(cochain: &[u8], faces: &[CoherenceFaceV1]) -> Vec<Value> {
    faces
        .iter()
        .zip(cochain.iter())
        .filter(|(_, value)| **value == 1)
        .map(|(face, _)| {
            json!({
                "faceRef": face.face_id,
                "contextRefs": face.context_refs,
                "sharedAtomRefs": face.shared_atom_refs
            })
        })
        .collect::<Vec<_>>()
}

fn sorted_pair(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}

#[allow(clippy::too_many_arguments)]
fn coherence_invariant_json(
    profile: &MeasurementProfileV1,
    status: &str,
    method_status: &str,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    faces: &[CoherenceFaceV1],
    tetrahedra: &[CoherenceTetrahedronV1],
    witnesses: &[CoherenceWitnessV1],
    cochain: &[u8],
    rank_d1: usize,
    rank_ker_d2: usize,
    h2_dimension: usize,
    d2_row_count: usize,
    cocycle_gate_passed: bool,
    representative: Vec<Value>,
) -> Value {
    json!({
        "invariantId": format!("coherence-obstruction:{}", profile.profile_id),
        "evaluator": "ag.coherence-obstruction",
        "method": "finite-f2-h2-coherence@1",
        "status": status,
        "methodStatus": method_status,
        "claimScope": "selected-cover banded abelian F2 H2 coherence calculation",
        "selectedCoverRef": profile.cover_ref,
        "coefficient": profile.coefficient,
        "cohomologyQuotient": "ker d^2/im d^1",
        "contextCount": selected_contexts.len(),
        "edgeCount": edges.len(),
        "faceCount": faces.len(),
        "tetrahedronCount": tetrahedra.len(),
        "rankD1": rank_d1,
        "rankKerD2": rank_ker_d2,
        "h2Dimension": h2_dimension,
        "d2RowCount": d2_row_count,
        "cocycleGate": {
            "condition": "d2 h = 0",
            "passed": cocycle_gate_passed
        },
        "faces": faces.iter().enumerate().map(|(index, face)| json!({
            "faceId": face.face_id,
            "contextRefs": face.context_refs,
            "edgeRefs": face.edge_refs,
            "sharedAtomRefs": face.shared_atom_refs,
            "cochainValue": cochain.get(index).copied()
        })).collect::<Vec<_>>(),
        "tetrahedra": tetrahedra.iter().map(|tetrahedron| json!({
            "tetrahedronId": tetrahedron.tetrahedron_id,
            "contextRefs": tetrahedron.context_refs,
            "faceRefs": tetrahedron.face_refs,
            "sharedAtomRefs": tetrahedron.shared_atom_refs
        })).collect::<Vec<_>>(),
        "coherenceWitnesses": witnesses.iter().map(|witness| json!({
            "atomRef": witness.atom_ref,
            "faceRef": witness.face_ref,
            "contextRefs": witness.context_refs,
            "sourceRefs": witness.source_refs
        })).collect::<Vec<_>>(),
        "representative": representative,
        "nonConclusions": [
            "This is cover-relative H2 over banded abelian F2, not a non-abelian gerbe verdict.",
            "H1 Cech verdict rows are not changed by this evaluator."
        ]
    })
}

fn cover_nerve_projection_v1(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
    cover_ref: &str,
) -> Value {
    let context_atom_refs = context_atom_refs(normalized, selected_contexts);
    let vertices = selected_contexts
        .iter()
        .map(|context| {
            json!({
                "contextRef": context,
                "atomRefs": context_atom_refs.get(context).cloned().unwrap_or_default(),
                "objectKind": "nerveVertex"
            })
        })
        .collect::<Vec<_>>();
    let edge_rows = edges
        .iter()
        .map(|edge| {
            json!({
                "edgeId": edge.edge_id,
                "sourceContextRef": edge.source_context,
                "targetContextRef": edge.target_context,
                "value": edge.value,
                "supportAtomRefs": edge.support_atom_refs,
                "sectionObservation": if edge.observed { "observed" } else { "not_observed" },
                "objectKind": "nerveEdge",
                "source": "selected cover restriction edge"
            })
        })
        .collect::<Vec<_>>();
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let mut edge_by_pair = BTreeMap::new();
    for edge in edges {
        edge_by_pair.insert(
            (edge.source_context.clone(), edge.target_context.clone()),
            edge.edge_id.clone(),
        );
        edge_by_pair.insert(
            (edge.target_context.clone(), edge.source_context.clone()),
            edge.edge_id.clone(),
        );
    }
    let atom_refs_by_context = normalized
        .contexts
        .iter()
        .filter(|context| selected.contains(&context.normalized_context_id))
        .map(|context| {
            (
                context.normalized_context_id.clone(),
                context.atom_ids.iter().cloned().collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut faces = Vec::new();
    for left in 0..selected_contexts.len() {
        for middle in left + 1..selected_contexts.len() {
            for right in middle + 1..selected_contexts.len() {
                let contexts = [
                    selected_contexts[left].clone(),
                    selected_contexts[middle].clone(),
                    selected_contexts[right].clone(),
                ];
                let Some(left_atoms) = atom_refs_by_context.get(&contexts[0]) else {
                    continue;
                };
                let Some(middle_atoms) = atom_refs_by_context.get(&contexts[1]) else {
                    continue;
                };
                let Some(right_atoms) = atom_refs_by_context.get(&contexts[2]) else {
                    continue;
                };
                let shared_atom_refs = left_atoms
                    .intersection(middle_atoms)
                    .cloned()
                    .collect::<BTreeSet<_>>()
                    .intersection(right_atoms)
                    .cloned()
                    .collect::<Vec<_>>();
                if shared_atom_refs.is_empty() {
                    continue;
                }
                let edge_refs = [
                    edge_by_pair
                        .get(&(contexts[0].clone(), contexts[1].clone()))
                        .cloned(),
                    edge_by_pair
                        .get(&(contexts[0].clone(), contexts[2].clone()))
                        .cloned(),
                    edge_by_pair
                        .get(&(contexts[1].clone(), contexts[2].clone()))
                        .cloned(),
                ]
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
                faces.push(json!({
                    "faceId": format!("nerve-face:{}:{}:{}", contexts[0], contexts[1], contexts[2]),
                    "coverRef": cover_ref,
                    "contextRefs": contexts,
                    "edgeRefs": edge_refs,
                    "sharedAtomRefs": shared_atom_refs,
                    "objectKind": "nerveTriangle",
                    "source": "selected cover triple overlap with shared atom refs",
                    "coherenceClaim": "not_visualized"
                }));
            }
        }
    }
    json!({
        "coverRef": cover_ref,
        "vertices": vertices,
        "edges": edge_rows,
        "faces": faces,
        "faceSource": "selected cover triple-overlap sharedAtomRefs recorded in archsig-measurement-packet/v0.5.4; not inferred by the viewer",
        "h2CoherenceVisualized": false
    })
}

fn project_h2_coherence_to_cover_nerve(
    mut cover_nerve_projection: Value,
    packet: &ArchSigMeasurementPacketV1,
) -> Value {
    let Some(coherence_row) = packet
        .structural_verdict
        .iter()
        .find(|row| row.evaluator == "ag.coherence-obstruction")
    else {
        return cover_nerve_projection;
    };
    if coherence_row.verdict != "measured_zero" && coherence_row.verdict != "measured_nonzero" {
        return cover_nerve_projection;
    }
    let Some(coherence_invariant) = packet
        .computed_invariants
        .iter()
        .find(|invariant| invariant["evaluator"] == "ag.coherence-obstruction")
    else {
        return cover_nerve_projection;
    };

    let structural_ref = structural_verdict_ref(coherence_row);
    let representative_contexts = coherence_invariant["representative"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(context_key)
        .collect::<BTreeSet<_>>();
    let measured_faces = coherence_invariant["faces"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|face| {
            let key = context_key(face)?;
            let cochain_value = face["cochainValue"].as_u64().unwrap_or_default();
            Some((key, cochain_value))
        })
        .collect::<BTreeMap<_, _>>();

    let mut visualized = false;
    if let Some(faces) = cover_nerve_projection["faces"].as_array_mut() {
        for face in faces {
            let Some(key) = context_key(face) else {
                continue;
            };
            if !measured_faces.contains_key(&key) {
                continue;
            }
            let claim = if coherence_row.verdict == "measured_nonzero"
                && representative_contexts.contains(&key)
            {
                "measured_nonzero"
            } else {
                "measured_zero"
            };
            if let Some(object) = face.as_object_mut() {
                object.insert(
                    "coherenceClaim".to_string(),
                    Value::String(claim.to_string()),
                );
                object.insert("h2CoherenceVisualized".to_string(), Value::Bool(true));
                object.insert(
                    "structuralVerdictRef".to_string(),
                    Value::String(structural_ref.clone()),
                );
                object.insert(
                    "coherenceProjectionBoundary".to_string(),
                    Value::String(
                        "Projected from ag.coherence-obstruction; viewer adds no H2 verdict"
                            .to_string(),
                    ),
                );
            }
            visualized = true;
        }
    }
    if visualized {
        cover_nerve_projection["h2CoherenceVisualized"] = Value::Bool(true);
    }
    cover_nerve_projection
}

fn context_key(value: &Value) -> Option<String> {
    let mut contexts = value["contextRefs"]
        .as_array()?
        .iter()
        .filter_map(Value::as_str)
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    if contexts.is_empty() {
        return None;
    }
    contexts.sort();
    Some(contexts.join("|"))
}

fn empty_cover_nerve_projection_v1(cover_ref: &str, reason: &str) -> Value {
    json!({
        "coverRef": cover_ref,
        "vertices": [],
        "edges": [],
        "faces": [],
        "faceSource": reason,
        "h2CoherenceVisualized": false,
        "projectionStatus": "not_projected_missing_packet_cover_nerve"
    })
}

fn unprefixed(value: &str) -> &str {
    value
        .split_once(':')
        .map(|(_, suffix)| suffix)
        .unwrap_or(value)
}

fn graph_component_count(selected_contexts: &[String], edges: &[CechEdgeV1]) -> usize {
    let adjacency = adjacency_map(selected_contexts, edges);
    let mut visited = BTreeSet::new();
    let mut components = 0usize;
    for context in selected_contexts {
        if visited.contains(context) {
            continue;
        }
        components += 1;
        let mut stack = vec![context.clone()];
        while let Some(current) = stack.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            for next in adjacency.get(&current).into_iter().flatten() {
                if !visited.contains(next) {
                    stack.push(next.clone());
                }
            }
        }
    }
    components
}

fn edge_cochain_is_coboundary(selected_contexts: &[String], edges: &[CechEdgeV1]) -> bool {
    let adjacency = valued_adjacency_map(selected_contexts, edges);
    let mut potentials: BTreeMap<String, u8> = BTreeMap::new();
    for context in selected_contexts {
        if potentials.contains_key(context) {
            continue;
        }
        potentials.insert(context.clone(), 0);
        let mut stack = vec![context.clone()];
        while let Some(current) = stack.pop() {
            let current_value = *potentials.get(&current).unwrap_or(&0);
            for (next, edge_value) in adjacency.get(&current).into_iter().flatten() {
                let expected = current_value ^ *edge_value;
                match potentials.get(next) {
                    Some(existing) if *existing != expected => return false,
                    Some(_) => {}
                    None => {
                        potentials.insert(next.clone(), expected);
                        stack.push(next.clone());
                    }
                }
            }
        }
    }
    true
}

fn adjacency_map(
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
) -> BTreeMap<String, Vec<String>> {
    let mut adjacency = selected_contexts
        .iter()
        .map(|context| (context.clone(), Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for edge in edges {
        adjacency
            .entry(edge.source_context.clone())
            .or_default()
            .push(edge.target_context.clone());
        adjacency
            .entry(edge.target_context.clone())
            .or_default()
            .push(edge.source_context.clone());
    }
    adjacency
}

fn valued_adjacency_map(
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
) -> BTreeMap<String, Vec<(String, u8)>> {
    let mut adjacency = selected_contexts
        .iter()
        .map(|context| (context.clone(), Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for edge in edges {
        adjacency
            .entry(edge.source_context.clone())
            .or_default()
            .push((edge.target_context.clone(), edge.value));
        adjacency
            .entry(edge.target_context.clone())
            .or_default()
            .push((edge.source_context.clone(), edge.value));
    }
    adjacency
}
