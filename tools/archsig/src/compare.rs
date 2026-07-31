use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::path::Path;

use serde::de::{DeserializeSeed, MapAccess, SeqAccess, Visitor};
use serde_json::{Map, Value, json};
use sha2::{Digest, Sha256};

use crate::{
    ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA, ARCHSIG_CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED, ARCHSIG_COMPARISON_REPORT_V1_SCHEMA,
    ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA,
    ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA, ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
    ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY, ArchSigMeasurementPacketV1,
    NORMALIZED_ARCHMAP_V2_SCHEMA, NormalizedArchMapV2, validate_measurement_packet_value_v1,
};

const RECORD_DISCIPLINE: &str = "Comparison is a record-level juxtaposition of two ArchSig runs. ArchSig derives a class-zero reading from the selected normalized ArchMap covers when each fine context has a unique observed coarse containment path.";

pub fn build_comparison_artifacts_v1(
    base_run: &Path,
    head_run: &Path,
) -> Result<(Value, Value), Box<dyn Error>> {
    let base_manifest = read_run_json(base_run, "archsig-run-manifest.json")?;
    let head_manifest = read_run_json(head_run, "archsig-run-manifest.json")?;
    require_schema(
        &base_manifest,
        ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
        "base run manifest",
    )?;
    require_schema(
        &head_manifest,
        ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
        "head run manifest",
    )?;
    validate_run_manifest_shape(&base_manifest, "base run manifest")?;
    validate_run_manifest_shape(&head_manifest, "head run manifest")?;
    validate_component_fingerprints(&base_manifest, "base run manifest")?;
    validate_component_fingerprints(&head_manifest, "head run manifest")?;
    let base_normalized = read_run_json(base_run, "normalized-archmap.json")?;
    let head_normalized = read_run_json(head_run, "normalized-archmap.json")?;
    require_schema(
        &base_normalized,
        NORMALIZED_ARCHMAP_V2_SCHEMA,
        "base normalized archmap",
    )?;
    require_schema(
        &head_normalized,
        NORMALIZED_ARCHMAP_V2_SCHEMA,
        "head normalized archmap",
    )?;
    let base_normalized_digest = validate_compare_normalized_archmap(
        &base_normalized,
        &base_manifest,
        "base normalized archmap",
    )?;
    let head_normalized_digest = validate_compare_normalized_archmap(
        &head_normalized,
        &head_manifest,
        "head normalized archmap",
    )?;
    let base_packet = read_run_json(base_run, "archsig-measurement-packet.json")?;
    let head_packet = read_run_json(head_run, "archsig-measurement-packet.json")?;
    require_schema(
        &base_packet,
        ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
        "base measurement packet",
    )?;
    require_schema(
        &head_packet,
        ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
        "head measurement packet",
    )?;
    validate_compare_packet(
        &base_packet,
        &base_manifest,
        "base measurement packet",
    )?;
    validate_compare_packet(
        &head_packet,
        &head_manifest,
        "head measurement packet",
    )?;

    let archmap_diff = build_archmap_diff(
        base_run,
        head_run,
        &base_normalized,
        &head_normalized,
        &base_normalized_digest,
        &head_normalized_digest,
    )?;
    let comparability = comparability(&base_manifest, &head_manifest);
    let cover_or_context_changed =
        diff_has_changes(&archmap_diff, "contexts") || diff_has_changes(&archmap_diff, "covers");
    let verdict_transitions = verdict_transitions(
        &base_packet,
        &head_packet,
        &archmap_diff,
        &comparability,
        cover_or_context_changed,
    );
    let conclusion_code = conclusion_code(&comparability, &verdict_transitions);
    let boundary_statements = comparison_boundaries(&comparability, cover_or_context_changed);
    let derived_refinement = derive_refinement(
        &base_manifest,
        &head_manifest,
        &base_packet,
        &head_packet,
        &base_normalized,
        &head_normalized,
    );
    let class_transport = class_transport(
        &base_packet,
        &head_packet,
        &comparability,
        &derived_refinement,
    );
    let profile_conclusion_code = (comparability["level"].as_str() == Some("not-comparable")
        && class_transport["status"] != "established")
        .then_some(ARCHSIG_TWO_PROFILES_REPORTED_SEPARATELY);

    let report = json!({
        "schema": ARCHSIG_COMPARISON_REPORT_V1_SCHEMA,
        "toolVersion": env!("CARGO_PKG_VERSION"),
        "conclusionCode": conclusion_code,
        "comparability": comparability,
        "discipline": RECORD_DISCIPLINE,
        "inputDigests": {
            "baseRun": run_digest(base_run, &base_manifest),
            "headRun": run_digest(head_run, &head_manifest)
        },
        "artifactRefs": {
            "archmapDiff": "archmap-diff.json",
            "baseMeasurementPacket": "base-run/archsig-measurement-packet.json",
            "headMeasurementPacket": "head-run/archsig-measurement-packet.json"
        },
        "independentConclusions": {
            "base": run_conclusion(&base_manifest, &base_packet),
            "head": run_conclusion(&head_manifest, &head_packet)
        },
        "verdictTransitions": verdict_transitions,
        "boundaryStatements": boundary_statements,
        "classTransport": class_transport,
        "residualDifferenceReading": derived_residual_difference_reading(
            &base_packet,
            &head_packet,
            &comparability,
        ),
        "profileConclusionCode": profile_conclusion_code,
        "nonConclusions": [
            "Comparison report records run-local verdict rows and deterministic ArchMap diff intersections.",
            "Comparison report does not infer class transport, obstruction identity transport, repair causality, or semantic equivalence beyond the derived class-zero predicate and the two run records.",
            "Cover or context changes are boundary data and map to other_transition for gate policy evaluation."
        ]
    });
    Ok((archmap_diff, report))
}


/// 同一複体上の 2 run の導出 residual の差が delta0(h) の像に入るかを記録する。
/// 第X部 定義2.3 の B^1=im(delta0)を選択複体上で有限検査し、
/// 修理成功の判定ではない。修理の成立は head run 自身の residual 測定が語る。
fn packet_residual_derivation(packet: &Value) -> Option<&Value> {
    packet
        .get("computedInvariants")?
        .as_array()?
        .iter()
        .find(|invariant| {
            invariant.get("invariantId").and_then(Value::as_str)
                == Some("saga-descent:residual-derivation")
                && invariant["residualDerivation"]["derived"] == Value::Bool(true)
        })
        .map(|invariant| &invariant["residualDerivation"])
}

fn derivation_edges(derivation: &Value) -> Option<Vec<(String, String, String, u8)>> {
    derivation["edges"]
        .as_array()?
        .iter()
        .map(|edge| {
            Some((
                edge.get("overlapRef")?.as_str()?.to_string(),
                edge.get("leftContextRef")?.as_str()?.to_string(),
                edge.get("rightContextRef")?.as_str()?.to_string(),
                u8::try_from(edge.get("value")?.as_u64()?).ok()?,
            ))
        })
        .collect()
}

fn derived_residual_difference_reading(
    base_packet: &Value,
    head_packet: &Value,
    comparability: &Value,
) -> Value {
    const THEOREM_REF: &str = "part10/2.3";
    if !matches!(
        comparability["level"].as_str(),
        Some("identical") | Some("verdict-row")
    ) {
        return json!({
            "status": "silence_by_design",
            "reason": "runs_not_comparable",
            "theoremRef": THEOREM_REF,
            "nonConclusion": "residual difference membership in B1 is read only for comparable runs; a not-comparable pair shares no checked complex"
        });
    }
    let (Some(base_derivation), Some(head_derivation)) = (
        packet_residual_derivation(base_packet),
        packet_residual_derivation(head_packet),
    ) else {
        return json!({
            "status": "silence_by_design",
            "reason": "residual_derivation_not_recorded",
            "theoremRef": THEOREM_REF,
            "nonConclusion": "residual difference membership in B1 requires both runs to record a derived saga-descent residual"
        });
    };
    for provenance_key in ["coverRef", "mappedCoverRef", "lawSurfaceRef", "charts"] {
        if base_derivation[provenance_key] != head_derivation[provenance_key] {
            return json!({
                "status": "not_computed",
                "reason": "residual_derivation_provenance_mismatch",
                "theoremRef": THEOREM_REF,
                "mismatchedField": provenance_key,
                "nonConclusion": "residual difference membership in B1 is fail-closed when the two runs derive residuals under different covers, law surfaces, or chart sets"
            });
        }
    }
    let (Some(base_edges), Some(head_edges)) = (
        derivation_edges(base_derivation),
        derivation_edges(head_derivation),
    ) else {
        return json!({
            "status": "silence_by_design",
            "reason": "residual_derivation_not_recorded",
            "theoremRef": THEOREM_REF,
            "nonConclusion": "residual difference membership in B1 requires both runs to record a derived saga-descent residual"
        });
    };
    let base_map = base_edges
        .iter()
        .map(|(overlap, left, right, value)| ((overlap.clone(), left.clone(), right.clone()), *value))
        .collect::<BTreeMap<_, _>>();
    let head_map = head_edges
        .iter()
        .map(|(overlap, left, right, value)| ((overlap.clone(), left.clone(), right.clone()), *value))
        .collect::<BTreeMap<_, _>>();
    if base_map.keys().collect::<BTreeSet<_>>() != head_map.keys().collect::<BTreeSet<_>>() {
        return json!({
            "status": "not_computed",
            "reason": "residual_complexes_do_not_match",
            "theoremRef": THEOREM_REF,
            "nonConclusion": "residual difference membership in B1 is fail-closed when the two runs derive residuals over different overlap complexes"
        });
    }
    let overlap_refs = base_map
        .keys()
        .map(|(overlap, _, _)| overlap.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let provenance = json!({
        "coverRef": base_derivation["coverRef"],
        "lawSurfaceRef": base_derivation["lawSurfaceRef"],
        "overlapComplex": { "overlapRefs": overlap_refs }
    });
    let mut charts = BTreeSet::new();
    for (_, left, right, _) in &base_edges {
        charts.insert(left.clone());
        charts.insert(right.clone());
    }
    let charts = charts.into_iter().collect::<Vec<_>>();
    let chart_index = charts
        .iter()
        .enumerate()
        .map(|(index, chart)| (chart.as_str(), index))
        .collect::<BTreeMap<_, _>>();
    let mut rows = Vec::new();
    let mut delta_support = Vec::new();
    for (key, base_value) in &base_map {
        let (overlap, left, right) = key;
        let delta = base_value ^ head_map[key];
        if delta == 1 {
            delta_support.push(overlap.clone());
        }
        let mut row = vec![0u8; charts.len() + 1];
        row[chart_index[left.as_str()]] ^= 1;
        row[chart_index[right.as_str()]] ^= 1;
        row[charts.len()] = delta;
        rows.push(row);
    }
    if delta_support.is_empty() {
        return json!({
            "status": "no_residual_change",
            "derived": true,
            "theoremRef": THEOREM_REF,
            "deltaSupport": [],
            "provenance": provenance
        });
    }
    match crate::saga::solve_f2(rows, charts.len()) {
        Some(solution) => json!({
            "status": "difference_in_B1",
            "derived": true,
            "equation": "delta0(h) = r_base XOR r_head",
            "theoremRef": THEOREM_REF,
            "inB1": true,
            "deltaSupport": delta_support,
            "witnessChartAssignment": charts
                .iter()
                .enumerate()
                .map(|(index, chart)| json!({
                    "chartRef": chart,
                    "parity": solution[index]
                }))
                .collect::<Vec<_>>(),
            "provenance": provenance,
            "reading": "the difference of the two runs' derived residuals is delta0(h) on the shared overlap complex; this records membership in B1, while repair success is read from the head run's own residual measurements"
        }),
        None => json!({
            "status": "difference_not_in_B1",
            "derived": true,
            "equation": "delta0(h) = r_base XOR r_head",
            "theoremRef": THEOREM_REF,
            "reason": "delta_not_a_boundary_within_selected_complex",
            "inB1": false,
            "deltaSupport": delta_support,
            "provenance": provenance,
            "nonConclusion": "the difference of the two runs' derived residuals is not in B1 on the shared overlap complex"
        }),
    }
}

fn class_transport(
    base_packet: &Value,
    head_packet: &Value,
    comparability: &Value,
    derived_refinement: &Value,
) -> Value {
    if derived_refinement["status"] != "established" {
        return json!({
            "status": "not_computed",
            "conclusionCode": Value::Null,
            "reason": derived_refinement["reason"],
            "readingKind": "derived-class-zero-preservation@1",
            "recordComparability": comparability["level"],
            "derivedRefinement": derived_refinement,
            "boundaryStatement": {
                "kind": "class_zero_transport_not_derived",
                "scopeRefs": ["comparison:run-pair"],
                "reason": derived_refinement["reason"],
                "text": "ArchSig did not derive a coarse-to-fine containment relation from the two selected normalized ArchMap covers."
            }
        });
    }
    let base_nonzero = match derived_class_nonzero(base_packet, "base") {
        Ok(nonzero) => nonzero,
        Err(reason) => {
            return class_transport_failure(
                comparability,
                derived_refinement,
                &format!("base_{reason}"),
                "The coarse run did not record a validated derived residual class certificate.",
            );
        }
    };
    let head_nonzero = match derived_class_nonzero(head_packet, "head") {
        Ok(nonzero) => nonzero,
        Err(reason) => {
            return class_transport_failure(
                comparability,
                derived_refinement,
                &format!("head_{reason}"),
                "The fine run did not record a validated derived residual class certificate.",
            );
        }
    };
    let zero_preserved = !base_nonzero && !head_nonzero;
    json!({
        "status": if zero_preserved { "established" } else { "not_computed" },
        "conclusionCode": zero_preserved.then_some(ARCHSIG_CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT),
        "readingKind": "derived-class-zero-preservation@1",
        "direction": "coarse-to-fine",
        "recordComparability": comparability["level"],
        "comparabilityBasis": "derived_from_normalized_archmap_context_restrictions_and_selected_covers",
        "runBinding": derived_refinement["runBinding"],
        "derivedRefinement": derived_refinement,
        "reason": if zero_preserved { Value::Null } else { json!("derived_class_zero_predicate_not_preserved") },
        "sourceClassNonZero": base_nonzero,
        "targetClassNonZero": head_nonzero,
        "zeroPreserved": zero_preserved,
        "boundaryStatement": if zero_preserved { Value::Null } else { json!({
            "kind": "class_zero_transport_not_established",
            "scopeRefs": ["comparison:run-pair"],
            "reason": "derived_class_zero_predicate_not_preserved",
            "text": "The derived coarse-to-fine reading is emitted only when both derived residual classes are zero."
        }) },
        "nonConclusion": "the reading is limited to the derived residual class zero predicate under the selected coarse-to-fine cover relation"
    })
}

fn class_transport_failure(
    comparability: &Value,
    derived_refinement: &Value,
    reason: &str,
    text: &str,
) -> Value {
    json!({
        "status": "not_computed",
        "conclusionCode": Value::Null,
        "reason": reason,
        "readingKind": "derived-class-zero-preservation@1",
        "recordComparability": comparability["level"],
        "derivedRefinement": derived_refinement,
        "boundaryStatement": {
            "kind": "class_zero_transport_not_derived",
            "scopeRefs": ["comparison:run-pair"],
            "reason": reason,
            "text": text
        }
    })
}

fn derived_class_nonzero(packet: &Value, side: &str) -> Result<bool, String> {
    let invariants = packet
        .get("computedInvariants")
        .and_then(Value::as_array)
        .ok_or_else(|| format!("{side}_class_invariants_missing"))?;
    let class_invariants = invariants
        .iter()
        .filter(|invariant| invariant.get("invariantId").and_then(Value::as_str)
            == Some("saga-descent:residual-class"))
        .collect::<Vec<_>>();
    let [invariant] = class_invariants.as_slice() else {
        return Err(format!("{side}_class_certificate_missing_or_ambiguous"));
    };
    if invariant.get("evaluator").and_then(Value::as_str) != Some("ag.saga-descent")
        || invariant.get("kind").and_then(Value::as_str) != Some("residual-class-support")
        || !invariant
            .get("suppliedSlots")
            .and_then(Value::as_array)
            .is_some_and(|slots| {
                slots.iter().any(|slot| slot == "complex.charts")
                    && slots.iter().any(|slot| slot == "complex.overlaps")
            })
    {
        return Err(format!("{side}_class_certificate_owner_invalid"));
    }
    let support = invariant
        .get("residualClassSupport")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{side}_class_certificate_missing"))?;
    if support.get("basis").and_then(Value::as_str) != Some("Z1/B1")
        || support.get("quotient").and_then(Value::as_str) != Some("Z1/B1")
        || !support
            .get("representative")
            .and_then(Value::as_array)
            .is_some_and(|representative| !representative.is_empty())
    {
        return Err(format!("{side}_class_certificate_shape_invalid"));
    }
    let component = support
        .get("component")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{side}_class_certificate_component_missing"))?;
    for field in ["chartRefs", "overlapRefs"] {
        if !component
            .get(field)
            .and_then(Value::as_array)
            .is_some_and(|refs| !refs.is_empty() && refs.iter().all(Value::is_string))
        {
            return Err(format!("{side}_class_certificate_component_invalid"));
        }
    }
    let cocycle = support
        .get("cocycle")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{side}_class_certificate_cocycle_missing"))?;
    if cocycle.get("checked").and_then(Value::as_bool) != Some(true)
        || cocycle.get("deltaOne").and_then(Value::as_str) != Some("zero")
        || cocycle.get("certificateKind").and_then(Value::as_str)
            != Some("checked-triple-cocycle-zero")
        || !cocycle
            .get("tripleOverlapRefs")
            .and_then(Value::as_array)
            .is_some_and(|refs| {
                !refs.is_empty()
                    && refs.iter().all(|triple| {
                        triple
                            .get("tripleRef")
                            .and_then(Value::as_str)
                            .is_some_and(|value| !value.is_empty())
                            && triple
                                .get("overlapRefs")
                                .and_then(Value::as_array)
                                .is_some_and(|overlaps| {
                                    overlaps.len() == 3 && overlaps.iter().all(Value::is_string)
                                })
                    })
            })
    {
        return Err(format!("{side}_class_certificate_cocycle_invalid"));
    }
    let nonzero = support
        .get("nonZero")
        .and_then(Value::as_bool)
        .ok_or_else(|| format!("{side}_class_nonzero_missing"))?;
    let verdict = packet
        .get("structuralVerdict")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter(|row| {
            row.get("evaluator").and_then(Value::as_str) == Some("ag.saga-descent")
                && row.get("law").and_then(Value::as_str) == Some("saga.residual-class")
        })
        .collect::<Vec<_>>();
    let [verdict] = verdict.as_slice() else {
        return Err(format!("{side}_class_verdict_missing_or_ambiguous"));
    };
    if verdict["verdictData"]["inScope"].as_bool() != Some(true)
        || verdict["verdictData"]["certRef"]
            .as_str()
            != Some("computedInvariants/saga-descent:residual-class")
        || verdict["target"]["classRef"].as_str()
            != Some("computedInvariants/saga-descent:residual-class")
        || !verdict["evidence"]["computedInvariantRefs"]
            .as_array()
            .is_some_and(|refs| refs.iter().any(|reference| reference == "saga-descent:residual-class"))
    {
        return Err(format!("{side}_class_certificate_provenance_invalid"));
    }
    let verdict_nonzero = verdict["verdictData"]["nonZero"].as_bool();
    let expected_verdict = if nonzero { "measured_nonzero" } else { "measured_zero" };
    if verdict["verdict"].as_str() != Some(expected_verdict)
        || verdict_nonzero != Some(nonzero)
        || verdict["verdictData"]["zero"].as_bool() != Some(!nonzero)
    {
        return Err(format!("{side}_class_certificate_verdict_mismatch"));
    }
    Ok(nonzero)
}

fn derive_refinement(
    base_manifest: &Value,
    head_manifest: &Value,
    base_packet: &Value,
    head_packet: &Value,
    base_normalized: &Value,
    head_normalized: &Value,
) -> Value {
    let (coarse_site_ref, coarse_cover_ref, coarse_cover) =
        match selected_normalized_cover(base_normalized, base_packet, "coarse") {
            Ok(selection) => selection,
            Err((reason, detail)) => return refinement_failure(reason, &detail),
        };
    let (fine_site_ref, fine_cover_ref, fine_cover) =
        match selected_normalized_cover(head_normalized, head_packet, "fine") {
            Ok(selection) => selection,
            Err((reason, detail)) => return refinement_failure(reason, &detail),
        };
    let _coarse_context_map = match validated_context_map(base_normalized, "coarse") {
        Ok(contexts) => contexts,
        Err((reason, detail)) => return refinement_failure(reason, &detail),
    };
    let fine_context_map = match validated_context_map(head_normalized, "fine") {
        Ok(contexts) => contexts,
        Err((reason, detail)) => return refinement_failure(reason, &detail),
    };
    let coarse_contexts = cover_contexts(coarse_cover);
    let fine_contexts = cover_contexts(fine_cover);
    if coarse_contexts.is_empty() {
        return refinement_failure("coarse_selected_cover_empty", "coarse selected cover has no observed contexts");
    }
    if fine_contexts.is_empty() {
        return refinement_failure("fine_selected_cover_empty", "fine selected cover has no observed contexts");
    }
    let mut context_rows = Vec::new();
    for fine_context in &fine_contexts {
        let candidates = if coarse_contexts.contains(fine_context) {
            vec![(fine_context.clone(), vec![vec![fine_context.clone()]])]
        } else {
            coarse_contexts
                .iter()
                .filter_map(|coarse_context| {
                    let paths = context_paths(&fine_context_map, fine_context, coarse_context);
                    (!paths.is_empty()).then(|| (coarse_context.clone(), paths))
                })
                .collect::<Vec<_>>()
        };
        match candidates.as_slice() {
            [] => {
                return refinement_failure(
                    "fine_chart_not_contained_in_coarse_cover",
                    &format!("fine context {fine_context} has no observed restriction path to a coarse context"),
                );
            }
            [(coarse_context, paths)] if paths.len() == 1 => context_rows.push(json!({
                "fineContextRef": fine_context,
                "coarseContextRef": coarse_context,
                "relation": if fine_context == coarse_context { "identity" } else { "observed_restriction_path" },
                "restrictionPath": paths[0]
            })),
            [(coarse_context, _)] => {
                return refinement_failure(
                    "fine_chart_has_ambiguous_restriction_paths",
                    &format!("fine context {fine_context} has multiple observed restriction paths to {coarse_context}"),
                );
            }
            _ => {
                return refinement_failure(
                    "fine_chart_has_ambiguous_coarse_containment",
                    &format!("fine context {fine_context} reaches multiple coarse contexts"),
                );
            }
        }
    }
    let coarse_digest = digest_at(base_manifest, "siteCoverDigest");
    let fine_digest = digest_at(head_manifest, "siteCoverDigest");
    json!({
        "status": "established",
        "direction": "coarse-to-fine",
        "basis": "MeasurementProfile-selected normalized ArchMap covers and unique observed context restriction paths",
        "siteRef": {
            "coarse": coarse_site_ref,
            "fine": fine_site_ref
        },
        "coarseCoverRef": coarse_cover_ref,
        "fineCoverRef": fine_cover_ref,
        "contextMap": context_rows,
        "runBinding": {
            "coarse": {
                "siteCoverDigest": coarse_digest,
                "side": "base",
                "measurementProfile": {
                    "siteRef": coarse_site_ref,
                    "coverRef": base_packet["profile"]["coverRef"],
                    "profileId": base_packet["profile"]["profileId"]
                }
            },
            "fine": {
                "siteCoverDigest": fine_digest,
                "side": "head",
                "measurementProfile": {
                    "siteRef": fine_site_ref,
                    "coverRef": head_packet["profile"]["coverRef"],
                    "profileId": head_packet["profile"]["profileId"]
                }
            }
        }
    })
}

fn selected_normalized_cover<'a>(
    normalized: &'a Value,
    packet: &Value,
    side: &str,
) -> Result<(String, String, &'a Value), (&'static str, String)> {
    let profile = packet
        .get("profile")
        .and_then(Value::as_object)
        .ok_or((
            "measurement_profile_missing",
            format!("{side} measurement packet has no profile object"),
        ))?;
    let site_ref = profile
        .get("siteRef")
        .and_then(Value::as_str)
        .filter(|value| !value.trim().is_empty())
        .ok_or((
            "measurement_profile_site_missing",
            format!("{side} measurement profile has no siteRef"),
        ))?;
    let cover_ref = profile
        .get("coverRef")
        .and_then(Value::as_str)
        .filter(|value| !value.trim().is_empty())
        .ok_or((
            "measurement_profile_cover_missing",
            format!("{side} measurement profile has no coverRef"),
        ))?;
    if site_ref != "archmap:/contexts" {
        let site_resolves = normalized
            .get("contexts")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .any(|context| {
                context.get("normalizedContextId").and_then(Value::as_str) == Some(site_ref)
                    || context.get("sourceContextId").and_then(Value::as_str) == Some(site_ref)
            });
        if !site_resolves {
            return Err((
                "measurement_profile_site_unresolved",
                format!("{side} measurement profile siteRef {site_ref} does not resolve in normalized ArchMap"),
            ));
        }
    }
    let matches = normalized
        .get("covers")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter(|cover| {
            (cover.get("normalizedCoverId").and_then(Value::as_str) == Some(cover_ref)
                || cover.get("sourceCoverId").and_then(Value::as_str) == Some(cover_ref))
                && cover.get("coverageStatus").and_then(Value::as_str)
                    == Some("selectedCandidate")
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [cover] => {
            let normalized_cover_ref = cover
                .get("normalizedCoverId")
                .and_then(Value::as_str)
                .ok_or((
                    "selected_cover_id_missing",
                    format!("{side} selected cover lacks normalizedCoverId"),
                ))?;
            Ok((site_ref.to_string(), normalized_cover_ref.to_string(), *cover))
        }
        [] => Err((
            "measurement_profile_cover_unresolved",
            format!("{side} measurement profile coverRef {cover_ref} does not resolve to a selectedCandidate cover"),
        )),
        _ => Err((
            "measurement_profile_cover_ambiguous",
            format!("{side} measurement profile coverRef {cover_ref} resolves to multiple covers"),
        )),
    }
}

fn cover_contexts(cover: &Value) -> BTreeSet<String> {
    cover
        .get("contextIds")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(ToOwned::to_owned)
        .collect()
}

fn validated_context_map(
    normalized: &Value,
    side: &str,
) -> Result<BTreeMap<String, Value>, (&'static str, String)> {
    let contexts = normalized
        .get("contexts")
        .and_then(Value::as_array)
        .ok_or((
            "normalized_contexts_missing",
            format!("{side} normalized ArchMap has no contexts array"),
        ))?;
    let mut map = BTreeMap::new();
    for context in contexts {
        let id = context
            .get("normalizedContextId")
            .and_then(Value::as_str)
            .filter(|value| !value.trim().is_empty())
            .ok_or((
                "normalized_context_id_missing",
                format!("{side} normalized context lacks normalizedContextId"),
            ))?;
        if map.insert(id.to_string(), context.clone()).is_some() {
            return Err((
                "normalized_context_id_duplicated",
                format!("{side} normalized ArchMap repeats context {id}"),
            ));
        }
    }
    for (id, context) in &map {
        let targets = context
            .get("restrictsTo")
            .and_then(Value::as_array)
            .ok_or((
                "normalized_context_restrictions_missing",
                format!("{side} normalized context {id} has no restrictsTo array"),
            ))?;
        for target in targets {
            let target = target.as_str().ok_or((
                "normalized_context_restriction_invalid",
                format!("{side} normalized context {id} has a non-string restrictsTo target"),
            ))?;
            if !map.contains_key(target) {
                return Err((
                    "normalized_context_restriction_unresolved",
                    format!("{side} normalized context {id} restrictsTo unknown context {target}"),
                ));
            }
        }
    }
    if has_context_cycle(&map) {
        return Err((
            "normalized_context_restriction_cycle",
            format!("{side} normalized context restrictions are cyclic"),
        ));
    }
    Ok(map)
}

fn has_context_cycle(contexts: &BTreeMap<String, Value>) -> bool {
    fn visit(
        current: &str,
        contexts: &BTreeMap<String, Value>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
    ) -> bool {
        if visiting.contains(current) {
            return true;
        }
        if !visited.insert(current.to_string()) {
            return false;
        }
        visiting.insert(current.to_string());
        let cycle = contexts[current]["restrictsTo"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .any(|next| visit(next, contexts, visiting, visited));
        visiting.remove(current);
        cycle
    }
    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    contexts
        .keys()
        .any(|id| visit(id, contexts, &mut visiting, &mut visited))
}

fn context_paths(
    contexts: &BTreeMap<String, Value>,
    start: &str,
    target: &str,
) -> Vec<Vec<String>> {
    fn walk(
        contexts: &BTreeMap<String, Value>,
        current: &str,
        target: &str,
        path: &mut Vec<String>,
        paths: &mut Vec<Vec<String>>,
    ) {
        if paths.len() >= 2 {
            return;
        }
        if current == target {
            paths.push(path.clone());
            return;
        }
        let mut nexts = contexts[current]["restrictsTo"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>();
        nexts.sort_unstable();
        for next in nexts {
            if path.iter().any(|item| item == next) {
                continue;
            }
            path.push(next.to_string());
            walk(contexts, next, target, path, paths);
            path.pop();
        }
    }
    if !contexts.contains_key(start) || !contexts.contains_key(target) {
        return Vec::new();
    }
    let mut path = vec![start.to_string()];
    let mut paths = Vec::new();
    walk(contexts, start, target, &mut path, &mut paths);
    paths
}

fn refinement_failure(reason: &str, detail: &str) -> Value {
    json!({
        "status": "not_computed",
        "reason": reason,
        "basis": "normalized ArchMap selected covers and observed context restriction paths",
        "detail": detail
    })
}

fn build_archmap_diff(
    base_run: &Path,
    head_run: &Path,
    base: &Value,
    head: &Value,
    base_normalized_digest: &str,
    head_normalized_digest: &str,
) -> Result<Value, Box<dyn Error>> {
    Ok(json!({
        "schema": ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA,
        "toolVersion": env!("CARGO_PKG_VERSION"),
        "basis": "deterministic JSON comparison of normalized-archmap/v0.5.4 sources, atoms, contexts, and covers",
        "inputDigests": {
            "baseNormalizedArchmap": {
                "path": artifact_ref(base_run, "normalized-archmap.json"),
                "sha256": base_normalized_digest
            },
            "headNormalizedArchmap": {
                "path": artifact_ref(head_run, "normalized-archmap.json"),
                "sha256": head_normalized_digest
            }
        },
        "sources": diff_sources(base, head),
        "atoms": diff_array_by_id(base, head, "atoms", "normalizedAtomId"),
        "contexts": diff_array_by_id(base, head, "contexts", "normalizedContextId"),
        "covers": diff_array_by_id(base, head, "covers", "normalizedCoverId"),
        "nonConclusions": [
            "ArchMap diff is computed from normalized artifacts; it is not an observation artifact.",
            "Diff operations are mechanical record intersections, not causal claims."
        ]
    }))
}

fn comparability(base: &Value, head: &Value) -> Value {
    let same_tool = text_at(base, &["toolVersion"]) == text_at(head, &["toolVersion"]);
    let same_archmap = digest_at(base, "archmap") == digest_at(head, "archmap");
    let same_law_policy = digest_at(base, "lawPolicy") == digest_at(head, "lawPolicy");
    let same_profile =
        digest_at(base, "profileFingerprint") == digest_at(head, "profileFingerprint");
    let same_cover = digest_at(base, "siteCoverDigest") == digest_at(head, "siteCoverDigest");
    let same_repair_plan = digest_at(base, "repairPlan") == digest_at(head, "repairPlan");
    let same_component_fingerprints = component_fingerprints_at(base)
        .zip(component_fingerprints_at(head))
        .is_some_and(|(base, head)| base == head);
    let same_law_surface = component_fingerprints_at(base).is_some()
        && component_fingerprints_at(head).is_some()
        && component_fingerprint_at(base, "lawSurface")
            == component_fingerprint_at(head, "lawSurface");
    let level = if same_tool
        && same_archmap
        && same_law_policy
        && same_profile
        && same_component_fingerprints
        && same_repair_plan
    {
        "identical"
    } else if same_tool
        && same_profile
        && same_cover
        && same_law_surface
        && same_component_fingerprints
    {
        "verdict-row"
    } else {
        "not-comparable"
    };
    json!({
        "level": level,
        "sameToolVersion": same_tool,
        "sameArchmapDigest": same_archmap,
        "sameLawPolicyDigest": same_law_policy,
        "sameProfileFingerprint": same_profile,
        "sameComponentFingerprints": same_component_fingerprints,
        "sameLawSurfaceFingerprint": same_law_surface,
        "sameSiteCoverDigest": same_cover,
        "sameRepairPlanDigest": same_repair_plan,
        "basis": "identical requires archmap, LawPolicy, law-surface, MeasurementProfile, and optional RepairPlan input digests plus tool version equality; verdict-row requires all three LawPolicy, law-surface, and MeasurementProfile component fingerprints, site cover digest, and tool version equality, while recording whether the optional RepairPlan digest changed"
    })
}

fn verdict_transitions(
    base_packet: &Value,
    head_packet: &Value,
    archmap_diff: &Value,
    comparability: &Value,
    cover_or_context_changed: bool,
) -> Vec<Value> {
    let base_rows = verdict_row_map(base_packet);
    let head_rows = verdict_row_map(head_packet);
    let keys = base_rows
        .keys()
        .chain(head_rows.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    keys.into_iter()
        .map(|key| {
            let base = base_rows.get(&key);
            let head = head_rows.get(&key);
            let base_verdict = base
                .and_then(|row| row.get("verdict").and_then(Value::as_str))
                .unwrap_or("absent");
            let head_verdict = head
                .and_then(|row| row.get("verdict").and_then(Value::as_str))
                .unwrap_or("absent");
            let (transition, category) = transition_kind(
                base_verdict,
                head_verdict,
                comparability,
                cover_or_context_changed,
            );
            json!({
                "rowKey": key,
                "baseRowRef": base.map(verdict_ref).unwrap_or(Value::Null),
                "headRowRef": head.map(verdict_ref).unwrap_or(Value::Null),
                "baseVerdict": base_verdict,
                "headVerdict": head_verdict,
                "transition": transition,
                "introducedByChangeCategory": category,
                "deltaRefs": delta_refs_for_row(&key, archmap_diff),
                "discipline": RECORD_DISCIPLINE
            })
        })
        .collect()
}

fn transition_kind(
    base: &str,
    head: &str,
    comparability: &Value,
    cover_or_context_changed: bool,
) -> (&'static str, &'static str) {
    if comparability["level"].as_str() == Some("not-comparable") || cover_or_context_changed {
        return ("other_transition", "other");
    }
    match (base, head) {
        ("absent", _) => ("new_recorded_row", "new"),
        (_, "absent") => ("removed_recorded_row", "removed"),
        ("measured_nonzero", "measured_zero") => {
            ("measured_obstruction_no_longer_recorded", "cleared")
        }
        ("measured_zero", "measured_nonzero") => {
            ("measured_obstruction_recorded_after_change", "new")
        }
        _ if base == head => ("preexisting_recorded_row", "preexisting"),
        _ => ("other_transition", "other"),
    }
}

fn conclusion_code(comparability: &Value, transitions: &[Value]) -> &'static str {
    if comparability["level"].as_str() == Some("not-comparable") {
        return ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA;
    }
    if transitions
        .iter()
        .any(|transition| transition["transition"] == "measured_obstruction_recorded_after_change")
    {
        return ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE;
    }
    if transitions
        .iter()
        .any(|transition| transition["transition"] == "measured_obstruction_no_longer_recorded")
    {
        return ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE;
    }
    ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED
}

fn comparison_boundaries(comparability: &Value, cover_or_context_changed: bool) -> Vec<Value> {
    let mut boundaries = Vec::new();
    if comparability["level"].as_str() == Some("not-comparable") || cover_or_context_changed {
        let kind = if cover_or_context_changed {
            "cover_changed_between_runs"
        } else {
            "runs_not_comparable_without_comparison_data"
        };
        boundaries.push(json!({
            "id": format!("boundary:comparison:{kind}"),
            "kind": kind,
            "reason": "record-level comparison data does not support class identity or causal transition claims outside classTransport's derived coarse-to-fine relation",
            "scopeRefs": ["comparison:run-pair"],
            "text": "Record transitions remain side by side; any class-zero reading is limited to classTransport's derived coarse-to-fine relation."
        }));
    }
    if comparability["sameRepairPlanDigest"] == Value::Bool(false) {
        boundaries.push(json!({
            "id": "boundary:comparison:repair-plan-changed-between-runs",
            "kind": "repair_plan_changed_between_runs",
            "reason": "the compared runs bind different RepairPlan input digests",
            "scopeRefs": ["comparison:run-pair"],
            "text": "Record-level verdict rows remain comparable under the shared policy, law-surface, profile, and site-cover contract; the RepairPlan change is recorded and does not establish causal repair."
        }));
    }
    boundaries
}

fn diff_sources(base: &Value, head: &Value) -> Value {
    let base_sources = source_refs(base);
    let head_sources = source_refs(head);
    diff_scalar_set(&base_sources, &head_sources, "source")
}

fn source_refs(value: &Value) -> BTreeSet<String> {
    ["atoms", "contexts", "covers"]
        .into_iter()
        .flat_map(|field| value[field].as_array().into_iter().flatten())
        .flat_map(|item| item["sourceRefs"].as_array().into_iter().flatten())
        .filter_map(Value::as_str)
        .map(str::to_string)
        .collect()
}

fn diff_scalar_set(base: &BTreeSet<String>, head: &BTreeSet<String>, kind: &str) -> Value {
    let added = head
        .difference(base)
        .map(|id| json!({ "op": "added", "kind": kind, "id": id }))
        .collect::<Vec<_>>();
    let removed = base
        .difference(head)
        .map(|id| json!({ "op": "removed", "kind": kind, "id": id }))
        .collect::<Vec<_>>();
    json!({
        "added": added,
        "removed": removed,
        "modified": []
    })
}

fn diff_array_by_id(base: &Value, head: &Value, field: &str, id_field: &str) -> Value {
    let base_items = map_by_id(base, field, id_field);
    let head_items = map_by_id(head, field, id_field);
    let keys = base_items
        .keys()
        .chain(head_items.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut added = Vec::new();
    let mut removed = Vec::new();
    let mut modified = Vec::new();
    for key in keys {
        match (base_items.get(&key), head_items.get(&key)) {
            (None, Some(head_value)) => {
                added.push(json!({ "op": "added", "kind": field, "id": key, "head": head_value }));
            }
            (Some(base_value), None) => {
                removed
                    .push(json!({ "op": "removed", "kind": field, "id": key, "base": base_value }));
            }
            (Some(base_value), Some(head_value))
                if canonical_value(base_value) != canonical_value(head_value) =>
            {
                modified.push(json!({
                    "op": "modified",
                    "kind": field,
                    "id": key,
                    "base": base_value,
                    "head": head_value
                }));
            }
            _ => {}
        }
    }
    json!({
        "added": added,
        "removed": removed,
        "modified": modified
    })
}

fn map_by_id(value: &Value, field: &str, id_field: &str) -> BTreeMap<String, Value> {
    value[field]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|item| {
            item[id_field]
                .as_str()
                .map(|id| (id.to_string(), item.clone()))
        })
        .collect()
}

fn diff_has_changes(diff: &Value, field: &str) -> bool {
    ["added", "removed", "modified"].into_iter().any(|op| {
        diff[field][op]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    })
}

fn verdict_row_map(packet: &Value) -> BTreeMap<String, Value> {
    packet["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|row| (row_key(row), row.clone()))
        .collect()
}

fn validate_compare_packet(
    packet: &Value,
    manifest: &Value,
    label: &str,
) -> Result<(), Box<dyn Error>> {
    serde_json::from_value::<ArchSigMeasurementPacketV1>(packet.clone())
        .map_err(|error| format!("{label} shape is invalid: {error}"))?;
    let failed = validate_measurement_packet_value_v1(packet)
        .into_iter()
        .any(|check| check.result == "fail");
    if failed {
        return Err(format!("{label} failed measurement packet validation").into());
    }
    if packet["structuralVerdict"]
        .as_array()
        .is_none_or(|rows| rows.is_empty())
    {
        return Err(format!("{label} must contain at least one structuralVerdict row").into());
    }
    validate_compare_run_contract(packet, manifest, label)?;
    validate_manifest_artifact_digest(packet, manifest, "measurementPacket", label)?;
    Ok(())
}

fn validate_compare_normalized_archmap(
    normalized_archmap: &Value,
    manifest: &Value,
    label: &str,
) -> Result<String, Box<dyn Error>> {
    let normalized: NormalizedArchMapV2 = serde_json::from_value(normalized_archmap.clone())
        .map_err(|error| format!("{label} shape is invalid: {error}"))?;
    let context_map = validated_context_map(normalized_archmap, label)
        .map_err(|(_, detail)| format!("{label} {detail}"))?;
    let mut source_context_ids = BTreeSet::new();
    for context in &normalized.contexts {
        if !source_context_ids.insert(context.source_context_id.as_str()) {
            return Err(format!("{label} repeats source context {}", context.source_context_id).into());
        }
    }
    let mut normalized_cover_ids = BTreeSet::new();
    let mut source_cover_ids = BTreeSet::new();
    for cover in &normalized.covers {
        if !normalized_cover_ids.insert(cover.normalized_cover_id.as_str()) {
            return Err(format!("{label} repeats normalized cover {}", cover.normalized_cover_id).into());
        }
        if !source_cover_ids.insert(cover.source_cover_id.as_str()) {
            return Err(format!("{label} repeats source cover {}", cover.source_cover_id).into());
        }
        for context_id in &cover.context_ids {
            if !context_map.contains_key(context_id) {
                return Err(format!(
                    "{label} cover {} references unknown context {}",
                    cover.normalized_cover_id, context_id
                )
                .into());
            }
        }
    }
    validate_compare_run_contract(normalized_archmap, manifest, label)?;
    validate_manifest_artifact_digest(normalized_archmap, manifest, "normalizedArchmap", label)
}

fn validate_compare_run_contract(
    artifact: &Value,
    manifest: &Value,
    label: &str,
) -> Result<(), Box<dyn Error>> {
    for field in ["toolVersion", "runId", "inputDigests", "componentFingerprints"] {
        if artifact.get(field) != manifest.get(field) {
            return Err(format!(
                "{label} {field} must match its run manifest provenance"
            )
            .into());
        }
    }
    Ok(())
}

fn validate_manifest_artifact_digest(
    artifact: &Value,
    manifest: &Value,
    artifact_key: &str,
    label: &str,
) -> Result<String, Box<dyn Error>> {
    let expected_digest = manifest["artifactDigests"][artifact_key]["sha256"]
        .as_str()
        .ok_or_else(|| format!("{label} run manifest requires artifactDigests.{artifact_key}.sha256"))?;
    let actual_digest = canonical_json_value_digest(artifact)?;
    if expected_digest != actual_digest {
        return Err(format!(
            "{label} digest does not match its run manifest artifactDigests.{artifact_key}.sha256"
        )
        .into());
    }
    Ok(actual_digest)
}

fn row_key(row: &Value) -> String {
    let evaluator = row["evaluator"].as_str().unwrap_or("unknown-evaluator");
    let law = row["law"].as_str().unwrap_or("unknown-law");
    let target = if row.get("target").is_some() {
        let mut target = row["target"].clone();
        if let Some(target_object) = target.as_object_mut() {
            target_object.remove("classRef");
        }
        canonical_value(&target)
    } else {
        row["verdictRef"]
            .as_str()
            .or_else(|| row["structuralVerdictRef"].as_str())
            .map(str::to_string)
            .unwrap_or_else(|| {
                row["verdictData"]["methodStatus"]
                    .as_str()
                    .or_else(|| row["methodStatus"].as_str())
                    .unwrap_or("unknown-target")
                    .to_string()
            })
    };
    format!("{evaluator}|{law}|{target}")
}

fn delta_refs_for_row(key: &str, archmap_diff: &Value) -> Vec<Value> {
    let tokens = key
        .split(|character: char| {
            !character.is_ascii_alphanumeric()
                && character != ':'
                && character != '-'
                && character != '_'
        })
        .filter(|token| !token.is_empty())
        .collect::<BTreeSet<_>>();
    let mut refs = Vec::new();
    for field in ["sources", "atoms", "contexts", "covers"] {
        for op in ["added", "removed", "modified"] {
            for item in archmap_diff[field][op].as_array().into_iter().flatten() {
                let id = item["id"].as_str().unwrap_or("");
                if tokens.contains(id) {
                    refs.push(json!({
                        "diffRef": format!("archmap-diff/{field}/{op}/{id}"),
                        "op": op,
                        "kind": field,
                        "id": id
                    }));
                }
            }
        }
    }
    refs
}

fn verdict_ref(row: &Value) -> Value {
    json!(
        row["verdictRef"]
            .as_str()
            .or_else(|| row["structuralVerdictRef"].as_str())
            .map(str::to_string)
            .unwrap_or_else(|| {
                format!(
                    "structuralVerdict/{}/{}/{}",
                    row["evaluator"].as_str().unwrap_or("unknown-evaluator"),
                    row["law"].as_str().unwrap_or("unknown-law"),
                    row["verdictData"]["methodStatus"]
                        .as_str()
                        .or_else(|| row["methodStatus"].as_str())
                        .unwrap_or("unknown-status")
                )
            })
    )
}

fn run_digest(run: &Path, manifest: &Value) -> Value {
    json!({
        "path": artifact_ref(run, "archsig-run-manifest.json"),
        "runId": manifest["runId"],
        "toolVersion": manifest["toolVersion"],
        "archmap": manifest["inputDigests"]["archmap"],
        "lawPolicy": manifest["inputDigests"]["lawPolicy"],
        "profileFingerprint": manifest["inputDigests"]["profileFingerprint"],
        "componentFingerprints": manifest["componentFingerprints"],
        "siteCoverDigest": manifest["inputDigests"]["siteCoverDigest"],
        "repairPlan": manifest["inputDigests"]["repairPlan"],
        "normalizedArchmap": manifest["artifactDigests"]["normalizedArchmap"],
        "measurementPacket": manifest["artifactDigests"]["measurementPacket"]
    })
}

fn run_conclusion(manifest: &Value, packet: &Value) -> Value {
    let verdict_counts = packet["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|row| row["verdict"].as_str())
        .fold(BTreeMap::<String, usize>::new(), |mut counts, verdict| {
            *counts.entry(verdict.to_string()).or_default() += 1;
            counts
        });
    json!({
        "runId": manifest["runId"],
        "mode": manifest["mode"],
        "conclusionCode": manifest["conclusionCode"],
        "structuralVerdictCounts": verdict_counts
    })
}

fn digest_at(value: &Value, key: &str) -> Option<String> {
    value["inputDigests"][key]["sha256"]
        .as_str()
        .map(str::to_string)
}

fn text_at(value: &Value, path: &[&str]) -> Option<String> {
    let mut current = value;
    for key in path {
        current = current.get(*key)?;
    }
    current.as_str().map(str::to_string)
}

fn component_fingerprints_at(value: &Value) -> Option<&Value> {
    value
        .get("componentFingerprints")
        .filter(|value| value.is_object())
}

fn component_fingerprint_at<'a>(value: &'a Value, component: &str) -> Option<&'a str> {
    component_fingerprints_at(value)?.get(component)?.as_str()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{comparability, context_paths, validate_component_fingerprints, validated_context_map};
    use serde_json::json;

    fn manifest(law_surface: &str) -> serde_json::Value {
        json!({
            "toolVersion": "0.5.4",
            "inputDigests": {
                "archmap": {"sha256": "same-archmap"},
                "lawPolicy": {"sha256": "same-policy"},
                "profileFingerprint": {"sha256": "same-profile"},
                "siteCoverDigest": {"sha256": "same-cover"}
            },
            "componentFingerprints": {
                "lawPolicy": "sha256:same-policy",
                "lawSurface": law_surface,
                "measurementProfile": "sha256:same-profile"
            }
        })
    }

    #[test]
    fn law_surface_fingerprint_change_blocks_identical_and_row_comparability() {
        let base = manifest("sha256:surface-a");
        let head = manifest("sha256:surface-b");
        let result = comparability(&base, &head);
        assert_eq!(result["level"], "not-comparable");
        assert_eq!(result["sameComponentFingerprints"], false);
        assert_eq!(result["sameLawSurfaceFingerprint"], false);
    }

    #[test]
    fn law_policy_fingerprint_change_blocks_row_comparability() {
        let mut base = manifest("sha256:surface-a");
        let mut head = manifest("sha256:surface-a");
        base["componentFingerprints"]["lawPolicy"] = json!("sha256:policy-a");
        head["componentFingerprints"]["lawPolicy"] = json!("sha256:policy-b");
        let result = comparability(&base, &head);
        assert_eq!(result["level"], "not-comparable");
        assert_eq!(result["sameComponentFingerprints"], false);
    }

    #[test]
    fn repair_plan_digest_change_excludes_identical_but_keeps_verdict_row_comparability() {
        let mut base = manifest("sha256:surface-a");
        let mut head = manifest("sha256:surface-a");
        base["inputDigests"]["repairPlan"] = json!({"sha256": "repair-plan-a"});
        head["inputDigests"]["repairPlan"] = json!({"sha256": "repair-plan-b"});
        let result = comparability(&base, &head);
        assert_eq!(result["level"], "verdict-row");
        assert_eq!(result["sameRepairPlanDigest"], false);
    }

    #[test]
    fn malformed_component_fingerprints_are_rejected() {
        let mut value = manifest("sha256:surface-a");
        value["componentFingerprints"] = json!({});
        assert!(validate_component_fingerprints(&value, "test manifest").is_err());
    }

    #[test]
    fn context_paths_records_a_unique_nontrivial_restriction_path() {
        let contexts = BTreeMap::from([
            (
                "coarse".to_string(),
                json!({"restrictsTo": []}),
            ),
            (
                "fine".to_string(),
                json!({"restrictsTo": ["middle"]}),
            ),
            (
                "middle".to_string(),
                json!({"restrictsTo": ["coarse"]}),
            ),
        ]);
        assert_eq!(
            context_paths(&contexts, "fine", "coarse"),
            vec![vec!["fine".to_string(), "middle".to_string(), "coarse".to_string()]]
        );
    }

    #[test]
    fn context_paths_caps_ambiguous_paths_for_fail_closed_selection() {
        let contexts = BTreeMap::from([
            (
                "coarse".to_string(),
                json!({"restrictsTo": []}),
            ),
            (
                "fine".to_string(),
                json!({"restrictsTo": ["left", "right"]}),
            ),
            (
                "left".to_string(),
                json!({"restrictsTo": ["coarse"]}),
            ),
            (
                "right".to_string(),
                json!({"restrictsTo": ["coarse"]}),
            ),
        ]);
        assert_eq!(
            context_paths(&contexts, "fine", "coarse"),
            vec![
                vec!["fine".to_string(), "left".to_string(), "coarse".to_string()],
                vec!["fine".to_string(), "right".to_string(), "coarse".to_string()],
            ]
        );
    }

    #[test]
    fn normalized_context_validation_rejects_unresolved_and_cyclic_restrictions() {
        let unresolved = json!({
            "contexts": [{"normalizedContextId": "fine", "restrictsTo": ["missing"]}]
        });
        assert_eq!(
            validated_context_map(&unresolved, "test").unwrap_err().0,
            "normalized_context_restriction_unresolved"
        );

        let cyclic = json!({
            "contexts": [
                {"normalizedContextId": "fine", "restrictsTo": ["coarse"]},
                {"normalizedContextId": "coarse", "restrictsTo": ["fine"]}
            ]
        });
        assert_eq!(
            validated_context_map(&cyclic, "test").unwrap_err().0,
            "normalized_context_restriction_cycle"
        );
    }
}

fn require_schema(value: &Value, expected: &str, label: &str) -> Result<(), Box<dyn Error>> {
    if value.get("schema").and_then(Value::as_str) != Some(expected) {
        return Err(format!("{label} must have schema {expected}").into());
    }
    Ok(())
}

fn read_run_json(run: &Path, name: &str) -> Result<Value, Box<dyn Error>> {
    let text = std::fs::read_to_string(run.join(name))?;
    reject_duplicate_keys(&text)?;
    Ok(serde_json::from_str(&text)?)
}

fn validate_component_fingerprints(manifest: &Value, label: &str) -> Result<(), Box<dyn Error>> {
    let object = manifest
        .get("componentFingerprints")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{label} requires componentFingerprints"))?;
    let expected = BTreeSet::from([
        "lawPolicy".to_string(),
        "lawSurface".to_string(),
        "measurementProfile".to_string(),
    ]);
    let actual = object.keys().cloned().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(format!(
            "{label} componentFingerprints keys must be lawPolicy, lawSurface, measurementProfile"
        )
        .into());
    }
    for (component, value) in object {
        let fingerprint = value
            .as_str()
            .ok_or_else(|| format!("{label} componentFingerprints.{component} must be a string"))?;
        if fingerprint.len() != 71
            || !fingerprint.starts_with("sha256:")
            || !fingerprint[7..]
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(format!(
                "{label} componentFingerprints.{component} must be sha256:<64 hex chars>"
            )
            .into());
        }
    }
    let input_digests = manifest
        .get("inputDigests")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{label} requires inputDigests object"))?;
    let required_digest_keys = BTreeSet::from([
        "archmap",
        "lawPolicy",
        "lawSurface",
        "measurementProfile",
        "profileFingerprint",
        "siteCoverDigest",
    ]);
    let allowed_digest_keys = BTreeSet::from([
        "archmap",
        "lawPolicy",
        "lawSurface",
        "measurementProfile",
        "measurementProfiles",
        "profileFingerprint",
        "repairPlan",
        "siteCoverDigest",
    ]);
    let actual_digest_keys = input_digests
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if actual_digest_keys
        .difference(&allowed_digest_keys)
        .next()
        .is_some()
    {
        return Err(format!("{label} inputDigests contains unknown keys").into());
    }
    if required_digest_keys
        .difference(&actual_digest_keys)
        .next()
        .is_some()
    {
        return Err(format!("{label} inputDigests is missing required keys").into());
    }
    for key in &actual_digest_keys {
        if *key == "measurementProfiles" {
            let entries = input_digests
                .get(*key)
                .and_then(Value::as_array)
                .ok_or_else(|| {
                    format!("{label} inputDigests.measurementProfiles must be an array")
                })?;
            if entries.is_empty() {
                return Err(
                    format!("{label} inputDigests.measurementProfiles must not be empty").into(),
                );
            }
            for entry in entries {
                let object = entry.as_object().ok_or_else(|| {
                    format!("{label} inputDigests.measurementProfiles entries must be objects")
                })?;
                let keys = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
                if keys != BTreeSet::from(["path", "sha256"]) {
                    return Err(format!(
                        "{label} inputDigests.measurementProfiles entry has invalid fields"
                    )
                    .into());
                }
                if !object.get("path").is_some_and(Value::is_string)
                    || !object
                        .get("sha256")
                        .and_then(Value::as_str)
                        .is_some_and(|digest| {
                            digest.len() == 64
                                && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
                        })
                {
                    return Err(format!(
                        "{label} inputDigests.measurementProfiles entry is invalid"
                    )
                    .into());
                }
            }
            continue;
        }
        let entry = input_digests
            .get(*key)
            .and_then(Value::as_object)
            .ok_or_else(|| format!("{label} inputDigests.{key} must be an object"))?;
        let digest = entry
            .get("sha256")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{label} inputDigests.{key}.sha256 is required"))?;
        if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(format!("{label} inputDigests.{key}.sha256 must be 64 hex chars").into());
        }
        let expected_entry_keys = match *key {
            "profileFingerprint" => BTreeSet::from(["basis", "sha256"]),
            "siteCoverDigest" => BTreeSet::from(["basis", "sha256", "status"]),
            _ => BTreeSet::from(["path", "sha256"]),
        };
        let actual_entry_keys = entry.keys().map(String::as_str).collect::<BTreeSet<_>>();
        if actual_entry_keys
            .difference(&expected_entry_keys)
            .next()
            .is_some()
            || expected_entry_keys
                .difference(&actual_entry_keys)
                .next()
                .is_some()
        {
            return Err(format!("{label} inputDigests.{key} has invalid fields").into());
        }
        for field in expected_entry_keys {
            if field != "sha256" && !entry.get(field).is_some_and(Value::is_string) {
                return Err(format!("{label} inputDigests.{key}.{field} must be a string").into());
            }
        }
    }
    let repair_plan_input = manifest.get("repairPlanInputPath");
    let repair_plan_path = repair_plan_input.and_then(Value::as_str);
    let repair_plan_digest = input_digests.get("repairPlan");
    match (repair_plan_path, repair_plan_digest) {
        (Some(path), Some(digest)) if digest["path"].as_str() == Some(path) => {}
        (Some(_), Some(_)) => {
            return Err(format!(
                "{label} inputDigests.repairPlan.path must match repairPlanInputPath"
            )
            .into());
        }
        (Some(_), None) => {
            return Err(format!(
                "{label} requires inputDigests.repairPlan when repairPlanInputPath is present"
            )
            .into());
        }
        (None, Some(_)) => {
            return Err(format!(
                "{label} must not contain inputDigests.repairPlan without repairPlanInputPath"
            )
            .into());
        }
        (None, None) => {}
    }
    for (component, digest_key) in [
        ("lawPolicy", "lawPolicy"),
        ("lawSurface", "lawSurface"),
        ("measurementProfile", "measurementProfile"),
    ] {
        let digest = input_digests
            .get(digest_key)
            .and_then(|value| value.get("sha256"))
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{label} requires inputDigests.{digest_key}.sha256"))?;
        if fingerprint_value(object, component) != Some(digest) {
            return Err(format!(
                "{label} componentFingerprints.{component} must match inputDigests.{digest_key}.sha256"
            )
            .into());
        }
    }
    Ok(())
}

fn fingerprint_value<'a>(
    object: &'a serde_json::Map<String, Value>,
    component: &str,
) -> Option<&'a str> {
    object
        .get(component)
        .and_then(Value::as_str)
        .and_then(|value| value.strip_prefix("sha256:"))
}

fn validate_run_manifest_shape(manifest: &Value, label: &str) -> Result<(), Box<dyn Error>> {
    let object = manifest
        .as_object()
        .ok_or_else(|| format!("{label} must be a JSON object"))?;
    let allowed = BTreeSet::from([
        "schema",
        "toolVersion",
        "runId",
        "inputDigests",
        "artifactDigests",
        "componentFingerprints",
        "commandName",
        "mode",
        "conclusionCode",
        "archmapInputPath",
        "lawPolicyInputPath",
        "lawSurfaceInputPath",
        "measurementProfileInputPath",
        "measurementProfileInputPaths",
        "repairPlanInputPath",
        "rawArtifactRetention",
        "generatedArtifacts",
        "omittedArtifacts",
        "artifactLinks",
        "validationReports",
        "rawArtifactPaths",
        "validationResultSummary",
        "nonConclusions",
    ]);
    let required = BTreeSet::from([
        "schema",
        "toolVersion",
        "runId",
        "inputDigests",
        "artifactDigests",
        "componentFingerprints",
        "commandName",
        "mode",
        "conclusionCode",
        "archmapInputPath",
        "lawPolicyInputPath",
        "rawArtifactRetention",
        "generatedArtifacts",
        "omittedArtifacts",
        "artifactLinks",
        "validationReports",
        "validationResultSummary",
        "nonConclusions",
    ]);
    let actual = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
    if actual.difference(&allowed).next().is_some() {
        return Err(format!("{label} contains unknown top-level manifest fields").into());
    }
    if required.difference(&actual).next().is_some() {
        return Err(format!("{label} is missing required top-level manifest fields").into());
    }
    let artifact_digests = manifest
        .get("artifactDigests")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{label} artifactDigests must be an object"))?;
    let expected_artifacts = if manifest["mode"].as_str() == Some("measurement") {
        BTreeSet::from(["measurementPacket", "normalizedArchmap"])
    } else {
        BTreeSet::new()
    };
    let actual_artifacts = artifact_digests
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if actual_artifacts != expected_artifacts {
        return Err(format!(
            "{label} artifactDigests must match artifacts emitted by its run mode"
        )
        .into());
    }
    for (artifact_key, artifact_path) in [
        ("measurementPacket", "archsig-measurement-packet.json"),
        ("normalizedArchmap", "normalized-archmap.json"),
    ] {
        let artifact = artifact_digests
            .get(artifact_key)
            .ok_or_else(|| format!("{label} artifactDigests.{artifact_key} is required"))?;
        let object = artifact
            .as_object()
            .ok_or_else(|| format!("{label} artifactDigests.{artifact_key} must be an object"))?;
        if object.keys().map(String::as_str).collect::<BTreeSet<_>>()
            != BTreeSet::from(["path", "sha256"])
            || object.get("path").and_then(Value::as_str)
                != Some(artifact_path)
            || !object
                .get("sha256")
                .and_then(Value::as_str)
                .is_some_and(|digest| {
                    digest.len() == 64 && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
                })
        {
            return Err(format!(
                "{label} artifactDigests.{artifact_key} must contain its artifact path and sha256 digest"
            )
            .into());
        }
    }
    Ok(())
}

fn reject_duplicate_keys(text: &str) -> Result<(), Box<dyn Error>> {
    let mut deserializer = serde_json::Deserializer::from_str(text);
    serde::de::Deserializer::deserialize_any(&mut deserializer, DuplicateKeyVisitor)?;
    Ok(())
}

struct DuplicateKeySeed;

impl<'de> DeserializeSeed<'de> for DuplicateKeySeed {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(DuplicateKeyVisitor)
    }
}

struct DuplicateKeyVisitor;

impl<'de> Visitor<'de> for DuplicateKeyVisitor {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value without duplicate object keys")
    }

    fn visit_bool<E>(self, _: bool) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_i64<E>(self, _: i64) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_u64<E>(self, _: u64) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_f64<E>(self, _: f64) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_str<E>(self, _: &str) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_string<E>(self, _: String) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(())
    }
    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(DuplicateKeyVisitor)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        while sequence.next_element_seed(DuplicateKeySeed)?.is_some() {}
        Ok(())
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut keys = BTreeSet::new();
        while let Some(key) = map.next_key::<String>()? {
            if !keys.insert(key.clone()) {
                return Err(serde::de::Error::custom(format!(
                    "duplicate JSON object key: {key}"
                )));
            }
            map.next_value_seed(DuplicateKeySeed)?;
        }
        Ok(())
    }
}

fn artifact_ref(run: &Path, name: &str) -> String {
    let run_name = run
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("run");
    format!("{run_name}/{name}")
}

fn canonical_json_value_digest(value: &Value) -> Result<String, Box<dyn Error>> {
    let bytes = serde_json::to_vec(&canonical_json_value(value))?;
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    Ok(format!("{:x}", hasher.finalize()))
}

fn canonical_json_value(value: &Value) -> Value {
    match value {
        Value::Array(items) => Value::Array(items.iter().map(canonical_json_value).collect()),
        Value::Object(object) => {
            let sorted = object
                .iter()
                .map(|(key, value)| (key.clone(), canonical_json_value(value)))
                .collect::<BTreeMap<_, _>>();
            let mut map = Map::new();
            for (key, value) in sorted {
                map.insert(key, value);
            }
            Value::Object(map)
        }
        _ => value.clone(),
    }
}

fn canonical_value(value: &Value) -> String {
    serde_json::to_string(value).unwrap_or_else(|_| "null".to_string())
}
