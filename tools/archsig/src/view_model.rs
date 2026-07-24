//! Display-independent typed measurement view model.
//!
//! `archsig-measurement-view-model` is a bounded projection of the measurement
//! packet (plus the normalized ArchMap observation input) into typed sections a
//! human-facing viewer can render without re-deriving or inferring anything.
//! Every leaf maps to a packet / normalized-archmap field; the mapping table is
//! documented in `docs/tool/archsig_view_model_contract.md`. Display vocabulary
//! (weather or otherwise) never appears in this artifact.

use crate::{NormalizedArchMapV2, NormalizedAtomV2};
use serde_json::{Value, json};
use std::collections::BTreeMap;

pub const ARCHSIG_MEASUREMENT_VIEW_MODEL_SCHEMA_VERSION: &str =
    "archsig-measurement-view-model/v0.5.4";

fn invariant_with_id_prefix<'a>(packet: &'a Value, prefix: &str) -> Option<&'a Value> {
    packet["computedInvariants"]
        .as_array()?
        .iter()
        .find(|inv| {
            inv["invariantId"]
                .as_str()
                .is_some_and(|id| id.starts_with(prefix))
        })
}

fn representation<'a>(invariant: &'a Value) -> &'a Value {
    if invariant["representation"].is_object() {
        &invariant["representation"]
    } else {
        invariant
    }
}

fn profile_rows(packet: &Value) -> Vec<Value> {
    let mut rows = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let primary = &packet["profile"];
    for profile in std::iter::once(primary).chain(
        packet["profiles"]
            .as_array()
            .into_iter()
            .flatten(),
    ) {
        let Some(profile_id) = profile["profileId"].as_str() else {
            continue;
        };
        if !seen.insert(profile_id.to_string()) {
            continue;
        }
        rows.push(json!({
            "profileRef": profile_id,
            "siteRef": profile["siteRef"],
            "coverRef": profile["coverRef"],
            "coefficient": profile["coefficient"],
            "domain": profile["domain"],
        }));
    }
    rows
}

/// Selected-cover complex projected verbatim from the packet's cech invariant
/// `coverNerveProjection` (vertices / edges / faces). The absence of a face over
/// a cycle is derivable by the consumer from this section alone; the view model
/// does not add any face the packet did not record.
fn complex_section(packet: &Value) -> Value {
    let Some(cech) = invariant_with_id_prefix(packet, "cech-cohomology:") else {
        return Value::Null;
    };
    let projection = &representation(cech)["coverNerveProjection"];
    if !projection.is_object() {
        return Value::Null;
    }
    let vertices = projection["vertices"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|vertex| {
            json!({
                "contextRef": vertex["contextRef"],
                "atomCount": vertex["atomRefs"].as_array().map(Vec::len),
            })
        })
        .collect::<Vec<_>>();
    let edges = projection["edges"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|edge| {
            json!({
                "edgeRef": edge["edgeId"],
                "sourceContextRef": edge["sourceContextRef"],
                "targetContextRef": edge["targetContextRef"],
            })
        })
        .collect::<Vec<_>>();
    let triples = projection["faces"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|face| {
            json!({
                "tripleRef": face["faceId"],
                "contextRefs": face["contextRefs"],
                "edgeRefs": face["edgeRefs"],
                "sharedAtomRefs": face["sharedAtomRefs"],
            })
        })
        .collect::<Vec<_>>();
    json!({
        "coverRef": projection["coverRef"],
        "vertices": vertices,
        "edges": edges,
        "triples": triples,
        "tripleSource": projection["faceSource"],
    })
}

/// Witness rows per restriction edge. Three states only; an unsupplied witness
/// is never collapsed into agreement.
fn edge_mismatch_section(packet: &Value) -> Value {
    let Some(cech) = invariant_with_id_prefix(packet, "cech-cohomology:") else {
        return Value::Null;
    };
    let projection = &representation(cech)["coverNerveProjection"];
    let Some(edges) = projection["edges"].as_array() else {
        return Value::Null;
    };
    let rows = edges
        .iter()
        .map(|edge| {
            let observed = edge["sectionObservation"].as_str() == Some("observed");
            let mismatch = edge["value"].as_u64() == Some(1);
            let status = if !observed {
                "witness_not_supplied"
            } else if mismatch {
                "mismatch_observed"
            } else {
                "agreement_observed"
            };
            json!({
                "edgeRef": edge["edgeId"],
                "status": status,
                "supportAtomRefs": edge["supportAtomRefs"],
            })
        })
        .collect::<Vec<_>>();
    json!(rows)
}

/// Class support for the measured cohomology reading. `undirected: true` states
/// that F2 coefficients carry no orientation; consumers must not render
/// direction, rotation, or magnitude from this section.
fn class_support_section(packet: &Value) -> Value {
    let Some(cech) = invariant_with_id_prefix(packet, "cech-cohomology:") else {
        return Value::Null;
    };
    let rep = representation(cech);
    let observed = &rep["observedCocycle"];
    let mut section = json!({
        "coefficient": rep["coefficient"],
        "undirected": true,
        "classNonzero": observed["classNonzero"],
        "representativeEdgeRefs": rep["classSupport"]["edgeRefs"],
        "supportAtomRefs": rep["classSupport"]["supportAtomRefs"],
        "b1": rep["nerveShape"]["b1"],
        "isForest": rep["nerveShape"]["isForest"],
    });
    if let Some(residual) = invariant_with_id_prefix(packet, "saga-descent:residual-class") {
        let residual_rep = representation(residual);
        section["residualClass"] = json!({
            "nonZero": residual_rep["residualClassSupport"]["nonZero"],
            "basis": residual_rep["residualClassSupport"]["basis"],
            "representative": residual_rep["residualClassSupport"]["representative"],
            "component": residual_rep["residualClassSupport"]["component"],
            "cocycleCertificateKind": residual_rep["residualClassSupport"]["cocycle"]["certificateKind"],
            "tripleOverlapRefs": residual_rep["residualClassSupport"]["cocycle"]["tripleOverlapRefs"],
            "suppliedData": residual_rep["residualClassSupport"]["suppliedData"],
        });
    }
    if let Some(membership) = invariant_with_id_prefix(packet, "saga-descent:boundary-membership") {
        let membership_value = if membership["value"].is_object() {
            &membership["value"]
        } else {
            representation(membership)
        };
        section["boundaryMembership"] = json!({
            "inB1": membership_value["inB1"],
            "residualSupport": membership_value["residualSupport"],
        });
    }
    section
}

/// Per-chart grounding rows, present only when a saga-grounded premise was
/// actually evaluated in this run.
fn local_observations_section(packet: &Value) -> Value {
    let Some(grounded) = invariant_with_id_prefix(packet, "saga-generated-end-to-end-packet")
    else {
        return Value::Null;
    };
    let rep = representation(grounded);
    let per_chart_value = if rep["lawDependent"]["premise"]["perChart"].is_array() {
        &rep["lawDependent"]["premise"]["perChart"]
    } else {
        &rep["premise"]["perChart"]
    };
    let Some(per_chart) = per_chart_value.as_array() else {
        return Value::Null;
    };
    let verdict_row = packet["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .find(|row| row["evaluator"].as_str() == Some("ag.saga-grounded"));
    let rows = per_chart
        .iter()
        .map(|chart| {
            json!({
                "chartRef": chart["chart"],
                "law": chart["law"],
                "holds": chart["holds"],
                "holdsCriterionRef": chart["holdsCriterionRef"],
                "defectValueRef": chart["defectValueRef"],
            })
        })
        .collect::<Vec<_>>();
    json!({
        "evaluator": "ag.saga-grounded",
        "verdict": verdict_row.map(|row| row["verdict"].clone()).unwrap_or(Value::Null),
        "reason": verdict_row.map(|row| row["reason"].clone()).unwrap_or(Value::Null),
        "perChart": rows,
    })
}

/// Observation coverage: which context x measurement-axis pairs this run
/// actually observed. Rows are projections of the normalized observation input
/// and packet rows; a missing row means the pair was not observed, and the
/// consumer must not guess coverage beyond these rows.
fn observation_coverage_section(packet: &Value, normalized: &NormalizedArchMapV2) -> Value {
    let complex = complex_section(packet);
    let Some(vertices) = complex["vertices"].as_array() else {
        return Value::Null;
    };
    let profile_ref = packet["profile"]["profileId"].clone();
    let mut section_atoms: BTreeMap<&str, Vec<&NormalizedAtomV2>> = BTreeMap::new();
    for atom in &normalized.atoms {
        if atom.axis == "cech" && atom.predicate == "sectionValue" {
            section_atoms.entry(atom.subject.as_str()).or_default().push(atom);
        }
    }
    let grounding = local_observations_section(packet);
    let mut grounding_by_chart = BTreeMap::new();
    if let Some(rows) = grounding["perChart"].as_array() {
        for row in rows {
            if let Some(chart) = row["chartRef"].as_str() {
                grounding_by_chart.insert(chart.to_string(), row);
            }
        }
    }
    let boundary_by_context = boundary_kinds_by_scope(packet);
    let mut rows = Vec::new();
    for vertex in vertices {
        let Some(context_ref) = vertex["contextRef"].as_str() else {
            continue;
        };
        let atoms = section_atoms.get(context_ref);
        let observed = atoms.is_some_and(|atoms| !atoms.is_empty());
        rows.push(json!({
            "contextRef": context_ref,
            "profileRef": profile_ref,
            "measurementAxis": "cech.sectionValue",
            "status": if observed { "observed" } else { "not_observed" },
            "supportRefs": atoms
                .map(|atoms| atoms.iter().map(|atom| atom.normalized_atom_id.clone()).collect::<Vec<_>>())
                .unwrap_or_default(),
            "sourceRefs": atoms
                .map(|atoms| {
                    let mut refs = atoms
                        .iter()
                        .flat_map(|atom| atom.source_refs.iter().cloned())
                        .collect::<Vec<_>>();
                    refs.sort();
                    refs.dedup();
                    refs
                })
                .unwrap_or_default(),
            "boundaryKinds": boundary_by_context.get(context_ref).cloned().unwrap_or_default(),
        }));
        if let Some(grounding_row) = grounding_by_chart.get(context_ref) {
            rows.push(json!({
                "contextRef": context_ref,
                "profileRef": profile_ref,
                "measurementAxis": "saga-grounded.holdsCriterion",
                "status": if grounding_row["holds"].as_bool() == Some(true) {
                    "measured_zero"
                } else {
                    "measured_nonzero"
                },
                "conclusionCode": grounding["reason"],
                "supportRefs": [grounding_row["holdsCriterionRef"].clone()],
                "sourceRefs": [grounding_row["defectValueRef"].clone()],
                "boundaryKinds": boundary_by_context.get(context_ref).cloned().unwrap_or_default(),
            }));
        }
    }
    json!(rows)
}

fn boundary_kinds_by_scope(packet: &Value) -> BTreeMap<String, Vec<Value>> {
    let mut map: BTreeMap<String, Vec<Value>> = BTreeMap::new();
    for statement in packet["boundaryStatements"].as_array().into_iter().flatten() {
        for scope in statement["scopeRefs"].as_array().into_iter().flatten() {
            if let Some(scope_ref) = scope.as_str() {
                map.entry(scope_ref.to_string())
                    .or_default()
                    .push(statement["kind"].clone());
            }
        }
    }
    map
}

/// Measured scalar values with their packet provenance. Per-run scalars carry
/// scope "cover"; no per-vertex/per-edge scalar exists in current packets, and
/// none is synthesized here.
fn scalar_fields_section(packet: &Value) -> Value {
    let mut fields = Vec::new();
    if let Some(debt) = invariant_with_id_prefix(packet, "harmonic-debt:") {
        let rep = representation(debt);
        for (field_id, key) in [
            ("harmonic-debt-norm", "harmonicDebtNorm"),
            ("essential-repair-lower-bound", "essentialRepairLowerBound"),
        ] {
            if !rep[key].is_null() {
                fields.push(json!({
                    "fieldId": field_id,
                    "scope": "cover",
                    "value": rep[key],
                    "sourceInvariantId": rep["invariantId"],
                    "lowerBoundStatus": rep["lowerBoundStatus"],
                }));
            }
        }
    }
    if let Some(capacity) = invariant_with_id_prefix(packet, "topological-debt-capacity:") {
        let rep = representation(capacity);
        if !rep["capacityLowerBound"].is_null() {
            fields.push(json!({
                "fieldId": "topological-debt-capacity-lower-bound",
                "scope": "cover",
                "value": rep["capacityLowerBound"],
                "sourceInvariantId": rep["invariantId"],
            }));
        }
    }
    if fields.is_empty() {
        Value::Null
    } else {
        json!(fields)
    }
}

pub fn build_measurement_view_model_v1(
    packet_value: &Value,
    normalized: &NormalizedArchMapV2,
    summary: &Value,
) -> Value {
    let complex = complex_section(packet_value);
    let observation_coverage = observation_coverage_section(packet_value, normalized);
    let local_observations = local_observations_section(packet_value);
    let edge_mismatch = edge_mismatch_section(packet_value);
    let class_support = class_support_section(packet_value);
    let scalar_fields = scalar_fields_section(packet_value);
    json!({
        "schema": ARCHSIG_MEASUREMENT_VIEW_MODEL_SCHEMA_VERSION,
        "sourceArtifactRefs": {
            "measurementPacket": "archsig-measurement-packet.json",
            "normalizedArchMap": "normalized-archmap.json",
            "summary": "archsig-analysis-summary.json",
        },
        "conclusion": summary["conclusion"],
        "profiles": profile_rows(packet_value),
        "complex": complex,
        "observationCoverage": observation_coverage,
        "localObservations": local_observations,
        "edgeMismatch": edge_mismatch,
        "classSupport": class_support,
        // Harmonic representative edge values are not recorded in current
        // packets; the section stays absent rather than being synthesized.
        "harmonicFlow": Value::Null,
        "scalarFields": scalar_fields,
        "boundaryStatements": packet_value["boundaryStatements"].clone(),
        "nonClaims": [
            "The view model is a bounded projection of the measurement packet and the normalized ArchMap observation input; it computes no new invariant and renders no verdict.",
            "Absent sections mean the corresponding measurement was not recorded in this run; absence is not zero.",
            "F2 class support carries no orientation; direction, rotation, and magnitude must not be derived from it.",
            "Coverage rows enumerate observed context x axis pairs only; consumers must not infer coverage beyond these rows.",
        ],
    })
}
