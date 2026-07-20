//! ArchMap supply bench: deterministic metric computation over dual-pass
//! extraction-consistency artifacts, group-structured adjudication records,
//! and reference-alignment artifacts.
//!
//! The bench records metrics; it holds no thresholds and issues no verdicts.
//! Mechanical scope: enumeration, hashing, literal normalized-key comparison,
//! reference resolution, and arithmetic aggregation of their results.
//! Adjudicated metrics are functions of supplied adjudication records; the
//! bench never adjudicates, votes, or merges by similarity.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::File;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};

use crate::authoring::ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA;
use crate::{ArchmapExtractionAdjudicationV1, ArchmapExtractionConsistencyV1};

pub const ARCHMAP_REFERENCE_SLICE_V1_SCHEMA: &str = "archmap-reference-slice/v1";
pub const ARCHMAP_REFERENCE_ALIGNMENT_V1_SCHEMA: &str = "archmap-reference-alignment/v1";
pub const ARCHMAP_SUPPLY_BENCH_REPORT_V1_SCHEMA: &str = "archmap-supply-bench-report/v1";

pub const ALIGNMENT_DECISION_REFERENCE_MATCHED: &str = "reference-matched";
pub const ALIGNMENT_DECISION_NOVEL_CORRECT: &str = "novel-correct";
pub const ALIGNMENT_DECISION_NOT_ADOPTED: &str = "not-adopted";
pub const ALIGNMENT_DECISION_UNRECOVERED: &str = "unrecovered";

const ADJUDICATION_DECISIONS: [&str; 3] = ["merged", "adopted", "not-adopted"];

const SUPPLY_BENCH_CLAIM_BOUNDARY: &str = "Values are records relative to the recorded comparison-series key (corpus, reference slice, reader model, rule-set version, adjudicator, harness). matchRate is a record, not a verdict. No claim is made beyond the measured corpus, models, and rule-set versions.";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapReferenceSliceV1 {
    pub schema: String,
    pub id: String,
    pub version: String,
    pub rule_set_version: String,
    pub atom_match_key_spec: String,
    pub atoms: Vec<ArchmapReferenceSliceAtomV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapReferenceSliceAtomV1 {
    pub atom_id: String,
    pub match_key: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub chunk_class: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapReferenceAlignmentV1 {
    pub schema: String,
    pub id: String,
    pub reference_ref: String,
    pub reference_version: String,
    pub pair_ref: String,
    pub adjudicator: String,
    pub rows: Vec<ArchmapReferenceAlignmentRowV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapReferenceAlignmentRowV1 {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reference_atom_id: Option<String>,
    #[serde(default)]
    pub candidate_atom_ids: Vec<String>,
    pub decision: String,
    pub basis: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapSupplyBenchReportV1 {
    pub schema: String,
    pub id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub series_key: Option<serde_json::Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reference_ref: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reference_version: Option<String>,
    pub pairs: Vec<SupplyBenchPairReportV1>,
    pub aggregate: BTreeMap<String, SupplyBenchStatV1>,
    pub chunk_class_aggregate: BTreeMap<String, BTreeMap<String, SupplyBenchStatV1>>,
    pub claim_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SupplyBenchPairReportV1 {
    pub pair_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub chunk_class: Option<String>,
    pub consistency_ref: String,
    pub machine_match_rate: f64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub machine_match_rate_key1: Option<f64>,
    pub key_convergence: SupplyBenchKeyConvergenceV1,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reference_recall: Option<SupplyBenchReferenceRecallV1>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub over_generation: Option<SupplyBenchOverGenerationV1>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SupplyBenchKeyConvergenceV1 {
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub matched: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub merge_groups: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub adopted: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub not_adopted: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rate: Option<f64>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SupplyBenchReferenceRecallV1 {
    pub reference_atoms: usize,
    pub mechanically_recovered: usize,
    pub mechanical_lower_bound: f64,
    pub adjudicated_recovered: usize,
    pub adjudicated: f64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SupplyBenchOverGenerationV1 {
    pub candidate_atoms: usize,
    pub not_adopted_atoms: usize,
    pub novel_correct_atoms: usize,
    pub rate: f64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SupplyBenchStatV1 {
    pub pairs: usize,
    pub min: f64,
    pub max: f64,
    pub mean: f64,
}

#[derive(Debug, Clone)]
pub struct SupplyBenchPairInput {
    pub pair_id: String,
    pub chunk_class: Option<String>,
    pub consistency: PathBuf,
    pub alignment: Option<PathBuf>,
}

#[derive(Debug, Clone)]
pub struct SupplyBenchOptions {
    pub id: String,
    pub pairs: Vec<SupplyBenchPairInput>,
    pub reference: Option<PathBuf>,
    pub series_key: Option<PathBuf>,
}

pub fn build_supply_bench_report_v1(
    options: &SupplyBenchOptions,
) -> Result<ArchmapSupplyBenchReportV1, Box<dyn Error>> {
    if options.pairs.is_empty() {
        return Err("--pair is required".into());
    }
    // Canonical processing order: pair id, independent of argument order.
    let mut ordered: BTreeMap<&str, &SupplyBenchPairInput> = BTreeMap::new();
    for pair in &options.pairs {
        if ordered.insert(pair.pair_id.as_str(), pair).is_some() {
            return Err(format!("duplicate pair id {}", pair.pair_id).into());
        }
    }

    let reference = match &options.reference {
        Some(path) => Some(load_reference_slice(path)?),
        None => None,
    };
    if let Some(reference) = &reference {
        for pair in ordered.values() {
            if pair.alignment.is_none() {
                return Err(format!(
                    "reference slice {} supplied but pair {} has no --alignment; \
                     adjudicated reference metrics cannot be silently skipped",
                    reference.id, pair.pair_id
                )
                .into());
            }
        }
    } else if let Some(pair) = ordered.values().find(|pair| pair.alignment.is_some()) {
        return Err(format!(
            "pair {} has an --alignment but no --reference slice was supplied",
            pair.pair_id
        )
        .into());
    }

    let series_key = match &options.series_key {
        Some(path) => Some(read_json_value(path)?),
        None => None,
    };

    let mut pair_reports = Vec::new();
    for pair in ordered.values() {
        let consistency = load_consistency(&pair.consistency)?;
        let adjudication = check_adjudications(&consistency)?;
        let key_convergence = key_convergence_metrics(&consistency, &adjudication);
        let (reference_recall, over_generation) = match (&reference, &pair.alignment) {
            (Some(reference), Some(alignment_path)) => {
                let alignment = load_alignment(alignment_path)?;
                let metrics =
                    reference_metrics(&consistency, reference, &alignment, &pair.pair_id)?;
                (Some(metrics.0), Some(metrics.1))
            }
            _ => (None, None),
        };
        pair_reports.push(SupplyBenchPairReportV1 {
            pair_id: pair.pair_id.clone(),
            chunk_class: pair.chunk_class.clone(),
            consistency_ref: consistency.id.clone(),
            machine_match_rate: consistency.match_rate,
            machine_match_rate_key1: consistency
                .atom_match_key1_comparison
                .as_ref()
                .map(|comparison| comparison.match_rate),
            key_convergence,
            reference_recall,
            over_generation,
        });
    }

    let aggregate = aggregate_metrics(pair_reports.iter());
    let mut chunk_class_aggregate = BTreeMap::new();
    let mut classes: BTreeMap<String, Vec<&SupplyBenchPairReportV1>> = BTreeMap::new();
    for report in &pair_reports {
        let class = report
            .chunk_class
            .clone()
            .unwrap_or_else(|| "unclassified".to_string());
        classes.entry(class).or_default().push(report);
    }
    for (class, reports) in classes {
        chunk_class_aggregate.insert(class, aggregate_metrics(reports.into_iter()));
    }

    Ok(ArchmapSupplyBenchReportV1 {
        schema: ARCHMAP_SUPPLY_BENCH_REPORT_V1_SCHEMA.to_string(),
        id: options.id.clone(),
        series_key,
        reference_ref: reference.as_ref().map(|slice| slice.id.clone()),
        reference_version: reference.as_ref().map(|slice| slice.version.clone()),
        pairs: pair_reports,
        aggregate,
        chunk_class_aggregate,
        claim_boundary: SUPPLY_BENCH_CLAIM_BOUNDARY.to_string(),
    })
}

/// Outcome of the adjudication completeness and merge-group integrity checks.
struct AdjudicationCheck {
    /// `Some(groups)` when the record is group-structured and key convergence
    /// is computable; `None` when the record is a legacy (pre-merge-group)
    /// adjudication record.
    merge_groups: Option<usize>,
    adopted: usize,
    not_adopted: usize,
}

fn check_adjudications(
    consistency: &ArchmapExtractionConsistencyV1,
) -> Result<AdjudicationCheck, Box<dyn Error>> {
    let unmatched_atoms: Vec<(&str, &str, &str)> = consistency
        .only_in_pass_a
        .iter()
        .map(|row| (row.candidate_atom_id.as_str(), row.key.as_str(), "pass-a"))
        .chain(
            consistency
                .only_in_pass_b
                .iter()
                .map(|row| (row.candidate_atom_id.as_str(), row.key.as_str(), "pass-b")),
        )
        .collect();

    if unmatched_atoms.is_empty() && consistency.adjudications.is_empty() {
        return Ok(AdjudicationCheck {
            merge_groups: Some(0),
            adopted: 0,
            not_adopted: 0,
        });
    }
    if !unmatched_atoms.is_empty() && consistency.adjudications.is_empty() {
        let sample = sample_keys(unmatched_atoms.iter().map(|(_, key, _)| *key));
        return Err(format!(
            "consistency {}: adjudication record is missing; adjudicated metrics are \
             not computable. Unadjudicated unmatched keys include: {sample}",
            consistency.id
        )
        .into());
    }

    for row in &consistency.adjudications {
        if !ADJUDICATION_DECISIONS.contains(&row.decision.as_str()) {
            return Err(format!(
                "consistency {}: adjudication for key {} has unknown decision {}",
                consistency.id, row.key, row.decision
            )
            .into());
        }
        if row.decision != "merged" && (row.merge_group.is_some() || row.canonical_atom_id.is_some())
        {
            return Err(format!(
                "consistency {}: adjudication for key {} carries mergeGroup or \
                 canonicalAtomId but its decision is {}; group membership is \
                 restricted to merged rows",
                consistency.id, row.key, row.decision
            )
            .into());
        }
    }

    let merged_rows: Vec<&ArchmapExtractionAdjudicationV1> = consistency
        .adjudications
        .iter()
        .filter(|row| row.decision == "merged")
        .collect();
    let has_any_group = consistency
        .adjudications
        .iter()
        .any(|row| row.merge_group.is_some());
    let adopted = consistency
        .adjudications
        .iter()
        .filter(|row| row.decision == "adopted")
        .count();
    let not_adopted = consistency
        .adjudications
        .iter()
        .filter(|row| row.decision == "not-adopted")
        .count();

    if has_any_group {
        check_group_structured(consistency, &unmatched_atoms, &merged_rows)?;
        let groups: BTreeSet<&str> = merged_rows
            .iter()
            .filter_map(|row| row.merge_group.as_deref())
            .collect();
        Ok(AdjudicationCheck {
            merge_groups: Some(groups.len()),
            adopted,
            not_adopted,
        })
    } else {
        check_key_level_completeness(consistency, &unmatched_atoms)?;
        if merged_rows.is_empty() {
            Ok(AdjudicationCheck {
                merge_groups: Some(0),
                adopted,
                not_adopted,
            })
        } else {
            Ok(AdjudicationCheck {
                merge_groups: None,
                adopted,
                not_adopted,
            })
        }
    }
}

/// Group-structured mode: every adjudication row names its candidate atom,
/// every merged row belongs to exactly one group with a canonical atom, and
/// each group joins at least one atom from each pass.
fn check_group_structured(
    consistency: &ArchmapExtractionConsistencyV1,
    unmatched_atoms: &[(&str, &str, &str)],
    merged_rows: &[&ArchmapExtractionAdjudicationV1],
) -> Result<(), Box<dyn Error>> {
    let mut atom_side: BTreeMap<&str, (&str, &str)> = BTreeMap::new();
    for (atom_id, key, side) in unmatched_atoms {
        if atom_side.insert(atom_id, (key, side)).is_some() {
            return Err(format!(
                "consistency {}: unmatched candidate atom {} appears more than once \
                 in the onlyIn lists",
                consistency.id, atom_id
            )
            .into());
        }
    }

    let mut seen_atoms: BTreeSet<&str> = BTreeSet::new();
    for row in &consistency.adjudications {
        let atom_id = row.candidate_atom_id.as_deref().ok_or_else(|| {
            format!(
                "consistency {}: group-structured adjudication requires candidateAtomId \
                 on every row; the row for key {} has none",
                consistency.id, row.key
            )
        })?;
        let (expected_key, _) = atom_side.get(atom_id).ok_or_else(|| {
            format!(
                "consistency {}: adjudication references candidate atom {} (key {}) \
                 which is not in the onlyIn lists",
                consistency.id, atom_id, row.key
            )
        })?;
        if *expected_key != row.key {
            return Err(format!(
                "consistency {}: adjudication for candidate atom {} records key {} \
                 but the onlyIn row records key {}",
                consistency.id, atom_id, row.key, expected_key
            )
            .into());
        }
        if !seen_atoms.insert(atom_id) {
            return Err(format!(
                "consistency {}: candidate atom {} has more than one adjudication row",
                consistency.id, atom_id
            )
            .into());
        }
    }
    let missing: Vec<&str> = atom_side
        .keys()
        .filter(|atom_id| !seen_atoms.contains(**atom_id))
        .copied()
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "consistency {}: partial adjudication; adjudicated metrics are not \
             computable. Unadjudicated candidate atoms include: {}",
            consistency.id,
            sample_keys(missing.into_iter())
        )
        .into());
    }

    let mut groups: BTreeMap<&str, Vec<&ArchmapExtractionAdjudicationV1>> = BTreeMap::new();
    for row in merged_rows {
        let group = row.merge_group.as_deref().ok_or_else(|| {
            format!(
                "consistency {}: merged adjudication for key {} has no mergeGroup while \
                 other rows are group-structured; mixed records are not accepted",
                consistency.id, row.key
            )
        })?;
        if row.canonical_atom_id.is_none() {
            return Err(format!(
                "consistency {}: merged adjudication for key {} in group {} has no \
                 canonicalAtomId",
                consistency.id, row.key, group
            )
            .into());
        }
        groups.entry(group).or_default().push(row);
    }
    for (group, rows) in &groups {
        let mut sides = BTreeSet::new();
        let mut canonical = BTreeSet::new();
        for row in rows {
            let atom_id = row.candidate_atom_id.as_deref().unwrap_or_default();
            if let Some((_, side)) = atom_side.get(atom_id) {
                sides.insert(*side);
            }
            canonical.insert(row.canonical_atom_id.as_deref().unwrap_or_default());
        }
        if !sides.contains("pass-a") || !sides.contains("pass-b") {
            return Err(format!(
                "consistency {}: merge group {} does not join both passes \
                 (members from: {})",
                consistency.id,
                group,
                sides.into_iter().collect::<Vec<_>>().join(", ")
            )
            .into());
        }
        if canonical.len() != 1 {
            return Err(format!(
                "consistency {}: merge group {} members disagree on canonicalAtomId \
                 ({})",
                consistency.id,
                group,
                canonical.into_iter().collect::<Vec<_>>().join(", ")
            )
            .into());
        }
    }
    Ok(())
}

/// Legacy mode: adjudication rows carry keys only. Completeness is checked at
/// key granularity: the number of adjudication rows per key must equal the
/// number of unmatched onlyIn rows per key.
fn check_key_level_completeness(
    consistency: &ArchmapExtractionConsistencyV1,
    unmatched_atoms: &[(&str, &str, &str)],
) -> Result<(), Box<dyn Error>> {
    let mut expected: BTreeMap<&str, usize> = BTreeMap::new();
    for (_, key, _) in unmatched_atoms {
        *expected.entry(key).or_default() += 1;
    }
    let mut recorded: BTreeMap<&str, usize> = BTreeMap::new();
    for row in &consistency.adjudications {
        *recorded.entry(row.key.as_str()).or_default() += 1;
    }
    for key in recorded.keys() {
        if !expected.contains_key(key) {
            return Err(format!(
                "consistency {}: adjudication references key {} which is not in the \
                 onlyIn lists",
                consistency.id, key
            )
            .into());
        }
    }
    let incomplete: Vec<String> = expected
        .iter()
        .filter(|(key, count)| recorded.get(**key).copied().unwrap_or(0) != **count)
        .map(|(key, count)| {
            format!(
                "{key} (unmatched {count}, adjudicated {})",
                recorded.get(*key).copied().unwrap_or(0)
            )
        })
        .collect();
    if !incomplete.is_empty() {
        return Err(format!(
            "consistency {}: partial adjudication; adjudicated metrics are not \
             computable. Keys with missing or surplus adjudication rows include: {}",
            consistency.id,
            sample_keys(incomplete.iter().map(String::as_str))
        )
        .into());
    }
    Ok(())
}

fn key_convergence_metrics(
    consistency: &ArchmapExtractionConsistencyV1,
    adjudication: &AdjudicationCheck,
) -> SupplyBenchKeyConvergenceV1 {
    match adjudication.merge_groups {
        Some(groups) => {
            let matched = consistency.matched.count;
            let denominator = matched + groups;
            let rate = if denominator == 0 {
                1.0
            } else {
                matched as f64 / denominator as f64
            };
            SupplyBenchKeyConvergenceV1 {
                status: "computed".to_string(),
                reason: None,
                matched: Some(matched),
                merge_groups: Some(groups),
                adopted: Some(adjudication.adopted),
                not_adopted: Some(adjudication.not_adopted),
                rate: Some(rate),
            }
        }
        None => SupplyBenchKeyConvergenceV1 {
            status: "not-computable".to_string(),
            reason: Some(
                "adjudication record predates merge-group structure; same-fact pair \
                 count cannot be derived from merged row counts"
                    .to_string(),
            ),
            matched: Some(consistency.matched.count),
            merge_groups: None,
            adopted: Some(adjudication.adopted),
            not_adopted: Some(adjudication.not_adopted),
            rate: None,
        },
    }
}

fn reference_metrics(
    consistency: &ArchmapExtractionConsistencyV1,
    reference: &ArchmapReferenceSliceV1,
    alignment: &ArchmapReferenceAlignmentV1,
    pair_id: &str,
) -> Result<(SupplyBenchReferenceRecallV1, SupplyBenchOverGenerationV1), Box<dyn Error>> {
    if alignment.pair_ref != pair_id {
        return Err(format!(
            "alignment {} records pairRef {} but was supplied for pair {}",
            alignment.id, alignment.pair_ref, pair_id
        )
        .into());
    }
    if alignment.reference_ref != reference.id || alignment.reference_version != reference.version {
        return Err(format!(
            "alignment {} records reference {}@{} but the supplied reference slice is {}@{}",
            alignment.id,
            alignment.reference_ref,
            alignment.reference_version,
            reference.id,
            reference.version
        )
        .into());
    }
    if reference.atoms.is_empty() {
        return Err(format!("reference slice {} has no atoms", reference.id).into());
    }

    let reference_ids: BTreeSet<&str> = reference
        .atoms
        .iter()
        .map(|atom| atom.atom_id.as_str())
        .collect();
    if reference_ids.len() != reference.atoms.len() {
        return Err(format!(
            "reference slice {} contains duplicate atom ids",
            reference.id
        )
        .into());
    }

    let mut seen_reference: BTreeSet<&str> = BTreeSet::new();
    let mut seen_candidates: BTreeSet<&str> = BTreeSet::new();
    let mut adjudicated_recovered = 0usize;
    let mut not_adopted_atoms = 0usize;
    let mut novel_correct_atoms = 0usize;
    for row in &alignment.rows {
        match row.decision.as_str() {
            ALIGNMENT_DECISION_REFERENCE_MATCHED => {
                let reference_atom_id = require_reference_atom(alignment, row)?;
                require_candidates(alignment, row, true)?;
                claim_reference_atom(
                    alignment,
                    &reference_ids,
                    &mut seen_reference,
                    reference_atom_id,
                )?;
                adjudicated_recovered += 1;
            }
            ALIGNMENT_DECISION_UNRECOVERED => {
                let reference_atom_id = require_reference_atom(alignment, row)?;
                require_candidates(alignment, row, false)?;
                claim_reference_atom(
                    alignment,
                    &reference_ids,
                    &mut seen_reference,
                    reference_atom_id,
                )?;
            }
            ALIGNMENT_DECISION_NOVEL_CORRECT | ALIGNMENT_DECISION_NOT_ADOPTED => {
                if row.reference_atom_id.is_some() {
                    return Err(format!(
                        "alignment {}: a {} row must not name a referenceAtomId",
                        alignment.id, row.decision
                    )
                    .into());
                }
                require_candidates(alignment, row, true)?;
                if row.decision == ALIGNMENT_DECISION_NOT_ADOPTED {
                    not_adopted_atoms += row.candidate_atom_ids.len();
                } else {
                    novel_correct_atoms += row.candidate_atom_ids.len();
                }
            }
            other => {
                return Err(format!(
                    "alignment {}: unknown decision {other}; expected one of \
                     {ALIGNMENT_DECISION_REFERENCE_MATCHED}, {ALIGNMENT_DECISION_UNRECOVERED}, \
                     {ALIGNMENT_DECISION_NOVEL_CORRECT}, {ALIGNMENT_DECISION_NOT_ADOPTED}",
                    alignment.id
                )
                .into());
            }
        }
        for candidate in &row.candidate_atom_ids {
            if !seen_candidates.insert(candidate.as_str()) {
                return Err(format!(
                    "alignment {}: candidate atom {} appears in more than one row",
                    alignment.id, candidate
                )
                .into());
            }
        }
    }

    let missing_reference: Vec<&str> = reference_ids
        .iter()
        .filter(|atom_id| !seen_reference.contains(**atom_id))
        .copied()
        .collect();
    if !missing_reference.is_empty() {
        return Err(format!(
            "alignment {}: incomplete over the reference slice; every reference atom \
             needs a reference-matched or unrecovered row. Missing atoms include: {}",
            alignment.id,
            sample_keys(missing_reference.into_iter())
        )
        .into());
    }

    let pair_atoms = pair_candidate_atom_ids(consistency);
    let missing_candidates: Vec<&str> = pair_atoms
        .iter()
        .filter(|atom_id| !seen_candidates.contains(**atom_id))
        .copied()
        .collect();
    if !missing_candidates.is_empty() {
        return Err(format!(
            "alignment {}: incomplete over the supply; every candidate atom of pair {} \
             needs an alignment row. Missing atoms include: {}",
            alignment.id,
            pair_id,
            sample_keys(missing_candidates.into_iter())
        )
        .into());
    }
    let unknown_candidates: Vec<&str> = seen_candidates
        .iter()
        .filter(|atom_id| !pair_atoms.contains(**atom_id))
        .copied()
        .collect();
    if !unknown_candidates.is_empty() {
        return Err(format!(
            "alignment {}: references candidate atoms that are not in pair {}: {}",
            alignment.id,
            pair_id,
            sample_keys(unknown_candidates.into_iter())
        )
        .into());
    }

    let pair_keys: BTreeSet<&str> = consistency
        .matched
        .rows
        .iter()
        .map(|row| row.key.as_str())
        .chain(consistency.only_in_pass_a.iter().map(|row| row.key.as_str()))
        .chain(consistency.only_in_pass_b.iter().map(|row| row.key.as_str()))
        .collect();
    let mechanically_recovered = reference
        .atoms
        .iter()
        .filter(|atom| pair_keys.contains(atom.match_key.as_str()))
        .count();
    let reference_atoms = reference.atoms.len();
    let candidate_atoms = pair_atoms.len();

    Ok((
        SupplyBenchReferenceRecallV1 {
            reference_atoms,
            mechanically_recovered,
            mechanical_lower_bound: mechanically_recovered as f64 / reference_atoms as f64,
            adjudicated_recovered,
            adjudicated: adjudicated_recovered as f64 / reference_atoms as f64,
        },
        SupplyBenchOverGenerationV1 {
            candidate_atoms,
            not_adopted_atoms,
            novel_correct_atoms,
            rate: if candidate_atoms == 0 {
                0.0
            } else {
                not_adopted_atoms as f64 / candidate_atoms as f64
            },
        },
    ))
}

fn require_reference_atom<'a>(
    alignment: &ArchmapReferenceAlignmentV1,
    row: &'a ArchmapReferenceAlignmentRowV1,
) -> Result<&'a str, Box<dyn Error>> {
    row.reference_atom_id.as_deref().ok_or_else(|| {
        format!(
            "alignment {}: a {} row must name a referenceAtomId",
            alignment.id, row.decision
        )
        .into()
    })
}

fn require_candidates(
    alignment: &ArchmapReferenceAlignmentV1,
    row: &ArchmapReferenceAlignmentRowV1,
    expected: bool,
) -> Result<(), Box<dyn Error>> {
    if expected && row.candidate_atom_ids.is_empty() {
        return Err(format!(
            "alignment {}: a {} row must list at least one candidate atom",
            alignment.id, row.decision
        )
        .into());
    }
    if !expected && !row.candidate_atom_ids.is_empty() {
        return Err(format!(
            "alignment {}: an {} row must not list candidate atoms",
            alignment.id, row.decision
        )
        .into());
    }
    Ok(())
}

fn claim_reference_atom<'a>(
    alignment: &ArchmapReferenceAlignmentV1,
    reference_ids: &BTreeSet<&str>,
    seen: &mut BTreeSet<&'a str>,
    reference_atom_id: &'a str,
) -> Result<(), Box<dyn Error>> {
    if !reference_ids.contains(reference_atom_id) {
        return Err(format!(
            "alignment {}: references atom {} which is not in the reference slice",
            alignment.id, reference_atom_id
        )
        .into());
    }
    if !seen.insert(reference_atom_id) {
        return Err(format!(
            "alignment {}: reference atom {} appears in more than one row",
            alignment.id, reference_atom_id
        )
        .into());
    }
    Ok(())
}

fn pair_candidate_atom_ids(consistency: &ArchmapExtractionConsistencyV1) -> BTreeSet<&str> {
    consistency
        .matched
        .rows
        .iter()
        .flat_map(|row| {
            row.pass_a_atom_ids
                .iter()
                .chain(row.pass_b_atom_ids.iter())
                .map(String::as_str)
        })
        .chain(
            consistency
                .only_in_pass_a
                .iter()
                .map(|row| row.candidate_atom_id.as_str()),
        )
        .chain(
            consistency
                .only_in_pass_b
                .iter()
                .map(|row| row.candidate_atom_id.as_str()),
        )
        .collect()
}

fn aggregate_metrics<'a>(
    reports: impl Iterator<Item = &'a SupplyBenchPairReportV1>,
) -> BTreeMap<String, SupplyBenchStatV1> {
    let mut values: BTreeMap<&'static str, Vec<f64>> = BTreeMap::new();
    for report in reports {
        values
            .entry("machineMatchRate")
            .or_default()
            .push(report.machine_match_rate);
        if let Some(rate) = report.key_convergence.rate {
            values.entry("keyConvergenceRate").or_default().push(rate);
        }
        if let Some(recall) = &report.reference_recall {
            values
                .entry("referenceRecallMechanicalLowerBound")
                .or_default()
                .push(recall.mechanical_lower_bound);
            values
                .entry("referenceRecallAdjudicated")
                .or_default()
                .push(recall.adjudicated);
        }
        if let Some(over) = &report.over_generation {
            values.entry("overGenerationRate").or_default().push(over.rate);
        }
    }
    values
        .into_iter()
        .map(|(metric, series)| {
            let min = series.iter().copied().fold(f64::INFINITY, f64::min);
            let max = series.iter().copied().fold(f64::NEG_INFINITY, f64::max);
            let mean = series.iter().sum::<f64>() / series.len() as f64;
            (
                metric.to_string(),
                SupplyBenchStatV1 {
                    pairs: series.len(),
                    min,
                    max,
                    mean,
                },
            )
        })
        .collect()
}

fn sample_keys<'a>(keys: impl Iterator<Item = &'a str>) -> String {
    let collected: Vec<&str> = keys.collect();
    let total = collected.len();
    let shown: Vec<&str> = collected.into_iter().take(5).collect();
    if total > shown.len() {
        format!("{} (and {} more)", shown.join(", "), total - shown.len())
    } else {
        shown.join(", ")
    }
}

fn load_consistency(path: &PathBuf) -> Result<ArchmapExtractionConsistencyV1, Box<dyn Error>> {
    let value = read_json_value(path)?;
    let schema = value.get("schema").and_then(|schema| schema.as_str());
    if schema != Some(ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA) {
        return Err(format!(
            "{}: schema must be {ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA}, got {}",
            path.display(),
            schema.unwrap_or("<missing>")
        )
        .into());
    }
    serde_json::from_value(value)
        .map_err(|error| format!("{}: {error}", path.display()).into())
}

fn load_reference_slice(path: &PathBuf) -> Result<ArchmapReferenceSliceV1, Box<dyn Error>> {
    let value = read_json_value(path)?;
    let schema = value.get("schema").and_then(|schema| schema.as_str());
    if schema != Some(ARCHMAP_REFERENCE_SLICE_V1_SCHEMA) {
        return Err(format!(
            "{}: schema must be {ARCHMAP_REFERENCE_SLICE_V1_SCHEMA}, got {}",
            path.display(),
            schema.unwrap_or("<missing>")
        )
        .into());
    }
    serde_json::from_value(value)
        .map_err(|error| format!("{}: {error}", path.display()).into())
}

fn load_alignment(path: &PathBuf) -> Result<ArchmapReferenceAlignmentV1, Box<dyn Error>> {
    let value = read_json_value(path)?;
    let schema = value.get("schema").and_then(|schema| schema.as_str());
    if schema != Some(ARCHMAP_REFERENCE_ALIGNMENT_V1_SCHEMA) {
        return Err(format!(
            "{}: schema must be {ARCHMAP_REFERENCE_ALIGNMENT_V1_SCHEMA}, got {}",
            path.display(),
            schema.unwrap_or("<missing>")
        )
        .into());
    }
    serde_json::from_value(value)
        .map_err(|error| format!("{}: {error}", path.display()).into())
}

fn read_json_value(path: &PathBuf) -> Result<serde_json::Value, Box<dyn Error>> {
    let file =
        File::open(path).map_err(|error| format!("{}: {error}", path.display()))?;
    serde_json::from_reader(file)
        .map_err(|error| format!("{} is not valid JSON: {error}", path.display()).into())
}
