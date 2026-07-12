use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::{self, File};
use std::io::Read;
use std::path::Component;
use std::path::{Path, PathBuf};
use std::process::Command;

use globset::{Glob, GlobSet, GlobSetBuilder};
use sha2::{Digest, Sha256};
use unicode_normalization::UnicodeNormalization;
use walkdir::WalkDir;

use crate::{
    ArchMapAtomV2, ArchMapDocumentV2, ArchMapSource, ArchmapCandidatePacketV1,
    ArchmapCoverageLedgerV1, ArchmapExtractionConsistencyV1, ArchmapExtractionContextDiffV1,
    ArchmapExtractionMatchCountV1, ArchmapExtractionMatchedCandidateV1,
    ArchmapExtractionOnlyInCandidateV1, ArchmapScopeManifestExclusionV1,
    ArchmapScopeManifestRepositoryV1, ArchmapScopeManifestScopeSpecV1, ArchmapScopeManifestV1,
    ArchmapScopeManifestWorklistEntryV1, ValidationCheck, ValidationExample,
};

pub const ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA: &str = "archmap-scope-manifest/v0.5.1";
pub const ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA: &str = "archmap-candidate-packet/v0.5.1";
pub const ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA: &str = "archmap-extraction-consistency/v0.5.1";
pub const ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA: &str = "archmap-coverage-ledger/v0.5.1";
pub const ARCHMAP_COVERAGE_LEDGER_CLAIM_BOUNDARY: &str = "Rows record the authoring survey of the selected scope at the recorded revision. They do not assert extraction completeness.";
const EXCLUSION_REASONS: [&str; 5] = [
    "user-excluded",
    "private",
    "generated",
    "binary",
    "out-of-scope",
];

#[derive(Debug, Clone)]
pub struct ScopeManifestOptions {
    pub repo_root: PathBuf,
    pub include_globs: Vec<String>,
    pub exclude_globs: Vec<String>,
    pub added_evidence: Vec<String>,
    pub requested_scope: Option<String>,
    pub approved_by: Option<String>,
    pub id: String,
    pub baseline: Option<PathBuf>,
    pub revision_override: Option<String>,
    pub dirty_override: Option<bool>,
}

#[derive(Debug, Clone)]
pub struct ExtractionDiffOptions {
    pub pass_a: Vec<PathBuf>,
    pub pass_b: Vec<PathBuf>,
    pub id: String,
    pub scope_manifest_ref: Option<String>,
}

#[derive(Debug, Clone)]
pub struct AuthoringAuditInputV1 {
    pub scope_manifest: ArchmapScopeManifestV1,
    pub candidate_packets: Vec<ArchmapCandidatePacketV1>,
    pub extraction_consistency: Vec<ArchmapExtractionConsistencyV1>,
    pub coverage_ledger: ArchmapCoverageLedgerV1,
}

pub fn build_scope_manifest_v1(
    options: &ScopeManifestOptions,
) -> Result<ArchmapScopeManifestV1, Box<dyn Error>> {
    let root = options.repo_root.canonicalize()?;
    let exclusions = options
        .exclude_globs
        .iter()
        .map(|spec| parse_exclusion_spec(spec))
        .collect::<Result<Vec<_>, _>>()?;
    let exclude_globs = exclusions
        .iter()
        .map(|(_, glob)| glob.clone())
        .collect::<Vec<_>>();
    for pattern in options.include_globs.iter().chain(exclude_globs.iter()) {
        reject_repo_relative_glob(pattern)?;
    }
    let include_set = build_glob_set(&options.include_globs)?;
    let exclude_set = build_glob_set(&exclude_globs)?;
    let mut entries = Vec::new();

    for entry in WalkDir::new(&root).follow_links(false).into_iter() {
        let entry = entry?;
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.path();
        let relative = repo_relative_path(&root, path)?;
        if !include_set.is_match(&relative) || exclude_set.is_match(&relative) {
            continue;
        }
        entries.push(worklist_entry(&root, &relative, false, None)?);
    }

    entries.sort_by(|left, right| left.path.as_bytes().cmp(right.path.as_bytes()));

    let mut scanned_paths: BTreeSet<String> =
        entries.iter().map(|entry| entry.path.clone()).collect();
    let mut added_entries = Vec::new();
    let mut added_specs = Vec::new();
    for spec in &options.added_evidence {
        let evidence = parse_added_evidence(spec)?;
        reject_non_repo_relative_path(&evidence.path)?;
        if !scanned_paths.insert(evidence.path.clone()) {
            return Err(format!(
                "--add-evidence path is already present in scanned worklist: {}",
                evidence.path
            )
            .into());
        }
        let path = root.join(&evidence.path);
        if !path.is_file() {
            return Err(format!("--add-evidence path is not a file: {}", evidence.path).into());
        }
        let canonical = path.canonicalize()?;
        if !canonical.starts_with(&root) {
            return Err(format!("--add-evidence path escapes repo root: {}", evidence.path).into());
        }
        added_specs.push(spec.clone());
        added_entries.push(worklist_entry(
            &root,
            &evidence.path,
            true,
            Some(format!("{}:{}", evidence.kind, evidence.name)),
        )?);
    }
    added_entries.sort_by(|left, right| left.source_id.cmp(&right.source_id));
    entries.extend(added_entries);

    let baseline_ref = if let Some(baseline_path) = &options.baseline {
        let baseline: ArchmapScopeManifestV1 =
            serde_json::from_reader(fs::File::open(baseline_path)?)?;
        let baseline_ref = baseline.id.clone();
        let baseline_hashes: BTreeMap<_, _> = baseline
            .worklist
            .iter()
            .map(|entry| (entry.source_id.clone(), entry.content_hash.clone()))
            .collect();
        entries.retain(|entry| {
            baseline_hashes
                .get(&entry.source_id)
                .is_none_or(|hash| hash != &entry.content_hash)
        });
        Some(baseline_ref)
    } else {
        None
    };

    for (index, entry) in entries.iter_mut().enumerate() {
        entry.order = index + 1;
    }

    Ok(ArchmapScopeManifestV1 {
        schema: ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA.to_string(),
        id: options.id.clone(),
        repository: ArchmapScopeManifestRepositoryV1 {
            root: ".".to_string(),
            revision: options
                .revision_override
                .clone()
                .or_else(|| git_revision(&root)),
            dirty: options.dirty_override.or_else(|| git_dirty(&root)),
        },
        scope_spec: ArchmapScopeManifestScopeSpecV1 {
            include_globs: options.include_globs.clone(),
            exclude_globs: exclude_globs.clone(),
            added_evidence: added_specs,
            requested_scope: options.requested_scope.clone(),
            approved_by: options.approved_by.clone(),
        },
        baseline_ref,
        worklist: entries,
        exclusions: exclusions
            .into_iter()
            .map(|(reason, path)| ArchmapScopeManifestExclusionV1 { path, reason })
            .collect(),
    })
}

fn parse_exclusion_spec(spec: &str) -> Result<(String, String), Box<dyn Error>> {
    let Some((reason, glob)) = spec.split_once(':') else {
        return Ok(("user-excluded".to_string(), spec.to_string()));
    };
    if EXCLUSION_REASONS.contains(&reason) && !glob.trim().is_empty() {
        Ok((reason.to_string(), glob.to_string()))
    } else {
        Err(format!(
            "--exclude reason must be one of {}; use --exclude <glob> for user-excluded",
            EXCLUSION_REASONS.join(", ")
        )
        .into())
    }
}

pub fn build_extraction_consistency_v1(
    options: &ExtractionDiffOptions,
) -> Result<ArchmapExtractionConsistencyV1, Box<dyn Error>> {
    if options.pass_a.is_empty() {
        return Err("--pass-a is required".into());
    }
    let pass_a = load_candidate_packets(&options.pass_a, "pass-a")?;
    let pass_b = load_candidate_packets(&options.pass_b, "pass-b")?;
    let scope_manifest_ref = options
        .scope_manifest_ref
        .clone()
        .or_else(|| {
            pass_a
                .first()
                .map(|packet| packet.scope_manifest_ref.clone())
        })
        .unwrap_or_else(|| "scope:unknown".to_string());

    let pass_a_refs = pass_a
        .iter()
        .map(|packet| packet.id.clone())
        .collect::<Vec<_>>();
    let pass_b_refs = pass_b
        .iter()
        .map(|packet| packet.id.clone())
        .collect::<Vec<_>>();
    let pass_a_atoms = candidate_atom_index(&pass_a);
    let pass_b_atoms = candidate_atom_index(&pass_b);
    let matched_rows = matched_candidates(&pass_a_atoms, &pass_b_atoms);
    let matched_count = matched_rows
        .iter()
        .map(|row| row.pass_a_atom_ids.len().min(row.pass_b_atom_ids.len()))
        .sum();
    let only_in_pass_a = only_in_candidates(&pass_a_atoms, &pass_b_atoms);
    let only_in_pass_b = only_in_candidates(&pass_b_atoms, &pass_a_atoms);
    let denominator = matched_count + only_in_pass_a.len() + only_in_pass_b.len();
    let match_rate = if denominator == 0 {
        1.0
    } else {
        matched_count as f64 / denominator as f64
    };
    let context_diff = context_diff(&pass_a, &pass_b);

    Ok(ArchmapExtractionConsistencyV1 {
        schema: ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA.to_string(),
        id: options.id.clone(),
        scope_manifest_ref,
        pass_a_refs,
        pass_b_refs,
        atom_match_key_spec: "kind | NFC(trim(subject)) | axis | predicate? | object?".to_string(),
        matched: ArchmapExtractionMatchCountV1 {
            count: matched_count,
            rows: matched_rows,
        },
        only_in_pass_a,
        only_in_pass_b,
        match_rate,
        context_diff,
        adjudications: vec![],
    })
}

fn load_candidate_packets(
    paths: &[PathBuf],
    label: &str,
) -> Result<Vec<ArchmapCandidatePacketV1>, Box<dyn Error>> {
    let mut packets = Vec::new();
    for path in paths {
        let packet: ArchmapCandidatePacketV1 = serde_json::from_reader(File::open(path)?)?;
        if let Err(errors) = validate_candidate_packet_v1(&packet) {
            return Err(format!(
                "{label} candidate packet {} failed validation: {}",
                path.display(),
                errors.join("; ")
            )
            .into());
        }
        packets.push(packet);
    }
    Ok(packets)
}

fn candidate_atom_index(
    packets: &[ArchmapCandidatePacketV1],
) -> BTreeMap<String, Vec<ArchMapAtomV2>> {
    let mut index: BTreeMap<String, Vec<ArchMapAtomV2>> = BTreeMap::new();
    for packet in packets {
        for atom in &packet.candidate_atoms {
            index
                .entry(atom_match_key(atom))
                .or_default()
                .push(atom.clone());
        }
    }
    index
}

fn matched_candidates(
    pass_a_atoms: &BTreeMap<String, Vec<ArchMapAtomV2>>,
    pass_b_atoms: &BTreeMap<String, Vec<ArchMapAtomV2>>,
) -> Vec<ArchmapExtractionMatchedCandidateV1> {
    let mut rows = Vec::new();
    for (key, pass_a) in pass_a_atoms {
        if let Some(pass_b) = pass_b_atoms.get(key) {
            let matched = pass_a.len().min(pass_b.len());
            if matched == 0 {
                continue;
            }
            let pass_a_matched = &pass_a[..matched];
            let pass_b_matched = &pass_b[..matched];
            let refs = pass_a_matched
                .iter()
                .chain(pass_b_matched.iter())
                .flat_map(|atom| atom.refs.iter().cloned())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            rows.push(ArchmapExtractionMatchedCandidateV1 {
                key: key.clone(),
                pass_a_atom_ids: pass_a_matched.iter().map(|atom| atom.id.clone()).collect(),
                pass_b_atom_ids: pass_b_matched.iter().map(|atom| atom.id.clone()).collect(),
                refs,
            });
        }
    }
    rows
}

fn only_in_candidates(
    source_atoms: &BTreeMap<String, Vec<ArchMapAtomV2>>,
    other_atoms: &BTreeMap<String, Vec<ArchMapAtomV2>>,
) -> Vec<ArchmapExtractionOnlyInCandidateV1> {
    let mut rows = Vec::new();
    for (key, atoms) in source_atoms {
        let matched = other_atoms.get(key).map(Vec::len).unwrap_or(0);
        for atom in atoms.iter().skip(matched) {
            rows.push(ArchmapExtractionOnlyInCandidateV1 {
                key: key.clone(),
                candidate_atom_id: atom.id.clone(),
                refs: atom.refs.clone(),
            });
        }
    }
    rows
}

fn context_diff(
    pass_a: &[ArchmapCandidatePacketV1],
    pass_b: &[ArchmapCandidatePacketV1],
) -> ArchmapExtractionContextDiffV1 {
    let pass_a_keys = context_keys(pass_a);
    let pass_b_keys = context_keys(pass_b);
    ArchmapExtractionContextDiffV1 {
        matched: pass_a_keys.intersection(&pass_b_keys).count(),
        only_in_pass_a: pass_a_keys.difference(&pass_b_keys).cloned().collect(),
        only_in_pass_b: pass_b_keys.difference(&pass_a_keys).cloned().collect(),
    }
}

fn context_keys(packets: &[ArchmapCandidatePacketV1]) -> BTreeSet<String> {
    let mut keys = BTreeSet::new();
    for packet in packets {
        let atom_keys = packet
            .candidate_atoms
            .iter()
            .map(|atom| (atom.id.clone(), atom_match_key(atom)))
            .collect::<BTreeMap<_, _>>();
        let context_members = packet
            .candidate_contexts
            .iter()
            .map(|context| {
                let mut members = context
                    .atoms
                    .iter()
                    .map(|atom_id| {
                        atom_keys
                            .get(atom_id)
                            .cloned()
                            .unwrap_or_else(|| format!("unresolved-atom:{atom_id}"))
                    })
                    .collect::<Vec<_>>();
                members.sort();
                (context.id.clone(), members)
            })
            .collect::<BTreeMap<_, _>>();
        let context_restricts = packet
            .candidate_contexts
            .iter()
            .map(|context| (context.id.clone(), context.restricts_to.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut memo = BTreeMap::new();
        for context in &packet.candidate_contexts {
            keys.insert(resolve_context_key(
                &context.id,
                &context_members,
                &context_restricts,
                &mut memo,
                &mut BTreeSet::new(),
            ));
        }
    }
    keys
}

fn resolve_context_key(
    context_id: &str,
    context_members: &BTreeMap<String, Vec<String>>,
    context_restricts: &BTreeMap<String, Vec<String>>,
    memo: &mut BTreeMap<String, String>,
    stack: &mut BTreeSet<String>,
) -> String {
    if let Some(key) = memo.get(context_id) {
        return key.clone();
    }
    if !stack.insert(context_id.to_string()) {
        return format!("cycle-context:{context_id}");
    }
    let members = context_members
        .get(context_id)
        .cloned()
        .unwrap_or_else(|| vec![format!("unresolved-context:{context_id}")]);
    let mut restricts = context_restricts
        .get(context_id)
        .cloned()
        .unwrap_or_default()
        .iter()
        .map(|target| resolve_context_key(target, context_members, context_restricts, memo, stack))
        .collect::<Vec<_>>();
    restricts.sort();
    stack.remove(context_id);
    let key = format!(
        "members=[{}]|restrictsTo=[{}]",
        members.join(","),
        restricts.join(",")
    );
    memo.insert(context_id.to_string(), key.clone());
    key
}

fn atom_match_key(atom: &ArchMapAtomV2) -> String {
    let normalized_subject = atom.subject.trim().nfc().collect::<String>();
    [
        atom.kind.as_str(),
        normalized_subject.as_str(),
        atom.axis.as_str(),
        atom.predicate.as_deref().unwrap_or(""),
        atom.object.as_deref().unwrap_or(""),
    ]
    .join("|")
}

fn reject_non_repo_relative_path(path: &str) -> Result<(), Box<dyn Error>> {
    reject_repo_relative_path(path).map_err(Into::into)
}

fn reject_repo_relative_path(path: &str) -> Result<(), String> {
    let candidate = Path::new(path);
    if path.trim().is_empty() {
        return Err("path must be non-empty".to_string());
    }
    if contains_local_marker(path) {
        return Err("path must not contain local or private workspace markers".to_string());
    }
    if candidate.is_absolute() {
        return Err("path must be repo-relative".to_string());
    }
    if candidate.components().any(|component| {
        matches!(
            component,
            Component::ParentDir | Component::Prefix(_) | Component::RootDir
        )
    }) {
        return Err("path must not escape the repo root".to_string());
    }
    Ok(())
}

fn reject_repo_relative_glob(pattern: &str) -> Result<(), Box<dyn Error>> {
    if pattern.trim().is_empty() {
        return Err("glob must be non-empty".into());
    }
    if contains_local_marker(pattern) {
        return Err(
            format!("glob must not contain local or private workspace markers: {pattern}").into(),
        );
    }
    let candidate = Path::new(pattern);
    if candidate.is_absolute() {
        return Err(format!("glob must be repo-relative: {pattern}").into());
    }
    if candidate.components().any(|component| {
        matches!(
            component,
            Component::ParentDir | Component::Prefix(_) | Component::RootDir
        )
    }) {
        return Err(format!("glob must not escape the repo root: {pattern}").into());
    }
    Ok(())
}

struct AddedEvidence {
    kind: String,
    name: String,
    path: String,
}

fn parse_added_evidence(spec: &str) -> Result<AddedEvidence, Box<dyn Error>> {
    let (left, path) = spec
        .split_once('=')
        .ok_or("--add-evidence must be <kind>:<name>=<repo-relative-path>")?;
    let (kind, name) = left
        .split_once(':')
        .ok_or("--add-evidence must be <kind>:<name>=<repo-relative-path>")?;
    if kind.trim().is_empty() || name.trim().is_empty() || path.trim().is_empty() {
        return Err("--add-evidence kind, name, and path must be non-empty".into());
    }
    Ok(AddedEvidence {
        kind: kind.to_string(),
        name: name.to_string(),
        path: normalize_slashes(path),
    })
}

fn build_glob_set(patterns: &[String]) -> Result<GlobSet, Box<dyn Error>> {
    let mut builder = GlobSetBuilder::new();
    for pattern in patterns {
        builder.add(Glob::new(pattern)?);
    }
    Ok(builder.build()?)
}

fn worklist_entry(
    root: &Path,
    relative: &str,
    author_added: bool,
    source_id: Option<String>,
) -> Result<ArchmapScopeManifestWorklistEntryV1, Box<dyn Error>> {
    let path = root.join(relative);
    let mut hasher = Sha256::new();
    let mut file = File::open(&path)?;
    let size_bytes = file.metadata()?.len();
    let mut buffer = [0_u8; 8192];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    let content_hash = format!("sha256:{:x}", hasher.finalize());
    Ok(ArchmapScopeManifestWorklistEntryV1 {
        order: 0,
        source_id: source_id.unwrap_or_else(|| format!("src:{relative}")),
        path: relative.to_string(),
        kind: source_kind(relative),
        content_hash,
        size_bytes,
        author_added,
    })
}

pub fn validate_scope_manifest_v1(manifest: &ArchmapScopeManifestV1) -> Result<(), Vec<String>> {
    let mut errors = Vec::new();
    if manifest.schema != ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA {
        errors.push(format!(
            "schema must be {ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA}, got {}",
            manifest.schema
        ));
    }
    for (index, pattern) in manifest.scope_spec.include_globs.iter().enumerate() {
        if let Err(error) = validate_repo_relative_glob(pattern) {
            errors.push(format!("scopeSpec.includeGlobs[{index}] {error}"));
        }
    }
    for (index, pattern) in manifest.scope_spec.exclude_globs.iter().enumerate() {
        if let Err(error) = validate_repo_relative_glob(pattern) {
            errors.push(format!("scopeSpec.excludeGlobs[{index}] {error}"));
        }
    }
    for (index, entry) in manifest.worklist.iter().enumerate() {
        if entry.order != index + 1 {
            errors.push(format!(
                "worklist[{}].order must be {}, got {}",
                index,
                index + 1,
                entry.order
            ));
        }
        if let Err(error) = reject_repo_relative_path(&entry.path) {
            errors.push(format!("worklist[{}].path {error}", index));
        }
        if !entry.content_hash.starts_with("sha256:") {
            errors.push(format!("worklist[{}].contentHash must use sha256:", index));
        }
    }
    for (index, exclusion) in manifest.exclusions.iter().enumerate() {
        if let Err(error) = reject_repo_relative_path(&exclusion.path) {
            errors.push(format!("exclusions[{}].path {error}", index));
        }
        if !EXCLUSION_REASONS.contains(&exclusion.reason.as_str()) {
            errors.push(format!(
                "exclusions[{}].reason must be user-excluded, private, generated, binary, or out-of-scope",
                index
            ));
        }
    }
    validation_result(errors)
}

pub fn validate_candidate_packet_v1(packet: &ArchmapCandidatePacketV1) -> Result<(), Vec<String>> {
    let mut errors = Vec::new();
    if packet.schema != ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA {
        errors.push(format!(
            "schema must be {ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA}, got {}",
            packet.schema
        ));
    }
    for (index, note) in packet.private_unavailable_notes.iter().enumerate() {
        validate_public_text(
            &format!("privateUnavailableNotes[{index}]"),
            note,
            &mut errors,
        );
    }
    for (source_id, source) in &packet.candidate_sources {
        if let Some(path) = &source.path {
            validate_public_text(
                &format!("candidateSources[{source_id}].path"),
                path,
                &mut errors,
            );
        }
        if let Some(source_text) = &source.source {
            validate_public_text(
                &format!("candidateSources[{source_id}].source"),
                source_text,
                &mut errors,
            );
        }
    }
    for (index, row) in packet.survey_rows.iter().enumerate() {
        if !matches!(row.status.as_str(), "read" | "partial" | "skipped") {
            errors.push(format!(
                "surveyRows[{}].status must be read, partial, or skipped",
                index
            ));
        }
        if matches!(row.status.as_str(), "partial" | "skipped")
            && row.reason.as_deref().unwrap_or_default().is_empty()
        {
            errors.push(format!(
                "surveyRows[{}].reason is required when status is partial or skipped",
                index
            ));
        }
        if let Some(reason) = &row.reason {
            validate_candidate_reason(&format!("surveyRows[{index}].reason"), reason, &mut errors);
        }
        for (note_index, note) in row.notes.iter().enumerate() {
            validate_public_text(
                &format!("surveyRows[{index}].notes[{note_index}]"),
                note,
                &mut errors,
            );
        }
    }
    for (index, atom) in packet.candidate_atoms.iter().enumerate() {
        validate_semantic_atom_object(index, atom, &mut errors);
        validate_no_diagnostic_shortcut(index, atom, &mut errors);
        for (ref_index, source_ref) in atom.refs.iter().enumerate() {
            validate_public_text(
                &format!("candidateAtoms[{index}].refs[{ref_index}]"),
                source_ref,
                &mut errors,
            );
        }
    }
    validate_self_review_gate(&packet.self_review, &mut errors);
    validation_result(errors)
}

pub fn validate_extraction_consistency_v1(
    report: &ArchmapExtractionConsistencyV1,
) -> Result<(), Vec<String>> {
    let mut errors = Vec::new();
    if report.schema != ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA {
        errors.push(format!(
            "schema must be {ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA}, got {}",
            report.schema
        ));
    }
    let denominator =
        report.matched.count + report.only_in_pass_a.len() + report.only_in_pass_b.len();
    let expected = if denominator == 0 {
        1.0
    } else {
        report.matched.count as f64 / denominator as f64
    };
    if (report.match_rate - expected).abs() > 1e-12 {
        errors.push(format!(
            "matchRate must equal matched/(matched+onlyInPassA+onlyInPassB): expected {expected}, got {}",
            report.match_rate
        ));
    }
    for (index, adjudication) in report.adjudications.iter().enumerate() {
        if !matches!(
            adjudication.decision.as_str(),
            "adopted" | "merged" | "not-adopted"
        ) {
            errors.push(format!(
                "adjudications[{}].decision must be adopted, merged, or not-adopted",
                index
            ));
        }
        validate_public_text(
            &format!("adjudications[{index}].basis"),
            &adjudication.basis,
            &mut errors,
        );
    }
    validation_result(errors)
}

pub fn validate_coverage_ledger_v1(ledger: &ArchmapCoverageLedgerV1) -> Result<(), Vec<String>> {
    let mut errors = Vec::new();
    if ledger.schema != ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA {
        errors.push(format!(
            "schema must be {ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA}, got {}",
            ledger.schema
        ));
    }
    if ledger.claim_boundary != ARCHMAP_COVERAGE_LEDGER_CLAIM_BOUNDARY {
        errors
            .push("claimBoundary must match the fixed selected-scope survey boundary".to_string());
    }
    for (index, row) in ledger.rows.iter().enumerate() {
        if !matches!(
            row.survey_status.as_str(),
            "surveyed" | "partially_surveyed" | "not_surveyed"
        ) {
            errors.push(format!(
                "rows[{}].surveyStatus must be surveyed, partially_surveyed, or not_surveyed",
                index
            ));
        }
        if matches!(
            row.survey_status.as_str(),
            "partially_surveyed" | "not_surveyed"
        ) && row.reason.as_deref().unwrap_or_default().is_empty()
        {
            errors.push(format!(
                "rows[{}].reason is required when surveyStatus is partial or not surveyed",
                index
            ));
        }
        if let Some(reason) = &row.reason {
            if !matches!(
                reason.as_str(),
                "private" | "binary" | "unreadable" | "tooling-error"
            ) {
                errors.push(format!(
                    "rows[{}].reason must be private, binary, unreadable, or tooling-error",
                    index
                ));
            }
        }
    }
    validation_result(errors)
}

pub fn validate_authoring_audit_input_v1(input: &AuthoringAuditInputV1) -> Result<(), Vec<String>> {
    let mut errors = Vec::new();
    if let Err(scope_errors) = validate_scope_manifest_v1(&input.scope_manifest) {
        errors.extend(
            scope_errors
                .into_iter()
                .map(|error| format!("scopeManifest {error}")),
        );
    }
    for (index, packet) in input.candidate_packets.iter().enumerate() {
        if let Err(packet_errors) = validate_candidate_packet_v1(packet) {
            errors.extend(
                packet_errors
                    .into_iter()
                    .map(|error| format!("candidatePackets[{index}] {error}")),
            );
        }
    }
    if input.candidate_packets.is_empty() {
        errors.push("candidatePackets must contain at least one packet".to_string());
    }
    for (index, consistency) in input.extraction_consistency.iter().enumerate() {
        if let Err(consistency_errors) = validate_extraction_consistency_v1(consistency) {
            errors.extend(
                consistency_errors
                    .into_iter()
                    .map(|error| format!("extractionConsistency[{index}] {error}")),
            );
        }
    }
    if let Err(ledger_errors) = validate_coverage_ledger_v1(&input.coverage_ledger) {
        errors.extend(
            ledger_errors
                .into_iter()
                .map(|error| format!("coverageLedger {error}")),
        );
    }
    validation_result(errors)
}

pub fn archmap_authoring_audit_checks_v1(
    archmap: &ArchMapDocumentV2,
    input: &AuthoringAuditInputV1,
) -> Vec<ValidationCheck> {
    vec![
        check_authoring_revision_recorded(&input.scope_manifest),
        check_authoring_sources_resolve(archmap, input),
        check_authoring_provenance_closure(archmap, input),
        check_authoring_ledger_spans_worklist(input),
        check_authoring_read_before_cite(archmap, input),
        check_authoring_survey_traceable_within_scope(archmap, input),
    ]
}

fn check_authoring_revision_recorded(manifest: &ArchmapScopeManifestV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if manifest
        .repository
        .revision
        .as_deref()
        .unwrap_or_default()
        .is_empty()
    {
        examples.push(validation_example(
            "scopeManifest.repository.revision",
            "missing",
            "scope manifest must record the source revision used for authoring",
        ));
    }
    let mut check = check_from_examples(
        "authoring-revision-recorded",
        "scope manifest records repository revision; dirty state is reported separately",
        examples,
    );
    if let Some(dirty) = manifest.repository.dirty {
        check.reason = Some(format!("repository.dirty={dirty}"));
    }
    check
}

fn check_authoring_sources_resolve(
    archmap: &ArchMapDocumentV2,
    input: &AuthoringAuditInputV1,
) -> ValidationCheck {
    let worklist = worklist_index(&input.scope_manifest);
    let mut examples = Vec::new();
    for (source_id, source) in &archmap.sources {
        if source_is_grounding_exempt(source_id, source) {
            continue;
        }
        if !source_resolves_to_worklist(source_id, source, &worklist) {
            examples.push(validation_example(
                "sources",
                source_id,
                "source must resolve through src: direct id, doc: path part, or authorAdded worklist evidence",
            ));
        }
    }
    check_from_examples(
        "authoring-sources-resolve",
        "ArchMap sources resolve inside the author-approved scope, with grounding-kind exemptions",
        examples,
    )
}

fn check_authoring_provenance_closure(
    archmap: &ArchMapDocumentV2,
    input: &AuthoringAuditInputV1,
) -> ValidationCheck {
    let ledger_atoms = ledger_adopted_atoms(&input.coverage_ledger);
    let survey_atoms = survey_row_provenance_atoms(&input.candidate_packets);
    let adjudicated_keys = adopted_adjudication_keys(&input.extraction_consistency);
    let mut examples = Vec::new();
    examples.extend(artifact_ref_examples(archmap, input));
    for atom in &archmap.atoms {
        if !ledger_atoms.contains(&atom.id) {
            examples.push(validation_example(
                &atom.id,
                "coverageLedger.rows[].adoptedAtomIds",
                "adopted ArchMap atom must be present in the coverage ledger",
            ));
        } else if !survey_atoms.contains(&atom.id)
            && !adjudicated_keys.contains(&atom_match_key(atom))
        {
            examples.push(validation_example(
                &atom.id,
                "candidatePackets[].surveyRows[].candidateAtomIds",
                "adopted ArchMap atom must trace to a survey row or adopted/merged adjudication",
            ));
        }
    }
    check_from_examples(
        "authoring-provenance-closure",
        "adopted ArchMap atoms close through candidate survey provenance, adjudications, and aligned artifact refs",
        examples,
    )
}

fn check_authoring_ledger_spans_worklist(input: &AuthoringAuditInputV1) -> ValidationCheck {
    let worklist = source_id_counts(
        input
            .scope_manifest
            .worklist
            .iter()
            .map(|entry| entry.source_id.as_str()),
    );
    let ledger = source_id_counts(
        input
            .coverage_ledger
            .rows
            .iter()
            .map(|row| row.source_id.as_str()),
    );
    let worklist_ids = worklist.keys().copied().collect::<BTreeSet<_>>();
    let ledger_ids = ledger.keys().copied().collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    for missing in worklist_ids.difference(&ledger_ids) {
        examples.push(validation_example(
            "scopeManifest.worklist[].sourceId",
            missing,
            "coverage ledger must contain every worklist source",
        ));
    }
    for extra in ledger_ids.difference(&worklist_ids) {
        examples.push(validation_example(
            "coverageLedger.rows[].sourceId",
            extra,
            "coverage ledger must not include sources outside the worklist",
        ));
    }
    for (source_id, count) in &ledger {
        if *count != 1 {
            examples.push(validation_example(
                "coverageLedger.rows[].sourceId",
                source_id,
                "coverage ledger must contain exactly one row for each worklist source",
            ));
        }
    }
    check_from_examples(
        "authoring-ledger-spans-worklist",
        "coverage ledger spans exactly the scope manifest worklist",
        examples,
    )
}

fn check_authoring_read_before_cite(
    archmap: &ArchMapDocumentV2,
    input: &AuthoringAuditInputV1,
) -> ValidationCheck {
    let mut examples = Vec::new();
    for citation in cited_refs(archmap) {
        if citation.owner_kind != "atom" {
            if let Some(source) = archmap.sources.get(&citation.source_ref) {
                if source_is_grounding_exempt(&citation.source_ref, source) {
                    continue;
                }
            }
        }
        if !citation_was_surveyed(&citation.source_ref, input) {
            examples.push(validation_example(
                &citation.owner,
                &citation.source_ref,
                "source ref must have a read survey row, or an exact partial survey row for the cited section, before it is cited",
            ));
        }
    }
    check_from_examples(
        "authoring-read-before-cite",
        "ArchMap citations only use sources that were read in candidate survey rows; grounding exemptions apply to context and cover refs only",
        examples,
    )
}

fn check_authoring_survey_traceable_within_scope(
    archmap: &ArchMapDocumentV2,
    input: &AuthoringAuditInputV1,
) -> ValidationCheck {
    let mut examples = Vec::new();
    for check in [
        check_authoring_revision_recorded(&input.scope_manifest),
        check_authoring_sources_resolve(archmap, input),
        check_authoring_provenance_closure(archmap, input),
        check_authoring_ledger_spans_worklist(input),
        check_authoring_read_before_cite(archmap, input),
    ] {
        if check.result == "fail" {
            examples.push(validation_example(
                &check.id,
                "fail",
                "authoring survey traceability requires this mechanical check to pass",
            ));
        }
    }
    check_from_examples(
        "authoring-survey-traceable-within-scope",
        "AUTHORING_SURVEY_TRACEABLE_WITHIN_SCOPE: ArchMap authoring survey is mechanically traceable within the recorded scope",
        examples,
    )
}

fn worklist_index(
    manifest: &ArchmapScopeManifestV1,
) -> BTreeMap<String, &ArchmapScopeManifestWorklistEntryV1> {
    manifest
        .worklist
        .iter()
        .map(|entry| (entry.source_id.clone(), entry))
        .collect()
}

fn source_resolves_to_worklist(
    source_id: &str,
    source: &ArchMapSource,
    worklist: &BTreeMap<String, &ArchmapScopeManifestWorklistEntryV1>,
) -> bool {
    if let Some(entry) = worklist.get(source_id) {
        return source.path.as_deref().is_none_or(|path| path == entry.path);
    }
    if let Some(path) = source.path.as_deref() {
        if worklist.values().any(|entry| entry.path == path) {
            return true;
        }
        if let Some(doc_path) = source_id.strip_prefix("doc:") {
            let doc_path = doc_path.split_once('#').map_or(doc_path, |(path, _)| path);
            return doc_path == path && worklist.values().any(|entry| entry.path == doc_path);
        }
    }
    worklist
        .values()
        .any(|entry| entry.author_added && entry.source_id == source_id)
}

fn source_is_grounding_exempt(source_id: &str, source: &ArchMapSource) -> bool {
    let kind = source.kind.to_ascii_lowercase();
    source_id.starts_with("ctx:")
        || matches!(
            kind.as_str(),
            "grounding"
                | "context"
                | "policy"
                | "profile"
                | "measurement"
                | "law-policy"
                | "measurement-profile"
                | "reader-profile"
        )
}

fn ledger_adopted_atoms(ledger: &ArchmapCoverageLedgerV1) -> BTreeSet<String> {
    ledger
        .rows
        .iter()
        .flat_map(|row| row.adopted_atom_ids.iter().cloned())
        .collect()
}

fn survey_row_provenance_atoms(packets: &[ArchmapCandidatePacketV1]) -> BTreeSet<String> {
    let candidate_atom_ids = packets
        .iter()
        .flat_map(|packet| packet.candidate_atoms.iter())
        .map(|atom| atom.id.clone())
        .collect::<BTreeSet<_>>();
    packets
        .iter()
        .flat_map(|packet| packet.survey_rows.iter())
        .flat_map(|row| row.candidate_atom_ids.iter().cloned())
        .filter(|atom_id| candidate_atom_ids.contains(atom_id))
        .collect()
}

fn adopted_adjudication_keys(consistency: &[ArchmapExtractionConsistencyV1]) -> BTreeSet<String> {
    consistency
        .iter()
        .flat_map(|report| report.adjudications.iter())
        .filter(|adjudication| matches!(adjudication.decision.as_str(), "adopted" | "merged"))
        .map(|adjudication| adjudication.key.clone())
        .collect()
}

fn citation_was_surveyed(source_ref: &str, input: &AuthoringAuditInputV1) -> bool {
    input
        .candidate_packets
        .iter()
        .flat_map(|packet| packet.survey_rows.iter())
        .any(|row| {
            row.source_id == source_ref
                && (row.status == "read" || (row.status == "partial" && source_ref.contains('#')))
        })
}

fn source_id_counts<'a>(ids: impl Iterator<Item = &'a str>) -> BTreeMap<&'a str, usize> {
    let mut counts = BTreeMap::new();
    for id in ids {
        *counts.entry(id).or_default() += 1;
    }
    counts
}

fn artifact_ref_examples(
    archmap: &ArchMapDocumentV2,
    input: &AuthoringAuditInputV1,
) -> Vec<ValidationExample> {
    let mut examples = Vec::new();
    examples.extend(worklist_chunk_read_examples(input));
    for packet in &input.candidate_packets {
        if packet.scope_manifest_ref != input.scope_manifest.id {
            examples.push(validation_example(
                &packet.id,
                &packet.scope_manifest_ref,
                "candidate packet scopeManifestRef must match the supplied scope manifest id",
            ));
        }
    }
    if input.coverage_ledger.scope_manifest_ref != input.scope_manifest.id {
        examples.push(validation_example(
            "coverageLedger.scopeManifestRef",
            &input.coverage_ledger.scope_manifest_ref,
            "coverage ledger scopeManifestRef must match the supplied scope manifest id",
        ));
    }
    if input.coverage_ledger.archmap_ref != archmap.id {
        examples.push(validation_example(
            "coverageLedger.archmapRef",
            &input.coverage_ledger.archmap_ref,
            "coverage ledger archmapRef must match the supplied ArchMap id",
        ));
    }
    let packet_ids = input
        .candidate_packets
        .iter()
        .map(|packet| packet.id.as_str())
        .collect::<BTreeSet<_>>();
    for pass_ref in &input.coverage_ledger.pass_refs {
        if !packet_ids.contains(pass_ref.as_str()) {
            examples.push(validation_example(
                "coverageLedger.passRefs",
                pass_ref,
                "coverage ledger passRefs must resolve to supplied candidate packet ids",
            ));
        }
    }
    for report in &input.extraction_consistency {
        if report.scope_manifest_ref != input.scope_manifest.id {
            examples.push(validation_example(
                &report.id,
                &report.scope_manifest_ref,
                "extraction consistency scopeManifestRef must match the supplied scope manifest id",
            ));
        }
        for pass_ref in report.pass_a_refs.iter().chain(report.pass_b_refs.iter()) {
            if !packet_ids.contains(pass_ref.as_str()) {
                examples.push(validation_example(
                    &report.id,
                    pass_ref,
                    "extraction consistency pass refs must resolve to supplied candidate packet ids",
                ));
            }
        }
    }
    examples
}

fn worklist_chunk_read_examples(input: &AuthoringAuditInputV1) -> Vec<ValidationExample> {
    let surveyed = input
        .candidate_packets
        .iter()
        .flat_map(|packet| packet.survey_rows.iter().map(|row| row.source_id.as_str()))
        .collect::<Vec<_>>();
    let reviewed = input
        .candidate_packets
        .iter()
        .flat_map(|packet| packet.reviewed_sources.iter().map(String::as_str))
        .collect::<Vec<_>>();
    let mut examples = Vec::new();
    for entry in &input.scope_manifest.worklist {
        if !surveyed
            .iter()
            .any(|source_id| source_id_resolves_to_worklist_entry(source_id, entry))
        {
            examples.push(validation_example(
                "candidatePackets[].surveyRows[].sourceId",
                &entry.source_id,
                "candidate survey rows must cover every scope worklist row",
            ));
        }
        if !reviewed
            .iter()
            .any(|source_id| source_id_resolves_to_worklist_entry(source_id, entry))
        {
            examples.push(validation_example(
                "candidatePackets[].reviewedSources[]",
                &entry.source_id,
                "candidate reviewedSources must cover every scope worklist row",
            ));
        }
    }
    examples
}

fn source_id_resolves_to_worklist_entry(
    source_id: &str,
    entry: &ArchmapScopeManifestWorklistEntryV1,
) -> bool {
    if source_id == entry.source_id {
        return true;
    }
    source_id
        .strip_prefix("doc:")
        .map(|doc_ref| doc_ref.split_once('#').map_or(doc_ref, |(path, _)| path) == entry.path)
        .unwrap_or(false)
}

struct CitationRef {
    owner_kind: &'static str,
    owner: String,
    source_ref: String,
}

fn cited_refs(archmap: &ArchMapDocumentV2) -> Vec<CitationRef> {
    let mut refs = Vec::new();
    for atom in &archmap.atoms {
        refs.extend(atom.refs.iter().map(|source_ref| CitationRef {
            owner_kind: "atom",
            owner: atom.id.clone(),
            source_ref: source_ref.clone(),
        }));
    }
    for context in &archmap.contexts {
        refs.extend(context.refs.iter().map(|source_ref| CitationRef {
            owner_kind: "context",
            owner: context.id.clone(),
            source_ref: source_ref.clone(),
        }));
    }
    for cover in &archmap.covers {
        refs.extend(cover.refs.iter().map(|source_ref| CitationRef {
            owner_kind: "cover",
            owner: cover.id.clone(),
            source_ref: source_ref.clone(),
        }));
    }
    refs
}

fn check_from_examples(id: &str, title: &str, examples: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = ValidationCheck {
        id: id.to_string(),
        title: title.to_string(),
        result: if examples.is_empty() { "pass" } else { "fail" }.to_string(),
        reason: None,
        count: None,
        examples,
        metric: None,
        lean_boundary: None,
    };
    if !check.examples.is_empty() {
        check.count = Some(check.examples.len());
    }
    check
}

fn validation_example(source: &str, target: &str, evidence: &str) -> ValidationExample {
    ValidationExample {
        component_id: None,
        path: None,
        source: Some(source.to_string()),
        target: Some(target.to_string()),
        evidence: Some(evidence.to_string()),
    }
}

fn validate_semantic_atom_object(index: usize, atom: &ArchMapAtomV2, errors: &mut Vec<String>) {
    if atom.kind == "semantic" && atom.object.as_deref().unwrap_or_default().trim().is_empty() {
        errors.push(format!(
            "candidateAtoms[{}] semantic atoms must include a non-empty object",
            index
        ));
    }
}

fn validate_no_diagnostic_shortcut(index: usize, atom: &ArchMapAtomV2, errors: &mut Vec<String>) {
    if let Some(token) = diagnostic_shortcut_token(&atom.id) {
        errors.push(format!(
            "candidateAtoms[{index}].id must not pre-author diagnostic conclusion token {token}"
        ));
    }
    if let Some(predicate) = atom.predicate.as_deref() {
        if let Some(token) = diagnostic_shortcut_token(predicate) {
            errors.push(format!(
                "candidateAtoms[{index}].predicate must not pre-author diagnostic conclusion token {token}"
            ));
        }
    }
}

fn diagnostic_shortcut_token(value: &str) -> Option<&'static str> {
    let parts = diagnostic_shortcut_parts(value);
    parts
        .iter()
        .find_map(|part| match part.as_str() {
            "mismatch" => Some("mismatch"),
            "obstruction" | "obstructive" => Some("obstruction"),
            "violation" | "violate" | "violated" | "violates" | "violating" => Some("violation"),
            "risk" | "risky" => Some("risk"),
            "debt" => Some("debt"),
            "unsafe" => Some("unsafe"),
            "lawful" => Some("lawful"),
            "nonzero" => Some("nonzero"),
            "failure" | "fail" | "failed" | "failing" => Some("failure"),
            _ => None,
        })
        .or_else(|| {
            parts
                .windows(2)
                .any(|window| window[0] == "non" && window[1] == "zero")
                .then_some("nonzero")
        })
}

fn diagnostic_shortcut_parts(value: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut previous_was_lower_or_digit = false;
    for character in value.chars() {
        if character.is_ascii_alphanumeric() {
            if character.is_ascii_uppercase() && previous_was_lower_or_digit && !current.is_empty()
            {
                parts.push(std::mem::take(&mut current));
            }
            current.push(character.to_ascii_lowercase());
            previous_was_lower_or_digit =
                character.is_ascii_lowercase() || character.is_ascii_digit();
        } else {
            if !current.is_empty() {
                parts.push(std::mem::take(&mut current));
            }
            previous_was_lower_or_digit = false;
        }
    }
    if !current.is_empty() {
        parts.push(current);
    }
    parts
}

fn validate_candidate_reason(field: &str, reason: &str, errors: &mut Vec<String>) {
    if !matches!(
        reason,
        "private" | "binary" | "unreadable" | "tooling-error"
    ) {
        errors.push(format!(
            "{field} must be private, binary, unreadable, or tooling-error"
        ));
    }
}

fn validate_self_review_gate(
    self_review: &crate::ArchmapCandidatePacketSelfReviewV1,
    errors: &mut Vec<String>,
) {
    for (field, passed) in [
        ("notScriptGenerated", self_review.not_script_generated),
        (
            "notCoarseWhenEvidenceWasRicher",
            self_review.not_coarse_when_evidence_was_richer,
        ),
        (
            "semanticAtomsHaveUseEvidence",
            self_review.semantic_atoms_have_use_evidence,
        ),
        (
            "noDiagnosticShortcutAtoms",
            self_review.no_diagnostic_shortcut_atoms,
        ),
        (
            "worklistChunkFullyRead",
            self_review.worklist_chunk_fully_read,
        ),
        (
            "aliasPreservingSemantics",
            self_review.alias_preserving_semantics,
        ),
    ] {
        if !passed {
            errors.push(format!("selfReview.{field} must be true"));
        }
    }
}

fn validate_repo_relative_glob(pattern: &str) -> Result<(), String> {
    reject_repo_relative_glob(pattern).map_err(|error| error.to_string())
}

fn validate_public_text(field: &str, value: &str, errors: &mut Vec<String>) {
    if contains_local_marker(value) {
        errors.push(format!(
            "{field} must not contain local or private workspace markers"
        ));
    }
}

fn contains_local_marker(value: &str) -> bool {
    let normalized = value.replace('\\', "/");
    [
        format!("{}/", ["", "Users"].join("/")),
        format!("{}/", ["", "private"].join("/")),
        [".", "codex"].join(""),
        ["Hello", "Lean"].join(""),
    ]
    .iter()
    .any(|marker| normalized.contains(marker.as_str()))
}

fn validation_result(errors: Vec<String>) -> Result<(), Vec<String>> {
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn source_kind(path: &str) -> String {
    match Path::new(path)
        .extension()
        .and_then(|extension| extension.to_str())
    {
        Some("md") | Some("markdown") => "doc",
        Some("rs") => "rust",
        Some("json") => "json",
        Some("toml") => "toml",
        _ => "file",
    }
    .to_string()
}

fn repo_relative_path(root: &Path, path: &Path) -> Result<String, Box<dyn Error>> {
    let relative = path.strip_prefix(root)?;
    Ok(normalize_slashes(
        relative
            .to_str()
            .ok_or("scope-manifest requires UTF-8 paths")?,
    ))
}

fn normalize_slashes(path: &str) -> String {
    path.replace('\\', "/")
}

fn git_revision(root: &Path) -> Option<String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .arg("rev-parse")
        .arg("HEAD")
        .output()
        .ok()?;
    output
        .status
        .success()
        .then(|| format!("git:{}", String::from_utf8_lossy(&output.stdout).trim()))
}

fn git_dirty(root: &Path) -> Option<bool> {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .arg("status")
        .arg("--porcelain")
        .output()
        .ok()?;
    output.status.success().then(|| !output.stdout.is_empty())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::{
        ArchmapCandidatePacketSelfReviewV1, ArchmapCandidatePacketSurveyRowV1,
        ArchmapCoverageLedgerRowV1, ArchmapExtractionContextDiffV1, ArchmapExtractionMatchCountV1,
    };

    fn passing_self_review() -> ArchmapCandidatePacketSelfReviewV1 {
        ArchmapCandidatePacketSelfReviewV1 {
            not_script_generated: true,
            not_coarse_when_evidence_was_richer: true,
            semantic_atoms_have_use_evidence: true,
            no_diagnostic_shortcut_atoms: true,
            worklist_chunk_fully_read: true,
            alias_preserving_semantics: true,
        }
    }

    #[test]
    fn validates_scope_manifest_order_paths_hashes_and_exclusion_reasons() {
        let manifest = ArchmapScopeManifestV1 {
            schema: ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA.to_string(),
            id: "scope:test".to_string(),
            repository: ArchmapScopeManifestRepositoryV1 {
                root: ".".to_string(),
                revision: None,
                dirty: None,
            },
            scope_spec: ArchmapScopeManifestScopeSpecV1 {
                include_globs: vec!["src/**/*.rs".to_string()],
                exclude_globs: vec![],
                added_evidence: vec![],
                requested_scope: None,
                approved_by: None,
            },
            baseline_ref: None,
            worklist: vec![ArchmapScopeManifestWorklistEntryV1 {
                order: 2,
                source_id: "src:a".to_string(),
                path: "../a.rs".to_string(),
                kind: "rust".to_string(),
                content_hash: "md5:abc".to_string(),
                size_bytes: 1,
                author_added: false,
            }],
            exclusions: vec![ArchmapScopeManifestExclusionV1 {
                path: "src/generated/**".to_string(),
                reason: "skipped".to_string(),
            }],
        };

        let errors = validate_scope_manifest_v1(&manifest).expect_err("manifest is invalid");
        assert!(errors.iter().any(|error| error.contains("order")));
        assert!(errors.iter().any(|error| error.contains("escape")));
        assert!(errors.iter().any(|error| error.contains("sha256")));
        assert!(errors.iter().any(|error| error.contains("user-excluded")));
    }

    #[test]
    fn validates_candidate_packet_controlled_status_and_semantic_object() {
        let packet = ArchmapCandidatePacketV1 {
            schema: ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA.to_string(),
            id: "packet:test".to_string(),
            scope_manifest_ref: "scope:test".to_string(),
            pass_id: "pass:a".to_string(),
            chunk: BTreeMap::new(),
            reviewed_sources: vec![],
            candidate_sources: BTreeMap::new(),
            candidate_atoms: vec![ArchMapAtomV2 {
                id: "atom:semantic".to_string(),
                kind: "semantic".to_string(),
                subject: "subject".to_string(),
                axis: "semantic".to_string(),
                predicate: Some("uses".to_string()),
                object: None,
                refs: vec![],
                label: None,
            }],
            candidate_contexts: vec![],
            candidate_covers: vec![],
            survey_rows: vec![ArchmapCandidatePacketSurveyRowV1 {
                source_id: "src:a".to_string(),
                status: "done".to_string(),
                reason: Some("out-of-scope".to_string()),
                surveyed_kinds: vec![],
                candidate_atom_ids: vec![],
                notes: vec![format!(
                    "see {}/example/private.txt",
                    ["", "Users"].join("/")
                )],
            }],
            private_unavailable_notes: vec![format!(
                "local path {}/tmp/a",
                ["", "private"].join("/")
            )],
            self_review: passing_self_review(),
        };

        let errors = validate_candidate_packet_v1(&packet).expect_err("packet is invalid");
        assert!(errors.iter().any(|error| error.contains("status")));
        assert!(errors.iter().any(|error| error.contains("reason")));
        assert!(
            errors
                .iter()
                .any(|error| error.contains("workspace markers"))
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("non-empty object"))
        );
    }

    #[test]
    fn validates_candidate_packet_self_review_gate() {
        let packet = ArchmapCandidatePacketV1 {
            schema: ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA.to_string(),
            id: "packet:test".to_string(),
            scope_manifest_ref: "scope:test".to_string(),
            pass_id: "pass:a".to_string(),
            chunk: BTreeMap::new(),
            reviewed_sources: vec![],
            candidate_sources: BTreeMap::new(),
            candidate_atoms: vec![],
            candidate_contexts: vec![],
            candidate_covers: vec![],
            survey_rows: vec![ArchmapCandidatePacketSurveyRowV1 {
                source_id: "src:a".to_string(),
                status: "skipped".to_string(),
                reason: Some("private".to_string()),
                surveyed_kinds: vec![],
                candidate_atom_ids: vec![],
                notes: vec![],
            }],
            private_unavailable_notes: vec![],
            self_review: ArchmapCandidatePacketSelfReviewV1 {
                no_diagnostic_shortcut_atoms: false,
                ..passing_self_review()
            },
        };

        let errors = validate_candidate_packet_v1(&packet).expect_err("packet is invalid");
        assert!(
            errors
                .iter()
                .any(|error| error.contains("selfReview.noDiagnosticShortcutAtoms"))
        );
    }

    #[test]
    fn validates_extraction_consistency_match_rate_and_decision_tokens() {
        let report = ArchmapExtractionConsistencyV1 {
            schema: ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA.to_string(),
            id: "consistency:test".to_string(),
            scope_manifest_ref: "scope:test".to_string(),
            pass_a_refs: vec!["packet:a".to_string()],
            pass_b_refs: vec!["packet:b".to_string()],
            atom_match_key_spec: "kind+subject+axis+predicate+object".to_string(),
            matched: ArchmapExtractionMatchCountV1 {
                count: 1,
                rows: vec![],
            },
            only_in_pass_a: vec![],
            only_in_pass_b: vec![],
            match_rate: 0.5,
            context_diff: ArchmapExtractionContextDiffV1 {
                matched: 0,
                only_in_pass_a: vec![],
                only_in_pass_b: vec![],
            },
            adjudications: vec![crate::ArchmapExtractionAdjudicationV1 {
                key: "k".to_string(),
                decision: "yes".to_string(),
                basis: "basis".to_string(),
            }],
        };

        let errors =
            validate_extraction_consistency_v1(&report).expect_err("consistency is invalid");
        assert!(errors.iter().any(|error| error.contains("matchRate")));
        assert!(errors.iter().any(|error| error.contains("decision")));
    }

    #[test]
    fn validates_coverage_ledger_boundary_and_unavailable_reasons() {
        let ledger = ArchmapCoverageLedgerV1 {
            schema: ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA.to_string(),
            id: "coverage:test".to_string(),
            scope_manifest_ref: "scope:test".to_string(),
            archmap_ref: "archmap:test".to_string(),
            pass_refs: vec![],
            rows: vec![ArchmapCoverageLedgerRowV1 {
                source_id: "src:a".to_string(),
                survey_status: "not_surveyed".to_string(),
                passes: vec![],
                surveyed_kinds: vec![],
                adopted_atom_ids: vec![],
                reason: Some("out-of-scope".to_string()),
            }],
            claim_boundary: "wrong".to_string(),
        };

        let errors = validate_coverage_ledger_v1(&ledger).expect_err("ledger is invalid");
        assert!(errors.iter().any(|error| error.contains("claimBoundary")));
        assert!(errors.iter().any(|error| error.contains("reason")));
    }
}
