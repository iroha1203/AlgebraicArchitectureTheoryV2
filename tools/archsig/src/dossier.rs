//! Diagnosis dossier: a mechanical, digest-verified bundle of existing run
//! outputs (analyze x N, compare, gate) into one JSON artifact.
//!
//! The dossier performs no measurement. Every embedded document is read from an
//! existing run directory or report file and admitted only after its digests
//! and runIds are found mutually consistent (fail-closed otherwise). Each frame
//! carries a supplier-declared state provenance so consumers can always
//! distinguish hypothetical states from observed or actually-changed ones. The
//! ordered frame list doubles as the temporal sequence supply.

use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::error::Error;
use std::path::{Path, PathBuf};

pub const ARCHSIG_DIAGNOSIS_DOSSIER_SCHEMA_VERSION: &str = "archsig-diagnosis-dossier/v0.5.4";

pub const DOSSIER_STATE_PROVENANCE_KINDS: [&str; 5] = [
    "observed-source",
    "authored-model",
    "measured-conclusion",
    "hypothetical-state",
    "actual-change",
];

#[derive(Debug, Clone)]
pub struct DossierFrameSpec {
    pub frame_id: String,
    pub state_provenance: String,
    pub run_dir: PathBuf,
}

/// Parse a CLI frame spec of the form `<frameId>=<stateProvenance>=<run-dir>`.
pub fn parse_dossier_frame_spec(raw: &str) -> Result<DossierFrameSpec, Box<dyn Error>> {
    let parts = raw.splitn(3, '=').collect::<Vec<_>>();
    if parts.len() != 3 || parts.iter().any(|part| part.is_empty()) {
        return Err(format!(
            "--frame must have the form <frameId>=<stateProvenance>=<run-dir>, got {raw}"
        )
        .into());
    }
    Ok(DossierFrameSpec {
        frame_id: parts[0].to_string(),
        state_provenance: parts[1].to_string(),
        run_dir: PathBuf::from(parts[2]),
    })
}

fn read_json_file(path: &Path) -> Result<Value, Box<dyn Error>> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    serde_json::from_str(&text)
        .map_err(|error| format!("cannot parse {}: {error}", path.display()).into())
}

fn canonical_json_file_digest(path: &Path) -> Result<String, Box<dyn Error>> {
    let value = read_json_file(path)?;
    let canonical = serde_json::to_vec(&value)?;
    let mut hasher = Sha256::new();
    hasher.update(&canonical);
    Ok(format!("{:x}", hasher.finalize()))
}

struct LoadedFrame {
    frame_id: String,
    state_provenance: String,
    run_id: String,
    packet_digest: String,
    view_model: Value,
    summary_conclusion: Value,
    run_manifest: Value,
}

fn load_frame(spec: &DossierFrameSpec) -> Result<LoadedFrame, Box<dyn Error>> {
    if !DOSSIER_STATE_PROVENANCE_KINDS.contains(&spec.state_provenance.as_str()) {
        return Err(format!(
            "frame {} has unknown state provenance {}; expected one of {}",
            spec.frame_id,
            spec.state_provenance,
            DOSSIER_STATE_PROVENANCE_KINDS.join(" / ")
        )
        .into());
    }
    let manifest = read_json_file(&spec.run_dir.join("archsig-run-manifest.json"))?;
    let packet_path = spec.run_dir.join("archsig-measurement-packet.json");
    let packet = read_json_file(&packet_path)?;
    let view_model_path = spec.run_dir.join("archsig-measurement-view-model.json");
    let view_model = read_json_file(&view_model_path)?;
    let summary = read_json_file(&spec.run_dir.join("archsig-analysis-summary.json"))?;

    let manifest_run_id = manifest["runId"]
        .as_str()
        .ok_or_else(|| format!("frame {}: run manifest has no runId", spec.frame_id))?;
    let packet_run_id = packet["runId"].as_str().unwrap_or_default();
    let view_model_run_id = view_model["runId"].as_str().unwrap_or_default();
    if manifest_run_id != packet_run_id || manifest_run_id != view_model_run_id {
        return Err(format!(
            "frame {}: runId mismatch across run artifacts (manifest {manifest_run_id}, packet {packet_run_id}, view model {view_model_run_id})",
            spec.frame_id
        )
        .into());
    }
    let packet_digest = canonical_json_file_digest(&packet_path)?;
    let recorded_digest = view_model["inputDigests"]["measurementPacket"]["sha256"]
        .as_str()
        .unwrap_or_default();
    if recorded_digest != packet_digest {
        return Err(format!(
            "frame {}: measurement packet digest mismatch (view model records {recorded_digest}, file digest is {packet_digest})",
            spec.frame_id
        )
        .into());
    }
    Ok(LoadedFrame {
        frame_id: spec.frame_id.clone(),
        state_provenance: spec.state_provenance.clone(),
        run_id: manifest_run_id.to_string(),
        packet_digest,
        view_model,
        summary_conclusion: summary["conclusion"].clone(),
        run_manifest: manifest,
    })
}

fn frame_id_for_packet_digest<'a>(
    frames: &'a [LoadedFrame],
    digest: &str,
) -> Option<&'a LoadedFrame> {
    frames.iter().find(|frame| frame.packet_digest == digest)
}

pub fn build_diagnosis_dossier_v1(
    frame_specs: &[DossierFrameSpec],
    comparison_paths: &[PathBuf],
    gate_paths: &[PathBuf],
) -> Result<Value, Box<dyn Error>> {
    if frame_specs.is_empty() {
        return Err("dossier requires at least one --frame".into());
    }
    let mut seen_ids = BTreeSet::new();
    for spec in frame_specs {
        if !seen_ids.insert(spec.frame_id.clone()) {
            return Err(format!("duplicate frame id {}", spec.frame_id).into());
        }
    }
    let frames = frame_specs
        .iter()
        .map(load_frame)
        .collect::<Result<Vec<_>, _>>()?;

    let mut comparisons = Vec::new();
    for path in comparison_paths {
        let report = read_json_file(path)?;
        let base_digest = report["inputDigests"]["baseRun"]["measurementPacket"]["sha256"]
            .as_str()
            .unwrap_or_default();
        let head_digest = report["inputDigests"]["headRun"]["measurementPacket"]["sha256"]
            .as_str()
            .unwrap_or_default();
        let base_frame = frame_id_for_packet_digest(&frames, base_digest).ok_or_else(|| {
            format!(
                "comparison {} baseRun packet digest does not match any supplied frame",
                path.display()
            )
        })?;
        let head_frame = frame_id_for_packet_digest(&frames, head_digest).ok_or_else(|| {
            format!(
                "comparison {} headRun packet digest does not match any supplied frame",
                path.display()
            )
        })?;
        comparisons.push(json!({
            "baseFrameId": base_frame.frame_id,
            "headFrameId": head_frame.frame_id,
            "conclusionCode": report["conclusionCode"],
            "report": report,
        }));
    }

    let mut gate_reports = Vec::new();
    for path in gate_paths {
        let report = read_json_file(path)?;
        let packet_digest = report["inputDigests"]["measurementPacket"]["sha256"]
            .as_str()
            .unwrap_or_default();
        let frame = frame_id_for_packet_digest(&frames, packet_digest).ok_or_else(|| {
            format!(
                "gate report {} packet digest does not match any supplied frame",
                path.display()
            )
        })?;
        gate_reports.push(json!({
            "frameId": frame.frame_id,
            "decision": report["decision"],
            "report": report,
        }));
    }

    let frame_rows = frames
        .iter()
        .enumerate()
        .map(|(order, frame)| {
            json!({
                "frameId": frame.frame_id,
                "order": order,
                "stateProvenance": frame.state_provenance,
                "runId": frame.run_id,
                "conclusion": frame.summary_conclusion,
                "measurementPacketDigest": { "sha256": frame.packet_digest },
                "viewModel": frame.view_model,
                "runManifest": frame.run_manifest,
            })
        })
        .collect::<Vec<_>>();
    let sequence = frames
        .iter()
        .map(|frame| frame.frame_id.clone())
        .collect::<Vec<_>>();

    Ok(json!({
        "schema": ARCHSIG_DIAGNOSIS_DOSSIER_SCHEMA_VERSION,
        "frames": frame_rows,
        "comparisons": comparisons,
        "gateReports": gate_reports,
        "sequence": sequence,
        "nonClaims": [
            "The dossier bundles existing run outputs after digest and runId consistency checks; it performs no measurement and renders no new verdict.",
            "Frame order is the supplier-declared sequence; it does not assert causality between frames.",
            "State provenance is supplier-declared; a hypothetical-state frame does not assert that any repository change was implemented or applied.",
            "Comparison and gate rows only restate the referenced reports; admission required their digests to match a supplied frame.",
        ],
    }))
}
