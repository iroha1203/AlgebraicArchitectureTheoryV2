use std::collections::BTreeSet;
use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use archsig::{
    ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION, ArchMapDocumentV0, ArchMapSourceInventoryInput,
    ArchMapSourceInventoryV0, ArchMapValidationReportV0, LawPolicyDocumentV0,
    SchemaVersionCatalogV0, build_archsig_analysis_packet, static_law_policy,
    static_schema_version_catalog, validate_archmap_report,
    validate_archsig_analysis_packet_report, validate_law_policy_report,
};
use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
#[command(
    version,
    about = "Validate ArchMap, LawPolicy, and ArchSig analysis artifacts"
)]
struct Args {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Validate a supplied ArchMap observation JSON artifact.
    Archmap {
        /// Input ArchMap JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Output ArchMap validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate or emit an interpretation profile artifact for ArchSig AAT analysis.
    #[command(visible_alias = "interpretation-profile")]
    LawPolicy {
        /// Optional LawPolicy JSON path. If omitted, the static fixture policy is validated.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical law-policy-v0 fixture instead of a validation report.
        #[arg(long)]
        fixture: bool,

        /// Output LawPolicy fixture or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Run the primary ArchMap + LawPolicy -> ArchSig analysis workflow.
    #[command(visible_aliases = ["llm-native-workflow", "north-star-workflow"])]
    Analyze {
        /// Input ArchMap observation artifact path.
        #[arg(long)]
        archmap: PathBuf,

        /// Input LawPolicy artifact path.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Output directory for ArchSig analysis workflow artifacts.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,
    },

    /// Build an ArchSig AAT analysis packet from ArchMap + interpretation profile.
    #[command(visible_alias = "aat-analysis")]
    ArchsigAnalysis {
        /// Input ArchMap observation artifact path.
        #[arg(long)]
        archmap: PathBuf,

        /// Input LawPolicy artifact path.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Output archsig-analysis-packet-v0 JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,

        /// Optional output validation report path.
        #[arg(long = "validation-out")]
        validation_out: Option<PathBuf>,

        /// Optional LLM interpretation packet output path. This writes the same structured packet for LLM reading.
        #[arg(long = "llm-interpretation-out")]
        llm_interpretation_out: Option<PathBuf>,
    },

    /// Summarize an archsig-analysis-packet-v0 for human and LLM review.
    #[command(visible_alias = "summary")]
    AnalysisSummary {
        /// Input archsig-analysis-packet-v0 JSON path.
        #[arg(long)]
        packet: PathBuf,

        /// Optional ArchMap validation report path.
        #[arg(long = "archmap-validation")]
        archmap_validation: Option<PathBuf>,

        /// Optional LawPolicy validation report path.
        #[arg(long = "law-policy-validation")]
        law_policy_validation: Option<PathBuf>,

        /// Optional ArchSig analysis validation report path.
        #[arg(long = "analysis-validation")]
        analysis_validation: Option<PathBuf>,

        /// Output summary JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Produce a current-state architecture inspection report from ArchMapStore artifacts.
    CodebaseInspection {
        /// Input archmap-snapshot-v0 JSON path. This is the materialized current-state base.
        #[arg(long)]
        snapshot: PathBuf,

        /// Input archmap-index-v0 JSON path. This is the large-repository lookup surface.
        #[arg(long)]
        index: PathBuf,

        /// Input archsig-analysis-packet-v0 JSON path for current-state structural readings.
        #[arg(long)]
        packet: PathBuf,

        /// Optional law-policy-v0 JSON path retained as selected interpretation provenance.
        #[arg(long = "law-policy")]
        law_policy: Option<PathBuf>,

        /// Optional recent archmap-delta-v0 JSON path. May be supplied multiple times.
        #[arg(long = "recent-delta")]
        recent_delta: Vec<PathBuf>,

        /// Maximum number of ranked readings to include.
        #[arg(long, default_value_t = 6)]
        limit: usize,

        /// Output archsig-codebase-inspection-report-v0 JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Produce a lightweight ArchSig PR review report from base ArchMap, PR-local ArchMap delta, and LawPolicy.
    PrReview {
        /// Input base archmap-observation-map-v0 JSON path.
        #[arg(long = "base-archmap")]
        base_archmap: PathBuf,

        /// Input archmap-delta-v0 JSON path. This is the PR-local ArchMap observation delta.
        #[arg(long = "delta-archmap")]
        delta_archmap: PathBuf,

        /// Input law-policy-v0 JSON path. No LawPolicy, no ArchSig judgement.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Output archsig-pr-review-report-v1 JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit a bounded external-agent protocol for generating ArchMap JSON.
    ArchmapGenerate {
        /// Source inventory JSON path used by the external agent.
        #[arg(long = "source-inventory")]
        source_inventory: PathBuf,

        /// Prompt pack path retained as provenance.
        #[arg(long = "prompt-pack")]
        prompt_pack: PathBuf,

        /// Model provider name retained as provenance.
        #[arg(long, default_value = "external-agent")]
        provider: String,

        /// Model id retained as provenance.
        #[arg(long = "model-id", default_value = "unspecified")]
        model_id: String,

        /// Output generation protocol JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit the current LLM Atom ArchMap schema catalog.
    SchemaCatalog {
        /// Output schema version catalog JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<ExitCode, Box<dyn Error>> {
    let args = Args::parse();

    match args.command {
        Some(Command::Archmap { input, out }) => {
            let document: ArchMapDocumentV0 = read_json(&input)?;
            let source_inventory_path = document
                .source_inventory_ref
                .as_ref()
                .and_then(|source_inventory_ref| source_inventory_ref.path.as_deref());
            let mut source_inventory_document: Option<ArchMapSourceInventoryV0> = None;
            let mut source_inventory_error: Option<String> = None;
            if let Some(path) = source_inventory_path {
                match resolve_archmap_sidecar_path(&input, path) {
                    Some(resolved_path) => match read_json(&resolved_path) {
                        Ok(source_inventory) => source_inventory_document = Some(source_inventory),
                        Err(error) => {
                            source_inventory_error = Some(format!(
                                "source inventory artifact could not be read: {error}"
                            ));
                        }
                    },
                    None => {
                        source_inventory_error =
                            Some("source inventory artifact path does not exist".to_string());
                    }
                }
            }
            let source_inventory = source_inventory_path.map(|path| ArchMapSourceInventoryInput {
                path,
                document: source_inventory_document.as_ref(),
                read_error: source_inventory_error.clone(),
            });
            let report: ArchMapValidationReportV0 = validate_archmap_report(
                &document,
                &input.display().to_string(),
                source_inventory,
            );
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::LawPolicy {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let policy = static_law_policy();
                write_json(out, &policy)?;
                return Ok(ExitCode::SUCCESS);
            }
            let policy: LawPolicyDocumentV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_law_policy);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-law-policy".to_string());
            let report = validate_law_policy_report(&policy, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ArchsigAnalysis {
            archmap,
            law_policy,
            out,
            validation_out,
            llm_interpretation_out,
        }) => {
            let archmap_document: ArchMapDocumentV0 = read_json(&archmap)?;
            let law_policy_document: LawPolicyDocumentV0 = read_json(&law_policy)?;
            let packet = build_archsig_analysis_packet(
                &archmap_document,
                &law_policy_document,
                Some(&archmap.display().to_string()),
                Some(&law_policy.display().to_string()),
            );
            let validation =
                validate_archsig_analysis_packet_report(&packet, "archsig-analysis-packet");
            let failed = validation.summary.result == "fail";
            if let Some(path) = validation_out {
                write_json(Some(path), &validation)?;
            }
            if let Some(path) = llm_interpretation_out {
                write_json(Some(path), &packet)?;
            }
            write_json(out, &packet)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::AnalysisSummary {
            packet,
            archmap_validation,
            law_policy_validation,
            analysis_validation,
            out,
        }) => {
            let packet_document: serde_json::Value = read_json(&packet)?;
            if !packet_document.is_object() {
                return Err("--packet must be a JSON object".into());
            }
            if packet_document.get("schemaVersion").and_then(|value| value.as_str())
                != Some(ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION)
            {
                return Err(format!(
                    "--packet must have schemaVersion {ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION}"
                )
                .into());
            }
            let archmap_validation = read_optional_json(archmap_validation.as_ref())?;
            let law_policy_validation = read_optional_json(law_policy_validation.as_ref())?;
            let analysis_validation = read_optional_json(analysis_validation.as_ref())?;
            let summary = build_analysis_summary(
                &packet_document,
                archmap_validation.as_ref(),
                law_policy_validation.as_ref(),
                analysis_validation.as_ref(),
            );
            write_json(out, &summary)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::CodebaseInspection {
            snapshot,
            index,
            packet,
            law_policy,
            recent_delta,
            limit,
            out,
        }) => {
            let snapshot_document: serde_json::Value = read_json(&snapshot)?;
            require_schema(&snapshot_document, "archmap-snapshot-v0", "--snapshot")?;
            let index_document: serde_json::Value = read_json(&index)?;
            require_schema(&index_document, "archmap-index-v0", "--index")?;
            let packet_document: serde_json::Value = read_json(&packet)?;
            require_schema(
                &packet_document,
                ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
                "--packet",
            )?;
            let law_policy_document = read_optional_json(law_policy.as_ref())?;
            if let Some(document) = law_policy_document.as_ref() {
                require_schema(document, "law-policy-v0", "--law-policy")?;
            }
            let mut recent_delta_documents = Vec::new();
            for delta_path in &recent_delta {
                let delta_document: serde_json::Value = read_json(delta_path)?;
                require_schema(&delta_document, "archmap-delta-v0", "--recent-delta")?;
                recent_delta_documents.push((delta_path.clone(), delta_document));
            }
            let report = build_codebase_inspection_report(
                &snapshot,
                &snapshot_document,
                &index,
                &index_document,
                &packet,
                &packet_document,
                law_policy.as_ref(),
                law_policy_document.as_ref(),
                &recent_delta_documents,
                limit,
            );
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::PrReview {
            base_archmap,
            delta_archmap,
            law_policy,
            out,
        }) => {
            let base_archmap_document: serde_json::Value = read_json(&base_archmap)?;
            require_schema(
                &base_archmap_document,
                "archmap-observation-map-v0",
                "--base-archmap",
            )?;
            let delta_archmap_document: serde_json::Value = read_json(&delta_archmap)?;
            require_schema(&delta_archmap_document, "archmap-delta-v0", "--delta-archmap")?;
            let law_policy_document: serde_json::Value = read_json(&law_policy)?;
            require_schema(&law_policy_document, "law-policy-v0", "--law-policy")?;
            let report = build_pr_review_report(
                &base_archmap,
                &base_archmap_document,
                &delta_archmap,
                &delta_archmap_document,
                &law_policy,
                &law_policy_document,
            );
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::ArchmapGenerate {
            source_inventory,
            prompt_pack,
            provider,
            model_id,
            out,
        }) => {
            let inventory: ArchMapSourceInventoryV0 = read_json(&source_inventory)?;
            let protocol = serde_json::json!({
                "schemaVersion": "archmap-generation-protocol-v0",
                "protocolId": format!("archmap-generation:{}", inventory.inventory_id),
                "sourceInventoryRef": {
                    "artifactId": inventory.inventory_id,
                    "kind": "source_inventory",
                    "path": source_inventory.display().to_string()
                },
                "promptPackRef": {
                    "artifactId": "archmap-prompt-pack",
                    "kind": "prompt",
                    "path": prompt_pack.display().to_string()
                },
                "modelProvenance": {
                    "provider": provider,
                    "modelId": model_id
                },
                "requiredWorkflow": [
                    "read source inventory includedRefs / excludedRefs / privateRefs / unavailableRefs separately",
                    "produce archmap-observation-map-v0 JSON with atomObservations, moleculeObservations, semanticObservations, observationGaps, projectionInfo, concernHints, provenance, and nonConclusions",
                    "run archsig archmap --input <archmap.json> before downstream projection",
                    "preserve invalid, dangling, unsupported, private, and unavailable evidence as boundary data"
                ],
                "generationBoundary": {
                    "selectionBoundary": inventory.selection_boundary,
                    "privateRefCount": inventory.private_refs.len(),
                    "unavailableRefCount": inventory.unavailable_refs.len(),
                    "nonConclusions": [
                        "external agent output is not semantic truth",
                        "generation protocol does not reconstruct private context",
                        "validation pass does not prove architecture lawfulness"
                    ]
                }
            });
            write_json(out, &protocol)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::Analyze {
            archmap,
            law_policy,
            out_dir,
        }) => {
            let archmap_validation_path = out_dir.join("archmap-validation.json");
            let law_policy_validation_path = out_dir.join("law-policy-validation.json");
            let analysis_packet_path = out_dir.join("archsig-analysis-packet.json");
            let analysis_validation_path = out_dir.join("archsig-analysis-validation.json");
            let llm_interpretation_path = out_dir.join("llm-interpretation-packet.json");

            let archmap_document: ArchMapDocumentV0 = read_json(&archmap)?;
            let source_inventory_path = archmap_document
                .source_inventory_ref
                .as_ref()
                .and_then(|source_inventory_ref| source_inventory_ref.path.as_deref());
            let mut source_inventory_document: Option<ArchMapSourceInventoryV0> = None;
            let mut source_inventory_error: Option<String> = None;
            if let Some(path) = source_inventory_path {
                match resolve_archmap_sidecar_path(&archmap, path) {
                    Some(resolved_path) => match read_json(&resolved_path) {
                        Ok(source_inventory) => source_inventory_document = Some(source_inventory),
                        Err(error) => {
                            source_inventory_error = Some(format!(
                                "source inventory artifact could not be read: {error}"
                            ));
                        }
                    },
                    None => {
                        source_inventory_error =
                            Some("source inventory artifact path does not exist".to_string());
                    }
                }
            }
            let source_inventory = source_inventory_path.map(|path| ArchMapSourceInventoryInput {
                path,
                document: source_inventory_document.as_ref(),
                read_error: source_inventory_error.clone(),
            });
            let archmap_validation = validate_archmap_report(
                &archmap_document,
                &archmap.display().to_string(),
                source_inventory,
            );
            let archmap_failed = archmap_validation.summary.result == "fail";
            write_json(Some(archmap_validation_path), &archmap_validation)?;

            let law_policy_document: LawPolicyDocumentV0 = read_json(&law_policy)?;
            let law_policy_validation =
                validate_law_policy_report(&law_policy_document, &law_policy.display().to_string());
            let law_policy_failed = law_policy_validation.summary.result == "fail";
            write_json(Some(law_policy_validation_path), &law_policy_validation)?;

            let analysis_packet = build_archsig_analysis_packet(
                &archmap_document,
                &law_policy_document,
                Some(&archmap.display().to_string()),
                Some(&law_policy.display().to_string()),
            );
            write_json(Some(analysis_packet_path.clone()), &analysis_packet)?;
            write_json(Some(llm_interpretation_path), &analysis_packet)?;
            let analysis_validation = validate_archsig_analysis_packet_report(
                &analysis_packet,
                &analysis_packet_path.display().to_string(),
            );
            let analysis_failed = analysis_validation.summary.result == "fail";
            write_json(Some(analysis_validation_path), &analysis_validation)?;

            Ok(if archmap_failed || law_policy_failed || analysis_failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::SchemaCatalog { out }) => {
            let catalog: SchemaVersionCatalogV0 = static_schema_version_catalog();
            write_json(out, &catalog)?;
            Ok(ExitCode::SUCCESS)
        }
        None => {
            Err("ArchSig is ArchMap/LawPolicy/analysis-packet primary; use `archsig analyze` for the main analysis path.".into())
        }
    }
}

fn write_json<T: serde::Serialize>(out: Option<PathBuf>, value: &T) -> Result<(), Box<dyn Error>> {
    match out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent)?;
                }
            }
            let mut file = File::create(path)?;
            serde_json::to_writer_pretty(&mut file, value)?;
            writeln!(file)?;
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            serde_json::to_writer_pretty(&mut handle, value)?;
            writeln!(handle)?;
        }
    }
    Ok(())
}

fn read_json<T: serde::de::DeserializeOwned>(path: &PathBuf) -> Result<T, Box<dyn Error>> {
    Ok(serde_json::from_reader(File::open(path)?)?)
}

fn read_optional_json(path: Option<&PathBuf>) -> Result<Option<serde_json::Value>, Box<dyn Error>> {
    path.map(read_json).transpose()
}

fn require_schema(
    document: &serde_json::Value,
    expected: &str,
    field_name: &str,
) -> Result<(), Box<dyn Error>> {
    let actual = document
        .get("schemaVersion")
        .or_else(|| document.get("schema"))
        .and_then(|value| value.as_str());
    if actual != Some(expected) {
        return Err(format!("{field_name} must have schemaVersion {expected}").into());
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn build_codebase_inspection_report(
    snapshot_path: &Path,
    snapshot: &serde_json::Value,
    index_path: &Path,
    index: &serde_json::Value,
    packet_path: &Path,
    packet: &serde_json::Value,
    law_policy_path: Option<&PathBuf>,
    law_policy: Option<&serde_json::Value>,
    recent_deltas: &[(PathBuf, serde_json::Value)],
    limit: usize,
) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let llm_packet = packet
        .get("llmInterpretationPacket")
        .unwrap_or(&serde_json::Value::Null);

    serde_json::json!({
        "schemaVersion": "archsig-codebase-inspection-report-v0",
        "mode": "codebase-inspection",
        "diagnosisKind": "current-state architectural diagnosis",
        "canonicalInputs": {
            "archMapSnapshot": {
                "path": snapshot_path.display().to_string(),
                "schemaVersion": schema_string(snapshot),
                "snapshotId": json_field(snapshot, "snapshotId"),
                "archMapRef": json_field(snapshot, "archMapRef"),
                "coveredCommitRange": json_field(snapshot, "coveredCommitRange"),
                "coverageSummary": json_field(snapshot, "coverageSummary"),
                "compactionReport": json_field(snapshot, "compactionReport")
            },
            "archMapIndex": {
                "path": index_path.display().to_string(),
                "schemaVersion": schema_string(index),
                "indexId": json_field(index, "indexId"),
                "snapshotRef": json_field(index, "snapshotRef"),
                "sourceRefKeyCount": object_key_count(index, "sourceRefIndex"),
                "atomRefKeyCount": object_key_count(index, "atomRefIndex"),
                "boundaryRefKeyCount": object_key_count(index, "boundaryRefIndex"),
                "axisRefKeyCount": object_key_count(index, "axisRefIndex"),
                "operationHintKeyCount": object_key_count(index, "operationHintIndex"),
                "featureHintKeyCount": object_key_count(index, "featureHintIndex"),
                "coverageGapKeyCount": object_key_count(index, "coverageGapIndex")
            },
            "analysisPacket": {
                "path": packet_path.display().to_string(),
                "analysisId": json_field(packet, "analysisId"),
                "archMapRef": json_field(packet, "archMapRef"),
                "selectedLawPolicyRef": json_field(packet, "selectedLawPolicyRef"),
                "archMapStoreRefs": json_field(packet, "archMapStoreRefs")
            },
            "lawPolicy": law_policy.map(|document| serde_json::json!({
                "path": law_policy_path.map(|path| path.display().to_string()),
                "schemaVersion": schema_string(document),
                "policyId": json_field(document, "policyId"),
                "profileId": json_field(document, "profileId")
            })),
            "recentDeltaWindow": recent_delta_summary(recent_deltas, limit)
        },
        "inspectionFlow": {
            "latestSnapshotRef": json_field(snapshot, "snapshotId"),
            "indexRef": json_field(index, "indexId"),
            "recentDeltaCount": recent_deltas.len(),
            "readingBoundary": "codebase inspection starts from latest ArchMapSnapshot plus ArchMapIndex and optionally narrows current-state context with a recent delta window; it does not replay all historical deltas on every run"
        },
        "currentStateDiagnosis": {
            "subsystemBoundarySummary": {
                "architectureBoundaryRefs": array_field(packet.get("architectureState").unwrap_or(&serde_json::Value::Null), "boundaryRefs"),
                "indexBoundaryKeys": object_keys(index, "boundaryRefIndex", limit),
                "boundaryReadingCount": array_len(packet, "featureBoundaryResidualReadings")
            },
            "featureLikeClusterSummary": {
                "featureIndexKeys": object_keys(index, "featureHintIndex", limit),
                "featureExtensionDiagnosisCount": array_len(packet, "featureExtensionDiagnosisReadings"),
                "featureBoundaryResidualCount": array_len(packet, "featureBoundaryResidualReadings"),
                "summary": limited_array_field(llm_packet, "featureExtensionDiagnosisSummary", limit)
            },
            "operationLikeRelationSummary": {
                "operationIndexKeys": object_keys(index, "operationHintIndex", limit),
                "operationSquareCandidateCount": array_len(packet, "operationSquareCandidates"),
                "pathContinuationTraceCount": array_len(packet, "pathContinuationTraces"),
                "summary": limited_array_field(llm_packet, "homotopyOrderSensitivitySummary", limit)
            },
            "topBoundaryHolonomy": top_boundary_holonomy(packet, limit),
            "topOrderSensitiveSquares": top_order_sensitive_squares(packet, limit),
            "architectureSpectrum": architecture_spectrum_summary(packet, llm_packet, Some(limit)),
            "architectureHomotopy": architecture_homotopy_summary(packet, Some(limit)),
            "architectureHealthNextActions": limited_array_field(llm_packet, "recommendedHumanReviewFocus", limit)
        },
        "coverageExactnessBoundary": {
            "flatnessStatus": json_field(flatness, "status"),
            "coverageGaps": array_field(flatness, "blockedByCoverageGaps"),
            "flatnessEvidenceBoundary": json_field(flatness, "evidenceBoundary"),
            "storeCompactionBoundary": json_field(packet.get("archMapStoreRefs").unwrap_or(&serde_json::Value::Null), "compactionBoundary"),
            "snapshotCompactionReport": json_field(snapshot, "compactionReport")
        },
        "surfaceBoundary": {
            "prReviewMode": "change-local diagnosis over base ArchMap / PR-local ArchMapDelta / LawPolicy",
            "codebaseInspectionMode": "current-state architectural diagnosis over latest ArchMapSnapshot / ArchMapIndex / analysis packet",
            "fieldSigBoundary": "FieldSig owns PR / diff / change-vector evolution analysis, forecast, governance, calibration, and longitudinal monitoring"
        },
        "nonConclusions": [
            "ArchSig codebase inspection does not prove repository-wide lawfulness",
            "ArchSig codebase inspection does not prove global safety",
            "ArchSig codebase inspection is not PR / diff evolution analysis",
            "ArchSig codebase inspection does not replace FieldSig longitudinal evolution monitoring",
            "Missing index entries are not absence evidence unless index coverage states a complete universe"
        ]
    })
}

fn recent_delta_summary(
    recent_deltas: &[(PathBuf, serde_json::Value)],
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        recent_deltas
            .iter()
            .take(limit)
            .map(|(path, document)| {
                serde_json::json!({
                    "path": path.display().to_string(),
                    "schemaVersion": schema_string(document),
                    "deltaId": json_field(document, "deltaId"),
                    "changedObservationRefs": array_field(document, "changedObservationRefs"),
                    "nonConclusions": array_field(document, "nonConclusions")
                })
            })
            .collect(),
    )
}

fn top_boundary_holonomy(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut readings = array_items(packet, "featureBoundaryResidualReadings");
    readings.sort_by_key(|reading| std::cmp::Reverse(boundary_residual_score(reading)));
    serde_json::Value::Array(
        readings
            .into_iter()
            .take(limit)
            .map(|reading| {
                serde_json::json!({
                    "readingId": json_field(reading, "readingId"),
                    "boundaryRef": json_field(reading, "boundaryRef"),
                    "status": json_field(reading, "status"),
                    "residualScore": boundary_residual_score(reading),
                    "mixedSubconfigurationRefs": array_field(reading, "mixedSubconfigurationRefs"),
                    "boundarySupportRefs": array_field(reading, "boundarySupportRefs"),
                    "topHolonomyAxes": top_holonomy_axes(reading, 4)
                })
            })
            .collect(),
    )
}

fn top_holonomy_axes(reading: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut axes = array_items(reading, "holonomyAxes");
    axes.sort_by_key(|axis| std::cmp::Reverse(i64_field(axis, "residualValue", 0)));
    serde_json::Value::Array(
        axes.into_iter()
            .take(limit)
            .map(|axis| {
                serde_json::json!({
                    "axisFamily": json_field(axis, "axisFamily"),
                    "status": json_field(axis, "status"),
                    "residualValue": json_field(axis, "residualValue"),
                    "measuredDefectRefs": array_field(axis, "measuredDefectRefs"),
                    "missingEvidence": array_field(axis, "missingEvidence")
                })
            })
            .collect(),
    )
}

fn boundary_residual_score(reading: &serde_json::Value) -> i64 {
    array_items(reading, "holonomyAxes")
        .into_iter()
        .map(|axis| i64_field(axis, "residualValue", 0))
        .sum()
}

fn top_order_sensitive_squares(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut witnesses = array_items(packet, "nonzeroMonodromyWitnesses");
    witnesses.sort_by_key(|witness| std::cmp::Reverse(i64_field(witness, "defectValue", 0)));
    serde_json::Value::Array(
        witnesses
            .into_iter()
            .take(limit)
            .map(|witness| {
                serde_json::json!({
                    "witnessId": json_field(witness, "witnessId"),
                    "candidateRef": json_field(witness, "candidateRef"),
                    "axisFamily": json_field(witness, "axisFamily"),
                    "defectValue": json_field(witness, "defectValue"),
                    "operationPair": array_field(witness, "operationPair"),
                    "pathPair": array_field(witness, "pathPair"),
                    "coverageBoundary": json_field(witness, "coverageBoundary"),
                    "recommendedReviewFocus": array_field(witness, "recommendedReviewFocus")
                })
            })
            .collect(),
    )
}

fn build_pr_review_report(
    base_archmap_path: &Path,
    base_archmap: &serde_json::Value,
    delta_archmap_path: &Path,
    delta_archmap: &serde_json::Value,
    law_policy_path: &Path,
    law_policy: &serde_json::Value,
) -> serde_json::Value {
    let changed_refs = string_array(delta_archmap, "changedObservationRefs");
    let matched_observations = changed_archmap_observations(base_archmap, &changed_refs);
    let changed_families = changed_atom_families(base_archmap, &changed_refs);
    let matched_laws = matched_policy_laws(law_policy, &changed_families);
    let matched_axis_refs = matched_policy_axis_refs(&matched_laws);
    let source_targets =
        source_targets_for_changed_refs(base_archmap, delta_archmap, &changed_refs);

    serde_json::json!({
        "schemaVersion": "archsig-pr-review-report-v1",
        "reviewId": format!(
            "archsig-pr-review:{}:{}:{}",
            json_string(base_archmap, "mapId", "base-archmap"),
            json_string(delta_archmap, "deltaId", "delta-archmap"),
            json_string(law_policy, "lawPolicyId", "law-policy")
        ),
        "canonicalInputs": {
            "baseArchMap": {
                "path": base_archmap_path.display().to_string(),
                "schemaVersion": schema_string(base_archmap),
                "mapId": json_field(base_archmap, "mapId"),
                "architectureId": json_field(base_archmap, "architectureId")
            },
            "deltaArchMap": {
                "path": delta_archmap_path.display().to_string(),
                "schemaVersion": schema_string(delta_archmap),
                "deltaId": json_field(delta_archmap, "deltaId"),
                "baseSnapshotRef": json_field(delta_archmap, "baseSnapshotRef"),
                "headSnapshotRef": json_field(delta_archmap, "headSnapshotRef"),
                "changedObservationRefs": array_field(delta_archmap, "changedObservationRefs")
            },
            "lawPolicy": {
                "path": law_policy_path.display().to_string(),
                "schemaVersion": schema_string(law_policy),
                "lawPolicyId": json_field(law_policy, "lawPolicyId"),
                "policyVersion": json_field(law_policy, "policyVersion"),
                "measurementPolicyId": json_field(
                    law_policy.get("measurementPolicy").unwrap_or(&serde_json::Value::Null),
                    "policyId"
                )
            }
        },
        "policyBoundary": {
            "lawPolicyRequired": true,
            "rule": "No LawPolicy, no ArchSig judgement",
            "selectedAxisRefs": array_field(
                law_policy.get("measurementPolicy").unwrap_or(&serde_json::Value::Null),
                "selectedAxisRefs"
            ),
            "coveragePolicy": json_field(
                law_policy.get("measurementPolicy").unwrap_or(&serde_json::Value::Null),
                "coveragePolicy"
            )
        },
        "changeLocalDiagnosis": {
            "changedObservationCount": changed_refs.len(),
            "matchedBaseObservationCount": matched_observations.as_array().map(Vec::len).unwrap_or_default(),
            "changedAtomFamilies": json_string_array(changed_families.iter()),
            "policyMatchedLawCount": matched_laws.as_array().map(Vec::len).unwrap_or_default(),
            "policyMatchedAxisRefs": json_string_array(matched_axis_refs.iter()),
            "sourceTargetCount": source_targets.as_array().map(Vec::len).unwrap_or_default()
        },
        "changedObservations": matched_observations,
        "policyMatchedLaws": matched_laws,
        "sourceTargets": source_targets,
        "evidenceBoundary": "ArchSig PR review reads base ArchMap, PR-local ArchMap delta, and LawPolicy only. Raw diff, ArchMapCommit, and base/head analysis packets are outside this input surface."
    })
}

fn changed_archmap_observations(
    base_archmap: &serde_json::Value,
    changed_refs: &[String],
) -> serde_json::Value {
    serde_json::Value::Array(
        changed_refs
            .iter()
            .map(|changed_ref| {
                if let Some((kind, observation)) =
                    find_archmap_observation(base_archmap, changed_ref)
                {
                    serde_json::json!({
                        "ref": changed_ref,
                        "matched": true,
                        "kind": kind,
                        "family": observation_family(kind, observation),
                        "subjectRef": json_field(observation, "subjectRef"),
                        "predicate": json_field(observation, "predicate"),
                        "roleName": json_field(observation, "roleName"),
                        "sourceRefs": array_field(observation, "sourceRefs")
                    })
                } else {
                    serde_json::json!({
                        "ref": changed_ref,
                        "matched": false
                    })
                }
            })
            .collect(),
    )
}

fn find_archmap_observation<'a>(
    archmap: &'a serde_json::Value,
    observation_ref: &str,
) -> Option<(&'static str, &'a serde_json::Value)> {
    for observation in array_items(archmap, "atomObservations") {
        if observation
            .get("atomObservationId")
            .and_then(serde_json::Value::as_str)
            == Some(observation_ref)
        {
            return Some(("atom", observation));
        }
    }
    for observation in array_items(archmap, "moleculeObservations") {
        if observation
            .get("moleculeObservationId")
            .and_then(serde_json::Value::as_str)
            == Some(observation_ref)
        {
            return Some(("molecule", observation));
        }
    }
    for observation in array_items(archmap, "semanticObservations") {
        if observation
            .get("semanticObservationId")
            .and_then(serde_json::Value::as_str)
            == Some(observation_ref)
        {
            return Some(("semantic", observation));
        }
    }
    None
}

fn observation_family(kind: &str, observation: &serde_json::Value) -> serde_json::Value {
    match kind {
        "atom" => json_field(observation, "atomFamily"),
        "molecule" => json_field(observation, "moleculeFamily"),
        "semantic" => serde_json::Value::String("semantic".to_string()),
        _ => serde_json::Value::Null,
    }
}

fn changed_atom_families(
    base_archmap: &serde_json::Value,
    changed_refs: &[String],
) -> BTreeSet<String> {
    changed_refs
        .iter()
        .filter_map(|changed_ref| {
            find_archmap_observation(base_archmap, changed_ref).and_then(|(kind, observation)| {
                if kind == "atom" {
                    observation
                        .get("atomFamily")
                        .and_then(serde_json::Value::as_str)
                        .map(str::to_string)
                } else if kind == "semantic" {
                    Some("semantic".to_string())
                } else {
                    None
                }
            })
        })
        .collect()
}

fn matched_policy_laws(
    law_policy: &serde_json::Value,
    changed_families: &BTreeSet<String>,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(law_policy, "selectedLaws")
            .into_iter()
            .filter(|law| {
                array_items(law, "appliesToAtomFamilies")
                    .into_iter()
                    .filter_map(serde_json::Value::as_str)
                    .any(|family| changed_families.contains(family))
            })
            .map(|law| {
                serde_json::json!({
                    "lawId": json_field(law, "lawId"),
                    "lawFamily": json_field(law, "lawFamily"),
                    "requiredAxisRefs": array_field(law, "requiredAxisRefs"),
                    "matchedAtomFamilies": json_string_array(
                        array_items(law, "appliesToAtomFamilies")
                            .into_iter()
                            .filter_map(serde_json::Value::as_str)
                            .filter(|family| changed_families.contains(*family))
                    )
                })
            })
            .collect(),
    )
}

fn matched_policy_axis_refs(matched_laws: &serde_json::Value) -> BTreeSet<String> {
    matched_laws
        .as_array()
        .into_iter()
        .flat_map(|laws| laws.iter())
        .flat_map(|law| array_items(law, "requiredAxisRefs"))
        .filter_map(serde_json::Value::as_str)
        .map(str::to_string)
        .collect()
}

fn source_targets_for_changed_refs(
    base_archmap: &serde_json::Value,
    delta_archmap: &serde_json::Value,
    changed_refs: &[String],
) -> serde_json::Value {
    let mut paths = BTreeSet::new();
    for target in array_items(
        delta_archmap
            .get("reviewIntent")
            .unwrap_or(&serde_json::Value::Null),
        "sourceFirstTargets",
    ) {
        if let Some(path) = target.as_str() {
            paths.insert(path.to_string());
        }
    }
    for changed_ref in changed_refs {
        if let Some((_kind, observation)) = find_archmap_observation(base_archmap, changed_ref) {
            for source_ref in array_items(observation, "sourceRefs") {
                if let Some(path) = source_ref.get("path").and_then(serde_json::Value::as_str) {
                    let target = if let Some(symbol) =
                        source_ref.get("symbol").and_then(serde_json::Value::as_str)
                    {
                        format!("{path}:{symbol}")
                    } else {
                        path.to_string()
                    };
                    paths.insert(target);
                }
            }
        }
    }
    json_string_array(paths.iter())
}

fn json_string_array<I, S>(items: I) -> serde_json::Value
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let mut values: Vec<String> = items
        .into_iter()
        .map(|item| item.as_ref().to_string())
        .collect();
    values.sort();
    values.dedup();
    serde_json::Value::Array(values.into_iter().map(serde_json::Value::String).collect())
}

fn string_array(value: &serde_json::Value, key: &str) -> Vec<String> {
    array_items(value, key)
        .into_iter()
        .filter_map(serde_json::Value::as_str)
        .map(str::to_string)
        .collect()
}

fn schema_string(document: &serde_json::Value) -> serde_json::Value {
    document
        .get("schemaVersion")
        .or_else(|| document.get("schema"))
        .cloned()
        .unwrap_or(serde_json::Value::Null)
}

fn json_string(document: &serde_json::Value, field: &str, fallback: &str) -> String {
    document
        .get(field)
        .and_then(|value| value.as_str())
        .unwrap_or(fallback)
        .to_string()
}

fn build_analysis_summary(
    packet: &serde_json::Value,
    archmap_validation: Option<&serde_json::Value>,
    law_policy_validation: Option<&serde_json::Value>,
    analysis_validation: Option<&serde_json::Value>,
) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let llm_packet = packet
        .get("llmInterpretationPacket")
        .unwrap_or(&serde_json::Value::Null);

    serde_json::json!({
        "packet": {
            "schemaVersion": json_field(packet, "schemaVersion"),
            "analysisId": json_field(packet, "analysisId"),
            "archMapRef": json_field(packet, "archMapRef"),
            "selectedLawPolicyRef": json_field(packet, "selectedLawPolicyRef"),
            "generatedAt": json_field(packet, "generatedAt")
        },
        "validation": {
            "archmap": validation_summary(archmap_validation),
            "lawPolicy": validation_summary(law_policy_validation),
            "analysis": validation_summary(analysis_validation)
        },
        "verdict": analysis_verdict(packet),
        "qualityMeasurement": quality_measurement(packet),
        "actionQueue": action_queue(packet),
        "measurementBasis": measurement_basis(
            packet,
            archmap_validation,
            law_policy_validation,
            analysis_validation
        ),
        "flatness": {
            "status": json_field(flatness, "status"),
            "zeroSignatureAxisRefs": array_field(flatness, "zeroSignatureAxisRefs"),
            "nonzeroSignatureAxisRefs": array_field(flatness, "nonzeroSignatureAxisRefs"),
            "blockedByCoverageGaps": array_field(flatness, "blockedByCoverageGaps")
        },
        "signatureAxes": signature_axis_summary(packet),
        "topWorkflowRisks": top_workflow_risks(packet),
        "spectralAnalysis": spectral_summary(packet),
        "architectureSpectrum": architecture_spectrum_summary(packet, llm_packet, None),
        "architectureHomotopy": architecture_homotopy_summary(packet, None),
        "transferBridges": transfer_bridge_summary(packet),
        "measurementExpansion": measurement_expansion_summary(packet, llm_packet),
        "splitReadiness": split_readiness_summary(packet),
        "llmReviewIndex": {
            "structuralReadingReviewSummary": array_field(llm_packet, "structuralReadingReviewSummary"),
            "currentStateEvolutionBoundarySummary": array_field(llm_packet, "currentStateEvolutionBoundarySummary"),
            "recommendedHumanReviewFocus": array_field(llm_packet, "recommendedHumanReviewFocus"),
            "transferBridgeEdgeSummary": array_field(llm_packet, "transferBridgeEdgeSummary")
        },
        "metadata": {
            "nonConclusions": array_field(packet, "nonConclusions"),
            "spectrumNonConclusions": array_field(
                packet.get("architectureSpectrumReport").unwrap_or(&serde_json::Value::Null),
                "nonConclusions"
            ),
            "homotopyNonConclusions": array_field(
                packet.get("architectureHomotopyReport").unwrap_or(&serde_json::Value::Null),
                "nonConclusions"
            ),
            "excludedReadings": array_field(packet, "excludedReadings")
        }
    })
}

fn analysis_verdict(packet: &serde_json::Value) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    let nonzero_axis_count = array_len(flatness, "nonzeroSignatureAxisRefs");
    let hotspot_count = array_len(spectrum, "topHotspots");
    let recurrent_count = array_len(spectrum, "recurrentObstructions");
    let architectural_hole_count = array_len(homotopy, "unfilledLoops");
    let nonzero_holonomy_count = array_len(homotopy, "nonzeroHolonomyLoops");
    let coverage_gap_count = coverage_gap_refs(packet).len();

    let flatness_status = flatness
        .get("status")
        .and_then(serde_json::Value::as_str)
        .unwrap_or("unknownUnderSelectedPolicy");
    let flatness_verdict = if nonzero_axis_count > 0 {
        "nonflatUnderSelectedPolicy"
    } else if flatness_status.contains("flat") {
        "flatUnderSelectedPolicy"
    } else {
        "unknownUnderSelectedPolicy"
    };
    let pressure_detected = nonzero_axis_count > 0 || hotspot_count > 0 || recurrent_count > 0;
    let holes_detected = architectural_hole_count > 0 || nonzero_holonomy_count > 0;
    let quality_state = match (pressure_detected, holes_detected, coverage_gap_count > 0) {
        (true, true, _) => "pressureAndArchitecturalHolesDetected",
        (true, false, _) => "architecturePressureDetected",
        (false, true, _) => "architecturalHolesDetected",
        (false, false, true) => "coverageGapsDetected",
        (false, false, false) => "noMeasuredPressureDetected",
    };
    let actionability = if pressure_detected || holes_detected || coverage_gap_count > 0 {
        "reviewRequired"
    } else {
        "noImmediateReviewQueue"
    };
    let primary_conclusion = if nonzero_axis_count > 0 && architectural_hole_count > 0 {
        "selected law axes are nonzero and architectural holes were measured from the supplied ArchMap and LawPolicy"
    } else if nonzero_axis_count > 0 {
        "selected law axes are nonzero under the supplied ArchMap and LawPolicy"
    } else if architectural_hole_count > 0 {
        "architectural holes were measured from unfilled loops under the supplied ArchMap and LawPolicy"
    } else if coverage_gap_count > 0 {
        "coverage gaps block a zero reading under the supplied ArchMap and LawPolicy"
    } else {
        "no nonzero architecture pressure was measured under the supplied ArchMap and LawPolicy"
    };

    serde_json::json!({
        "flatness": flatness_verdict,
        "qualityState": quality_state,
        "primaryConclusion": primary_conclusion,
        "actionability": actionability,
        "readingMode": "measurementOverSuppliedArchMapAndLawPolicy"
    })
}

fn quality_measurement(packet: &serde_json::Value) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "selectedAxisCount": array_len(packet, "signatureAxes"),
        "nonzeroAxisCount": array_len(flatness, "nonzeroSignatureAxisRefs"),
        "zeroAxisCount": array_len(flatness, "zeroSignatureAxisRefs"),
        "spectrumHotspotCount": array_len(spectrum, "topHotspots"),
        "recurrentObstructionCount": array_len(spectrum, "recurrentObstructions"),
        "witnessClusterCount": array_len(spectrum, "topWitnessClusters"),
        "architecturalHoleCount": array_len(homotopy, "unfilledLoops"),
        "filledLoopCount": array_len(homotopy, "filledLoops"),
        "nonzeroHolonomyLoopCount": array_len(homotopy, "nonzeroHolonomyLoops"),
        "localCurvatureCellCount": array_len(homotopy, "topLocalCurvatureCells"),
        "workflowRiskCount": array_len(packet, "workflowRiskReadings"),
        "transferBridgeCount": array_len(packet, "transferBridgeReadings"),
        "coverageGapCount": coverage_gap_refs(packet).len()
    })
}

fn action_queue(packet: &serde_json::Value) -> serde_json::Value {
    let mut actions = Vec::new();
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);

    for hotspot in array_items(spectrum, "topHotspots") {
        actions.push(serde_json::json!({
            "kind": "spectrumHotspot",
            "conclusion": "measuredPressureHotspot",
            "ref": json_field(hotspot, "hotspotId"),
            "axisRef": json_field(hotspot, "axisRef"),
            "value": json_field(hotspot, "curvatureValue"),
            "witnessRefs": array_field(hotspot, "witnessRefs"),
            "recommendedAction": json_field(hotspot, "recommendedNextAction")
        }));
    }
    for loop_ref in array_items(homotopy, "unfilledLoops") {
        actions.push(serde_json::json!({
            "kind": "architecturalHole",
            "conclusion": "unfilledLoopMeasured",
            "ref": loop_ref.clone(),
            "recommendedAction": "inspect path refs and add contract, test, runtime, policy, or source-backed filler evidence"
        }));
    }
    for loop_ref in array_items(homotopy, "nonzeroHolonomyLoops") {
        actions.push(serde_json::json!({
            "kind": "nonzeroHolonomy",
            "conclusion": "nonzeroSelectedAxisContinuationDistance",
            "ref": loop_ref.clone(),
            "recommendedAction": "compare selected path continuations and decide whether the loop needs filler evidence or design change"
        }));
    }
    for axis in array_items(packet, "signatureAxes") {
        if i64_field(axis, "value", 0) != 0 {
            actions.push(serde_json::json!({
                "kind": "nonzeroSignatureAxis",
                "conclusion": "nonzeroAxisUnderSelectedPolicy",
                "ref": json_field(axis, "signatureAxisId"),
                "lawRef": json_field(axis, "lawRef"),
                "value": json_field(axis, "value"),
                "coverageStatus": json_field(axis, "coverageStatus"),
                "sourceRefCount": array_len(axis, "sourceRefs"),
                "missingEvidenceCount": array_len(axis, "missingEvidence"),
                "recommendedAction": "inspect source refs and selected law witness support"
            }));
        }
    }
    let mut workflow_risks = array_items(packet, "workflowRiskReadings");
    workflow_risks.sort_by_key(|reading| std::cmp::Reverse(i64_field(reading, "riskScore", 0)));
    for reading in workflow_risks {
        actions.push(serde_json::json!({
            "kind": "workflowRisk",
            "conclusion": "highRankedWorkflowPressure",
            "ref": json_field(reading, "moleculeObservationRef"),
            "roleName": json_field(reading, "roleName"),
            "value": json_field(reading, "riskScore"),
            "riskTier": json_field(reading, "riskTier"),
            "recommendedAction": array_field(reading, "reviewFocus")
        }));
    }

    serde_json::Value::Array(
        actions
            .into_iter()
            .enumerate()
            .map(|(index, mut action)| {
                if let Some(object) = action.as_object_mut() {
                    object.insert(
                        "priority".to_string(),
                        serde_json::Value::Number((index + 1).into()),
                    );
                }
                action
            })
            .collect(),
    )
}

fn measurement_basis(
    packet: &serde_json::Value,
    archmap_validation: Option<&serde_json::Value>,
    law_policy_validation: Option<&serde_json::Value>,
    analysis_validation: Option<&serde_json::Value>,
) -> serde_json::Value {
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "archMapRef": json_field(packet, "archMapRef"),
        "selectedLawPolicyRef": json_field(packet, "selectedLawPolicyRef"),
        "spectrumProfileRef": json_field(spectrum, "profileRef"),
        "homotopyProfileRef": json_field(homotopy, "profileRef"),
        "validation": {
            "archmap": validation_result(archmap_validation),
            "lawPolicy": validation_result(law_policy_validation),
            "analysis": validation_result(analysis_validation)
        },
        "coverageGaps": json_string_array(coverage_gap_refs(packet).iter()),
        "spectrumMeasuredBoundary": json_field(spectrum, "measuredBoundary"),
        "homotopyMeasuredBoundary": json_field(homotopy, "measuredBoundary"),
        "basisStatement": "conclusions are measured from the supplied ArchMap and selected LawPolicy"
    })
}

fn validation_result(report: Option<&serde_json::Value>) -> serde_json::Value {
    validation_summary(report)
        .get("result")
        .cloned()
        .unwrap_or(serde_json::Value::Null)
}

fn coverage_gap_refs(packet: &serde_json::Value) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    if let Some(flatness) = packet.get("flatnessReading") {
        collect_value_labels(array_items(flatness, "blockedByCoverageGaps"), &mut refs);
    }
    if let Some(spectrum) = packet.get("architectureSpectrumReport") {
        collect_value_labels(array_items(spectrum, "coverageGaps"), &mut refs);
    }
    if let Some(homotopy) = packet.get("architectureHomotopyReport") {
        collect_value_labels(array_items(homotopy, "coverageGaps"), &mut refs);
    }
    refs
}

fn collect_value_labels(items: Vec<&serde_json::Value>, refs: &mut BTreeSet<String>) {
    for item in items {
        if let Some(label) = value_label(item) {
            refs.insert(label);
        }
    }
}

fn value_label(value: &serde_json::Value) -> Option<String> {
    value
        .as_str()
        .map(str::to_string)
        .or_else(|| {
            value
                .get("gapId")
                .and_then(serde_json::Value::as_str)
                .map(str::to_string)
        })
        .or_else(|| {
            value
                .get("id")
                .and_then(serde_json::Value::as_str)
                .map(str::to_string)
        })
        .or_else(|| {
            value
                .get("description")
                .and_then(serde_json::Value::as_str)
                .map(str::to_string)
        })
}

fn measurement_expansion_summary(
    packet: &serde_json::Value,
    llm_packet: &serde_json::Value,
) -> serde_json::Value {
    serde_json::json!({
        "summary": array_field(llm_packet, "measurementExpansionSummary"),
        "atomSupportAxis": array_field(llm_packet, "atomSupportAxisSummary"),
        "atomCompatibility": array_field(llm_packet, "atomCompatibilitySummary"),
        "lawUniverseCoverage": array_field(llm_packet, "lawUniverseCoverageSummary"),
        "featureExtensionFormula": array_field(llm_packet, "featureExtensionFormulaSummary"),
        "operationCalculusLaw": array_field(llm_packet, "operationCalculusLawSummary"),
        "pathSignatureTrajectory": array_field(llm_packet, "pathSignatureTrajectorySummary"),
        "homotopyOrderSensitivity": array_field(llm_packet, "homotopyOrderSensitivitySummary"),
        "diagramFillability": array_field(llm_packet, "diagramFillabilitySummary"),
        "axisForgettingRisk": array_field(llm_packet, "axisForgettingRiskSummary"),
        "signatureTrajectoryHomotopyRefutation": array_field(llm_packet, "signatureTrajectoryHomotopyRefutationSummary"),
        "bridgeSplitObstructionTransfer": array_field(llm_packet, "bridgeSplitObstructionTransferSummary"),
        "nonzeroMonodromyWitness": array_field(llm_packet, "nonzeroMonodromyWitnessSummary"),
        "featureBoundaryResidual": array_field(llm_packet, "featureBoundaryResidualSummary"),
        "featureExtensionDiagnosis": array_field(llm_packet, "featureExtensionDiagnosisSummary"),
        "counts": {
            "atomSupportAxisReadings": array_len(packet, "atomSupportAxisReadings"),
            "atomCompatibilityReadings": array_len(packet, "atomCompatibilityReadings"),
            "lawUniverseCoverageReadings": array_len(packet, "lawUniverseCoverageReadings"),
            "featureExtensionFormulaReadings": array_len(packet, "featureExtensionFormulaReadings"),
            "operationCalculusLawReadings": array_len(packet, "operationCalculusLawReadings"),
            "pathSignatureTrajectoryReadings": array_len(packet, "pathSignatureTrajectoryReadings"),
            "homotopyOrderSensitivityReadings": array_len(packet, "homotopyOrderSensitivityReadings"),
            "diagramFillabilityReadings": array_len(packet, "diagramFillabilityReadings"),
            "axisForgettingRiskReadings": array_len(packet, "axisForgettingRiskReadings"),
            "signatureTrajectoryHomotopyRefutationReadings": array_len(packet, "signatureTrajectoryHomotopyRefutationReadings"),
            "bridgeSplitObstructionTransferReadings": array_len(packet, "bridgeSplitObstructionTransferReadings"),
            "nonzeroMonodromyWitnesses": array_len(packet, "nonzeroMonodromyWitnesses"),
            "featureBoundaryResidualReadings": array_len(packet, "featureBoundaryResidualReadings"),
            "featureExtensionDiagnosisReadings": array_len(packet, "featureExtensionDiagnosisReadings")
        }
    })
}

fn validation_summary(report: Option<&serde_json::Value>) -> serde_json::Value {
    let Some(report) = report else {
        return serde_json::Value::Null;
    };
    if let Some(summary) = report.get("summary") {
        return summary.clone();
    }
    serde_json::json!({
        "result": json_field(report, "status"),
        "failedCheckCount": json_field(report, "failedChecks"),
        "warningCheckCount": json_field(report, "warningChecks"),
        "passedCheckCount": json_field(report, "passedChecks")
    })
}

fn top_workflow_risks(packet: &serde_json::Value) -> serde_json::Value {
    let mut readings = array_items(packet, "workflowRiskReadings");
    readings.sort_by_key(|reading| std::cmp::Reverse(i64_field(reading, "riskScore", 0)));
    serde_json::Value::Array(
        readings
            .into_iter()
            .map(|reading| {
                serde_json::json!({
                    "molecule": json_field(reading, "moleculeObservationRef"),
                    "roleName": json_field(reading, "roleName"),
                    "status": json_field(reading, "status"),
                    "riskScore": json_field(reading, "riskScore"),
                    "riskTier": json_field(reading, "riskTier"),
                    "topAxes": top_axis_summary(reading),
                    "reviewFocus": array_field(reading, "reviewFocus")
                })
            })
            .collect(),
    )
}

fn top_axis_summary(reading: &serde_json::Value) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(reading, "topAxes")
            .into_iter()
            .take(3)
            .map(|axis| {
                serde_json::json!({
                    "axis": json_field(axis, "axis"),
                    "score": json_field(axis, "score"),
                    "status": json_field(axis, "status"),
                    "coverageGapRefs": array_field(axis, "coverageGapRefs")
                })
            })
            .collect(),
    )
}

fn spectral_summary(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "spectralAnalysisReadings")
            .into_iter()
            .map(|reading| {
                serde_json::json!({
                    "id": json_field(reading, "spectralReadingId"),
                    "family": json_field(reading, "representationFamily"),
                    "status": json_field(reading, "status"),
                    "shape": json_field(reading, "matrixShape"),
                    "values": array_field(reading, "values"),
                    "dominantComponents": array_field(reading, "dominantComponents"),
                    "recommendedNextAction": json_field(reading, "recommendedNextAction")
                })
            })
            .collect(),
    )
}

fn transfer_bridge_summary(packet: &serde_json::Value) -> serde_json::Value {
    let mut bridges = Vec::new();
    for reading in array_items(packet, "transferBridgeReadings") {
        for bridge in array_items(reading, "bridgeAtomFamilies") {
            let edges = serde_json::Value::Array(
                array_items(bridge, "edgeBreakdowns")
                    .into_iter()
                    .map(|edge| {
                        serde_json::json!({
                            "edgeId": json_field(edge, "edgeId"),
                            "source": json_field(edge, "sourceMoleculeRef"),
                            "target": json_field(edge, "targetMoleculeRef"),
                            "overlapScore": json_field(edge, "overlapScore"),
                            "sharedAtomFamilies": array_field(edge, "sharedAtomFamilies"),
                            "dependencyKind": json_field(edge, "dependencyKind"),
                            "recommendedCutKind": json_field(edge, "recommendedCutKind"),
                            "sourceRefCount": array_len(edge, "sourceRefs"),
                            "reviewFocus": array_field(edge, "reviewFocus")
                        })
                    })
                    .collect(),
            );
            bridges.push(serde_json::json!({
                "transferBridgeId": json_field(reading, "transferBridgeId"),
                "status": json_field(reading, "status"),
                "bridgeId": json_field(bridge, "bridgeId"),
                "sourceHub": json_field(bridge, "sourceHubMoleculeRef"),
                "targetHub": json_field(bridge, "targetHubMoleculeRef"),
                "intermediateMoleculeRefs": array_field(bridge, "intermediateMoleculeRefs"),
                "bridgeScore": json_field(bridge, "bridgeScore"),
                "reviewRisk": json_field(bridge, "reviewRisk"),
                "sharedAxisRefs": array_field(bridge, "sharedAxisRefs"),
                "pathPairRefs": array_field(bridge, "pathPairRefs"),
                "edges": edges
            }));
        }
    }
    serde_json::Value::Array(bridges)
}

fn architecture_spectrum_summary(
    packet: &serde_json::Value,
    llm_packet: &serde_json::Value,
    limit: Option<usize>,
) -> serde_json::Value {
    let report = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "reportId": json_field(report, "reportId"),
        "status": json_field(report, "status"),
        "profileRef": json_field(report, "profileRef"),
        "summary": array_field_with_limit(llm_packet, "architectureSpectrumReportSummary", limit),
        "hotspots": array_field_with_limit(report, "topHotspots", limit),
        "topEigenmodes": array_field_with_limit(report, "topEigenmodes", limit),
        "witnessClusters": array_field_with_limit(report, "topWitnessClusters", limit),
        "recurrentObstructions": array_field_with_limit(report, "recurrentObstructions", limit),
        "coverageGaps": array_field_with_limit(report, "coverageGaps", limit),
        "measuredBoundary": json_field(report, "measuredBoundary"),
        "recommendedReviewFocus": array_field_with_limit(report, "recommendedReviewFocus", limit),
        "nonConclusions": array_field(report, "nonConclusions")
    })
}

fn architecture_homotopy_summary(
    packet: &serde_json::Value,
    limit: Option<usize>,
) -> serde_json::Value {
    let report = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "reportId": json_field(report, "reportId"),
        "status": json_field(report, "status"),
        "profileRef": json_field(report, "profileRef"),
        "filledLoops": array_field_with_limit(report, "filledLoops", limit),
        "unfilledLoops": array_field_with_limit(report, "unfilledLoops", limit),
        "nonzeroHolonomyLoops": array_field_with_limit(report, "nonzeroHolonomyLoops", limit),
        "topLocalCurvatureCells": array_field_with_limit(report, "topLocalCurvatureCells", limit),
        "aggregateReadings": array_field_with_limit(report, "aggregateReadings", limit),
        "coverageGaps": array_field_with_limit(report, "coverageGaps", limit),
        "measuredBoundary": json_field(report, "measuredBoundary"),
        "recommendedReviewFocus": array_field_with_limit(report, "recommendedReviewFocus", limit),
        "nonConclusions": array_field(report, "nonConclusions")
    })
}

fn split_readiness_summary(packet: &serde_json::Value) -> serde_json::Value {
    let mut readings = array_items(packet, "splitReadinessReadings");
    readings.sort_by_key(|reading| i64_field(reading, "readinessScore", i64::MAX));
    serde_json::Value::Array(
        readings
            .into_iter()
            .map(|reading| {
                serde_json::json!({
                    "molecule": json_field(reading, "moleculeRef"),
                    "status": json_field(reading, "status"),
                    "readinessScore": json_field(reading, "readinessScore"),
                    "liftingEvidenceStatus": json_field(reading, "liftingEvidenceStatus"),
                    "recommendedBoundaryOperation": json_field(reading, "recommendedBoundaryOperation"),
                    "bridgeEdgeRefs": array_field(reading, "bridgeEdgeRefs"),
                    "interactionObstructionRefs": array_field(reading, "interactionObstructionRefs")
                })
            })
            .collect(),
    )
}

fn signature_axis_summary(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "signatureAxes")
            .into_iter()
            .map(|axis| {
                serde_json::json!({
                    "axis": json_field(axis, "signatureAxisId"),
                    "lawRef": json_field(axis, "lawRef"),
                    "value": json_field(axis, "value"),
                    "coverageStatus": json_field(axis, "coverageStatus"),
                    "missingEvidenceCount": array_len(axis, "missingEvidence"),
                    "sourceRefCount": array_len(axis, "sourceRefs")
                })
            })
            .collect(),
    )
}

fn json_field(value: &serde_json::Value, key: &str) -> serde_json::Value {
    value.get(key).cloned().unwrap_or(serde_json::Value::Null)
}

fn array_field(value: &serde_json::Value, key: &str) -> serde_json::Value {
    serde_json::Value::Array(array_items(value, key).into_iter().cloned().collect())
}

fn array_field_with_limit(
    value: &serde_json::Value,
    key: &str,
    limit: Option<usize>,
) -> serde_json::Value {
    let items = array_items(value, key).into_iter();
    match limit {
        Some(limit) => serde_json::Value::Array(items.take(limit).cloned().collect()),
        None => serde_json::Value::Array(items.cloned().collect()),
    }
}

fn limited_array_field(value: &serde_json::Value, key: &str, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(value, key)
            .into_iter()
            .take(limit)
            .cloned()
            .collect(),
    )
}

fn array_items<'a>(value: &'a serde_json::Value, key: &str) -> Vec<&'a serde_json::Value> {
    value
        .get(key)
        .and_then(serde_json::Value::as_array)
        .map(|items| items.iter().collect())
        .unwrap_or_default()
}

fn array_len(value: &serde_json::Value, key: &str) -> usize {
    value
        .get(key)
        .and_then(serde_json::Value::as_array)
        .map(Vec::len)
        .unwrap_or_default()
}

fn object_key_count(value: &serde_json::Value, key: &str) -> usize {
    value
        .get(key)
        .and_then(serde_json::Value::as_object)
        .map(serde_json::Map::len)
        .unwrap_or_default()
}

fn object_keys(value: &serde_json::Value, key: &str, limit: usize) -> serde_json::Value {
    let mut keys: Vec<_> = value
        .get(key)
        .and_then(serde_json::Value::as_object)
        .map(|object| object.keys().cloned().collect())
        .unwrap_or_default();
    keys.sort();
    serde_json::Value::Array(
        keys.into_iter()
            .take(limit)
            .map(serde_json::Value::String)
            .collect(),
    )
}

fn i64_field(value: &serde_json::Value, key: &str, default: i64) -> i64 {
    value
        .get(key)
        .and_then(serde_json::Value::as_i64)
        .unwrap_or(default)
}

fn resolve_archmap_sidecar_path(archmap_path: &Path, sidecar_path: &str) -> Option<PathBuf> {
    let raw_path = PathBuf::from(sidecar_path);
    if raw_path.is_absolute() {
        return raw_path.exists().then_some(raw_path);
    }

    if let Ok(current_dir) = std::env::current_dir() {
        let candidate = current_dir.join(&raw_path);
        if candidate.exists() {
            return Some(candidate);
        }
    }

    let archmap_parent = archmap_path.parent()?;
    let local_candidate = archmap_parent.join(&raw_path);
    if local_candidate.exists() {
        return Some(local_candidate);
    }
    for ancestor in archmap_parent.ancestors() {
        let candidate = ancestor.join(&raw_path);
        if candidate.exists() {
            return Some(candidate);
        }
    }
    None
}
