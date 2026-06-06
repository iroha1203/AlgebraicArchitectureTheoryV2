use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use archsig::{
    ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION, ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION,
    ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION, ArchMapDocumentV0, ArchMapSourceInventoryInput,
    ArchMapSourceInventoryV0, ArchMapValidationReportV0, ArchSigAnalysisPacketValidationReportV0,
    ArchSigArtifactValidationResultV0, ArchSigAtomViewerAtomNodeV0, ArchSigAtomViewerDataV0,
    ArchSigAtomViewerEdgeV0, ArchSigAtomViewerLayoutSettingsV0, ArchSigAtomViewerMoleculeGroupV0,
    ArchSigAtomViewerOmittedDetailCountsV0, ArchSigAtomViewerSourceArtifactRefsV0,
    ArchSigAtomViewerTruncationPolicyV0, ArchSigAtomViewerVisualV0,
    ArchSigRunManifestRawArtifactPathsV0, ArchSigRunManifestV0,
    ArchSigRunManifestValidationReportPathsV0, ArchSigRunManifestValidationResultSummaryV0,
    LawPolicyDocumentV0, LawPolicyValidationReportV0, SchemaVersionCatalogV0,
    build_archsig_analysis_packet, static_law_policy, static_schema_version_catalog,
    validate_archmap_report, validate_archsig_analysis_packet_report, validate_law_policy_report,
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

        /// Also write full raw analysis artifacts for FieldSig handoff and deep evidence lookup.
        #[arg(long = "emit-raw-artifacts")]
        emit_raw_artifacts: bool,

        /// Fail when Part IV distance measurement would rely on legacy profile fallback, proxy, or schema-only rows.
        #[arg(long = "strict-distance")]
        strict_distance: bool,
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

        /// Optional compact LLM interpretation packet output path.
        #[arg(long = "llm-interpretation-out")]
        llm_interpretation_out: Option<PathBuf>,

        /// Fail when Part IV distance measurement would rely on legacy profile fallback, proxy, or schema-only rows.
        #[arg(long = "strict-distance")]
        strict_distance: bool,
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

    /// Produce a lightweight ArchSig PR review report from base/head ArchMap, PR-local ArchMap delta, and LawPolicy.
    PrReview {
        /// Input base archmap-observation-map-v0 JSON path.
        #[arg(long = "base-archmap")]
        base_archmap: PathBuf,

        /// Optional input head archmap-observation-map-v0 JSON path for Part IV PR drift distance.
        #[arg(long = "after-archmap")]
        after_archmap: Option<PathBuf>,

        /// Optional intermediate archmap-observation-map-v0 snapshots along the PR path. May be supplied multiple times.
        #[arg(long = "path-archmap")]
        path_archmap: Vec<PathBuf>,

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
            strict_distance,
        }) => {
            let archmap_document: ArchMapDocumentV0 = read_json(&archmap)?;
            let law_policy_document: LawPolicyDocumentV0 = read_json(&law_policy)?;
            let law_policy_validation =
                validate_law_policy_report(&law_policy_document, &law_policy.display().to_string());
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
                write_json(Some(path), &packet.llm_interpretation_packet)?;
            }
            write_json(out, &packet)?;
            if strict_distance {
                enforce_strict_distance_contract(&law_policy_validation, &validation)?;
            }
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
            after_archmap,
            path_archmap,
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
            let base_archmap_typed: ArchMapDocumentV0 =
                serde_json::from_value(base_archmap_document.clone())?;
            let after_archmap_document = if let Some(after_archmap) = after_archmap.as_ref() {
                let document: serde_json::Value = read_json(after_archmap)?;
                require_schema(
                    &document,
                    "archmap-observation-map-v0",
                    "--after-archmap",
                )?;
                Some(document)
            } else {
                None
            };
            let after_archmap_typed = after_archmap_document
                .as_ref()
                .map(|document| serde_json::from_value::<ArchMapDocumentV0>(document.clone()))
                .transpose()?;
            let mut path_archmap_documents = Vec::new();
            let mut path_archmap_typed = Vec::new();
            for path in &path_archmap {
                let document: serde_json::Value = read_json(path)?;
                require_schema(&document, "archmap-observation-map-v0", "--path-archmap")?;
                path_archmap_typed.push(serde_json::from_value::<ArchMapDocumentV0>(
                    document.clone(),
                )?);
                path_archmap_documents.push(document);
            }
            let delta_archmap_document: serde_json::Value = read_json(&delta_archmap)?;
            require_schema(&delta_archmap_document, "archmap-delta-v0", "--delta-archmap")?;
            let law_policy_document: serde_json::Value = read_json(&law_policy)?;
            require_schema(&law_policy_document, "law-policy-v0", "--law-policy")?;
            let law_policy_typed: LawPolicyDocumentV0 =
                serde_json::from_value(law_policy_document.clone())?;
            let report = build_pr_review_report(
                &base_archmap,
                &base_archmap_document,
                after_archmap.as_deref(),
                after_archmap_document.as_ref(),
                &path_archmap,
                &path_archmap_documents,
                &delta_archmap,
                &delta_archmap_document,
                &law_policy,
                &law_policy_document,
                &base_archmap_typed,
                after_archmap_typed.as_ref(),
                &path_archmap_typed,
                &law_policy_typed,
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
            emit_raw_artifacts,
            strict_distance,
        }) => {
            let archmap_validation_path = out_dir.join("archmap-validation.json");
            let law_policy_validation_path = out_dir.join("law-policy-validation.json");
            let analysis_summary_path = out_dir.join("archsig-analysis-summary.json");
            let atom_viewer_data_path = out_dir.join("archsig-atom-viewer-data.json");
            let run_manifest_path = out_dir.join("archsig-run-manifest.json");
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
            let analysis_validation = validate_archsig_analysis_packet_report(
                &analysis_packet,
                &analysis_packet_path.display().to_string(),
            );
            let analysis_failed = analysis_validation.summary.result == "fail";
            write_json(Some(analysis_validation_path), &analysis_validation)?;
            let analysis_packet_value = serde_json::to_value(&analysis_packet)?;
            let archmap_validation_value = serde_json::to_value(&archmap_validation)?;
            let law_policy_validation_value = serde_json::to_value(&law_policy_validation)?;
            let analysis_validation_value = serde_json::to_value(&analysis_validation)?;
            let analysis_summary = build_analysis_summary(
                &analysis_packet_value,
                Some(&archmap_validation_value),
                Some(&law_policy_validation_value),
                Some(&analysis_validation_value),
            );
            write_json(Some(analysis_summary_path.clone()), &analysis_summary)?;
            let atom_viewer_data = build_atom_viewer_data(
                &archmap_document,
                &analysis_packet_value,
                &analysis_summary,
                &archmap,
                &law_policy,
            );
            write_json(Some(atom_viewer_data_path.clone()), &atom_viewer_data)?;

            let analysis_detail_index_path = out_dir.join("archsig-analysis-detail-index.json");
            if emit_raw_artifacts {
                write_analysis_packet_artifacts(
                    Some(analysis_packet_path.clone()),
                    &analysis_packet,
                    Some(analysis_detail_index_path.clone()),
                )?;
                write_json(
                    Some(llm_interpretation_path.clone()),
                    &analysis_packet.llm_interpretation_packet,
                )?;
            }
            let run_manifest = build_analyze_run_manifest(
                &archmap,
                &law_policy,
                emit_raw_artifacts,
                &archmap_validation,
                &law_policy_validation,
                &analysis_validation,
            );
            write_json(Some(run_manifest_path), &run_manifest)?;

            report_analyze_validation_failures(
                out_dir.as_path(),
                &archmap_validation,
                &law_policy_validation,
                &analysis_validation,
            );

            if strict_distance {
                enforce_strict_distance_contract(&law_policy_validation, &analysis_validation)?;
            }

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

fn enforce_strict_distance_contract(
    law_policy_validation: &LawPolicyValidationReportV0,
    analysis_validation: &ArchSigAnalysisPacketValidationReportV0,
) -> Result<(), Box<dyn Error>> {
    let mut violations = Vec::new();
    if law_policy_validation
        .policy
        .part4_distance_profile
        .is_none()
    {
        violations.push(
            "part4DistanceProfile is required for --strict-distance; legacy profile fallback is disabled"
                .to_string(),
        );
    }
    if law_policy_validation.summary.result != "pass" {
        violations.push(format!(
            "LawPolicy validation must pass for --strict-distance (result={}, failed={}, warnings={})",
            law_policy_validation.summary.result,
            law_policy_validation.summary.failed_check_count,
            law_policy_validation.summary.warning_check_count
        ));
    }
    if analysis_validation.summary.result != "pass" {
        violations.push(format!(
            "analysis packet validation must pass for --strict-distance (result={}, failed={}, warnings={}, proxyRegressionChecks={})",
            analysis_validation.summary.result,
            analysis_validation.summary.failed_check_count,
            analysis_validation.summary.warning_check_count,
            analysis_validation.summary.proxy_regression_check_count
        ));
    }
    if analysis_validation.summary.proxy_regression_check_count == 0 {
        violations
            .push("analysis packet validation did not run proxy-regression guardrails".to_string());
    }

    if violations.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "--strict-distance rejected incomplete Part IV distance measurement contract: {}",
            violations.join("; ")
        )
        .into())
    }
}

const COMPACT_REF_ARRAY_THRESHOLD: usize = 50;
const COMPACT_REF_SAMPLE_COUNT: usize = 5;

fn write_analysis_packet_artifacts(
    out: Option<PathBuf>,
    packet: &archsig::ArchSigAnalysisPacketV0,
    detail_out: Option<PathBuf>,
) -> Result<(), Box<dyn Error>> {
    let mut packet_value = serde_json::to_value(packet)?;
    let detail_path = match (&out, detail_out) {
        (_, Some(path)) => Some(path),
        (Some(path), None) => Some(default_detail_index_path(path)),
        (None, None) => None,
    };
    let detail_ref_base = detail_path
        .as_ref()
        .map(|path| path.display().to_string())
        .unwrap_or_else(|| "detail-index-not-written".to_string());
    let mut compact = CompactRefContext::new(detail_ref_base);
    let mut json_pointer = Vec::new();
    compact_ref_arrays(&mut packet_value, &mut json_pointer, &mut compact);
    attach_detail_index_ref(&mut packet_value, &compact);

    if let Some(path) = detail_path {
        write_json_minified(Some(path), &compact.detail_index_value())?;
    }
    write_json_minified(out, &packet_value)?;
    Ok(())
}

fn build_analyze_run_manifest(
    archmap: &Path,
    law_policy: &Path,
    emit_raw_artifacts: bool,
    archmap_validation: &ArchMapValidationReportV0,
    law_policy_validation: &LawPolicyValidationReportV0,
    analysis_validation: &ArchSigAnalysisPacketValidationReportV0,
) -> ArchSigRunManifestV0 {
    let mut generated_artifacts = vec![
        "archmap-validation.json",
        "law-policy-validation.json",
        "archsig-analysis-validation.json",
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
    ];
    let mut omitted_artifacts = Vec::new();
    if emit_raw_artifacts {
        generated_artifacts.extend([
            "archsig-analysis-packet.json",
            "archsig-analysis-detail-index.json",
            "llm-interpretation-packet.json",
        ]);
    } else {
        omitted_artifacts.extend([
            "archsig-analysis-packet.json",
            "archsig-analysis-detail-index.json",
            "llm-interpretation-packet.json",
        ]);
    }

    ArchSigRunManifestV0 {
        schema_version: ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION.to_string(),
        command_name: "analyze".to_string(),
        archmap_input_path: archmap.display().to_string(),
        law_policy_input_path: law_policy.display().to_string(),
        output_mode: if emit_raw_artifacts {
            "summary-viewer-manifest-with-raw-artifacts"
        } else {
            "summary-viewer-manifest"
        }
        .to_string(),
        raw_artifact_retention: if emit_raw_artifacts { "full" } else { "omitted" }.to_string(),
        generated_artifacts: generated_artifacts.into_iter().map(str::to_string).collect(),
        omitted_artifacts: omitted_artifacts.into_iter().map(str::to_string).collect(),
        summary_path: "archsig-analysis-summary.json".to_string(),
        atom_viewer_data_path: "archsig-atom-viewer-data.json".to_string(),
        validation_reports: ArchSigRunManifestValidationReportPathsV0 {
            archmap: "archmap-validation.json".to_string(),
            law_policy: "law-policy-validation.json".to_string(),
            analysis: "archsig-analysis-validation.json".to_string(),
        },
        raw_artifact_paths: emit_raw_artifacts.then(|| ArchSigRunManifestRawArtifactPathsV0 {
            analysis_packet: "archsig-analysis-packet.json".to_string(),
            analysis_detail_index: "archsig-analysis-detail-index.json".to_string(),
            llm_interpretation_packet: "llm-interpretation-packet.json".to_string(),
        }),
        validation_result_summary: ArchSigRunManifestValidationResultSummaryV0 {
            archmap: ArchSigArtifactValidationResultV0 {
                result: archmap_validation.summary.result.clone(),
                failed_check_count: archmap_validation.summary.failed_check_count,
                warning_check_count: archmap_validation.summary.warning_check_count,
            },
            law_policy: ArchSigArtifactValidationResultV0 {
                result: law_policy_validation.summary.result.clone(),
                failed_check_count: law_policy_validation.summary.failed_check_count,
                warning_check_count: law_policy_validation.summary.warning_check_count,
            },
            analysis: ArchSigArtifactValidationResultV0 {
                result: analysis_validation.summary.result.clone(),
                failed_check_count: analysis_validation.summary.failed_check_count,
                warning_check_count: analysis_validation.summary.warning_check_count,
            },
        },
        non_conclusions: vec![
            "run manifest records generated and omitted artifacts for this ArchSig analyze run"
                .to_string(),
            "omitted raw artifacts can be regenerated by rerunning analyze with --emit-raw-artifacts"
                .to_string(),
            "manifest paths are artifact navigation aids, not source completeness proof".to_string(),
        ],
    }
}

fn build_atom_viewer_data(
    archmap: &ArchMapDocumentV0,
    packet: &serde_json::Value,
    summary: &serde_json::Value,
    archmap_path: &Path,
    law_policy_path: &Path,
) -> ArchSigAtomViewerDataV0 {
    const ATOM_NODE_LIMIT: usize = 20_000;
    const MOLECULE_GROUP_LIMIT: usize = 120;
    const EDGE_LIMIT: usize = 30_000;
    const OVERLAY_LIMIT: usize = 80;
    const LABEL_LIMIT: usize = 3;
    const SOURCE_REF_SAMPLE_LIMIT: usize = 3;

    let mut atom_molecule_ref_counts: BTreeMap<&str, usize> = BTreeMap::new();
    for molecule in &archmap.molecule_observations {
        for atom_ref in &molecule.atom_observation_refs {
            *atom_molecule_ref_counts
                .entry(atom_ref.as_str())
                .or_default() += 1;
        }
    }
    let atom_nodes = archmap
        .atom_observations
        .iter()
        .map(|atom| {
            (
                atom_priority_score(
                    atom,
                    atom_molecule_ref_counts
                        .get(atom.atom_observation_id.as_str())
                        .copied()
                        .unwrap_or_default(),
                ),
                atom,
            )
        })
        .collect::<Vec<_>>();
    let mut atom_candidates = atom_nodes;
    atom_candidates.sort_by(|(left_score, left), (right_score, right)| {
        right_score
            .cmp(left_score)
            .then_with(|| left.atom_observation_id.cmp(&right.atom_observation_id))
    });
    let selected_atom_ids = atom_candidates
        .iter()
        .take(ATOM_NODE_LIMIT)
        .map(|(_, atom)| atom.atom_observation_id.as_str())
        .collect::<BTreeSet<_>>();
    let atom_nodes = atom_candidates
        .into_iter()
        .take(ATOM_NODE_LIMIT)
        .map(|(priority_score, atom)| {
            let molecule_ref_count = atom_molecule_ref_counts
                .get(atom.atom_observation_id.as_str())
                .copied()
                .unwrap_or_default();
            ArchSigAtomViewerAtomNodeV0 {
                node_id: atom.atom_observation_id.clone(),
                atom_family: atom.atom_family.clone(),
                subject_ref: atom.subject_ref.clone(),
                predicate: atom.predicate.clone(),
                observation_status: atom.observation_status.clone(),
                confidence: atom.confidence.clone(),
                object_ref_count: atom.object_refs.len(),
                source_ref_count: atom.source_refs.len(),
                source_ref_samples: source_ref_samples(&atom.source_refs, SOURCE_REF_SAMPLE_LIMIT),
                labels: atom_labels(atom, LABEL_LIMIT),
                projection_refs: atom.projection_refs.clone(),
                selection_reason: format!(
                    "topNPriority: status={} confidence={} sourceRefs={} moleculeRefs={}",
                    atom.observation_status,
                    atom.confidence,
                    atom.source_refs.len(),
                    molecule_ref_count
                ),
                priority_score,
                visual: ArchSigAtomViewerVisualV0 {
                    kind: "atom".to_string(),
                    color_by: Some("observationStatus".to_string()),
                    size_by: Some("sourceRefCount".to_string()),
                    hull_by: None,
                },
            }
        })
        .collect::<Vec<_>>();

    let molecule_groups = archmap
        .molecule_observations
        .iter()
        .map(|molecule| (molecule_priority_score(molecule), molecule))
        .collect::<Vec<_>>();
    let mut molecule_groups = molecule_groups;
    molecule_groups.sort_by(|(left_score, left), (right_score, right)| {
        right_score.cmp(left_score).then_with(|| {
            left.molecule_observation_id
                .cmp(&right.molecule_observation_id)
        })
    });
    let molecule_groups = molecule_groups
        .into_iter()
        .take(MOLECULE_GROUP_LIMIT)
        .map(|(priority_score, molecule)| {
            let selected_refs = molecule
                .atom_observation_refs
                .iter()
                .filter(|atom_ref| selected_atom_ids.contains(atom_ref.as_str()))
                .cloned()
                .collect::<Vec<_>>();
            ArchSigAtomViewerMoleculeGroupV0 {
                group_id: molecule.molecule_observation_id.clone(),
                molecule_family: molecule.molecule_family.clone(),
                role_name: molecule.role_name.clone(),
                atom_observation_refs: selected_refs.clone(),
                observation_status: molecule.observation_status.clone(),
                confidence: molecule.confidence.clone(),
                source_ref_count: molecule.source_refs.len(),
                source_ref_samples: source_ref_samples(
                    &molecule.source_refs,
                    SOURCE_REF_SAMPLE_LIMIT,
                ),
                labels: molecule_labels(molecule, LABEL_LIMIT),
                omitted_atom_observation_ref_count: molecule
                    .atom_observation_refs
                    .len()
                    .saturating_sub(selected_refs.len()),
                selection_reason: format!(
                    "topNPriority: status={} confidence={} sourceRefs={} atomRefs={}",
                    molecule.observation_status,
                    molecule.confidence,
                    molecule.source_refs.len(),
                    molecule.atom_observation_refs.len()
                ),
                priority_score,
                visual: ArchSigAtomViewerVisualV0 {
                    kind: "moleculeGroup".to_string(),
                    color_by: None,
                    size_by: None,
                    hull_by: Some("atomObservationRefs".to_string()),
                },
            }
        })
        .collect::<Vec<_>>();

    let mut atom_edges = Vec::new();
    let mut omitted_edge_count = 0usize;
    for molecule in &molecule_groups {
        for atom_ref in &molecule.atom_observation_refs {
            if atom_edges.len() >= EDGE_LIMIT {
                omitted_edge_count += 1;
                continue;
            }
            atom_edges.push(ArchSigAtomViewerEdgeV0 {
                edge_id: format!("edge:{}:{}", molecule.group_id, atom_ref),
                source_node_ref: molecule.group_id.clone(),
                target_node_ref: atom_ref.clone(),
                edge_kind: "moleculeContainsAtom".to_string(),
                relation_ref: Some(molecule.group_id.clone()),
                visual: ArchSigAtomViewerVisualV0 {
                    kind: "moleculeAtomEdge".to_string(),
                    color_by: Some("edgeKind".to_string()),
                    size_by: None,
                    hull_by: None,
                },
            });
        }
    }

    let signature_axes = array_field_with_limit(packet, "signatureAxes", Some(OVERLAY_LIMIT));
    let obstruction_circuits =
        array_field_with_limit(packet, "obstructionCircuits", Some(OVERLAY_LIMIT));
    let signature_axis_omissions = omitted_array_count(packet, "signatureAxes", OVERLAY_LIMIT);
    let obstruction_circuit_omissions =
        omitted_array_count(packet, "obstructionCircuits", OVERLAY_LIMIT);
    let overlays = serde_json::json!({
        "signatureAxes": signature_axes,
        "obstructionCircuits": obstruction_circuits,
        "coverageGaps": json_field(summary, "coverageGapSummary"),
        "dominantFindings": json_field(summary, "dominantFindings"),
        "actionQueue": json_field(summary, "actionQueue"),
        "omittedOverlayCounts": {
            "signatureAxes": signature_axis_omissions,
            "obstructionCircuits": obstruction_circuit_omissions
        },
        "focusFilterDefaults": {
            "families": ["obstructionCircuits", "coverageGaps", "repairFocus", "moleculeGroups"],
            "policy": "viewer UI may filter this bounded projection without loading raw packet detail"
        }
    });
    let aat_geometry_overlays = build_aat_geometry_overlays(packet, OVERLAY_LIMIT);
    let report_pane = serde_json::json!({
        "overview": {
            "mapId": &archmap.map_id,
            "architectureId": &archmap.architecture_id,
            "analysisId": json_field(packet, "analysisId"),
            "summaryVerdict": json_field(summary, "verdict"),
            "validation": json_field(summary, "validation"),
            "measurementStatusSummary": json_field(summary, "measurementStatusSummary")
        },
        "distanceDiagnosis": json_field(summary, "distanceDiagnosis"),
        "topFindings": json_field(summary, "dominantFindings"),
        "actionQueue": json_field(summary, "actionQueue"),
        "coverageAndBoundaries": {
            "coverageGaps": json_field(summary, "coverageGapSummary"),
            "measurementBasis": json_field(summary, "measurementBasis"),
            "metadata": json_field(summary, "metadata")
        },
        "artifacts": {
            "summary": "archsig-analysis-summary.json",
            "manifest": "archsig-run-manifest.json",
            "rawArtifacts": "see archsig-run-manifest.json rawArtifactRetention"
        }
    });

    ArchSigAtomViewerDataV0 {
        schema_version: ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION.to_string(),
        data_kind: "bounded-atom-viewer-projection".to_string(),
        source_artifact_refs: ArchSigAtomViewerSourceArtifactRefsV0 {
            archmap: archmap_path.display().to_string(),
            law_policy: law_policy_path.display().to_string(),
            summary: "archsig-analysis-summary.json".to_string(),
            manifest: "archsig-run-manifest.json".to_string(),
        },
        layout_settings: ArchSigAtomViewerLayoutSettingsV0 {
            layout_kind: "aat-bounded-force-3d".to_string(),
            node_limit: ATOM_NODE_LIMIT,
            molecule_group_limit: MOLECULE_GROUP_LIMIT,
            edge_limit: EDGE_LIMIT,
            overlay_limit: OVERLAY_LIMIT,
            label_limit: LABEL_LIMIT,
            source_ref_sample_limit: SOURCE_REF_SAMPLE_LIMIT,
            distance_boundary:
                "3D distance is a visual projection, not an AAT theorem metric".to_string(),
        },
        atom_nodes,
        molecule_groups,
        atom_edges,
        law_axis_overlays: overlays["signatureAxes"].clone(),
        analysis_overlays: overlays,
        aat_geometry_overlays,
        report_pane,
        omitted_detail_counts: ArchSigAtomViewerOmittedDetailCountsV0 {
            atom_nodes: archmap.atom_observations.len().saturating_sub(ATOM_NODE_LIMIT),
            molecule_groups: archmap
                .molecule_observations
                .len()
                .saturating_sub(MOLECULE_GROUP_LIMIT),
            atom_edges: omitted_edge_count,
            source_refs: omitted_source_ref_count(archmap, SOURCE_REF_SAMPLE_LIMIT),
            labels: omitted_label_count(archmap, LABEL_LIMIT),
            overlay_items: signature_axis_omissions + obstruction_circuit_omissions,
            raw_packet_detail: "raw packet is not embedded in viewer data".to_string(),
            omitted_reasons: vec![
                "atom nodes are selected by deterministic top-N priority over observation status, confidence, source refs, object refs, projection refs, and molecule refs".to_string(),
                "molecule groups are selected by deterministic top-N priority over observation status, confidence, source refs, and atom refs".to_string(),
                "source refs and labels are represented by count plus bounded samples".to_string(),
                "diagnostic distance readings are bounded projections; full evaluator rows remain in optional raw artifacts".to_string(),
                "raw packet detail is intentionally omitted from browser viewer data".to_string(),
            ],
        },
        truncation_policy: ArchSigAtomViewerTruncationPolicyV0 {
            atom_nodes: format!("top {ATOM_NODE_LIMIT} ArchMap atom observations by viewer priority"),
            molecule_groups: format!(
                "top {MOLECULE_GROUP_LIMIT} ArchMap molecule observations by viewer priority"
            ),
            overlays: format!("top {OVERLAY_LIMIT} items per selected overlay family"),
            future_work:
                "Viewer UI can add focus filters over this bounded projection without reading raw packet detail"
                    .to_string(),
        },
        non_conclusions: vec![
            "viewer data is a bounded visual projection, not a replacement for the analysis packet"
                .to_string(),
            "3D layout distance is not a theorem metric, semantic equivalence, or causal relation"
                .to_string(),
            "raw packet detail is intentionally omitted unless analyze is rerun with --emit-raw-artifacts"
                .to_string(),
        ],
    }
}

fn source_ref_samples(
    refs: &[archsig::ArchMapSourceRef],
    limit: usize,
) -> Vec<archsig::ArchMapSourceRef> {
    refs.iter().take(limit).cloned().collect()
}

fn atom_priority_score(atom: &archsig::ArchMapAtomObservationV0, molecule_ref_count: usize) -> i64 {
    status_score(&atom.observation_status)
        + confidence_score(&atom.confidence)
        + (atom.source_refs.len() as i64 * 20)
        + (atom.object_refs.len() as i64 * 10)
        + (atom.projection_refs.len() as i64 * 10)
        + (molecule_ref_count as i64 * 50)
}

fn molecule_priority_score(molecule: &archsig::ArchMapMoleculeObservationV0) -> i64 {
    status_score(&molecule.observation_status)
        + confidence_score(&molecule.confidence)
        + (molecule.source_refs.len() as i64 * 20)
        + (molecule.atom_observation_refs.len() as i64 * 15)
}

fn status_score(status: &str) -> i64 {
    match status {
        "observed" => 1_000,
        "inferred" => 500,
        "partial" => 250,
        _ => 0,
    }
}

fn confidence_score(confidence: &str) -> i64 {
    match confidence {
        "high" => 300,
        "medium" => 150,
        "low" => 25,
        _ => 0,
    }
}

fn atom_labels(atom: &archsig::ArchMapAtomObservationV0, limit: usize) -> Vec<String> {
    [
        atom.atom_family.as_str(),
        atom.subject_ref.as_str(),
        atom.predicate.as_str(),
    ]
    .into_iter()
    .take(limit)
    .map(str::to_string)
    .collect()
}

fn molecule_labels(molecule: &archsig::ArchMapMoleculeObservationV0, limit: usize) -> Vec<String> {
    [
        molecule.molecule_family.as_str(),
        molecule.role_name.as_str(),
        molecule.observation_status.as_str(),
    ]
    .into_iter()
    .take(limit)
    .map(str::to_string)
    .collect()
}

fn omitted_array_count(value: &serde_json::Value, field: &str, limit: usize) -> usize {
    value
        .get(field)
        .and_then(|items| items.as_array())
        .map(|items| items.len().saturating_sub(limit))
        .unwrap_or_default()
}

fn build_aat_geometry_overlays(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    const GEOMETRY_ATOM_REF_SAMPLE_LIMIT: usize = 5000;
    let spectrum_report = packet
        .get("architectureSpectrumReport")
        .map(|report| compact_geometry_report(report, limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT))
        .unwrap_or_else(|| serde_json::Value::Array(Vec::new()));
    let diagnostic_distance_readings = serde_json::json!({
        "atomDistances": compact_geometry_array(packet, "atomDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "configurationDistances": compact_geometry_array(packet, "configurationDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "signatureDistances": compact_geometry_array(packet, "signatureDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "operationDistances": compact_geometry_array(packet, "operationDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "curvatureMassDistances": compact_geometry_array(packet, "curvatureMassReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "homotopyDistances": compact_geometry_array(packet, "homotopyDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "representationMetrics": compact_geometry_array(packet, "representationMetricReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT)
    });
    let omitted_distance_counts = serde_json::json!({
        "atomDistances": omitted_array_count(packet, "atomDistanceReadings", limit),
        "configurationDistances": omitted_array_count(packet, "configurationDistanceReadings", limit),
        "signatureDistances": omitted_array_count(packet, "signatureDistanceReadings", limit),
        "operationDistances": omitted_array_count(packet, "operationDistanceReadings", limit),
        "curvatureMassDistances": omitted_array_count(packet, "curvatureMassReadings", limit),
        "homotopyDistances": omitted_array_count(packet, "homotopyDistanceReadings", limit),
        "representationMetrics": omitted_array_count(packet, "representationMetricReadings", limit)
    });
    serde_json::json!({
        "schemaVersion": "archsig-aat-geometry-overlays-v0",
        "projectionBoundary": "bounded projection of computed ArchSig AAT geometry readings; not a theorem metric and not a raw packet copy",
        "curvatureSupports": compact_geometry_array(packet, "curvatureSupportReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "curvatureTransfers": compact_geometry_array(packet, "curvatureTransferReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedAtomShapes": compact_geometry_array(packet, "generatedAtomShapes", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedMolecules": compact_geometry_array(packet, "generatedMolecules", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedLawInputs": compact_geometry_array(packet, "generatedLawInputs", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedObstructions": compact_geometry_array(packet, "generatedObstructions", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedRepairTargets": compact_geometry_array(packet, "generatedRepairTargets", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "diagnosticDistanceBoundary": "diagnostic distances come from Part IV evaluator readings; viewerDistanceInputs are visual layout support and must not be read as diagnostic metrics",
        "diagnosticDistanceReadings": diagnostic_distance_readings,
        "viewerDistanceInputs": compact_viewer_distance_inputs(packet, limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "spectrumReport": spectrum_report,
        "pathPairs": compact_geometry_array(packet, "pathPairCandidates", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "loops": compact_geometry_array(packet, "loopCandidates", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "holonomyReadings": compact_geometry_array(packet, "homotopyHolonomyReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "stokesReadings": compact_geometry_array(packet, "stokesStyleReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "homotopyReport": packet
            .get("architectureHomotopyReport")
            .map(|report| compact_geometry_report(report, limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT))
            .unwrap_or_else(|| serde_json::Value::Array(Vec::new())),
        "nonzeroMonodromyWitnesses": compact_geometry_array(packet, "nonzeroMonodromyWitnesses", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "localCurvatureDiagrams": compact_geometry_array(packet, "localCurvatureDiagramReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "pathHomotopyDiagrams": compact_geometry_array(packet, "pathHomotopyDiagramReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "flatnessReading": json_field(packet, "flatnessReading"),
        "omittedGeometryCounts": {
            "curvatureSupports": omitted_array_count(packet, "curvatureSupportReadings", limit),
            "curvatureTransfers": omitted_array_count(packet, "curvatureTransferReadings", limit),
            "generatedAtomShapes": omitted_array_count(packet, "generatedAtomShapes", limit),
            "generatedMolecules": omitted_array_count(packet, "generatedMolecules", limit),
            "generatedLawInputs": omitted_array_count(packet, "generatedLawInputs", limit),
            "generatedObstructions": omitted_array_count(packet, "generatedObstructions", limit),
            "generatedRepairTargets": omitted_array_count(packet, "generatedRepairTargets", limit),
            "diagnosticDistanceReadings": omitted_distance_counts,
            "viewerDistanceInputs": omitted_array_count(packet, "viewerDistanceInputs", limit),
            "pathPairs": omitted_array_count(packet, "pathPairCandidates", limit),
            "loops": omitted_array_count(packet, "loopCandidates", limit),
            "holonomyReadings": omitted_array_count(packet, "homotopyHolonomyReadings", limit),
            "stokesReadings": omitted_array_count(packet, "stokesStyleReadings", limit),
            "nonzeroMonodromyWitnesses": omitted_array_count(packet, "nonzeroMonodromyWitnesses", limit),
            "localCurvatureDiagrams": omitted_array_count(packet, "localCurvatureDiagramReadings", limit),
            "pathHomotopyDiagrams": omitted_array_count(packet, "pathHomotopyDiagramReadings", limit)
        }
    })
}

fn compact_geometry_array(
    value: &serde_json::Value,
    field: &str,
    limit: usize,
    atom_ref_limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(value, field)
            .into_iter()
            .take(limit)
            .map(|item| compact_geometry_item(item, atom_ref_limit))
            .collect(),
    )
}

fn compact_viewer_distance_inputs(
    value: &serde_json::Value,
    limit: usize,
    atom_ref_limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(value, "viewerDistanceInputs")
            .into_iter()
            .take(limit)
            .map(|item| compact_viewer_distance_input(item, atom_ref_limit))
            .collect(),
    )
}

fn compact_viewer_distance_input(
    value: &serde_json::Value,
    atom_ref_limit: usize,
) -> serde_json::Value {
    let mut atom_refs = BTreeSet::new();
    collect_atom_refs(value, &mut atom_refs);
    let sampled_atom_refs = atom_refs
        .iter()
        .take(atom_ref_limit)
        .cloned()
        .collect::<Vec<_>>();
    let atom_shape_refs = string_array(value, "atomShapeRefs")
        .into_iter()
        .take(atom_ref_limit)
        .collect::<Vec<_>>();
    let coordinate_components = string_array(value, "coordinateComponents")
        .into_iter()
        .take(24)
        .collect::<Vec<_>>();
    serde_json::json!({
        "id": json_field(value, "distanceInputId"),
        "kind": json_field(value, "distanceKind"),
        "status": compact_first_string_field(value, &["status", "measurementStatus"]),
        "value": json_field(value, "distanceValue"),
        "distanceInputId": json_field(value, "distanceInputId"),
        "distanceKind": json_field(value, "distanceKind"),
        "sourceRef": json_field(value, "sourceRef"),
        "targetRef": json_field(value, "targetRef"),
        "generatedMoleculeRef": json_field(value, "generatedMoleculeRef"),
        "atomShapeRefs": atom_shape_refs,
        "coordinateComponents": coordinate_components,
        "distanceValue": json_field(value, "distanceValue"),
        "evidenceBoundary": json_field(value, "evidenceBoundary"),
        "atomRefs": sampled_atom_refs,
        "atomRefCount": atom_refs.len(),
        "omittedAtomRefs": atom_refs.len().saturating_sub(atom_ref_limit)
    })
}

fn compact_geometry_report(
    value: &serde_json::Value,
    limit: usize,
    atom_ref_limit: usize,
) -> serde_json::Value {
    if value.is_null() {
        return serde_json::Value::Array(Vec::new());
    }
    if let Some(items) = value.as_array() {
        return serde_json::Value::Array(
            items
                .iter()
                .take(limit)
                .map(|item| compact_geometry_item(item, atom_ref_limit))
                .collect(),
        );
    }
    let mut compact_items = Vec::new();
    collect_compact_geometry_report_items(value, limit, atom_ref_limit, &mut compact_items);
    serde_json::Value::Array(compact_items)
}

fn collect_compact_geometry_report_items(
    value: &serde_json::Value,
    limit: usize,
    atom_ref_limit: usize,
    out: &mut Vec<serde_json::Value>,
) {
    if out.len() >= limit {
        return;
    }
    match value {
        serde_json::Value::Array(items) => {
            for item in items {
                if out.len() >= limit {
                    return;
                }
                if item.is_object() {
                    let compact = compact_geometry_item(item, atom_ref_limit);
                    if compact
                        .get("atomRefCount")
                        .and_then(serde_json::Value::as_u64)
                        .unwrap_or_default()
                        > 0
                    {
                        out.push(compact);
                    }
                }
            }
        }
        serde_json::Value::Object(map) => {
            for item in map.values() {
                collect_compact_geometry_report_items(item, limit, atom_ref_limit, out);
            }
        }
        _ => {}
    }
}

fn compact_geometry_item(value: &serde_json::Value, atom_ref_limit: usize) -> serde_json::Value {
    let mut atom_refs = BTreeSet::new();
    collect_atom_refs(value, &mut atom_refs);
    let sampled_atom_refs = atom_refs
        .iter()
        .take(atom_ref_limit)
        .cloned()
        .collect::<Vec<_>>();
    serde_json::json!({
        "id": compact_first_string_field(value, &[
            "ref",
            "readingRef",
            "readingId",
            "obstructionRef",
            "obstructionCircuitId",
            "pathRef",
            "loopRef",
            "axisRef"
        ]),
        "kind": compact_first_string_field(value, &[
            "kind",
            "readingKind",
            "curvatureKind",
            "holonomyKind",
            "status",
            "curvatureStatus"
        ]),
        "status": compact_first_string_field(value, &[
            "status",
            "coverageStatus",
            "curvatureStatus",
            "holonomyStatus",
            "flatnessStatus"
        ]),
        "value": compact_first_number_field(value, &[
            "curvatureValue",
            "value",
            "score",
            "defectValue",
            "cycleWeight",
            "coverageGapCount",
            "refCount",
            "sourceRefCount"
        ]),
        "atomRefs": sampled_atom_refs,
        "atomRefCount": atom_refs.len(),
        "omittedAtomRefs": atom_refs.len().saturating_sub(atom_ref_limit)
    })
}

fn collect_atom_refs(value: &serde_json::Value, refs: &mut BTreeSet<String>) {
    match value {
        serde_json::Value::String(text) => {
            if text.starts_with("atom:") {
                refs.insert(text.clone());
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                collect_atom_refs(item, refs);
            }
        }
        serde_json::Value::Object(map) => {
            for item in map.values() {
                collect_atom_refs(item, refs);
            }
        }
        _ => {}
    }
}

fn compact_first_string_field(value: &serde_json::Value, keys: &[&str]) -> serde_json::Value {
    keys.iter()
        .find_map(|key| value.get(*key).and_then(serde_json::Value::as_str))
        .map(|text| serde_json::Value::String(text.to_string()))
        .unwrap_or(serde_json::Value::Null)
}

fn compact_first_number_field(value: &serde_json::Value, keys: &[&str]) -> serde_json::Value {
    keys.iter()
        .find_map(|key| value.get(*key).and_then(serde_json::Value::as_f64))
        .and_then(serde_json::Number::from_f64)
        .map(serde_json::Value::Number)
        .unwrap_or(serde_json::Value::Null)
}

fn omitted_source_ref_count(archmap: &ArchMapDocumentV0, sample_limit: usize) -> usize {
    let atom_omissions = archmap
        .atom_observations
        .iter()
        .map(|atom| atom.source_refs.len().saturating_sub(sample_limit))
        .sum::<usize>();
    let molecule_omissions = archmap
        .molecule_observations
        .iter()
        .map(|molecule| molecule.source_refs.len().saturating_sub(sample_limit))
        .sum::<usize>();
    atom_omissions + molecule_omissions
}

fn omitted_label_count(archmap: &ArchMapDocumentV0, label_limit: usize) -> usize {
    let atom_label_count = archmap.atom_observations.len() * 3;
    let molecule_label_count = archmap.molecule_observations.len() * 3;
    atom_label_count.saturating_sub(archmap.atom_observations.len() * label_limit)
        + molecule_label_count.saturating_sub(archmap.molecule_observations.len() * label_limit)
}

fn default_detail_index_path(packet_path: &Path) -> PathBuf {
    let stem = packet_path
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("archsig-analysis-packet");
    let file_name = format!("{stem}-detail-index.json");
    packet_path.with_file_name(file_name)
}

struct CompactRefContext {
    detail_ref_base: String,
    next_ref_set: usize,
    ref_set_by_hash: BTreeMap<u64, Vec<String>>,
    ref_sets: BTreeMap<String, CompactRefSet>,
}

struct CompactRefSet {
    item_count: usize,
    sample_refs: Vec<String>,
    refs: Vec<String>,
    json_pointers: Vec<String>,
}

impl CompactRefContext {
    fn new(detail_ref_base: String) -> Self {
        Self {
            detail_ref_base,
            next_ref_set: 1,
            ref_set_by_hash: BTreeMap::new(),
            ref_sets: BTreeMap::new(),
        }
    }

    fn intern_ref_set(
        &mut self,
        refs: Vec<String>,
        json_pointer: String,
    ) -> (String, usize, Vec<String>) {
        let hash = hash_refs(&refs);
        let ref_set_id = self
            .ref_set_by_hash
            .get(&hash)
            .and_then(|candidate_ids| {
                candidate_ids.iter().find_map(|candidate_id| {
                    self.ref_sets
                        .get(candidate_id)
                        .filter(|candidate| candidate.refs == refs)
                        .map(|_| candidate_id.clone())
                })
            })
            .unwrap_or_else(|| {
                let id = format!("refset:{:06}", self.next_ref_set);
                self.next_ref_set += 1;
                self.ref_set_by_hash
                    .entry(hash)
                    .or_default()
                    .push(id.clone());
                self.ref_sets.insert(
                    id.clone(),
                    CompactRefSet {
                        item_count: refs.len(),
                        sample_refs: refs
                            .iter()
                            .take(COMPACT_REF_SAMPLE_COUNT)
                            .cloned()
                            .collect(),
                        refs,
                        json_pointers: Vec::new(),
                    },
                );
                id
            });
        let ref_set = self
            .ref_sets
            .get_mut(&ref_set_id)
            .expect("interned ref set must exist");
        ref_set.json_pointers.push(json_pointer);
        (ref_set_id, ref_set.item_count, ref_set.sample_refs.clone())
    }

    fn detail_ref(&self, ref_set_id: &str) -> String {
        format!("{}#{}", self.detail_ref_base, ref_set_id)
    }

    fn detail_index_value(&self) -> serde_json::Value {
        let mut dictionary_by_ref = BTreeMap::<String, usize>::new();
        let mut ref_dictionary = Vec::<String>::new();
        for ref_set in self.ref_sets.values() {
            for ref_value in &ref_set.refs {
                if !dictionary_by_ref.contains_key(ref_value) {
                    let index = ref_dictionary.len();
                    dictionary_by_ref.insert(ref_value.clone(), index);
                    ref_dictionary.push(ref_value.clone());
                }
            }
        }
        let ref_sets = self
            .ref_sets
            .iter()
            .map(|(ref_set_id, ref_set)| {
                let ref_indexes = ref_set
                    .refs
                    .iter()
                    .filter_map(|ref_value| dictionary_by_ref.get(ref_value).copied())
                    .collect::<Vec<_>>();
                serde_json::json!({
                    "refSetId": ref_set_id,
                    "refCount": ref_set.item_count,
                    "jsonPointers": ref_set.json_pointers,
                    "refIndexes": ref_indexes,
                })
            })
            .collect::<Vec<_>>();
        serde_json::json!({
            "schemaVersion": "archsig-analysis-detail-index-v0",
            "indexKind": "deduplicated-string-ref-set-dictionary",
            "compactThreshold": COMPACT_REF_ARRAY_THRESHOLD,
            "refSetCount": self.ref_sets.len(),
            "refDictionary": ref_dictionary,
            "refSets": ref_sets,
            "nonConclusions": [
                "detail index preserves full string reference sets omitted from the compact analysis packet",
                "refSets[].refIndexes indexes into refDictionary and preserves ref order inside each set",
                "detail refs are evidence navigation aids, not theorem evidence or source completeness proof"
            ]
        })
    }
}

fn compact_ref_arrays(
    value: &mut serde_json::Value,
    json_pointer: &mut Vec<String>,
    compact: &mut CompactRefContext,
) {
    match value {
        serde_json::Value::Array(items)
            if items.len() > COMPACT_REF_ARRAY_THRESHOLD
                && items.iter().all(serde_json::Value::is_string) =>
        {
            let refs = items
                .iter()
                .filter_map(serde_json::Value::as_str)
                .map(str::to_string)
                .collect::<Vec<_>>();
            let pointer = json_pointer_string(json_pointer);
            let (ref_set_id, ref_count, sample_refs) = compact.intern_ref_set(refs, pointer);
            *value = serde_json::json!({
                "schemaVersion": "archsig-detail-ref-v0",
                "refSetId": ref_set_id,
                "refCount": ref_count,
                "sampleRefs": sample_refs,
                "detailRef": compact.detail_ref(&ref_set_id),
            });
        }
        serde_json::Value::Array(items) => {
            for (index, item) in items.iter_mut().enumerate() {
                json_pointer.push(index.to_string());
                compact_ref_arrays(item, json_pointer, compact);
                json_pointer.pop();
            }
        }
        serde_json::Value::Object(map) => {
            for (key, child) in map.iter_mut() {
                json_pointer.push(json_pointer_escape(key));
                compact_ref_arrays(child, json_pointer, compact);
                json_pointer.pop();
            }
        }
        _ => {}
    }
}

fn hash_refs(refs: &[String]) -> u64 {
    let mut hasher = DefaultHasher::new();
    refs.hash(&mut hasher);
    hasher.finish()
}

fn json_pointer_string(segments: &[String]) -> String {
    if segments.is_empty() {
        String::new()
    } else {
        format!("/{}", segments.join("/"))
    }
}

fn attach_detail_index_ref(packet_value: &mut serde_json::Value, compact: &CompactRefContext) {
    if let serde_json::Value::Object(map) = packet_value {
        map.insert(
            "detailIndexRef".to_string(),
            serde_json::json!({
                "schemaVersion": "archsig-analysis-detail-index-ref-v0",
                "artifactKind": "archsig-analysis-detail-index",
                "path": compact.detail_ref_base,
                "refSetCount": compact.ref_sets.len(),
                "compactThreshold": COMPACT_REF_ARRAY_THRESHOLD,
                "detailRefFormat": "<path>#<refSetId>"
            }),
        );
    }
}

fn json_pointer_escape(key: &str) -> String {
    key.replace('~', "~0").replace('/', "~1")
}

fn write_json_minified<T: serde::Serialize>(
    out: Option<PathBuf>,
    value: &T,
) -> Result<(), Box<dyn Error>> {
    match out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent)?;
                }
            }
            let mut file = File::create(path)?;
            serde_json::to_writer(&mut file, value)?;
            writeln!(file)?;
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            serde_json::to_writer(&mut handle, value)?;
            writeln!(handle)?;
        }
    }
    Ok(())
}

fn read_json<T: serde::de::DeserializeOwned>(path: &PathBuf) -> Result<T, Box<dyn Error>> {
    Ok(serde_json::from_reader(File::open(path)?)?)
}

fn report_analyze_validation_failures(
    out_dir: &Path,
    archmap_validation: &ArchMapValidationReportV0,
    law_policy_validation: &LawPolicyValidationReportV0,
    analysis_validation: &ArchSigAnalysisPacketValidationReportV0,
) {
    if archmap_validation.summary.result != "fail"
        && law_policy_validation.summary.result != "fail"
        && analysis_validation.summary.result != "fail"
    {
        return;
    }

    eprintln!(
        "archsig analyze produced artifacts in {} but validation failed:",
        out_dir.display()
    );

    if archmap_validation.summary.result == "fail" {
        eprintln!(
            "  archmap-validation.json: fail ({} failed check(s))",
            archmap_validation.summary.failed_check_count
        );
        let archmap_groups = [
            (
                "sourceInventoryChecks",
                archmap_validation.source_inventory_checks.as_slice(),
            ),
            (
                "sourceRefChecks",
                archmap_validation.source_ref_checks.as_slice(),
            ),
            (
                "claimBoundaryChecks",
                archmap_validation.claim_boundary_checks.as_slice(),
            ),
            (
                "semanticCoverageChecks",
                archmap_validation.semantic_coverage_checks.as_slice(),
            ),
            (
                "formalPromotionGuardrailChecks",
                archmap_validation
                    .formal_promotion_guardrail_checks
                    .as_slice(),
            ),
            (
                "atomicObservationChecks",
                archmap_validation.atomic_observation_checks.as_slice(),
            ),
            (
                "responsibilityChecks",
                archmap_validation.responsibility_checks.as_slice(),
            ),
        ];
        for (group, checks) in archmap_groups {
            for check in checks.iter().filter(|check| check.result == "fail") {
                eprintln!(
                    "    - {group}/{}: {}",
                    check.id,
                    check.reason.as_deref().unwrap_or(&check.title)
                );
            }
        }
    }

    if law_policy_validation.summary.result == "fail" {
        eprintln!(
            "  law-policy-validation.json: fail ({} failed check(s))",
            law_policy_validation.summary.failed_check_count
        );
        for check in law_policy_validation
            .checks
            .iter()
            .filter(|check| check.result == "fail")
        {
            eprintln!(
                "    - checks/{}: {}",
                check.id,
                check.reason.as_deref().unwrap_or(&check.title)
            );
        }
    }

    if analysis_validation.summary.result == "fail" {
        eprintln!(
            "  archsig-analysis-validation.json: fail ({} failed check(s))",
            analysis_validation.summary.failed_check_count
        );
        for check in analysis_validation
            .checks
            .iter()
            .filter(|check| check.result == "fail")
        {
            eprintln!(
                "    - checks/{}: {}",
                check.id,
                check.reason.as_deref().unwrap_or(&check.title)
            );
        }
    }
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
                "monodromyFamilyStatus": reading_family_status_summary(packet, "monodromyReadingFamily"),
                "boundaryHolonomyFamilyStatus": reading_family_status_summary(packet, "boundaryHolonomyReadingFamily"),
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
    after_archmap_path: Option<&Path>,
    after_archmap: Option<&serde_json::Value>,
    path_archmap_paths: &[PathBuf],
    path_archmaps: &[serde_json::Value],
    delta_archmap_path: &Path,
    delta_archmap: &serde_json::Value,
    law_policy_path: &Path,
    law_policy: &serde_json::Value,
    base_archmap_typed: &ArchMapDocumentV0,
    after_archmap_typed: Option<&ArchMapDocumentV0>,
    path_archmap_typed: &[ArchMapDocumentV0],
    law_policy_typed: &LawPolicyDocumentV0,
) -> serde_json::Value {
    let changed_refs = string_array(delta_archmap, "changedObservationRefs");
    let matched_observations = changed_archmap_observations(base_archmap, &changed_refs);
    let changed_families = changed_atom_families(base_archmap, &changed_refs);
    let matched_laws = matched_policy_laws(law_policy, &changed_families);
    let matched_axis_refs = matched_policy_axis_refs(&matched_laws);
    let source_targets =
        source_targets_for_changed_refs(base_archmap, delta_archmap, &changed_refs);
    let base_packet = build_archsig_analysis_packet(
        base_archmap_typed,
        law_policy_typed,
        Some(&base_archmap_path.display().to_string()),
        Some(&law_policy_path.display().to_string()),
    );
    let base_packet_value = serde_json::to_value(&base_packet).unwrap_or(serde_json::Value::Null);
    let after_packet_value = after_archmap_typed.map(|after_archmap_typed| {
        let after_path = after_archmap_path
            .map(|path| path.display().to_string())
            .unwrap_or_else(|| "after-archmap".to_string());
        let packet = build_archsig_analysis_packet(
            after_archmap_typed,
            law_policy_typed,
            Some(&after_path),
            Some(&law_policy_path.display().to_string()),
        );
        serde_json::to_value(&packet).unwrap_or(serde_json::Value::Null)
    });
    let path_packet_values = path_archmap_typed
        .iter()
        .enumerate()
        .map(|(index, path_archmap_typed)| {
            let path = path_archmap_paths
                .get(index)
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| format!("path-archmap:{index}"));
            let packet = build_archsig_analysis_packet(
                path_archmap_typed,
                law_policy_typed,
                Some(&path),
                Some(&law_policy_path.display().to_string()),
            );
            serde_json::to_value(&packet).unwrap_or(serde_json::Value::Null)
        })
        .collect::<Vec<_>>();
    let pr_drift_readings = pr_drift_readings(
        base_archmap,
        after_archmap,
        delta_archmap,
        &changed_refs,
        &base_packet_value,
        &path_packet_values,
        after_packet_value.as_ref(),
    );
    let architecture_navigation_report = architecture_navigation_report(&pr_drift_readings);

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
            "afterArchMap": after_archmap.map(|after_archmap| serde_json::json!({
                "path": after_archmap_path
                    .map(|path| path.display().to_string())
                    .unwrap_or_else(|| "after-archmap".to_string()),
                "schemaVersion": schema_string(after_archmap),
                "mapId": json_field(after_archmap, "mapId"),
                "architectureId": json_field(after_archmap, "architectureId")
            })).unwrap_or(serde_json::Value::Null),
            "pathArchMaps": serde_json::Value::Array(path_archmaps.iter().enumerate().map(|(index, path_archmap)| {
                serde_json::json!({
                    "path": path_archmap_paths
                        .get(index)
                        .map(|path| path.display().to_string())
                        .unwrap_or_else(|| format!("path-archmap:{index}")),
                    "schemaVersion": schema_string(path_archmap),
                    "mapId": json_field(path_archmap, "mapId"),
                    "architectureId": json_field(path_archmap, "architectureId")
                })
            }).collect()),
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
        "prDriftReadings": pr_drift_readings,
        "architectureNavigationReport": architecture_navigation_report,
        "evidenceBoundary": "ArchSig PR review reads base/head ArchMap, PR-local ArchMap delta, and LawPolicy as canonical inputs. Raw diff and ArchMapCommit are outside this input surface. Base/head analysis packets are generated internally from those inputs and are not accepted as PR-review input artifacts."
    })
}

fn pr_drift_readings(
    base_archmap: &serde_json::Value,
    after_archmap: Option<&serde_json::Value>,
    delta_archmap: &serde_json::Value,
    changed_refs: &[String],
    base_packet: &serde_json::Value,
    path_packets: &[serde_json::Value],
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let coverage_gaps = pr_coverage_gaps(base_archmap, after_archmap, base_packet, after_packet);
    let endpoint_distance = pr_endpoint_signature_distance(base_packet, after_packet);
    let total_path_movement = pr_total_path_movement(base_packet, path_packets, after_packet);
    let hidden_excursion_status = if !path_packets.is_empty() && after_packet.is_some() {
        "measuredFromSuppliedIntermediateArchMapSnapshots"
    } else if after_packet.is_some() {
        "blockedWithoutIntermediateArchMapPathSnapshots"
    } else {
        "blockedWithoutAfterArchMap"
    };
    let safe_change_budget = pr_safe_change_budget(base_packet, &endpoint_distance, &coverage_gaps);
    let top_moved_axes = pr_top_moved_axes(base_packet, after_packet);
    let top_moved_atoms = pr_top_moved_atoms(base_archmap, after_archmap, changed_refs);
    let review_focus = pr_review_focus(
        delta_archmap,
        &top_moved_axes,
        &top_moved_atoms,
        &coverage_gaps,
    );

    serde_json::Value::Array(vec![serde_json::json!({
        "readingId": format!(
            "pr-drift:{}:{}",
            json_string(base_archmap, "mapId", "base-archmap"),
            after_archmap
                .map(|document| json_string(document, "mapId", "after-archmap"))
                .unwrap_or_else(|| "after-archmap-missing".to_string())
        ),
        "distanceProfileRef": json_field(
            base_packet.get("part4DistanceFoundation")
                .and_then(|foundation| foundation.get("profile"))
                .unwrap_or(&serde_json::Value::Null),
            "profileId"
        ),
        "baseAnalysisRef": json_field(base_packet, "analysisId"),
        "afterAnalysisRef": after_packet
            .map(|packet| json_field(packet, "analysisId"))
            .unwrap_or(serde_json::Value::Null),
        "endpointSignatureDistance": endpoint_distance,
        "totalPathMovement": total_path_movement,
        "hiddenExcursionStatus": hidden_excursion_status,
        "topMovedAtoms": top_moved_atoms,
        "topMovedAxes": top_moved_axes,
        "coverageGaps": coverage_gaps,
        "safeChangeBudget": safe_change_budget,
        "reviewFocus": review_focus,
        "evidenceBoundary": "PR drift is measured from base/head ArchSig packets generated from ArchMap + LawPolicy and localized by ArchMapDelta; it is not raw diff analysis, merge approval, repair safety, or forecast.",
        "nonConclusions": [
            "PR drift is not merge approval",
            "PR drift does not prove automatic repair safety",
            "PR drift does not predict future incidents",
            "coverage gaps limit safe-change budget instead of becoming measured zero"
        ]
    })])
}

fn architecture_navigation_report(pr_drift_readings: &serde_json::Value) -> serde_json::Value {
    let Some(reading) = pr_drift_readings.as_array().and_then(|items| items.first()) else {
        return serde_json::json!({
            "status": "blocked",
            "recommendedReviewFocus": [],
            "safeChangeStatus": "blockedWithoutPrDriftReading"
        });
    };
    serde_json::json!({
        "status": "needsReview",
        "endpointSignatureDistance": json_field(reading, "endpointSignatureDistance"),
        "totalPathMovement": json_field(reading, "totalPathMovement"),
        "hiddenExcursionStatus": json_field(reading, "hiddenExcursionStatus"),
        "safeChangeBudget": json_field(reading, "safeChangeBudget"),
        "topMovedAtoms": array_field_with_limit(reading, "topMovedAtoms", Some(5)),
        "topMovedAxes": array_field_with_limit(reading, "topMovedAxes", Some(5)),
        "recommendedReviewFocus": array_field(reading, "reviewFocus"),
        "evidenceBoundary": "Architecture navigation report ranks source-backed PR drift surfaces; reviewers still inspect the cited source refs and supplied ArchMap evidence."
    })
}

fn pr_endpoint_signature_distance(
    base_packet: &serde_json::Value,
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let Some(after_packet) = after_packet else {
        return pr_distance_value(
            "blocked",
            None,
            "milli-signature-endpoint-distance",
            vec![],
            vec!["afterArchMap:not-supplied".to_string()],
            "endpoint signature distance requires --after-archmap; missing head evidence is blocked, not zero",
        );
    };
    let base_axes = signature_axis_value_map(base_packet);
    let after_axes = signature_axis_value_map(after_packet);
    let axis_refs = base_axes
        .keys()
        .chain(after_axes.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut total = 0_i64;
    let mut provenance_refs = Vec::new();
    let mut basis_refs = Vec::new();
    for axis_ref in axis_refs {
        let before = base_axes.get(&axis_ref).copied().unwrap_or_default();
        let after = after_axes.get(&axis_ref).copied().unwrap_or_default();
        total += (after - before).abs() * 1000;
        provenance_refs.push(axis_ref.clone());
        basis_refs.push(format!("axisDelta:{axis_ref}:{before}->{after}"));
    }
    pr_distance_value(
        "measured",
        Some(total),
        "milli-signature-endpoint-distance",
        provenance_refs,
        basis_refs,
        "endpoint signature distance is the selected-axis L1 delta between internally generated base/head ArchSig packets",
    )
}

fn pr_total_path_movement(
    base_packet: &serde_json::Value,
    path_packets: &[serde_json::Value],
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let Some(after_packet) = after_packet else {
        return pr_distance_value(
            "blocked",
            None,
            "milli-signature-path-movement",
            vec![],
            vec!["afterArchMap:not-supplied".to_string()],
            "total path movement requires --after-archmap; missing head evidence is blocked, not zero",
        );
    };
    let mut packets = Vec::with_capacity(path_packets.len() + 2);
    packets.push(base_packet);
    packets.extend(path_packets.iter());
    packets.push(after_packet);
    let mut total = 0_i64;
    let mut provenance_refs = BTreeSet::new();
    let mut basis_refs = Vec::new();
    for (index, window) in packets.windows(2).enumerate() {
        let before = signature_axis_value_map(window[0]);
        let after = signature_axis_value_map(window[1]);
        let axis_refs = before
            .keys()
            .chain(after.keys())
            .cloned()
            .collect::<BTreeSet<_>>();
        for axis_ref in axis_refs {
            let before_value = before.get(&axis_ref).copied().unwrap_or_default();
            let after_value = after.get(&axis_ref).copied().unwrap_or_default();
            total += (after_value - before_value).abs() * 1000;
            provenance_refs.insert(axis_ref.clone());
            basis_refs.push(format!(
                "pathSegment:{index}:axisDelta:{axis_ref}:{before_value}->{after_value}"
            ));
        }
    }
    let mut value = pr_distance_value(
        "measured",
        Some(total),
        "milli-signature-path-movement",
        provenance_refs.into_iter().collect(),
        basis_refs,
        if path_packets.is_empty() {
            "total path movement is measured as the two-point base/head lower bound; hidden intermediate excursions require supplied ArchMap path snapshots"
        } else {
            "total path movement is the selected-axis sum across supplied base/intermediate/head ArchMap snapshots"
        },
    );
    if let Some(object) = value.as_object_mut() {
        object.insert(
            "pathGranularity".to_string(),
            serde_json::Value::String(if path_packets.is_empty() {
                "twoPointBaseHead".to_string()
            } else {
                "suppliedIntermediateSnapshots".to_string()
            }),
        );
        object.insert(
            "pathSnapshotCount".to_string(),
            serde_json::Value::Number((path_packets.len() as i64).into()),
        );
    }
    value
}

fn pr_safe_change_budget(
    base_packet: &serde_json::Value,
    endpoint_distance: &serde_json::Value,
    coverage_gaps: &serde_json::Value,
) -> serde_json::Value {
    let base_margin = first_signature_distance(base_packet)
        .and_then(|reading| reading.get("safeRegionMargin"))
        .and_then(|margin| margin.get("measuredValue"))
        .and_then(serde_json::Value::as_i64);
    let endpoint = endpoint_distance
        .get("measuredValue")
        .and_then(serde_json::Value::as_i64);
    let has_coverage_gaps = coverage_gaps
        .as_array()
        .is_some_and(|items| !items.is_empty());
    let remaining = match (base_margin, endpoint) {
        (Some(base_margin), Some(endpoint)) => Some((base_margin - endpoint).max(0)),
        _ => None,
    };
    serde_json::json!({
        "status": if has_coverage_gaps {
            "blockedByCoverageGap"
        } else if remaining.is_some() {
            "measured"
        } else {
            "blocked"
        },
        "baseSafeRegionMargin": base_margin,
        "prMovement": endpoint,
        "remainingBudget": remaining,
        "marginUsage": match (base_margin, endpoint) {
            (Some(base_margin), Some(endpoint)) if base_margin > 0 => {
                serde_json::Value::String(format!("{endpoint}/{base_margin}"))
            }
            _ => serde_json::Value::Null
        },
        "coverageGapLimited": has_coverage_gaps,
        "blockerRefs": string_vec_from_array_objects(coverage_gaps, "gapId"),
        "reading": "safe change budget is evaluated against selected Part IV signature margin; coverage gaps block safe-region conclusion instead of being counted as zero risk"
    })
}

fn pr_top_moved_axes(
    base_packet: &serde_json::Value,
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let Some(after_packet) = after_packet else {
        return serde_json::Value::Array(Vec::new());
    };
    let base_axes = signature_axis_object_map(base_packet);
    let after_axes = signature_axis_object_map(after_packet);
    let axis_refs = base_axes
        .keys()
        .chain(after_axes.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut rows = axis_refs
        .into_iter()
        .filter_map(|axis_ref| {
            let before = base_axes
                .get(&axis_ref)
                .and_then(|axis| axis.get("value"))
                .and_then(serde_json::Value::as_i64)
                .unwrap_or_default();
            let after = after_axes
                .get(&axis_ref)
                .and_then(|axis| axis.get("value"))
                .and_then(serde_json::Value::as_i64)
                .unwrap_or_default();
            let delta = after - before;
            if delta == 0 {
                return None;
            }
            let base_axis = base_axes.get(&axis_ref).copied().unwrap_or(&serde_json::Value::Null);
            let after_axis = after_axes
                .get(&axis_ref)
                .copied()
                .unwrap_or(&serde_json::Value::Null);
            Some(serde_json::json!({
                "axisRef": axis_ref,
                "beforeValue": before,
                "afterValue": after,
                "delta": delta,
                "movementMagnitude": delta.abs(),
                "baseCoverageStatus": json_field(base_axis, "coverageStatus"),
                "afterCoverageStatus": json_field(after_axis, "coverageStatus"),
                "sourceRefs": json_string_array(
                    string_vec_from_value(base_axis, "sourceRefs")
                        .into_iter()
                        .chain(string_vec_from_value(after_axis, "sourceRefs"))
                ),
                "blockerRefs": json_string_array(
                    string_vec_from_value(base_axis, "missingEvidence")
                        .into_iter()
                        .chain(string_vec_from_value(after_axis, "missingEvidence"))
                ),
                "evidenceBoundary": "axis movement is read from generated base/head signature axis values under the same LawPolicy"
            }))
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| {
        -row.get("movementMagnitude")
            .and_then(serde_json::Value::as_i64)
            .unwrap_or_default()
    });
    serde_json::Value::Array(rows.into_iter().take(8).collect())
}

fn pr_top_moved_atoms(
    base_archmap: &serde_json::Value,
    after_archmap: Option<&serde_json::Value>,
    changed_refs: &[String],
) -> serde_json::Value {
    let Some(after_archmap) = after_archmap else {
        return serde_json::Value::Array(Vec::new());
    };
    let base_atoms = observation_object_map(base_archmap, "atomObservations", "atomObservationId");
    let after_atoms =
        observation_object_map(after_archmap, "atomObservations", "atomObservationId");
    let changed = changed_refs.iter().cloned().collect::<BTreeSet<_>>();
    let atom_refs = base_atoms
        .keys()
        .chain(after_atoms.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut rows = atom_refs
        .into_iter()
        .filter_map(|atom_ref| {
            let before = base_atoms.get(&atom_ref).copied();
            let after = after_atoms.get(&atom_ref).copied();
            if before.map(observation_movement_fingerprint)
                == after.map(observation_movement_fingerprint)
            {
                return None;
            }
            let movement_kind = match (before, after) {
                (None, Some(_)) => "added",
                (Some(_), None) => "removed",
                (Some(_), Some(_)) => "changed",
                (None, None) => return None,
            };
            let base = before.unwrap_or(&serde_json::Value::Null);
            let head = after.unwrap_or(&serde_json::Value::Null);
            let source_refs = if after.is_some() {
                array_field(head, "sourceRefs")
            } else {
                array_field(base, "sourceRefs")
            };
            let score = match movement_kind {
                "added" | "removed" => 3,
                _ => 1,
            } + i64::from(changed.contains(&atom_ref)) * 2;
            Some(serde_json::json!({
                "atomObservationRef": atom_ref,
                "movementKind": movement_kind,
                "movementScore": score,
                "changedByDelta": changed.contains(&atom_ref),
                "beforeFamily": json_field(base, "atomFamily"),
                "afterFamily": json_field(head, "atomFamily"),
                "beforePredicate": json_field(base, "predicate"),
                "afterPredicate": json_field(head, "predicate"),
                "sourceRefs": source_refs,
                "evidenceBoundary": "moved atom rows compare base/head ArchMap atom observations and retain source refs from the supplied ArchMap evidence"
            }))
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| {
        -row.get("movementScore")
            .and_then(serde_json::Value::as_i64)
            .unwrap_or_default()
    });
    serde_json::Value::Array(rows.into_iter().take(8).collect())
}

fn pr_coverage_gaps(
    base_archmap: &serde_json::Value,
    after_archmap: Option<&serde_json::Value>,
    base_packet: &serde_json::Value,
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let mut gaps: BTreeMap<String, serde_json::Value> = BTreeMap::new();
    for (side, document) in [("base", Some(base_archmap)), ("after", after_archmap)] {
        if let Some(document) = document {
            for gap in array_items(document, "observationGaps") {
                let gap_id = json_string(gap, "gapId", "observation-gap");
                gaps.insert(
                    format!("{side}:{gap_id}"),
                    serde_json::json!({
                        "side": side,
                        "gapId": gap_id,
                        "gapKind": json_field(gap, "gapKind"),
                        "reason": json_field(gap, "reason"),
                        "sourceRefs": array_field(gap, "sourceRefs")
                    }),
                );
            }
        }
    }
    for (side, packet) in [("base", Some(base_packet)), ("after", after_packet)] {
        if let Some(packet) = packet {
            for axis in array_items(packet, "signatureAxes") {
                for missing in string_vec_from_value(axis, "missingEvidence") {
                    gaps.insert(
                        format!("{side}:{}", missing),
                        serde_json::json!({
                            "side": side,
                            "gapId": missing,
                            "gapKind": "signatureAxisMissingEvidence",
                            "reason": "selected signature axis has missing evidence under LawPolicy",
                            "sourceRefs": array_field(axis, "sourceRefs")
                        }),
                    );
                }
            }
        }
    }
    serde_json::Value::Array(gaps.into_values().collect())
}

fn observation_movement_fingerprint(observation: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "atomFamily": json_field(observation, "atomFamily"),
        "predicate": json_field(observation, "predicate"),
        "subjectRef": json_field(observation, "subjectRef"),
        "objectRefs": array_field(observation, "objectRefs"),
        "observationStatus": json_field(observation, "observationStatus"),
        "evidenceBoundary": json_field(observation, "evidenceBoundary"),
        "confidence": json_field(observation, "confidence"),
        "uncertainty": array_field(observation, "uncertainty"),
        "projectionRefs": array_field(observation, "projectionRefs")
    })
}

fn pr_review_focus(
    delta_archmap: &serde_json::Value,
    top_moved_axes: &serde_json::Value,
    top_moved_atoms: &serde_json::Value,
    coverage_gaps: &serde_json::Value,
) -> serde_json::Value {
    let mut focus = Vec::new();
    for axis in array_items(
        delta_archmap
            .get("reviewIntent")
            .unwrap_or(&serde_json::Value::Null),
        "expectedReviewAxes",
    ) {
        if let Some(axis) = axis.as_str() {
            focus.push(format!("delta-requested-axis:{axis}"));
        }
    }
    for axis in top_moved_axes.as_array().into_iter().flatten().take(5) {
        if let Some(axis_ref) = axis.get("axisRef").and_then(serde_json::Value::as_str) {
            focus.push(format!("moved-axis:{axis_ref}"));
        }
    }
    for atom in top_moved_atoms.as_array().into_iter().flatten().take(5) {
        if let Some(atom_ref) = atom
            .get("atomObservationRef")
            .and_then(serde_json::Value::as_str)
        {
            focus.push(format!("moved-atom:{atom_ref}"));
        }
    }
    if coverage_gaps
        .as_array()
        .is_some_and(|items| !items.is_empty())
    {
        focus.push("coverage-gaps-limit-safe-change-budget".to_string());
    }
    json_string_array(focus.iter())
}

fn pr_distance_value(
    status: &str,
    measured_value: Option<i64>,
    unit: &str,
    provenance_refs: Vec<String>,
    evaluator_basis_refs: Vec<String>,
    reading: &str,
) -> serde_json::Value {
    let mut value = serde_json::json!({
        "status": status,
        "unit": unit,
        "provenanceRefs": json_string_array(provenance_refs.iter()),
        "evaluatorBasisRefs": json_string_array(evaluator_basis_refs.iter()),
        "coverageRefs": [],
        "blockerRefs": [],
        "reading": reading
    });
    if let Some(measured_value) = measured_value {
        if let Some(object) = value.as_object_mut() {
            object.insert(
                "measuredValue".to_string(),
                serde_json::Value::Number(measured_value.into()),
            );
        }
    }
    value
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

fn first_signature_distance(packet: &serde_json::Value) -> Option<&serde_json::Value> {
    packet
        .get("signatureDistanceReadings")
        .and_then(serde_json::Value::as_array)
        .and_then(|items| items.first())
}

fn signature_axis_value_map(packet: &serde_json::Value) -> BTreeMap<String, i64> {
    array_items(packet, "signatureAxes")
        .into_iter()
        .filter_map(|axis| {
            Some((
                axis.get("signatureAxisId")?.as_str()?.to_string(),
                axis.get("value").and_then(serde_json::Value::as_i64)?,
            ))
        })
        .collect()
}

fn signature_axis_object_map<'a>(
    packet: &'a serde_json::Value,
) -> BTreeMap<String, &'a serde_json::Value> {
    array_items(packet, "signatureAxes")
        .into_iter()
        .filter_map(|axis| Some((axis.get("signatureAxisId")?.as_str()?.to_string(), axis)))
        .collect()
}

fn observation_object_map<'a>(
    document: &'a serde_json::Value,
    collection_key: &str,
    id_key: &str,
) -> BTreeMap<String, &'a serde_json::Value> {
    array_items(document, collection_key)
        .into_iter()
        .filter_map(|observation| {
            Some((observation.get(id_key)?.as_str()?.to_string(), observation))
        })
        .collect()
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

fn string_vec_from_value(value: &serde_json::Value, key: &str) -> Vec<String> {
    array_items(value, key)
        .into_iter()
        .filter_map(serde_json::Value::as_str)
        .map(str::to_string)
        .collect()
}

fn string_vec_from_array_objects(value: &serde_json::Value, key: &str) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flat_map(|items| items.iter())
        .filter_map(|item| item.get(key))
        .filter_map(serde_json::Value::as_str)
        .map(str::to_string)
        .collect()
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
        "analysisUsefulness": analysis_usefulness(packet),
        "qualityMeasurement": quality_measurement(packet),
        "distanceDiagnosis": distance_diagnosis(packet),
        "measurementStatusSummary": measurement_status_summary(packet),
        "trendDiagnosis": trend_diagnosis(packet),
        "architectureInsightSummary": architecture_insight_summary(packet),
        "reviewSupport": review_support(packet),
        "dominantFindings": dominant_findings(packet),
        "actionQueue": action_queue(packet),
        "axisSummary": axis_summary(packet),
        "aatObservationAxisSummary": aat_observation_axis_summary(packet),
        "designPrincipleSummary": design_principle_summary(packet),
        "architecturalHoleSummary": architectural_hole_summary(packet),
        "bridgeSummary": bridge_summary(packet),
        "coverageGapSummary": coverage_gap_summary(packet),
        "detailIndex": detail_index(packet),
        "measurementBasis": measurement_basis(
            packet,
            archmap_validation,
            law_policy_validation,
            analysis_validation
        ),
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

const DOMINANT_FINDING_LIMIT: usize = 8;

fn dominant_findings(packet: &serde_json::Value) -> serde_json::Value {
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);

    serde_json::json!({
        "nonzeroAxes": nonzero_axis_findings(packet, DOMINANT_FINDING_LIMIT),
        "spectrumHotspots": hotspot_findings(spectrum, DOMINANT_FINDING_LIMIT),
        "recurrentObstructions": recurrent_obstruction_findings(spectrum, DOMINANT_FINDING_LIMIT),
        "architecturalHoles": loop_ref_findings(
            homotopy,
            "unfilledLoops",
            "/architectureHomotopyReport/unfilledLoops",
            "unfilledLoopMeasured",
            DOMINANT_FINDING_LIMIT
        ),
        "nonzeroHolonomy": loop_ref_findings(
            homotopy,
            "nonzeroHolonomyLoops",
            "/architectureHomotopyReport/nonzeroHolonomyLoops",
            "nonzeroSelectedAxisContinuationDistance",
            DOMINANT_FINDING_LIMIT
        ),
        "bridgePressure": bridge_pressure_findings(packet, DOMINANT_FINDING_LIMIT),
        "projectionFidelityLoss": projection_fidelity_findings(packet, DOMINANT_FINDING_LIMIT),
        "atomOriginClosureDebt": atom_origin_closure_findings(packet, DOMINANT_FINDING_LIMIT),
        "effectRelationPressure": effect_relation_findings(packet, DOMINANT_FINDING_LIMIT),
        "synthesisBlockage": synthesis_blockage_findings(packet, DOMINANT_FINDING_LIMIT),
        "operationPreconditionReadiness": operation_precondition_findings(packet, DOMINANT_FINDING_LIMIT),
        "pathMultiplicityLoss": path_multiplicity_findings(packet, DOMINANT_FINDING_LIMIT)
    })
}

const READING_MODE_FINDING_LIMIT: usize = 1;

fn trend_diagnosis(packet: &serde_json::Value) -> serde_json::Value {
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "verdict": analysis_verdict(packet),
        "trendCounts": trend_counts(packet),
        "pressureConcentration": {
            "nonzeroAxisRefs": nonzero_axis_ref_list(packet, READING_MODE_FINDING_LIMIT),
            "spectrumHotspotRefs": compact_ref_list(spectrum, "topHotspots", "hotspotId", READING_MODE_FINDING_LIMIT),
            "recurrentObstructionRefs": compact_ref_list(spectrum, "recurrentObstructions", "modeRef", READING_MODE_FINDING_LIMIT),
            "bridgePressureRefs": bridge_pressure_ref_list(packet, READING_MODE_FINDING_LIMIT),
            "pathMultiplicityLossRefs": compact_ref_list(packet, "pathMultiplicityLossReadings", "readingId", 1),
            "projectionFidelityLossRefs": compact_ref_list(packet, "observationProjectionFidelityReadings", "readingId", 1),
            "atomOriginClosureDebtRefs": compact_ref_list(packet, "atomOriginClosureDebtReadings", "readingId", 1)
        },
        "trendInsights": trend_insights(packet),
        "packetRefs": packet_refs(&[
            "/signatureAxes",
            "/architectureSpectrumReport",
            "/transferBridgeReadings",
            "/pathMultiplicityLossReadings",
            "/observationProjectionFidelityReadings",
            "/atomOriginClosureDebtReadings"
        ])
    })
}

fn review_support(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "actionQueueCount": array_len_keyless(&action_queue(packet)),
        "blockerSummary": {
            "architecturalHoleRefs": homotopy_ref_list(packet, "unfilledLoops", READING_MODE_FINDING_LIMIT),
            "nonzeroHolonomyRefs": homotopy_ref_list(packet, "nonzeroHolonomyLoops", READING_MODE_FINDING_LIMIT),
            "operationPreconditionRefs": compact_ref_list(packet, "operationPreconditionReadinessReadings", "operationRef", READING_MODE_FINDING_LIMIT),
            "synthesisBlockageRefs": compact_ref_list(packet, "synthesisBlockageReadings", "readingId", READING_MODE_FINDING_LIMIT),
            "effectRelationPressureRefs": compact_ref_list(packet, "effectRelationAlgebraReadings", "readingId", READING_MODE_FINDING_LIMIT),
            "coverageGapRefs": json_string_array(coverage_gap_refs(packet).iter())
        },
        "packetRefs": packet_refs(&[
            "/architectureHomotopyReport",
            "/operationPreconditionReadinessReadings",
            "/synthesisBlockageReadings",
            "/effectRelationAlgebraReadings",
            "/flatnessReading/blockedByCoverageGaps",
            "/architectureSpectrumReport/coverageGaps",
            "/architectureHomotopyReport/coverageGaps"
        ])
    })
}

fn analysis_usefulness(packet: &serde_json::Value) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    let coverage_gap_count = coverage_gap_refs(packet).len();
    let nonzero_axis_count = array_len(flatness, "nonzeroSignatureAxisRefs");
    let hotspot_count = array_len(spectrum, "topHotspots");
    let architectural_hole_count = array_len(homotopy, "unfilledLoops");
    let repair_candidate_count = array_len(packet, "repairOperationCandidates");

    serde_json::json!({
        "mode": if coverage_gap_count > 0 {
            "gapQualifiedActionableAnalysis"
        } else {
            "closedCoverageActionableAnalysis"
        },
        "valueStatement": if coverage_gap_count > 0 {
            "coverage gaps qualify zero, flatness, completeness, and repair-safety claims, but they do not block structural pressure localization or review prioritization"
        } else {
            "no coverage gap was recorded in the selected coverage universe; pressure and zero readings can be read against the supplied ArchMap and LawPolicy"
        },
        "usableNow": usable_now_findings(
            nonzero_axis_count,
            hotspot_count,
            architectural_hole_count,
            repair_candidate_count,
        ),
        "blockedByGaps": blocked_claims_by_gaps(coverage_gap_count),
        "evidenceToUpgradeConfidence": evidence_to_upgrade_confidence(packet),
        "packetRefs": packet_refs(&[
            "/signatureAxes",
            "/architectureSpectrumReport/topHotspots",
            "/architectureHomotopyReport/unfilledLoops",
            "/repairOperationCandidates",
            "/flatnessReading/blockedByCoverageGaps"
        ])
    })
}

fn usable_now_findings(
    nonzero_axis_count: usize,
    hotspot_count: usize,
    architectural_hole_count: usize,
    repair_candidate_count: usize,
) -> serde_json::Value {
    let mut findings = Vec::new();
    if nonzero_axis_count > 0 {
        findings.push(serde_json::json!({
            "kind": "selectedLawPressure",
            "claim": format!("{nonzero_axis_count} selected LawPolicy axis/axes have nonzero observed support"),
            "use": "prioritize architecture review around selected law pressure rather than treating the repo as uniformly unknown"
        }));
    }
    if hotspot_count > 0 {
        findings.push(serde_json::json!({
            "kind": "curvatureHotspots",
            "claim": format!("{hotspot_count} spectrum hotspot(s) localize repeated obstruction support"),
            "use": "start review from the highest hotspot detail refs"
        }));
    }
    if architectural_hole_count > 0 {
        findings.push(serde_json::json!({
            "kind": "architecturalHoles",
            "claim": format!("{architectural_hole_count} unfilled loop(s) were measured"),
            "use": "identify contract, runtime, policy, or source-backed filler evidence to inspect next"
        }));
    }
    if repair_candidate_count > 0 {
        findings.push(serde_json::json!({
            "kind": "repairReviewQueue",
            "claim": format!("{repair_candidate_count} repair candidate(s) were derived as review cues"),
            "use": "turn candidates into implementation tasks only after preconditions and transfer risk are checked"
        }));
    }
    serde_json::Value::Array(findings)
}

fn blocked_claims_by_gaps(coverage_gap_count: usize) -> serde_json::Value {
    if coverage_gap_count == 0 {
        return serde_json::json!({
            "coverageGapCount": 0,
            "claims": []
        });
    }
    serde_json::json!({
        "coverageGapCount": coverage_gap_count,
        "claims": [
            {
                "claim": "global architecture flatness or lawfulness",
                "reason": "selected coverage gaps prevent promoting absent evidence to zero"
            },
            {
                "claim": "automatic repair safety",
                "reason": "repair candidates still need precondition, runtime, and transfer-risk evidence"
            },
            {
                "claim": "source extraction completeness",
                "reason": "ArchMap observation gaps explicitly bound the supplied source universe"
            }
        ]
    })
}

fn evidence_to_upgrade_confidence(packet: &serde_json::Value) -> serde_json::Value {
    let mut refs = coverage_gap_refs(packet).into_iter().collect::<Vec<_>>();
    refs.sort();
    serde_json::Value::Array(
        refs.into_iter()
            .take(ARCHITECTURE_INSIGHT_REF_LIMIT + 1)
            .map(|gap_ref| {
                let evidence_kind = if gap_ref.contains("runtime") {
                    "runtime traces, request logs, queue traces, or provider execution logs"
                } else if gap_ref.contains("openapi") || gap_ref.contains("framework") {
                    "expanded framework registry, route table, dependency graph, or generated contract"
                } else if gap_ref.contains("provider") || gap_ref.contains("credentials") {
                    "provider policy, credential scope, webhook headers, or provider response samples"
                } else if gap_ref.contains("db") || gap_ref.contains("rls") {
                    "database migration, RLS policy, and deployed tenant-policy evidence"
                } else {
                    "source-backed evidence for the named coverage gap"
                };
                serde_json::json!({
                    "gapRef": gap_ref,
                    "evidenceKind": evidence_kind
                })
            })
            .collect(),
    )
}

const ARCHITECTURE_INSIGHT_LIMIT: usize = 3;
const ARCHITECTURE_INSIGHT_REF_LIMIT: usize = 2;

fn architecture_insight_summary(packet: &serde_json::Value) -> serde_json::Value {
    let clusters = architecture_pressure_clusters(packet);
    serde_json::json!({
        "topInsight": architecture_top_insight(packet, &clusters),
        "insightCards": architecture_insight_cards(packet, &clusters, ARCHITECTURE_INSIGHT_LIMIT),
        "primaryPressureClusters": cluster_summaries(&clusters, ARCHITECTURE_INSIGHT_LIMIT),
        "coverageBlockers": coverage_blocker_insights(packet, ARCHITECTURE_INSIGHT_LIMIT),
        "repairPlanning": repair_planning_summary(packet, ARCHITECTURE_INSIGHT_LIMIT),
        "readNext": architecture_read_next(&clusters),
        "claimBoundary": "insights are structural reading aids over the supplied ArchMap and LawPolicy; they are not a proof, forecast, or automatic repair plan",
        "packetRefs": packet_refs(&[
            "/signatureAxes",
            "/architectureSpectrumReport/topHotspots",
            "/repairOperationCandidates",
            "/operationPreconditionReadinessReadings",
            "/operationDeltas"
        ])
    })
}

fn architecture_top_insight(
    packet: &serde_json::Value,
    clusters: &[ArchitectureInsightCluster],
) -> serde_json::Value {
    let top_cluster = clusters.first();
    let top_cluster_title = top_cluster
        .map(|cluster| concern_metadata(&cluster.concern).0)
        .unwrap_or("no dominant pressure cluster");
    let coverage_gap_count = coverage_gap_refs(packet).len();
    let repair_candidate_count = array_len(packet, "repairOperationCandidates");
    serde_json::json!({
        "headline": if top_cluster.is_some() {
            format!("{top_cluster_title} is the dominant structural pressure cluster under the selected LawPolicy")
        } else {
            "no dominant structural pressure cluster was measured under the selected LawPolicy".to_string()
        },
        "whyItMatters": "The useful reading is not a flat count: prioritize places where law axes, spectrum hotspots, coverage blockers, repair candidates, and operation preconditions overlap.",
        "coveragePosture": if coverage_gap_count > 0 {
            "coverage gaps qualify zero/flatness/repair-safety claims; measured pressure localization remains usable"
        } else {
            "no coverage blocker was recorded for the selected coverage universe"
        },
        "repairPosture": if repair_candidate_count > 0 {
            "repair candidates exist, but their preconditions and transfer risks must be reviewed before implementation"
        } else {
            "no repair candidate was emitted for this packet"
        }
    })
}

#[derive(Debug, Default)]
struct ArchitectureInsightCluster {
    concern: String,
    pressure_score: i64,
    nonzero_axis_refs: BTreeSet<String>,
    hotspot_refs: BTreeSet<String>,
    repair_refs: BTreeSet<String>,
    precondition_refs: BTreeSet<String>,
    coverage_gap_refs: BTreeSet<String>,
    detail_refs: BTreeSet<String>,
}

fn architecture_pressure_clusters(packet: &serde_json::Value) -> Vec<ArchitectureInsightCluster> {
    let mut clusters = BTreeMap::<String, ArchitectureInsightCluster>::new();
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);

    for (index, axis) in array_items(packet, "signatureAxes").into_iter().enumerate() {
        if i64_field(axis, "value", 0) == 0 {
            continue;
        }
        let text = architecture_signal_text(
            axis,
            &["signatureAxisId", "axisRef", "lawRef", "coverageStatus"],
            &[],
        );
        for concern in concern_keys_for_text(&text) {
            record_architecture_signal(
                &mut clusters,
                concern,
                "nonzeroSignatureAxis",
                json_field(axis, "signatureAxisId")
                    .as_str()
                    .unwrap_or("unknown"),
                &format!("packet:/signatureAxes/{index}"),
                i64_field(axis, "value", 1).max(1) * 100,
                coverage_refs_from_signal(axis),
            );
        }
    }

    for (index, hotspot) in array_items(spectrum, "topHotspots").into_iter().enumerate() {
        let text = architecture_signal_text(
            hotspot,
            &["hotspotId", "axisRef", "recommendedNextAction"],
            &[],
        );
        for concern in concern_keys_for_text(&text) {
            record_architecture_signal(
                &mut clusters,
                concern,
                "spectrumHotspot",
                json_field(hotspot, "hotspotId")
                    .as_str()
                    .unwrap_or("unknown"),
                &format!("packet:/architectureSpectrumReport/topHotspots/{index}"),
                i64_field(hotspot, "curvatureValue", 1).max(1) * 50,
                coverage_refs_from_signal(hotspot),
            );
        }
    }

    for (index, candidate) in array_items(packet, "repairOperationCandidates")
        .into_iter()
        .enumerate()
    {
        let text = architecture_signal_text(
            candidate,
            &[
                "repairOperationCandidateId",
                "operationKind",
                "evidenceBoundary",
            ],
            &[
                "expectedSignatureAxisEffects",
                "transferRisks",
                "targetObstructionRefs",
            ],
        );
        for concern in concern_keys_for_text(&text) {
            record_architecture_signal(
                &mut clusters,
                concern,
                "repairCandidate",
                json_field(candidate, "repairOperationCandidateId")
                    .as_str()
                    .unwrap_or("unknown"),
                &format!("packet:/repairOperationCandidates/{index}"),
                75,
                coverage_refs_from_signal(candidate),
            );
        }
    }

    for (index, reading) in array_items(packet, "operationPreconditionReadinessReadings")
        .into_iter()
        .enumerate()
    {
        let text = architecture_signal_text(
            reading,
            &[
                "operationRef",
                "operationKind",
                "readinessStatus",
                "recommendedNextAction",
            ],
            &[],
        );
        let precondition_score = (array_len(reading, "missingPreconditionRefs")
            + array_len(reading, "coverageGapRefs")
            + array_len(reading, "witnessGapRefs"))
        .max(1) as i64;
        for concern in concern_keys_for_text(&text) {
            record_architecture_signal(
                &mut clusters,
                concern,
                "operationPrecondition",
                json_field(reading, "operationRef")
                    .as_str()
                    .unwrap_or("unknown"),
                &format!("packet:/operationPreconditionReadinessReadings/{index}"),
                precondition_score * 10,
                coverage_refs_from_signal(reading),
            );
        }
    }

    let mut values = clusters.into_values().collect::<Vec<_>>();
    values.sort_by(|left, right| {
        right
            .pressure_score
            .cmp(&left.pressure_score)
            .then(left.concern.cmp(&right.concern))
    });
    values
}

fn record_architecture_signal(
    clusters: &mut BTreeMap<String, ArchitectureInsightCluster>,
    concern: &str,
    kind: &str,
    reference: &str,
    detail_ref: &str,
    score: i64,
    coverage_refs: BTreeSet<String>,
) {
    let cluster =
        clusters
            .entry(concern.to_string())
            .or_insert_with(|| ArchitectureInsightCluster {
                concern: concern.to_string(),
                ..ArchitectureInsightCluster::default()
            });
    cluster.pressure_score += score;
    match kind {
        "nonzeroSignatureAxis" => {
            cluster.nonzero_axis_refs.insert(reference.to_string());
        }
        "spectrumHotspot" => {
            cluster.hotspot_refs.insert(reference.to_string());
        }
        "repairCandidate" => {
            cluster.repair_refs.insert(reference.to_string());
        }
        "operationPrecondition" => {
            cluster.precondition_refs.insert(reference.to_string());
        }
        _ => {}
    }
    cluster.detail_refs.insert(detail_ref.to_string());
    cluster.coverage_gap_refs.extend(coverage_refs);
}

fn cluster_summaries(clusters: &[ArchitectureInsightCluster], limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        clusters
            .iter()
            .take(limit)
            .map(|cluster| {
                let (title, why, recommended_review) = concern_metadata(&cluster.concern);
                serde_json::json!({
                    "concern": cluster.concern,
                    "title": title,
                    "reading": why,
                    "pressureScore": cluster.pressure_score,
                    "signalCounts": {
                        "nonzeroAxisCount": cluster.nonzero_axis_refs.len(),
                        "spectrumHotspotCount": cluster.hotspot_refs.len(),
                        "repairCandidateCount": cluster.repair_refs.len(),
                        "operationPreconditionBlockerCount": cluster.precondition_refs.len(),
                        "coverageBlockerCount": cluster.coverage_gap_refs.len()
                    },
                    "recommendedReview": recommended_review,
                    "detailRefs": limited_string_set_values(&cluster.detail_refs, ARCHITECTURE_INSIGHT_REF_LIMIT)
                })
            })
            .collect(),
    )
}

fn architecture_insight_cards(
    _packet: &serde_json::Value,
    clusters: &[ArchitectureInsightCluster],
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        clusters
            .iter()
            .take(limit)
            .enumerate()
            .map(|(index, cluster)| {
                let observed = observed_signal_sentences(cluster);
                let missing = insight_card_missing_evidence(cluster);
                let (claim, why_it_matters, next_validation) =
                    insight_card_language(&cluster.concern);
                serde_json::json!({
                    "cardId": format!("insight-card:{}", index + 1),
                    "concern": cluster.concern,
                    "claim": claim,
                    "whyItMatters": why_it_matters,
                    "aatEvidence": {
                        "nonzeroAxisRefs": limited_string_set_values(&cluster.nonzero_axis_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1),
                        "spectrumHotspotRefs": limited_string_set_values(&cluster.hotspot_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1),
                        "repairCandidateRefs": limited_string_set_values(&cluster.repair_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1),
                        "operationPreconditionRefs": limited_string_set_values(&cluster.precondition_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1),
                        "coverageGapRefs": limited_string_set_values(&cluster.coverage_gap_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1)
                    },
                    "observedSignals": observed,
                    "missingEvidence": missing,
                    "notBlockedByGaps": "measured nonzero axes, spectrum hotspots, repair cues, and precondition blockers are usable review signals even when gaps block zero, global flatness, and repair-safety claims",
                    "blockedClaims": [
                        "global lawfulness or flatness",
                        "automatic repair safety",
                        "source extraction completeness"
                    ],
                    "nextValidation": next_validation,
                    "detailRefs": limited_string_set_values(&cluster.detail_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1)
                })
            })
            .collect(),
    )
}

fn insight_card_missing_evidence(cluster: &ArchitectureInsightCluster) -> serde_json::Value {
    limited_string_set_values(
        &cluster.coverage_gap_refs,
        ARCHITECTURE_INSIGHT_REF_LIMIT + 1,
    )
}

fn observed_signal_sentences(cluster: &ArchitectureInsightCluster) -> serde_json::Value {
    let mut signals = Vec::new();
    if !cluster.nonzero_axis_refs.is_empty()
        || !cluster.hotspot_refs.is_empty()
        || !cluster.repair_refs.is_empty()
    {
        signals.push(format!(
            "cluster combines {} nonzero axis ref(s), {} hotspot ref(s), {} repair cue(s), and {} precondition blocker ref(s)",
            cluster.nonzero_axis_refs.len(),
            cluster.hotspot_refs.len(),
            cluster.repair_refs.len(),
            cluster.precondition_refs.len()
        ));
    }
    serde_json::Value::Array(signals.into_iter().map(serde_json::Value::String).collect())
}

fn insight_card_language(concern: &str) -> (&'static str, &'static str, serde_json::Value) {
    match concern {
        "authorityTrustBoundary" => (
            "authority and trust checks should be reviewed as one boundary across provider ingress and tenant-scoped routes",
            "The packet shows authority, tenant, role, trust, and permission signals overlapping in the same architecture boundary; reviewing them separately can miss handoff failures.",
            serde_json::json!([
                "trace the selected routes from request identity to tenant or workspace scope",
                "compare provider trust evidence with route/session authority evidence",
                "decide which gaps must be resolved before making a zero or repair-safety claim"
            ]),
        ),
        "stateEffectLifecycle" => (
            "state/effect pressure is concentrated where durable status, retry, external effects, and finalization meet",
            "The relevant risk is not just an async implementation detail; it is the boundary where effect ordering and state-machine ownership must agree.",
            serde_json::json!([
                "review retry, idempotency, compensation, and terminal status evidence together",
                "check whether commit/enqueue or provider-effect paths have an explicit recovery story",
                "separate missing runtime traces from observed source-backed pressure"
            ]),
        ),
        "llmOutputGovernance" => (
            "LLM and generated-output pressure is a cross-boundary architecture property, not a single chat-agent concern",
            "Prompt/context validation, provider output, generated artifacts, and persistence gates appear together; treating them as isolated code paths weakens review.",
            serde_json::json!([
                "follow generated content from prompt inputs through provider response to persistence",
                "check output filtering and tenant/workspace authority at the persistence boundary",
                "collect provider response samples or runtime traces before claiming the boundary is safe"
            ]),
        ),
        "providerIntegrationBoundary" => (
            "external provider ingress participates in the same pressure as authority, output mediation, and retry/finalization",
            "Provider boundaries are carrying trust, authority, runtime, and effect-ordering assumptions at once, so credential or webhook review alone is too narrow.",
            serde_json::json!([
                "review webhook verification, credential scope, provider response evidence, and retry behavior together",
                "map provider-originated data into the paths that persist or generate downstream artifacts",
                "resolve provider policy and response-sample gaps before promoting absence to zero"
            ]),
        ),
        "layerContractBoundary" => (
            "layer/contract pressure is concentrated where API, service, repository, and schema responsibilities converge",
            "The packet points to boundary responsibilities that must preserve contracts across layers, not just files with many dependencies.",
            serde_json::json!([
                "compare API route contracts with service and repository ownership",
                "check whether schema, persistence, and dependency boundaries have one owner",
                "use source refs to distinguish boundary design pressure from mere surface size"
            ]),
        ),
        "sourceProjectionBoundary" => (
            "source-backed projection pressure means domain cohesion and evidence fidelity are part of the same review surface",
            "The useful question is whether the ArchMap projection preserved the coordinates needed for law-relative reading, not whether every missing atom is absent.",
            serde_json::json!([
                "review projection-lost families and forgotten coordinates before repair planning",
                "connect domain cohesion readings back to concrete source-backed atoms",
                "decide which expected-missing evidence is out of scope versus required for confidence"
            ]),
        ),
        _ => (
            "multiple structural readings overlap, but the selected policy did not label a narrower concern",
            "This still gives a review starting point, but the LawPolicy may need a more specific axis to turn the cluster into a sharper architectural claim.",
            serde_json::json!([
                "inspect the packet detail refs for the cluster",
                "decide whether a more specific LawPolicy axis should be introduced",
                "separate observed support from missing evidence before planning repair"
            ]),
        ),
    }
}

fn coverage_blocker_insights(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut blockers = BTreeMap::<String, CoverageBlockerInsight>::new();
    for gap in coverage_gap_refs(packet) {
        let blocker = blockers
            .entry(gap.clone())
            .or_insert_with(|| CoverageBlockerInsight::new(&gap));
        blocker
            .detail_refs
            .insert("packet:/flatnessReading/blockedByCoverageGaps".to_string());
        blocker
            .detail_refs
            .insert("packet:/architectureSpectrumReport/coverageGaps".to_string());
        blocker
            .detail_refs
            .insert("packet:/architectureHomotopyReport/coverageGaps".to_string());
    }
    for (index, axis) in array_items(packet, "signatureAxes").into_iter().enumerate() {
        for gap in coverage_refs_from_signal(axis) {
            blockers
                .entry(gap.clone())
                .or_insert_with(|| CoverageBlockerInsight::new(&gap))
                .axis_refs
                .insert(
                    json_field(axis, "signatureAxisId")
                        .as_str()
                        .unwrap_or("unknown")
                        .to_string(),
                );
            blockers
                .get_mut(&gap)
                .expect("coverage blocker exists")
                .detail_refs
                .insert(format!("packet:/signatureAxes/{index}"));
        }
    }
    for (index, candidate) in array_items(packet, "repairOperationCandidates")
        .into_iter()
        .enumerate()
    {
        for gap in coverage_refs_from_signal(candidate) {
            blockers
                .entry(gap.clone())
                .or_insert_with(|| CoverageBlockerInsight::new(&gap))
                .repair_refs
                .insert(
                    json_field(candidate, "repairOperationCandidateId")
                        .as_str()
                        .unwrap_or("unknown")
                        .to_string(),
                );
            blockers
                .get_mut(&gap)
                .expect("coverage blocker exists")
                .detail_refs
                .insert(format!("packet:/repairOperationCandidates/{index}"));
        }
    }

    let mut values = blockers.into_values().collect::<Vec<_>>();
    values.sort_by(|left, right| {
        right
            .impact_count()
            .cmp(&left.impact_count())
            .then(left.gap_ref.cmp(&right.gap_ref))
    });

    serde_json::json!({
        "coverageBlockerCount": values.len(),
        "items": values
            .into_iter()
            .take(limit)
            .map(|blocker| blocker.to_json())
            .collect::<Vec<_>>(),
        "recommendedReview": "resolve or explicitly accept the highest-impact gaps before reading selected axes as zero or planning repair safety",
        "packetRefs": packet_refs(&[
            "/flatnessReading/blockedByCoverageGaps",
            "/architectureSpectrumReport/coverageGaps",
            "/architectureHomotopyReport/coverageGaps"
        ])
    })
}

#[derive(Debug)]
struct CoverageBlockerInsight {
    gap_ref: String,
    axis_refs: BTreeSet<String>,
    repair_refs: BTreeSet<String>,
    detail_refs: BTreeSet<String>,
}

impl CoverageBlockerInsight {
    fn new(gap_ref: &str) -> Self {
        Self {
            gap_ref: gap_ref.to_string(),
            axis_refs: BTreeSet::new(),
            repair_refs: BTreeSet::new(),
            detail_refs: BTreeSet::new(),
        }
    }

    fn impact_count(&self) -> usize {
        self.axis_refs.len() + self.repair_refs.len()
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "gapRef": self.gap_ref,
            "impactCount": self.impact_count(),
            "affectedAxisCount": self.axis_refs.len(),
            "affectedRepairCandidateCount": self.repair_refs.len(),
            "detailRefs": limited_string_set_values(&self.detail_refs, ARCHITECTURE_INSIGHT_REF_LIMIT)
        })
    }
}

fn repair_planning_summary(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut candidates = array_items(packet, "repairOperationCandidates")
        .into_iter()
        .enumerate()
        .map(|(index, candidate)| {
            let missing_evidence_count = coverage_refs_from_signal(candidate).len()
                + array_len(candidate, "missingEvidence");
            let transfer_risk_count = array_len(candidate, "transferRisks");
            serde_json::json!({
                "ref": json_field(candidate, "repairOperationCandidateId"),
                "operationKind": json_field(candidate, "operationKind"),
                "targetObstructionCount": array_len(candidate, "targetObstructionRefs"),
                "expectedAxisEffectCount": array_len(candidate, "expectedSignatureAxisEffects"),
                "preconditionCount": array_len(candidate, "preconditions"),
                "coverageBlockerCount": coverage_refs_from_signal(candidate).len(),
                "transferRiskCount": transfer_risk_count,
                "missingEvidenceCount": missing_evidence_count,
                "readiness": if missing_evidence_count > 0 || transfer_risk_count > 0 {
                    "reviewPreconditionsBeforeImplementation"
                } else {
                    "candidateReadyForHumanSelection"
                },
                "detailRefs": detail_refs("repairOperationCandidates", &format!("/repairOperationCandidates/{index}"))
            })
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|candidate| {
        std::cmp::Reverse(
            candidate["missingEvidenceCount"]
                .as_u64()
                .unwrap_or_default()
                + candidate["transferRiskCount"].as_u64().unwrap_or_default(),
        )
    });
    serde_json::json!({
        "candidateCount": array_len(packet, "repairOperationCandidates"),
        "candidateOperations": candidates.into_iter().take(limit).collect::<Vec<_>>(),
        "operationDeltaCount": array_len(packet, "operationDeltas"),
        "recommendedReview": "check target obstruction, expected axis effects, missing evidence, and transfer risk before turning a candidate into an implementation task",
        "packetRefs": packet_refs(&["/repairOperationCandidates", "/operationDeltas"])
    })
}

fn architecture_read_next(clusters: &[ArchitectureInsightCluster]) -> serde_json::Value {
    let cluster = clusters.first();
    let mut items = Vec::new();
    if let Some(cluster) = cluster {
        items.push(serde_json::json!({
            "step": 1,
            "focus": concern_metadata(&cluster.concern).0,
            "reason": "start with the highest combined structural pressure; gaps qualify completeness, not the existence of this review signal",
            "detailRefs": limited_string_set_values(&cluster.detail_refs, ARCHITECTURE_INSIGHT_REF_LIMIT)
        }));
    }
    items.extend([
        serde_json::json!({
            "step": 2,
            "focus": "spectrum and selected law overlap",
            "reason": "spectrum hotspots and nonzero signature axes show where selected law pressure concentrates",
            "packetRefs": packet_refs(&["/architectureSpectrumReport/topHotspots", "/signatureAxes"])
        }),
        serde_json::json!({
            "step": 3,
            "focus": "coverage blockers",
            "reason": "use coverage gaps to qualify zero/flatness and choose confidence-upgrade evidence, not to discard structural pressure findings",
            "packetRefs": packet_refs(&[
                "/flatnessReading/blockedByCoverageGaps",
                "/architectureSpectrumReport/coverageGaps",
                "/architectureHomotopyReport/coverageGaps"
            ])
        }),
        serde_json::json!({
            "step": 4,
            "focus": "repair preconditions and transfer",
            "reason": "repair candidates are useful only after missing evidence, preconditions, and transferred obstruction risk are visible",
            "packetRefs": packet_refs(&["/repairOperationCandidates", "/operationPreconditionReadinessReadings", "/operationDeltas"])
        }),
    ]);
    serde_json::Value::Array(items)
}

fn architecture_signal_text(
    value: &serde_json::Value,
    scalar_fields: &[&str],
    array_fields: &[&str],
) -> String {
    let mut parts = Vec::new();
    for field in scalar_fields {
        if let Some(text) = value.get(field).and_then(serde_json::Value::as_str) {
            parts.push(text.to_string());
        }
    }
    for field in array_fields {
        parts.extend(string_array(value, field));
    }
    parts.join(" ")
}

fn concern_keys_for_text(text: &str) -> BTreeSet<&'static str> {
    let normalized = text.to_ascii_lowercase();
    let mut concerns = BTreeSet::new();
    if contains_any(
        &normalized,
        &[
            "authority",
            "permission",
            "tenant",
            "role",
            "jwt",
            "auth",
            "trust",
            "session",
            "rls",
            "token",
        ],
    ) {
        concerns.insert("authorityTrustBoundary");
    }
    if contains_any(
        &normalized,
        &[
            "state",
            "status",
            "job",
            "retry",
            "idempot",
            "event",
            "effect",
            "commit",
            "flush",
            "compensation",
            "transition",
            "upload",
        ],
    ) {
        concerns.insert("stateEffectLifecycle");
    }
    if contains_any(
        &normalized,
        &[
            "prompt",
            "llm",
            "ai",
            "model",
            "provider output",
            "context",
            "embedding",
            "agent",
            "generated",
        ],
    ) {
        concerns.insert("llmOutputGovernance");
    }
    if contains_any(
        &normalized,
        &[
            "provider",
            "webhook",
            "slack",
            "zoom",
            "salesforce",
            "external",
            "ingress",
            "s3",
            "email",
        ],
    ) {
        concerns.insert("providerIntegrationBoundary");
    }
    if contains_any(
        &normalized,
        &[
            "layer",
            "repository",
            "service",
            "api",
            "route",
            "contract",
            "schema",
            "dependency",
            "interface",
        ],
    ) {
        concerns.insert("layerContractBoundary");
    }
    if contains_any(
        &normalized,
        &[
            "source",
            "projection",
            "domain",
            "cohesion",
            "origin",
            "inventory",
            "atom",
        ],
    ) {
        concerns.insert("sourceProjectionBoundary");
    }
    if concerns.is_empty() {
        concerns.insert("generalStructuralPressure");
    }
    concerns
}

fn contains_any(value: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| value.contains(needle))
}

fn concern_metadata(concern: &str) -> (&'static str, &'static str, &'static str) {
    match concern {
        "authorityTrustBoundary" => (
            "authority / trust boundary",
            "authority, tenant, role, trust, and permission signals are overlapping in selected law, spectrum, and operation readings",
            "review route/session authority, tenant scope, trust handoff, and policy evidence together",
        ),
        "stateEffectLifecycle" => (
            "state / effect lifecycle",
            "state transitions, durable effects, retries, events, and status finalization are coupled with selected structural pressure",
            "review state machine ownership, effect ordering, retry/idempotency, and terminal status evidence together",
        ),
        "llmOutputGovernance" => (
            "LLM / output governance",
            "prompt, model, provider output, generated artifact, and persistence boundaries participate in the same pressure cluster",
            "review prompt/context validation, output filtering, persistence gates, and source-backed projection evidence together",
        ),
        "providerIntegrationBoundary" => (
            "provider integration boundary",
            "external provider ingress, webhook, credential, and response surfaces appear in the same structural pressure cluster",
            "review provider trust assumptions, webhook verification, credential policy, and provider response evidence together",
        ),
        "layerContractBoundary" => (
            "layer / contract boundary",
            "API, service, repository, schema, route, and dependency boundaries are carrying selected law pressure",
            "review layer responsibility, contract ownership, API/service/repository split, and schema dependency evidence together",
        ),
        "sourceProjectionBoundary" => (
            "source projection boundary",
            "source-backed domain identity, projection, Atom origin, and cohesion readings affect the same architecture surface",
            "review source inventory, domain projection, Atom origin closure, and projection fidelity together",
        ),
        _ => (
            "general structural pressure",
            "multiple structural readings overlap without a narrower concern label",
            "review the linked packet details and decide whether a more specific LawPolicy axis is needed",
        ),
    }
}

fn coverage_refs_from_signal(value: &serde_json::Value) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    for key in [
        "coverageGapRefs",
        "missingEvidence",
        "preconditions",
        "witnessGapRefs",
        "exactnessAssumptions",
    ] {
        collect_value_labels(array_items(value, key), &mut refs);
    }
    refs.into_iter()
        .filter(|reference| reference.starts_with("gap:") || reference.starts_with("coverage:"))
        .collect()
}

fn limited_string_set_values(values: &BTreeSet<String>, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        values
            .iter()
            .take(limit)
            .map(|value| serde_json::Value::String(value.clone()))
            .collect(),
    )
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
        "part4SupportingDistanceCount": array_len(
            packet
                .get("part4DistanceFoundation")
                .unwrap_or(&serde_json::Value::Null),
            "supportingDistances"
        ),
        "atomDistanceReadingCount": array_len(packet, "atomDistanceReadings"),
        "configurationDistanceReadingCount": array_len(packet, "configurationDistanceReadings"),
        "signatureDistanceReadingCount": array_len(packet, "signatureDistanceReadings"),
        "operationDistanceReadingCount": array_len(packet, "operationDistanceReadings"),
        "curvatureMassReadingCount": array_len(packet, "curvatureMassReadings"),
        "homotopyDistanceReadingCount": array_len(packet, "homotopyDistanceReadings"),
        "representationMetricReadingCount": array_len(packet, "representationMetricReadings"),
        "transferBridgeCount": array_len(packet, "transferBridgeReadings"),
        "projectionFidelityLossCount": array_len(packet, "observationProjectionFidelityReadings"),
        "atomOriginClosureDebtCount": array_len(packet, "atomOriginClosureDebtReadings"),
        "effectRelationPressureCount": array_len(packet, "effectRelationAlgebraReadings"),
        "synthesisBlockageCount": array_len(packet, "synthesisBlockageReadings"),
        "operationPreconditionBlockerCount": array_len(packet, "operationPreconditionReadinessReadings"),
        "pathMultiplicityLossCount": array_len(packet, "pathMultiplicityLossReadings"),
        "coverageGapCount": coverage_gap_refs(packet).len()
    })
}

fn distance_diagnosis(packet: &serde_json::Value) -> serde_json::Value {
    let foundation = packet
        .get("part4DistanceFoundation")
        .unwrap_or(&serde_json::Value::Null);
    let status_summary = json_field(foundation, "statusSummary");
    let signature_distance = array_items(packet, "signatureDistanceReadings")
        .into_iter()
        .next()
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    let operation_distance = array_items(packet, "operationDistanceReadings")
        .into_iter()
        .next()
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    let curvature_distance = array_items(packet, "curvatureMassReadings")
        .into_iter()
        .next()
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    let homotopy_distance = array_items(packet, "homotopyDistanceReadings")
        .into_iter()
        .next()
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    let diagnostic_scope = foundation
        .get("diagnosticScope")
        .unwrap_or(&serde_json::Value::Null);
    let blocked_count = status_summary
        .get("blockedCount")
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    let measured_count = status_summary
        .get("measuredCount")
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();

    serde_json::json!({
        "verdict": if blocked_count > 0 {
            "distanceBlockedByCoverageOrEvidence"
        } else if measured_count > 0 {
            "distanceMeasuredWithinPolicy"
        } else {
            "distanceNeedsEvaluatorEvidence"
        },
        "distanceStatusSummary": status_summary,
        "distanceProfileRef": json_field(
            foundation.get("profile").unwrap_or(&serde_json::Value::Null),
            "profileId"
        ),
        "measuredMovement": {
            "totalMeasuredDistance": compact_distance_value(&signature_distance, "totalMeasuredDistance"),
            "pathDrift": compact_distance_value(&signature_distance, "pathDrift"),
            "endpointDistance": compact_distance_value(&signature_distance, "endpointDistance")
        },
        "unmeasuredAxes": json_string_array(
            string_vec_from_value(diagnostic_scope, "unmeasuredAxisRefs")
                .into_iter()
                .chain(string_vec_from_value(&signature_distance, "unmeasuredAxisRefs"))
        ),
        "topMovedAtoms": top_atom_distance_rows(packet, 6),
        "topMovedAxes": top_signature_axis_distance_rows(packet, 6),
        "safeMargin": compact_distance_value(&signature_distance, "safeRegionMargin"),
        "repairDistance": {
            "operationRef": json_field(&operation_distance, "operationRef"),
            "operationCost": compact_distance_value(&operation_distance, "operationCost"),
            "targetDistanceDecrease": compact_distance_value(&operation_distance, "targetDistanceDecrease"),
            "sideEffectBound": compact_distance_value(&operation_distance, "sideEffectBound")
        },
        "curvatureDistance": {
            "readingId": json_field(&curvature_distance, "readingId"),
            "curvatureMass": compact_distance_value(&curvature_distance, "curvatureMass"),
            "transportDistance": compact_distance_value(&curvature_distance, "transportDistance")
        },
        "homotopyDistance": {
            "readingId": json_field(&homotopy_distance, "homotopyDistanceReadingId"),
            "homotopyDistance": compact_distance_value(&homotopy_distance, "homotopyDistance"),
            "fillingCost": compact_distance_value(&homotopy_distance, "fillingCost"),
            "observationGapLowerBound": compact_distance_value(&homotopy_distance, "observationGapLowerBound")
        },
        "representationMetric": representation_metric_distance_rows(packet, 6),
        "detailRefs": [
            packet_ref("/part4DistanceFoundation"),
            packet_ref("/atomDistanceReadings"),
            packet_ref("/signatureDistanceReadings"),
            packet_ref("/operationDistanceReadings"),
            packet_ref("/curvatureMassReadings"),
            packet_ref("/homotopyDistanceReadings"),
            packet_ref("/representationMetricReadings")
        ],
        "distanceBoundary": "diagnostic distance is computed from Part IV evaluators over ArchMap + LawPolicy evidence; viewer layout distance is a separate visual projection and is not a diagnostic metric",
        "nonClaims": [
            "distance diagnosis is not a single architecture quality score",
            "blocked or unmeasured distance is not measured zero",
            "repair distance is not automatic repair safety",
            "representation metric does not certify global structural faithfulness"
        ]
    })
}

fn compact_distance_value(container: &serde_json::Value, key: &str) -> serde_json::Value {
    let value = container.get(key).unwrap_or(&serde_json::Value::Null);
    if value.is_null() {
        return serde_json::Value::Null;
    }
    serde_json::json!({
        "status": json_field(value, "status"),
        "measuredValue": json_field(value, "measuredValue"),
        "unit": json_field(value, "unit"),
        "provenanceRefSample": array_field_with_limit(value, "provenanceRefs", Some(3)),
        "coverageRefSample": array_field_with_limit(value, "coverageRefs", Some(3)),
        "blockerRefCount": array_len(value, "blockerRefs")
    })
}

fn top_atom_distance_rows(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut rows = array_items(packet, "atomDistanceReadings")
        .into_iter()
        .map(|reading| {
            let bundle = reading
                .get("atomLayoutDistanceBundle")
                .unwrap_or(&serde_json::Value::Null);
            serde_json::json!({
                "readingId": json_field(reading, "atomDistanceReadingId"),
                "sourceAtomRef": json_field(reading, "sourceAtomRef"),
                "targetAtomRef": json_field(reading, "targetAtomRef"),
                "bundle": compact_distance_value(reading, "atomLayoutDistanceBundle"),
                "statusRank": distance_status_rank(json_field(bundle, "status").as_str())
            })
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| {
        -row.get("statusRank")
            .and_then(serde_json::Value::as_i64)
            .unwrap_or_default()
    });
    serde_json::Value::Array(rows.into_iter().take(limit).collect())
}

fn top_signature_axis_distance_rows(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut rows = array_items(packet, "signatureDistanceReadings")
        .into_iter()
        .flat_map(|reading| array_items(reading, "axisDistances"))
        .map(|axis| {
            let axis_distance = axis.get("axisDistance").unwrap_or(&serde_json::Value::Null);
            serde_json::json!({
                "signatureAxisRef": json_field(axis, "signatureAxisRef"),
                "axisRef": json_field(axis, "axisRef"),
                "rhoI": compact_distance_value(axis, "rhoI"),
                "axisDistance": compact_distance_value(axis, "axisDistance"),
                "coverageStatus": json_field(axis, "coverageStatus"),
                "sourceRefCount": array_len(axis, "sourceRefs"),
                "blockerRefCount": array_len(axis, "blockerRefs"),
                "statusRank": distance_status_rank(json_field(axis_distance, "status").as_str())
            })
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| {
        -row.get("statusRank")
            .and_then(serde_json::Value::as_i64)
            .unwrap_or_default()
    });
    serde_json::Value::Array(rows.into_iter().take(limit).collect())
}

fn representation_metric_distance_rows(
    packet: &serde_json::Value,
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "representationMetricReadings")
            .into_iter()
            .take(limit)
            .map(|reading| {
                serde_json::json!({
                    "readingId": json_field(reading, "representationMetricReadingId"),
                    "representationFamily": json_field(reading, "representationFamily"),
                    "structuralDistance": compact_distance_value(reading, "structuralDistance"),
                    "analyticDistance": compact_distance_value(reading, "analyticDistance"),
                    "lipschitzStability": compact_distance_value(reading, "lipschitzStability"),
                    "biLipschitzFaithfulness": compact_distance_value(reading, "biLipschitzFaithfulness"),
                    "part4DistanceRefs": array_field_with_limit(reading, "part4DistanceRefs", Some(6))
                })
            })
            .collect(),
    )
}

fn distance_status_rank(status: Option<&str>) -> i64 {
    match status.unwrap_or_default() {
        "measured" => 50,
        "zero" => 40,
        "partial" => 35,
        "blocked" | "blockedByCoverageGap" => 30,
        "unmeasured" => 20,
        "unavailable" | "incomparable" | "infinite" => 10,
        _ => 0,
    }
}

fn measurement_status_summary(packet: &serde_json::Value) -> serde_json::Value {
    let mut measured = 0usize;
    let mut partial = 0usize;
    let mut proxy = 0usize;
    let mut unmeasured = 0usize;
    let mut blocked = 0usize;
    let mut schema_foundation_only = 0usize;

    for value in [
        json_field(packet, "architectureSpectrumReport"),
        json_field(packet, "architectureHomotopyReport"),
    ] {
        classify_measurement_status(
            json_field(&value, "measurementStatus").as_str(),
            &mut measured,
            &mut partial,
            &mut proxy,
            &mut unmeasured,
            &mut blocked,
            &mut schema_foundation_only,
        );
    }
    for family_key in ["monodromyReadingFamily", "boundaryHolonomyReadingFamily"] {
        let family = packet.get(family_key).unwrap_or(&serde_json::Value::Null);
        classify_measurement_status(
            json_field(family, "status").as_str(),
            &mut measured,
            &mut partial,
            &mut proxy,
            &mut unmeasured,
            &mut blocked,
            &mut schema_foundation_only,
        );
    }
    for array_key in [
        "curvatureSupportReadings",
        "curvatureTransferReadings",
        "fillerCandidateReadings",
        "architecturalHoleReadings",
        "homotopyHolonomyReadings",
        "stokesStyleReadings",
        "axisWiseMonodromyDefects",
        "amiAggregateReadings",
    ] {
        for item in array_items(packet, array_key) {
            classify_measurement_status(
                json_field(item, "measurementStatus").as_str(),
                &mut measured,
                &mut partial,
                &mut proxy,
                &mut unmeasured,
                &mut blocked,
                &mut schema_foundation_only,
            );
            classify_measurement_status(
                json_field(&json_field(item, "readingBoundary"), "readingStrength").as_str(),
                &mut measured,
                &mut partial,
                &mut proxy,
                &mut unmeasured,
                &mut blocked,
                &mut schema_foundation_only,
            );
        }
    }
    for item in array_items(packet, "representationStrengthReadings") {
        for field in [
            "zeroPreserving",
            "zeroReflecting",
            "obstructionPreserving",
            "obstructionReflecting",
            "aggregateZeroSafety",
            "cancellationRisk",
        ] {
            classify_measurement_status(
                json_field(item, field).as_str(),
                &mut measured,
                &mut partial,
                &mut proxy,
                &mut unmeasured,
                &mut blocked,
                &mut schema_foundation_only,
            );
        }
    }

    serde_json::json!({
        "measuredCount": measured,
        "partialCount": partial,
        "proxyCount": proxy,
        "unmeasuredCount": unmeasured,
        "blockedCount": blocked,
        "schemaFoundationOnlyCount": schema_foundation_only,
        "claimBoundary": "measured counts require evaluator/source refs; proxy and schema-only rows are not measured claims"
    })
}

#[allow(clippy::too_many_arguments)]
fn classify_measurement_status(
    value: Option<&str>,
    measured: &mut usize,
    partial: &mut usize,
    proxy: &mut usize,
    unmeasured: &mut usize,
    blocked: &mut usize,
    schema_foundation_only: &mut usize,
) {
    let Some(value) = value else {
        return;
    };
    let normalized = value.to_ascii_lowercase();
    if normalized == "measured" || normalized.starts_with("boundedmeasured") {
        *measured += 1;
    } else if normalized == "partial" {
        *partial += 1;
    } else if normalized == "schemafoundationonly" {
        *schema_foundation_only += 1;
    } else if normalized.contains("proxy") {
        *proxy += 1;
    } else if normalized.contains("unmeasured") {
        *unmeasured += 1;
    } else if normalized.contains("blocked") || normalized.contains("gap") {
        *blocked += 1;
    }
}

fn trend_counts(packet: &serde_json::Value) -> serde_json::Value {
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
        "nonzeroAxisCount": array_len(flatness, "nonzeroSignatureAxisRefs"),
        "spectrumHotspotCount": array_len(spectrum, "topHotspots"),
        "recurrentObstructionCount": array_len(spectrum, "recurrentObstructions"),
        "bridgePressureCount": bridge_pressure_action_count(packet),
        "architecturalHoleCount": array_len(homotopy, "unfilledLoops"),
        "nonzeroHolonomyLoopCount": array_len(homotopy, "nonzeroHolonomyLoops"),
        "pathMultiplicityLossCount": array_len(packet, "pathMultiplicityLossReadings"),
        "projectionFidelityLossCount": array_len(packet, "observationProjectionFidelityReadings"),
        "atomOriginClosureDebtCount": array_len(packet, "atomOriginClosureDebtReadings"),
        "coverageGapCount": coverage_gap_refs(packet).len()
    })
}

const ACTION_QUEUE_HOTSPOT_LIMIT: usize = 8;
const ACTION_QUEUE_HOMOTOPY_LIMIT: usize = 4;
const ACTION_QUEUE_AXIS_LIMIT: usize = 8;
const ACTION_QUEUE_BRIDGE_LIMIT: usize = 4;

fn action_queue(packet: &serde_json::Value) -> serde_json::Value {
    let mut actions = Vec::new();
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);

    for (index, hotspot) in array_items(spectrum, "topHotspots")
        .into_iter()
        .enumerate()
        .take(ACTION_QUEUE_HOTSPOT_LIMIT)
    {
        actions.push(serde_json::json!({
            "kind": "spectrumHotspot",
            "conclusion": "measuredPressureHotspot",
            "ref": json_field(hotspot, "hotspotId"),
            "axisRef": json_field(hotspot, "axisRef"),
            "score": json_field(hotspot, "curvatureValue"),
            "recommendedAction": json_field(hotspot, "recommendedNextAction"),
            "detailRefs": detail_refs("architectureSpectrumReport.topHotspots", &format!("/architectureSpectrumReport/topHotspots/{index}"))
        }));
    }
    for (index, loop_ref) in array_items(homotopy, "unfilledLoops")
        .into_iter()
        .enumerate()
        .take(ACTION_QUEUE_HOMOTOPY_LIMIT)
    {
        actions.push(serde_json::json!({
            "kind": "architecturalHole",
            "conclusion": "unfilledLoopMeasured",
            "ref": loop_ref.clone(),
            "recommendedAction": "inspect packet loop detail and add contract, test, runtime, policy, or source-backed filler evidence",
            "detailRefs": detail_refs("architectureHomotopyReport.unfilledLoops", &format!("/architectureHomotopyReport/unfilledLoops/{index}"))
        }));
    }
    for (index, loop_ref) in array_items(homotopy, "nonzeroHolonomyLoops")
        .into_iter()
        .enumerate()
        .take(ACTION_QUEUE_HOMOTOPY_LIMIT)
    {
        actions.push(serde_json::json!({
            "kind": "nonzeroHolonomy",
            "conclusion": "nonzeroSelectedAxisContinuationDistance",
            "ref": loop_ref.clone(),
            "recommendedAction": "compare selected path continuations in packet detail and decide whether the loop needs filler evidence or design change",
            "detailRefs": detail_refs("architectureHomotopyReport.nonzeroHolonomyLoops", &format!("/architectureHomotopyReport/nonzeroHolonomyLoops/{index}"))
        }));
    }
    for (index, axis) in array_items(packet, "signatureAxes")
        .into_iter()
        .enumerate()
        .filter(|(_, axis)| i64_field(axis, "value", 0) != 0)
        .take(ACTION_QUEUE_AXIS_LIMIT)
    {
        actions.push(serde_json::json!({
            "kind": "nonzeroSignatureAxis",
            "conclusion": "nonzeroAxisUnderSelectedPolicy",
            "ref": json_field(axis, "signatureAxisId"),
            "lawRef": json_field(axis, "lawRef"),
            "score": json_field(axis, "value"),
            "coverageStatus": json_field(axis, "coverageStatus"),
            "sourceRefCount": ref_count(axis, "sourceRefs"),
            "missingEvidenceCount": array_len(axis, "missingEvidence"),
            "recommendedAction": "inspect packet detail for source refs and selected law witness support",
            "detailRefs": detail_refs("signatureAxes", &format!("/signatureAxes/{index}"))
        }));
    }
    for action in aat_observation_axis_actions(packet) {
        actions.push(action);
    }
    for bridge in bridge_pressure_actions(packet)
        .into_iter()
        .take(ACTION_QUEUE_BRIDGE_LIMIT)
    {
        actions.push(bridge);
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

fn aat_observation_axis_actions(packet: &serde_json::Value) -> Vec<serde_json::Value> {
    let mut actions = Vec::new();
    for (index, reading) in array_items(packet, "observationProjectionFidelityReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "projectionFidelityLoss",
            "conclusion": json_field(reading, "fidelityStatus"),
            "ref": json_field(reading, "readingId"),
            "score": array_len(reading, "projectionLossAxes") + i64_field(reading, "forgottenCoordinateCount", 0).max(0) as usize,
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("observationProjectionFidelityReadings", &format!("/observationProjectionFidelityReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "atomOriginClosureDebtReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "atomOriginClosureDebt",
            "conclusion": json_field(reading, "closureStatus"),
            "ref": json_field(reading, "readingId"),
            "score": i64_field(reading, "derivedOrInferredAtomCount", 0).max(0) as usize
                + i64_field(reading, "expectedMissingAtomCount", 0).max(0) as usize,
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("atomOriginClosureDebtReadings", &format!("/atomOriginClosureDebtReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "effectRelationAlgebraReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "effectRelationPressure",
            "conclusion": json_field(reading, "effectOrderingPressure"),
            "ref": json_field(reading, "readingId"),
            "score": array_len(reading, "unresolvedEffectRelations") + array_len(reading, "externalBoundaryRefs"),
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("effectRelationAlgebraReadings", &format!("/effectRelationAlgebraReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "synthesisBlockageReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "synthesisBlockage",
            "conclusion": json_field(reading, "blockageStatus"),
            "ref": json_field(reading, "readingId"),
            "score": array_len(reading, "constraintRefs") + array_len(reading, "missingEvidenceRefs"),
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("synthesisBlockageReadings", &format!("/synthesisBlockageReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "operationPreconditionReadinessReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "operationPreconditionReadiness",
            "conclusion": json_field(reading, "readinessStatus"),
            "ref": json_field(reading, "operationRef"),
            "score": array_len(reading, "missingPreconditionRefs") + array_len(reading, "coverageGapRefs") + array_len(reading, "witnessGapRefs"),
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("operationPreconditionReadinessReadings", &format!("/operationPreconditionReadinessReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "pathMultiplicityLossReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "pathMultiplicityLoss",
            "conclusion": json_field(reading, "multiplicityLossStatus"),
            "ref": json_field(reading, "readingId"),
            "score": i64_field(reading, "alternatePathPressure", 0).max(0) as usize + array_len(reading, "fanInBoundaryRefs"),
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("pathMultiplicityLossReadings", &format!("/pathMultiplicityLossReadings/{index}"))
        }));
    }
    actions
}

fn bridge_pressure_actions(packet: &serde_json::Value) -> Vec<serde_json::Value> {
    let mut actions = Vec::new();
    for (reading_index, reading) in array_items(packet, "transferBridgeReadings")
        .into_iter()
        .enumerate()
    {
        for (bridge_index, bridge) in array_items(reading, "bridgeAtomFamilies")
            .into_iter()
            .enumerate()
        {
            let review_risk = bridge
                .get("reviewRisk")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("");
            let bridge_score = i64_field(bridge, "bridgeScore", 0);
            if review_risk == "high" || bridge_score > 0 {
                let path = format!(
                    "/transferBridgeReadings/{reading_index}/bridgeAtomFamilies/{bridge_index}"
                );
                actions.push(serde_json::json!({
                    "kind": "bridgePressure",
                    "conclusion": "transferBridgePressure",
                    "ref": json_field(bridge, "bridgeId"),
                    "score": json_field(bridge, "bridgeScore"),
                    "reviewRisk": json_field(bridge, "reviewRisk"),
                    "recommendedAction": json_field(bridge, "recommendedBoundaryPreparation"),
                    "detailRefs": detail_refs("transferBridgeReadings.bridgeAtomFamilies", &path)
                }));
            }
        }
    }
    actions
}

fn axis_summary(packet: &serde_json::Value) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "selectedAxisCount": array_len(packet, "signatureAxes"),
        "nonzeroAxisCount": array_len(flatness, "nonzeroSignatureAxisRefs"),
        "zeroAxisCount": array_len(flatness, "zeroSignatureAxisRefs"),
        "nonzeroAxes": nonzero_axis_findings(packet, usize::MAX),
        "packetRefs": packet_refs(&["/signatureAxes", "/flatnessReading"])
    })
}

fn aat_observation_axis_summary(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "projectionFidelityLossCount": array_len(packet, "observationProjectionFidelityReadings"),
        "atomOriginClosureDebtCount": array_len(packet, "atomOriginClosureDebtReadings"),
        "effectRelationPressureCount": array_len(packet, "effectRelationAlgebraReadings"),
        "synthesisBlockageCount": array_len(packet, "synthesisBlockageReadings"),
        "operationPreconditionReadinessCount": array_len(packet, "operationPreconditionReadinessReadings"),
        "pathMultiplicityLossCount": array_len(packet, "pathMultiplicityLossReadings"),
        "packetRefs": packet_refs(&[
            "/observationProjectionFidelityReadings",
            "/atomOriginClosureDebtReadings",
            "/effectRelationAlgebraReadings",
            "/synthesisBlockageReadings",
            "/operationPreconditionReadinessReadings",
            "/pathMultiplicityLossReadings"
        ])
    })
}

fn nonzero_axis_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "signatureAxes")
            .into_iter()
            .enumerate()
            .filter(|(_, axis)| i64_field(axis, "value", 0) != 0)
            .take(limit)
            .map(|(index, axis)| {
                serde_json::json!({
                    "ref": json_field(axis, "signatureAxisId"),
                    "lawRef": json_field(axis, "lawRef"),
                    "axisRef": json_field(axis, "axisRef"),
                    "score": json_field(axis, "value"),
                    "coverageStatus": json_field(axis, "coverageStatus"),
                    "missingEvidenceCount": array_len(axis, "missingEvidence"),
                    "sourceRefCount": ref_count(axis, "sourceRefs"),
                    "detailRefs": detail_refs("signatureAxes", &format!("/signatureAxes/{index}")),
                    "packetRefs": packet_refs(&[&format!("/signatureAxes/{index}")])
                })
            })
            .collect(),
    )
}

fn design_principle_summary(packet: &serde_json::Value) -> serde_json::Value {
    let mut status_counts = BTreeMap::<String, usize>::new();
    let items = array_items(packet, "designPrincipleReadings")
        .into_iter()
        .map(|reading| {
            let status = json_field(reading, "status")
                .as_str()
                .unwrap_or("unknown")
                .to_string();
            *status_counts.entry(status.clone()).or_default() += 1;
            serde_json::json!({
                "principle": json_field(reading, "principle"),
                "status": status,
                "witnessRuleRef": json_field(reading, "witnessRuleRef"),
                "witnessStatus": json_field(reading, "witnessStatus"),
                "evidenceRefCount": array_len(reading, "witnessEvidenceRefs"),
                "sourceRefCount": ref_count(reading, "sourceRefs"),
                "obstructionRefCount": array_len(reading, "obstructionRefs"),
                "recommendedNextAction": json_field(reading, "recommendedNextAction")
            })
        })
        .collect::<Vec<_>>();
    serde_json::json!({
        "statusCounts": status_counts,
        "items": items,
        "claimBoundary": "design principles are principle-specific witness readings, not static lint rules or theorem proofs"
    })
}

fn architectural_hole_summary(packet: &serde_json::Value) -> serde_json::Value {
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "architecturalHoleCount": array_len(homotopy, "unfilledLoops"),
        "nonzeroHolonomyLoopCount": array_len(homotopy, "nonzeroHolonomyLoops"),
        "localCurvatureCellCount": array_len(homotopy, "topLocalCurvatureCells"),
        "unfilledLoopExamples": loop_ref_findings(
            homotopy,
            "unfilledLoops",
            "/architectureHomotopyReport/unfilledLoops",
            "unfilledLoopMeasured",
            DOMINANT_FINDING_LIMIT
        ),
        "nonzeroHolonomyExamples": loop_ref_findings(
            homotopy,
            "nonzeroHolonomyLoops",
            "/architectureHomotopyReport/nonzeroHolonomyLoops",
            "nonzeroSelectedAxisContinuationDistance",
            DOMINANT_FINDING_LIMIT
        ),
        "packetRefs": packet_refs(&["/architectureHomotopyReport"])
    })
}

fn loop_ref_findings(
    container: &serde_json::Value,
    key: &str,
    base_path: &str,
    conclusion: &str,
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(container, key)
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, item)| {
                let path = format!("{base_path}/{index}");
                serde_json::json!({
                    "ref": item.clone(),
                    "conclusion": conclusion,
                    "detailRefs": detail_refs(key, &path),
                    "packetRefs": packet_refs(&[&path])
                })
            })
            .collect(),
    )
}

fn bridge_summary(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "transferBridgeReadingCount": array_len(packet, "transferBridgeReadings"),
        "bridgePressureCount": bridge_pressure_action_count(packet),
        "bridgePressure": bridge_pressure_findings(packet, DOMINANT_FINDING_LIMIT),
        "packetRefs": packet_refs(&["/transferBridgeReadings"])
    })
}

fn bridge_pressure_action_count(packet: &serde_json::Value) -> usize {
    bridge_pressure_actions(packet).len()
}

fn bridge_pressure_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        bridge_pressure_actions(packet)
            .into_iter()
            .take(limit)
            .map(|mut item| {
                if let Some(object) = item.as_object_mut() {
                    object.remove("kind");
                    object.remove("priority");
                }
                item
            })
            .collect(),
    )
}

fn hotspot_findings(spectrum: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(spectrum, "topHotspots")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, hotspot)| {
                serde_json::json!({
                    "ref": json_field(hotspot, "hotspotId"),
                    "axisRef": json_field(hotspot, "axisRef"),
                    "score": json_field(hotspot, "curvatureValue"),
                    "coverageGapCount": array_len(hotspot, "coverageGapRefs"),
                    "recommendedAction": json_field(hotspot, "recommendedNextAction"),
                    "detailRefs": detail_refs("architectureSpectrumReport.topHotspots", &format!("/architectureSpectrumReport/topHotspots/{index}")),
                    "packetRefs": packet_refs(&[&format!("/architectureSpectrumReport/topHotspots/{index}")])
                })
            })
            .collect(),
    )
}

fn recurrent_obstruction_findings(spectrum: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(spectrum, "recurrentObstructions")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "modeRef"),
                    "conclusion": "recurrentObstructionSupport",
                    "reading": json_field(reading, "reading"),
                    "transferEdgeCount": array_len(reading, "transferEdgeRefs"),
                    "detailRefs": detail_refs("architectureSpectrumReport.recurrentObstructions", &format!("/architectureSpectrumReport/recurrentObstructions/{index}")),
                    "packetRefs": packet_refs(&[&format!("/architectureSpectrumReport/recurrentObstructions/{index}")])
                })
            })
            .collect(),
    )
}

fn projection_fidelity_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "observationProjectionFidelityReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "fidelityStatus"),
                    "forgottenCoordinateCount": json_field(reading, "forgottenCoordinateCount"),
                    "collisionCount": json_field(reading, "observationCollisionCount"),
                    "reflectionStatus": json_field(reading, "reflectionStatus"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("observationProjectionFidelityReadings", &format!("/observationProjectionFidelityReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/observationProjectionFidelityReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn atom_origin_closure_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "atomOriginClosureDebtReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "closureStatus"),
                    "sourceBackedAtomCount": json_field(reading, "sourceBackedAtomCount"),
                    "derivedOrInferredAtomCount": json_field(reading, "derivedOrInferredAtomCount"),
                    "expectedMissingAtomCount": json_field(reading, "expectedMissingAtomCount"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("atomOriginClosureDebtReadings", &format!("/atomOriginClosureDebtReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/atomOriginClosureDebtReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn effect_relation_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "effectRelationAlgebraReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "effectOrderingPressure"),
                    "requiredRelationCount": array_len(reading, "requiredEffectRelations"),
                    "unresolvedRelationCount": array_len(reading, "unresolvedEffectRelations"),
                    "externalBoundaryCount": array_len(reading, "externalBoundaryRefs"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("effectRelationAlgebraReadings", &format!("/effectRelationAlgebraReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/effectRelationAlgebraReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn synthesis_blockage_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "synthesisBlockageReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "blockageStatus"),
                    "targetConstructionCount": array_len(reading, "targetConstructionRefs"),
                    "constraintCount": array_len(reading, "constraintRefs"),
                    "missingEvidenceCount": array_len(reading, "missingEvidenceRefs"),
                    "noSolutionCertificateStatus": json_field(reading, "noSolutionCertificateStatus"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("synthesisBlockageReadings", &format!("/synthesisBlockageReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/synthesisBlockageReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn operation_precondition_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "operationPreconditionReadinessReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "operationRef"),
                    "conclusion": json_field(reading, "readinessStatus"),
                    "operationKind": json_field(reading, "operationKind"),
                    "missingPreconditionCount": array_len(reading, "missingPreconditionRefs"),
                    "coverageGapCount": array_len(reading, "coverageGapRefs"),
                    "witnessGapCount": array_len(reading, "witnessGapRefs"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("operationPreconditionReadinessReadings", &format!("/operationPreconditionReadinessReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/operationPreconditionReadinessReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn path_multiplicity_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "pathMultiplicityLossReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "multiplicityLossStatus"),
                    "observedPathCount": json_field(reading, "observedPathCount"),
                    "alternatePathPressure": json_field(reading, "alternatePathPressure"),
                    "fanInBoundaryCount": array_len(reading, "fanInBoundaryRefs"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("pathMultiplicityLossReadings", &format!("/pathMultiplicityLossReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/pathMultiplicityLossReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn coverage_gap_summary(packet: &serde_json::Value) -> serde_json::Value {
    let refs = coverage_gap_refs(packet);
    serde_json::json!({
        "coverageGapCount": refs.len(),
        "gapRefs": json_string_array(refs.iter()),
        "packetRefs": packet_refs(&[
            "/flatnessReading/blockedByCoverageGaps",
            "/architectureSpectrumReport/coverageGaps",
            "/architectureHomotopyReport/coverageGaps"
        ])
    })
}

fn detail_index(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "packetRefSyntax": "packet:<json-pointer>",
        "sections": [
            detail_index_section("signatureAxes", "/signatureAxes", array_len(packet, "signatureAxes")),
            detail_index_section("part4DistanceFoundation", "/part4DistanceFoundation", object_key_count(packet, "part4DistanceFoundation")),
            detail_index_section("atomDistanceReadings", "/atomDistanceReadings", array_len(packet, "atomDistanceReadings")),
            detail_index_section("configurationDistanceReadings", "/configurationDistanceReadings", array_len(packet, "configurationDistanceReadings")),
            detail_index_section("signatureDistanceReadings", "/signatureDistanceReadings", array_len(packet, "signatureDistanceReadings")),
            detail_index_section("operationDistanceReadings", "/operationDistanceReadings", array_len(packet, "operationDistanceReadings")),
            detail_index_section("curvatureMassReadings", "/curvatureMassReadings", array_len(packet, "curvatureMassReadings")),
            detail_index_section("homotopyDistanceReadings", "/homotopyDistanceReadings", array_len(packet, "homotopyDistanceReadings")),
            detail_index_section("representationMetricReadings", "/representationMetricReadings", array_len(packet, "representationMetricReadings")),
            detail_index_section("architectureSpectrumReport.topHotspots", "/architectureSpectrumReport/topHotspots", array_len(packet.get("architectureSpectrumReport").unwrap_or(&serde_json::Value::Null), "topHotspots")),
            detail_index_section("architectureSpectrumReport.recurrentObstructions", "/architectureSpectrumReport/recurrentObstructions", array_len(packet.get("architectureSpectrumReport").unwrap_or(&serde_json::Value::Null), "recurrentObstructions")),
            detail_index_section("architectureHomotopyReport.unfilledLoops", "/architectureHomotopyReport/unfilledLoops", array_len(packet.get("architectureHomotopyReport").unwrap_or(&serde_json::Value::Null), "unfilledLoops")),
            detail_index_section("architectureHomotopyReport.nonzeroHolonomyLoops", "/architectureHomotopyReport/nonzeroHolonomyLoops", array_len(packet.get("architectureHomotopyReport").unwrap_or(&serde_json::Value::Null), "nonzeroHolonomyLoops")),
            detail_index_section("transferBridgeReadings", "/transferBridgeReadings", array_len(packet, "transferBridgeReadings")),
            detail_index_section("observationProjectionFidelityReadings", "/observationProjectionFidelityReadings", array_len(packet, "observationProjectionFidelityReadings")),
            detail_index_section("atomOriginClosureDebtReadings", "/atomOriginClosureDebtReadings", array_len(packet, "atomOriginClosureDebtReadings")),
            detail_index_section("effectRelationAlgebraReadings", "/effectRelationAlgebraReadings", array_len(packet, "effectRelationAlgebraReadings")),
            detail_index_section("synthesisBlockageReadings", "/synthesisBlockageReadings", array_len(packet, "synthesisBlockageReadings")),
            detail_index_section("operationPreconditionReadinessReadings", "/operationPreconditionReadinessReadings", array_len(packet, "operationPreconditionReadinessReadings")),
            detail_index_section("pathMultiplicityLossReadings", "/pathMultiplicityLossReadings", array_len(packet, "pathMultiplicityLossReadings")),
            detail_index_section("llmInterpretationPacket", "/llmInterpretationPacket", object_key_count(packet, "llmInterpretationPacket"))
        ]
    })
}

fn detail_index_section(name: &str, path: &str, count: usize) -> serde_json::Value {
    serde_json::json!({
        "name": name,
        "packetRef": packet_ref(path),
        "count": count
    })
}

fn detail_refs(_section: &str, path: &str) -> serde_json::Value {
    serde_json::json!([packet_ref(path)])
}

fn trend_insights(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "insightCount": 5,
        "items": [
            cross_axis_cooccurrence_insight(packet),
            operation_freedom_loss_insight(packet),
            path_continuation_defect_insight(packet),
            boundary_residual_localization_insight(packet),
            repair_transfer_risk_insight(packet)
        ]
    })
}

fn cross_axis_cooccurrence_insight(packet: &serde_json::Value) -> serde_json::Value {
    let mut clusters = support_contribution_clusters(packet);
    clusters.sort_by(|left, right| {
        right
            .kind_count
            .cmp(&left.kind_count)
            .then(right.evidence_count.cmp(&left.evidence_count))
            .then(left.support_ref.cmp(&right.support_ref))
    });
    let cluster = clusters.first();
    serde_json::json!({
        "kind": "crossAxisCooccurrence",
        "claim": if cluster.is_some() {
            "multiple readings concentrate on one architecture support"
        } else {
            "no cross-axis support cluster was measured"
        },
        "whyNontrivial": "Intersects law-axis, spectrum, homotopy, bridge, and operation support.",
        "measurement": {
            "clusterCount": clusters.len(),
            "maxReadingKindCount": cluster.map(|cluster| cluster.kind_count).unwrap_or_default()
        },
        "packetRefs": packet_refs(&[
            "/signatureAxes",
            "/architectureSpectrumReport/topHotspots",
            "/architectureHomotopyReport",
            "/transferBridgeReadings"
        ])
    })
}

#[derive(Debug)]
struct SupportCluster {
    support_ref: String,
    reading_kinds: BTreeSet<String>,
    evidence_refs: BTreeSet<String>,
    kind_count: usize,
    evidence_count: usize,
}

fn support_contribution_clusters(packet: &serde_json::Value) -> Vec<SupportCluster> {
    let mut clusters = BTreeMap::<String, SupportCluster>::new();
    for (index, axis) in array_items(packet, "signatureAxes").into_iter().enumerate() {
        if i64_field(axis, "value", 0) == 0 {
            continue;
        }
        let evidence_ref = format!("packet:/signatureAxes/{index}");
        for support in string_array(axis, "sourceRefs")
            .into_iter()
            .chain(optional_string(axis, "axisRef"))
            .chain(optional_string(axis, "lawRef"))
        {
            push_support_contribution(
                &mut clusters,
                "nonzeroSignatureAxis",
                &support,
                &evidence_ref,
            );
        }
    }

    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    for (index, hotspot) in array_items(spectrum, "topHotspots").into_iter().enumerate() {
        let evidence_ref = format!("packet:/architectureSpectrumReport/topHotspots/{index}");
        for support in string_array(hotspot, "supportRefs")
            .into_iter()
            .chain(string_array(hotspot, "witnessRefs"))
            .chain(optional_string(hotspot, "axisRef"))
        {
            push_support_contribution(&mut clusters, "spectrumHotspot", &support, &evidence_ref);
        }
    }
    for (index, recurrent) in array_items(spectrum, "recurrentObstructions")
        .into_iter()
        .enumerate()
    {
        let evidence_ref = format!("/architectureSpectrumReport/recurrentObstructions/{index}");
        for support in string_array(recurrent, "supportRefs")
            .into_iter()
            .chain(string_array(recurrent, "witnessRefs"))
            .chain(optional_string(recurrent, "modeRef"))
        {
            push_support_contribution(
                &mut clusters,
                "recurrentObstruction",
                &support,
                &format!("packet:{evidence_ref}"),
            );
        }
    }

    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    for (index, loop_ref) in array_items(homotopy, "unfilledLoops")
        .into_iter()
        .enumerate()
    {
        if let Some(support) = loop_ref.as_str() {
            push_support_contribution(
                &mut clusters,
                "architecturalHole",
                support,
                &format!("packet:/architectureHomotopyReport/unfilledLoops/{index}"),
            );
        }
    }
    for (index, loop_ref) in array_items(homotopy, "nonzeroHolonomyLoops")
        .into_iter()
        .enumerate()
    {
        if let Some(support) = loop_ref.as_str() {
            push_support_contribution(
                &mut clusters,
                "nonzeroHolonomy",
                support,
                &format!("packet:/architectureHomotopyReport/nonzeroHolonomyLoops/{index}"),
            );
        }
    }

    for (reading_index, reading) in array_items(packet, "transferBridgeReadings")
        .into_iter()
        .enumerate()
    {
        for (bridge_index, bridge) in array_items(reading, "bridgeAtomFamilies")
            .into_iter()
            .enumerate()
        {
            let evidence_ref = format!(
                "packet:/transferBridgeReadings/{reading_index}/bridgeAtomFamilies/{bridge_index}"
            );
            for support in optional_string(bridge, "sourceHubMoleculeRef")
                .chain(optional_string(bridge, "targetHubMoleculeRef"))
                .chain(string_array(bridge, "intermediateMoleculeRefs"))
                .chain(
                    string_array(bridge, "sharedAxisRefs")
                        .into_iter()
                        .map(|axis| format!("axis:{axis}")),
                )
            {
                push_support_contribution(&mut clusters, "bridgePressure", &support, &evidence_ref);
            }
        }
    }

    clusters
        .into_values()
        .filter_map(|mut cluster| {
            cluster.kind_count = cluster.reading_kinds.len();
            cluster.evidence_count = cluster.evidence_refs.len();
            (cluster.kind_count >= 2 && cluster.evidence_count >= 2).then_some(cluster)
        })
        .collect()
}

fn push_support_contribution(
    clusters: &mut BTreeMap<String, SupportCluster>,
    kind: &str,
    support_ref: &str,
    evidence_ref: &str,
) {
    let normalized = normalize_support_ref(support_ref);
    if normalized.is_empty() {
        return;
    }
    let cluster = clusters
        .entry(normalized.clone())
        .or_insert(SupportCluster {
            support_ref: normalized,
            reading_kinds: BTreeSet::new(),
            evidence_refs: BTreeSet::new(),
            kind_count: 0,
            evidence_count: 0,
        });
    cluster.reading_kinds.insert(kind.to_string());
    cluster.evidence_refs.insert(evidence_ref.to_string());
}

fn normalize_support_ref(value: &str) -> String {
    let trimmed = value.trim();
    let normalized = trimmed
        .strip_prefix("molecule-reading:")
        .map(|value| format!("molecule:{value}"))
        .unwrap_or_else(|| trimmed.to_string());
    normalized
        .replace("axis-", "axis:")
        .replace("law-", "law:")
        .to_ascii_lowercase()
}

fn operation_freedom_loss_insight(packet: &serde_json::Value) -> serde_json::Value {
    let galois = array_items(packet, "operationInvariantGaloisReadings")
        .into_iter()
        .next();
    let blocked_operation_refs = galois
        .map(|reading| string_array(reading, "blockedOperationRefs"))
        .unwrap_or_default();
    let blocked_operations = blocked_operation_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let blocked_preconditions = array_items(packet, "operationPreconditionReadinessReadings")
        .into_iter()
        .filter(|reading| {
            reading
                .get("operationRef")
                .and_then(serde_json::Value::as_str)
                .is_some_and(|operation| blocked_operations.contains(operation))
                || json_field(reading, "readinessStatus")
                    .as_str()
                    .is_some_and(|status| status.contains("blocked"))
        })
        .collect::<Vec<_>>();
    let missing_precondition_count = blocked_preconditions
        .iter()
        .map(|reading| array_len(reading, "missingPreconditionRefs"))
        .sum::<usize>();
    serde_json::json!({
        "kind": "operationFreedomLoss",
        "claim": if blocked_operation_refs.is_empty() && missing_precondition_count == 0 {
            "no operation freedom loss was measured for the selected invariant family"
        } else {
            "selected invariants narrow the observed operation family"
        },
        "whyNontrivial": "Intersects Galois reading, preconditions, and transfer evidence.",
        "measurement": {
            "blockedOperationCount": blocked_operation_refs.len(),
            "missingPreconditionCount": missing_precondition_count
        },
        "packetRefs": packet_refs(&["/operationInvariantGaloisReadings"])
    })
}

fn path_continuation_defect_insight(packet: &serde_json::Value) -> serde_json::Value {
    let mut defects = array_items(packet, "axisWiseMonodromyDefects");
    defects.sort_by_key(|defect| {
        std::cmp::Reverse(
            defect
                .get("distanceValue")
                .and_then(serde_json::Value::as_i64)
                .unwrap_or(-1),
        )
    });
    let top_defect = defects.iter().find(|defect| {
        defect
            .get("distanceValue")
            .and_then(serde_json::Value::as_i64)
            .is_some_and(|value| value > 0)
    });
    let positive_defect_count = defects
        .iter()
        .filter(|defect| {
            defect
                .get("distanceValue")
                .and_then(serde_json::Value::as_i64)
                .is_some_and(|value| value > 0)
        })
        .count();
    let unmeasured_defect_count = defects
        .iter()
        .filter(|defect| json_field(defect, "measurementStatus").as_str() == Some("unmeasured"))
        .count();
    serde_json::json!({
        "kind": "pathContinuationDefect",
        "claim": if top_defect.is_some() {
            "same-endpoint candidates diverge on a selected continuation axis"
        } else if unmeasured_defect_count > 0 {
            "path continuation cannot be read as zero because selected axes remain unmeasured"
        } else {
            "no nonzero selected-axis continuation defect was measured"
        },
        "whyNontrivial": "Compares p/q continuation traces axis by axis.",
        "measurement": {
            "positiveDefectCount": positive_defect_count,
            "unmeasuredDefectCount": unmeasured_defect_count,
            "topAxisFamily": top_defect.and_then(|defect| defect.get("axisFamily").and_then(serde_json::Value::as_str)).unwrap_or("none")
        },
        "packetRefs": packet_refs(&["/axisWiseMonodromyDefects"])
    })
}

fn boundary_residual_localization_insight(packet: &serde_json::Value) -> serde_json::Value {
    let residual = array_items(packet, "featureBoundaryResidualReadings")
        .into_iter()
        .max_by_key(|reading| {
            array_items(reading, "holonomyAxes")
                .into_iter()
                .filter_map(|axis| {
                    axis.get("residualValue")
                        .and_then(serde_json::Value::as_i64)
                })
                .sum::<i64>()
        });
    let measured_axis_refs = residual
        .map(|reading| {
            array_items(reading, "holonomyAxes")
                .into_iter()
                .filter(|axis| json_field(axis, "status").as_str() == Some("measuredResidual"))
                .filter_map(|axis| {
                    axis.get("holonomyAxisRef")
                        .and_then(serde_json::Value::as_str)
                })
                .map(str::to_string)
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let coverage_blocked_count = residual
        .map(|reading| {
            array_items(reading, "holonomyAxes")
                .into_iter()
                .filter(|axis| json_field(axis, "status").as_str() == Some("coverageBlocked"))
                .count()
        })
        .unwrap_or_default();
    let boundary_support_count = residual
        .map(|reading| array_len(reading, "boundarySupportRefs"))
        .unwrap_or_default();
    serde_json::json!({
        "kind": "boundaryResidualLocalization",
        "claim": if !measured_axis_refs.is_empty() {
            "residual obstruction localizes on boundary holonomy axes"
        } else if coverage_blocked_count > 0 {
            "boundary residual localization is blocked by missing selected-axis evidence"
        } else {
            "no boundary-local residual obstruction was measured"
        },
        "whyNontrivial": "Separates core, feature, boundary support, residual axes, and coverage.",
        "measurement": {
            "measuredBoundaryAxisCount": measured_axis_refs.len(),
            "coverageBlockedBoundaryAxisCount": coverage_blocked_count,
            "boundarySupportCount": boundary_support_count
        },
        "packetRefs": packet_refs(&["/featureBoundaryResidualReadings"])
    })
}

fn repair_transfer_risk_insight(packet: &serde_json::Value) -> serde_json::Value {
    let mut deltas = array_items(packet, "operationDeltas");
    deltas.sort_by_key(|delta| std::cmp::Reverse(array_len(delta, "transferredObstructions")));
    let delta = deltas.first().copied();
    let transfer_refs = delta
        .map(|delta| string_array(delta, "transferredObstructions"))
        .unwrap_or_default();
    let decreased_axes = delta
        .map(|delta| string_array(delta, "decreasedAxes"))
        .unwrap_or_default();
    let bridge_refs = array_items(packet, "bridgeSplitObstructionTransferReadings")
        .into_iter()
        .flat_map(|reading| {
            optional_string(reading, "readingId")
                .chain(string_array(reading, "bridgeEdgeRefs"))
                .chain(string_array(reading, "obstructionRefs"))
        })
        .collect::<Vec<_>>();
    serde_json::json!({
        "kind": "repairTransferRisk",
        "claim": if !transfer_refs.is_empty() {
            "candidate repair carries explicit transfer risk"
        } else if !bridge_refs.is_empty() {
            "repair planning depends on bridge-split obstruction transfer evidence"
        } else {
            "no repair transfer risk was measured"
        },
        "whyNontrivial": "Pairs decreased axes with transfer, invariants, bridges, and missing evidence.",
        "measurement": {
            "decreasesAxisCount": decreased_axes.len(),
            "transferRiskCount": transfer_refs.len(),
            "bridgeEvidenceCount": bridge_refs.len()
        },
        "packetRefs": packet_refs(&["/operationDeltas"])
    })
}

fn optional_string(value: &serde_json::Value, key: &str) -> std::vec::IntoIter<String> {
    value
        .get(key)
        .and_then(serde_json::Value::as_str)
        .map(|text| vec![text.to_string()])
        .unwrap_or_default()
        .into_iter()
}

fn compact_ref_list(
    container: &serde_json::Value,
    key: &str,
    ref_key: &str,
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(container, key)
            .into_iter()
            .take(limit)
            .filter_map(|item| {
                item.get(ref_key)
                    .and_then(serde_json::Value::as_str)
                    .map(|text| serde_json::Value::String(text.to_string()))
            })
            .collect(),
    )
}

fn nonzero_axis_ref_list(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "signatureAxes")
            .into_iter()
            .filter(|axis| i64_field(axis, "value", 0) != 0)
            .take(limit)
            .filter_map(|axis| {
                axis.get("signatureAxisId")
                    .and_then(serde_json::Value::as_str)
                    .map(|text| serde_json::Value::String(text.to_string()))
            })
            .collect(),
    )
}

fn bridge_pressure_ref_list(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        bridge_pressure_actions(packet)
            .into_iter()
            .take(limit)
            .filter_map(|reading| {
                reading
                    .get("ref")
                    .and_then(serde_json::Value::as_str)
                    .map(|text| serde_json::Value::String(text.to_string()))
            })
            .collect(),
    )
}

fn homotopy_ref_list(packet: &serde_json::Value, key: &str, limit: usize) -> serde_json::Value {
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::Value::Array(
        array_items(homotopy, key)
            .into_iter()
            .take(limit)
            .filter_map(|item| {
                item.as_str()
                    .map(|text| serde_json::Value::String(text.to_string()))
            })
            .collect(),
    )
}

fn array_len_keyless(value: &serde_json::Value) -> usize {
    value.as_array().map(Vec::len).unwrap_or_default()
}

fn packet_refs(paths: &[&str]) -> serde_json::Value {
    serde_json::Value::Array(
        paths
            .iter()
            .map(|path| serde_json::Value::String(packet_ref(path)))
            .collect(),
    )
}

fn packet_ref(path: &str) -> String {
    format!("packet:{path}")
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
        "monodromyFamily": reading_family_status_summary(packet, "monodromyReadingFamily"),
        "boundaryHolonomyFamily": reading_family_status_summary(packet, "boundaryHolonomyReadingFamily"),
        "spectrumMeasuredBoundary": json_field(spectrum, "measuredBoundary"),
        "homotopyMeasuredBoundary": json_field(homotopy, "measuredBoundary"),
        "projectionFidelityBoundary": first_string_field(packet, "observationProjectionFidelityReadings", "measurementBoundary"),
        "atomOriginBoundary": first_string_field(packet, "atomOriginClosureDebtReadings", "evidenceBoundary"),
        "effectRelationBoundary": first_string_field(packet, "effectRelationAlgebraReadings", "evidenceBoundary"),
        "synthesisBoundary": first_string_field(packet, "synthesisBlockageReadings", "synthesisBoundary"),
        "operationPreconditionBoundary": first_string_field(packet, "operationPreconditionReadinessReadings", "candidateBoundary"),
        "pathMultiplicityBoundary": first_string_field(packet, "pathMultiplicityLossReadings", "homotopyBoundary"),
        "basisStatement": "conclusions are measured from the supplied ArchMap and selected LawPolicy"
    })
}

fn reading_family_status_summary(
    packet: &serde_json::Value,
    family_key: &str,
) -> serde_json::Value {
    let family = packet.get(family_key).unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "status": json_field(family, "status"),
        "measuredAxisCount": json_field(family, "measuredAxisCount"),
        "unmeasuredAxisCount": json_field(family, "unmeasuredAxisCount"),
        "positiveWitnessCount": json_field(family, "positiveWitnessCount"),
        "coverageBlockerCount": json_field(family, "coverageBlockerCount")
    })
}

fn first_string_field(
    packet: &serde_json::Value,
    array_key: &str,
    field_key: &str,
) -> serde_json::Value {
    packet
        .get(array_key)
        .and_then(serde_json::Value::as_array)
        .and_then(|items| items.first())
        .and_then(|item| item.get(field_key))
        .cloned()
        .unwrap_or(serde_json::Value::Null)
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
        .map(normalize_gap_label)
        .or_else(|| {
            value
                .get("gapId")
                .and_then(serde_json::Value::as_str)
                .map(normalize_gap_label)
        })
        .or_else(|| {
            value
                .get("id")
                .and_then(serde_json::Value::as_str)
                .map(normalize_gap_label)
        })
        .or_else(|| {
            value
                .get("description")
                .and_then(serde_json::Value::as_str)
                .map(normalize_gap_label)
        })
}

fn normalize_gap_label(value: &str) -> String {
    let trimmed = value.trim();
    if let Some(rest) = trimmed.strip_prefix("gap:") {
        let parts = rest.split(':').take(2).collect::<Vec<_>>();
        if parts.len() == 2 && parts.iter().all(|part| !part.trim().is_empty()) {
            return format!("gap:{}:{}", parts[0].trim(), parts[1].trim());
        }
    }
    if let Some(rest) = trimmed.strip_prefix("coverage:") {
        let label = rest.split(':').next().unwrap_or("").trim();
        if !label.is_empty() {
            return format!("coverage:{label}");
        }
    }
    if let Some((id, _)) = trimmed.split_once(':') {
        let id = id.trim();
        if !id.contains(' ') && !id.is_empty() {
            return id.to_string();
        }
    }
    trimmed.to_string()
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
        "measurementStatus": json_field(report, "measurementStatus"),
        "readingBoundary": json_field(report, "readingBoundary"),
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
        "measurementStatus": json_field(report, "measurementStatus"),
        "readingBoundary": json_field(report, "readingBoundary"),
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

fn ref_count(value: &serde_json::Value, key: &str) -> usize {
    let Some(value) = value.get(key) else {
        return 0;
    };
    value
        .as_array()
        .map(Vec::len)
        .or_else(|| {
            value
                .get("refCount")
                .and_then(serde_json::Value::as_u64)
                .map(|count| count as usize)
        })
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
