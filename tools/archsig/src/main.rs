use std::error::Error;
use std::path::PathBuf;
use std::process::ExitCode;

use archsig::{
    ARCHMAP_V1_SCHEMA, ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION, ArchMapDocumentV0,
    ArchMapDocumentV1, ArchMapSourceInventoryInput, ArchMapSourceInventoryV0,
    ArchMapValidationReportV0, LAW_POLICY_V1_SCHEMA, LawPolicyDocumentV0, LawPolicyDocumentV1,
    SchemaVersionCatalogV0, build_archsig_analysis_packet, static_law_policy,
    static_schema_version_catalog, validate_archmap_report, validate_archmap_v1_report,
    validate_archsig_analysis_packet_report, validate_law_policy_report,
    validate_law_policy_v1_report,
};
use clap::{Parser, Subcommand};

mod cli;
mod reports;
use cli::*;
use reports::*;

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

fn validate_archmap_command_input(
    input: &PathBuf,
) -> Result<(serde_json::Value, bool, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    if json_schema(&raw) == Some(ARCHMAP_V1_SCHEMA) {
        let document: ArchMapDocumentV1 = serde_json::from_value(raw)?;
        let report = validate_archmap_v1_report(&document, &input.display().to_string());
        let failed = report.summary.result == "fail";
        return Ok((serde_json::to_value(report)?, failed, true));
    }

    let document: ArchMapDocumentV0 = serde_json::from_value(raw)?;
    let source_inventory_path = document
        .source_inventory_ref
        .as_ref()
        .and_then(|source_inventory_ref| source_inventory_ref.path.as_deref());
    let mut source_inventory_document: Option<ArchMapSourceInventoryV0> = None;
    let mut source_inventory_error: Option<String> = None;
    if let Some(path) = source_inventory_path {
        match resolve_archmap_sidecar_path(input, path) {
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
    let report: ArchMapValidationReportV0 =
        validate_archmap_report(&document, &input.display().to_string(), source_inventory);
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed, false))
}

fn validate_law_policy_command_input(
    input: Option<&PathBuf>,
) -> Result<(serde_json::Value, bool, bool), Box<dyn Error>> {
    let Some(input) = input else {
        let policy = static_law_policy();
        let report = validate_law_policy_report(&policy, "static-law-policy");
        let failed = report.summary.result == "fail";
        return Ok((serde_json::to_value(report)?, failed, false));
    };

    let raw: serde_json::Value = read_json(input)?;
    if json_schema(&raw) == Some(LAW_POLICY_V1_SCHEMA) {
        let policy: LawPolicyDocumentV1 = serde_json::from_value(raw)?;
        let report = validate_law_policy_v1_report(&policy, &input.display().to_string());
        let failed = report.summary.result == "fail";
        return Ok((serde_json::to_value(report)?, failed, true));
    }

    let policy: LawPolicyDocumentV0 = serde_json::from_value(raw)?;
    let report = validate_law_policy_report(&policy, &input.display().to_string());
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed, false))
}

fn json_schema(document: &serde_json::Value) -> Option<&str> {
    document
        .get("schema")
        .or_else(|| document.get("schemaVersion"))
        .and_then(|value| value.as_str())
}

fn run() -> Result<ExitCode, Box<dyn Error>> {
    let args = Args::parse();

    match args.command {
        Some(Command::Archmap { input, out }) => {
            let (report, failed, _) = validate_archmap_command_input(&input)?;
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
            let (report, failed, _) = validate_law_policy_command_input(input.as_ref())?;
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

            let (archmap_preflight, archmap_failed, archmap_is_v1) =
                validate_archmap_command_input(&archmap)?;
            let (law_policy_preflight, law_policy_failed, law_policy_is_v1) =
                validate_law_policy_command_input(Some(&law_policy))?;
            if archmap_is_v1 || law_policy_is_v1 {
                std::fs::create_dir_all(&out_dir)?;
                remove_analyze_success_artifacts(&out_dir)?;
                write_json(Some(archmap_validation_path), &archmap_preflight)?;
                write_json(Some(law_policy_validation_path), &law_policy_preflight)?;
                eprintln!(
                    "archsig analyze wrote v1 validation artifacts to {} but the v1 evaluator pipeline is not implemented yet",
                    out_dir.display()
                );
                return Ok(if archmap_failed || law_policy_failed {
                    ExitCode::from(1)
                } else {
                    ExitCode::from(1)
                });
            }

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

fn remove_analyze_success_artifacts(out_dir: &PathBuf) -> Result<(), Box<dyn Error>> {
    for artifact in [
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
        "archsig-analysis-packet.json",
        "archsig-analysis-detail-index.json",
        "archsig-analysis-validation.json",
        "llm-interpretation-packet.json",
    ] {
        let path = out_dir.join(artifact);
        match std::fs::remove_file(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(Box::new(error)),
        }
    }
    Ok(())
}
