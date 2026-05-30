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

        /// Maximum number of ranked readings to include.
        #[arg(long, default_value_t = 6)]
        limit: usize,

        /// Output summary JSON path. If omitted, JSON is written to stdout.
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
            limit,
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
                limit,
            );
            write_json(out, &summary)?;
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

fn build_analysis_summary(
    packet: &serde_json::Value,
    archmap_validation: Option<&serde_json::Value>,
    law_policy_validation: Option<&serde_json::Value>,
    analysis_validation: Option<&serde_json::Value>,
    limit: usize,
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
        "flatness": {
            "status": json_field(flatness, "status"),
            "zeroSignatureAxisRefs": array_field(flatness, "zeroSignatureAxisRefs"),
            "nonzeroSignatureAxisRefs": array_field(flatness, "nonzeroSignatureAxisRefs"),
            "blockedByCoverageGaps": array_field(flatness, "blockedByCoverageGaps")
        },
        "signatureAxes": signature_axis_summary(packet),
        "topWorkflowRisks": top_workflow_risks(packet, limit),
        "spectralAnalysis": spectral_summary(packet),
        "transferBridges": transfer_bridge_summary(packet),
        "measurementExpansion": measurement_expansion_summary(packet, llm_packet, limit),
        "splitReadiness": split_readiness_summary(packet, limit),
        "llmReviewIndex": {
            "structuralReadingReviewSummary": array_field(llm_packet, "structuralReadingReviewSummary"),
            "currentStateEvolutionBoundarySummary": array_field(llm_packet, "currentStateEvolutionBoundarySummary"),
            "recommendedHumanReviewFocus": limited_array_field(llm_packet, "recommendedHumanReviewFocus", limit),
            "transferBridgeEdgeSummary": array_field(llm_packet, "transferBridgeEdgeSummary")
        },
        "nonConclusions": array_field(packet, "nonConclusions")
    })
}

fn measurement_expansion_summary(
    packet: &serde_json::Value,
    llm_packet: &serde_json::Value,
    limit: usize,
) -> serde_json::Value {
    serde_json::json!({
        "summary": array_field(llm_packet, "measurementExpansionSummary"),
        "atomSupportAxis": limited_array_field(llm_packet, "atomSupportAxisSummary", limit),
        "atomCompatibility": limited_array_field(llm_packet, "atomCompatibilitySummary", limit),
        "lawUniverseCoverage": limited_array_field(llm_packet, "lawUniverseCoverageSummary", limit),
        "featureExtensionFormula": limited_array_field(llm_packet, "featureExtensionFormulaSummary", limit),
        "operationCalculusLaw": limited_array_field(llm_packet, "operationCalculusLawSummary", limit),
        "pathSignatureTrajectory": limited_array_field(llm_packet, "pathSignatureTrajectorySummary", limit),
        "homotopyOrderSensitivity": limited_array_field(llm_packet, "homotopyOrderSensitivitySummary", limit),
        "diagramFillability": limited_array_field(llm_packet, "diagramFillabilitySummary", limit),
        "axisForgettingRisk": limited_array_field(llm_packet, "axisForgettingRiskSummary", limit),
        "signatureTrajectoryHomotopyRefutation": limited_array_field(llm_packet, "signatureTrajectoryHomotopyRefutationSummary", limit),
        "bridgeSplitObstructionTransfer": limited_array_field(llm_packet, "bridgeSplitObstructionTransferSummary", limit),
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
            "bridgeSplitObstructionTransferReadings": array_len(packet, "bridgeSplitObstructionTransferReadings")
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

fn top_workflow_risks(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut readings = array_items(packet, "workflowRiskReadings");
    readings.sort_by_key(|reading| std::cmp::Reverse(i64_field(reading, "riskScore", 0)));
    serde_json::Value::Array(
        readings
            .into_iter()
            .take(limit)
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

fn split_readiness_summary(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut readings = array_items(packet, "splitReadinessReadings");
    readings.sort_by_key(|reading| i64_field(reading, "readinessScore", i64::MAX));
    serde_json::Value::Array(
        readings
            .into_iter()
            .take(limit)
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
