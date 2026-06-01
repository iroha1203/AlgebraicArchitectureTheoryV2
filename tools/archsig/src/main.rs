use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::File;
use std::hash::{Hash, Hasher};
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

        /// Optional compact LLM interpretation packet output path.
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
                write_json(Some(path), &packet.llm_interpretation_packet)?;
            }
            write_analysis_packet_artifacts(out, &packet, None)?;
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
            let analysis_detail_index_path = out_dir.join("archsig-analysis-detail-index.json");
            write_analysis_packet_artifacts(
                Some(analysis_packet_path.clone()),
                &analysis_packet,
                Some(analysis_detail_index_path),
            )?;
            write_json(
                Some(llm_interpretation_path),
                &analysis_packet.llm_interpretation_packet,
            )?;
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
        "measurementStatusSummary": measurement_status_summary(packet),
        "trendDiagnosis": trend_diagnosis(packet),
        "reviewSupport": review_support(packet),
        "dominantFindings": dominant_findings(packet),
        "actionQueue": action_queue(packet),
        "axisSummary": axis_summary(packet),
        "aatObservationAxisSummary": aat_observation_axis_summary(packet),
        "workflowRiskSummary": workflow_risk_summary(packet),
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
        "workflowRisks": workflow_risk_findings(packet, DOMINANT_FINDING_LIMIT),
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
            "workflowRiskRefs": workflow_risk_ref_list(packet, READING_MODE_FINDING_LIMIT),
            "bridgePressureRefs": bridge_pressure_ref_list(packet, READING_MODE_FINDING_LIMIT),
            "pathMultiplicityLossRefs": compact_ref_list(packet, "pathMultiplicityLossReadings", "readingId", 1),
            "projectionFidelityLossRefs": compact_ref_list(packet, "observationProjectionFidelityReadings", "readingId", 1),
            "atomOriginClosureDebtRefs": compact_ref_list(packet, "atomOriginClosureDebtReadings", "readingId", 1)
        },
        "trendInsights": trend_insights(packet),
        "packetRefs": packet_refs(&[
            "/signatureAxes",
            "/architectureSpectrumReport",
            "/workflowRiskReadings",
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
        "projectionFidelityLossCount": array_len(packet, "observationProjectionFidelityReadings"),
        "atomOriginClosureDebtCount": array_len(packet, "atomOriginClosureDebtReadings"),
        "effectRelationPressureCount": array_len(packet, "effectRelationAlgebraReadings"),
        "synthesisBlockageCount": array_len(packet, "synthesisBlockageReadings"),
        "operationPreconditionBlockerCount": array_len(packet, "operationPreconditionReadinessReadings"),
        "pathMultiplicityLossCount": array_len(packet, "pathMultiplicityLossReadings"),
        "coverageGapCount": coverage_gap_refs(packet).len()
    })
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
        "workflowRiskCount": array_len(packet, "workflowRiskReadings"),
        "bridgePressureCount": bridge_pressure_action_count(packet),
        "architecturalHoleCount": array_len(homotopy, "unfilledLoops"),
        "nonzeroHolonomyLoopCount": array_len(homotopy, "nonzeroHolonomyLoops"),
        "pathMultiplicityLossCount": array_len(packet, "pathMultiplicityLossReadings"),
        "projectionFidelityLossCount": array_len(packet, "observationProjectionFidelityReadings"),
        "atomOriginClosureDebtCount": array_len(packet, "atomOriginClosureDebtReadings"),
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

    for (index, hotspot) in array_items(spectrum, "topHotspots").into_iter().enumerate() {
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
    {
        actions.push(serde_json::json!({
            "kind": "nonzeroHolonomy",
            "conclusion": "nonzeroSelectedAxisContinuationDistance",
            "ref": loop_ref.clone(),
            "recommendedAction": "compare selected path continuations in packet detail and decide whether the loop needs filler evidence or design change",
            "detailRefs": detail_refs("architectureHomotopyReport.nonzeroHolonomyLoops", &format!("/architectureHomotopyReport/nonzeroHolonomyLoops/{index}"))
        }));
    }
    for (index, axis) in array_items(packet, "signatureAxes").into_iter().enumerate() {
        if i64_field(axis, "value", 0) != 0 {
            actions.push(serde_json::json!({
                "kind": "nonzeroSignatureAxis",
                "conclusion": "nonzeroAxisUnderSelectedPolicy",
                "ref": json_field(axis, "signatureAxisId"),
                "lawRef": json_field(axis, "lawRef"),
                "score": json_field(axis, "value"),
                "coverageStatus": json_field(axis, "coverageStatus"),
                "sourceRefCount": array_len(axis, "sourceRefs"),
                "missingEvidenceCount": array_len(axis, "missingEvidence"),
                "recommendedAction": "inspect packet detail for source refs and selected law witness support",
                "detailRefs": detail_refs("signatureAxes", &format!("/signatureAxes/{index}"))
            }));
        }
    }
    let mut workflow_risks: Vec<_> = array_items(packet, "workflowRiskReadings")
        .into_iter()
        .enumerate()
        .collect();
    workflow_risks
        .sort_by_key(|(_, reading)| std::cmp::Reverse(i64_field(reading, "riskScore", 0)));
    for (index, reading) in workflow_risks {
        actions.push(serde_json::json!({
            "kind": "workflowRisk",
            "conclusion": "highRankedWorkflowPressure",
            "ref": json_field(reading, "moleculeObservationRef"),
            "roleName": json_field(reading, "roleName"),
            "score": json_field(reading, "riskScore"),
            "riskTier": json_field(reading, "riskTier"),
            "recommendedAction": compact_recommended_action(reading, "reviewFocus", "review workflow risk packet detail before planning repair"),
            "detailRefs": detail_refs("workflowRiskReadings", &format!("/workflowRiskReadings/{index}"))
        }));
    }
    for action in aat_observation_axis_actions(packet) {
        actions.push(action);
    }
    for bridge in bridge_pressure_actions(packet) {
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
                    "sourceRefCount": array_len(axis, "sourceRefs"),
                    "detailRefs": detail_refs("signatureAxes", &format!("/signatureAxes/{index}")),
                    "packetRefs": packet_refs(&[&format!("/signatureAxes/{index}")])
                })
            })
            .collect(),
    )
}

fn workflow_risk_summary(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "workflowRiskCount": array_len(packet, "workflowRiskReadings"),
        "highestRisks": workflow_risk_findings(packet, DOMINANT_FINDING_LIMIT),
        "packetRefs": packet_refs(&["/workflowRiskReadings"])
    })
}

fn workflow_risk_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut readings: Vec<_> = array_items(packet, "workflowRiskReadings")
        .into_iter()
        .enumerate()
        .collect();
    readings.sort_by_key(|(_, reading)| std::cmp::Reverse(i64_field(reading, "riskScore", 0)));
    serde_json::Value::Array(
        readings
            .into_iter()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "moleculeObservationRef"),
                    "roleName": json_field(reading, "roleName"),
                    "status": json_field(reading, "status"),
                    "score": json_field(reading, "riskScore"),
                    "riskTier": json_field(reading, "riskTier"),
                    "recommendedAction": compact_recommended_action(reading, "reviewFocus", "review workflow risk packet detail before planning repair"),
                    "detailRefs": detail_refs("workflowRiskReadings", &format!("/workflowRiskReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/workflowRiskReadings/{index}")])
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
                "sourceRefCount": array_len(reading, "sourceRefs"),
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
            detail_index_section("workflowRiskReadings", "/workflowRiskReadings", array_len(packet, "workflowRiskReadings")),
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
        "whyNontrivial": "Intersects law-axis, workflow, spectrum, homotopy, and bridge support.",
        "measurement": {
            "clusterCount": clusters.len(),
            "maxReadingKindCount": cluster.map(|cluster| cluster.kind_count).unwrap_or_default()
        },
        "packetRefs": packet_refs(&["/workflowRiskReadings"])
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

    for (index, reading) in array_items(packet, "workflowRiskReadings")
        .into_iter()
        .enumerate()
    {
        let evidence_ref = format!("packet:/workflowRiskReadings/{index}");
        for support in optional_string(reading, "moleculeObservationRef")
            .chain(string_array(reading, "semanticRefs"))
            .chain(string_array(reading, "concernRefs"))
            .chain(
                array_items(reading, "topAxes")
                    .into_iter()
                    .filter_map(|axis| axis.get("axis").and_then(serde_json::Value::as_str))
                    .map(|axis| format!("axis:{axis}")),
            )
        {
            push_support_contribution(&mut clusters, "workflowRisk", &support, &evidence_ref);
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

fn workflow_risk_ref_list(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut readings = array_items(packet, "workflowRiskReadings");
    readings.sort_by_key(|reading| std::cmp::Reverse(i64_field(reading, "riskScore", 0)));
    serde_json::Value::Array(
        readings
            .into_iter()
            .take(limit)
            .filter_map(|reading| {
                reading
                    .get("moleculeObservationRef")
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

fn compact_recommended_action(
    value: &serde_json::Value,
    key: &str,
    fallback: &str,
) -> serde_json::Value {
    let items = array_items(value, key);
    if items.is_empty() {
        return serde_json::Value::String(fallback.to_string());
    }
    serde_json::Value::String(
        items
            .into_iter()
            .filter_map(serde_json::Value::as_str)
            .take(3)
            .collect::<Vec<_>>()
            .join("; "),
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
