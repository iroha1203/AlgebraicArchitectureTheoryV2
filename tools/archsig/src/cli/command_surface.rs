use std::error::Error;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
use archsig::{
    ARCHMAP_V2_SCHEMA, ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT, ArchMapDocumentV2,
    LAW_EQUATION_SURFACE_V1_SCHEMA, LAW_POLICY_V1_SCHEMA, LawEquationSurfaceV1,
    LawPolicyDocumentV1, MEASUREMENT_PROFILE_V1_SCHEMA, MeasurementProfileV1,
    SchemaVersionCatalogV0, build_comparison_artifacts_v1, build_foundation_measurement_packet_v1,
    build_gate_report_v1, build_insight_brief_v1, build_insight_report_v1,
    build_measurement_summary_v1, build_measurement_view_model_v1,
    build_measurement_viewer_data_v1, build_policy_bundle,
    component_fingerprints as build_component_fingerprints, normalize_archmap_v2,
    resolve_and_verify_policy_bundle, static_schema_version_catalog, validate_archmap_v2_report,
    validate_law_policy_v1_report, validate_law_surface_v1_report,
    validate_measurement_packet_value_v1, validate_measurement_profile_v1_checks,
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
    /// Validate a LawPolicy v0.5.4 selector artifact for ArchSig AAT analysis.
    LawPolicy {
        /// Input LawPolicy v0.5.4 JSON path.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Input MeasurementProfile v0.5.4 JSON path.
        #[arg(long = "measurement-profile")]
        measurement_profile: PathBuf,

        /// Supplied law-equation-surface/v0.5.4 JSON path.
        #[arg(long = "law-surface")]
        law_surface: PathBuf,

        /// Output LawPolicy fixture or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a supplied law-equation-surface/v0.5.4 author declaration.
    LawSurface {
        /// Input law-equation-surface/v0.5.4 JSON path.
        #[arg(long = "law-surface")]
        law_surface: PathBuf,

        /// Output law-equation-surface validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a standalone MeasurementProfile v0.5.4 artifact.
    MeasurementProfile {
        /// Input MeasurementProfile v0.5.4 JSON path.
        #[arg(long = "measurement-profile")]
        measurement_profile: PathBuf,

        /// Output MeasurementProfile validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Run the primary ArchMap + policy-bundle (LawPolicy + law surface + MeasurementProfile) -> ArchSig analysis workflow.
    Analyze {
        /// Input ArchMap observation artifact path.
        #[arg(long)]
        archmap: PathBuf,

        /// Input LawPolicy artifact path.
        #[arg(
            long = "law-policy",
            required_unless_present = "policy_bundle",
            conflicts_with = "policy_bundle"
        )]
        law_policy: Option<PathBuf>,

        /// Optional law-equation-surface/v0.5.4 artifact supplying evaluator execution plans.
        #[arg(long = "law-surface", conflicts_with = "policy_bundle")]
        law_surface: Option<PathBuf>,

        /// Input MeasurementProfile artifact path.
        #[arg(
            long = "measurement-profile",
            required_unless_present = "policy_bundle",
            conflicts_with = "policy_bundle"
        )]
        measurement_profiles: Option<Vec<PathBuf>>,

        /// Policy bundle supplying the LawPolicy, law surface, MeasurementProfile, and fingerprints.
        #[arg(long = "policy-bundle", conflicts_with_all = ["law_policy", "law_surface", "measurement_profiles"])]
        policy_bundle: Option<PathBuf>,

        /// Output directory for ArchSig analysis workflow artifacts.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,

        /// Append a wall-clock suffix to the deterministic run id. Omitted by default to keep byte-identical outputs.
        #[arg(long)]
        stamp: bool,
    },

    /// Apply a gate policy to an ArchSig measurement packet.
    Gate {
        /// Input archsig-measurement-packet/v0.5.4 JSON path.
        #[arg(long)]
        packet: PathBuf,

        /// Input archsig-gate-policy/v0.5.4 JSON path.
        #[arg(long)]
        policy: PathBuf,

        /// Optional archsig-comparison-report/v0.5.7 JSON path for introduced-by-change rules.
        #[arg(long)]
        comparison: Option<PathBuf>,

        /// Output archsig-gate-report/v0.5.4 JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Compare two ArchSig analyze run directories at record level.
    Compare {
        /// Base run directory containing normalized-archmap, measurement packet, and run manifest.
        #[arg(long = "base-run")]
        base_run: PathBuf,

        /// Head run directory containing normalized-archmap, measurement packet, and run manifest.
        #[arg(long = "head-run")]
        head_run: PathBuf,

        /// Output directory for archmap-diff.json and archsig-comparison-report.json.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,
    },
    /// Create or validate an ArchSig policy bundle.
    PolicyBundle {
        /// Existing policy bundle to validate. Omit this when creating a bundle.
        #[arg(long = "policy-bundle", conflicts_with_all = ["law_policy", "law_surface", "measurement_profile"])]
        policy_bundle: Option<PathBuf>,

        /// LawPolicy component used when creating or explicitly verifying a bundle.
        #[arg(long = "law-policy", requires_all = ["law_surface", "measurement_profile"])]
        law_policy: Option<PathBuf>,

        /// Law equation surface component used when creating or explicitly verifying a bundle.
        #[arg(long = "law-surface", requires_all = ["law_policy", "measurement_profile"])]
        law_surface: Option<PathBuf>,

        /// MeasurementProfile component used when creating or explicitly verifying a bundle.
        #[arg(long = "measurement-profile", requires_all = ["law_policy", "law_surface"])]
        measurement_profile: Option<PathBuf>,

        /// Bundle identifier for a newly created bundle.
        #[arg(long, default_value = "policy-bundle:archsig-v052")]
        id: String,

        /// Output bundle or validation report path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },
    SchemaCatalog {
        /// Output schema version catalog JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },
}

pub(crate) fn is_internal_runtime_error(message: &str) -> bool {
    let lower = message.to_ascii_lowercase();
    [
        "is a directory",
        "permission denied",
        "read-only file system",
        "no space left on device",
        "too many open files",
        "broken pipe",
    ]
    .iter()
    .any(|needle| lower.contains(needle))
}

fn validate_archmap_command_input(
    input: &PathBuf,
) -> Result<(serde_json::Value, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, ARCHMAP_V2_SCHEMA, "--archmap")?;
    let document: ArchMapDocumentV2 = serde_json::from_value(raw)?;
    let report = validate_archmap_v2_report(&document, &stable_input_ref(input));
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed))
}

fn validate_law_policy_command_input(
    input: &PathBuf,
    measurement_profile: &MeasurementProfileV1,
    law_surface: &LawEquationSurfaceV1,
) -> Result<(serde_json::Value, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, LAW_POLICY_V1_SCHEMA, "--law-policy")?;
    let policy: LawPolicyDocumentV1 = serde_json::from_value(raw)?;
    let report = validate_law_policy_v1_report(
        &policy,
        &stable_input_ref(input),
        Some(measurement_profile),
        Some(law_surface),
    );
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed))
}

fn validate_measurement_profile_command_input(
    input: &PathBuf,
) -> Result<(serde_json::Value, MeasurementProfileV1, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, MEASUREMENT_PROFILE_V1_SCHEMA, "--measurement-profile")?;
    let profile: MeasurementProfileV1 = serde_json::from_value(raw)?;
    let checks = validate_measurement_profile_v1_checks(&profile);
    let failed_check_count = checks.iter().filter(|check| check.result == "fail").count();
    let warning_check_count = checks.iter().filter(|check| check.result == "warn").count();
    let failed = failed_check_count > 0;
    Ok((
        serde_json::json!({
            "schema": "measurement-profile-validation-report/v0.5.4",
            "input": {
                "schema": profile.schema,
                "path": stable_input_ref(input),
                "id": profile.profile_id
            },
            "checks": checks,
            "summary": {
                "result": if failed { "fail" } else if warning_check_count > 0 { "warn" } else { "pass" },
                "failedCheckCount": failed_check_count,
                "warningCheckCount": warning_check_count
            }
        }),
        profile,
        failed,
    ))
}

fn validate_law_surface_command_input(
    input: &PathBuf,
) -> Result<(serde_json::Value, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, LAW_EQUATION_SURFACE_V1_SCHEMA, "--law-surface")?;
    let surface: LawEquationSurfaceV1 = serde_json::from_value(raw.clone())?;
    let report = validate_law_surface_v1_report(&surface, &raw, &stable_input_ref(input));
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed))
}

fn stable_input_ref(input: &Path) -> String {
    let file_name = input
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("artifact.json");
    format!("input:{file_name}")
}

fn summary_result(document: &serde_json::Value) -> &str {
    document["summary"]["result"].as_str().unwrap_or("fail")
}

fn validation_result_summary(document: &serde_json::Value) -> serde_json::Value {
    let result = summary_result(document);
    validation_result_summary_from_counts(
        result,
        document["summary"]["failedCheckCount"]
            .as_u64()
            .unwrap_or_else(|| usize::from(result == "fail") as u64) as usize,
        document["summary"]["warningCheckCount"]
            .as_u64()
            .unwrap_or(0) as usize,
    )
}

fn validation_result_summary_from_counts(
    result: &str,
    failed_check_count: usize,
    warning_check_count: usize,
) -> serde_json::Value {
    serde_json::json!({
        "result": result,
        "failedCheckCount": failed_check_count,
        "warningCheckCount": warning_check_count
    })
}
