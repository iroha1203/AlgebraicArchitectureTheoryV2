mod air;
mod air_validation;
mod artifact_retention;
mod baseline_suppression;
mod component_validation;
mod custom_rule_plugin;
mod dataset;
mod extractor;
mod feature_dataset;
mod feature_report;
mod framework_adapter;
mod github;
mod graph;
mod law_policy_template;
mod measurement_unit;
mod no_solution_certificate;
mod obstruction_drift;
mod operational_feedback;
mod organization_policy;
mod outcome_linkage;
mod policy;
mod policy_decision;
mod pr_comment;
mod python_extractor;
mod relation_complexity;
mod repair_rule;
mod reported_axes_catalog;
mod runtime;
pub mod schema;
mod schema_catalog;
mod schema_compatibility;
mod schema_versioning;
mod snapshot;
mod synthesis_constraint;
mod theorem_precondition;
mod validation;

#[cfg(test)]
mod test_support;

pub use air::build_air_document;
pub use air_validation::validate_air_document_report;
pub use artifact_retention::{
    static_report_artifact_retention_manifest, validate_report_artifact_retention_report,
};
pub use baseline_suppression::build_baseline_suppression_report;
pub use component_validation::validate_component_universe_report;
pub use custom_rule_plugin::{
    static_custom_rule_plugin_registry, validate_custom_rule_plugin_registry_report,
};
pub use dataset::build_empirical_dataset;
pub use extractor::{extract_sig0, extract_sig0_with_policy, extract_sig0_with_runtime};
pub use feature_dataset::{
    build_feature_extension_dataset, build_feature_extension_dataset_from_files,
};
pub use feature_report::build_feature_extension_report;
pub use framework_adapter::attach_framework_adapter_evidence;
pub use github::{
    build_pr_history_dataset_from_github_files, build_pr_history_dataset_from_github_values,
    build_pr_metadata_from_github_files, build_pr_metadata_from_github_values,
};
pub use law_policy_template::{
    static_law_policy_template_registry, validate_law_policy_template_registry_report,
};
pub use measurement_unit::{
    static_measurement_unit_registry, validate_measurement_unit_registry_report,
};
pub use no_solution_certificate::{
    static_no_solution_certificate, validate_no_solution_certificate_report,
};
pub use obstruction_drift::{
    static_architecture_drift_ledger, static_obstruction_witness_artifact,
};
pub use operational_feedback::{
    ReportOutcomeDailyLedgerInput, build_report_outcome_daily_ledger,
    build_report_outcome_daily_ledger_from_files, static_calibration_review_record,
};
pub use organization_policy::{static_organization_policy, validate_organization_policy_report};
pub use outcome_linkage::{
    build_outcome_linkage_dataset, build_outcome_linkage_dataset_from_files,
};
pub use policy_decision::build_policy_decision_report;
pub use pr_comment::render_pr_comment_markdown;
pub use python_extractor::extract_python_sig0;
pub use relation_complexity::{
    extract_relation_complexity_observation, extract_relation_complexity_observation_from_file,
};
pub use repair_rule::{static_repair_rule_registry, validate_repair_rule_registry_report};
pub use reported_axes_catalog::static_detectable_values_reported_axes_catalog;
pub use schema::*;
pub use schema_catalog::static_schema_version_catalog;
pub use schema_compatibility::build_schema_compatibility_check_report;
pub use snapshot::{build_signature_diff_report, build_signature_snapshot_record};
pub use synthesis_constraint::{
    static_synthesis_constraint_artifact, validate_synthesis_constraint_artifact_report,
};
pub use theorem_precondition::{
    build_theorem_precondition_check_report, static_theorem_package_registry,
};

fn measured_status(source: &str) -> MetricStatus {
    MetricStatus {
        measured: true,
        reason: None,
        source: Some(source.to_string()),
    }
}

fn unmeasured_status(reason: String) -> MetricStatus {
    MetricStatus {
        measured: false,
        reason: Some(reason),
        source: None,
    }
}
