mod air;
mod air_validation;
mod component_validation;
mod dataset;
mod extractor;
mod feature_report;
mod github;
mod graph;
mod policy;
mod relation_complexity;
mod repair_rule;
mod runtime;
pub mod schema;
mod snapshot;
mod theorem_precondition;
mod validation;

#[cfg(test)]
mod test_support;

pub use air::build_air_document;
pub use air_validation::validate_air_document_report;
pub use component_validation::validate_component_universe_report;
pub use dataset::build_empirical_dataset;
pub use extractor::{extract_sig0, extract_sig0_with_policy, extract_sig0_with_runtime};
pub use feature_report::build_feature_extension_report;
pub use github::{build_pr_metadata_from_github_files, build_pr_metadata_from_github_values};
pub use relation_complexity::{
    extract_relation_complexity_observation, extract_relation_complexity_observation_from_file,
};
pub use repair_rule::{static_repair_rule_registry, validate_repair_rule_registry_report};
pub use schema::*;
pub use snapshot::{build_signature_diff_report, build_signature_snapshot_record};
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
