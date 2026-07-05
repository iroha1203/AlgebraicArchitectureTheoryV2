mod registry;
mod validate;

pub use registry::{
    REPLACEMENT_REGISTRY_REF, expand_law_policy_v1, is_known_v1_distance_profile,
    static_law_evaluator_registry_v1,
};
pub use validate::validate_law_policy_v1_report;
