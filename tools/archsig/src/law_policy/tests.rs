use super::constants::{MAX_PART4_DISTANCE_PROFILE_WEIGHT, MAX_PART4_OPERATION_COST};
use super::*;
use crate::{
    LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION, LawPolicyDocumentV0,
    LawPolicyPart4DistanceWeightV0,
};

#[test]
fn static_law_policy_validates() {
    let policy = static_law_policy();
    let report = validate_law_policy_report(&policy, "static-law-policy.json");
    assert_eq!(
        report.schema_version,
        LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION
    );
    assert_eq!(report.summary.result, "pass");
    assert_eq!(report.summary.selected_law_count, 2);
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-non-conclusion-boundary" && check.result == "pass"
    }));
}

#[test]
fn missing_law_policy_non_conclusion_fails() {
    let mut policy = static_law_policy();
    policy.non_conclusions.clear();
    let report = validate_law_policy_report(&policy, "bad-law-policy.json");
    assert_eq!(report.summary.result, "fail");
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-non-conclusion-boundary" && check.result == "fail"
    }));
}

#[test]
fn unknown_witness_ref_fails() {
    let mut policy = static_law_policy();
    policy.selected_laws[0]
        .required_witness_refs
        .push("witness:missing".to_string());
    let report = validate_law_policy_report(&policy, "bad-law-policy.json");
    assert_eq!(report.summary.result, "fail");
    assert!(
        report
            .checks
            .iter()
            .any(|check| { check.id == "law-policy-law-refs-resolve" && check.result == "fail" })
    );
}

#[test]
fn duplicate_law_policy_ids_fail() {
    let mut policy = static_law_policy();
    policy.selected_laws[1].law_id = policy.selected_laws[0].law_id.clone();
    policy.witness_rules[1].witness_rule_id = policy.witness_rules[0].witness_rule_id.clone();
    policy.coverage_requirements[1].coverage_requirement_id = policy.coverage_requirements[0]
        .coverage_requirement_id
        .clone();

    let report = validate_law_policy_report(&policy, "bad-law-policy.json");

    assert_eq!(report.summary.result, "fail");
    let id_check = report
        .checks
        .iter()
        .find(|check| check.id == "law-policy-ids-unique")
        .expect("ids uniqueness check is emitted");
    assert_eq!(id_check.result, "fail");
    assert!(
        id_check
            .examples
            .iter()
            .any(|example| example.source.as_deref() == Some("selectedLaws[].lawId"))
    );
    assert!(
        id_check
            .examples
            .iter()
            .any(|example| example.source.as_deref() == Some("witnessRules[].witnessRuleId"))
    );
    assert!(id_check.examples.iter().any(|example| {
        example.source.as_deref() == Some("coverageRequirements[].coverageRequirementId")
    }));
}

#[test]
fn invalid_measurement_policy_fails() {
    let mut policy = static_law_policy();
    policy.measurement_policy.selected_axis_refs = vec!["axis:missing".to_string()];
    policy.measurement_policy.arch_map_store_ref_kinds = vec!["archmap-delta".to_string()];

    let report = validate_law_policy_report(&policy, "bad-law-policy.json");

    assert_eq!(report.summary.result, "fail");
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-monodromy-measurement-policy" && check.result == "fail"
    }));
}

#[test]
fn invalid_part4_distance_profile_fails() {
    let mut policy = static_law_policy();
    let profile = policy
        .part4_distance_profile
        .as_mut()
        .expect("fixture declares a Part IV distance profile");
    profile
        .atom_weights
        .retain(|weight| weight.axis_ref != "atom.fiber");
    profile.signature_weights[0].axis_ref = "sig-axis:missing".to_string();
    profile.operation_costs[0].cost = 0;
    profile.coverage_requirement_refs = vec!["coverage:missing".to_string()];
    profile.non_conclusions.clear();

    let report = validate_law_policy_report(&policy, "bad-law-policy.json");

    assert_eq!(report.summary.result, "fail");
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-part4-distance-profile" && check.result == "fail"
    }));
}

#[test]
fn part4_distance_profile_rejects_sparse_and_unused_weights() {
    let mut missing_signature = static_law_policy();
    missing_signature
        .part4_distance_profile
        .as_mut()
        .expect("fixture declares a Part IV distance profile")
        .signature_weights
        .retain(|weight| weight.axis_ref != "sig-axis:semantic-inconsistency");
    let missing_report = validate_law_policy_report(&missing_signature, "bad-law-policy.json");
    assert_eq!(missing_report.summary.result, "fail");
    assert!(missing_report.checks.iter().any(|check| {
        check.id == "law-policy-part4-distance-profile"
            && check.result == "fail"
            && check.examples.iter().any(|example| {
                example.evidence.as_deref().is_some_and(|evidence| {
                    evidence.contains("must include every selected signature axis")
                })
            })
    }));

    let mut unused_atom = static_law_policy();
    unused_atom
        .part4_distance_profile
        .as_mut()
        .expect("fixture declares a Part IV distance profile")
        .atom_weights
        .push(LawPolicyPart4DistanceWeightV0 {
            axis_ref: "atom.unused".to_string(),
            weight: 1,
            source_ref: "fixture:unused".to_string(),
        });
    let unused_report = validate_law_policy_report(&unused_atom, "bad-law-policy.json");
    assert_eq!(unused_report.summary.result, "fail");
    assert!(unused_report.checks.iter().any(|check| {
        check.id == "law-policy-part4-distance-profile"
            && check.result == "fail"
            && check.examples.iter().any(|example| {
                example.evidence.as_deref().is_some_and(|evidence| {
                    evidence.contains("must not include unused Atom geometry components")
                })
            })
    }));
}

#[test]
fn part4_distance_profile_rejects_unbounded_weights_and_costs() {
    let mut policy = static_law_policy();
    let profile = policy
        .part4_distance_profile
        .as_mut()
        .expect("fixture declares a Part IV distance profile");
    profile.atom_weights[0].weight = MAX_PART4_DISTANCE_PROFILE_WEIGHT + 1;
    profile.signature_weights[0].weight = MAX_PART4_DISTANCE_PROFILE_WEIGHT + 1;
    profile.operation_costs[0].cost = MAX_PART4_OPERATION_COST + 1;

    let report = validate_law_policy_report(&policy, "bad-law-policy.json");

    assert_eq!(report.summary.result, "fail");
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-part4-distance-profile"
            && check.result == "fail"
            && check.examples.iter().any(|example| {
                example
                    .evidence
                    .as_deref()
                    .is_some_and(|evidence| evidence.contains("bounded ArchSig distance range"))
            })
    }));
}

#[test]
fn absent_part4_distance_profile_warns() {
    let mut policy = static_law_policy();
    policy.part4_distance_profile = None;

    let report = validate_law_policy_report(&policy, "law-policy-without-part4-distance.json");

    assert_eq!(report.summary.result, "warn");
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-part4-distance-profile" && check.result == "warn"
    }));
}

#[test]
fn invalid_spectrum_measurement_profile_fails() {
    let mut policy = static_law_policy();
    let profile = policy
        .spectrum_measurement_profile
        .as_mut()
        .expect("fixture declares a spectrum profile");
    profile.selected_axis_refs = vec!["axis:missing".to_string()];
    profile.measured_witness_rule_refs = vec!["witness:missing".to_string()];
    profile.coverage_requirement_refs.clear();
    profile.non_conclusions.clear();

    let report = validate_law_policy_report(&policy, "bad-law-policy.json");

    assert_eq!(report.summary.result, "fail");
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-spectrum-measurement-profile" && check.result == "fail"
    }));
}

#[test]
fn absent_spectrum_measurement_profile_is_valid() {
    let mut policy = static_law_policy();
    policy.spectrum_measurement_profile = None;

    let report = validate_law_policy_report(&policy, "law-policy-without-spectrum.json");

    assert_eq!(report.summary.result, "pass");
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-spectrum-measurement-profile" && check.result == "pass"
    }));
}

#[test]
fn invalid_homotopy_measurement_profile_fails() {
    let mut policy = static_law_policy();
    let profile = policy
        .homotopy_measurement_profile
        .as_mut()
        .expect("fixture declares a homotopy profile");
    profile.selected_axis_refs = vec!["axis:missing".to_string()];
    profile.path_discovery_rules.clear();
    profile.filler_rules.clear();
    profile.coverage_requirement_refs = vec!["coverage:missing".to_string()];
    profile.non_conclusions.clear();

    let report = validate_law_policy_report(&policy, "bad-law-policy.json");

    assert_eq!(report.summary.result, "fail");
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-homotopy-measurement-profile" && check.result == "fail"
    }));
}

#[test]
fn absent_homotopy_measurement_profile_is_valid() {
    let mut policy = static_law_policy();
    policy.homotopy_measurement_profile = None;

    let report = validate_law_policy_report(&policy, "law-policy-without-homotopy.json");

    assert_eq!(report.summary.result, "pass");
    assert!(report.checks.iter().any(|check| {
        check.id == "law-policy-homotopy-measurement-profile" && check.result == "pass"
    }));
}

#[test]
fn unknown_top_level_law_policy_field_is_rejected() {
    let mut value = serde_json::to_value(static_law_policy()).expect("policy serializes");
    value["unexpectedField"] = serde_json::json!("unknown");

    let error = serde_json::from_value::<LawPolicyDocumentV0>(value)
        .expect_err("unknown top-level fields must be rejected");

    assert!(error.to_string().contains("unknown field"));
}

#[test]
fn canonical_fixture_matches_static_law_policy() {
    let fixture: LawPolicyDocumentV0 =
        serde_json::from_str(include_str!("../../tests/fixtures/minimal/law_policy.json"))
            .expect("law policy fixture parses");
    assert_eq!(fixture, static_law_policy());
}
