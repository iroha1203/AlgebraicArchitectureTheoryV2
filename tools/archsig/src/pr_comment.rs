use std::fmt::Write as _;

use crate::{
    FeatureExtensionReportV0, FeatureReportCoverageGap, FeatureReportObstructionWitness,
    PR_COMMENT_SUMMARY_SCHEMA_VERSION, PolicyDecisionReportV0,
};

const SUMMARY_NON_CONCLUSIONS: [&str; 4] = [
    "This summary does not approve architecture lawfulness.",
    "This summary is not a Lean theorem proof.",
    "Unmeasured axes are not measured-zero evidence.",
    "Advisory signals are not repair success evidence.",
];

pub fn render_pr_comment_markdown(
    feature_report: &FeatureExtensionReportV0,
    policy_decision: Option<&PolicyDecisionReportV0>,
) -> String {
    let mut out = String::new();
    writeln!(
        out,
        "<!-- schemaVersion: {PR_COMMENT_SUMMARY_SCHEMA_VERSION} -->"
    )
    .unwrap();
    writeln!(out, "## ArchSig PR Review Summary").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "### Level 1 Review Summary").unwrap();
    writeln!(out).unwrap();
    writeln!(
        out,
        "- Split status: `{}`",
        feature_report.review_summary.split_status
    )
    .unwrap();
    writeln!(
        out,
        "- Claim classification: `{}`",
        feature_report.review_summary.claim_classification
    )
    .unwrap();
    writeln!(
        out,
        "- Required action: {}",
        feature_report.review_summary.required_action
    )
    .unwrap();
    if let Some(policy_decision) = policy_decision {
        writeln!(
            out,
            "- Policy decision: `{}` (fail: {}, warn: {}, advisory: {})",
            policy_decision.summary.decision,
            policy_decision.summary.fail_count,
            policy_decision.summary.warn_count,
            policy_decision.summary.advisory_count
        )
        .unwrap();
    } else {
        writeln!(out, "- Policy decision: `not-provided`").unwrap();
    }
    writeln!(
        out,
        "- Top witnesses: {}",
        inline_list(&feature_report.review_summary.top_witnesses)
    )
    .unwrap();
    if let Some(policy_decision) = policy_decision {
        writeln!(
            out,
            "- Required axis status: {}",
            required_axis_summary(policy_decision)
        )
        .unwrap();
    }
    writeln!(out).unwrap();

    writeln!(out, "<details>").unwrap();
    writeln!(out, "<summary>Level 2 Evidence Detail</summary>").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "### Changed Components").unwrap();
    writeln!(
        out,
        "- Added: {}",
        inline_list(&feature_report.interpreted_extension.added_components)
    )
    .unwrap();
    writeln!(
        out,
        "- Changed: {}",
        inline_list(&feature_report.interpreted_extension.changed_components)
    )
    .unwrap();
    writeln!(
        out,
        "- Added relations: {}",
        inline_list(&feature_report.interpreted_extension.added_relations)
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "### Witness Evidence").unwrap();
    write_witnesses(
        &mut out,
        &feature_report.introduced_obstruction_witnesses,
        "introduced",
    );
    write_witnesses(
        &mut out,
        &feature_report.eliminated_obstruction_witnesses,
        "eliminated",
    );
    if let Some(policy_decision) = policy_decision {
        for witness in &policy_decision.witness_decisions {
            writeln!(
                out,
                "- Policy witness `{}`: `{}` / `{}` / `{}`",
                witness.witness_id,
                witness.status,
                witness.claim_classification,
                witness.measurement_boundary
            )
            .unwrap();
        }
    }
    writeln!(out).unwrap();
    writeln!(out, "### Runtime Summary").unwrap();
    writeln!(
        out,
        "- Measurement boundary: `{}`",
        feature_report.runtime_summary.measurement_boundary
    )
    .unwrap();
    writeln!(
        out,
        "- runtimePropagation: `{}`",
        feature_report
            .runtime_summary
            .runtime_propagation
            .map(|value| value.to_string())
            .unwrap_or_else(|| "unmeasured".to_string())
    )
    .unwrap();
    writeln!(
        out,
        "- Runtime claim refs: {}",
        inline_list(&feature_report.runtime_summary.claim_refs)
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "### Coverage Gaps").unwrap();
    write_coverage_gaps(&mut out, &feature_report.coverage_gaps);
    if let Some(policy_decision) = policy_decision {
        for gap in &policy_decision.coverage_gap_decisions {
            writeln!(
                out,
                "- Policy coverage gap `{}` / `{}`: `{}` (allowed: {})",
                gap.layer, gap.axis, gap.status, gap.allowed_by_policy
            )
            .unwrap();
        }
    }
    writeln!(out).unwrap();
    writeln!(out, "</details>").unwrap();
    writeln!(out).unwrap();

    writeln!(out, "<details>").unwrap();
    writeln!(out, "<summary>Level 3 Formal Detail</summary>").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "### Theorem Package Refs").unwrap();
    writeln!(
        out,
        "- {}",
        inline_list(&feature_report.theorem_package_refs)
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "### Theorem Preconditions").unwrap();
    writeln!(
        out,
        "- Result: `{}` (formal proved: {}, blocked: {}, unmeasured: {})",
        feature_report.theorem_precondition_summary.result,
        feature_report
            .theorem_precondition_summary
            .formal_proved_claim_count,
        feature_report
            .theorem_precondition_summary
            .blocked_claim_count,
        feature_report
            .theorem_precondition_summary
            .unmeasured_claim_count
    )
    .unwrap();
    for check in &feature_report.theorem_precondition_checks {
        writeln!(
            out,
            "- `{}`: `{}` / `{}`; missing: {}; theorem refs: {}",
            check.claim_id,
            check.result,
            check.resolved_claim_classification,
            inline_list(&check.missing_preconditions),
            inline_list(&check.theorem_refs)
        )
        .unwrap();
    }
    writeln!(out).unwrap();
    writeln!(out, "### Assumption Boundary").unwrap();
    writeln!(
        out,
        "- Discharged assumptions: {}",
        inline_list(&feature_report.discharged_assumptions)
    )
    .unwrap();
    writeln!(
        out,
        "- Missing assumptions: {}",
        inline_list(&feature_report.undischarged_assumptions)
    )
    .unwrap();
    writeln!(
        out,
        "- Runtime exactness assumptions: {}",
        inline_list(&feature_report.runtime_summary.exactness_assumptions)
    )
    .unwrap();
    writeln!(
        out,
        "- Semantic exactness assumptions: {}",
        inline_list(&feature_report.semantic_path_summary.exactness_assumptions)
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "### Non-Conclusions").unwrap();
    for non_conclusion in SUMMARY_NON_CONCLUSIONS {
        writeln!(out, "- {non_conclusion}").unwrap();
    }
    for non_conclusion in &feature_report.non_conclusions {
        writeln!(out, "- {non_conclusion}").unwrap();
    }
    if let Some(policy_decision) = policy_decision {
        for non_conclusion in &policy_decision.non_conclusions {
            writeln!(out, "- {non_conclusion}").unwrap();
        }
    }
    writeln!(out).unwrap();
    writeln!(out, "</details>").unwrap();
    out
}

fn inline_list(values: &[String]) -> String {
    if values.is_empty() {
        "none".to_string()
    } else {
        values
            .iter()
            .map(|value| format!("`{value}`"))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn required_axis_summary(policy_decision: &PolicyDecisionReportV0) -> String {
    if policy_decision.required_axis_decisions.is_empty() {
        return "none".to_string();
    }
    policy_decision
        .required_axis_decisions
        .iter()
        .map(|decision| {
            format!(
                "`{}` = `{}` ({})",
                decision.axis, decision.status, decision.actual_measurement_boundary
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn write_witnesses(
    out: &mut String,
    witnesses: &[FeatureReportObstructionWitness],
    lifecycle: &str,
) {
    if witnesses.is_empty() {
        writeln!(out, "- {lifecycle}: none").unwrap();
        return;
    }
    for witness in witnesses {
        writeln!(
            out,
            "- {lifecycle} `{}`: `{}` / `{}` / `{}`; components: {}",
            witness.witness_id,
            witness.kind,
            witness.claim_classification,
            witness.measurement_boundary,
            inline_list(&witness.components)
        )
        .unwrap();
    }
}

fn write_coverage_gaps(out: &mut String, coverage_gaps: &[FeatureReportCoverageGap]) {
    if coverage_gaps.is_empty() {
        writeln!(out, "- none").unwrap();
        return;
    }
    for gap in coverage_gaps {
        writeln!(
            out,
            "- `{}`: `{}`; unmeasured axes: {}; unsupported: {}",
            gap.layer,
            gap.measurement_boundary,
            inline_list(&gap.unmeasured_axes),
            inline_list(&gap.unsupported_constructs)
        )
        .unwrap();
    }
}

#[cfg(test)]
mod tests {
    use crate::feature_report::build_feature_extension_report;
    use crate::organization_policy::static_organization_policy;
    use crate::policy_decision::build_policy_decision_report;
    use crate::test_support::air_fixture_document;

    use super::*;

    #[test]
    fn markdown_keeps_review_levels_and_non_conclusion_boundary() {
        let document = air_fixture_document("good_extension.json");
        let feature_report = build_feature_extension_report(&document, "good_extension.json");
        let policy = static_organization_policy();
        let policy_decision = build_policy_decision_report(
            &feature_report,
            "feature-report.json",
            &policy,
            "organization-policy.json",
        );

        let markdown = render_pr_comment_markdown(&feature_report, Some(&policy_decision));

        assert!(markdown.contains("### Level 1 Review Summary"));
        assert!(markdown.contains("<summary>Level 2 Evidence Detail</summary>"));
        assert!(markdown.contains("<summary>Level 3 Formal Detail</summary>"));
        assert!(markdown.contains("Policy decision: `fail`"));
        assert!(markdown.contains("runtimePropagation"));
        assert!(markdown.contains("This summary does not approve architecture lawfulness."));
    }
}
