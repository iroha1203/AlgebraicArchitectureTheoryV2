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
mod runtime;
pub mod schema;
mod snapshot;
mod theorem_precondition;
mod validation;

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
pub use schema::*;
pub use snapshot::{build_signature_diff_report, build_signature_snapshot_record};
pub use theorem_precondition::{
    build_theorem_precondition_check_report, static_theorem_package_registry,
};

#[cfg(test)]
pub(crate) use extractor::{ParsedImport, parse_imports};
#[cfg(test)]
pub(crate) use graph::compute_signature;

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

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::path::Path;

    use super::*;

    #[test]
    fn parses_leading_imports_only() {
        let source = r#"
-- comment
import Formal.Arch.Graph
import Formal.Arch.Signature -- inline comment

def x := 1
import Should.Not.Appear
"#;

        let imports = parse_imports(source);

        assert_eq!(
            imports,
            vec![
                ParsedImport {
                    module: "Formal.Arch.Graph".to_string(),
                    evidence: "import Formal.Arch.Graph".to_string(),
                },
                ParsedImport {
                    module: "Formal.Arch.Signature".to_string(),
                    evidence: "import Formal.Arch.Signature".to_string(),
                },
            ]
        );
    }

    #[test]
    fn theorem_check_keeps_measured_witness_out_of_formal_proved_claims() {
        let document = air_fixture_document("good_extension.json");
        let report = build_theorem_precondition_check_report(&document, "good_extension.json");

        assert_eq!(
            report.schema_version,
            THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.registry.scope, "static theorem package v0");
        assert!(report.registry.packages.iter().any(|package| {
            package.theorem_refs
                == vec![
                    "SelectedStaticSplitExtension".to_string(),
                    "CoreEdgesPreserved".to_string(),
                    "DeclaredInterfaceFactorization".to_string(),
                    "NoNewForbiddenStaticEdge".to_string(),
                    "EmbeddingPolicyPreserved".to_string(),
                ]
        }));

        let boundary_check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-boundary-zero")
            .expect("boundary claim is checked");
        assert_eq!(
            boundary_check.resolved_claim_classification,
            "MEASURED_WITNESS"
        );
        assert_eq!(report.summary.formal_proved_claim_count, 0);
        assert!(report.summary.measured_witness_count > 0);
    }

    #[test]
    fn theorem_check_blocks_formal_claims_with_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-blocked".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec!["SelectedStaticSplitExtension".to_string()],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: vec![
                "declared interface factorization not discharged".to_string(),
            ],
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-blocked")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "BLOCKED_FORMAL_CLAIM");
        assert_eq!(check.result, "warn");
        assert_eq!(report.summary.blocked_claim_count, 1);
        assert_eq!(report.summary.formal_proved_claim_count, 0);
    }

    #[test]
    fn theorem_check_accepts_registered_formal_claim_without_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-proved".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec![
                "SelectedStaticSplitExtension".to_string(),
                "CoreEdgesPreserved".to_string(),
                "DeclaredInterfaceFactorization".to_string(),
                "NoNewForbiddenStaticEdge".to_string(),
                "EmbeddingPolicyPreserved".to_string(),
            ],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: Vec::new(),
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-proved")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "FORMAL_PROVED");
        assert_eq!(check.result, "pass");
        assert_eq!(report.summary.formal_proved_claim_count, 1);
    }

    #[test]
    fn extracts_minimal_fixture() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let document = extract_sig0(&root).expect("fixture extracts");

        assert_eq!(document.schema_version, SCHEMA_VERSION);
        assert_eq!(document.component_kind, COMPONENT_KIND);
        assert!(document.components.iter().any(|c| c.id == "Formal"));
        assert!(document.components.iter().any(|c| c.id == "Formal.Arch.B"));
        assert!(!document.components.iter().any(|c| c.id == "lakefile"));
        assert!(document.edges.iter().any(|edge| {
            edge.source == "Formal.Arch.B"
                && edge.target == "Formal.Arch.A"
                && edge.kind == "import"
                && edge.evidence == "import Formal.Arch.A"
        }));
        assert_eq!(document.signature.has_cycle, 0);
        assert_eq!(document.signature.scc_max_size, 1);
        assert_eq!(document.signature.fanout_risk, 3);
        assert_eq!(document.signature.boundary_violation_count, 0);
        assert_eq!(document.signature.abstraction_violation_count, 0);
        assert!(
            document
                .metric_status
                .get("hasCycle")
                .expect("hasCycle status")
                .measured
        );
        assert!(
            !document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .measured
        );
        assert_eq!(
            document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .reason
                .as_deref(),
            Some("policy file not provided")
        );
        assert!(document.policy_violations.is_empty());
        assert!(document.runtime_edge_evidence.is_empty());
        assert!(document.runtime_dependency_graph.is_none());
    }

    #[test]
    fn projects_runtime_edge_evidence_to_runtime_dependency_graph() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let runtime_edges = root.join("runtime_edges.json");
        let document =
            extract_sig0_with_runtime(&root, None, Some(&runtime_edges)).expect("fixture extracts");

        assert_eq!(document.runtime_edge_evidence.len(), 2);
        assert!(document.runtime_edge_evidence.iter().any(|edge| {
            edge.source == "Formal"
                && edge.target == "Formal.Arch.A"
                && edge.label == "rpc"
                && edge.failure_mode.as_deref() == Some("timeout")
                && edge.timeout_budget.as_deref() == Some("250ms")
                && edge.retry_policy.as_deref() == Some("bounded-retry")
                && edge.circuit_breaker_coverage.as_deref() == Some("covered")
                && edge.confidence.as_deref() == Some("fixture")
                && edge.evidence_location.path == "runtime/routes.json"
        }));

        let projection = document
            .runtime_dependency_graph
            .as_ref()
            .expect("runtime projection");
        assert_eq!(projection.projection_rule, RUNTIME_PROJECTION_RULE_VERSION);
        assert_eq!(projection.edge_kind, "runtime");
        assert_eq!(projection.edges.len(), 2);
        assert!(projection.edges.iter().any(|edge| {
            edge.source == "Formal"
                && edge.target == "Formal.Arch.A"
                && edge.kind == "runtime"
                && edge.evidence == "runtime edge evidence count: 1"
        }));
        assert!(
            document
                .metric_status
                .get("runtimePropagation")
                .expect("runtime status")
                .measured
        );

        let dataset = build_empirical_dataset(&document, &document, dataset_input(), "head")
            .expect("dataset builds");
        assert_eq!(
            dataset.signature_after.signature.runtime_propagation,
            Some(2)
        );
        assert_eq!(dataset.delta_signature_signed.runtime_propagation, Some(0));
        assert!(
            dataset
                .signature_after
                .metric_status
                .get("runtimePropagation")
                .expect("runtime dataset status")
                .measured
        );
    }

    #[test]
    fn builds_relation_complexity_observation_from_candidate_fixture() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let observation = extract_relation_complexity_observation_from_file(
            &root.join("relation_complexity_candidates.json"),
        )
        .expect("relation complexity fixture extracts");

        assert_eq!(
            observation.schema_version,
            RELATION_COMPLEXITY_OBSERVATION_SCHEMA_VERSION
        );
        assert_eq!(
            observation.measurement_universe.rule_set_version.as_deref(),
            Some(RELATION_COMPLEXITY_RULE_SET_VERSION)
        );
        assert_eq!(observation.workflow.id, "checkout-payment");
        assert_eq!(observation.counts.constraints, 1);
        assert_eq!(observation.counts.compensations, 1);
        assert_eq!(observation.counts.projections, 0);
        assert_eq!(observation.counts.failure_transitions, 1);
        assert_eq!(observation.counts.idempotency_requirements, 0);
        assert_eq!(observation.relation_complexity, 3);
        assert_eq!(observation.evidence.len(), 2);
        assert!(observation.evidence.iter().any(|evidence| {
            evidence.id == "constraint-1"
                && evidence.path == "src/billing/checkout.rs"
                && evidence.symbol.as_deref() == Some("CheckoutWorkflow::validate")
                && evidence.line == Some(42)
                && evidence.tags == vec!["constraints".to_string()]
                && evidence.ownership == "application-owned"
                && evidence.review_status == "candidate"
        }));
        assert!(observation.evidence.iter().any(|evidence| {
            evidence.id == "compensate-timeout"
                && evidence.tags
                    == vec![
                        "compensations".to_string(),
                        "failureTransitions".to_string(),
                    ]
                && evidence.ownership == "application-configured"
        }));
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/framework/generated.rs"
                && evidence.reason == "ownership-not-counted:framework-generated"
        }));
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/billing/checkout.rs"
                && evidence.reason == "unsupported-tags:notATag"
        }));
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/billing/checkout_test.rs" && evidence.reason == "test-fixture"
        }));
    }

    #[test]
    fn relation_complexity_fixture_excludes_unsupported_framework() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let observation = extract_relation_complexity_observation_from_file(
            &root.join("relation_complexity_unsupported_framework.json"),
        )
        .expect("relation complexity fixture extracts");

        assert_eq!(observation.relation_complexity, 0);
        assert!(observation.evidence.is_empty());
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/billing/unsupported.rs"
                && evidence.reason == "unsupported-framework:unsupported-framework"
        }));
    }

    #[test]
    fn applies_policy_with_measured_zero_counts() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let policy = root.join("policy_measured_zero.json");
        let document = extract_sig0_with_policy(&root, Some(&policy)).expect("fixture extracts");

        assert_eq!(
            document.policies.policy_id.as_deref(),
            Some("minimal-measured-zero")
        );
        assert_eq!(document.policies.boundary_group_count, Some(2));
        assert_eq!(document.policies.abstraction_relation_count, Some(1));
        assert_eq!(document.signature.boundary_violation_count, 0);
        assert_eq!(document.signature.abstraction_violation_count, 0);
        assert!(
            document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .measured
        );
        assert_eq!(
            document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .source
                .as_deref(),
            Some("policy:minimal-measured-zero")
        );
        assert!(document.policy_violations.is_empty());
    }

    #[test]
    fn counts_policy_violations_by_unique_dependency_edge() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let policy = root.join("policy_violations.json");
        let document = extract_sig0_with_policy(&root, Some(&policy)).expect("fixture extracts");

        assert_eq!(document.signature.boundary_violation_count, 2);
        assert_eq!(document.signature.abstraction_violation_count, 1);
        assert!(
            document
                .policy_violations
                .iter()
                .any(|violation| violation.axis == "boundaryViolationCount"
                    && violation.source == "Formal"
                    && violation.target == "Formal.Arch.A")
        );
        assert!(document.policy_violations.iter().any(|violation| {
            violation.axis == "abstractionViolationCount"
                && violation.source == "Formal"
                && violation.target == "Formal.Arch.B"
                && violation
                    .relation_ids
                    .as_ref()
                    .is_some_and(|relations| relations == &vec!["formal-api".to_string()])
        }));
    }

    #[test]
    fn validates_minimal_fixture_with_tooling_boundary_warnings() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let policy = root.join("policy_measured_zero.json");
        let document = extract_sig0_with_policy(&root, Some(&policy)).expect("fixture extracts");

        let report =
            validate_component_universe_report(&document, ".lake/sig0.json", DEFAULT_UNIVERSE_MODE)
                .expect("report validates");

        assert_eq!(report.schema_version, VALIDATION_REPORT_SCHEMA_VERSION);
        assert_eq!(report.universe_mode, DEFAULT_UNIVERSE_MODE);
        assert_eq!(report.summary.component_count, 3);
        assert_eq!(report.summary.local_edge_count, 3);
        assert_eq!(report.summary.external_edge_count, 0);
        assert_eq!(report.summary.failed_check_count, 0);
        assert_eq!(report.summary.warning_check_count, 0);
        assert_eq!(report.summary.not_measured_check_count, 0);
        assert_eq!(report.summary.result, "pass");
        assert!(
            report
                .checks
                .iter()
                .any(|check| { check.id == "metric-status-complete" && check.result == "pass" })
        );
        assert!(
            report
                .checks
                .iter()
                .any(|check| { check.id == "boundary-policy-status" && check.result == "pass" })
        );
        assert!(report.warnings.is_empty());
    }

    #[test]
    fn validation_report_detects_duplicate_and_uncovered_local_target() {
        let mut metric_status = BTreeMap::new();
        metric_status.insert(
            "boundaryViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );
        metric_status.insert(
            "abstractionViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );
        let document = Sig0Document {
            schema_version: SCHEMA_VERSION.to_string(),
            root: ".".to_string(),
            component_kind: COMPONENT_KIND.to_string(),
            components: vec![
                Component {
                    id: "Formal".to_string(),
                    path: "Formal.lean".to_string(),
                },
                Component {
                    id: "Formal".to_string(),
                    path: "FormalDuplicate.lean".to_string(),
                },
            ],
            edges: vec![Edge {
                source: "Formal".to_string(),
                target: "Formal.Arch.Missing".to_string(),
                kind: "import".to_string(),
                evidence: "import Formal.Arch.Missing".to_string(),
            }],
            policies: Policies {
                boundary_allowed: Vec::new(),
                abstraction_allowed: Vec::new(),
                policy_id: None,
                schema_version: None,
                boundary_group_count: None,
                abstraction_relation_count: None,
            },
            signature: Signature {
                has_cycle: 0,
                scc_max_size: 1,
                max_depth: 1,
                fanout_risk: 1,
                boundary_violation_count: 0,
                abstraction_violation_count: 0,
            },
            metric_status,
            policy_violations: Vec::new(),
            runtime_edge_evidence: Vec::new(),
            runtime_dependency_graph: None,
        };

        let report =
            validate_component_universe_report(&document, ".lake/sig0.json", DEFAULT_UNIVERSE_MODE)
                .expect("report validates");

        assert_eq!(report.summary.result, "fail");
        assert_eq!(report.summary.failed_check_count, 3);
        assert!(report.checks.iter().any(|check| {
            check.id == "component-id-nodup" && check.result == "fail" && check.count == Some(1)
        }));
        assert!(report.checks.iter().any(|check| {
            check.id == "edge-endpoint-resolved" && check.result == "fail" && check.count == Some(1)
        }));
        assert!(report.checks.iter().any(|check| {
            check.id == "edge-closure-local" && check.result == "fail" && check.count == Some(1)
        }));
    }

    #[test]
    fn validation_report_warns_about_external_targets_in_local_only_mode() {
        let mut document = extract_sig0(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/minimal")
                .as_path(),
        )
        .expect("fixture extracts");
        document.edges.push(Edge {
            source: "Formal".to_string(),
            target: "Mathlib.Data.List.Basic".to_string(),
            kind: "import".to_string(),
            evidence: "import Mathlib.Data.List.Basic".to_string(),
        });

        let report =
            validate_component_universe_report(&document, ".lake/sig0.json", DEFAULT_UNIVERSE_MODE)
                .expect("report validates");

        assert_eq!(report.summary.external_edge_count, 1);
        assert!(report.checks.iter().any(|check| {
            check.id == "external-edge-targets" && check.result == "warn" && check.count == Some(1)
        }));
        assert_eq!(
            report.warnings,
            vec!["local-only universe excludes external or synthetic import targets".to_string()]
        );
    }

    #[test]
    fn builds_empirical_dataset_with_comparable_and_unmeasured_deltas() {
        let before = sig0_document_for_edges(
            vec![
                ("A", "A.lean"),
                ("B", "B.lean"),
                ("C", "C.lean"),
                ("D", "D.lean"),
            ],
            vec![("A", "B")],
        );
        let after = sig0_document_for_edges(
            vec![
                ("A", "A.lean"),
                ("B", "B.lean"),
                ("C", "C.lean"),
                ("D", "D.lean"),
            ],
            vec![("A", "B"), ("A", "C"), ("C", "D")],
        );

        let dataset = build_empirical_dataset(&before, &after, dataset_input(), "head")
            .expect("dataset builds");

        assert_eq!(dataset.schema_version, EMPIRICAL_DATASET_SCHEMA_VERSION);
        assert_eq!(dataset.signature_before.commit.sha, "base-sha");
        assert_eq!(dataset.signature_after.commit.role, "head");
        assert_eq!(dataset.delta_signature_signed.fanout_risk, Some(2));
        assert_eq!(dataset.delta_signature_signed.max_fanout, Some(1));
        assert_eq!(dataset.delta_signature_signed.reachable_cone_size, Some(2));
        assert_eq!(
            dataset.delta_signature_signed.boundary_violation_count,
            None
        );
        assert_eq!(dataset.signature_after.signature.weighted_scc_risk, None);
        assert!(
            !dataset
                .signature_after
                .metric_status
                .get("weightedSccRisk")
                .expect("weighted status")
                .measured
        );
        assert_eq!(dataset.signature_after.signature.runtime_propagation, None);
        assert!(
            !dataset
                .signature_after
                .metric_status
                .get("runtimePropagation")
                .expect("runtime status")
                .measured
        );

        let fanout_status = dataset
            .metric_delta_status
            .get("fanoutRisk")
            .expect("fanout delta status");
        assert!(fanout_status.comparable);
        assert!(fanout_status.before_measured);
        assert!(fanout_status.after_measured);

        let boundary_status = dataset
            .metric_delta_status
            .get("boundaryViolationCount")
            .expect("boundary delta status");
        assert!(!boundary_status.comparable);
        assert!(!boundary_status.before_measured);
        assert!(!boundary_status.after_measured);
        assert!(
            boundary_status
                .reason
                .contains("policy file not provided before")
                || boundary_status.reason.contains("policy file not provided")
        );
    }

    #[test]
    fn dataset_merge_role_uses_merge_commit() {
        let document = sig0_document_for_edges(vec![("A", "A.lean")], Vec::new());
        let dataset = build_empirical_dataset(&document, &document, dataset_input(), "merge")
            .expect("dataset builds");

        assert_eq!(dataset.signature_after.commit.sha, "merge-sha");
        assert_eq!(
            dataset.analysis_metadata.signature_after_commit_role,
            "merge"
        );
    }

    #[test]
    fn detects_cycle_fixture_metrics() {
        let components = vec![
            Component {
                id: "A".to_string(),
                path: "A.lean".to_string(),
            },
            Component {
                id: "B".to_string(),
                path: "B.lean".to_string(),
            },
        ];
        let edges = vec![
            Edge {
                source: "A".to_string(),
                target: "B".to_string(),
                kind: "import".to_string(),
                evidence: "import B".to_string(),
            },
            Edge {
                source: "B".to_string(),
                target: "A".to_string(),
                kind: "import".to_string(),
                evidence: "import A".to_string(),
            },
        ];

        let signature = compute_signature(&components, &edges);

        assert_eq!(signature.has_cycle, 1);
        assert_eq!(signature.scc_max_size, 2);
        assert_eq!(signature.fanout_risk, 2);
    }

    fn sig0_document_for_edges(
        components: Vec<(&str, &str)>,
        edge_pairs: Vec<(&str, &str)>,
    ) -> Sig0Document {
        let components: Vec<Component> = components
            .into_iter()
            .map(|(id, path)| Component {
                id: id.to_string(),
                path: path.to_string(),
            })
            .collect();
        let edges: Vec<Edge> = edge_pairs
            .into_iter()
            .map(|(source, target)| Edge {
                source: source.to_string(),
                target: target.to_string(),
                kind: "import".to_string(),
                evidence: format!("import {target}"),
            })
            .collect();
        let signature = compute_signature(&components, &edges);
        let mut metric_status = BTreeMap::new();
        for axis in ["hasCycle", "sccMaxSize", "maxDepth", "fanoutRisk"] {
            metric_status.insert(axis.to_string(), measured_status("archsig:import-graph"));
        }
        metric_status.insert(
            "boundaryViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );
        metric_status.insert(
            "abstractionViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );

        Sig0Document {
            schema_version: SCHEMA_VERSION.to_string(),
            root: ".".to_string(),
            component_kind: COMPONENT_KIND.to_string(),
            components,
            edges,
            policies: Policies {
                boundary_allowed: Vec::new(),
                abstraction_allowed: Vec::new(),
                policy_id: None,
                schema_version: None,
                boundary_group_count: None,
                abstraction_relation_count: None,
            },
            signature,
            metric_status,
            policy_violations: Vec::new(),
            runtime_edge_evidence: Vec::new(),
            runtime_dependency_graph: None,
        }
    }

    fn air_fixture_document(fixture: &str) -> AirDocumentV0 {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/air")
            .join(fixture);
        let contents = std::fs::read_to_string(&path).expect("AIR fixture is readable");
        serde_json::from_str(&contents).expect("AIR fixture parses")
    }

    fn dataset_input() -> EmpiricalDatasetInput {
        EmpiricalDatasetInput {
            repository: RepositoryRef {
                owner: "example".to_string(),
                name: "service".to_string(),
                default_branch: "main".to_string(),
            },
            pull_request: PullRequestRef {
                number: 42,
                author: "alice".to_string(),
                created_at: "2026-04-01T00:00:00Z".to_string(),
                merged_at: Some("2026-04-02T00:00:00Z".to_string()),
                base_commit: "base-sha".to_string(),
                head_commit: "head-sha".to_string(),
                merge_commit: Some("merge-sha".to_string()),
                labels: vec!["feature".to_string()],
                is_bot_generated: false,
            },
            pr_metrics: PullRequestMetrics {
                changed_files: 2,
                changed_lines_added: 20,
                changed_lines_deleted: 5,
                changed_components: vec!["A".to_string(), "C".to_string()],
                review_comment_count: 1,
                review_thread_count: 1,
                review_round_count: 1,
                first_review_latency_hours: Some(2.0),
                approval_latency_hours: Some(6.0),
                merge_latency_hours: Some(12.0),
            },
            issue_incident_links: Vec::new(),
            analysis_metadata: AnalysisMetadata::default(),
        }
    }
}
