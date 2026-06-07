use crate::{
    AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION, AI_PROPOSAL_GOVERNANCE_SCHEMA_VERSION,
    AIR_SCHEMA_VERSION, ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION,
    ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION, ARCHITECTURE_POLICY_SCHEMA_VERSION,
    ARCHITECTURE_POLICY_VALIDATION_REPORT_SCHEMA_VERSION, ARCHMAP_SCHEMA_VERSION,
    ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION, ARCHSIG_ANALYSIS_PACKET_V1_SCHEMA,
    CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION, CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION,
    DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION,
    FEATURE_EXTENSION_REPORT_SCHEMA_VERSION, FORECAST_CONE_SKELETON_SCHEMA_VERSION,
    HYPOTHESIS_REFRESH_CYCLE_SCHEMA_VERSION, INCIDENT_CORRELATION_MONITOR_SCHEMA_VERSION,
    INTENT_ARCHMAP_ALIGNMENT_SCHEMA_VERSION, INTENT_CALIBRATION_RECORD_SCHEMA_VERSION,
    INTENTMAP_SCHEMA_VERSION, LAW_VIOLATION_REPORT_SCHEMA_VERSION,
    OBSTRUCTION_WITNESS_SCHEMA_VERSION, OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION,
    OWNERSHIP_BOUNDARY_MONITOR_SCHEMA_VERSION, PR_FORCE_REPORT_SCHEMA_VERSION,
    PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION, REPAIR_ADOPTION_RECORD_SCHEMA_VERSION,
    REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION, SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION,
    SCHEMA_VERSION, SCHEMA_VERSION_CATALOG_SCHEMA_VERSION, SFT_REVIEW_SUMMARY_SCHEMA_VERSION,
    SIGNATURE_TRAJECTORY_REPORT_SCHEMA_VERSION, SchemaCompatibilityBoundaryV0,
    SchemaCompatibilityDimensionV0, SchemaCompatibilityPolicyV0, SchemaVersionCatalogEntryV0,
    SchemaVersionCatalogV0, TEAM_THRESHOLD_POLICY_SCHEMA_VERSION,
};

pub fn static_schema_version_catalog() -> SchemaVersionCatalogV0 {
    let catalog_version = "b10-schema-catalog-v0";
    SchemaVersionCatalogV0 {
        schema_version: SCHEMA_VERSION_CATALOG_SCHEMA_VERSION.to_string(),
        catalog_id: "archsig-b9-b10-schema-version-catalog".to_string(),
        catalog_version: catalog_version.to_string(),
        phase: "B9 Schema standardization and compatibility / B10 operational feedback".to_string(),
        artifacts: vec![
            artifact(
                "signature-artifact",
                "Architecture Signature artifact",
                SCHEMA_VERSION,
                "extractor-output",
                "B0-B8",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#4-architecture-signature-artifact-layer",
                    "docs/design/archsig_tooling_index.md",
                ],
                vec![],
                compatibility_boundary(
                    "Map component/relation/signature fields by stable camelCase names; new axes must be added with metricStatus boundary metadata.",
                    vec![],
                    vec![
                        "New required axes must declare measuredZero/measuredNonzero/unmeasured/outOfScope semantics.",
                    ],
                    vec![
                        "metricStatus is the compatibility boundary for coverage and exactness of Sig0 axes.",
                    ],
                ),
            ),
            artifact(
                "air",
                "Architecture Intermediate Representation",
                AIR_SCHEMA_VERSION,
                "intermediate-representation",
                "B0-B9",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#31-air-v0-schema",
                    "docs/design/archsig_tooling_index.md",
                ],
                vec!["#608", "#609"],
                compatibility_boundary(
                    "Map ids, relation refs, evidence refs, claims, coverage layers, and theorem-package refs explicitly; never infer a formal claim from renamed fields.",
                    vec![],
                    vec![
                        "New required theorem, coverage, projection, or exactness assumptions must be listed in claims or coverage layers.",
                    ],
                    vec![
                        "AIR coverage layers and claim classifications are the exactness boundary for report generation.",
                    ],
                ),
            ),
            artifact(
                "archmap",
                "ArchMap supplied JSON artifact",
                ARCHMAP_SCHEMA_VERSION,
                "semantic-observation-input",
                "ArchMap MVP",
                "implemented",
                vec![
                    "docs/tool/README.md",
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                    "tools/fieldsig/docs/artifacts-and-boundaries.md",
                ],
                vec!["#1032", "#1033", "#1035", "#1228", "#1246"],
                compatibility_boundary(
                    "Map source inventory, prompt/model provenance, atom candidates, molecule candidates, obstruction circuit candidates, observation gaps, AAT-facing and SFT-facing map items, coverage, conflicts, and non-conclusions by stable camelCase names.",
                    vec![],
                    vec![
                        "New mapping kinds must preserve source refs, claim boundary, missing evidence, and non-conclusions.",
                        "New atomic observation fields must remain optional/default-compatible in archmap-v0 unless schemaVersion is deliberately bumped.",
                        "SFT-facing mapping kinds must remain projection input and not forecast result claims.",
                    ],
                    vec![
                        "ArchMap is supplied JSON evidence, not architecture ground truth, certified ArchitectureAtom truth, or a Lean theorem claim.",
                    ],
                ),
            ),
            artifact(
                "archmap-validation-report",
                "ArchMap Validation Report",
                ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION,
                "validation-output",
                "ArchMap MVP",
                "implemented",
                vec![
                    "docs/tool/README.md",
                    "tools/archsig/docs/commands.md",
                    "tools/fieldsig/docs/commands.md",
                ],
                vec!["#1032", "#1034", "#1229", "#1245"],
                compatibility_boundary(
                    "Keep source inventory checks, source ref checks, claim boundary checks, semantic coverage checks, conflict checks, projection-separation checks, formal promotion guardrail checks, and atomic observation summary separate.",
                    vec![],
                    vec![
                        "New checks must report whether they fail, warn, or pass without promoting uncertain mappings.",
                        "Atomic observation checks must distinguish atom candidates, molecule candidates, obstruction circuit candidates, and observation gaps.",
                    ],
                    vec![
                        "Validation pass does not imply semantic correctness, completeness, architecture lawfulness, certified atom truth, zero curvature, or SFT forecast correctness.",
                    ],
                ),
            ),
            artifact(
                "architecture-policy",
                "Architecture policy artifact",
                ARCHITECTURE_POLICY_SCHEMA_VERSION,
                "law-aware-review-policy",
                "ArchMap law-aware review",
                "implemented",
                vec![
                    "docs/tool/README.md",
                    "tools/archsig/docs/commands.md",
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                ],
                vec!["#1162"],
                compatibility_boundary(
                    "Map adopted laws, layer selectors, dependency rules, exceptions, and SRP taxonomy explicitly; do not infer policy from repository shape.",
                    vec![],
                    vec![
                        "New law families must declare deterministic versus LLM-review enforcement boundary.",
                    ],
                    vec![
                        "Architecture policy is review evidence, not a Lean theorem or architecture lawfulness proof.",
                    ],
                ),
            ),
            artifact(
                "architecture-policy-validation-report",
                "Architecture policy validation report",
                ARCHITECTURE_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
                "validation-output",
                "ArchMap law-aware review",
                "implemented",
                vec!["tools/archsig/docs/commands.md"],
                vec!["#1162"],
                compatibility_boundary(
                    "Keep identity, adopted law, layer selector, dependency rule, SRP evidence, and non-conclusion checks separate.",
                    vec![],
                    vec!["New checks must distinguish fail, warn, and unmeasured policy evidence."],
                    vec![
                        "Validation pass does not imply architecture lawfulness or SRP violation.",
                    ],
                ),
            ),
            artifact(
                "law-violation-report",
                "Law violation report",
                LAW_VIOLATION_REPORT_SCHEMA_VERSION,
                "review-output",
                "ArchMap law-aware review",
                "implemented",
                vec![
                    "tools/archsig/docs/commands.md",
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                ],
                vec!["#1164", "#1165"],
                compatibility_boundary(
                    "Map deterministic Layered findings, allowed exceptions, SRP cues, unmeasured selectors, review actions, and non-conclusions explicitly.",
                    vec![],
                    vec![
                        "New law findings must preserve evidence refs and policy refs before review classification.",
                    ],
                    vec![
                        "Layered findings are selected-universe tooling evidence and SRP cues are not tool-only violations.",
                    ],
                ),
            ),
            artifact(
                "archmap-generation-protocol",
                "ArchMap generation protocol",
                "archmap-generation-protocol-v0",
                "external-agent-protocol",
                "ArchMap v2",
                "implemented",
                vec!["docs/tool/README.md", "tools/archsig/docs/commands.md"],
                vec!["#1139"],
                compatibility_boundary(
                    "Map source inventory refs, prompt pack refs, model provenance, required workflow, and private / unavailable generation boundary explicitly.",
                    vec![],
                    vec![
                        "New generation workflow fields must preserve model provenance and validation boundary.",
                    ],
                    vec![
                        "Generation protocol does not execute the model or prove the generated ArchMap correct.",
                    ],
                ),
            ),
            artifact(
                "intentmap",
                "IntentMap supplied JSON artifact",
                INTENTMAP_SCHEMA_VERSION,
                "planning-intent-input",
                "PRD v3",
                "implemented",
                vec!["docs/tool/archsig_archmap_prd_v3.md"],
                vec!["#1149", "#1150", "#1156"],
                compatibility_boundary(
                    "Map intent source refs, LLM provenance, intent items, missing decisions, ambiguous intents, missing evidence, and non-conclusions by stable camelCase names.",
                    vec![],
                    vec![
                        "New intent kinds must preserve source refs, claim classification, confidence boundary, missing decisions, and non-conclusions.",
                    ],
                    vec![
                        "IntentMap is LLM-authored planning evidence, not implementation truth, forecast correctness, or a complete plan.",
                    ],
                ),
            ),
            artifact(
                "intent-archmap-alignment",
                "IntentMap to ArchMap AlignmentMap",
                INTENT_ARCHMAP_ALIGNMENT_SCHEMA_VERSION,
                "planning-alignment-input",
                "PRD v3",
                "implemented",
                vec![
                    "docs/tool/archsig_archmap_prd_v3.md",
                    "tools/fieldsig/docs/commands.md",
                ],
                vec!["#1151", "#1152", "#1154", "#1156"],
                compatibility_boundary(
                    "Map intent refs, ArchMap refs, alignment kind, preserves / forgets, confidence, unaligned / unsupported / ambiguous boundaries, missing evidence, and non-conclusions explicitly.",
                    vec![],
                    vec![
                        "New alignment kinds must keep intentUnaligned / unsupported / ambiguous states distinct from measured zero.",
                    ],
                    vec![
                        "AlignmentMap validation does not prove semantic correctness, implementation impact, quality, causality, or future outcome.",
                    ],
                ),
            ),
            artifact(
                "operation-support-estimate",
                "Operation support estimate",
                OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION,
                "bounded-forecast-input",
                "SFT review judgement",
                "implemented",
                vec![
                    "docs/tool/roadmap.md",
                    "tools/fieldsig/docs/commands.md",
                    "tools/fieldsig/docs/artifacts-and-boundaries.md",
                ],
                vec!["#1182", "#1184", "#1185"],
                compatibility_boundary(
                    "Map candidate operation families, policy constraints, support disposition, governance action refs, forbidden support, unknown remainder, and evidence boundary explicitly.",
                    vec![],
                    vec![
                        "New policy fields must preserve allowed, conditionallyAllowed, forbidden, and unknown distinctions.",
                    ],
                    vec![
                        "Operation support is bounded evidence, not actual future support or policy safety proof.",
                    ],
                ),
            ),
            artifact(
                "archsig-analysis-packet-v1",
                "ArchSig v1 typed evaluator analysis packet",
                ARCHSIG_ANALYSIS_PACKET_V1_SCHEMA,
                "current-state-handoff",
                "ArchSig v1 / FieldSig handoff",
                "implemented",
                vec![
                    "docs/tool/archmap_minimal_observation_contract_prd.md",
                    "docs/tool/llm_native_e2e_workflow.md",
                    "tools/fieldsig/README.md",
                ],
                vec!["#1842"],
                compatibility_boundary(
                    "Map schema, inputRefs, typed evaluator results, architecture distance, generated packet refs, spectrum, homotopy, structural reading refs, bounded conclusions, detail refs, and non-conclusions explicitly.",
                    vec![],
                    vec![
                        "New ArchSig handoff readings must preserve packet refs and keep unmeasured / blocked / unknown statuses distinct from measured zero.",
                        "FieldSig must not treat raw ArchMap atoms or ArchSig current-state refs as forecast truth.",
                    ],
                    vec![
                        "ArchSig v1 packet compatibility is a FieldSig handoff JSON contract, not a semantic-preservation theorem, Lean proof, forecast correctness claim, or repair safety proof.",
                    ],
                ),
            ),
            artifact(
                "forecast-cone-skeleton",
                "ForecastCone skeleton",
                FORECAST_CONE_SKELETON_SCHEMA_VERSION,
                "bounded-forecast-artifact",
                "SFT review judgement",
                "implemented",
                vec![
                    "docs/tool/roadmap.md",
                    "tools/fieldsig/docs/commands.md",
                    "tools/fieldsig/docs/artifacts-and-boundaries.md",
                ],
                vec!["#1185"],
                compatibility_boundary(
                    "Map finite support, bounded horizon, path classes, gluing evidence, governance interventions, typed boundary failures, forecast boundary, unknown remainder, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New future evidence must keep gluing, governance, and typed boundary failure refs source-bound.",
                    ],
                    vec![
                        "ForecastCone does not assign probability, causal prediction, global safety, or theorem proof.",
                    ],
                ),
            ),
            artifact(
                "consequence-envelope-report",
                "ConsequenceEnvelope report",
                CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION,
                "review-projection",
                "SFT review judgement",
                "implemented",
                vec![
                    "docs/tool/roadmap.md",
                    "tools/fieldsig/docs/commands.md",
                    "tools/fieldsig/docs/artifacts-and-boundaries.md",
                ],
                vec!["#1182", "#1185"],
                compatibility_boundary(
                    "Map affected regions, axes, deltas, obstruction candidates, missing boundaries, typed failures, reviewer actions, theorem boundaries, recommendations, and unknown remainder explicitly.",
                    vec![],
                    vec![
                        "New reviewer-facing fields must preserve evidence refs and boundary refs.",
                    ],
                    vec![
                        "ConsequenceEnvelope is report projection, not final judgement, causality proof, or Lean theorem.",
                    ],
                ),
            ),
            artifact(
                "sft-review-summary",
                "SFT review summary",
                SFT_REVIEW_SUMMARY_SCHEMA_VERSION,
                "review-judgement-input",
                "SFT review judgement",
                "implemented",
                vec![
                    "docs/tool/roadmap.md",
                    "tools/fieldsig/docs/commands.md",
                    "tools/fieldsig/docs/artifacts-and-boundaries.md",
                ],
                vec!["#1182", "#1183", "#1186"],
                compatibility_boundary(
                    "Map opened futures, closed futures, boundary failures, next actions, evidence refs, boundary refs, and LLM judgement contract without making the LLM call.",
                    vec![],
                    vec![
                        "New judgement statuses must remain bounded triage and require evidence refs.",
                    ],
                    vec![
                        "SFT review summary is deterministic projection, not merge approval, probability claim, or theorem proof.",
                    ],
                ),
            ),
            artifact(
                "pr-quality-analysis",
                "PR Quality Analysis report",
                PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION,
                "review-output",
                "PRD v3",
                "implemented",
                vec![
                    "docs/tool/archsig_archmap_prd_v3.md",
                    "tools/archsig/docs/commands.md",
                ],
                vec!["#1153"],
                compatibility_boundary(
                    "Map ArchMap, AIR, theorem-check, feature-report, and policy-decision refs to reviewer-facing cues and missing evidence without automatic merge approval.",
                    vec![],
                    vec![
                        "New cue kinds must declare evidence boundary and avoid merge-decision or architecture-lawfulness claims.",
                    ],
                    vec![
                        "PR quality analysis is review evidence, not merge approval or a global architecture ranking.",
                    ],
                ),
            ),
            artifact(
                "aat-observable-bundle",
                "AAT Observable Bundle",
                AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION,
                "aat-observable-review-bundle",
                "AAT observable bridge",
                "implemented",
                vec![
                    "docs/tool/aat_archsig_reduction.md",
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                    "tools/archsig/docs/commands.md",
                ],
                vec![
                    "#1166", "#1167", "#1168", "#1169", "#1170", "#1171", "#1172", "#1173",
                    "#1174", "#1175", "#1176", "#1177", "#1178", "#1179",
                ],
                compatibility_boundary(
                    "Map AAT concepts, source refs, selected universe, witness refs, operation candidates, theorem boundaries, review actions, and responsibility splits without promoting tooling evidence to proof.",
                    vec![],
                    vec![
                        "New AAT concept mappings must declare expressibility, retention, reviewability, measurement status, responsibility, and non-conclusions.",
                        "New measured axes must keep measuredZero, measuredNonzero, unmeasured, outOfScope, private, unavailable, unsupported, and dynamic boundaries distinct.",
                    ],
                    vec![
                        "AAT Observable Bundle is a review artifact bundle, not AAT itself, extractor completeness, global lawfulness proof, or merge approval.",
                    ],
                ),
            ),
            artifact(
                "intent-calibration-record",
                "Intent calibration record",
                INTENT_CALIBRATION_RECORD_SCHEMA_VERSION,
                "empirical-feedback",
                "PRD v3",
                "implemented",
                vec![
                    "docs/tool/archsig_archmap_prd_v3.md",
                    "docs/tool/sft_calibration_benchmark.md",
                ],
                vec!["#1157"],
                compatibility_boundary(
                    "Map IntentMap item refs, forecast item refs, observed implementation refs, missing decision statuses, and forecast usefulness feedback separately.",
                    vec![],
                    vec![
                        "New calibration fields must distinguish observed evidence, missing decision status, and qualitative usefulness feedback.",
                    ],
                    vec![
                        "Calibration is empirical feedback, not causal proof or forecast correctness proof.",
                    ],
                ),
            ),
            artifact(
                "feature-extension-report",
                "Feature Extension Report",
                FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
                "review-output",
                "B1-B9",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#5-feature-extension-report",
                    "docs/design/archsig_tooling_index.md",
                ],
                vec!["#608", "#609"],
                compatibility_boundary(
                    "Map review summary, witness, theorem precondition, coverage gap, repair suggestion, and non-conclusion fields separately.",
                    vec![],
                    vec![
                        "New required review assumptions must appear in discharged/undischarged assumptions or theorem precondition checks.",
                    ],
                    vec![
                        "Coverage gaps, runtime summary, semantic summary, and non-conclusions delimit report exactness.",
                    ],
                ),
            ),
            artifact(
                "obstruction-witness",
                "Obstruction Witness",
                OBSTRUCTION_WITNESS_SCHEMA_VERSION,
                "embedded-witness",
                "B1-B9",
                "implemented",
                vec!["docs/aat_v2_tooling_design.md#6-obstruction-witness-schema"],
                vec!["#608", "#610"],
                compatibility_boundary(
                    "Map witness id, layer, kind, extension role, classification, evidence, theorem refs, claim classification, measurement boundary, and non-conclusions independently.",
                    vec![],
                    vec![
                        "New witness kinds must declare layer, evidence requirements, measurement boundary, and non-conclusions.",
                    ],
                    vec![
                        "Witness measurement boundary and claim classification distinguish measured evidence from formal theorem claims.",
                    ],
                ),
            ),
            artifact(
                "architecture-drift-ledger",
                "Architecture Drift Ledger",
                ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION,
                "batch-history-output",
                "B1-B9",
                "implemented",
                vec!["docs/aat_v2_tooling_design.md#51-architecture-drift-ledger"],
                vec!["#608", "#610"],
                compatibility_boundary(
                    "Map stable grouping keys, aggregation window, source, metric, status, suppression, repair, witness, claim, and non-conclusion fields separately.",
                    vec![],
                    vec![
                        "New batch metrics must declare grouping key, aggregation window, measurement boundary, and evidence refs.",
                    ],
                    vec![
                        "Ledger status and suppression metadata are operational state, not formal proof state.",
                    ],
                ),
            ),
            artifact(
                "detectable-values-reported-axes-catalog",
                "Detectable values / reported axes catalog",
                DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION,
                "axis-catalog",
                "B9",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#41-detectable-values--reported-axes",
                    "docs/design/schema_version_catalog.md#detectable-values--reported-axes-catalog",
                ],
                vec!["#608"],
                compatibility_boundary(
                    "Map axis id, layer, value type, measurement boundary, evidence requirements, theorem refs, and non-conclusions explicitly.",
                    vec![],
                    vec![
                        "New reported axes must declare whether unmeasured differs from measured zero.",
                    ],
                    vec![
                        "Axis coverage and exactness metadata delimit what a zero or nonzero value can support.",
                    ],
                ),
            ),
            artifact(
                "report-outcome-daily-ledger",
                "Report outcome daily ledger",
                REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION,
                "operational-feedback-output",
                "B10",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#phase-b10-operational-feedback-loop",
                    "docs/design/schema_version_catalog.md#report-outcome-daily-ledger-metadata",
                ],
                vec!["#620"],
                compatibility_boundary(
                    "Map aggregation window, source report refs, retention policy, outcome metric summaries, missing/private/unmeasured boundaries, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New daily batch metrics must preserve source report refs, retention policy, and missing/private/unmeasured boundary counts.",
                    ],
                    vec![
                        "Missing, private, unavailable, and unmeasured outcome data delimit the operational feedback exactness boundary.",
                    ],
                ),
            ),
            artifact(
                "calibration-review-record",
                "Calibration review record",
                CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION,
                "operational-feedback-input",
                "B10",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#phase-b10-operational-feedback-loop",
                    "docs/design/schema_version_catalog.md#calibration-review-record-metadata",
                ],
                vec!["#621"],
                compatibility_boundary(
                    "Map report finding refs, witness refs, reviewer decision, outcome refs, confidence, missing evidence, calibration input, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New calibration fields must preserve missing / private evidence boundaries and formal-claim non-conclusions.",
                    ],
                    vec![
                        "Reviewer decision, confidence, missing evidence, and calibration input delimit empirical policy tuning exactness.",
                    ],
                ),
            ),
            artifact(
                "team-threshold-policy",
                "Team threshold policy",
                TEAM_THRESHOLD_POLICY_SCHEMA_VERSION,
                "operational-feedback-policy",
                "B10",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#phase-b10-operational-feedback-loop",
                    "docs/design/schema_version_catalog.md#team-threshold-policy-metadata",
                ],
                vec!["#622"],
                compatibility_boundary(
                    "Map team scope, effective period, per-axis thresholds, CI modes, calibration sources, rollback policy, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New threshold axes must preserve warn / fail / advisory mode and calibration source refs.",
                    ],
                    vec![
                        "Team-local threshold policy and calibration source boundaries delimit empirical policy tuning exactness.",
                    ],
                ),
            ),
            artifact(
                "ownership-boundary-monitor",
                "Ownership boundary monitor",
                OWNERSHIP_BOUNDARY_MONITOR_SCHEMA_VERSION,
                "operational-feedback-monitor",
                "B10",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#phase-b10-operational-feedback-loop",
                    "docs/design/schema_version_catalog.md#ownership-boundary-monitor-metadata",
                ],
                vec!["#623"],
                compatibility_boundary(
                    "Map source refs, ownership scopes, boundary erosion signals, missing evidence, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New ownership or boundary erosion metrics must preserve measurement boundary and missing / private evidence refs.",
                    ],
                    vec![
                        "Ownership scope and boundary erosion signal metadata delimit empirical monitoring exactness.",
                    ],
                ),
            ),
            artifact(
                "repair-adoption-record",
                "Repair adoption record",
                REPAIR_ADOPTION_RECORD_SCHEMA_VERSION,
                "operational-feedback-record",
                "B10",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#phase-b10-operational-feedback-loop",
                    "docs/design/schema_version_catalog.md#repair-adoption-record-metadata",
                ],
                vec!["#623"],
                compatibility_boundary(
                    "Map suggestion refs, adopted / rejected / deferred decision, follow-up outcomes, side-effect notes, missing evidence, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New adoption fields must preserve repair suggestion traceability, workflow state, side effects, and missing / private evidence boundaries.",
                    ],
                    vec![
                        "Repair adoption workflow state and follow-up outcome refs delimit empirical repair tracking exactness.",
                    ],
                ),
            ),
            artifact(
                "incident-correlation-monitor",
                "Incident / rollback / MTTR correlation monitor",
                INCIDENT_CORRELATION_MONITOR_SCHEMA_VERSION,
                "operational-feedback-monitor",
                "B10",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#phase-b10-operational-feedback-loop",
                    "docs/design/schema_version_catalog.md#incident-correlation-monitor-metadata",
                ],
                vec!["#624"],
                compatibility_boundary(
                    "Map correlation window, source refs, metric axes, correlations, confounder notes, missing / private data, refresh decision, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New incident correlation fields must preserve source refs, metric axes, confounder notes, and missing / private evidence boundaries.",
                    ],
                    vec![
                        "Correlation observations, confounders, and missing / private data delimit empirical incident-monitoring exactness.",
                    ],
                ),
            ),
            artifact(
                "hypothesis-refresh-cycle",
                "Empirical hypothesis refresh cycle",
                HYPOTHESIS_REFRESH_CYCLE_SCHEMA_VERSION,
                "operational-feedback-research-cycle",
                "B10",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#phase-b10-operational-feedback-loop",
                    "docs/design/schema_version_catalog.md#hypothesis-refresh-cycle-metadata",
                ],
                vec!["#624"],
                compatibility_boundary(
                    "Map source monitor refs, versioned hypothesis refs, change reasons, refresh decision, retained / rejected hypotheses, proposed updates, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New refresh fields must preserve hypothesis version refs, disposition rationale, source refs, and formal-claim non-conclusions.",
                    ],
                    vec![
                        "Hypothesis dispositions and refresh decisions delimit empirical research tracking exactness.",
                    ],
                ),
            ),
            artifact(
                "pr-force-report",
                "PR Force Report",
                PR_FORCE_REPORT_SCHEMA_VERSION,
                "architecture-dynamics-output",
                "D5-D6",
                "implemented",
                vec![
                    "docs/design/architecture_dynamics_tooling_design.md#pr-force-report-v0",
                    "docs/design/architecture_signature_dynamics.md#layer-4-pr-force-model",
                ],
                vec!["#675"],
                compatibility_boundary(
                    "Map accepted PR transition refs, signed Signature deltas, observed force vector slots, decomposition components, evidence refs, measurement boundary, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New force axes must declare MeasurementStatus, source artifact refs, and whether they are observed, latent, dissipated, or advisory.",
                    ],
                    vec![
                        "ObservedForce excludes rejected raw proposal force; heuristic decomposition remains advisory tooling evidence.",
                    ],
                ),
            ),
            artifact(
                "architecture-dynamics-metrics-report",
                "Architecture Dynamics Metrics Report",
                ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION,
                "architecture-dynamics-output",
                "D5-D6",
                "implemented",
                vec![
                    "docs/design/architecture_dynamics_tooling_design.md#architecture-dynamics-metrics-report-v0",
                    "docs/design/architecture_signature_dynamics.md#quantitative-metric-derivation",
                ],
                vec!["#671", "#718"],
                compatibility_boundary(
                    "Map repository, selected window, source refs, trajectory / force / gap / field-control / AI dynamics / attractor-engineering metric groups, basin simulations, field shaping signals, readiness axes, measurement boundary, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New dynamics metrics must declare MeasurementStatus, source refs, measurement boundary, assumptions, and non-conclusions.",
                        "New basin simulations must declare selected initial states, finite operation scripts, selected regions, bounded horizon, classification status, missing evidence, and non-conclusions.",
                        "New field shaping signals must declare selected signal, source refs, confidence, measurement boundary, and non-conclusions.",
                        "VibeCodingReadiness must remain a multi-axis readiness artifact, not a single numeric score.",
                    ],
                    vec![
                        "Metrics report remains a multi-axis diagnostic artifact and does not promote tooling evidence to Lean theorem claims.",
                        "BasinBoundaryFragility and TrajectoryReturnTime remain bounded simulation evidence, not global basin stability or recurrence theorems.",
                        "ObservedForce, LatentForceEstimate, and DissipatedForceEstimate remain separate force classes.",
                        "FieldShapingDelta uses notComparable when before/after measurement boundaries are not comparable.",
                    ],
                ),
            ),
            artifact(
                "signature-trajectory-report",
                "Signature Trajectory Report",
                SIGNATURE_TRAJECTORY_REPORT_SCHEMA_VERSION,
                "architecture-dynamics-output",
                "D5-D6",
                "implemented",
                vec![
                    "docs/design/architecture_dynamics_tooling_design.md#signature-trajectory-report-v0",
                    "docs/design/architecture_signature_dynamics.md#signature-trajectory-metrics",
                ],
                vec!["#676"],
                compatibility_boundary(
                    "Map repository, selected window, trajectory points, force refs, drift / stability / excursion / endpoint-compression signals, selected regions, measurement boundary, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New trajectory fields must preserve MeasurementStatus, source refs, selected region refs, and bounded-window assumptions.",
                        "Extractor, policy, or schema version differences require notComparable or explicit migration boundary evidence.",
                    ],
                    vec![
                        "Trajectory report remains finite observed trajectory tooling evidence, not a global attractor or basin theorem.",
                        "Endpoint safe-region membership does not imply path safety.",
                    ],
                ),
            ),
            artifact(
                "ai-proposal-governance",
                "AI Proposal Governance",
                AI_PROPOSAL_GOVERNANCE_SCHEMA_VERSION,
                "review-governance-output",
                "B14",
                "implemented",
                vec![
                    "docs/tool/ai_proposal_governance.md",
                    "tools/fieldsig/docs/artifacts-and-boundaries.md#sft-forecasting-input-artifacts",
                ],
                vec!["#900"],
                compatibility_boundary(
                    "Map proposal refs, prompt / policy boundary, support taxonomy, shortcut witnesses, review / CI mediation, posterior field update, evidence boundary, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New support categories must remain within allowed, conditionallyAllowed, forbidden, unknown, or outOfScope unless a schema migration records the boundary.",
                        "New mediation fields must preserve that policy compliance, review pass, and CI pass are not architecture lawfulness.",
                    ],
                    vec![
                        "AI proposal governance is reviewer-facing process evidence, not an AI safety theorem.",
                        "Posterior field update refs are calibration hooks, not causal proofs.",
                    ],
                ),
            ),
        ],
        compatibility_policy: compatibility_policy(catalog_version),
        non_conclusions: vec![
            "schema migration is not a semantic-preservation theorem".to_string(),
            "catalog membership does not imply extractor completeness".to_string(),
            "compatibility pass does not imply architecture lawfulness".to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
        ],
    }
}

fn artifact(
    artifact_id: &str,
    artifact_name: &str,
    schema_version_name: &str,
    artifact_role: &str,
    owner_phase: &str,
    status: &str,
    primary_docs: Vec<&str>,
    downstream_issues: Vec<&str>,
    compatibility_boundary: SchemaCompatibilityBoundaryV0,
) -> SchemaVersionCatalogEntryV0 {
    SchemaVersionCatalogEntryV0 {
        artifact_id: artifact_id.to_string(),
        artifact_name: artifact_name.to_string(),
        schema_version_name: schema_version_name.to_string(),
        artifact_role: artifact_role.to_string(),
        owner_phase: owner_phase.to_string(),
        status: status.to_string(),
        primary_docs: primary_docs.into_iter().map(str::to_string).collect(),
        downstream_issues: downstream_issues.into_iter().map(str::to_string).collect(),
        compatibility_boundary,
    }
}

fn compatibility_boundary(
    field_mapping_policy: &str,
    deprecated_fields: Vec<&str>,
    new_required_assumptions: Vec<&str>,
    coverage_exactness_boundary: Vec<&str>,
) -> SchemaCompatibilityBoundaryV0 {
    SchemaCompatibilityBoundaryV0 {
        field_mapping_policy: field_mapping_policy.to_string(),
        deprecated_fields: deprecated_fields.into_iter().map(str::to_string).collect(),
        new_required_assumptions: new_required_assumptions
            .into_iter()
            .map(str::to_string)
            .collect(),
        coverage_exactness_boundary: coverage_exactness_boundary
            .into_iter()
            .map(str::to_string)
            .collect(),
        non_conclusions: vec![
            "field mapping does not prove semantic preservation".to_string(),
            "missing coverage is not measured zero".to_string(),
            "renamed fields do not discharge new required assumptions".to_string(),
        ],
    }
}

fn compatibility_policy(catalog_version: &str) -> SchemaCompatibilityPolicyV0 {
    SchemaCompatibilityPolicyV0 {
        schema_version: SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION.to_string(),
        policy_id: "archsig-b9-schema-compatibility-policy".to_string(),
        policy_version: "b9-compatibility-policy-v0".to_string(),
        applies_to_catalog_version: catalog_version.to_string(),
        dimensions: vec![
            dimension(
                "field_mapping",
                vec![
                    "sourceField",
                    "targetField",
                    "mappingKind",
                    "requiredReview",
                ],
                "A checker may validate declared field mappings, but it must not infer semantic equivalence.",
            ),
            dimension(
                "deprecated_fields",
                vec!["field", "replacement", "removalPhase", "readerBehavior"],
                "Deprecated fields remain compatibility metadata until removal; migration must preserve explicit reader behavior.",
            ),
            dimension(
                "new_required_assumptions",
                vec![
                    "assumptionId",
                    "appliesTo",
                    "requiredFor",
                    "fallbackWhenMissing",
                ],
                "New assumptions must be reported as missing or undischarged unless explicit evidence is present.",
            ),
            dimension(
                "non_conclusions",
                vec!["nonConclusion", "appliesTo", "reason"],
                "Non-conclusions are mandatory guardrails and cannot be dropped by migration.",
            ),
            dimension(
                "coverage_exactness_boundary",
                vec![
                    "axisOrLayer",
                    "measurementBoundary",
                    "coverageAssumptions",
                    "exactnessAssumptions",
                ],
                "Coverage and exactness metadata delimit what any reported value can support.",
            ),
        ],
        required_checks: vec![
            "known schemaVersion in catalog".to_string(),
            "field mapping entries are explicit for renamed or removed fields".to_string(),
            "deprecated fields declare replacement or removal behavior".to_string(),
            "new required assumptions are surfaced as missing until discharged".to_string(),
            "non-conclusions are preserved or strengthened".to_string(),
            "coverage and exactness metadata are not dropped".to_string(),
        ],
        non_conclusions: vec![
            "compatibility policy is not a proof of semantic preservation".to_string(),
            "compatibility policy is not evidence of extractor completeness".to_string(),
            "compatibility policy is not a Lean theorem package".to_string(),
        ],
    }
}

fn dimension(
    dimension: &str,
    required_metadata: Vec<&str>,
    checker_boundary: &str,
) -> SchemaCompatibilityDimensionV0 {
    SchemaCompatibilityDimensionV0 {
        dimension: dimension.to_string(),
        required_metadata: required_metadata.into_iter().map(str::to_string).collect(),
        checker_boundary: checker_boundary.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    #[test]
    fn static_catalog_records_b9_schema_versions_and_boundaries() {
        let catalog = static_schema_version_catalog();
        assert_eq!(
            catalog.schema_version,
            SCHEMA_VERSION_CATALOG_SCHEMA_VERSION
        );
        assert_eq!(
            catalog.compatibility_policy.schema_version,
            SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION
        );
        assert!(
            catalog
                .non_conclusions
                .contains(&"schema migration is not a semantic-preservation theorem".to_string())
        );

        let versions: BTreeSet<_> = catalog
            .artifacts
            .iter()
            .map(|artifact| artifact.schema_version_name.as_str())
            .collect();
        for expected in [
            SCHEMA_VERSION,
            AIR_SCHEMA_VERSION,
            FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
            ARCHSIG_ANALYSIS_PACKET_V1_SCHEMA,
            OBSTRUCTION_WITNESS_SCHEMA_VERSION,
            ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION,
            DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION,
            CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION,
            INCIDENT_CORRELATION_MONITOR_SCHEMA_VERSION,
            HYPOTHESIS_REFRESH_CYCLE_SCHEMA_VERSION,
            PR_FORCE_REPORT_SCHEMA_VERSION,
        ] {
            assert!(
                versions.contains(expected),
                "missing schema version {expected}"
            );
        }

        for artifact in &catalog.artifacts {
            assert!(
                !artifact
                    .compatibility_boundary
                    .field_mapping_policy
                    .is_empty()
            );
            assert!(!artifact.compatibility_boundary.non_conclusions.is_empty());
            assert!(
                artifact
                    .compatibility_boundary
                    .non_conclusions
                    .iter()
                    .any(|non_conclusion| non_conclusion.contains("semantic preservation"))
            );
        }
    }

    #[test]
    fn canonical_fixture_matches_static_catalog() {
        let fixture: SchemaVersionCatalogV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/schema_version_catalog.json"
        ))
        .expect("schema version catalog fixture parses");
        assert_eq!(fixture, static_schema_version_catalog());
    }
}
