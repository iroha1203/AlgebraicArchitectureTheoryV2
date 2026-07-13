#![recursion_limit = "256"]

mod ag_measurement;
mod archmap;
pub mod authoring;
mod compare;
mod gate;
mod law_execution;
mod law_policy;
mod law_surface;
mod normalizer;
mod policy_bundle;
mod repair_plan;
mod saga;
mod schema;
mod schema_catalog;
mod validation;

pub use ag_measurement::{
    build_foundation_measurement_packet_v1, build_insight_brief_v1, build_insight_report_v1,
    build_measurement_summary_v1, build_measurement_viewer_data_v1,
    selected_measurement_profile_v1, validate_measurement_packet_value_v1,
};
pub use archmap::{
    compare_archmap_v2_doctrine, static_aat_atom_binding_vocabulary_v1,
    static_aat_atom_vocabulary_v1, validate_archmap_v2_report,
};
pub use authoring::{
    ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA, ARCHMAP_COVERAGE_LEDGER_CLAIM_BOUNDARY,
    ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA, ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA,
    ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA, AuthoringAuditInputV1, ExtractionDiffOptions,
    ScopeManifestOptions, archmap_authoring_audit_checks_v1, build_extraction_consistency_v1,
    build_scope_manifest_v1, validate_authoring_audit_input_v1, validate_candidate_packet_v1,
    validate_coverage_ledger_v1, validate_extraction_consistency_v1, validate_scope_manifest_v1,
};
pub use compare::build_comparison_artifacts_v1;
pub use gate::{build_gate_report_v1, validate_gate_policy_v1};
pub use law_policy::{
    expand_law_policy_v1, is_compatible_evaluator_condition, static_law_evaluator_registry_v1,
    validate_law_policy_v1_report, validate_measurement_profile_v1_checks,
};
pub use law_surface::{
    LAW_EQUATION_SURFACE_V1_SCHEMA, LAW_EQUATION_SURFACE_VALIDATION_REPORT_SCHEMA,
    LAW_SURFACE_BINDING_VOCABULARY_SCHEMA, LawBindingV1, LawEquationSurfaceV1, LawEquationV1,
    LawForbiddenSupportGeneratorV1, LawSurfaceBindingPairV1, LawSurfaceBindingVocabularyV1,
    LawSurfaceValidationInputV1, LawSurfaceValidationReportV1, LawSurfaceValidationSummaryV1,
    LawWitnessVariableV1, static_law_surface_binding_vocabulary_v1, validate_law_surface_v1_report,
};
pub use normalizer::normalize_archmap_v2;
pub use policy_bundle::{
    ARCHSIG_POLICY_BUNDLE_V1_SCHEMA, ARCHSIG_POLICY_BUNDLE_VALIDATION_REPORT_SCHEMA,
    ArchSigPolicyBundleV1, ComponentFingerprintsV1, build_policy_bundle, component_fingerprints,
    resolve_and_verify_policy_bundle,
};
pub use repair_plan::{build_repair_plan_validation_report_v1, validate_repair_plan_v1_checks};
pub(crate) use schema::*;
pub use schema::{
    AAT_ATOM_VOCABULARY_V1_SCHEMA, ARCHMAP_V2_SCHEMA, ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION,
    ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE, ARCHSIG_ANALYSIS_CONCLUSION_CODES,
    ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA, ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION,
    ARCHSIG_BOUNDARY_STATEMENT_V1_SCHEMA, ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION,
    ARCHSIG_COMPARISON_CONCLUSION_CODES,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED, ARCHSIG_COMPARISON_REPORT_V1_SCHEMA,
    ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA,
    ARCHSIG_GATE_BLOCKED_BY_GATE_POLICY, ARCHSIG_GATE_NOT_EVALUABLE,
    ARCHSIG_GATE_PASS_WITHIN_GATE_POLICY, ARCHSIG_GATE_POLICY_V1_SCHEMA,
    ARCHSIG_GATE_REPORT_DECISIONS, ARCHSIG_GATE_REPORT_V1_SCHEMA,
    ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE, ARCHSIG_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE,
    ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS, ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
    ARCHSIG_NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE, ARCHSIG_REPAIR_PLAN_V1_SCHEMA,
    ARCHSIG_REPAIR_TARGETS_IDENTIFIED, ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
    ARCHSIG_SAGA_CONCLUSION_CODES, ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL,
    ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX,
    ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT, AatAtomVocabularyEntryV1, AatAtomVocabularyV1,
    AgAnalyticReadingV1, AgAssumptionLedgerEntryV1, AgStructuralVerdictV1, AgVerdictDataV1,
    ArchMapAtomV2, ArchMapContextV2, ArchMapCoverV2, ArchMapDocumentV2,
    ArchMapExtractionDoctrineRefV2, ArchMapSource, ArchMapSourceRef, ArchMapValidationReportV1,
    ArchMapValidationReportV2, ArchMapValidationSummaryV1, ArchMapValidationSummaryV2,
    ArchSigArtifactValidationResultV1, ArchSigAtomViewerAtomNodeV1, ArchSigAtomViewerDataV1,
    ArchSigAtomViewerEdgeV1, ArchSigAtomViewerLayoutSettingsV1, ArchSigAtomViewerMoleculeGroupV1,
    ArchSigAtomViewerOmittedDetailCountsV1, ArchSigAtomViewerSourceArtifactRefsV1,
    ArchSigAtomViewerTruncationPolicyV1, ArchSigAtomViewerVisualV1, ArchSigMeasurementPacketV1,
    ArchSigRunManifestRawArtifactPathsV1, ArchSigRunManifestV1,
    ArchSigRunManifestValidationReportPathsV1, ArchSigRunManifestValidationResultSummaryV1,
    ArchmapCandidatePacketSelfReviewV1, ArchmapCandidatePacketSurveyRowV1,
    ArchmapCandidatePacketV1, ArchmapCoverageLedgerRowV1, ArchmapCoverageLedgerV1,
    ArchmapExtractionAdjudicationV1, ArchmapExtractionConsistencyV1,
    ArchmapExtractionContextDiffV1, ArchmapExtractionMatchCountV1,
    ArchmapExtractionMatchedCandidateV1, ArchmapExtractionOnlyInCandidateV1,
    ArchmapScopeManifestExclusionV1, ArchmapScopeManifestRepositoryV1,
    ArchmapScopeManifestScopeSpecV1, ArchmapScopeManifestV1, ArchmapScopeManifestWorklistEntryV1,
    BoundaryStatementV1, ExpandedLawPolicyEntryV1, LAW_POLICY_V1_SCHEMA,
    LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION, LawEvaluatorManifestV1, LawEvaluatorRegistryV1,
    LawPolicyBasisLedgerEntryV1, LawPolicyBasisManifestV1, LawPolicyDocumentV1, LawPolicyEntryV1,
    LawPolicyPackEntryV1, LawPolicyPackManifestV1, LawPolicyValidationInputV1,
    LawPolicyValidationReportV1, LawPolicyValidationSummaryV1, MEASUREMENT_PROFILE_V1_SCHEMA,
    MeasurementProfileFiniteBoundsV1, MeasurementProfileV1, MeasurementProfileWitnessV1,
    NORMALIZED_ARCHMAP_V2_SCHEMA, NormalizedArchMapSummaryV2, NormalizedArchMapV2,
    NormalizedAtomV2, NormalizedContextV2, NormalizedCoverV2, RepairPlanComplexV1,
    RepairPlanDocumentV1, RepairPlanFaithfulnessV1, RepairPlanOverlapV1, RepairPlanPrimitiveV1,
    RepairPlanProjectionRowV1, RepairPlanResidualV1, RepairPlanSemanticProjectionV1,
    RepairPlanSupportV1, RepairPlanTripleOverlapV1, SCHEMA_VERSION_CATALOG_SCHEMA_VERSION,
    SchemaVersionCatalogV0,
};
pub use schema_catalog::static_schema_version_catalog;
