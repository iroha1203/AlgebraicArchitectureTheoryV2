#![recursion_limit = "256"]

mod ag_measurement;
mod archmap;
mod compare;
mod gate;
mod law_policy;
mod normalizer;
mod schema;
mod schema_catalog;
mod typed_evaluator;
mod validation;

pub use ag_measurement::{
    build_foundation_measurement_packet_v1, build_insight_brief_v1, build_insight_report_v1,
    build_measurement_summary_v1, build_measurement_viewer_data_v1,
    selected_measurement_profile_v1, validate_measurement_packet_v1,
};
pub use archmap::{
    compare_archmap_v2_doctrine, static_aat_atom_vocabulary_v1, validate_archmap_v1_report,
    validate_archmap_v2_report,
};
pub use compare::build_comparison_artifacts_v1;
pub use gate::{build_gate_report_v1, validate_gate_policy_v1};
pub use law_policy::{
    REPLACEMENT_REGISTRY_REF, expand_law_policy_v1, static_law_evaluator_registry_v1,
    validate_law_policy_v1_report,
};
pub use normalizer::{normalize_archmap_v1, normalize_archmap_v2};
pub(crate) use schema::*;
pub use schema::{
    AAT_ATOM_VOCABULARY_V1_SCHEMA, ARCHITECTURE_DISTANCE_V1_SCHEMA, ARCHMAP_V1_SCHEMA,
    ARCHMAP_V2_SCHEMA, ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION, ARCHSIG_ANALYSIS_PACKET_V1_SCHEMA,
    ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA, ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION,
    ARCHSIG_BOUNDARY_STATEMENT_V1_SCHEMA,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED, ARCHSIG_COMPARISON_REPORT_V1_SCHEMA,
    ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA, ARCHSIG_GATE_POLICY_V1_SCHEMA,
    ARCHSIG_GATE_REPORT_V1_SCHEMA, ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
    ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION, AatAtomVocabularyEntryV1, AatAtomVocabularyV1,
    AgAnalyticReadingV1, AgAssumptionLedgerEntryV1, AgStructuralVerdictV1, AgVerdictDataV1,
    ArchMapAtomV1, ArchMapAtomV2, ArchMapContextV2, ArchMapCoverV2, ArchMapDocumentV1,
    ArchMapDocumentV2, ArchMapExtractionDoctrineRefV2, ArchMapMoleculeV1, ArchMapSource,
    ArchMapSourceRef, ArchMapValidationReportV1, ArchMapValidationReportV2,
    ArchMapValidationSummaryV1, ArchMapValidationSummaryV2, ArchSigArtifactValidationResultV0,
    ArchSigAtomViewerAtomNodeV0, ArchSigAtomViewerDataV0, ArchSigAtomViewerEdgeV0,
    ArchSigAtomViewerLayoutSettingsV0, ArchSigAtomViewerMoleculeGroupV0,
    ArchSigAtomViewerOmittedDetailCountsV0, ArchSigAtomViewerSourceArtifactRefsV0,
    ArchSigAtomViewerTruncationPolicyV0, ArchSigAtomViewerVisualV0, ArchSigMeasurementPacketV1,
    ArchSigRunManifestRawArtifactPathsV0, ArchSigRunManifestV0,
    ArchSigRunManifestValidationReportPathsV0, ArchSigRunManifestValidationResultSummaryV0,
    BoundaryStatementV1, ExpandedLawPolicyEntryV1, LAW_POLICY_V1_SCHEMA,
    LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION, LawEvaluatorManifestV1, LawEvaluatorRegistryV1,
    LawPolicyBasisManifestV1, LawPolicyDocumentV1, LawPolicyEntryV1, LawPolicyPackEntryV1,
    LawPolicyPackManifestV1, LawPolicyValidationInputV1, LawPolicyValidationReportV1,
    LawPolicyValidationSummaryV1, MEASUREMENT_PROFILE_V1_SCHEMA, MeasurementProfileV1,
    MeasurementProfileWitnessV1, NORMALIZED_ARCHMAP_V1_SCHEMA, NORMALIZED_ARCHMAP_V2_SCHEMA,
    NormalizedArchMapSummaryV1, NormalizedArchMapSummaryV2, NormalizedArchMapV1,
    NormalizedArchMapV2, NormalizedAtomBindingV1, NormalizedAtomPredicateV1, NormalizedAtomV1,
    NormalizedAtomV2, NormalizedContextV2, NormalizedCoverV2, NormalizedMoleculeV1,
    ReplacementEvaluatorManifestV1, ReplacementRegistryResolutionV1,
    SCHEMA_VERSION_CATALOG_SCHEMA_VERSION, SchemaVersionCatalogV0,
    TYPED_EVALUATOR_RESULTS_V1_SCHEMA, TypedEvaluatorResultV1, TypedEvaluatorResultsSummaryV1,
    TypedEvaluatorResultsV1,
};
pub use schema_catalog::static_schema_version_catalog;
pub use typed_evaluator::{
    build_architecture_distance_v1, build_typed_analysis_packet_v1,
    build_typed_analysis_summary_v1, build_typed_analysis_validation_v1,
    build_typed_atom_viewer_data_v1, build_typed_detail_index_v1,
    build_typed_llm_interpretation_packet_v1, enrich_architecture_distance_with_part4_bundle_v1,
    evaluate_typed_v1,
};
