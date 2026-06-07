mod archmap;
mod archsig_analysis_packet;
mod law_policy;
mod normalizer;
mod schema;
mod schema_catalog;
mod validation;

pub use archmap::{
    ArchMapSourceInventoryInput, validate_archmap_report, validate_archmap_v1_report,
};
pub use archsig_analysis_packet::{
    build_archsig_analysis_packet, validate_archsig_analysis_packet_report,
};
pub use law_policy::{
    static_law_policy, validate_law_policy_report, validate_law_policy_v1_report,
};
pub use normalizer::normalize_archmap_v1;
pub(crate) use schema::*;
pub use schema::{
    ARCHMAP_SCHEMA_VERSION, ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION, ARCHMAP_V1_SCHEMA,
    ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION, ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
    ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION,
    ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION, ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
    ArchMapAtomObservationV0, ArchMapAtomV1, ArchMapDocumentV0, ArchMapDocumentV1,
    ArchMapMoleculeObservationV0, ArchMapMoleculeV1, ArchMapSourceInventoryV0, ArchMapSourceRef,
    ArchMapSourceV1, ArchMapValidationReportV0, ArchMapValidationReportV1,
    ArchMapValidationSummaryV1, ArchSigAnalysisPacketV0, ArchSigAnalysisPacketValidationReportV0,
    ArchSigArtifactValidationResultV0, ArchSigAtomViewerAtomNodeV0, ArchSigAtomViewerDataV0,
    ArchSigAtomViewerEdgeV0, ArchSigAtomViewerLayoutSettingsV0, ArchSigAtomViewerMoleculeGroupV0,
    ArchSigAtomViewerOmittedDetailCountsV0, ArchSigAtomViewerSourceArtifactRefsV0,
    ArchSigAtomViewerTruncationPolicyV0, ArchSigAtomViewerVisualV0,
    ArchSigRunManifestRawArtifactPathsV0, ArchSigRunManifestV0,
    ArchSigRunManifestValidationReportPathsV0, ArchSigRunManifestValidationResultSummaryV0,
    LAW_POLICY_SCHEMA_VERSION, LAW_POLICY_V1_SCHEMA, LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
    LawPolicyDocumentV0, LawPolicyDocumentV1, LawPolicyEntryV1, LawPolicyValidationInputV1,
    LawPolicyValidationReportV0, LawPolicyValidationReportV1, LawPolicyValidationSummaryV1,
    NORMALIZED_ARCHMAP_V1_SCHEMA, NormalizedArchMapSummaryV1, NormalizedArchMapV1,
    NormalizedAtomBindingV1, NormalizedAtomPredicateV1, NormalizedAtomV1, NormalizedMoleculeV1,
    SCHEMA_VERSION_CATALOG_SCHEMA_VERSION, SchemaVersionCatalogV0,
};
pub use schema_catalog::static_schema_version_catalog;
