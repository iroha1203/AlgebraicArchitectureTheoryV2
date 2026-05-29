mod archmap;
mod archsig_analysis_packet;
mod law_policy;
mod schema;
mod schema_catalog;
mod validation;

pub use archmap::{ArchMapSourceInventoryInput, validate_archmap_report};
pub use archsig_analysis_packet::{
    build_archsig_analysis_packet, validate_archsig_analysis_packet_report,
};
pub use law_policy::{static_law_policy, validate_law_policy_report};
pub(crate) use schema::*;
pub use schema::{
    ARCHMAP_SCHEMA_VERSION, ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION,
    ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION, ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
    ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION, ArchMapDocumentV0,
    ArchMapSourceInventoryV0, ArchMapValidationReportV0, ArchSigAnalysisPacketV0,
    ArchSigAnalysisPacketValidationReportV0, LAW_POLICY_SCHEMA_VERSION,
    LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION, LawPolicyDocumentV0, LawPolicyValidationReportV0,
    SCHEMA_VERSION_CATALOG_SCHEMA_VERSION, SchemaVersionCatalogV0,
};
pub use schema_catalog::static_schema_version_catalog;
