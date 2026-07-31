#![recursion_limit = "256"]

mod authoring;
mod supply_bench;

pub use archsig::{
    ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA, ARCHMAP_COVERAGE_LEDGER_CLAIM_BOUNDARY,
    ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA, ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA,
    ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA, ARCHMAP_V2_SCHEMA,
};
pub use authoring::{
    AuthoringAuditInputV1, ExtractionDiffOptions, ScopeManifestOptions,
    archmap_authoring_audit_checks_v1, build_extraction_consistency_v1, build_scope_manifest_v1,
    parse_candidate_packet_value, validate_authoring_audit_input_v1, validate_candidate_packet_v1,
    validate_coverage_ledger_v1, validate_extraction_consistency_v1, validate_scope_manifest_v1,
};
pub use supply_bench::{
    ALIGNMENT_DECISION_NOT_ADOPTED, ALIGNMENT_DECISION_NOVEL_CORRECT,
    ALIGNMENT_DECISION_REFERENCE_MATCHED, ALIGNMENT_DECISION_UNRECOVERED,
    ARCHMAP_REFERENCE_ALIGNMENT_V1_SCHEMA, ARCHMAP_REFERENCE_SLICE_V1_SCHEMA,
    ARCHMAP_SUPPLY_BENCH_REPORT_V1_SCHEMA, ArchmapReferenceAlignmentRowV1,
    ArchmapReferenceAlignmentV1, ArchmapReferenceSliceAtomV1, ArchmapReferenceSliceV1,
    ArchmapSupplyBenchReportV1, SupplyBenchOptions, SupplyBenchPairInput,
    build_supply_bench_report_v1,
};
