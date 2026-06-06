use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use crate::reports::{array_field_with_limit, array_items, json_field, string_array};
use archsig::{
    ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION, ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
    ArchMapDocumentV0, ArchMapValidationReportV0, ArchSigAnalysisPacketValidationReportV0,
    ArchSigArtifactValidationResultV0, ArchSigAtomViewerAtomNodeV0, ArchSigAtomViewerDataV0,
    ArchSigAtomViewerEdgeV0, ArchSigAtomViewerLayoutSettingsV0, ArchSigAtomViewerMoleculeGroupV0,
    ArchSigAtomViewerOmittedDetailCountsV0, ArchSigAtomViewerSourceArtifactRefsV0,
    ArchSigAtomViewerTruncationPolicyV0, ArchSigAtomViewerVisualV0,
    ArchSigRunManifestRawArtifactPathsV0, ArchSigRunManifestV0,
    ArchSigRunManifestValidationReportPathsV0, ArchSigRunManifestValidationResultSummaryV0,
    LawPolicyValidationReportV0,
};

include!("io.rs");
include!("analyze.rs");
include!("atom_viewer.rs");
include!("detail_index.rs");
