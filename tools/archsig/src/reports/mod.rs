use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use archsig::{ArchMapDocumentV0, LawPolicyDocumentV0, build_archsig_analysis_packet};

include!("codebase_inspection.rs");
include!("pr_review.rs");
include!("summary.rs");
include!("detail_index.rs");
