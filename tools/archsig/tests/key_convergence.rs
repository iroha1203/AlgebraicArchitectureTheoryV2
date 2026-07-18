use std::path::PathBuf;

use archsig::{ExtractionDiffOptions, build_extraction_consistency_v1};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/key_convergence")
        .join(name)
}

/// Regression lock for the atom-match-key@2 convergence gain on the
/// train-ticket fullbuild corpus (Issue #3545, key-convergence PRD R6).
/// The corpus is the real 44-packet dual-pass extraction distilled to the
/// key-bearing atom fields; adjudication established that the two passes
/// observed the same content, so key match rates below measure representation
/// convergence only.
#[test]
fn fullbuild_corpus_locks_key_convergence_rates() {
    let report = build_extraction_consistency_v1(&ExtractionDiffOptions {
        pass_a: vec![fixture("pass_a_corpus.json")],
        pass_b: vec![fixture("pass_b_corpus.json")],
        id: "consistency:key-convergence-corpus".to_string(),
        scope_manifest_ref: Some("scope:train-ticket-fullbuild@1".to_string()),
    })
    .expect("extraction diff over the corpus fixtures");

    assert!(
        report.atom_match_key_spec.contains("atom-match-key@2"),
        "primary matching must run under atom-match-key@2, got {}",
        report.atom_match_key_spec
    );

    let legacy = report
        .atom_match_key1_comparison
        .as_ref()
        .expect("extraction diff reports the atom-match-key@1 comparison");
    assert!(
        legacy.atom_match_key_spec.contains("atom-match-key@1"),
        "comparison row must be labeled atom-match-key@1, got {}",
        legacy.atom_match_key_spec
    );

    // PRD acceptance floor: @1 baseline stays a record (~0.094 on this
    // corpus), @2 must reach at least 0.19 by mechanical normalization alone.
    assert!(
        legacy.match_rate > 0.05 && legacy.match_rate < 0.15,
        "atom-match-key@1 baseline drifted: {}",
        legacy.match_rate
    );
    assert!(
        report.match_rate >= 0.19,
        "atom-match-key@2 must reach matchRate >= 0.19 on the fullbuild corpus, got {}",
        report.match_rate
    );
    assert!(
        report.matched.count > legacy.matched_count,
        "@2 must match strictly more pairs than @1 ({} vs {})",
        report.matched.count,
        legacy.matched_count
    );
}
