use std::path::PathBuf;

use archsig::{SupplyBenchOptions, SupplyBenchPairInput, build_supply_bench_report_v1};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/supply_bench")
        .join(name)
}

fn pair(pair_id: &str, consistency: &str) -> SupplyBenchPairInput {
    SupplyBenchPairInput {
        pair_id: pair_id.to_string(),
        chunk_class: None,
        consistency: fixture(consistency),
        alignment: None,
    }
}

fn expect_error(options: &SupplyBenchOptions, fragments: &[&str]) -> String {
    let error = build_supply_bench_report_v1(options)
        .err()
        .unwrap_or_else(|| panic!("expected an error containing {fragments:?}"))
        .to_string();
    for fragment in fragments {
        assert!(
            error.contains(fragment),
            "error must contain {fragment:?}, got: {error}"
        );
    }
    error
}

#[test]
fn computes_key_convergence_from_merge_groups() {
    let report = build_supply_bench_report_v1(&SupplyBenchOptions {
        id: "supply-bench:test".to_string(),
        pairs: vec![pair("pair-01", "pair-01.json"), pair("pair-02", "pair-02.json")],
        reference: None,
        series_key: None,
    })
    .expect("happy-path bench report");

    assert_eq!(report.schema, "archmap-supply-bench-report/v1");
    assert_eq!(report.pairs.len(), 2);

    let pair1 = &report.pairs[0];
    assert_eq!(pair1.pair_id, "pair-01");
    assert_eq!(pair1.machine_match_rate, 0.4);
    assert_eq!(pair1.machine_match_rate_key1, Some(0.4));
    assert_eq!(pair1.key_convergence.status, "computed");
    assert_eq!(pair1.key_convergence.matched, Some(2));
    assert_eq!(pair1.key_convergence.merge_groups, Some(1));
    assert_eq!(pair1.key_convergence.adopted, Some(1));
    assert_eq!(pair1.key_convergence.rate, Some(2.0 / 3.0));

    let pair2 = &report.pairs[1];
    assert_eq!(pair2.key_convergence.merge_groups, Some(1));
    assert_eq!(pair2.key_convergence.rate, Some(0.75));

    let convergence = report
        .aggregate
        .get("keyConvergenceRate")
        .expect("aggregate key convergence");
    assert_eq!(convergence.pairs, 2);
    assert_eq!(convergence.min, 2.0 / 3.0);
    assert_eq!(convergence.max, 0.75);
    assert!((convergence.mean - (2.0 / 3.0 + 0.75) / 2.0).abs() < 1e-12);
}

#[test]
fn report_is_deterministic_across_argument_order() {
    let mut tuned = pair("pair-01", "pair-01.json");
    tuned.chunk_class = Some("tuned".to_string());
    let mut disjoint = pair("pair-02", "pair-02.json");
    disjoint.chunk_class = Some("prompt-literal-disjoint".to_string());

    let forward = build_supply_bench_report_v1(&SupplyBenchOptions {
        id: "supply-bench:test".to_string(),
        pairs: vec![tuned.clone(), disjoint.clone()],
        reference: None,
        series_key: Some(fixture("series-key.json")),
    })
    .expect("forward order");
    let reversed = build_supply_bench_report_v1(&SupplyBenchOptions {
        id: "supply-bench:test".to_string(),
        pairs: vec![disjoint, tuned],
        reference: None,
        series_key: Some(fixture("series-key.json")),
    })
    .expect("reversed order");

    let forward_bytes = serde_json::to_string_pretty(&forward).expect("serialize forward");
    let reversed_bytes = serde_json::to_string_pretty(&reversed).expect("serialize reversed");
    assert_eq!(
        forward_bytes, reversed_bytes,
        "supply-bench output must not depend on pair argument order"
    );
    assert!(forward.chunk_class_aggregate.contains_key("tuned"));
    assert!(
        forward
            .chunk_class_aggregate
            .contains_key("prompt-literal-disjoint")
    );
    assert!(forward.series_key.is_some());
}

#[test]
fn computes_reference_recall_and_over_generation_from_alignment() {
    let mut with_alignment = pair("pair-01", "pair-01.json");
    with_alignment.alignment = Some(fixture("alignment-pair-01.json"));
    let report = build_supply_bench_report_v1(&SupplyBenchOptions {
        id: "supply-bench:test".to_string(),
        pairs: vec![with_alignment],
        reference: Some(fixture("reference.json")),
        series_key: None,
    })
    .expect("reference-aligned bench report");

    assert_eq!(report.reference_ref.as_deref(), Some("reference:supply-bench-fixture"));
    assert_eq!(report.reference_version.as_deref(), Some("1"));
    let recall = report.pairs[0]
        .reference_recall
        .as_ref()
        .expect("reference recall");
    assert_eq!(recall.reference_atoms, 4);
    assert_eq!(recall.mechanically_recovered, 3);
    assert_eq!(recall.mechanical_lower_bound, 0.75);
    assert_eq!(recall.adjudicated_recovered, 3);
    assert_eq!(recall.adjudicated, 0.75);

    let over = report.pairs[0]
        .over_generation
        .as_ref()
        .expect("over generation");
    assert_eq!(over.candidate_atoms, 7);
    assert_eq!(over.not_adopted_atoms, 0);
    assert_eq!(over.novel_correct_atoms, 1);
    assert_eq!(over.rate, 0.0);

    assert!(report.aggregate.contains_key("referenceRecallMechanicalLowerBound"));
    assert!(report.aggregate.contains_key("referenceRecallAdjudicated"));
    assert!(report.aggregate.contains_key("overGenerationRate"));
}

// AC4 (a): a missing adjudication record is an explicit error, not a silent zero.
#[test]
fn missing_adjudication_record_is_an_explicit_error() {
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "neg-missing-adjudication.json")],
            reference: None,
            series_key: None,
        },
        &[
            "consistency:neg-missing-adjudication",
            "adjudication record is missing",
            "relation|svc-a.Alpha|relation|calls|svc-b",
        ],
    );
}

// AC4 (b): partial adjudication fails closed and names the uncovered atoms.
#[test]
fn partial_adjudication_is_an_explicit_error() {
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "neg-partial-adjudication.json")],
            reference: None,
            series_key: None,
        },
        &[
            "consistency:neg-partial-adjudication",
            "partial adjudication",
            "atom:b3",
        ],
    );
}

// AC4 (c): a legacy record without merge groups reports key convergence as
// not computable instead of guessing pair counts from row counts.
#[test]
fn legacy_adjudication_reports_key_convergence_not_computable() {
    let report = build_supply_bench_report_v1(&SupplyBenchOptions {
        id: "supply-bench:test".to_string(),
        pairs: vec![pair("pair-01", "legacy-adjudication.json")],
        reference: None,
        series_key: None,
    })
    .expect("legacy record is readable");
    let convergence = &report.pairs[0].key_convergence;
    assert_eq!(convergence.status, "not-computable");
    assert!(
        convergence
            .reason
            .as_deref()
            .unwrap_or_default()
            .contains("merge-group structure")
    );
    assert_eq!(convergence.rate, None);
    assert!(!report.aggregate.contains_key("keyConvergenceRate"));
}

// AC4 (d): a consistency artifact with missing required fields fails closed
// on the bench path with the file named.
#[test]
fn malformed_consistency_fails_closed() {
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "neg-missing-field.json")],
            reference: None,
            series_key: None,
        },
        &["neg-missing-field.json", "matched"],
    );
}

// AC4 (e): merge-group integrity violations fail closed.
#[test]
fn merge_group_integrity_violations_fail_closed() {
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "neg-mixed-group.json")],
            reference: None,
            series_key: None,
        },
        &["consistency:neg-mixed-group", "no mergeGroup", "mixed records"],
    );
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "neg-one-sided-group.json")],
            reference: None,
            series_key: None,
        },
        &[
            "consistency:neg-one-sided-group",
            "group-1",
            "does not join both passes",
        ],
    );
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "neg-canonical-mismatch.json")],
            reference: None,
            series_key: None,
        },
        &[
            "consistency:neg-canonical-mismatch",
            "disagree on canonicalAtomId",
        ],
    );
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "neg-adopted-with-group.json")],
            reference: None,
            series_key: None,
        },
        &[
            "consistency:neg-adopted-with-group",
            "restricted to merged rows",
        ],
    );
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "neg-duplicate-atom.json")],
            reference: None,
            series_key: None,
        },
        &[
            "consistency:neg-duplicate-atom",
            "atom:a3",
            "more than one adjudication row",
        ],
    );
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "neg-unknown-atom.json")],
            reference: None,
            series_key: None,
        },
        &[
            "consistency:neg-unknown-atom",
            "atom:zz",
            "not in the onlyIn lists",
        ],
    );
}

// AC4 (f): reference-alignment completeness and uniqueness violations fail closed.
#[test]
fn alignment_completeness_and_uniqueness_violations_fail_closed() {
    let aligned = |alignment: &str| {
        let mut input = pair("pair-01", "pair-01.json");
        input.alignment = Some(fixture(alignment));
        SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![input],
            reference: Some(fixture("reference.json")),
            series_key: None,
        }
    };
    expect_error(
        &aligned("neg-alignment-incomplete-reference.json"),
        &["incomplete over the reference slice", "ref:r4"],
    );
    expect_error(
        &aligned("neg-alignment-duplicate-candidate.json"),
        &["atom:a4", "more than one row"],
    );
    expect_error(
        &aligned("neg-alignment-unknown-candidate.json"),
        &["atom:zz", "not in pair"],
    );
    expect_error(
        &aligned("neg-alignment-missing-candidate.json"),
        &["incomplete over the supply", "atom:a4"],
    );
    expect_error(
        &aligned("neg-alignment-wrong-pair.json"),
        &["pair-99", "pair-01"],
    );
}

// Bench corpus fixture integrity: the prompt-literal-disjoint chunk must have
// zero intersection with prompt-pack code literals (service names, route
// words, and class names), re-checked mechanically on every CI run so a
// prompt-pack edit cannot silently invalidate the corpus classification.
#[test]
fn corpus_disjoint_chunk_stays_disjoint_from_prompt_pack_code_literals() {
    let corpus: serde_json::Value = serde_json::from_reader(
        std::fs::File::open(fixture("corpus_v1.json")).expect("corpus fixture"),
    )
    .expect("corpus fixture JSON");
    let prompt_pack = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("skills/archmap-creater/references/prompt-pack.md"),
    )
    .expect("prompt-pack reference");
    // Odd split segments capture inline backtick spans and fenced code block
    // bodies; prose stays at even indices and is not checked.
    let code: String = prompt_pack
        .split('`')
        .enumerate()
        .filter(|(index, _)| index % 2 == 1)
        .map(|(_, segment)| format!("{segment}\n"))
        .collect();

    let chunks = corpus["chunks"].as_array().expect("corpus chunks");
    let tuned: Vec<&str> = chunks
        .iter()
        .filter(|chunk| chunk["chunkClass"] == "tuned")
        .map(|chunk| chunk["chunkId"].as_str().unwrap())
        .collect();
    assert_eq!(tuned, vec!["chunk-04", "chunk-13"], "tuned chunk set is fixed");

    let disjoint: Vec<&serde_json::Value> = chunks
        .iter()
        .filter(|chunk| chunk["chunkClass"] == "prompt-literal-disjoint")
        .collect();
    assert!(!disjoint.is_empty(), "corpus needs a prompt-literal-disjoint chunk");
    for chunk in disjoint {
        for row in chunk["rows"].as_array().expect("chunk rows") {
            let path = row["path"].as_str().expect("row path");
            let service = path.split('/').next().expect("service dir");
            let route_word = service.trim_start_matches("ts-").replace('-', "");
            assert!(
                !code.contains(service),
                "prompt-pack code literal names service {service}"
            );
            assert!(
                !code.contains(&route_word),
                "prompt-pack code literal names route word {route_word} of {service}"
            );
            if let Some(class_name) = path.rsplit('/').next().and_then(|f| f.strip_suffix(".java"))
            {
                assert!(
                    !code.contains(class_name),
                    "prompt-pack code literal names class {class_name}"
                );
            }
        }
    }
}

// A supplied reference with a pair lacking an alignment must not silently
// skip adjudicated reference metrics.
#[test]
fn reference_without_alignment_fails_closed() {
    expect_error(
        &SupplyBenchOptions {
            id: "supply-bench:test".to_string(),
            pairs: vec![pair("pair-01", "pair-01.json")],
            reference: Some(fixture("reference.json")),
            series_key: None,
        },
        &["pair-01", "no --alignment"],
    );
}
