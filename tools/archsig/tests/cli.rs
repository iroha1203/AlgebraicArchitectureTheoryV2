use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal")
}

fn expressiveness_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/expressiveness")
}

fn coupon_rounding_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/coupon_rounding")
}

fn acts_spectrum_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/acts_spectrum")
}

fn homotopy_report_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/homotopy_report")
}

fn complete_archmap_acceptance_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/complete_archmap_acceptance")
}

fn inspection_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/inspection")
}

fn pr_review_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/pr_review")
}

fn sharded_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/sharded")
}

#[test]
fn cli_help_exposes_only_llm_atom_archmap_surface() {
    let output = run_sig0_output(&["--help"]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);

    for command in [
        "archmap",
        "archmap-generate",
        "law-policy",
        "interpretation-profile",
        "archsig-analysis",
        "aat-analysis",
        "analysis-summary",
        "summary",
        "codebase-inspection",
        "pr-review",
        "analyze",
        "llm-native-workflow",
        "north-star-workflow",
        "schema-catalog",
    ] {
        assert!(
            stdout.contains(command),
            "ArchSig help must expose retained command {command}\n{stdout}"
        );
    }

    for removed in removed_commands() {
        assert!(
            !stdout.contains(removed),
            "ArchSig help still exposes removed command {removed}\n{stdout}"
        );
    }
}

#[test]
fn cli_summarizes_archsig_analysis_packet() {
    let out_dir = temp_dir("analysis-summary");
    let root = fixture_root();
    let summary = out_dir.join("archsig-analysis-summary.json");

    run_sig0(&[
        "analysis-summary",
        "--packet",
        root.join("archsig_analysis_packet.json")
            .to_str()
            .expect("packet path is utf-8"),
        "--out",
        summary.to_str().expect("summary path is utf-8"),
    ]);

    let json = read_json(&summary);
    assert_eq!(
        json["packet"]["schemaVersion"],
        "archsig-analysis-packet-v0"
    );
    assert_eq!(
        json["packet"]["analysisId"],
        "archsig-analysis:fixture-archmap-atom-observation:llm-native-aat-law-policy-fixture"
    );
    assert_eq!(json["validation"]["archmap"], Value::Null);
    assert!(
        json["axisSummary"]["nonzeroAxes"]
            .as_array()
            .is_some_and(|axes| !axes.is_empty())
    );
    assert!(
        json.get("workflowSignalSummary").is_none()
            && !has_nested_key(&json, "signalDensityScore")
            && !has_nested_key(&json, "highestSignalDensity")
            && !has_nested_key(&json, "affectedWorkflows"),
        "analysis-summary must not surface density-ranked workflow signals"
    );
    assert!(
        json["bridgeSummary"]["bridgePressure"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    );
    assert!(
        json["detailIndex"]["sections"]
            .as_array()
            .is_some_and(|sections| !sections.is_empty())
    );
    assert_eq!(
        json["verdict"]["flatness"], "nonflatUnderSelectedPolicy",
        "analysis-summary must put the measured flatness verdict near the top"
    );
    assert_eq!(
        json["verdict"]["qualityState"], "pressureAndArchitecturalHolesDetected",
        "analysis-summary must state the quality conclusion before caveats"
    );
    assert!(
        json["verdict"]["primaryConclusion"]
            .as_str()
            .is_some_and(|text| text.contains("selected law axes are nonzero")),
        "analysis-summary verdict must say what ArchMap + LawPolicy measured"
    );
    assert!(
        json["qualityMeasurement"]["nonzeroAxisCount"]
            .as_u64()
            .is_some_and(|count| count > 0),
        "qualityMeasurement must count nonzero axes"
    );
    assert!(
        json["qualityMeasurement"]["spectrumHotspotCount"]
            .as_u64()
            .is_some_and(|count| count > 0),
        "qualityMeasurement must count spectrum hotspots"
    );
    assert!(
        json["qualityMeasurement"]["architecturalHoleCount"]
            .as_u64()
            .is_some_and(|count| count > 0),
        "qualityMeasurement must count unfilled architectural holes"
    );
    assert!(
        json["qualityMeasurement"]["projectionFidelityLossCount"]
            .as_u64()
            .is_some_and(|count| count > 0)
            && json["qualityMeasurement"]["operationPreconditionBlockerCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && json["qualityMeasurement"]["pathMultiplicityLossCount"]
                .as_u64()
                .is_some_and(|count| count > 0),
        "qualityMeasurement must count added AAT observation axes"
    );
    assert_eq!(
        json["analysisUsefulness"]["mode"], "gapQualifiedActionableAnalysis",
        "analysis-summary must not collapse coverage-qualified analysis into no-value gap reporting"
    );
    assert!(
        json["analysisUsefulness"]["valueStatement"]
            .as_str()
            .is_some_and(|text| {
                text.contains("do not block structural pressure localization")
                    && text.contains("review prioritization")
            })
            && json["analysisUsefulness"]["usableNow"]
                .as_array()
                .is_some_and(|items| {
                    items
                        .iter()
                        .any(|item| item["kind"] == "selectedLawPressure")
                        && items.iter().any(|item| item["kind"] == "curvatureHotspots")
                        && items.iter().any(|item| item["kind"] == "repairReviewQueue")
                })
            && json["analysisUsefulness"]["blockedByGaps"]["claims"]
                .as_array()
                .is_some_and(|claims| !claims.is_empty())
            && json["analysisUsefulness"]["evidenceToUpgradeConfidence"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "analysisUsefulness must separate usable findings from claims blocked by gaps"
    );
    assert!(
        json["actionQueue"].as_array().is_some_and(|items| {
            !items.is_empty()
                && items.iter().any(|item| {
                    item["conclusion"]
                        .as_str()
                        .is_some_and(|text| text == "measuredPressureHotspot")
                })
                && items.iter().all(|item| {
                    item["detailRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
                        && item.get("witnessRefs").is_none()
                        && item.get("supportRefs").is_none()
                        && item.get("sourceRefs").is_none()
                })
        }),
        "analysis-summary must expose a compact conclusion-first action queue with detail refs"
    );
    assert!(
        json["actionQueue"].as_array().is_some_and(|items| {
            items.iter().any(|item| {
                item["conclusion"]
                    .as_str()
                    .is_some_and(|text| text == "measuredPressureHotspot")
            }) && items.iter().any(|item| {
                item["kind"]
                    .as_str()
                    .is_some_and(|text| text == "architecturalHole")
            }) && items.iter().any(|item| {
                item["kind"]
                    .as_str()
                    .is_some_and(|text| text == "nonzeroSignatureAxis")
            }) && items.iter().any(|item| {
                item["kind"]
                    .as_str()
                    .is_some_and(|text| text == "bridgePressure")
            }) && items.iter().any(|item| {
                item["kind"]
                    .as_str()
                    .is_some_and(|text| text == "projectionFidelityLoss")
            }) && items.iter().any(|item| {
                item["kind"]
                    .as_str()
                    .is_some_and(|text| text == "operationPreconditionReadiness")
            }) && items.iter().any(|item| {
                item["kind"]
                    .as_str()
                    .is_some_and(|text| text == "pathMultiplicityLoss")
            })
        }),
        "analysis-summary must put hotspots, holes, nonzero axes, bridge pressure, and added AAT axes in the action queue"
    );
    assert!(
        json["measurementBasis"]["basisStatement"]
            .as_str()
            .is_some_and(|text| text.contains("supplied ArchMap")),
        "analysis-summary must record the measurement basis without diluting the verdict"
    );
    assert!(
        json["measurementStatusSummary"]["measuredCount"]
            .as_u64()
            .is_some_and(|count| count > 0)
            && json["measurementStatusSummary"]["proxyCount"]
                .as_u64()
                .is_some()
            && json["measurementStatusSummary"]["schemaFoundationOnlyCount"] == 0
            && json["measurementStatusSummary"]["claimBoundary"]
                .as_str()
                .is_some_and(|text| text.contains("not measured claims")),
        "analysis-summary must distinguish measured, proxy, partial, and schema-only status compactly"
    );
    assert!(
        json["dominantFindings"]["spectrumHotspots"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "analysis-summary must expose compact ArchitectureSpectrumReport hotspots"
    );
    assert!(
        json["dominantFindings"]["recurrentObstructions"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "analysis-summary must expose compact recurrent obstruction entries"
    );
    assert!(
        json["dominantFindings"]["projectionFidelityLoss"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && json["dominantFindings"]["synthesisBlockage"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && json["aatObservationAxisSummary"]["packetRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "analysis-summary must expose compact added AAT observation axis readings"
    );
    assert!(
        json["trendDiagnosis"]["trendCounts"]["nonzeroAxisCount"]
            .as_u64()
            .is_some_and(|count| count > 0)
            && json["trendDiagnosis"]["pressureConcentration"]["nonzeroAxisRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && json["trendDiagnosis"]["packetRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "trendDiagnosis must expose compact repository-wide tendency refs"
    );
    let trend_insights = json["trendDiagnosis"]["trendInsights"]["items"]
        .as_array()
        .expect("trendInsights items must be an array");
    for kind in [
        "crossAxisCooccurrence",
        "operationFreedomLoss",
        "pathContinuationDefect",
        "boundaryResidualLocalization",
        "repairTransferRisk",
    ] {
        assert!(
            trend_insights.iter().any(|item| {
                item["kind"].as_str().is_some_and(|actual| actual == kind)
                    && item["whyNontrivial"]
                        .as_str()
                        .is_some_and(|text| !text.is_empty())
                    && item["packetRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
            }),
            "trendInsights must expose compact nontrivial {kind} measurement"
        );
    }
    assert!(
        trend_insights.iter().any(|item| {
            item["kind"].as_str() == Some("pathContinuationDefect")
                && item["measurement"]["positiveDefectCount"]
                    .as_u64()
                    .is_some_and(|count| count > 0)
        }) && trend_insights.iter().any(|item| {
            item["kind"].as_str() == Some("operationFreedomLoss")
                && item["measurement"]["blockedOperationCount"]
                    .as_u64()
                    .is_some_and(|count| count > 0)
        }) && trend_insights.iter().any(|item| {
            item["kind"].as_str() == Some("repairTransferRisk")
                && item["measurement"]["transferRiskCount"]
                    .as_u64()
                    .is_some_and(|count| count > 0)
        }),
        "trendInsights must be backed by concrete operation, path, and transfer measurements"
    );
    assert!(
        json["architectureInsightSummary"]["primaryPressureClusters"]
            .as_array()
            .is_some_and(|clusters| {
                !clusters.is_empty()
                    && clusters.iter().any(|cluster| {
                        cluster["signalCounts"]["nonzeroAxisCount"]
                            .as_u64()
                            .is_some_and(|count| count > 0)
                            && cluster["recommendedReview"]
                                .as_str()
                                .is_some_and(|text| !text.is_empty())
                            && cluster["detailRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                    })
            }),
        "architectureInsightSummary must group structural pressure across AAT-computed surfaces"
    );
    assert!(
        json["architectureInsightSummary"]["insightCards"]
            .as_array()
            .is_some_and(|cards| {
                !cards.is_empty()
                    && cards.iter().any(|card| {
                        card["claim"].as_str().is_some_and(|text| !text.is_empty())
                            && card["whyItMatters"]
                                .as_str()
                                .is_some_and(|text| !text.is_empty())
                            && card["aatEvidence"]["nonzeroAxisRefs"].as_array().is_some()
                            && card["aatEvidence"]["spectrumHotspotRefs"]
                                .as_array()
                                .is_some()
                            && card["aatEvidence"]["operationPreconditionRefs"]
                                .as_array()
                                .is_some()
                            && card["observedSignals"]
                                .as_array()
                                .is_some_and(|items| !items.is_empty())
                            && card["nextValidation"]
                                .as_array()
                                .is_some_and(|items| !items.is_empty())
                            && card["notBlockedByGaps"]
                                .as_str()
                                .is_some_and(|text| text.contains("usable review signals"))
                            && card.get("sourceRefs").is_none()
                            && card.get("supportRefs").is_none()
                            && card.get("witnessRefs").is_none()
                    })
            }),
        "architectureInsightSummary must expose evidence-backed insight cards, not only ranked refs"
    );
    assert!(
        json["architectureInsightSummary"]["coverageBlockers"]["items"]
            .as_array()
            .is_some_and(|items| {
                !items.is_empty()
                    && items.iter().any(|item| {
                        item["gapRef"]
                            .as_str()
                            .is_some_and(|gap| gap == "gap-runtime-user-db-trace")
                            && item["impactCount"].as_u64().is_some()
                            && item["detailRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                    })
            }),
        "architectureInsightSummary must expose compact coverage blockers with impact refs"
    );
    assert!(
        json["architectureInsightSummary"]["repairPlanning"]["candidateOperations"]
            .as_array()
            .is_some_and(|items| {
                !items.is_empty()
                    && items.iter().any(|item| {
                        item["preconditionCount"]
                            .as_u64()
                            .is_some_and(|count| count > 0)
                            && item["transferRiskCount"].as_u64().is_some()
                            && item["readiness"]
                                .as_str()
                                .is_some_and(|text| text.contains("review"))
                    })
            })
            && json["architectureInsightSummary"]["readNext"]
                .as_array()
                .is_some_and(|items| {
                    items.len() >= 3
                        && items[0]["focus"]
                            .as_str()
                            .is_some_and(|focus| focus != "coverage blockers")
                }),
        "architectureInsightSummary must lead with useful structural reading before coverage qualification"
    );
    assert!(
        json["reviewSupport"]["actionQueueCount"]
            .as_u64()
            .is_some_and(|count| count > 0)
            && json["reviewSupport"]["blockerSummary"]["architecturalHoleRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && json["reviewSupport"]["blockerSummary"]["operationPreconditionRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && json["reviewSupport"]["packetRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "reviewSupport must expose compact review queue and blocker refs"
    );
    assert!(
        json["detailIndex"]["sections"]
            .as_array()
            .is_some_and(|sections| {
                sections.iter().any(|section| {
                    section["name"]
                        .as_str()
                        .is_some_and(|name| name == "architectureSpectrumReport.topHotspots")
                        && section["packetRef"].as_str().is_some_and(|packet_ref| {
                            packet_ref == "packet:/architectureSpectrumReport/topHotspots"
                        })
                })
            }),
        "analysis-summary must index ArchitectureSpectrumReport detail"
    );
    assert!(
        json["measurementBasis"]["spectrumMeasuredBoundary"]
            .as_str()
            .is_some_and(|boundary| boundary.contains("ArchSig curvature support")),
        "analysis-summary must keep the ArchitectureSpectrumReport measured boundary"
    );
    assert!(
        json["measurementBasis"]["projectionFidelityBoundary"]
            .as_str()
            .is_some_and(|boundary| boundary.contains("projection loss"))
            && json["measurementBasis"]["synthesisBoundary"]
                .as_str()
                .is_some_and(|boundary| boundary.contains("synthesis solver")),
        "analysis-summary must keep added AAT observation axis measurement boundaries"
    );
    assert!(
        json["coverageGapSummary"]["gapRefs"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "analysis-summary must expose compact coverage gap refs"
    );
    assert!(
        json.get("architectureSpectrum").is_none()
            && json.get("architectureHomotopy").is_none()
            && json.get("spectralAnalysis").is_none()
            && json.get("transferBridges").is_none()
            && json.get("measurementExpansion").is_none(),
        "analysis-summary must not reprint raw packet detail surfaces"
    );
    assert!(
        json.get("nonConclusions").is_none(),
        "analysis-summary must not keep nonConclusions as a top-level main diagnosis"
    );
    assert!(
        json["metadata"]["nonConclusions"]
            .as_array()
            .is_some_and(|non_conclusions| !non_conclusions.is_empty())
            && json["metadata"]["spectrumNonConclusions"]
                .as_array()
                .is_some_and(|non_conclusions| !non_conclusions.is_empty())
            && json["metadata"]["homotopyNonConclusions"]
                .as_array()
                .is_some_and(|non_conclusions| !non_conclusions.is_empty()),
        "analysis-summary must preserve non-conclusions as metadata"
    );
    assert!(
        !has_nested_key(&json, "supportRefs")
            && !has_nested_key(&json, "sourceRefs")
            && !has_nested_key(&json, "witnessRefs")
            && !has_nested_key(&json, "topEigenmodes")
            && !has_nested_key(&json, "witnessClusters")
            && !has_nested_key(&json, "aggregateReadings"),
        "compact summary must omit raw evidence arrays and packet detail expansions"
    );
}

#[test]
fn cli_analysis_summary_stays_compact_for_sanitized_large_repo_class_packet() {
    let out_dir = temp_dir("analysis-summary-large-repo");
    let root = fixture_root();
    let manifest = read_json(&root.join("../large_repo_summary/manifest.json"));
    let packet_path = out_dir.join("sanitized-large-repo-packet.json");
    let summary_path = out_dir.join("sanitized-large-repo-summary.json");
    let mut packet = read_json(&root.join("archsig_analysis_packet.json"));

    expand_large_repo_summary_fixture(&mut packet, &manifest);
    fs::write(
        &packet_path,
        serde_json::to_vec_pretty(&packet).expect("large packet serializes"),
    )
    .expect("large packet fixture can be written");

    run_sig0(&[
        "analysis-summary",
        "--packet",
        packet_path.to_str().expect("packet path is utf-8"),
        "--out",
        summary_path.to_str().expect("summary path is utf-8"),
    ]);

    let summary_bytes = fs::metadata(&summary_path)
        .expect("summary metadata can be read")
        .len();
    let byte_budget = manifest["summaryByteBudget"]
        .as_u64()
        .expect("manifest records summary byte budget");
    assert!(
        summary_bytes <= byte_budget,
        "compact summary exceeded sanitized large-repo budget: {summary_bytes} > {byte_budget}"
    );

    let summary = read_json(&summary_path);
    assert!(
        summary["qualityMeasurement"]["spectrumHotspotCount"]
            .as_u64()
            .is_some_and(|count| count >= 64)
            && summary["qualityMeasurement"]["coverageGapCount"] == 1,
        "large summary must preserve conclusion counts without double-counting equivalent gap labels"
    );
    assert!(
        summary["actionQueue"].as_array().is_some_and(|items| {
            !items.is_empty()
                && items.len() <= 48
                && items.iter().all(|item| {
                    item["detailRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
                        && item.get("supportRefs").is_none()
                        && item.get("sourceRefs").is_none()
                        && item.get("witnessRefs").is_none()
                })
        }),
        "large summary must keep the full compact action queue"
    );
    assert!(
        !has_nested_key(&summary, "supportRefs")
            && !has_nested_key(&summary, "sourceRefs")
            && !has_nested_key(&summary, "witnessRefs")
            && !has_nested_key(&summary, "topEigenmodes")
            && !has_nested_key(&summary, "witnessClusters")
            && !has_nested_key(&summary, "aggregateReadings"),
        "large summary must omit raw detail copies"
    );
}

#[test]
fn cli_analysis_summary_rejects_removed_limit_option() {
    let root = fixture_root();
    let output = run_sig0_output(&[
        "analysis-summary",
        "--packet",
        root.join("archsig_analysis_packet.json")
            .to_str()
            .expect("packet path is utf-8"),
        "--limit",
        "2",
    ]);

    assert!(
        !output.status.success(),
        "analysis-summary must remove --limit"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unexpected argument '--limit'"),
        "analysis-summary --limit should be rejected\n{stderr}"
    );
}

#[test]
fn cli_codebase_inspection_reads_snapshot_index_surface() {
    let out_dir = temp_dir("codebase-inspection");
    let inspection = inspection_root();
    let coupon = coupon_rounding_root();
    let minimal = fixture_root();
    let review = pr_review_root();
    let report = out_dir.join("archsig-codebase-inspection.json");

    run_sig0(&[
        "codebase-inspection",
        "--snapshot",
        inspection
            .join("archmap_snapshot.json")
            .to_str()
            .expect("snapshot path is utf-8"),
        "--index",
        inspection
            .join("archmap_index.json")
            .to_str()
            .expect("index path is utf-8"),
        "--packet",
        coupon
            .join("archsig_analysis_packet.json")
            .to_str()
            .expect("packet path is utf-8"),
        "--law-policy",
        minimal
            .join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--recent-delta",
        review
            .join("archmap_delta.json")
            .to_str()
            .expect("recent delta path is utf-8"),
        "--limit",
        "3",
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(
        json["schemaVersion"],
        "archsig-codebase-inspection-report-v0"
    );
    assert_eq!(
        json["diagnosisKind"],
        "current-state architectural diagnosis"
    );
    assert_eq!(
        json["canonicalInputs"]["archMapSnapshot"]["schemaVersion"],
        "archmap-snapshot-v0"
    );
    assert_eq!(
        json["canonicalInputs"]["archMapIndex"]["schemaVersion"],
        "archmap-index-v0"
    );
    assert_eq!(json["inspectionFlow"]["recentDeltaCount"], 1);
    assert!(
        json["currentStateDiagnosis"]["topBoundaryHolonomy"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    );
    assert!(
        json["currentStateDiagnosis"]["topOrderSensitiveSquares"]
            .as_array()
            .is_some_and(|items| {
                items
                    .iter()
                    .any(|item| item["defectValue"].as_i64().is_some_and(|value| value > 0))
            })
    );
    assert!(
        json["coverageExactnessBoundary"]["coverageGaps"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    );
    assert!(
        json["currentStateDiagnosis"]["architectureSpectrum"]["hotspots"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "codebase-inspection must expose ArchitectureSpectrumReport hotspots"
    );
    assert!(
        json["currentStateDiagnosis"]["architectureSpectrum"]["recurrentObstructions"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "codebase-inspection must expose recurrent obstruction entries"
    );
    assert!(
        json["currentStateDiagnosis"]["architectureSpectrum"]["measuredBoundary"]
            .as_str()
            .is_some_and(|boundary| boundary.contains("selected LawPolicy")),
        "codebase-inspection must keep the spectrum measured boundary"
    );
    assert!(
        json["currentStateDiagnosis"]["architectureSpectrum"]["recommendedReviewFocus"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "codebase-inspection must expose next review focus"
    );
    assert!(
        json["surfaceBoundary"]["prReviewMode"]
            .as_str()
            .is_some_and(|boundary| boundary.contains("change-local"))
    );
    assert!(json["nonConclusions"].as_array().is_some_and(|items| {
        items
            .iter()
            .any(|item| item.as_str().is_some_and(|text| text.contains("FieldSig")))
    }));
}

#[test]
fn cli_rejects_summary_for_non_analysis_packet() {
    let root = fixture_root();
    let output = run_sig0_output(&[
        "analysis-summary",
        "--packet",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
    ]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--packet must have schemaVersion archsig-analysis-packet-v0"),
        "{stderr}"
    );
}

#[test]
fn cli_accepts_analysis_command_aliases() {
    let out_dir = temp_dir("analysis-aliases");
    let root = fixture_root();
    let profile_validation = out_dir.join("interpretation-profile-validation.json");
    run_sig0(&[
        "interpretation-profile",
        "--input",
        root.join("law_policy.json")
            .to_str()
            .expect("profile path is utf-8"),
        "--out",
        profile_validation
            .to_str()
            .expect("profile validation path is utf-8"),
    ]);

    let packet = out_dir.join("aat-analysis-packet.json");
    run_sig0(&[
        "aat-analysis",
        "--archmap",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("profile path is utf-8"),
        "--out",
        packet.to_str().expect("packet path is utf-8"),
    ]);
    assert_north_star_packet_surfaces(&read_json(&packet));

    let workflow_dir = out_dir.join("legacy-workflow");
    run_sig0(&[
        "north-star-workflow",
        "--archmap",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("profile path is utf-8"),
        "--out-dir",
        workflow_dir.to_str().expect("workflow dir is utf-8"),
    ]);
    assert!(workflow_dir.join("archsig-analysis-packet.json").is_file());

    let llm_native_dir = out_dir.join("llm-native-alias");
    run_sig0(&[
        "llm-native-workflow",
        "--archmap",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("profile path is utf-8"),
        "--out-dir",
        llm_native_dir.to_str().expect("workflow dir is utf-8"),
    ]);
    assert!(
        llm_native_dir
            .join("archsig-analysis-packet.json")
            .is_file()
    );
}

#[test]
fn cli_rejects_implicit_scan_default() {
    let output = run_sig0_output(&[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("ArchMap/LawPolicy/analysis-packet primary")
            && stderr.contains("archsig analyze"),
        "implicit scan should be rejected with the analyze boundary\n{stderr}"
    );
}

#[test]
fn removed_legacy_commands_are_not_accepted() {
    for command in removed_commands() {
        let output = run_sig0_output(&[command, "--help"]);
        assert!(
            !output.status.success(),
            "removed command {command} should not be accepted"
        );
    }
}

#[test]
fn cli_runs_primary_archmap_lawpolicy_archsig_analyze_workflow() {
    let out_dir = temp_dir("analyze-workflow");
    let root = fixture_root();
    let archmap = root.join("archmap.json");
    let law_policy = root.join("law_policy.json");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        law_policy.to_str().expect("law policy path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("output directory path is utf-8"),
    ]);

    let expected = [
        "archmap-validation.json",
        "law-policy-validation.json",
        "archsig-analysis-packet.json",
        "archsig-analysis-detail-index.json",
        "archsig-analysis-validation.json",
        "llm-interpretation-packet.json",
    ];
    for file in expected {
        assert!(
            out_dir.join(file).is_file(),
            "analyze workflow must write {file}"
        );
    }
    for removed_file in [
        "air.json",
        "air-validation.json",
        "theorem-precondition-check.json",
        "feature-report.json",
        "aat-observable-bundle.json",
        "aat-observable-bundle-validation.json",
    ] {
        assert!(
            !out_dir.join(removed_file).exists(),
            "analyze workflow must not emit legacy artifact {removed_file}"
        );
    }

    let archmap_validation = read_json(&out_dir.join("archmap-validation.json"));
    assert_eq!(
        archmap_validation["schemaVersion"],
        "archmap-validation-report-v0"
    );
    let law_policy_validation = read_json(&out_dir.join("law-policy-validation.json"));
    assert_eq!(
        law_policy_validation["schemaVersion"],
        "law-policy-validation-report-v0"
    );
    let analysis_packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    assert_eq!(
        analysis_packet["schemaVersion"],
        "archsig-analysis-packet-v0"
    );
    let detail_index = read_json(&out_dir.join("archsig-analysis-detail-index.json"));
    assert_eq!(
        detail_index["schemaVersion"],
        "archsig-analysis-detail-index-v0"
    );
    assert_eq!(
        analysis_packet["detailIndexRef"]["artifactKind"],
        "archsig-analysis-detail-index"
    );
    assert!(
        analysis_packet["obstructionCircuits"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "analysis packet must construct obstruction circuits"
    );
    assert!(
        analysis_packet["signatureAxes"]
            .as_array()
            .expect("signature axes are array")
            .iter()
            .any(
                |axis| axis["signatureAxisId"] == "sig-axis:semantic-inconsistency"
                    && axis["value"] == 1
            ),
        "analysis packet must value required signature axes"
    );
    assert_north_star_packet_surfaces(&analysis_packet);
    let analysis_validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert_eq!(
        analysis_validation["summary"]["result"].as_str(),
        Some("pass")
    );
    assert_eq!(analysis_validation["summary"]["aatConceptSurfaceCount"], 12);
    assert_eq!(
        analysis_validation["summary"]["designPrincipleReadingCount"],
        9
    );
    assert!(
        analysis_validation["summary"]["boundedJudgementCount"]
            .as_u64()
            .is_some_and(|count| count >= 10),
        "validation summary must count bounded judgements"
    );
    let llm_packet = read_json(&out_dir.join("llm-interpretation-packet.json"));
    assert_eq!(llm_packet, analysis_packet["llmInterpretationPacket"]);
    assert!(
        llm_packet.get("obstructionCircuits").is_none(),
        "LLM interpretation artifact must not duplicate the full analysis packet"
    );
    assert!(
        analysis_validation.get("packet").is_none(),
        "analysis validation must not embed the full analysis packet"
    );
}

#[test]
fn cli_analyze_reports_failed_validation_checks_to_stderr() {
    let out_dir = temp_dir("analyze-workflow-validation-failure");
    let root = fixture_root();
    let archmap = root.join("archmap_invalid_gap_measured_zero.json");
    let law_policy = root.join("law_policy.json");

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        law_policy.to_str().expect("law policy path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("output directory path is utf-8"),
    ]);

    assert!(
        !output.status.success(),
        "invalid analyze input must return a validation failure"
    );
    assert!(
        out_dir.join("archsig-analysis-packet.json").is_file(),
        "analyze should still write inspection artifacts before returning validation failure"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("archsig analyze produced artifacts")
            && stderr.contains("archmap-validation.json: fail")
            && stderr.contains("archmap-observation-gaps-not-measured-zero"),
        "analyze failure should identify the failed validation report and check\n{stderr}"
    );
}

#[test]
fn sharded_archmap_design_fixture_uses_horizontal_slices() {
    let root = sharded_root();
    let manifest = read_json(&root.join("manifest.json"));
    assert_eq!(manifest["schemaVersion"], "archmap-shard-manifest-v0");
    assert_eq!(
        manifest["shardingMode"],
        "horizontal-bounded-observation-slices"
    );

    let slices = manifest["slices"]
        .as_array()
        .expect("manifest slices are an array");
    assert!(
        slices.len() >= 2,
        "horizontal fixture should include multiple bounded slices"
    );
    for slice in slices {
        assert_eq!(slice["sliceKind"], "boundedObservationSlice");
        let path = slice["path"].as_str().expect("slice path is present");
        let slice_json = read_json(&root.join(path));
        assert_eq!(slice_json["schemaVersion"], "archmap-observation-slice-v0");
        assert_eq!(slice_json["sliceId"], slice["sliceId"]);
        assert_eq!(slice_json["surface"], slice["surface"]);
        assert!(
            slice_json.get("sourceUniverseFragment").is_some(),
            "slice {path} must carry its local source universe fragment"
        );
        assert!(
            slice_json.get("atomObservations").is_some(),
            "slice {path} must retain ArchMap observation arrays"
        );
    }

    assert_eq!(
        manifest["exportPolicy"]["targetSchemaVersion"],
        "archmap-observation-map-v0"
    );
}

#[test]
fn cli_archsig_analysis_step_outputs_packet_and_validation() {
    let out_dir = temp_dir("archsig-analysis-step");
    let root = fixture_root();
    let packet = out_dir.join("packet.json");
    let validation = out_dir.join("validation.json");
    let llm_packet = out_dir.join("llm-packet.json");
    run_sig0(&[
        "archsig-analysis",
        "--archmap",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--out",
        packet.to_str().expect("packet path is utf-8"),
        "--validation-out",
        validation.to_str().expect("validation path is utf-8"),
        "--llm-interpretation-out",
        llm_packet.to_str().expect("llm packet path is utf-8"),
    ]);
    let packet_json = read_json(&packet);
    let validation_json = read_json(&validation);
    assert_eq!(packet_json["schemaVersion"], "archsig-analysis-packet-v0");
    assert_north_star_packet_surfaces(&packet_json);
    assert_eq!(
        validation_json["schemaVersion"],
        "archsig-analysis-packet-validation-report-v0"
    );
    assert_eq!(
        read_json(&llm_packet),
        packet_json["llmInterpretationPacket"]
    );
    assert!(
        validation_json.get("packet").is_none(),
        "analysis validation must not embed the full analysis packet"
    );
}

#[test]
fn coupon_tax_rounding_fixture_locks_semantic_monodromy() {
    let out_dir = temp_dir("coupon-tax-rounding");
    let root = coupon_rounding_root();
    let minimal = fixture_root();
    let packet = out_dir.join("coupon-packet.json");

    run_sig0(&[
        "archsig-analysis",
        "--archmap",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--law-policy",
        minimal
            .join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--out",
        packet.to_str().expect("packet path is utf-8"),
    ]);

    let generated = read_json(&packet);
    let golden = read_json(&root.join("archsig_analysis_packet.json"));
    assert_eq!(generated["analysisId"], golden["analysisId"]);
    assert_eq!(
        generated["axisWiseMonodromyDefects"],
        golden["axisWiseMonodromyDefects"]
    );
    assert!(
        golden["axisWiseMonodromyDefects"]
            .as_array()
            .is_some_and(|defects| defects.iter().any(|defect| {
                defect["axisFamily"] == "semantic"
                    && defect["measurementStatus"] == "measured"
                    && defect["distanceValue"]
                        .as_i64()
                        .is_some_and(|value| value > 0)
                    && defect["distanceKind"]
                        .as_str()
                        .is_some_and(|kind| kind.contains("semantic-sequence-mismatch"))
                    && defect["observationRefs"].as_array().is_some_and(|refs| {
                        refs.iter().any(|value| {
                            value.as_str() == Some("semantic:coupon-tax-rounding-paths")
                        }) && refs.iter().all(|value| {
                            value
                                .as_str()
                                .is_none_or(|text| !text.contains("derived-semantic-order"))
                        })
                    })
                    && defect["witnessRefs"].as_array().is_some_and(|refs| {
                        refs.iter().any(|value| {
                            value.as_str().is_some_and(|text| {
                                text.contains("semantic-path-p-operation-discount")
                            })
                        }) && refs.iter().any(|value| {
                            value
                                .as_str()
                                .is_some_and(|text| text.contains("semantic-path-q-operation-tax"))
                        })
                    })
            }))
    );
    assert!(
        golden["nonzeroMonodromyWitnesses"]
            .as_array()
            .is_some_and(|witnesses| witnesses.iter().any(|witness| {
                witness["axisFamily"] == "semantic"
                    && witness["defectValue"]
                        .as_i64()
                        .is_some_and(|value| value > 0)
            }))
    );
    assert!(
        golden["axisWiseMonodromyDefects"]
            .as_array()
            .is_some_and(|defects| defects.iter().any(|defect| {
                defect["axisFamily"] == "effect"
                    && defect["distanceKind"]
                        .as_str()
                        .is_some_and(|kind| kind.contains("effect-replay-order-mismatch"))
                    && defect["distanceValue"]
                        .as_i64()
                        .is_some_and(|value| value > 0)
                    && defect["witnessRefs"].as_array().is_some_and(|refs| {
                        refs.iter().any(|value| {
                            value.as_str().is_some_and(|text| {
                                text.contains("effect-path-p-operation-discount")
                            })
                        }) && refs.iter().any(|value| {
                            value
                                .as_str()
                                .is_some_and(|text| text.contains("effect-path-q-operation-tax"))
                        })
                    })
            })),
        "coupon fixture must lock effect replay mismatch through comparable continuation values"
    );
    assert!(
        generated["effectRelationAlgebraReadings"]
            .as_array()
            .is_some_and(|readings| readings.iter().any(|reading| {
                reading["relationEvaluations"]
                    .as_array()
                    .is_some_and(|evaluations| {
                        evaluations.iter().any(|evaluation| {
                            evaluation["lawAxis"] == "replaySafety"
                                && evaluation["status"] == "blocked"
                                && evaluation["blockedReasonRefs"]
                                    .as_array()
                                    .is_some_and(|refs| !refs.is_empty())
                        })
                    })
            })),
        "effect replay mismatch fixture must expose replay safety as a law evaluation axis"
    );
    assert!(
        golden["featureBoundaryResidualReadings"]
            .as_array()
            .is_some_and(|readings| !readings.is_empty())
    );
    assert!(golden.to_string().contains("PaymentAmount"));
    assert!(golden.to_string().contains("ReceiptAmount"));
}

#[test]
fn state_effect_law_evaluators_keep_missing_runtime_blocked() {
    let root = fixture_root();
    let packet = read_json(&root.join("archsig_analysis_packet.json"));
    let state_reading = packet["stateTransitionAlgebraReadings"]
        .as_array()
        .expect("state transition readings are array")
        .first()
        .expect("minimal fixture has state transition reading");
    assert_eq!(state_reading["lawEvaluatorStatus"], "blocked");
    assert!(
        state_reading["transitionRelationInputs"]
            .as_array()
            .is_some_and(|inputs| inputs.iter().any(|input| {
                input["eventRefs"].as_array().is_some_and(|refs| {
                    refs.iter()
                        .any(|value| value.as_str() == Some("gap-runtime-user-db-trace"))
                })
            })),
        "missing runtime trace must remain a transition input blocker"
    );
    assert!(
        state_reading["lawEvaluations"]
            .as_array()
            .is_some_and(|evaluations| evaluations.iter().any(|evaluation| {
                evaluation["lawAxis"] == "replaySafety"
                    && evaluation["status"] == "blocked"
                    && evaluation["blockedReasonRefs"]
                        .as_array()
                        .is_some_and(|refs| {
                            refs.iter()
                                .any(|value| value.as_str() == Some("gap-runtime-user-db-trace"))
                        })
            })),
        "missing runtime trace must block replay safety rather than become measured zero"
    );
}

#[test]
fn supplied_operation_square_missing_endpoint_is_blocked_not_synthesized() {
    let out_dir = temp_dir("operation-square-missing-endpoint");
    let root = fixture_root();
    let mut archmap = read_json(&root.join("archmap.json"));
    archmap["operationSquareEvidence"][0]["endpointObjectRefs"] = Value::Array(Vec::new());
    archmap["operationSquareEvidence"][0]["sharedEndpointRefs"] = Value::Array(Vec::new());
    let archmap_path = out_dir.join("archmap-missing-endpoint.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap json serializes"),
    )
    .expect("temporary archmap fixture can be written");
    let packet = out_dir.join("packet.json");

    run_sig0(&[
        "archsig-analysis",
        "--archmap",
        archmap_path.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--out",
        packet.to_str().expect("packet path is utf-8"),
    ]);

    let json = read_json(&packet);
    let candidates = json["operationSquareCandidates"]
        .as_array()
        .expect("operation square candidates are array");
    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0]["candidateSource"], "blocked");
    assert!(
        candidates[0]["missingRefs"]
            .as_array()
            .is_some_and(|refs| refs.iter().any(|value| {
                value
                    .as_str()
                    .is_some_and(|text| text.contains("endpointObjectRefs"))
            })),
        "missing endpoint evidence must be preserved on the blocked candidate"
    );
    assert!(
        json["pathContinuationTraces"]
            .as_array()
            .is_some_and(|items| items.is_empty()),
        "blocked operation square must not produce measured continuation traces"
    );
    assert!(
        !json.to_string().contains(":continuation"),
        "ArchSig must not synthesize a fake :continuation operation"
    );
}

#[test]
fn acts_spectrum_fixture_manifest_locks_golden_validation() {
    let fixtures_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let manifest = read_json(&acts_spectrum_root().join("manifest.json"));
    let cases = manifest["cases"]
        .as_array()
        .expect("ACTS fixture manifest has cases");

    assert!(
        manifest["nonConclusions"].as_array().is_some_and(|items| {
            items.iter().any(|item| {
                item.as_str()
                    .is_some_and(|text| text.contains("not architecture lawfulness proof"))
            })
        }),
        "ACTS fixture manifest must preserve fixture non-conclusions"
    );

    for case in cases {
        let case_id = case["caseId"].as_str().expect("case id is present");
        let packet = read_json(
            &fixtures_root.join(case["packetPath"].as_str().expect("packet path is present")),
        );
        let validation = read_json(
            &fixtures_root.join(
                case["validationPath"]
                    .as_str()
                    .expect("validation path is present"),
            ),
        );

        assert_eq!(
            validation["summary"]["result"], "pass",
            "{case_id} validation output must pass"
        );
        assert!(
            validation["checks"]
                .as_array()
                .expect("validation checks are array")
                .iter()
                .any(|check| {
                    check["id"] == "archsig-analysis-packet-architecture-spectrum-report-surface"
                        && check["result"] == "pass"
                }),
            "{case_id} must lock ArchitectureSpectrumReport validation"
        );

        let report = &packet["architectureSpectrumReport"];
        assert!(
            report["nonConclusions"].as_array().is_some_and(|items| {
                items.iter().any(|item| {
                    item.as_str()
                        .is_some_and(|text| text.contains("single architecture quality score"))
                })
            }),
            "{case_id} must preserve report-level non-conclusions"
        );

        match case_id {
            "zero-curvature-support" => {
                let axis_ref = case["axisRef"].as_str().expect("axis ref is present");
                let expected = case["expectedCurvatureValue"]
                    .as_i64()
                    .expect("expected curvature value is present");
                let supports = packet["curvatureSupportReadings"][0]["witnessSupports"]
                    .as_array()
                    .expect("witness supports are array");
                assert!(
                    supports.iter().any(|support| {
                        support["selectedAxisRef"] == axis_ref
                            && support["curvatureValue"] == expected
                            && support["missingEvidence"]
                                .as_array()
                                .is_some_and(|items| !items.is_empty())
                    }),
                    "zero curvature support must remain distinct from missing evidence"
                );
            }
            "nonzero-semantic-curvature" => {
                let axis_ref = case["axisRef"].as_str().expect("axis ref is present");
                let minimum = case["minimumCurvatureValue"]
                    .as_i64()
                    .expect("minimum curvature value is present");
                assert!(
                    report["topHotspots"]
                        .as_array()
                        .expect("top hotspots are array")
                        .iter()
                        .any(|hotspot| {
                            hotspot["axisRef"] == axis_ref
                                && hotspot["curvatureValue"]
                                    .as_i64()
                                    .is_some_and(|value| value >= minimum)
                                && hotspot["witnessRefs"]
                                    .as_array()
                                    .is_some_and(|refs| !refs.is_empty())
                        }),
                    "nonzero semantic curvature must be visible as hotspot"
                );
            }
            "transfer-cycle" => {
                assert!(
                    packet["curvatureTransferReadings"][0]["transferEdges"]
                        .as_array()
                        .expect("transfer edges are array")
                        .iter()
                        .any(|edge| {
                            edge["sourceSupportRef"] == edge["targetSupportRef"]
                                && edge["weight"].as_i64().is_some_and(|value| value > 0)
                        }),
                    "transfer fixture must contain a positive closed transfer edge"
                );
                assert!(
                    report["recurrentObstructions"]
                        .as_array()
                        .expect("recurrent obstructions are array")
                        .iter()
                        .any(|mode| {
                            mode["transferEdgeRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                                && mode["spectralRadiusReading"].as_str().is_some_and(|text| {
                                    text.contains("rho(T^kappa) finite-matrix estimate")
                                })
                        }),
                    "transfer cycle must surface as recurrent obstruction support"
                );
            }
            "coverage-gap-boundary" => {
                let required_text = case["requiredText"]
                    .as_str()
                    .expect("required text is present");
                assert!(
                    report["coverageGaps"]
                        .as_array()
                        .expect("coverage gaps are array")
                        .iter()
                        .any(|gap| gap
                            .as_str()
                            .is_some_and(|text| text.contains(required_text))),
                    "coverage gap must remain explicit in ArchitectureSpectrumReport"
                );
            }
            "coupon-tax-rounding-acts" => {
                let required_text = case["requiredText"]
                    .as_str()
                    .expect("required text is present");
                assert!(
                    packet.to_string().contains(required_text),
                    "coupon/tax/rounding fixture must keep payment trace gap"
                );
                assert!(
                    report["topHotspots"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                        && report["recurrentObstructions"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty()),
                    "coupon/tax/rounding fixture must expose ACTS report surfaces"
                );
            }
            other => panic!("unhandled ACTS fixture case {other}"),
        }
    }
}

#[test]
fn homotopy_report_fixture_manifest_locks_golden_validation() {
    let root = homotopy_report_root();
    let manifest = read_json(&root.join("manifest.json"));
    let packet = read_json(&root.join("archsig_analysis_packet.json"));
    let validation = read_json(&root.join("validation.json"));
    assert_eq!(
        manifest["schemaVersion"],
        "archsig-homotopy-report-fixture-manifest-v0"
    );
    assert_eq!(validation["summary"]["result"], "pass");
    assert!(
        validation["checks"]
            .as_array()
            .expect("validation checks are array")
            .iter()
            .any(|check| {
                check["id"] == "archsig-analysis-packet-architecture-homotopy-report-surface"
                    && check["result"] == "pass"
            }),
        "HomotopyReport fixture must lock ArchitectureHomotopyReport validation"
    );

    let report = &packet["architectureHomotopyReport"];
    assert!(
        report["nonConclusions"].as_array().is_some_and(|items| {
            items.iter().any(|item| {
                item.as_str()
                    .is_some_and(|text| text.contains("single architecture quality score"))
            })
        }),
        "HomotopyReport fixture must preserve report-level non-conclusions"
    );

    for case in manifest["cases"]
        .as_array()
        .expect("manifest cases are array")
    {
        let case_id = case["caseId"].as_str().expect("case id is present");
        let path_rule_ref = case["pathRuleRef"]
            .as_str()
            .expect("path rule ref is present");
        let loop_ref = loop_ref_for_path_rule(&packet, path_rule_ref);
        let stokes = packet["stokesStyleReadings"]
            .as_array()
            .expect("stokes readings are array")
            .iter()
            .find(|reading| reading["loopRef"] == loop_ref)
            .unwrap_or_else(|| panic!("missing Stokes reading for {case_id}"));
        let holonomy = packet["homotopyHolonomyReadings"]
            .as_array()
            .expect("holonomy readings are array")
            .iter()
            .find(|reading| reading["loopRef"] == loop_ref)
            .unwrap_or_else(|| panic!("missing holonomy reading for {case_id}"));
        assert!(
            holonomy["distanceInputRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
                && holonomy["sourceRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty()),
            "{case_id} must compute holonomy from source-backed continuation inputs"
        );
        assert!(
            holonomy["comparedContinuationSummary"]
                .as_str()
                .is_some_and(|summary| summary.contains("semanticEvidence=")
                    && summary.contains("traceAxes=")
                    && summary.contains("missing=")),
            "{case_id} must expose measured continuation comparison basis"
        );

        if let Some(expected) = case["expectedHolonomyValue"].as_i64() {
            assert_eq!(
                holonomy["value"], expected,
                "{case_id} must lock expected holonomy value"
            );
            if expected == 0 {
                assert!(
                    holonomy["comparedContinuationSummary"]
                        .as_str()
                        .is_some_and(|summary| summary.contains("semanticEvidence=0")),
                    "{case_id} zero holonomy must come from absent source-backed semantic defect, not text fallback"
                );
            }
        }
        if let Some(minimum) = case["minimumHolonomyValue"].as_i64() {
            assert!(
                holonomy["value"]
                    .as_i64()
                    .is_some_and(|value| value >= minimum),
                "{case_id} must expose nonzero holonomy"
            );
            assert!(
                holonomy["observationRefs"].as_array().is_some_and(|refs| {
                    refs.iter().any(|item| {
                        item.as_str()
                            .is_some_and(|value| value.starts_with("semantic:"))
                    })
                }),
                "{case_id} nonzero holonomy must be backed by semantic observation refs"
            );
        }
        if let Some(expected_status) = case["expectedStokesStatus"].as_str() {
            assert_eq!(
                stokes["status"], expected_status,
                "{case_id} must lock Stokes status"
            );
            if expected_status == "filledNonzeroHolonomyReview" {
                assert!(
                    stokes["fillingEvidenceRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
                        && stokes["localCurvatureCellCandidates"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty()),
                    "{case_id} Stokes positive reading must require measured filler and local curvature cells"
                );
            }
        }
        if let Some(required_missing) = case["requiredMissingEvidence"].as_str() {
            assert!(
                holonomy["missingFillerRefs"]
                    .as_array()
                    .expect("missing filler refs are array")
                    .iter()
                    .any(|item| item.as_str() == Some(required_missing)),
                "{case_id} must keep missing filler evidence"
            );
            assert!(
                report["unfilledLoops"]
                    .as_array()
                    .expect("unfilled loops are array")
                    .iter()
                    .any(|item| item.as_str() == Some(loop_ref)),
                "{case_id} must surface as an unfilled loop"
            );
        }
        if let Some(required_text) = case["requiredText"].as_str() {
            assert!(
                packet.to_string().contains(required_text),
                "{case_id} must keep required fixture text {required_text}"
            );
        }
    }
}

#[test]
fn complete_archmap_acceptance_fixture_runs_full_measurement_without_private_names() {
    let root = complete_archmap_acceptance_root();
    let manifest = read_json(&root.join("manifest.json"));
    let archmap = read_json(&root.join("archmap.json"));
    let law_policy = read_json(&root.join("law_policy.json"));
    let out_dir = temp_dir("complete-archmap-acceptance");

    assert_eq!(
        manifest["schemaVersion"],
        "complete-archmap-acceptance-fixture-manifest-v0"
    );
    let minimum_counts = &manifest["minimumCounts"];
    for (field, minimum) in [
        ("atomObservations", "atomObservations"),
        ("moleculeObservations", "moleculeObservations"),
        ("semanticObservations", "semanticObservations"),
        ("projectionInfo", "projectionInfo"),
    ] {
        let count = archmap[field]
            .as_array()
            .unwrap_or_else(|| panic!("{field} must be an array"))
            .len() as u64;
        let minimum = minimum_counts[minimum]
            .as_u64()
            .unwrap_or_else(|| panic!("{field} minimum is present"));
        assert!(
            count >= minimum,
            "complete ArchMap acceptance fixture must keep enough {field}: {count} < {minimum}"
        );
    }

    let public_fixture_text = format!("{}\n{}\n{}", manifest, archmap, law_policy);
    for forbidden in [
        "private_repo_name",
        "private/repo/path",
        ".archsig/private-repo",
    ] {
        assert!(
            !public_fixture_text.contains(forbidden),
            "sanitized acceptance fixture must not expose private identifier {forbidden}"
        );
    }

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("output directory path is utf-8"),
    ]);

    for (file, label) in [
        ("archmap-validation.json", "ArchMap validation"),
        ("law-policy-validation.json", "LawPolicy validation"),
        (
            "archsig-analysis-validation.json",
            "ArchSig analysis validation",
        ),
    ] {
        let validation = read_json(&out_dir.join(file));
        assert_eq!(
            validation["summary"]["result"], "pass",
            "{label} must pass for complete-first acceptance fixture"
        );
    }

    let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    let spectrum = &packet["architectureSpectrumReport"];
    assert!(
        spectrum["topHotspots"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && spectrum["recurrentObstructions"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "complete ArchMap acceptance fixture must expose meaningful spectrum readings"
    );

    let expected = &manifest["expectedReadings"];
    let homotopy = &packet["architectureHomotopyReport"];
    for (field, minimum_field) in [
        ("filledLoops", "minFilledLoops"),
        ("nonzeroHolonomyLoops", "minNonzeroHolonomyLoops"),
        ("topLocalCurvatureCells", "minLocalCurvatureCells"),
    ] {
        let count = homotopy[field]
            .as_array()
            .unwrap_or_else(|| panic!("{field} must be an array"))
            .len() as u64;
        let minimum = expected[minimum_field]
            .as_u64()
            .unwrap_or_else(|| panic!("{minimum_field} is present"));
        assert!(
            count >= minimum,
            "complete ArchMap acceptance fixture must keep {field}: {count} < {minimum}"
        );
    }

    let required_stokes_status = expected["requiredStokesStatus"]
        .as_str()
        .expect("required Stokes status is present");
    assert!(
        packet["stokesStyleReadings"]
            .as_array()
            .expect("Stokes readings are array")
            .iter()
            .any(|reading| reading["status"] == required_stokes_status
                && reading["measurementStatus"] == "measured"
                && reading["localCurvatureCellCandidates"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())),
        "complete ArchMap acceptance fixture must include measured Stokes positive local curvature"
    );

    let required_gap = expected["requiredBlockedGap"]
        .as_str()
        .expect("required blocked gap is present");
    let blocked_hole = packet["architecturalHoleReadings"]
        .as_array()
        .expect("architectural hole readings are array")
        .iter()
        .find(|reading| {
            reading["missingFillerEvidence"]
                .as_array()
                .is_some_and(|items| items.iter().any(|item| item.as_str() == Some(required_gap)))
        })
        .expect("targeted gap must remain an architectural hole");
    let blocked_loop = blocked_hole["loopRef"]
        .as_str()
        .expect("blocked hole loop ref is present");
    assert!(
        homotopy["unfilledLoops"]
            .as_array()
            .expect("unfilled loops are array")
            .iter()
            .any(|item| item.as_str() == Some(blocked_loop)),
        "targeted missing filler must stay in unfilled loops"
    );
    assert!(
        packet["stokesStyleReadings"]
            .as_array()
            .expect("Stokes readings are array")
            .iter()
            .any(|reading| reading["loopRef"] == blocked_loop
                && reading["status"] == "blockedByArchitecturalHole"
                && reading["measurementStatus"] == "blockedByCoverageGap"),
        "targeted gap loop must remain blocked while unrelated filled loops are measured"
    );

    let summary_path = out_dir.join("archsig-analysis-summary.json");
    run_sig0(&[
        "analysis-summary",
        "--packet",
        out_dir
            .join("archsig-analysis-packet.json")
            .to_str()
            .expect("packet path is utf-8"),
        "--archmap-validation",
        out_dir
            .join("archmap-validation.json")
            .to_str()
            .expect("ArchMap validation path is utf-8"),
        "--law-policy-validation",
        out_dir
            .join("law-policy-validation.json")
            .to_str()
            .expect("LawPolicy validation path is utf-8"),
        "--analysis-validation",
        out_dir
            .join("archsig-analysis-validation.json")
            .to_str()
            .expect("analysis validation path is utf-8"),
        "--out",
        summary_path.to_str().expect("summary path is utf-8"),
    ]);
    let summary = read_json(&summary_path);
    assert_eq!(
        summary["verdict"]["readingMode"], "measurementOverSuppliedArchMapAndLawPolicy",
        "summary must lead with measured ArchMap + LawPolicy verdict"
    );
    assert!(
        summary["qualityMeasurement"]["spectrumHotspotCount"]
            .as_u64()
            .is_some_and(|count| count >= 1)
            && summary["qualityMeasurement"]["nonzeroHolonomyLoopCount"]
                .as_u64()
                .is_some_and(|count| count >= 1)
            && summary["qualityMeasurement"]["localCurvatureCellCount"]
                .as_u64()
                .is_some_and(|count| count >= 1),
        "summary must expose spectrum, homotopy, and Stokes power before metadata"
    );
    assert!(
        summary["actionQueue"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "summary must keep a repair/review action queue"
    );
}

#[test]
fn cli_pr_review_reads_archmapstore_inputs() {
    let out_dir = temp_dir("pr-review");
    let review = pr_review_root();
    let minimal = fixture_root();
    let report = out_dir.join("archsig-pr-review.json");

    run_sig0(&[
        "pr-review",
        "--base-archmap",
        minimal
            .join("archmap.json")
            .to_str()
            .expect("base archmap path is utf-8"),
        "--delta-archmap",
        review
            .join("archmap_delta.json")
            .to_str()
            .expect("delta path is utf-8"),
        "--law-policy",
        minimal
            .join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "archsig-pr-review-report-v1");
    assert_eq!(
        json["canonicalInputs"]["baseArchMap"]["schemaVersion"],
        "archmap-observation-map-v0"
    );
    assert_eq!(
        json["canonicalInputs"]["deltaArchMap"]["schemaVersion"],
        "archmap-delta-v0"
    );
    assert_eq!(
        json["canonicalInputs"]["lawPolicy"]["schemaVersion"],
        "law-policy-v0"
    );
    assert_eq!(json["policyBoundary"]["lawPolicyRequired"], true);
    assert_eq!(
        json["policyBoundary"]["rule"],
        "No LawPolicy, no ArchSig judgement"
    );
    assert!(
        json.get("rawDiffHint").is_none(),
        "raw diff must not be part of the PR review input surface"
    );
    assert!(
        json["changedObservations"]
            .as_array()
            .is_some_and(|observations| observations.iter().any(|observation| {
                observation["ref"] == "atom:contract:create-user" && observation["matched"] == true
            }))
    );
    assert!(
        json["policyMatchedLaws"]
            .as_array()
            .is_some_and(|laws| !laws.is_empty())
    );
    assert!(json.get("nonConclusions").is_none());
}

#[test]
fn cli_negative_archmap_fixtures_preserve_guardrails() {
    let out_dir = temp_dir("negative-archmap-fixtures");
    let root = fixture_root();

    let concern_validation = out_dir.join("concern-validation.json");
    let concern_output = run_sig0_output(&[
        "archmap",
        "--input",
        root.join("archmap_invalid_concern_promoted.json")
            .to_str()
            .expect("invalid concern fixture path is utf-8"),
        "--out",
        concern_validation
            .to_str()
            .expect("concern validation path is utf-8"),
    ]);
    assert!(
        !concern_output.status.success(),
        "concern promotion fixture must fail validation"
    );
    let concern_json = read_json(&concern_validation);
    assert!(
        has_check_result(
            &concern_json,
            "archmap-concern-hints-are-not-obstruction-circuits",
            "fail"
        ),
        "concernHints must not be accepted as obstruction circuits"
    );

    let gap_validation = out_dir.join("gap-validation.json");
    let gap_output = run_sig0_output(&[
        "archmap",
        "--input",
        root.join("archmap_invalid_gap_measured_zero.json")
            .to_str()
            .expect("invalid gap fixture path is utf-8"),
        "--out",
        gap_validation
            .to_str()
            .expect("gap validation path is utf-8"),
    ]);
    assert!(
        !gap_output.status.success(),
        "gap measured-zero fixture must fail validation"
    );
    let gap_json = read_json(&gap_validation);
    assert!(
        has_check_result(
            &gap_json,
            "archmap-observation-gaps-not-measured-zero",
            "fail"
        ),
        "observation gaps must not be rounded to measured zero"
    );
}

#[test]
fn cli_regression_same_archmap_multiple_law_policies() {
    let root = fixture_root();
    let full_packet = read_json(&root.join("archsig_analysis_packet.json"));
    let layer_only_packet = read_json(&root.join("archsig_analysis_packet_layer_only.json"));
    assert_ne!(
        full_packet["selectedLawPolicyRef"]["artifactId"],
        layer_only_packet["selectedLawPolicyRef"]["artifactId"],
        "golden corpus must include multiple LawPolicy analyses"
    );
    assert!(
        full_packet["obstructionCircuits"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "full policy fixture should construct an obstruction"
    );
    assert_eq!(
        layer_only_packet["obstructionCircuits"]
            .as_array()
            .expect("layer-only obstructions are array")
            .len(),
        0,
        "layer-only policy should reanalyze the same ArchMap without semantic obstruction"
    );
}

#[test]
fn cli_locks_archmap_atom_observation_regression() {
    let out_dir = temp_dir("archmap-atom-observation-regression");
    let root = fixture_root();
    let archmap = expressiveness_root().join("archmap_atom_observation_suite_v0.json");
    let validation = out_dir.join("archmap-validation.json");

    run_sig0(&[
        "archmap",
        "--input",
        archmap.to_str().expect("archmap path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
    ]);

    let json = read_json(&validation);
    assert_eq!(
        json["atomicObservationSummary"]["atomObservationCount"], 4,
        "Atom observation regression must lock source-grounded atom observations"
    );
    assert_eq!(
        json["atomicObservationSummary"]["moleculeObservationCount"], 1,
        "Atom observation regression must lock molecule observations"
    );
    assert_eq!(
        json["atomicObservationSummary"]["semanticObservationCount"], 1,
        "Atom observation regression must lock semantic observations"
    );
    assert_eq!(
        json["atomicObservationSummary"]["observationGapCount"], 1,
        "Atom observation regression must preserve observation gaps"
    );
    assert_eq!(
        json["atomicObservationSummary"]["concernHintCount"], 1,
        "Atom observation regression must keep concern hints as review cues"
    );
    assert!(
        json.get(&["legacy", "SchemaChecks"].concat()).is_none(),
        "ArchMap validation report must not retain legacy compatibility checks"
    );
    assert!(
        json.get(&["homo", "morphismDiagnostics"].concat())
            .is_none(),
        "ArchMap validation report must not retain pre-Atom projection diagnostics"
    );

    let full_packet = out_dir.join("archsig-analysis-full.json");
    let full_validation = out_dir.join("archsig-analysis-full-validation.json");
    run_sig0(&[
        "archsig-analysis",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--out",
        full_packet.to_str().expect("full packet path is utf-8"),
        "--validation-out",
        full_validation
            .to_str()
            .expect("full validation path is utf-8"),
    ]);
    let full = read_json(&full_packet);
    assert_north_star_packet_surfaces(&full);
    assert!(
        full["obstructionCircuits"]
            .as_array()
            .expect("full obstruction circuits are array")
            .iter()
            .any(|entry| entry["lawRef"] == "law:semantic-contract-alignment"),
        "semantic LawPolicy should construct law-relative obstruction from the same ArchMap"
    );

    let layer_packet = out_dir.join("archsig-analysis-layer-only.json");
    let layer_validation = out_dir.join("archsig-analysis-layer-only-validation.json");
    run_sig0(&[
        "archsig-analysis",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy_layer_only.json")
            .to_str()
            .expect("layer-only law policy path is utf-8"),
        "--out",
        layer_packet.to_str().expect("layer packet path is utf-8"),
        "--validation-out",
        layer_validation
            .to_str()
            .expect("layer validation path is utf-8"),
    ]);
    let layer_only = read_json(&layer_packet);
    assert_eq!(
        layer_only["obstructionCircuits"]
            .as_array()
            .expect("layer-only obstruction circuits are array")
            .len(),
        0,
        "layer-only LawPolicy should reanalyze the same ArchMap without semantic obstruction"
    );
}

#[test]
fn cli_rejects_legacy_archmap_fields() {
    let out_dir = temp_dir("legacy-archmap-fields");
    let mut archmap = read_json(&fixture_root().join("archmap.json"));
    archmap[["map", "Items"].concat()] = serde_json::json!([]);
    archmap[["homo", "morphism"].concat()] =
        serde_json::json!({"reading": "old compatibility input"});
    archmap[["obstruction", "CircuitCandidates"].concat()] = serde_json::json!([]);
    let input = out_dir.join("legacy-archmap.json");
    fs::write(
        &input,
        serde_json::to_vec_pretty(&archmap).expect("json serializes"),
    )
    .expect("legacy fixture can be written");
    let output = run_sig0_output(&[
        "archmap",
        "--input",
        input.to_str().expect("legacy input path is utf-8"),
        "--out",
        out_dir
            .join("validation.json")
            .to_str()
            .expect("validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "legacy ArchMap fields must be rejected instead of accepted as compatibility input"
    );
}

#[test]
fn legacy_archsig_surface_does_not_reenter_source_or_paths() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let src_root = crate_root.join("src");
    let disallowed_source_symbols = [
        "pub struct Sig0Document",
        "AIR_SCHEMA_VERSION",
        "SIGNATURE_DIFF_REPORT_SCHEMA_VERSION",
        "FEATURE_EXTENSION_REPORT_SCHEMA_VERSION",
        "THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION",
        "RepairRuleRegistryV0",
        "SynthesisConstraint",
        "NoSolutionCertificate",
        "AatObservableBundle",
        "OrganizationPolicy",
        "ArchitecturePolicy",
        "PolicyDecision",
        "PrQuality",
        "SnapshotAttribution",
        "FrameworkAdapter",
    ];
    for file in collect_files(&src_root) {
        let text = fs::read_to_string(&file).expect("source file is utf-8");
        for symbol in disallowed_source_symbols {
            assert!(
                !text.contains(symbol),
                "legacy ArchSig symbol {symbol} re-entered {}",
                file.display()
            );
        }
    }

    for removed_path in [
        "skills/aat-reviewer",
        "skills/arch-pr-analyzer",
        "tests/fixtures/air",
        "tests/fixtures/module_root",
        "tests/fixtures/python_imports",
    ] {
        assert!(
            !crate_root.join(removed_path).exists(),
            "legacy ArchSig path {removed_path} re-entered"
        );
    }
}

#[test]
fn cli_schema_catalog_is_primary_archsig_surface_only() {
    let out_dir = temp_dir("schema-catalog");
    let catalog = out_dir.join("schema-version-catalog.json");
    run_sig0(&[
        "schema-catalog",
        "--out",
        catalog.to_str().expect("catalog path is utf-8"),
    ]);
    let json = read_json(&catalog);
    let artifacts = json["artifacts"].as_array().expect("artifacts are array");
    let ids = artifacts
        .iter()
        .map(|entry| entry["artifactId"].as_str().expect("artifact id"))
        .collect::<Vec<_>>();
    assert_eq!(
        ids,
        vec![
            "archmap",
            "archmap-validation-report",
            "law-policy",
            "law-policy-validation-report",
            "archsig-analysis-packet",
            "archsig-analysis-packet-validation-report",
        ]
    );
    for entry in artifacts {
        assert_eq!(entry["artifactRole"].as_str(), Some("primary"));
    }
}

fn removed_commands() -> &'static [&'static str] {
    &[
        "adapter-scan",
        "validate",
        "relation-complexity",
        "snapshot",
        "signature-diff",
        "diff",
        "air",
        "air-from-archmap",
        "validate-air",
        "feature-report",
        "theorem-check",
        "repair-registry",
        "synthesis-constraints",
        "no-solution-certificate",
        "organization-policy",
        "architecture-policy",
        "law-violation-report",
        "law-policy-templates",
        "custom-rule-plugins",
        "measurement-units",
        "pr-quality-analysis",
        "aat-observable-bundle",
        "archmap-workflow",
        "reported-axes-catalog",
        "policy-decision",
        "report-artifacts",
        "pr-comment",
        "baseline-suppression",
        "schema-compatibility",
    ]
}

fn temp_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("archsig-{test_name}-{nanos}"));
    fs::create_dir_all(&dir).expect("temporary directory can be created");
    dir
}

fn run_sig0(args: &[&str]) {
    let output = run_sig0_output(args);
    assert!(
        output.status.success(),
        "archsig {:?} failed\nstdout:\n{}\nstderr:\n{}",
        args,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_sig0_output(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_archsig"))
        .args(args)
        .output()
        .expect("archsig command runs")
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("json fixture can be read"))
        .expect("json fixture parses")
}

fn has_nested_key(value: &Value, key: &str) -> bool {
    match value {
        Value::Object(object) => {
            object.contains_key(key) || object.values().any(|value| has_nested_key(value, key))
        }
        Value::Array(items) => items.iter().any(|value| has_nested_key(value, key)),
        _ => false,
    }
}

fn expand_large_repo_summary_fixture(packet: &mut Value, manifest: &Value) {
    let hotspot_count = manifest["hotspotCount"]
        .as_u64()
        .expect("manifest hotspotCount is numeric") as usize;
    let support_refs_per_hotspot = manifest["supportRefsPerHotspot"]
        .as_u64()
        .expect("manifest supportRefsPerHotspot is numeric")
        as usize;
    let spectrum = packet["architectureSpectrumReport"]
        .as_object_mut()
        .expect("packet contains ArchitectureSpectrumReport");
    let base_hotspot = spectrum["topHotspots"][0].clone();
    let hotspots = (0..hotspot_count)
        .map(|index| {
            let mut hotspot = base_hotspot.clone();
            hotspot["hotspotId"] =
                serde_json::json!(format!("spectrum-hotspot:sanitized-large-repo-{index}"));
            hotspot["axisRef"] = serde_json::json!(if index % 2 == 0 {
                "axis:semantic-inconsistency"
            } else {
                "axis:layer-violation"
            });
            hotspot["curvatureValue"] = serde_json::json!((index % 5) + 1);
            hotspot["supportRefs"] = serde_json::Value::Array(
                (0..support_refs_per_hotspot)
                    .map(|support_index| {
                        serde_json::json!(format!("atom:sanitized-support-{index}-{support_index}"))
                    })
                    .collect(),
            );
            hotspot["witnessRefs"] = serde_json::Value::Array(
                (0..support_refs_per_hotspot)
                    .map(|support_index| {
                        serde_json::json!(format!(
                            "witness:sanitized-large-repo-{index}-{support_index}"
                        ))
                    })
                    .collect(),
            );
            hotspot["coverageGapRefs"] = serde_json::json!([
                "gap-runtime-user-db-trace: runtime trace was requested but not supplied"
            ]);
            hotspot
        })
        .collect();
    spectrum.insert(
        "topHotspots".to_string(),
        serde_json::Value::Array(hotspots),
    );
}

fn has_check_result(json: &Value, id: &str, result: &str) -> bool {
    json.as_object().is_some_and(|object| {
        object.values().any(|value| {
            value.as_array().is_some_and(|checks| {
                checks
                    .iter()
                    .any(|check| check["id"] == id && check["result"] == result)
            })
        })
    })
}

fn loop_ref_for_path_rule<'a>(packet: &'a Value, path_rule_ref: &str) -> &'a str {
    let path_pair = packet["pathPairCandidates"]
        .as_array()
        .expect("path pair candidates are array")
        .iter()
        .find(|candidate| candidate["pPathRef"].as_str() == Some(path_rule_ref))
        .unwrap_or_else(|| panic!("missing path pair for {path_rule_ref}"));
    let path_pair_ref = path_pair["candidateId"]
        .as_str()
        .expect("path pair candidate id is present");
    packet["loopCandidates"]
        .as_array()
        .expect("loop candidates are array")
        .iter()
        .find(|candidate| candidate["pathPairRef"].as_str() == Some(path_pair_ref))
        .and_then(|candidate| candidate["loopId"].as_str())
        .unwrap_or_else(|| panic!("missing loop candidate for {path_rule_ref}"))
}

fn assert_north_star_packet_surfaces(json: &Value) {
    for concept in [
        "Atom",
        "Configuration",
        "ArchitectureObject",
        "Invariant",
        "LawUniverse",
        "ObstructionCircuit",
        "ArchitectureSignature",
        "Operation",
        "Path",
        "Homotopy",
        "Diagram",
        "AnalyticRepresentation",
    ] {
        assert!(
            json["aatConceptSurfaces"]
                .as_array()
                .expect("aat concept surfaces are array")
                .iter()
                .any(|entry| entry["concept"] == concept),
            "North Star packet must expose AAT concept {concept}"
        );
    }
    for family in [
        "weightedAdjacencyMatrix",
        "walkCount",
        "reachableConeSize",
        "nilpotenceBoundary",
        "selectedSubgraphSpectrum",
        "propagationDepth",
        "spectralRadius",
        "curvatureValuation",
        "stateAlgebra",
        "zeroReflectingAggregateBoundary",
    ] {
        assert!(
            json["analyticRepresentations"]
                .as_array()
                .expect("analytic representations are array")
                .iter()
                .any(|entry| entry["representationFamily"] == family),
            "North Star packet must expose analytic representation {family}"
        );
    }
    let weighted_adjacency = json["analyticRepresentations"]
        .as_array()
        .expect("analytic representations are array")
        .iter()
        .find(|entry| entry["representationFamily"] == "weightedAdjacencyMatrix")
        .expect("weighted adjacency representation exists");
    assert!(
        weighted_adjacency["selectedGraphNodes"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && weighted_adjacency["selectedGraphEdges"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && weighted_adjacency["sparseMatrixEntries"]
                .as_array()
                .is_some_and(|items| {
                    !items.is_empty()
                        && items.iter().all(|entry| {
                            entry["rowRef"].as_str().is_some()
                                && entry["columnRef"].as_str().is_some()
                                && entry["value"].as_i64().is_some_and(|value| value > 0)
                                && entry["evidenceRefs"]
                                    .as_array()
                                    .is_some_and(|refs| !refs.is_empty())
                        })
                }),
        "weighted adjacency must expose source-backed selected graph nodes, edges, and sparse matrix entries"
    );
    for principle in [
        "InformationHiding",
        "Encapsulation",
        "SeparationOfConcerns",
        "Substitutability",
        "OpenClosedExtension",
        "DependencyInversion",
        "RepresentationIndependence",
        "IdempotencyAndReplaySafety",
        "AuthorityAndTrustBoundary",
    ] {
        assert!(
            json["designPrincipleReadings"]
                .as_array()
                .expect("design principle readings are array")
                .iter()
                .any(|entry| entry["principle"] == principle),
            "North Star packet must expose design principle {principle}"
        );
    }
    assert!(
        json["designPrincipleReadings"]
            .as_array()
            .expect("design principle readings are array")
            .iter()
            .all(|entry| {
                matches!(
                    entry["status"].as_str(),
                    Some("preserved" | "stressed" | "unmeasured" | "notApplicable")
                ) && entry["witnessRuleRef"].as_str().is_some()
                    && entry["witnessStatus"].as_str().is_some()
                    && entry["witnessEvidenceRefs"].as_array().is_some()
                    && entry["recommendedNextAction"]
                        .as_str()
                        .is_some_and(|action| !action.contains("turn stressed readings"))
            }),
        "design principle readings must use principle-specific witness evaluation"
    );
    assert!(
        json["boundedJudgements"]
            .as_array()
            .expect("bounded judgements are array")
            .iter()
            .any(|entry| entry["status"] == "actionable"),
        "bounded judgements must include actionable readings"
    );
    assert!(
        json.get("workflowSignalReadings").is_none() && !has_nested_key(json, "signalDensityScore"),
        "North Star packet must not expose workflow-signal density proxy readings"
    );
    let spectral_readings = json["spectralAnalysisReadings"]
        .as_array()
        .expect("spectral analysis readings are array");
    assert!(
        !spectral_readings.is_empty(),
        "North Star packet must expose spectral analysis readings"
    );
    for family in [
        "relationAtomWeightedAdjacencyMatrix",
        "moleculeAtomOverlapCouplingMatrix",
        "obstructionAxisCurvatureMatrix",
        "operationSignatureDeltaMatrix",
    ] {
        assert!(
            spectral_readings
                .iter()
                .any(|entry| entry["representationFamily"] == family),
            "North Star packet must expose spectral representation {family}"
        );
    }
    assert!(
        spectral_readings.iter().all(|entry| {
            entry["matrixShape"]["rowDomain"].as_str().is_some()
                && entry["matrixShape"]["columnDomain"].as_str().is_some()
                && entry["entryRule"].as_str().is_some()
                && entry["values"]
                    .as_array()
                    .is_some_and(|values| !values.is_empty())
                && entry["coverageBoundary"].as_str().is_some()
                && entry["zeroReflectingBoundary"].as_str().is_some()
                && entry["recommendedNextAction"].as_str().is_some()
        }),
        "spectral analysis readings must carry matrix shape, entry rule, values, and evidence boundaries"
    );
    let spectral_modes = json["spectralModeReadings"]
        .as_array()
        .expect("spectral mode readings are array");
    assert!(
        !spectral_modes.is_empty(),
        "North Star packet must expose spectral mode readings"
    );
    for family in [
        "moleculeAtomOverlapCouplingMatrix",
        "obstructionAxisCurvatureMatrix",
        "operationSignatureDeltaMatrix",
    ] {
        assert!(
            spectral_modes
                .iter()
                .any(|entry| entry["representationFamily"] == family),
            "North Star packet must expose spectral mode for representation {family}"
        );
    }
    assert!(
        spectral_modes.iter().all(|entry| {
            entry["sourceSpectralReadingRef"].as_str().is_some()
                && entry["modeKind"].as_str().is_some()
                && entry["spectralGapProxy"]["value"].as_str().is_some()
                && entry["localizationIndex"]["value"].as_str().is_some()
                && entry["matrixDensity"]["value"].as_str().is_some()
                && entry["decomposabilityReading"].as_str().is_some()
                && entry["repairPerturbationReading"].as_str().is_some()
                && entry["evidenceBoundary"].as_str().is_some()
                && entry["recommendedNextAction"].as_str().is_some()
        }),
        "spectral mode readings must carry source refs, mode metrics, decomposability, repair perturbation, and evidence boundaries"
    );
    let spectral_drilldowns = json["spectralDrilldownReadings"]
        .as_array()
        .expect("spectral drilldown readings are array");
    assert!(
        !spectral_drilldowns.is_empty(),
        "North Star packet must expose spectral drilldown readings"
    );
    assert!(
        spectral_drilldowns.iter().all(|entry| {
            entry["sourceSpectralModeRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
                && entry["dominantAtomFamilyComposition"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["repairAxisDeltaReadings"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["evidenceBoundary"].as_str().is_some()
                && entry["recommendedNextAction"].as_str().is_some()
        }),
        "spectral drilldown readings must carry source mode refs, atom-family composition, repair axis deltas, and evidence boundaries"
    );
    assert!(
        spectral_drilldowns.iter().all(|entry| {
            entry["dominantAtomFamilyComposition"]
                .as_array()
                .expect("dominant atom family composition is array")
                .iter()
                .all(|composition| {
                    composition["atomFamily"].as_str().is_some()
                        && composition["count"].as_u64().is_some_and(|count| count > 0)
                        && composition["atomObservationRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
        }),
        "dominant atom-family composition must carry atom family counts and refs"
    );
    let curvature_support = json["curvatureSupportReadings"]
        .as_array()
        .expect("curvature support readings are array");
    assert!(
        !curvature_support.is_empty(),
        "North Star packet must expose curvature support readings"
    );
    assert!(
        curvature_support.iter().all(|entry| {
            entry["profileRef"].as_str().is_some()
                && entry["status"].as_str().is_some()
                && entry["witnessSupports"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["topCurvatureModes"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["witnessClusters"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["coverageBoundary"].as_str().is_some()
                && entry["exactnessAssumptionRefs"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["measurementBoundary"].as_str().is_some()
                && entry["nonConclusions"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
        }),
        "curvature support readings must carry profile refs, witness rows, modes, clusters, and boundaries"
    );
    assert!(
        curvature_support.iter().all(|entry| {
            entry["witnessSupports"]
                .as_array()
                .expect("curvature witness supports are array")
                .iter()
                .all(|support| {
                    support["witnessRuleRef"].as_str().is_some()
                        && support["selectedAxisRef"].as_str().is_some()
                        && support["signatureAxisRef"].as_str().is_some()
                        && support["curvatureValue"]
                            .as_i64()
                            .is_some_and(|value| value >= 0)
                        && support["weight"].as_i64().is_some_and(|value| value >= 0)
                        && support["missingEvidence"].as_array().is_some()
                        && support["reading"].as_str().is_some()
                })
        }),
        "curvature witness support rows must carry witness, axis, curvature, weight, missing evidence, and reading fields"
    );
    assert!(
        curvature_support.iter().any(|entry| {
            entry["witnessSupports"]
                .as_array()
                .expect("curvature witness supports are array")
                .iter()
                .any(|support| {
                    support["curvatureValue"] == 0
                        && support["missingEvidence"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                })
        }),
        "curvature support readings must keep unmeasured support separate from measured zero"
    );
    let curvature_transfer = json["curvatureTransferReadings"]
        .as_array()
        .expect("curvature transfer readings are array");
    assert!(
        !curvature_transfer.is_empty(),
        "North Star packet must expose curvature transfer readings"
    );
    assert!(
        curvature_transfer.iter().all(|entry| {
            entry["profileRef"].as_str().is_some()
                && entry["transferOperator"]["nonzeroEdgeCount"]
                    .as_u64()
                    .is_some()
                && entry["transferOperator"]["entryRule"].as_str().is_some()
                && entry["transferEdges"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["recurrentObstructionModes"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["spectralRadiusReading"]["value"].as_str().is_some()
                && entry["evidenceBoundary"].as_str().is_some()
                && entry["nonConclusions"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
        }),
        "curvature transfer readings must carry operator, edges, recurrent modes, rho reading, and non-conclusions"
    );
    assert!(
        curvature_transfer.iter().all(|entry| {
            entry["transferEdges"]
                .as_array()
                .expect("curvature transfer edges are array")
                .iter()
                .all(|edge| {
                    edge["sourceSupportRef"].as_str().is_some()
                        && edge["targetSupportRef"].as_str().is_some()
                        && edge["witnessRefs"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                        && edge["defectValue"].as_i64().is_some_and(|value| value > 0)
                        && edge["weight"].as_i64().is_some_and(|value| value > 0)
                })
        }),
        "curvature transfer edges must carry support refs, witness refs, positive defect value, and positive weight"
    );
    assert!(
        curvature_transfer.iter().all(|entry| {
            entry["nonConclusions"]
                .as_array()
                .expect("curvature transfer non-conclusions are array")
                .iter()
                .any(|item| {
                    item.as_str()
                        .is_some_and(|text| text.contains("does not replace FieldSig forecast"))
                })
        }),
        "curvature transfer readings must preserve FieldSig forecast boundary"
    );
    let architecture_spectrum_report = json["architectureSpectrumReport"]
        .as_object()
        .expect("North Star packet must expose ArchitectureSpectrumReport");
    assert!(
        architecture_spectrum_report["topHotspots"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "ArchitectureSpectrumReport must expose hotspots"
    );
    assert!(
        architecture_spectrum_report["topEigenmodes"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "ArchitectureSpectrumReport must expose top mode data"
    );
    assert!(
        architecture_spectrum_report["topWitnessClusters"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "ArchitectureSpectrumReport must expose witness clusters"
    );
    assert!(
        architecture_spectrum_report["recurrentObstructions"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "ArchitectureSpectrumReport must expose recurrent obstruction entries"
    );
    assert!(
        architecture_spectrum_report["measuredBoundary"]
            .as_str()
            .is_some_and(|boundary| boundary.contains("curvature support and transfer")),
        "ArchitectureSpectrumReport must keep measured boundary explicit"
    );
    assert!(
        architecture_spectrum_report["recommendedReviewFocus"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "ArchitectureSpectrumReport must expose next review focus"
    );
    assert!(
        architecture_spectrum_report["nonConclusions"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| {
                    item.as_str()
                        .is_some_and(|text| text.contains("single architecture quality score"))
                })
            }),
        "ArchitectureSpectrumReport must preserve report-level non-conclusions"
    );
    let transfer_bridges = json["transferBridgeReadings"]
        .as_array()
        .expect("transfer bridge readings are array");
    assert!(
        !transfer_bridges.is_empty(),
        "North Star packet must expose transfer bridge readings"
    );
    assert!(
        transfer_bridges.iter().all(|entry| {
            entry["transferBridgeId"].as_str().is_some()
                && entry["status"].as_str().is_some()
                && entry["transferMatrixEntries"].as_array().is_some()
                && entry["bridgeAtomFamilies"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["evolutionRiskRanking"]["repairTransferRiskRanking"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["evolutionRiskRanking"]["boundaryPreparationRanking"]
                    .as_array()
                    .is_some()
                && entry["reading"].as_str().is_some()
                && entry["evidenceBoundary"].as_str().is_some()
                && entry["recommendedNextAction"].as_str().is_some()
        }),
        "transfer bridge readings must carry transfer matrix, bridge atom families, evolution risk ranking, and evidence boundaries"
    );
    assert!(
        transfer_bridges.iter().all(|entry| {
            entry["transferMatrixEntries"]
                .as_array()
                .expect("transfer matrix entries are array")
                .iter()
                .all(|matrix_entry| {
                    matrix_entry["operationDeltaRef"].as_str().is_some()
                        && matrix_entry["transferredAxisRef"].as_str().is_some()
                        && matrix_entry["transferWeight"]
                            .as_i64()
                            .is_some_and(|weight| weight > 0)
                        && matrix_entry["transferKind"].as_str().is_some()
                        && matrix_entry["reading"].as_str().is_some()
                })
        }),
        "transfer matrix entries must carry operation x transferred-axis readings when present"
    );
    assert!(
        transfer_bridges.iter().all(|entry| {
            entry["bridgeAtomFamilies"]
                .as_array()
                .expect("bridge atom families are array")
                .iter()
                .all(|bridge| {
                    bridge["sourceHubMoleculeRef"].as_str().is_some()
                        && bridge["targetHubMoleculeRef"].as_str().is_some()
                        && bridge["bridgeAtomFamilies"].as_array().is_some()
                        && bridge["pathPairRefs"].as_array().is_some()
                        && bridge["edgeBreakdowns"].as_array().is_some()
                        && bridge["reviewRisk"].as_str().is_some()
                        && bridge["recommendedBoundaryPreparation"].as_str().is_some()
                        && bridge["evidenceBoundary"].as_str().is_some()
                })
        }),
        "bridge atom family readings must carry hub refs, bridge families, path refs, review risk, and evidence boundaries"
    );
    assert!(
        transfer_bridges.iter().all(|entry| {
            entry["bridgeAtomFamilies"]
                .as_array()
                .expect("bridge atom families are array")
                .iter()
                .flat_map(|bridge| {
                    bridge["edgeBreakdowns"]
                        .as_array()
                        .expect("edge breakdowns are array")
                })
                .all(|edge| {
                    edge["sourceMoleculeRef"].as_str().is_some()
                        && edge["targetMoleculeRef"].as_str().is_some()
                        && edge["pairRef"].as_str().is_some()
                        && edge["overlapScore"].as_i64().is_some_and(|score| score > 0)
                        && edge["sharedAtomFamilies"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                        && edge["familySupportingAtomRefs"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                        && edge["sourceRefs"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                        && edge["sourceRefRationale"].as_str().is_some()
                        && edge["dependencyKind"].as_str().is_some()
                        && edge["dependencyReading"].as_str().is_some()
                        && edge["reviewFocus"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                        && edge["recommendedCutKind"].as_str().is_some()
                        && edge["cutRationale"].as_str().is_some()
                        && edge["llmReviewSummary"].as_str().is_some()
                })
        }),
        "bridge edge breakdowns must carry molecule refs, source refs, review focus, dependency reading, and cut recommendation"
    );
    for surface in [
        "atomSupportAxisReadings",
        "atomCompatibilityReadings",
        "lawUniverseCoverageReadings",
        "featureExtensionFormulaReadings",
        "operationCalculusLawReadings",
        "pathSignatureTrajectoryReadings",
        "homotopyOrderSensitivityReadings",
        "diagramFillabilityReadings",
        "observationProjectionFidelityReadings",
        "atomOriginClosureDebtReadings",
        "effectRelationAlgebraReadings",
        "synthesisBlockageReadings",
        "operationPreconditionReadinessReadings",
        "pathMultiplicityLossReadings",
        "representationStrengthReadings",
        "localCurvatureDiagramReadings",
        "threeLayerFlatnessReadings",
        "observationProjectionReadings",
        "stateTransitionAlgebraReadings",
        "operationInvariantGaloisReadings",
        "splitReadinessReadings",
    ] {
        assert!(
            json[surface]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
            "North Star packet must expose AAT structural surface {surface}"
        );
    }
    assert!(
        json["atomSupportAxisReadings"]
            .as_array()
            .expect("Atom support axis readings are array")
            .iter()
            .all(|reading| {
                reading["supportSize"].as_u64().is_some()
                    && reading["axisRestrictionCounts"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["axisConcentration"].as_str().is_some()
                    && reading["mixedAxisMoleculePressure"].as_str().is_some()
                    && reading["coverageBoundary"].as_str().is_some()
            }),
        "Atom support readings must carry support, axis restriction, concentration, and boundary"
    );
    assert!(
        json["atomCompatibilityReadings"]
            .as_array()
            .expect("Atom compatibility readings are array")
            .iter()
            .all(|reading| {
                reading["status"].as_str().is_some()
                    && reading["sameSlotConflictCount"].as_u64().is_some()
                    && reading["payloadInconsistencyKinds"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["payloadComparisonPolicy"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["conflicts"].as_array().is_some_and(|items| {
                        items.iter().all(|conflict| {
                            conflict["payloadComparisonPolicy"].as_str().is_some()
                                && conflict["comparedPayloadRefs"].as_array().is_some()
                                && conflict["sourceRefs"].as_array().is_some()
                                && conflict["confidenceRefs"].as_array().is_some()
                                && conflict["semanticConflictRelationRefs"]
                                    .as_array()
                                    .is_some()
                        })
                    })
                    && reading["confidenceBoundary"].as_str().is_some()
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "Atom compatibility readings must carry conflict counts, status, and boundaries"
    );
    assert!(
        json["lawUniverseCoverageReadings"]
            .as_array()
            .expect("LawUniverse coverage readings are array")
            .iter()
            .all(|reading| {
                reading["requiredLawCoverage"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && reading["witnessFamilyCoverage"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["signatureAxisCoverage"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["coverageRequirementStatus"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["exactnessAssumptionStatus"].as_array().is_some()
                    && reading["lawWitnessAxisEvaluations"]
                        .as_array()
                        .is_some_and(|items| {
                            !items.is_empty()
                                && items.iter().all(|item| {
                                    item["lawRef"].as_str().is_some()
                                        && item["alignmentStatus"].as_str().is_some()
                                        && item["coverageStatus"].as_str().is_some()
                                        && item["exactnessStatus"].as_str().is_some()
                                        && item["requiredWitnessRefs"]
                                            .as_array()
                                            .is_some_and(|refs| !refs.is_empty())
                                        && item["requiredAxisRefs"]
                                            .as_array()
                                            .is_some_and(|refs| !refs.is_empty())
                                        && item["coverageRequirementRefs"]
                                            .as_array()
                                            .is_some_and(|refs| !refs.is_empty())
                                        && item["exactnessAssumptionRefs"]
                                            .as_array()
                                            .is_some_and(|refs| !refs.is_empty())
                                })
                        })
                    && reading["coverageBoundary"].as_str().is_some()
            }),
        "LawUniverse coverage readings must carry law, witness, axis, exactness, and boundary data"
    );
    assert!(
        json["featureExtensionFormulaReadings"]
            .as_array()
            .expect("feature extension readings are array")
            .iter()
            .all(|reading| {
                reading["classificationSummary"]
                    .as_array()
                    .is_some_and(|items| items.len() >= 7)
                    && reading["residualCoverageGapRefs"].as_array().is_some()
                    && reading["witnessBasis"].as_array().is_some_and(|items| {
                        !items.is_empty()
                            && items.iter().all(|basis| {
                                basis["labels"]
                                    .as_array()
                                    .is_some_and(|labels| !labels.is_empty())
                                    && (basis["observationRefs"]
                                        .as_array()
                                        .is_some_and(|refs| !refs.is_empty())
                                        || basis["sourceRefs"]
                                            .as_array()
                                            .is_some_and(|refs| !refs.is_empty()))
                            })
                    })
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "feature extension formula readings must carry required axes, witness basis, and boundary"
    );
    assert!(
        json["operationCalculusLawReadings"]
            .as_array()
            .expect("operation calculus readings are array")
            .iter()
            .all(|reading| {
                reading["operationRef"].as_str().is_some()
                    && reading["compositionStatus"].as_str().is_some()
                    && reading["associativityUnderObservationStatus"]
                        .as_str()
                        .is_some()
                    && reading["refinementAbstractionCompatibility"]
                        .as_str()
                        .is_some()
                    && reading["protectionIdempotence"].as_str().is_some()
                    && reading["runtimeLocalization"].as_str().is_some()
                    && reading["repairMonotonicity"].as_str().is_some()
                    && reading["lawEvidence"].as_array().is_some_and(|items| {
                        items.len() >= 9
                            && items.iter().all(|evidence| {
                                evidence["lawAxis"].as_str().is_some()
                                    && matches!(
                                        evidence["status"].as_str(),
                                        Some("observed")
                                            | Some("unmeasured")
                                            | Some("blocked")
                                            | Some("notApplicable")
                                    )
                                    && evidence["requiredEvidenceRefs"].as_array().is_some()
                                    && evidence["observedEvidenceRefs"].as_array().is_some()
                                    && evidence["blockedReasonRefs"].as_array().is_some()
                            })
                    })
                    && reading["synthesisNoSolutionBoundary"].as_str().is_some()
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "operation calculus readings must carry operation law axes, evidence status, and boundary"
    );
    assert!(
        json["pathSignatureTrajectoryReadings"]
            .as_array()
            .expect("path signature trajectory readings are array")
            .iter()
            .all(|reading| {
                reading["endpointSignatureDelta"].as_array().is_some()
                    && reading["maxAxisExcursion"].as_array().is_some()
                    && reading["nonMonotoneAxisRefs"].as_array().is_some()
                    && reading["pathCostProxy"].as_str().is_some()
                    && reading["trajectoryCoverageBoundary"].as_str().is_some()
            }),
        "path signature trajectory readings must carry endpoint, excursion, non-monotone, cost, and boundary data"
    );
    assert!(
        json["homotopyOrderSensitivityReadings"]
            .as_array()
            .expect("homotopy order sensitivity readings are array")
            .iter()
            .all(|reading| {
                reading["operationOrderSensitivity"].as_str().is_some()
                    && reading["homotopyBlockerRefs"].as_array().is_some()
                    && reading["selectedObservationPreservationStatus"]
                        .as_str()
                        .is_some()
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "homotopy / operation-order readings must carry sensitivity, blockers, preservation status, and boundary"
    );
    assert!(
        json["diagramFillabilityReadings"]
            .as_array()
            .expect("diagram fillability readings are array")
            .iter()
            .all(|reading| {
                reading["diagramFamily"].as_str().is_some()
                    && reading["missingFillerKind"].as_str().is_some()
                    && reading["fillerCandidateRefs"].as_array().is_some()
                    && reading["nonFillabilityWitnessRefs"].as_array().is_some()
                    && reading["fillingBlockerRefs"].as_array().is_some()
                    && reading["featureExtensionRefs"].as_array().is_some()
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "diagram fillability readings must carry filler, witness, blocker, feature-extension, and boundary data"
    );
    assert!(
        json["observationProjectionFidelityReadings"]
            .as_array()
            .expect("observation projection fidelity readings are array")
            .iter()
            .all(|reading| {
                reading["sourceProjectionRef"].as_str().is_some()
                    && reading["fidelityStatus"].as_str().is_some()
                    && reading["forgottenCoordinateCount"].as_u64().is_some()
                    && reading["reconstructionBlockerRefs"].as_array().is_some()
                    && reading["reflectionStatus"].as_str().is_some()
                    && reading["measurementBoundary"].as_str().is_some()
            }),
        "observation projection fidelity readings must keep projection loss separate from zero/lawfulness"
    );
    assert!(
        json["axisForgettingRiskReadings"]
            .as_array()
            .expect("axis forgetting risk readings are array")
            .iter()
            .all(|reading| {
                reading["selectedSignatureAxisRefs"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && reading["blockedSignatureAxisRefs"].as_array().is_some()
                    && reading["zeroReflectionStatus"].as_str().is_some()
                    && reading["obstructionReflectionStatus"].as_str().is_some()
            }),
        "axis forgetting risk must connect projection loss to selected signature axes"
    );
    assert!(
        json["atomOriginClosureDebtReadings"]
            .as_array()
            .expect("Atom origin closure debt readings are array")
            .iter()
            .all(|reading| {
                reading["sourceBackedAtomCount"].as_u64().is_some()
                    && reading["derivedOrInferredAtomCount"].as_u64().is_some()
                    && reading["expectedMissingAtomCount"].as_u64().is_some()
                    && reading["closureStatus"].as_str().is_some()
                    && reading["weakensZeroOrRepairClaims"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
            }),
        "Atom origin closure debt readings must distinguish source-backed, inferred, and missing expected atoms"
    );
    assert!(
        json["effectRelationAlgebraReadings"]
            .as_array()
            .expect("effect relation algebra readings are array")
            .iter()
            .all(|reading| {
                reading["requiredEffectRelations"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && reading["relationInputs"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["relationEvaluations"]
                        .as_array()
                        .is_some_and(|items| {
                            let axes = items
                                .iter()
                                .filter_map(|item| item["lawAxis"].as_str())
                                .collect::<std::collections::BTreeSet<_>>();
                            axes.contains("orderingPreservation")
                                && axes.contains("replaySafety")
                                && axes.contains("idempotency")
                                && axes.contains("compensationAvailability")
                                && axes.contains("authorityRequirement")
                                && items.iter().all(|item| {
                                    item["status"].as_str().is_some_and(|status| {
                                        matches!(
                                            status,
                                            "observed" | "blocked" | "unmeasured" | "notApplicable"
                                        )
                                    }) && item["requiredInputRefs"].as_array().is_some()
                                })
                        })
                    && reading["relationEvaluatorStatus"].as_str().is_some()
                    && reading["effectOrderingPressure"].as_str().is_some()
                    && reading["stateTransitionRef"].as_str().is_some()
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "effect relation algebra readings must be separate from state transition pressure"
    );
    assert!(
        json["synthesisBlockageReadings"]
            .as_array()
            .expect("synthesis blockage readings are array")
            .iter()
            .all(|reading| {
                reading["targetConstructionRefs"].as_array().is_some()
                    && reading["constraintRefs"].as_array().is_some()
                    && reading["missingEvidenceRefs"].as_array().is_some()
                    && reading["blockageStatus"].as_str().is_some()
                    && reading["noSolutionCertificateStatus"].as_str().is_some()
                    && reading["synthesisBoundary"].as_str().is_some()
            }),
        "synthesis blockage readings must distinguish candidate absence from no-solution certification"
    );
    assert!(
        json["operationPreconditionReadinessReadings"]
            .as_array()
            .expect("operation precondition readiness readings are array")
            .iter()
            .all(|reading| {
                reading["operationRef"].as_str().is_some()
                    && reading["readinessStatus"].as_str().is_some()
                    && reading["preconditionRefs"].as_array().is_some()
                    && reading["missingPreconditionRefs"].as_array().is_some()
                    && reading["candidateBoundary"].as_str().is_some()
            }),
        "operation precondition readiness readings must keep repair candidates bounded by precondition evidence"
    );
    assert!(
        json["pathMultiplicityLossReadings"]
            .as_array()
            .expect("path multiplicity loss readings are array")
            .iter()
            .all(|reading| {
                reading["observedPathCount"].as_u64().is_some()
                    && reading["alternatePathPressure"].as_u64().is_some()
                    && reading["reachabilityForgottenRefs"].as_array().is_some()
                    && reading["multiplicityLossStatus"].as_str().is_some()
                    && reading["homotopyBoundary"].as_str().is_some()
            }),
        "path multiplicity loss readings must expose reachability and homotopy review pressure"
    );
    assert!(
        json["representationStrengthReadings"]
            .as_array()
            .expect("representation strength readings are array")
            .iter()
            .all(|reading| {
                reading["sourceReadingRef"].as_str().is_some()
                    && reading["representationFamily"].as_str().is_some()
                    && reading["zeroPreserving"].as_str().is_some()
                    && reading["zeroReflecting"].as_str().is_some()
                    && reading["obstructionPreserving"].as_str().is_some()
                    && reading["obstructionReflecting"].as_str().is_some()
                    && reading["blockedReflectionOrPreservationReasons"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["requiredAssumptions"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "representation strength readings must carry strength classes and assumptions"
    );
    assert!(
        json["threeLayerFlatnessReadings"]
            .as_array()
            .expect("three-layer flatness readings are array")
            .iter()
            .all(|reading| {
                reading["staticStatus"].as_str().is_some()
                    && reading["runtimeStatus"].as_str().is_some()
                    && reading["semanticStatus"].as_str().is_some()
                    && reading["nonImplicationReading"].as_str().is_some()
                    && reading["recommendedNextAction"].as_str().is_some()
            }),
        "three-layer flatness readings must carry static/runtime/semantic statuses"
    );
    assert!(
        json["observationProjectionReadings"]
            .as_array()
            .expect("observation projection readings are array")
            .iter()
            .all(|reading| {
                reading["observedAtomFamilies"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && reading["coarseProjectionRisks"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["sourceCoordinates"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["observedCoordinates"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["forgottenCoordinateEvidence"].as_array().is_some()
                    && reading["nonInjectivityCandidates"].as_array().is_some()
                    && reading["reconstructionBlockerEvidence"]
                        .as_array()
                        .is_some()
                    && reading["reconstructionRisk"].as_str().is_some()
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "observation projection readings must carry canonical coordinates, typed blockers, and projection risks"
    );
    assert!(
        json["stateTransitionAlgebraReadings"]
            .as_array()
            .expect("state transition algebra readings are array")
            .iter()
            .all(|reading| {
                reading["requiredRelations"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && reading["transitionRelationInputs"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["lawEvaluations"].as_array().is_some_and(|items| {
                        let axes = items
                            .iter()
                            .filter_map(|item| item["lawAxis"].as_str())
                            .collect::<std::collections::BTreeSet<_>>();
                        axes.contains("stateTransitionRelation")
                            && axes.contains("commutativity")
                            && axes.contains("idempotency")
                            && axes.contains("replaySafety")
                            && axes.contains("orderingPreservation")
                            && axes.contains("invariantPreservation")
                            && items.iter().all(|item| {
                                item["status"].as_str().is_some_and(|status| {
                                    matches!(
                                        status,
                                        "observed" | "blocked" | "unmeasured" | "notApplicable"
                                    )
                                }) && item["requiredInputRefs"].as_array().is_some()
                            })
                    })
                    && reading["lawEvaluatorStatus"].as_str().is_some()
                    && reading["reading"].as_str().is_some()
                    && reading["recommendedNextAction"].as_str().is_some()
            }),
        "state transition algebra readings must carry required transition relations"
    );
    assert!(
        json["splitReadinessReadings"]
            .as_array()
            .expect("split readiness readings are array")
            .iter()
            .all(|reading| {
                reading["moleculeRef"].as_str().is_some()
                    && reading["status"].as_str().is_some()
                    && reading["readinessScore"].as_i64().is_some()
                    && reading["recommendedBoundaryOperation"].as_str().is_some()
            }),
        "split readiness readings must carry molecule refs, score, and boundary operation"
    );
    assert!(
        json["structuralReadingReviewSurface"]["connectedReadingRefs"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && json["structuralReadingReviewSurface"]["reviewFocus"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && json["structuralReadingReviewSurface"]["currentStateReading"]
                .as_str()
                .is_some_and(|reading| reading.contains("current architecture state")),
        "structural reading review surface must connect AAT readings as current architecture state"
    );
    assert!(
        json["currentStateEvolutionBoundary"]["handoffArtifactRef"] == "archsig-analysis-packet-v0"
            && json["currentStateEvolutionBoundary"]["archsigCurrentStateScope"]
                .as_str()
                .is_some_and(|scope| scope.contains("current AAT structural state"))
            && json["currentStateEvolutionBoundary"]["fieldsigEvolutionScope"]
                .as_str()
                .is_some_and(|scope| scope.contains("PR, diff, change-vector"))
            && json["currentStateEvolutionBoundary"]["forbiddenReadings"]
                .as_array()
                .is_some_and(|items| items.len() >= 3),
        "current-state/evolution boundary must separate ArchSig and FieldSig responsibilities"
    );
    assert!(
        json["archMapStoreRefs"]["deltaRef"]["artifactKind"] == "archmap-delta"
            && json["archMapStoreRefs"]["commitRef"]["artifactKind"] == "archmap-commit"
            && json["archMapStoreRefs"]["snapshotRef"]["artifactKind"] == "archmap-snapshot"
            && json["archMapStoreRefs"]["indexRef"]["artifactKind"] == "archmap-index"
            && json["archMapStoreRefs"]["rawDiffBoundary"]
                .as_str()
                .is_some_and(|boundary| boundary.contains("not ArchSig semantic inputs")),
        "ArchMapStore refs must expose delta / commit / snapshot / index and raw-diff exclusion boundary"
    );
    for family in ["monodromyReadingFamily", "boundaryHolonomyReadingFamily"] {
        let family_status = json[family]["status"].as_str();
        let measured_axis_count = json[family]["measuredAxisCount"].as_u64();
        let coverage_blocker_count = json[family]["coverageBlockerCount"].as_u64();
        assert!(
            json[family]["archMapStoreRefSetRef"] == json["archMapStoreRefs"]["refSetId"]
                && json[family]["selectedAxisRefs"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && json[family]["distanceKind"].as_str().is_some()
                && json[family]["weightPolicy"].as_str().is_some()
                && json[family]["coveragePolicy"].as_str().is_some()
                && family_status.is_some_and(|status| status != "schemaFoundationOnly")
                && measured_axis_count.is_some()
                && json[family]["unmeasuredAxisCount"].as_u64().is_some()
                && json[family]["positiveWitnessCount"].as_u64().is_some()
                && coverage_blocker_count.is_some()
                && (measured_axis_count.is_some_and(|count| count > 0)
                    || (family_status == Some("blockedByCoverageGap")
                        && coverage_blocker_count.is_some_and(|count| count > 0)))
                && json[family]["evidenceBoundary"].as_str().is_some(),
            "{family} must connect to ArchMapStore refs and carry evidence-derived status counts"
        );
    }
    assert!(
        json["operationSquareCandidates"]
            .as_array()
            .is_some_and(|items| {
                !items.is_empty()
                    && items.iter().all(|candidate| {
                        candidate["candidateSource"].as_str().is_some_and(|source| {
                            source == "inferred" || source == "supplied" || source == "blocked"
                        }) && candidate["candidateBasisRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                            && candidate["pPathRef"].as_str().is_some_and(|path| {
                                candidate["candidateSource"] == "blocked" || path.contains(" . ")
                            })
                            && candidate["qPathRef"].as_str().is_some_and(|path| {
                                candidate["candidateSource"] == "blocked" || path.contains(" . ")
                            })
                            && candidate["missingRefs"].as_array().is_some()
                            && (candidate["candidateSource"] != "inferred"
                                || candidate["evidenceBoundary"]
                                    .as_str()
                                    .is_some_and(|boundary| boundary.contains("reviewCueOnly")))
                            && (candidate["candidateSource"] != "supplied"
                                || candidate["suppliedPairRef"].as_str().is_some())
                    })
            }),
        "operation square candidates must distinguish supplied/inferred/blocked path pairs and preserve source-backed basis refs"
    );
    assert!(
        json["pathContinuationTraces"]
            .as_array()
            .is_some_and(|items| {
                let all_candidates_blocked = json["operationSquareCandidates"]
                    .as_array()
                    .is_some_and(|candidates| {
                        !candidates.is_empty()
                            && candidates.iter().all(|candidate| {
                                candidate["candidateSource"].as_str() == Some("blocked")
                            })
                    });
                (all_candidates_blocked || !items.is_empty())
                    && items.iter().all(|trace| {
                        trace["axisTraces"].as_array().is_some_and(|axes| {
                            let families = axes
                                .iter()
                                .filter_map(|axis| axis["axisFamily"].as_str())
                                .collect::<std::collections::BTreeSet<_>>();
                            [
                                "static",
                                "contract",
                                "semantic",
                                "state",
                                "effect",
                                "authority",
                                "runtime",
                                "projection",
                            ]
                            .iter()
                            .all(|family| families.contains(family))
                                && axes.iter().all(|axis| {
                                    axis["traceStatus"].as_str() != Some("unmeasured")
                                        || axis["missingRefs"]
                                            .as_array()
                                            .is_some_and(|refs| !refs.is_empty())
                                })
                        })
                    })
            }),
        "path continuation traces must expose required axis families and keep unmeasured axes as missing evidence"
    );
    assert!(
        json["axisWiseMonodromyDefects"]
            .as_array()
            .is_some_and(|items| {
                let all_candidates_blocked = json["operationSquareCandidates"]
                    .as_array()
                    .is_some_and(|candidates| {
                        !candidates.is_empty()
                            && candidates.iter().all(|candidate| {
                                candidate["candidateSource"].as_str() == Some("blocked")
                            })
                    });
                (all_candidates_blocked || !items.is_empty())
                    && items.iter().all(|defect| {
                        defect["distanceKind"].as_str().is_some()
                            && defect["measuredSupportRefs"].as_array().is_some()
                            && defect["witnessRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && defect["coverageBoundary"].as_str().is_some()
                            && defect["cancellationBoundary"].as_str().is_some()
                            && (defect["measurementStatus"].as_str() != Some("unmeasured")
                                || defect["missingRefs"]
                                    .as_array()
                                    .is_some_and(|refs| !refs.is_empty()))
                    })
            }),
        "axis-wise defects must carry distance kind, support, witnesses, coverage, and unmeasured boundaries"
    );
    assert!(
        json["amiAggregateReadings"]
            .as_array()
            .is_some_and(|items| {
                let all_candidates_blocked = json["operationSquareCandidates"]
                    .as_array()
                    .is_some_and(|candidates| {
                        !candidates.is_empty()
                            && candidates.iter().all(|candidate| {
                                candidate["candidateSource"].as_str() == Some("blocked")
                            })
                    });
                !items.is_empty()
                    && items.iter().all(|aggregate| {
                        aggregate["selectedSquareFamily"].as_str().is_some()
                            && (all_candidates_blocked
                                || aggregate["selectedAxisFamily"]
                                    .as_array()
                                    .is_some_and(|axes| !axes.is_empty()))
                            && aggregate["weightPolicy"].as_str().is_some()
                            && (all_candidates_blocked
                                || aggregate["topContributors"]
                                    .as_array()
                                    .is_some_and(|contributors| !contributors.is_empty()))
                            && aggregate["zeroReflectionAssumptions"]
                                .as_array()
                                .is_some_and(|assumptions| !assumptions.is_empty())
                            && aggregate["aggregateToLocalReadingBoundary"]
                                .as_str()
                                .is_some_and(|boundary| boundary.contains("local"))
                    })
            }),
        "AMI aggregate readings must remain bounded review aggregates with local-reading boundaries"
    );
    assert!(
        json["nonzeroMonodromyWitnesses"]
            .as_array()
            .is_some_and(|items| {
                let all_candidates_blocked = json["operationSquareCandidates"]
                    .as_array()
                    .is_some_and(|candidates| {
                        !candidates.is_empty()
                            && candidates.iter().all(|candidate| {
                                candidate["candidateSource"].as_str() == Some("blocked")
                            })
                    });
                (all_candidates_blocked || !items.is_empty())
                    && items.iter().all(|witness| {
                        witness["operationPair"]
                            .as_array()
                            .is_some_and(|pair| pair.len() == 2)
                            && witness["pathPair"]
                                .as_array()
                                .is_some_and(|pair| pair.len() == 2)
                            && witness["defectValue"]
                                .as_i64()
                                .is_some_and(|value| value > 0)
                            && witness["affectedAtomRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && witness["lawRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && witness["signatureAxisRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && witness["recommendedReviewFocus"]
                                .as_array()
                                .is_some_and(|focus| !focus.is_empty())
                            && witness["nonConclusions"]
                                .as_array()
                                .is_some_and(|items| !items.is_empty())
                    })
            }),
        "nonzero monodromy witnesses must expose operation/path pairs, positive defect value, traceable refs, review focus, and non-conclusions"
    );
    assert!(
        json["featureBoundaryResidualReadings"]
            .as_array()
            .is_some_and(|items| {
                !items.is_empty()
                    && items.iter().all(|reading| {
                        reading["mixedSubconfigurationRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                            && reading["boundarySupportRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && reading["holonomyAxes"].as_array().is_some_and(|axes| {
                                axes.len() == 8
                                    && axes.iter().all(|axis| {
                                        axis["holonomyAxisRef"]
                                            .as_str()
                                            .is_some_and(|axis_ref| axis_ref.starts_with("Hol_"))
                                            && axis["supportRefs"]
                                                .as_array()
                                                .is_some_and(|refs| !refs.is_empty())
                                    })
                            })
                            && reading["coverageAssumptions"]
                                .as_array()
                                .is_some_and(|items| !items.is_empty())
                            && reading["exactnessAssumptions"]
                                .as_array()
                                .is_some_and(|items| !items.is_empty())
                            && reading["nonConclusions"]
                                .as_array()
                                .is_some_and(|items| !items.is_empty())
                    })
            }),
        "feature boundary residual readings must expose mixed support, Hol_* axes, assumptions, and non-conclusions"
    );
    assert!(
        json["featureExtensionDiagnosisReadings"]
            .as_array()
            .is_some_and(|items| {
                !items.is_empty()
                    && items.iter().all(|reading| {
                        reading["classificationSummary"]
                            .as_array()
                            .is_some_and(|summary| summary.len() == 7)
                            && reading["attributionRecords"]
                                .as_array()
                                .is_some_and(|records| {
                                    !records.is_empty()
                                        && records.iter().any(|record| {
                                            record["labels"]
                                                .as_array()
                                                .is_some_and(|labels| labels.len() > 1)
                                        })
                                        && records.iter().all(|record| {
                                            record["observationRefs"]
                                                .as_array()
                                                .is_some_and(|refs| !refs.is_empty())
                                                || record["sourceRefs"]
                                                    .as_array()
                                                    .is_some_and(|refs| !refs.is_empty())
                                        })
                                })
                            && reading["residualCoverageGapRefs"].as_array().is_some()
                            && reading["liftingFailureRefs"].as_array().is_some()
                            && reading["fillingFailureRefs"].as_array().is_some()
                            && reading["complexityTransferRefs"].as_array().is_some()
                            && reading["classificationBoundary"]
                                .as_str()
                                .is_some_and(|boundary| boundary.contains("non-disjoint"))
                            && reading["fieldsigBoundary"]
                                .as_str()
                                .is_some_and(|boundary| boundary.contains("FieldSig"))
                            && reading["nonConclusions"]
                                .as_array()
                                .is_some_and(|items| !items.is_empty())
                    })
            }),
        "feature extension diagnosis readings must expose seven non-disjoint labels, witness-backed attribution refs, separated failure refs, and FieldSig boundary"
    );
    assert!(
        {
            let all_candidates_blocked =
                json["operationSquareCandidates"]
                    .as_array()
                    .is_some_and(|candidates| {
                        !candidates.is_empty()
                            && candidates.iter().all(|candidate| {
                                candidate["candidateSource"].as_str() == Some("blocked")
                            })
                    });
            json["llmInterpretationPacket"]["structuralReadingReviewSummary"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
                && json["llmInterpretationPacket"]["currentStateEvolutionBoundarySummary"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && json["llmInterpretationPacket"]["measurementExpansionSummary"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && (all_candidates_blocked
                    || json["llmInterpretationPacket"]["nonzeroMonodromyWitnessSummary"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty()))
                && json["llmInterpretationPacket"]["featureBoundaryResidualSummary"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && json["llmInterpretationPacket"]["featureExtensionDiagnosisSummary"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && json["llmInterpretationPacket"]["atomSupportAxisSummary"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && json["llmInterpretationPacket"]["lawUniverseCoverageSummary"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
        },
        "LLM interpretation packet must summarize structural readings, measurement expansion, and current-state/evolution boundary"
    );
    assert!(
        json["llmInterpretationPacket"]["recommendedHumanReviewFocus"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "LLM interpretation packet must provide review focus"
    );
}

fn collect_files(root: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(path) = stack.pop() {
        for entry in fs::read_dir(&path).expect("directory can be read") {
            let entry = entry.expect("directory entry can be read");
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else {
                files.push(path);
            }
        }
    }
    files
}
