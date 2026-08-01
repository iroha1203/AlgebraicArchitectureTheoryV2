fn remove_analyze_success_artifacts(out_dir: &PathBuf) -> Result<(), Box<dyn Error>> {
    let mut artifacts = vec![
        "archsig-analysis-summary.json".to_string(),
        "archsig-atom-viewer-data.json".to_string(),
        "archsig-measurement-view-model.json".to_string(),
        "archsig-run-manifest.json".to_string(),
        "normalized-archmap.json".to_string(),
        "archsig-measurement-packet.json".to_string(),
        "archsig-insight-report.json".to_string(),
        "archsig-insight-brief.md".to_string(),
        "archsig-analysis-validation.json".to_string(),
        "law-surface-validation.json".to_string(),
    ];
    artifacts.extend([
        ["typed", "evaluator", "results.json"].join("-"),
        ["architecture", "distance.json"].join("-"),
        ["archsig", "analysis", "packet.json"].join("-"),
        ["archsig", "analysis", "detail", "index.json"].join("-"),
        ["llm", "interpretation", "packet.json"].join("-"),
    ]);
    for artifact in artifacts {
        let path = out_dir.join(artifact);
        match std::fs::remove_file(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(Box::new(error)),
        }
    }
    Ok(())
}

fn reject_analyze_output_overwrite(out_dir: &PathBuf) -> Result<(), Box<dyn Error>> {
    let existing = [
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-measurement-view-model.json",
        "archsig-run-manifest.json",
        "normalized-archmap.json",
        "archsig-measurement-packet.json",
        "archsig-insight-report.json",
        "archsig-insight-brief.md",
        "archsig-analysis-validation.json",
        "law-surface-validation.json",
    ]
    .into_iter()
    .filter(|artifact| out_dir.join(artifact).exists())
    .collect::<Vec<_>>();
    if existing.is_empty() {
        return Ok(());
    }
    Err(format!(
        "analyze output directory already contains current artifacts ({}); choose a fresh --out-dir",
        existing.join(", ")
    )
    .into())
}

fn reject_compare_output_alias(
    base_run: &PathBuf,
    head_run: &PathBuf,
    out_dir: &PathBuf,
) -> Result<(), Box<dyn Error>> {
    let base = std::fs::canonicalize(base_run)?;
    let head = std::fs::canonicalize(head_run)?;
    let output = resolve_path_with_existing_ancestor(out_dir)?;
    if output == base || output == head || output.starts_with(&base) || output.starts_with(&head) {
        return Err("compare output directory must be outside both input run directories".into());
    }
    Ok(())
}

fn reject_compare_output_overwrite(out_dir: &PathBuf) -> Result<(), Box<dyn Error>> {
    let existing = ["archmap-diff.json", "archsig-comparison-report.json"]
        .into_iter()
        .filter(|artifact| out_dir.join(artifact).exists())
        .collect::<Vec<_>>();
    if existing.is_empty() {
        return Ok(());
    }
    Err(format!(
        "compare output directory already contains current artifacts ({}); choose a fresh --out-dir",
        existing.join(", ")
    )
    .into())
}

fn build_validation_failure_insight_report(
    archmap_validation: &Value,
    law_policy_validation: &Value,
    law_surface_validation: Option<&Value>,
) -> Value {
    let failed_refs = validation_failure_refs(
        archmap_validation,
        law_policy_validation,
        law_surface_validation,
    );
    let primary_ref = failed_refs
        .first()
        .cloned()
        .unwrap_or_else(|| "validation:unknown-failure".to_string());
    serde_json::json!({
        "schema": "archsig-insight-report/v0.5.4",
        "reportId": "insight:validation-failure",
        "sourcePacketRef": null,
        "generatedAt": "deterministic-run-artifact",
        "outputArtifacts": {
            "summaryRef": null,
            "briefRef": "archsig-insight-brief.md",
            "viewerDataRef": "archsig-atom-viewer-data.json"
        },
        "headline": {
            "conclusionCode": ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT,
            "title": "Validation failed before measurement",
            "summary": "ArchSig stopped before normalization because an input validation check failed.",
            "decisionState": "blocked",
            "primaryVerdictRefs": [],
            "boundaryDigestRef": "boundary-digest:validation"
        },
        "readThisFirst": {
            "heading": "Read this first",
                "conclusion": ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT,
            "whatItMeans": "No measurement packet or AG invariant was computed. Fix the failing ArchMap, LawPolicy, or law-equation-surface validation first.",
            "whereToLookFirst": failed_refs,
            "nextAction": "Inspect failed validation checks",
            "boundary": "Pre-normalization validation failed; no structural verdict is available.",
            "details": {
                "validationRefs": failed_refs,
                "sourceRefs": [],
                "atomRefs": [],
                "contextRefs": []
            }
        },
        "insightCards": [{
            "id": "insight:validation-failure:001",
            "kind": "validation_failure",
            "severity": "blocking",
            "title": "Validation failed before measurement",
            "oneLine": "ArchSig stopped before normalization because input validation failed.",
            "whyItMatters": "The viewer and brief can identify the blocker, but they must not present measurement conclusions that were never computed.",
            "evidence": {
                "structuralVerdictRefs": [],
                "computedInvariantRefs": [],
                "analyticReadingRefs": [],
                "assumptionRefs": [],
                "sourceRefs": [],
                "atomRefs": [],
                "contextRefs": [],
                "coverRefs": [],
                "evaluatorRefs": [],
                "validationRefs": failed_refs,
                "evidenceResolutionStatus": "validation_failure_before_measurement"
            },
            "sampleRefs": {
                "atomRefs": [],
                "contextRefs": [],
                "sourceRefs": [],
                "note": "No normalized ArchMap projection exists after validation failure."
            },
            "nextAction": {
                "label": "Inspect failed validation checks",
                "kind": "validation_blocker",
                "targetRefs": [primary_ref]
            },
            "viewerNavigation": {
                "sceneId": "boundary-assumption",
                "highlightRefs": {
                    "atomRefs": [],
                    "contextRefs": [],
                    "sourceRefs": [],
                    "validationRefs": failed_refs
                }
            },
            "tourRefs": ["tour:validation-failure:001"],
            "rankingBasis": ["validation_failure"],
            "nonClaims": [
                "This is not a measured AG obstruction.",
                "No measurement packet, structural verdict, or analytic reading was computed."
            ]
        }],
        "actionQueue": [{
            "id": "action:validation:1",
            "kind": "validation_blocker",
            "title": "Inspect failed validation checks",
            "reason": "Input validation failed before ArchSig could normalize and measure.",
            "targetRefs": failed_refs,
            "expectedUserOutcome": "Fix the input contract before reading measurement claims.",
            "nonClaims": ["No AG measurement conclusion exists for this run."]
        }],
        "boundaryDigest": {
            "id": "boundary-digest:validation",
            "shortText": "Validation failed before normalization; measurement is not computed.",
            "checkedCount": 0,
            "assumedCount": 0,
            "violatedCount": 1,
            "unmeasuredCount": 0,
            "unknownCount": 0,
            "notComputedCount": 1,
            "blockingCount": 1,
            "blocking": failed_refs,
            "nonClaims": ["Validation failure does not imply measured nonzero or measured zero."]
        },
        "viewerVisualScenes": [validation_failure_scene(&failed_refs)],
        "guidedTours": [{
            "tourId": "tour:validation-failure:001",
            "title": "Validation failed before measurement",
            "insightRefs": ["insight:validation-failure:001"],
            "steps": [{
                "sceneId": "boundary-assumption",
                "caption": "This boundary explains why no measurement packet was produced.",
                "highlightRefs": {
                    "validationRefs": failed_refs
                }
            }]
        }],
        "copyBlocks": {
            "sourceRefs": [],
            "llmHandoff": {
                "instruction": "Use this as a validation blocker only. Do not infer measurement conclusions.",
                "boundary": "Validation failed before normalization.",
                "topInsights": ["ArchSig stopped before measurement because validation failed."]
            }
        },
        "rankingBasis": ["validation_failure"],
        "claimValidation": {
            "measuredClaimsRequireStructuralVerdictRefs": true,
            "analyticReadingsDoNotPromoteLawfulOrUnlawful": true,
            "validationFailureDoesNotCreateMeasurementClaim": true
        },
        "nonConclusions": [
            "Validation failure insight is a pre-normalization projection.",
            "No measurement packet claims are generated."
        ]
    })
}

fn build_validation_failure_viewer_data(insight_report: &Value) -> Value {
    serde_json::json!({
        "schema": "archsig-atom-viewer-data/v0.5.4",
        "sourceArtifactRefs": {
            "archmapValidation": "archmap-validation.json",
            "lawPolicyValidation": "law-policy-validation.json",
            "insightReport": "archsig-insight-report.json",
            "insightBrief": "archsig-insight-brief.md"
        },
        "decisionBar": {
            "conclusion": ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT,
            "validation": "see archmap-validation.json and law-policy-validation.json",
            "boundaryDigest": insight_report["boundaryDigest"]["shortText"],
            "artifactLinks": insight_report["outputArtifacts"]
        },
        "insightQueue": insight_report["insightCards"],
        "actionQueue": insight_report["actionQueue"],
        "viewerVisualScenes": insight_report["viewerVisualScenes"],
        "guidedTours": insight_report["guidedTours"],
        "copyBlocks": insight_report["copyBlocks"],
        "sagaDescent": {
            "projectionBoundary": "SAGA fields are unavailable because validation stopped before measurement.",
            "sourcePacketRef": "archsig-measurement-packet.json",
            "stages": [
                {"stageId": "grounding", "order": 0, "status": "not_computed", "rows": [], "measurements": [], "visualRole": "grounding"},
                {"stageId": "descent", "order": 1, "status": "not_computed", "rows": [], "measurements": [], "harmonicDebt": [], "visualRole": "descent-measurement"},
                {"stageId": "comparison", "order": 2, "status": "not_computed", "rows": [], "visualRole": "comparison-record"},
                {"stageId": "silence", "order": 3, "status": "not_computed", "rows": [], "visualRole": "silence"}
            ],
            "silenceRows": [],
            "leafFieldMap": [],
            "nonClaims": ["Validation stopped before a measurement packet could supply SAGA fields."]
        },
        "reportPane": {
            "readThisFirst": insight_report["readThisFirst"],
            "insightQueue": insight_report["insightCards"],
            "actionQueue": insight_report["actionQueue"],
            "evidenceDetailShape": ["What", "Why", "Measurement", "Boundary", "Next"],
            "boundaryDigest": insight_report["boundaryDigest"],
            "artifactLinks": insight_report["outputArtifacts"]
        },
        "finitePosetSite": {
            "atoms": [],
            "contexts": [],
            "covers": []
        },
        "largeGraphStrategy": {
            "mode": "validation_blocked",
            "thresholds": {
                "fullGeometryAtoms": 2_000,
                "instancedAtoms": 10_000,
                "clusterAtoms": 50_000
            },
            "topInsightEvidencePinning": {
                "policy": "preserve_for_top_insight",
                "preservedRefs": insight_report["readThisFirst"]["whereToLookFirst"],
                "aggregatedRefs": [],
                "omittedRefs": []
            }
        },
        "omittedDetailCounts": {
            "omittedAtoms": 0,
            "omittedEdges": 0,
            "omittedContextMemberships": 0,
            "omittedCoverOverlaps": 0,
            "omittedSceneLayerObjects": 0,
            "omittedLabels": 0,
            "omittedSourceRefs": 0,
            "omittedReasons": ["normalization did not run after validation failure"]
        },
        "nonConclusions": [
            "Validation failure viewer data is a diagnostic projection, not a measurement scene."
        ]
    })
}

fn validation_failure_refs(
    archmap_validation: &Value,
    law_policy_validation: &Value,
    law_surface_validation: Option<&Value>,
) -> Vec<String> {
    let mut refs = Vec::new();
    refs.extend(validation_report_failure_refs(
        "archmap-validation",
        archmap_validation,
    ));
    refs.extend(validation_report_failure_refs(
        "law-policy-validation",
        law_policy_validation,
    ));
    if let Some(law_surface_validation) = law_surface_validation {
        refs.extend(validation_report_failure_refs(
            "law-surface-validation",
            law_surface_validation,
        ));
    }
    if refs.is_empty() {
        refs.push("validation:failed".to_string());
    }
    refs
}

fn validation_report_failure_refs(prefix: &str, report: &Value) -> Vec<String> {
    report["checks"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|check| check["result"].as_str() == Some("fail"))
        .map(|check| {
            format!(
                "{}:{}",
                prefix,
                check["id"]
                    .as_str()
                    .or_else(|| check["checkId"].as_str())
                    .unwrap_or("failed-check")
            )
        })
        .collect()
}

fn validation_failure_scene(failed_refs: &[String]) -> Value {
    serde_json::json!({
        "sceneId": "boundary-assumption",
        "kind": "validation_boundary",
        "title": "Validation Boundary",
        "sceneStatus": "active",
        "userQuestion": "Why did ArchSig stop before measurement?",
        "axisMapping": {
            "x": "input contract",
            "y": "validation result",
            "z": "blocked measurement stage"
        },
        "primaryRefs": {
            "insightRefs": ["insight:validation-failure:001"],
            "validationRefs": failed_refs,
            "atomRefs": [],
            "contextRefs": [],
            "coverRefs": [],
            "sourceRefs": []
        },
        "layers": [{
            "layerId": "layer:boundary-assumption:validation-wall",
            "kind": "boundary_wall",
            "geometryRole": "wall",
            "encodingRef": "encoding:boundary-assumption:validation",
            "clickTargetKind": "validationBlocker",
            "refs": {
                "validationRefs": failed_refs
            },
            "omissionPolicy": "preserve_for_top_insight",
            "animationPurpose": "navigation"
        }],
        "visualEncodings": [{
            "encodingId": "encoding:boundary-assumption:validation",
            "colorRole": "not_computed",
            "shapeRole": "wall_fog",
            "lineRole": "broken_line",
            "textRole": "validation blocker before measurement"
        }],
        "boundaryDigestRef": "boundary-digest:validation"
    })
}
