use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

fn temp_dir(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time after epoch")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("archsig-archview-{name}-{nanos}"));
    fs::create_dir_all(&path).expect("temporary directory can be created");
    path
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("json artifact can be read"))
        .expect("json artifact parses")
}

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/ag_measurement")
}

fn measurement_profile_for(root: &Path, law_policy: &str) -> PathBuf {
    let suffix = law_policy
        .strip_prefix("law_policy_")
        .expect("law policy uses current fixture naming");
    root.join(format!("measurement_profile_{suffix}"))
}

fn value_at<'a>(value: &'a Value, path: &[&str]) -> &'a Value {
    path.iter().fold(value, |current, key| &current[*key])
}

#[test]
fn archview_projection_e2e_matches_analyze_geometry_for_golden_cases() {
    let root = fixture_root();
    let manifest = read_json(&root.join("archsig_viewer_gluing_geometry_golden_ux.json"));
    assert_eq!(
        manifest["schema"],
        "archsig-viewer-gluing-geometry-golden-ux/v0.5.3"
    );
    assert_eq!(manifest["cases"].as_array().map(Vec::len), Some(5));

    for case in manifest["cases"]
        .as_array()
        .expect("golden cases are array")
    {
        let case_id = case["caseId"].as_str().expect("case id is string");
        let out_dir = temp_dir(case_id);
        let archmap_name = case["archmap"].as_str().expect("archmap is string");
        let archmap_path = if let Some(mutations) = case["mutations"].as_array() {
            let mut archmap = read_json(&root.join(archmap_name));
            for mutation in mutations {
                let atom_id = mutation["atomId"]
                    .as_str()
                    .expect("mutation atom id is string");
                let field = mutation["field"]
                    .as_str()
                    .expect("mutation field is string");
                let atom = archmap["atoms"]
                    .as_array_mut()
                    .expect("atoms are array")
                    .iter_mut()
                    .find(|atom| atom["id"] == atom_id)
                    .unwrap_or_else(|| panic!("{case_id} mutation atom is missing: {atom_id}"));
                atom[field] = mutation["value"].clone();
            }
            let path = out_dir.join(format!("{case_id}.archmap.json"));
            fs::write(
                &path,
                serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
            )
            .expect("mutated archmap writes");
            path
        } else {
            root.join(archmap_name)
        };
        let law_policy = case["lawPolicy"].as_str().expect("law policy is string");
        let measurement_profile = measurement_profile_for(&root, law_policy);
        let law_surface = if archmap_name.contains("cech_h1_visible") {
            "law_surface_cech_h1_v052.json"
        } else {
            "law_surface_ag_v052.json"
        };
        let law_surface_path = root.join(law_surface);
        let law_policy_path = if law_surface == "law_surface_cech_h1_v052.json" {
            let mut policy = read_json(&root.join(law_policy));
            policy["lawSurfaceRef"] = read_json(&law_surface_path)["id"].clone();
            let path = out_dir.join("law_policy.json");
            fs::write(
                &path,
                serde_json::to_vec_pretty(&policy).expect("law policy serializes"),
            )
            .expect("law policy writes");
            path
        } else {
            root.join(law_policy)
        };
        let args = vec![
            "analyze".to_string(),
            "--archmap".to_string(),
            archmap_path
                .to_str()
                .expect("archmap path is utf-8")
                .to_string(),
            "--law-policy".to_string(),
            law_policy_path
                .to_str()
                .expect("law policy path is utf-8")
                .to_string(),
            "--measurement-profile".to_string(),
            measurement_profile
                .to_str()
                .expect("measurement profile path is utf-8")
                .to_string(),
            "--law-surface".to_string(),
            law_surface_path
                .to_str()
                .expect("law surface path is utf-8")
                .to_string(),
            "--out-dir".to_string(),
            out_dir.to_str().expect("output path is utf-8").to_string(),
        ];
        let arg_refs = args.iter().map(String::as_str).collect::<Vec<_>>();
        let output = Command::new(env!("CARGO_BIN_EXE_archsig"))
            .args(&arg_refs)
            .output()
            .expect("archsig analyze runs");
        assert!(
            output.status.success(),
            "{case_id} analyze failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        let report = read_json(&out_dir.join("archsig-insight-report.json"));
        let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
        let gluing = &report["gluingGeometry"];
        assert_eq!(gluing["schema"], "archsig-viewer-gluing-geometry/v0.5.3");
        assert_eq!(viewer["aatGeometryOverlays"]["gluingGeometry"], *gluing);
        assert!(viewer["aatGeometryOverlays"]["omittedGeometryCounts"].is_object());

        let expected = &case["expected"];
        for (key, path) in [
            ("minNerveVertices", vec!["nerve", "vertices"]),
            ("minNerveEdges", vec!["nerve", "edges"]),
            ("minNerveTriangles", vec!["nerve", "triangles"]),
            (
                "minCocycleSupportEdges",
                vec!["cocycleRibbon", "supportEdges"],
            ),
            ("minForbiddenCages", vec!["forbiddenCages"]),
            ("minRepairMorphs", vec!["repairMorphs"]),
            ("minCurvatureFieldRows", vec!["locusField", "fieldRows"]),
            ("minBlockedRegions", vec!["locusField", "blockedRegions"]),
        ] {
            if let Some(minimum) = expected[key].as_u64() {
                assert!(
                    value_at(gluing, &path)
                        .as_array()
                        .is_some_and(|items| items.len() >= minimum as usize),
                    "{case_id} {key} does not meet expected projection count"
                );
            }
        }
        if let Some(maximum) = expected["maxCocycleSupportEdges"].as_u64() {
            assert!(
                gluing["cocycleRibbon"]["supportEdges"]
                    .as_array()
                    .is_some_and(|items| items.len() <= maximum as usize)
            );
            assert_eq!(gluing["renderLimits"]["cocycleSupportEdges"], maximum);
            assert!(gluing["omittedGeometryCounts"]["cocycleSupportEdges"].is_u64());
        }
        if let Some(expected_h2) = expected["h2CoherenceVisualized"].as_bool() {
            assert_eq!(gluing["nerve"]["h2CoherenceVisualized"], expected_h2);
        }
        if let Some(minimum) = expected["minRepairFromCageRefs"].as_u64() {
            assert!(gluing["repairMorphs"].as_array().is_some_and(|items| {
                items.iter().any(|item| {
                    item["fromCageRefs"]
                        .as_array()
                        .is_some_and(|refs| refs.len() >= minimum as usize)
                        && item["fromAtomRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
            }));
        }
        if let Some(minimum) = expected["minAnalyticMassRows"].as_u64() {
            assert!(
                gluing["locusField"]["fieldRows"]
                    .as_array()
                    .is_some_and(|items| {
                        items
                            .iter()
                            .filter(|item| {
                                item["harmonicMass"].is_number()
                                    && item["sourceReadingRef"].is_string()
                            })
                            .count()
                            >= minimum as usize
                    })
            );
        }
        if let Some(minimum) = expected["minBlockedAnchorGlyphs"].as_u64() {
            assert!(gluing["atomGlyphs"].as_array().is_some_and(|items| {
                items
                    .iter()
                    .filter(|item| {
                        item["semanticAnchor"] == "blocked_missing_anchor"
                            && item["shapeRole"] == "blocked_anchor_glyph"
                            && item["fiberShapeRole"].is_string()
                            && item["carrierColorRole"].is_string()
                    })
                    .count()
                    >= minimum as usize
            }));
        }
        if let Some(visible) = expected["closureGapVisible"].as_bool() {
            assert_eq!(
                gluing["cocycleRibbon"]["closureGapEncoding"]["visible"],
                visible
            );
        }
        if let Some(minimum) = expected["minNerveTriangles"].as_u64() {
            if minimum > 0 {
                assert!(
                    gluing["nerve"]["triangleSource"]
                        .as_str()
                        .is_some_and(|text| { text.contains("not inferred by the viewer") })
                );
            }
        }
        let report_text = serde_json::to_string(&report).expect("report serializes");
        for required in expected["requiredNonClaims"]
            .as_array()
            .into_iter()
            .flatten()
        {
            let required = required.as_str().expect("non-claim is string");
            assert!(
                report_text.contains(required),
                "{case_id} non-claim is missing: {required}"
            );
        }
        for scene_id in expected["requiredScenes"].as_array().into_iter().flatten() {
            let scene_id = scene_id.as_str().expect("scene id is string");
            let scene = viewer["viewerVisualScenes"]
                .as_array()
                .expect("viewer scenes are array")
                .iter()
                .find(|scene| scene["sceneId"] == scene_id)
                .unwrap_or_else(|| panic!("{case_id} scene is missing: {scene_id}"));
            assert_eq!(scene["axisMappingImplemented"], true);
        }
    }
}

#[test]
fn archview_saga_projection_e2e_is_packet_grounded() {
    let root = fixture_root();
    let out_dir = temp_dir("saga-projection");
    let mut law_policy = read_json(&root.join("law_policy_ag.json"));
    law_policy["policies"] = serde_json::json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let law_policy_path = out_dir.join("law_policy_saga_descent.json");
    fs::write(
        &law_policy_path,
        serde_json::to_vec_pretty(&law_policy).expect("law policy serializes"),
    )
    .expect("law policy writes");
    let archmap_path = root.join("archmap_v2.json");
    let law_surface_path = out_dir.join("law_surface.json");
    let mut law_surface = read_json(&root.join("law_surface_ag_v052.json"));
    law_surface["laws"]
        .as_array_mut()
        .expect("law surface laws")
        .push(serde_json::json!({
            "lawId": "ag.saga-descent",
            "conditionType": "descent",
            "evaluatorRef": "ag.saga-descent"
        }));
    fs::write(
        &law_surface_path,
        serde_json::to_vec_pretty(&law_surface).expect("law surface serializes"),
    )
    .expect("law surface writes");
    let measurement_profile = measurement_profile_for(&root, "law_policy_ag.json");
    let args = vec![
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("archmap path"),
        "--law-policy",
        law_policy_path.to_str().expect("law policy path"),
        "--measurement-profile",
        measurement_profile
            .to_str()
            .expect("measurement profile path"),
        "--law-surface",
        law_surface_path.to_str().expect("law surface path"),
        "--out-dir",
        out_dir.to_str().expect("output path"),
    ];
    let output = Command::new(env!("CARGO_BIN_EXE_archsig"))
        .args(args)
        .output()
        .expect("archsig analyze runs");
    assert!(
        output.status.success(),
        "SAGA analyze failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    assert_eq!(viewer["schema"], "archsig-atom-viewer-data/v0.5.3");
    let viewer_packet_digest = viewer["inputDigests"]["measurementPacket"]["sha256"]
        .as_str()
        .expect("viewer packet digest");
    assert_eq!(
        viewer["sagaDescent"]["sourcePacketRef"],
        "archsig-measurement-packet.json"
    );
    let stages = viewer["sagaDescent"]["stages"]
        .as_array()
        .expect("SAGA stages");
    assert_eq!(stages.len(), 4);
    assert_eq!(
        stages
            .iter()
            .map(|stage| stage["stageId"].as_str().expect("stage id"))
            .collect::<Vec<_>>(),
        vec!["grounding", "descent", "comparison", "silence"]
    );
    assert_eq!(stages[3]["status"], "silence_by_design");
    assert!(
        viewer["sagaDescent"]["leafFieldMap"]
            .as_array()
            .is_some_and(|mapping| !mapping.is_empty())
    );
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .is_some_and(|rows| { rows.iter().any(|row| row["kind"] == "silence_by_design") })
    );

    let gate_path = out_dir.join("archsig-gate-report.json");
    let packet_path = out_dir.join("archsig-measurement-packet.json");
    let gate_policy_path = root.join("gate_policy_conservative.json");
    let gate_output = Command::new(env!("CARGO_BIN_EXE_archsig"))
        .args([
            "gate",
            "--packet",
            packet_path.to_str().expect("packet path"),
            "--policy",
            gate_policy_path.to_str().expect("gate policy path"),
            "--out",
            gate_path.to_str().expect("gate output path"),
        ])
        .output()
        .expect("archsig gate runs");
    assert!(
        matches!(gate_output.status.code(), Some(0 | 1)),
        "gate command failed unexpectedly\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&gate_output.stdout),
        String::from_utf8_lossy(&gate_output.stderr)
    );
    let gate = read_json(&gate_path);
    assert_eq!(gate["schema"], "archsig-gate-report/v0.5.3");
    assert_eq!(
        gate["inputDigests"]["measurementPacket"]["sha256"],
        viewer_packet_digest
    );
    assert!(gate["ruleOutcomes"].as_array().is_some_and(|outcomes| {
        !outcomes.is_empty()
            && outcomes.iter().all(|outcome| {
                if outcome["status"] == "not_applicable" {
                    true
                } else {
                    outcome["appliedMapping"].as_array().is_some_and(|rows| {
                        rows.iter().all(|row| {
                            let action_valid = matches!(
                                row["action"].as_str(),
                                Some("pass") | Some("pass_with_boundary") | Some("block")
                            );
                            let ref_valid = if row["rowRef"].is_string() {
                                row["boundaryOverrideApplied"].is_boolean()
                            } else {
                                row["rowKey"].is_string()
                            };
                            action_valid && ref_valid
                        })
                    })
                }
            })
    }));
}
