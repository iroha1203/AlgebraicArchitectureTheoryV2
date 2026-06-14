use std::collections::BTreeSet;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use archsig::{ArchMapDocumentV2, compare_archmap_v2_doctrine};
use serde_json::{Value, json};

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal")
}

fn archmap_v1_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/archmap_v1")
}

fn practical_rust_service_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/practical-rust-service")
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

fn atom_generated_acceptance_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/atom_generated_acceptance")
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

fn negative_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/negative")
}

fn ag_measurement_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/ag_measurement")
}

#[test]
fn cli_validates_archmap_v2_finite_poset_site_contract() {
    let out_dir = temp_dir("archmap-v2-validation");
    let root = ag_measurement_root();
    let report = out_dir.join("archmap-validation.json");

    run_sig0(&[
        "archmap",
        "--input",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "archmap-validation-report-v2");
    assert_eq!(json["inputSchema"], "archmap/v2");
    assert_eq!(json["summary"]["result"], "pass");
    assert_eq!(json["summary"]["atomCount"], 3);
    assert_eq!(json["summary"]["contextCount"], 3);
    assert_eq!(json["summary"]["coverCount"], 1);
}

#[test]
fn cli_law_policy_ag_evaluator_requires_measurement_profile() {
    let out_dir = temp_dir("ag-policy-missing-profile");
    let root = ag_measurement_root();
    let report = out_dir.join("law-policy-validation.json");

    run_sig0_expect_code(
        &[
            "law-policy",
            "--input",
            root.join("law_policy_missing_profile.json")
                .to_str()
                .expect("path is utf-8"),
            "--out",
            report.to_str().expect("path is utf-8"),
        ],
        1,
    );

    let json = read_json(&report);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"].as_array().unwrap().iter().any(|check| {
            check["id"] == "law-policy-v1-ag-evaluator-profile-required"
                && check["result"] == "fail"
        }),
        "AG evaluator execution must fail closed without MeasurementProfile"
    );
}

#[test]
fn cli_analyze_v2_writes_measurement_packet_foundation() {
    let out_dir = temp_dir("ag-measurement-analyze");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let normalized = read_json(&out_dir.join("normalized-archmap.json"));
    assert_eq!(normalized["schema"], "normalized-archmap/v2");
    assert_eq!(
        normalized["summary"]["doctrineFingerprint"],
        "sha256:ag-fixture-doctrine"
    );

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["schema"], "archsig-measurement-packet/v1");
    assert!(packet["profile"].is_object());
    assert!(packet["structuralVerdict"].is_array());
    assert!(packet["computedInvariants"].is_array());
    assert!(packet["analyticReadings"].is_array());
    assert!(packet["assumptions"].is_array());
    assert!(packet["nonConclusions"].is_array());
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(cech["dimensions"]["H1"], Value::from(0));
    assert_eq!(cech["selectedH2"]["dimension"], Value::Null);
    assert_eq!(
        cech["selectedH2"]["status"],
        "not_measured_for_triple_overlap_faces"
    );
    assert_eq!(packet["analyticReadings"][0]["regime"], "theorem-candidate");

    let validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert_eq!(validation["summary"]["result"], "pass");

    let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    assert_eq!(viewer["schemaVersion"], "archsig-atom-viewer-data-v2");
    assert_eq!(
        viewer["sourceArtifactRefs"]["measurementPacket"],
        "archsig-measurement-packet.json"
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_cech_h1_visible_fixture_measures_nonzero() {
    let out_dir = temp_dir("ag-measurement-cech-h1-visible");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.cech-obstruction@1"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["nonZero"],
        true
    );
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(
        cech["claimScope"],
        "selected-cover 1-skeleton Cech cochain calculation"
    );
    assert_eq!(cech["observedCocycle"]["classNonzero"], true);
    assert_eq!(
        cech["observedCocycle"]["representative"]
            .as_array()
            .expect("representative is array")
            .len(),
        1
    );
    assert_eq!(
        cech["observedCocycle"]["mismatchSupportRefs"][0],
        "atom:left-bottom-cech-mismatch"
    );
    assert!(
        cech["coverNerveProjection"]["faces"]
            .as_array()
            .is_some_and(Vec::is_empty),
        "Cech H1 visible fixture has restriction chains but no measured triple-overlap 2-simplex"
    );
    assert_eq!(
        cech["selectedH2"]["status"],
        "computed_for_selected_1_skeleton"
    );
    let witness_counting = invariant_by_id(&packet, "witness-counting:profile:ag-default@1");
    assert_eq!(
        witness_counting["invariantId"],
        "witness-counting:profile:ag-default@1"
    );
    assert_eq!(witness_counting["verdict"], "measured_zero");

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_cover_nerve_faces_require_packet_triple_overlap_support() {
    let out_dir = temp_dir("ag-measurement-cech-triple-overlap");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(json!({
            "id": "atom:triple-overlap",
            "kind": "component",
            "subject": "src:triple-overlap",
            "axis": "static",
            "predicate": "tripleOverlapWitness",
            "refs": ["src:triple-overlap"]
        }));
    archmap["sources"]["src:triple-overlap"] = json!({
        "kind": "policy",
        "path": "docs/tool/archsig_viewer_gluing_geometry_prd.md",
        "section": "cover nerve triple-overlap fixture"
    });
    for context_id in ["ctx:top", "ctx:left", "ctx:bottom"] {
        let context = archmap["contexts"]
            .as_array_mut()
            .expect("contexts is array")
            .iter_mut()
            .find(|context| context["id"] == context_id)
            .unwrap_or_else(|| panic!("context {context_id} exists"));
        context["atoms"]
            .as_array_mut()
            .expect("context atoms is array")
            .push(Value::String("atom:triple-overlap".to_string()));
    }
    let archmap_path = out_dir.join("archmap_v2_cech_triple_overlap.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    let faces = cech["coverNerveProjection"]["faces"]
        .as_array()
        .expect("cover nerve faces are array");
    assert!(
        faces.iter().any(|face| {
            let contexts = face["contextRefs"]
                .as_array()
                .expect("contextRefs is array")
                .iter()
                .filter_map(Value::as_str)
                .collect::<BTreeSet<_>>();
            contexts == BTreeSet::from(["ctx:bottom", "ctx:left", "ctx:top"])
                && face["sharedAtomRefs"]
                    .as_array()
                    .expect("sharedAtomRefs is array")
                    .iter()
                    .any(|atom| atom == "atom:triple-overlap")
                && face["coherenceClaim"] == "not_visualized"
        }),
        "cover nerve faces must be sourced from selected triple-overlap sharedAtomRefs"
    );
    assert_eq!(
        cech["coverNerveProjection"]["faceSource"],
        "selected cover triple-overlap sharedAtomRefs recorded in archsig-measurement-packet/v1; not inferred by the viewer"
    );
    assert_eq!(cech["coverNerveProjection"]["h2CoherenceVisualized"], false);
    assert_eq!(cech["selectedH2"]["dimension"], Value::Null);
    assert_eq!(
        cech["selectedH2"]["status"],
        "not_measured_for_triple_overlap_faces"
    );

    let report = read_json(&out_dir.join("archsig-insight-report.json"));
    assert_eq!(
        report["gluingGeometry"]["nerve"]["triangles"], cech["coverNerveProjection"]["faces"],
        "viewer gluing projection must consume packet-projected faces"
    );
    assert_eq!(
        report["gluingGeometry"]["nerve"]["h2CoherenceVisualized"],
        false
    );
    assert!(
        report["gluingGeometry"]["nerve"]["triangleSource"]
            .as_str()
            .is_some_and(|text| text.contains("not inferred by the viewer"))
    );
}

#[test]
fn cli_analyze_v2_emits_insight_report_brief_and_viewer_scene_contract() {
    let out_dir = temp_dir("ag-measurement-insight-viewer");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    let report = read_json(&out_dir.join("archsig-insight-report.json"));
    let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    let brief = fs::read_to_string(out_dir.join("archsig-insight-brief.md"))
        .expect("insight brief is generated");

    assert_eq!(report["schema"], "archsig-insight-report/v1");
    assert_eq!(
        report["headline"]["conclusionCode"],
        "MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    );
    assert_eq!(report["insightCards"][0]["kind"], "global_glue_mismatch");
    assert!(
        report["insightCards"][0]["whyItMatters"]
            .as_str()
            .is_some_and(|text| text.contains("architecture drift")),
        "Top insight must explain why it matters"
    );
    assert!(
        report["insightCards"][0]["evidence"]["structuralVerdictRefs"]
            .as_array()
            .is_some_and(|refs| !refs.is_empty())
            && report["insightCards"][0]["evidence"]["sourceRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty()),
        "Top insight must carry verdict and where refs"
    );
    assert_eq!(
        report["insightCards"][0]["evidence"]["evidenceResolutionStatus"],
        "resolved_from_packet_support"
    );
    assert!(
        report["insightCards"][0]["sampleRefs"]["note"]
            .as_str()
            .is_some_and(|note| note.contains("orientation only")),
        "sample refs must be separated from measured evidence refs"
    );
    assert!(
        report["rankingBasis"]
            .as_array()
            .expect("ranking basis is array")
            .iter()
            .any(|entry| entry == "measured_nonzero structural verdict"),
        "deterministic ranking basis must be recorded"
    );
    let ranking_basis = report["rankingBasis"]
        .as_array()
        .expect("ranking basis is array");
    let boundary_rank = ranking_basis
        .iter()
        .position(|entry| entry == "measurement boundary")
        .expect("measurement boundary ranking basis is recorded");
    let zero_rank = ranking_basis
        .iter()
        .position(|entry| entry == "measured_zero confirmation")
        .expect("measured_zero ranking basis is recorded");
    assert!(
        boundary_rank < zero_rank,
        "ranking basis must place measurement boundary before measured_zero confirmation"
    );
    assert_eq!(
        report["insightCards"][0]["tourRefs"][0], report["guidedTours"][0]["tourId"],
        "Insight Card tourRefs and Tour insightRefs must be mutually linked"
    );
    assert!(
        report["guidedTours"][0]["insightRefs"]
            .as_array()
            .expect("tour insightRefs are array")
            .contains(&report["insightCards"][0]["id"])
    );
    let tour_ids = report["guidedTours"]
        .as_array()
        .expect("guided tours are array")
        .iter()
        .map(|tour| tour["tourId"].as_str().expect("tour id is present"))
        .collect::<BTreeSet<_>>();
    for card in report["insightCards"]
        .as_array()
        .expect("insight cards are array")
    {
        for tour_ref in card["tourRefs"].as_array().expect("tour refs are array") {
            let tour_ref = tour_ref.as_str().expect("tour ref is string");
            assert!(
                tour_ids.contains(tour_ref),
                "every insight card tourRef must resolve to a guided tour"
            );
            let tour = report["guidedTours"]
                .as_array()
                .expect("guided tours are array")
                .iter()
                .find(|tour| tour["tourId"] == tour_ref)
                .expect("tour ref resolves");
            assert!(
                tour["insightRefs"]
                    .as_array()
                    .expect("tour insight refs are array")
                    .contains(&card["id"]),
                "guided tour must link back to its insight card"
            );
        }
    }
    for scene in report["viewerVisualScenes"]
        .as_array()
        .expect("viewer visual scenes are array")
    {
        assert!(
            scene["userQuestion"]
                .as_str()
                .is_some_and(|text| !text.is_empty())
        );
        assert!(scene["axisMapping"]["x"].as_str().is_some());
        assert!(
            scene["layers"][0]["refs"].is_object()
                && scene["layers"][0]["clickTargetKind"].as_str().is_some()
                && scene["visualEncodings"][0]["shapeRole"].as_str().is_some()
                && scene["visualEncodings"][0]["lineRole"].as_str().is_some()
                && scene["visualEncodings"][0]["textRole"].as_str().is_some()
        );
        if scene["sceneStatus"] == "active" {
            assert_eq!(
                scene["layers"][0]["omissionPolicy"],
                "preserve_for_top_insight"
            );
        } else {
            assert_eq!(scene["layers"][0]["omissionPolicy"], "omittable_background");
            assert_eq!(scene["visualEncodings"][0]["colorRole"], "not_applicable");
        }
    }
    assert!(
        report["viewerVisualScenes"]
            .as_array()
            .expect("scenes are array")
            .iter()
            .any(|scene| scene["sceneId"] == "overview"
                && scene["layers"][0]["kind"] == "top_insight_beacon"),
        "overview scene must carry top insight beacons"
    );
    assert!(
        report["viewerVisualScenes"]
            .as_array()
            .expect("scenes are array")
            .iter()
            .any(|scene| scene["sceneId"] == "cech-gluing"
                && scene["layers"][0]["kind"] == "overlap_seam"),
        "gluing scene must expose overlap seams"
    );
    assert!(
        report["viewerVisualScenes"]
            .as_array()
            .expect("scenes are array")
            .iter()
            .any(|scene| scene["sceneId"] == "cech-h1-mismatch"
                && scene["layers"][0]["geometryRole"] == "ribbon"),
        "H1 scene must expose cocycle representative ribbon/seam"
    );
    let boundary_scene = report["viewerVisualScenes"]
        .as_array()
        .expect("scenes are array")
        .iter()
        .find(|scene| scene["sceneId"] == "boundary-assumption")
        .expect("boundary scene is present");
    let boundary_layers = boundary_scene["layers"]
        .as_array()
        .expect("boundary scene layers are array");
    let boundary_encodings = boundary_scene["visualEncodings"]
        .as_array()
        .expect("boundary scene visual encodings are array");
    assert_eq!(
        boundary_layers.len(),
        6,
        "boundary scene must expose one layer per checked/assumed/unknown/unmeasured/not_computed/violated state"
    );
    for state in [
        "checked",
        "assumed",
        "unknown",
        "unmeasured",
        "not_computed",
        "violated",
    ] {
        assert!(
            boundary_layers
                .iter()
                .any(|layer| layer["boundaryState"] == state
                    && layer["encodingRef"] == format!("encoding:boundary-assumption:{state}")),
            "boundary scene must include a layer for {state}"
        );
        assert!(
            boundary_encodings
                .iter()
                .any(|encoding| encoding["boundaryState"] == state
                    && encoding["colorRole"] == state
                    && encoding["shapeRole"].as_str().is_some()
                    && encoding["lineRole"].as_str().is_some()
                    && encoding["textRole"].as_str().is_some()),
            "boundary scene must include visual encoding for {state}"
        );
    }
    let repair_scene = report["viewerVisualScenes"]
        .as_array()
        .expect("scenes are array")
        .iter()
        .find(|scene| scene["sceneId"] == "repair-dual")
        .expect("repair scene is present");
    assert!(
        repair_scene["nonClaims"]
            .as_array()
            .expect("repair scene nonClaims are array")
            .iter()
            .any(|claim| claim
                .as_str()
                .is_some_and(|text| text.contains("not a semantic refactor guarantee"))),
        "repair scene must carry the not-auto-repair non-claim"
    );
    assert!(
        repair_scene["visualEncodings"][0]["textRole"]
            .as_str()
            .is_some_and(|text| text.contains("not automatic repair")),
        "repair scene text role must keep the non-automatic repair boundary visible"
    );
    assert_eq!(
        viewer["decisionBar"]["conclusion"],
        "MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    );
    assert!(
        viewer["atomNodes"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && viewer["moleculeGroups"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && viewer["atomEdges"].as_array().is_some(),
        "AG viewer data must project finitePosetSite into renderer-compatible atomNodes, moleculeGroups, and atomEdges"
    );
    assert!(
        viewer["reportPane"]["evidenceDetailShape"]
            .as_array()
            .expect("detail shape is array")
            .iter()
            .any(|section| section == "Boundary")
            && viewer["copyBlocks"]["sourceRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty()),
        "viewer must expose Evidence Detail shape and copyable source refs"
    );
    assert!(
        viewer["actionQueue"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && viewer["reportPane"]["actionQueue"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "viewer must expose suggested next inspections at top-level and in the report pane"
    );
    assert!(
        viewer["largeGraphStrategy"]["topInsightEvidencePinning"]["preservedRefs"]
            .as_array()
            .is_some_and(|refs| !refs.is_empty()),
        "large graph strategy must pin concrete top-insight evidence refs"
    );
    assert_eq!(
        viewer["omittedDetailCounts"]["omittedSceneLayerObjects"].as_u64(),
        Some(0)
    );
    assert_eq!(
        viewer["reportPane"]["omittedDetailCounts"], viewer["omittedDetailCounts"],
        "report pane and viewer payload must agree on omitted detail counts"
    );
    assert_eq!(summary["readThisFirst"]["heading"], "Read this first");
    assert_eq!(
        manifest["artifactLinks"]["insightBrief"],
        "archsig-insight-brief.md"
    );
    assert!(
        manifest["generatedArtifacts"]
            .as_array()
            .expect("generated artifacts are array")
            .iter()
            .any(|artifact| artifact == "archsig-insight-report.json")
    );
    assert!(brief.starts_with("# ArchSig Insight Brief\n\n## Read this first"));
    assert!(brief.contains("## LLM handoff"));
}

#[test]
fn cli_analyze_v2_insight_surface_preserves_false_clean_and_not_computed_boundaries() {
    let out_dir = temp_dir("ag-measurement-insight-boundaries");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let report = read_json(&out_dir.join("archsig-insight-report.json"));
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    let brief = fs::read_to_string(out_dir.join("archsig-insight-brief.md"))
        .expect("insight brief is generated");
    assert_eq!(
        summary["conclusion"].as_str(),
        Some("NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"),
        "measured_zero H1 must stay conclusion-first even when boundary digest is present"
    );
    assert_eq!(
        report["headline"]["conclusionCode"].as_str(),
        Some("NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"),
        "insight headline must keep the profile-relative zero conclusion as the product-facing verdict"
    );
    assert_eq!(
        viewer["decisionBar"]["conclusion"].as_str(),
        Some("NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"),
        "viewer Decision Bar must lead with the useful H1 zero conclusion, not the boundary"
    );
    assert!(
        report["insightCards"]
            .as_array()
            .expect("insight cards are array")
            .iter()
            .any(|card| card["kind"] == "no_measured_glue_mismatch"),
        "measured_zero must be represented as a profile-relative zero insight"
    );
    let card_kinds = report["insightCards"]
        .as_array()
        .expect("insight cards are array")
        .iter()
        .map(|card| card["kind"].as_str().unwrap_or_default())
        .collect::<Vec<_>>();
    let boundary_index = card_kinds
        .iter()
        .position(|kind| *kind == "measurement_boundary")
        .expect("fixture must surface a measurement boundary card");
    let zero_index = card_kinds
        .iter()
        .position(|kind| *kind == "no_measured_glue_mismatch")
        .expect("fixture must surface a measured_zero card");
    assert!(
        zero_index < boundary_index,
        "measured_zero confirmation must rank before measurement boundary when both are present"
    );
    assert!(
        viewer["viewerVisualScenes"]
            .as_array()
            .expect("viewer visual scenes are array")
            .iter()
            .filter(|scene| {
                scene["sceneId"] == "cech-gluing"
                    || scene["sceneId"] == "cech-h1-mismatch"
                    || scene["sceneId"] == "obstruction"
            })
            .all(|scene| scene["visualEncodings"][0]["colorRole"] != "measured_nonzero"),
        "zero or inactive scenes must not use measured_nonzero coloring"
    );
    assert!(
        viewer["viewerVisualScenes"]
            .as_array()
            .expect("viewer visual scenes are array")
            .iter()
            .any(|scene| scene["sceneId"] == "overview"
                && scene["visualEncodings"][0]["colorRole"] == "measured_zero"),
        "measured_zero top insight must render overview as the selected-support zero conclusion"
    );
    assert!(
        viewer["viewerVisualScenes"]
            .as_array()
            .expect("viewer visual scenes are array")
            .iter()
            .any(|scene| scene["sceneId"] == "cech-gluing"
                && scene["sceneStatus"] == "active"
                && scene["visualEncodings"][0]["colorRole"] == "measured_zero"),
        "measured_zero Cech scene must stay active and explicitly measured_zero"
    );
    let gluing_geometry = report["gluingGeometry"]
        .as_object()
        .expect("insight report must expose gluing geometry projection");
    assert_eq!(
        gluing_geometry["schema"].as_str(),
        Some("archsig-viewer-gluing-geometry/v1"),
        "gluing geometry projection must be typed"
    );
    assert!(
        gluing_geometry["nerve"]["vertices"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && gluing_geometry["nerve"]["edges"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "cover nerve must expose packet-derived vertices and restriction edges"
    );
    assert!(
        gluing_geometry["nerve"]["triangleSource"]
            .as_str()
            .is_some_and(|text| text.contains("not inferred by the viewer")),
        "cover nerve triangles must be sourced from packet cover projection, not viewer inference"
    );
    assert_eq!(
        gluing_geometry["nerve"]["h2CoherenceVisualized"].as_bool(),
        Some(false),
        "gluing viewer PRD must preserve the H2 silence boundary"
    );
    assert!(
        gluing_geometry["cocycleRibbon"]["closureGapEncoding"]["nonClaim"]
            .as_str()
            .is_some_and(|text| text.contains("monodromy verdict is not generated")),
        "H1 cocycle ribbon must keep the monodromy non-claim explicit"
    );
    assert!(
        gluing_geometry["atomGlyphs"]
            .as_array()
            .is_some_and(|items| items
                .iter()
                .any(|item| item["shapeRole"] == "structured_atom_glyph")),
        "atom internal glyph projection must expose fiber/carrier/valence/semantic-anchor roles"
    );
    assert!(
        gluing_geometry["repairMorphs"]
            .as_array()
            .is_some_and(Vec::is_empty),
        "repair morphs must not be inferred without packet alexanderDualRepair minimal hitting sets"
    );
    assert!(
        gluing_geometry["omittedGeometryCounts"]
            .as_object()
            .is_some_and(|counts| counts.contains_key("measuredZeroRegions")
                && counts.contains_key("cocycleSupportEdges")
                && counts.contains_key("blockedRegions")
                && counts.contains_key("atomGlyphs")),
        "gluing projection must report omitted counts for each independently capped geometry family"
    );
    assert_eq!(
        viewer["aatGeometryOverlays"]["gluingGeometry"], report["gluingGeometry"],
        "viewer data must consume the same gluing geometry projection as the insight report"
    );
    for scene_id in [
        "site-cover",
        "cech-gluing",
        "cech-h1-mismatch",
        "hodge-debt-field",
    ] {
        let scene = viewer["viewerVisualScenes"]
            .as_array()
            .expect("viewer visual scenes are array")
            .iter()
            .find(|scene| scene["sceneId"] == scene_id)
            .unwrap_or_else(|| panic!("scene {scene_id} exists"));
        assert_eq!(
            scene["axisMappingImplemented"].as_bool(),
            Some(true),
            "{scene_id} must mark axisMapping as geometry-driving"
        );
        assert!(
            scene["visualEncodingLegend"]
                .as_array()
                .is_some_and(|items| items.len() >= 4),
            "{scene_id} must carry fixed color/shape/line/opacity legend"
        );
        assert!(
            scene["projectionBoundary"]
                .as_str()
                .is_some_and(|text| text.contains("does not create a new structural verdict")),
            "{scene_id} must keep visual richness below verdict level"
        );
    }
    for forbidden in [
        "Architecture is clean",
        "No architecture issue exists",
        "Codebase is lawful",
    ] {
        assert!(
            !brief.contains(forbidden),
            "false clean claim must not appear in brief: {forbidden}"
        );
    }

    let no_ambient_out_dir = temp_dir("ag-measurement-insight-no-common-ambient");
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["predicate"] != "commonAmbient")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:tor-common-ambient"))
            .cloned()
            .collect(),
    );
    let archmap_path = no_ambient_out_dir.join("archmap_v2_law_conflict_tor_no_ambient.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        no_ambient_out_dir.to_str().expect("path is utf-8"),
    ]);
    let report = read_json(&no_ambient_out_dir.join("archsig-insight-report.json"));
    let viewer = read_json(&no_ambient_out_dir.join("archsig-atom-viewer-data.json"));
    assert!(
        report["insightCards"]
            .as_array()
            .expect("insight cards are array")
            .iter()
            .any(|card| card["kind"] == "not_computed_blocker"
                && card["rankingBasis"]
                    .as_array()
                    .expect("ranking basis is array")
                    .iter()
                    .any(|basis| basis == "no_common_ambient")),
        "not_computed reason code must be promoted to a blocker insight"
    );
    assert!(
        viewer["viewerVisualScenes"]
            .as_array()
            .expect("scenes are array")
            .iter()
            .any(|scene| scene["sceneId"] == "law-conflict-tor"
                && scene["visualEncodings"][0]["textRole"]
                    .as_str()
                    .is_some_and(|text| text.contains("no_common_ambient"))),
        "LawConflict scene must show blocking reason instead of an empty conflict view"
    );
    assert!(
        viewer["viewerVisualScenes"]
            .as_array()
            .expect("viewer visual scenes are array")
            .iter()
            .any(|scene| scene["sceneId"] == "law-conflict-tor"
                && scene["visualEncodings"][0]["colorRole"] == "not_computed"),
        "LawConflict not_computed blocker must remain visually distinct"
    );
}

#[test]
fn cli_analyze_v2_insight_viewer_truncates_large_background_projection() {
    let out_dir = temp_dir("ag-measurement-insight-large-viewer");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    let template_atom = archmap["atoms"]
        .as_array()
        .and_then(|atoms| atoms.first())
        .cloned()
        .expect("fixture has an atom template");
    let original_atoms = archmap["atoms"]
        .as_array()
        .cloned()
        .expect("fixture atoms are array");
    let mut atoms = Vec::new();
    for index in 0..10_050 {
        let mut atom = template_atom.clone();
        atom["id"] = Value::String(format!("atom:background:{index}"));
        atom["predicate"] = Value::String("backgroundSample".to_string());
        atoms.push(atom);
    }
    atoms.extend(original_atoms);
    archmap["atoms"] = Value::Array(atoms);
    let archmap_path = out_dir.join("archmap_v2_large_background.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("large archmap serializes"),
    )
    .expect("large archmap can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    let brief = fs::read_to_string(out_dir.join("archsig-insight-brief.md"))
        .expect("insight brief is generated");
    assert!(
        viewer["finitePosetSite"]["atoms"]
            .as_array()
            .is_some_and(|atoms| atoms.len() <= 10_000),
        "viewer payload must truncate background atom projection"
    );
    assert_eq!(
        viewer["largeGraphStrategy"]["mode"], "cluster_aggregation",
        "large graph strategy must switch when the source ArchMap crosses the atom threshold"
    );
    assert!(
        viewer["omittedDetailCounts"]["omittedAtoms"]
            .as_u64()
            .is_some_and(|count| count > 0),
        "viewer payload must report omitted background atoms"
    );
    for key in [
        "omittedAtoms",
        "omittedEdges",
        "omittedContextMemberships",
        "omittedCoverOverlaps",
        "omittedSceneLayerObjects",
        "omittedLabels",
        "omittedSourceRefs",
    ] {
        assert!(
            brief.contains(key),
            "insight brief must include omitted detail count for {key}"
        );
    }
    assert!(
        viewer["largeGraphStrategy"]["topInsightEvidencePinning"]["preservedRefs"]
            .as_array()
            .is_some_and(|refs| !refs.is_empty()),
        "top insight evidence must remain pinned while background atoms are truncated"
    );
    assert!(
        viewer["finitePosetSite"]["atoms"]
            .as_array()
            .expect("viewer atoms are array")
            .iter()
            .any(
                |atom| atom["normalizedAtomId"] == "atom:left-bottom-cech-mismatch"
                    || atom["sourceAtomId"] == "atom:left-bottom-cech-mismatch"
            ),
        "top insight support atom must remain in the truncated viewer projection even when it appears after background atoms"
    );
}

#[test]
fn cli_analyze_v2_insight_artifacts_redact_local_source_refs() {
    let out_dir = temp_dir("ag-measurement-insight-source-redaction");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    let private_ref = "/Users/nakahata/private/internal.rs";
    archmap["sources"][private_ref] = json!({
        "kind": "rust",
        "path": private_ref,
        "symbol": "InternalOnly",
        "line": 1
    });
    let atoms = archmap["atoms"].as_array_mut().expect("atoms are array");
    let mismatch = atoms
        .iter_mut()
        .find(|atom| atom["id"] == "atom:left-bottom-cech-mismatch")
        .expect("mismatch atom exists");
    mismatch["refs"]
        .as_array_mut()
        .expect("refs are array")
        .push(Value::String(private_ref.to_string()));
    let archmap_path = out_dir.join("archmap_v2_private_source_ref.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let report = fs::read_to_string(out_dir.join("archsig-insight-report.json"))
        .expect("insight report is generated");
    let brief = fs::read_to_string(out_dir.join("archsig-insight-brief.md"))
        .expect("insight brief is generated");
    let viewer = fs::read_to_string(out_dir.join("archsig-atom-viewer-data.json"))
        .expect("viewer data is generated");
    for artifact in [&report, &brief, &viewer] {
        assert!(
            !artifact.contains(private_ref),
            "insight artifacts must not leak local source refs"
        );
        assert!(
            artifact.contains("source-ref:redacted-local-path"),
            "insight artifacts must preserve a redacted source-ref marker"
        );
    }
}

#[test]
fn cli_analyze_v2_validation_failure_emits_blocking_insight_projection() {
    let out_dir = temp_dir("ag-measurement-insight-validation-failure");
    let root = archmap_v1_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("replacement_negative/archmap_label_only_semantic.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    assert!(
        !out_dir.join("archsig-analysis-summary.json").exists(),
        "validation failure must not emit a success summary"
    );
    assert!(
        !out_dir.join("archsig-measurement-packet.json").exists(),
        "validation failure must not emit a measurement packet"
    );
    let report = read_json(&out_dir.join("archsig-insight-report.json"));
    let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    let brief = fs::read_to_string(out_dir.join("archsig-insight-brief.md"))
        .expect("validation brief is generated");
    assert_eq!(report["insightCards"][0]["kind"], "validation_failure");
    assert_eq!(
        viewer["decisionBar"]["conclusion"],
        "VALIDATION_FAILED_BEFORE_MEASUREMENT"
    );
    assert_eq!(viewer["largeGraphStrategy"]["mode"], "validation_blocked");
    assert_eq!(manifest["status"], "validation_failed");
    assert!(
        brief.contains("Validation failed before measurement")
            && brief.contains("Do not infer beyond the listed claims and boundaries."),
        "validation brief must be usable without measurement claims"
    );
}

#[test]
fn cli_analyze_v2_cech_rejects_unsupported_measurement_profile_selectors() {
    let out_dir = temp_dir("ag-measurement-cech-bad-profile");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_ag.json"));
    policy["measurementProfiles"][0]["coefficient"] = Value::String("Z".to_string());
    let policy_path = out_dir.join("law_policy_bad_cech_selector.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_cech_h1_visible.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_cech_requires_matching_witness_family() {
    let out_dir = temp_dir("ag-measurement-cech-witness-family");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_ag.json"));
    policy["measurementProfiles"][0]["witnessFamily"] = Value::Array(vec![]);
    let policy_path = out_dir.join("law_policy_missing_cech_witness.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_cech_h1_visible.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_cech_ignores_unanchored_mismatch_support() {
    let out_dir = temp_dir("ag-measurement-cech-unanchored-support");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    archmap["atoms"][4]["object"] = Value::String("ctx:right".to_string());
    let archmap_path = out_dir.join("archmap_v2_unanchored_cech.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(cech["dimensions"]["H1"], Value::from(1));
    assert_eq!(cech["observedCocycle"]["classNonzero"], false);
    assert_eq!(
        cech["observedCocycle"]["mismatchSupportRefs"]
            .as_array()
            .expect("mismatch support refs is array")
            .len(),
        0
    );
}

#[test]
fn cli_analyze_v2_square_free_repair_outputs_hitting_sets_and_nsdepth() {
    let out_dir = temp_dir("ag-measurement-square-free-repair");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_square_free_repair.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.square-free-repair@1"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "nsdepth_certificate_verified"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["certRef"],
        "atom:nsdepth-certificate"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(repair["obstructionIdeal"]["id"], "I_Ob^U");
    assert_eq!(
        repair["minimalForbiddenSupports"],
        serde_json::json!([["x_checkout", "x_inventory"], ["x_inventory", "x_payment"]])
    );
    assert_eq!(
        repair["alexanderDualRepair"]["minimalHittingSets"],
        serde_json::json!([["x_inventory"], ["x_checkout", "x_payment"]])
    );
    assert_eq!(
        repair["stanleyReisnerComplex"]["reducedHomology"]["betti"],
        serde_json::json!([
            {"degree": 0, "dimension": 1},
            {"degree": 1, "dimension": 0}
        ])
    );
    assert_eq!(repair["nsdepthCertificate"]["status"], "verified");
    assert_eq!(repair["nsdepthCertificate"]["nsdepth"], Value::from(2));
    assert_eq!(
        repair["nsdepthCertificate"]["verifiedMinimalForbiddenSupports"],
        serde_json::json!([["x_checkout", "x_inventory"], ["x_inventory", "x_payment"]])
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "MEASURED_AG_OBSTRUCTION_UNDER_PROFILE"
    );
    let report = read_json(&out_dir.join("archsig-insight-report.json"));
    let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    assert!(
        report["gluingGeometry"]["forbiddenCages"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "square-free obstruction fixture must project minimal forbidden support as cage geometry"
    );
    assert!(
        report["gluingGeometry"]["repairMorphs"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| {
                    item["animationRole"] == "continuous_morph_lower_bound"
                        && item["nonClaim"] == "not automatic repair"
                        && item["fromCageRefs"]
                            .as_array()
                            .is_some_and(|refs| refs.len() >= 2)
                        && item["fromAtomRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
            }),
        "square-free repair fixture must project lower-bound repair candidate from related forbidden supports"
    );
    assert_eq!(
        viewer["aatGeometryOverlays"]["forbiddenCages"], report["gluingGeometry"]["forbiddenCages"],
        "viewer overlay must carry forbidden cage geometry"
    );
    assert_eq!(
        viewer["aatGeometryOverlays"]["repairMorphs"], report["gluingGeometry"]["repairMorphs"],
        "viewer overlay must carry repair morph geometry"
    );
}

#[test]
fn cli_analyze_v2_square_free_without_certificate_returns_unknown() {
    let out_dir = temp_dir("ag-measurement-square-free-no-cert");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["id"] != "atom:nsdepth-certificate")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:nsdepth-certificate"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_square_free_no_cert.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "nsdepth_certificate_missing"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(repair["nsdepthCertificate"]["status"], "missing");
}

#[test]
fn cli_analyze_v2_square_free_requires_matching_witness_family() {
    let out_dir = temp_dir("ag-measurement-square-free-witness-family");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_square_free.json"));
    policy["measurementProfiles"][0]["witnessFamily"] = Value::Array(vec![]);
    let policy_path = out_dir.join("law_policy_square_free_missing_witness.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_square_free_repair.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_square_free_malformed_nsdepth_certificate_returns_unknown() {
    let out_dir = temp_dir("ag-measurement-square-free-bad-cert");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"][5]["object"] = Value::String("not-a-verifier-payload".to_string());
    let archmap_path = out_dir.join("archmap_v2_square_free_bad_cert.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "nsdepth_certificate_invalid_payload"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(repair["nsdepthCertificate"]["status"], "invalid_payload");
}

#[test]
fn cli_analyze_v2_square_free_wrong_nsdepth_value_returns_unknown() {
    let out_dir = temp_dir("ag-measurement-square-free-wrong-nsdepth");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"][5]["object"] = Value::String(
        "nsdepth=1;depthRule=alexanderDualMaxMinimalHittingSet@1;minimalForbiddenSupports=x_checkout+x_inventory|x_inventory+x_payment;supportAtomRefs=atom:ob-checkout-inventory,atom:ob-inventory-payment"
            .to_string(),
    );
    let archmap_path = out_dir.join("archmap_v2_square_free_wrong_nsdepth.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "nsdepth_certificate_invalid_payload"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(repair["nsdepthCertificate"]["status"], "invalid_payload");
}

#[test]
fn cli_analyze_v2_square_free_junk_nsdepth_segment_returns_unknown() {
    let out_dir = temp_dir("ag-measurement-square-free-junk-nsdepth");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"][5]["object"] = Value::String(
        "nsdepth=2;depthRule=alexanderDualMaxMinimalHittingSet@1;unexpected-segment;minimalForbiddenSupports=x_checkout+x_inventory|x_inventory+x_payment;supportAtomRefs=atom:ob-checkout-inventory,atom:ob-inventory-payment"
            .to_string(),
    );
    let archmap_path = out_dir.join("archmap_v2_square_free_junk_nsdepth.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "nsdepth_certificate_invalid_payload"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(repair["nsdepthCertificate"]["status"], "invalid_payload");
}

#[test]
fn cli_analyze_v2_square_free_numeric_only_certificate_returns_unknown() {
    let out_dir = temp_dir("ag-measurement-square-free-extra-bad-cert");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"][5]["object"] = Value::String("2".to_string());
    let archmap_path = out_dir.join("archmap_v2_square_free_extra_bad_cert.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "nsdepth_certificate_author_supplied_unverified"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(
        repair["nsdepthCertificate"]["status"],
        "author_supplied_unverified"
    );
}

#[test]
fn cli_analyze_v2_square_free_rejects_generator_outside_witness_family() {
    let out_dir = temp_dir("ag-measurement-square-free-unknown-variable");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"][3]["subject"] = Value::String("x_unknown".to_string());
    let archmap_path = out_dir.join("archmap_v2_square_free_unknown_variable.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_square_free.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_square_free_rejects_too_many_witness_variables() {
    let out_dir = temp_dir("ag-measurement-square-free-too-many-witnesses");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_square_free.json"));
    policy["measurementProfiles"][0]["witnessFamily"] = Value::Array(
        (0..13)
            .map(|index| {
                serde_json::json!({
                    "law": "ag.square-free-repair",
                    "variable": format!("x_{index}")
                })
            })
            .collect(),
    );
    let policy_path = out_dir.join("law_policy_square_free_too_many_witnesses.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_square_free_repair.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_square_free_without_generators_returns_measured_zero() {
    let out_dir = temp_dir("ag-measurement-square-free-zero");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["predicate"] != "obstructionGenerator")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| {
                !matches!(
                    atom.as_str(),
                    Some("atom:ob-checkout-inventory" | "atom:ob-inventory-payment")
                )
            })
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_square_free_zero.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(
        repair["obstructionIdeal"]["generators"]
            .as_array()
            .expect("generators is array")
            .len(),
        0
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_outputs_conflict_classes() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.law-conflict-tor@1"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "finite_degree1_shared_support_conflict_computed"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["certRef"],
        "atom:tor-common-ambient"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(tor["method"], "finite-degree1-shared-support-conflict@1");
    assert_eq!(
        tor["claimScope"],
        "degree-1 shared-support conflict detector over the selected common ambient pair"
    );
    assert_eq!(
        tor["commonAmbient"]["ambientRef"],
        "ambient:checkout-inventory"
    );
    assert_eq!(
        tor["lawConflicts"],
        serde_json::json!([{
            "conflictId": "LawConflict_1:1",
            "degree": 1,
            "support": ["x_checkout", "x_inventory", "x_payment"],
            "sharedSupport": ["x_inventory"],
            "leftLaw": "law:checkout",
            "leftGeneratorRef": "atom:checkout-law-generator",
            "rightLaw": "law:inventory",
            "rightGeneratorRef": "atom:inventory-law-generator",
            "contextRefs": ["ctx:tor-common-ambient"],
            "sourceRefs": ["src:checkout-policy", "src:inventory-policy"]
        }])
    );
    assert_eq!(
        tor["torByDegree"],
        serde_json::json!([{
            "degree": 1,
            "classCount": 1,
            "scope": "detected shared witness-variable support only"
        }])
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "MEASURED_AG_OBSTRUCTION_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_disjoint_supports_are_measured_zero() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-disjoint");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][1]["object"] = Value::String("x_checkout".to_string());
    archmap["atoms"][2]["object"] = Value::String("x_payment".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_disjoint.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(
        tor["lawConflicts"]
            .as_array()
            .expect("conflicts is array")
            .len(),
        0
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_nested_common_factor_is_nonzero() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-nested");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][1]["object"] = Value::String("x_inventory".to_string());
    archmap["atoms"][2]["object"] = Value::String("x_inventory,x_payment".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_nested.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(
        tor["lawConflicts"][0]["sharedSupport"],
        serde_json::json!(["x_inventory"])
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_rejects_generators_outside_ambient_pair() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-ambient-mismatch");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][2]["subject"] = Value::String("law:shipping".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_ambient_mismatch.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_without_common_ambient_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-no-ambient");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["predicate"] != "commonAmbient")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:tor-common-ambient"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_no_ambient.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "not_computed");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "no_common_ambient"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(tor["status"], "not_computed");
    assert_eq!(tor["reason"], "no_common_ambient");
}

#[test]
fn cli_analyze_v2_law_conflict_tor_requires_matching_witness_family() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-witness-family");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_tor.json"));
    policy["measurementProfiles"][0]["witnessFamily"] = Value::Array(vec![]);
    let policy_path = out_dir.join("law_policy_tor_missing_witness.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_law_conflict_tor.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_rejects_unsupported_resolution_selector() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-bad-resolution");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_tor.json"));
    policy["measurementProfiles"][0]["resolutionSelector"] =
        Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_tor_bad_resolution.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_law_conflict_tor.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_rejects_malformed_common_ambient_pair() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-bad-ambient");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][0]["object"] = Value::String("law:checkout".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_bad_ambient.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_rejects_generator_outside_witness_family() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-unknown-variable");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][1]["object"] = Value::String("x_unknown,x_inventory".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_unknown_variable.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_outputs_analytic_hodge_reading() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_sheaf_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.sheaf-laplacian@1"
    );
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "finite_laplacian_analytic_reading_computed"
    );
    let invariant = invariant_by_id(&packet, "sheaf-laplacian:profile:ag-sheaf-laplacian@1");
    assert_eq!(
        invariant["claimScope"],
        "graph Laplacian analytic proxy; not a full sheaf chain-complex Hodge theorem"
    );
    assert_eq!(
        invariant["laplacianMatrix"],
        serde_json::json!([[1.0, -1.0], [-1.0, 1.0]])
    );
    let reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["evaluator"] == "ag.sheaf-laplacian@1")
        .expect("laplacian analytic reading exists");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);
    assert_eq!(reading["regime"], "analytic-measurement");
    assert_eq!(
        reading["value"]["readingKind"],
        "graph-laplacian-hodge-proxy@1"
    );
    assert_eq!(
        reading["value"]["modelScope"],
        "finite graph Laplacian over selected cochain cells and boundary edges"
    );
    assert_eq!(
        reading["value"]["hodgeDecomposition"]["harmonic"],
        serde_json::json!([0.5, 0.5])
    );
    assert_eq!(
        reading["value"]["hodgeDecomposition"]["exact"],
        serde_json::json!([0.0, 0.0])
    );
    assert_eq!(
        reading["value"]["hodgeDecomposition"]["coexact"],
        serde_json::json!([0.5, -0.5])
    );
    assert_eq!(reading["value"]["harmonicMass"], Value::from(0.5));
    assert_eq!(reading["value"]["distanceToFlatness"], Value::from(0.5));
    assert_eq!(reading["value"]["spectralGap"], Value::from(2.0));
    assert_eq!(
        reading["value"]["curvatureTransferSpectrum"],
        serde_json::json!([
            {"cell": "cell:left", "curvature": 1.0},
            {"cell": "cell:right", "curvature": -1.0}
        ])
    );
    assert_eq!(reading["value"]["essentialRepairLowerBound"], Value::Null);
    assert_eq!(
        reading["value"]["nonConclusion"],
        "near-flat analytic values are not structural lawfulness verdicts"
    );
    let candidate = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| {
            reading["readingId"]
                .as_str()
                .is_some_and(|id| id.starts_with("theorem-candidate:harmonic-debt:"))
        })
        .expect("harmonic debt theorem-candidate reading exists");
    assert_eq!(candidate["regime"], "theorem-candidate");
    assert_eq!(
        candidate["value"]["essentialRepairLowerBound"],
        Value::from(0.707107)
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_rejects_duplicate_cochain_cells() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-duplicate-cell");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    let mut duplicate = archmap["atoms"][0].clone();
    duplicate["id"] = Value::String("atom:laplacian-left-cochain-duplicate".to_string());
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(duplicate);
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:laplacian-left-cochain-duplicate".to_string(),
        ));
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_duplicate_cell.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_rejects_non_finite_cochain_values() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-nan");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    archmap["atoms"][0]["object"] = Value::String("NaN".to_string());
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_nan.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_rejects_malformed_profile_selector() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-bad-profile");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_laplacian.json"));
    policy["measurementProfiles"][0]["resolutionSelector"] =
        Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_laplacian_bad_profile.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_sheaf_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_missing_witness_cell_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-missing-witness");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_laplacian.json"));
    policy["measurementProfiles"][0]["witnessFamily"]
        .as_array_mut()
        .expect("witnessFamily is array")
        .push(serde_json::json!({
            "law": "ag.sheaf-laplacian",
            "variable": "cell:extra"
        }));
    let policy_path = out_dir.join("law_policy_laplacian_missing_witness.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_sheaf_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "not_computed");
    let invariant = invariant_by_id(&packet, "sheaf-laplacian:profile:ag-sheaf-laplacian@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["reason"], "cellular_model_missing:cell:extra");
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_near_flat_is_not_measured_zero() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-near-flat");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    archmap["atoms"][0]["object"] = Value::String("0.001".to_string());
    archmap["atoms"][1]["object"] = Value::String("0".to_string());
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_near_flat.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(packet["structuralVerdict"][0]["verdictData"]["zero"], false);
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_without_boundary_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-no-boundary");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["predicate"] != "cellularBoundary")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:laplacian-boundary"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_no_boundary.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "not_computed");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "cellular_model_missing"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_outputs_pairing_and_audit_reading() {
    let out_dir = temp_dir("ag-measurement-period-stokes");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_period_stokes.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_period.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        0,
        "period readings are analytic-only and must not generate structural verdict rows"
    );
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(
        invariant["periodPairingMatrix"],
        serde_json::json!([[2.0, -1.0]])
    );
    assert_eq!(invariant["stokesAudit"]["status"], "checked");
    assert_eq!(
        invariant["stokesAudit"]["maxAbsoluteResidual"],
        Value::from(0.0)
    );
    let reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["evaluator"] == "ag.period-stokes@1")
        .expect("period analytic reading exists");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);
    assert_eq!(reading["regime"], "analytic-measurement");
    assert_eq!(reading["value"]["modelRelative"], true);
    assert_eq!(
        reading["value"]["cycleBasis"],
        serde_json::json!(["cycle:alpha", "cycle:beta"])
    );
    assert_eq!(
        reading["value"]["periodPairingMatrix"],
        serde_json::json!([[2.0, -1.0]])
    );
    assert_eq!(
        reading["value"]["nonConclusion"],
        "period pairing is a model-relative analytic reading and is not a structural lawfulness verdict"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(|entry| {
                entry["assumption"] == "period_comparison" && entry["status"] == "assumed"
            })
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_audit_mismatch_fails_fast() {
    let out_dir = temp_dir("ag-measurement-period-stokes-audit-mismatch");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"][3]["object"] = Value::String("chain:sigma=4".to_string());
    let archmap_path = out_dir.join("archmap_v2_period_stokes_audit_mismatch.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_period.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Stokes audit failed"),
        "Stokes audit mismatch must fail as evaluator error\n{stderr}"
    );
    assert!(
        !out_dir.join("archsig-measurement-packet.json").exists(),
        "Stokes audit fail-fast must not leave a success packet"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_without_audit_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-period-stokes-no-audit");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| {
                atom["predicate"] != "dOmegaIntegral" && atom["predicate"] != "boundaryPeriod"
            })
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| {
                !matches!(
                    atom.as_str(),
                    Some("atom:stokes-domega-sigma" | "atom:stokes-boundary-sigma")
                )
            })
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_period_stokes_no_audit.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_period.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        0
    );
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["reason"], "period_model_missing");
}

#[test]
fn cli_analyze_v2_period_stokes_missing_pairing_cell_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-period-stokes-missing-cell");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(serde_json::json!({
            "id": "atom:period-eta-alpha",
            "kind": "semantic",
            "subject": "omega:secondary",
            "object": "cycle:alpha=5",
            "axis": "period",
            "predicate": "periodIntegral",
            "refs": ["src:period-alpha"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String("atom:period-eta-alpha".to_string()));
    let archmap_path = out_dir.join("archmap_v2_period_stokes_missing_cell.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_period.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(
        invariant["reason"],
        "period_model_missing:omega:secondary/cycle:beta"
    );
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["evaluator"] != "ag.period-stokes@1"),
        "missing period pairing cells must not synthesize zero analytic readings"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_rejects_unknown_cycle() {
    let out_dir = temp_dir("ag-measurement-period-stokes-unknown-cycle");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"][0]["object"] = Value::String("cycle:missing=2".to_string());
    let archmap_path = out_dir.join("archmap_v2_period_stokes_unknown_cycle.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_period_stokes_rejects_duplicate_pairings() {
    let out_dir = temp_dir("ag-measurement-period-stokes-duplicate");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    let mut duplicate = archmap["atoms"][0].clone();
    duplicate["id"] = Value::String("atom:period-omega-alpha-duplicate".to_string());
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(duplicate);
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:period-omega-alpha-duplicate".to_string(),
        ));
    let archmap_path = out_dir.join("archmap_v2_period_stokes_duplicate.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_period_stokes_rejects_non_finite_values() {
    let out_dir = temp_dir("ag-measurement-period-stokes-nan");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"][0]["object"] = Value::String("cycle:alpha=NaN".to_string());
    let archmap_path = out_dir.join("archmap_v2_period_stokes_nan.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_period_stokes_rejects_malformed_profile_selector() {
    let out_dir = temp_dir("ag-measurement-period-stokes-bad-profile");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_period.json"));
    policy["measurementProfiles"][0]["resolutionSelector"] =
        Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_period_bad_profile.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_period_stokes.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_period_stokes_missing_witness_cycle_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-period-stokes-missing-witness");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_period.json"));
    policy["measurementProfiles"][0]["witnessFamily"]
        .as_array_mut()
        .expect("witnessFamily is array")
        .push(serde_json::json!({
            "law": "ag.period-stokes",
            "variable": "cycle:extra"
        }));
    let policy_path = out_dir.join("law_policy_period_missing_witness.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_period_stokes.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["reason"], "period_model_missing:cycle:extra");
}

#[test]
fn cli_analyze_v2_support_transfer_outputs_residue_and_wasserstein_cost() {
    let out_dir = temp_dir("ag-measurement-support-transfer");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_support_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        0,
        "transfer readings are analytic-only and must not generate structural verdict rows"
    );
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(
        invariant["transferMeasurementPairing"],
        serde_json::json!([[0.25, 0.75]])
    );
    assert_eq!(invariant["transferResidue"], Value::from(0.790569));
    assert_eq!(invariant["wassersteinTransferCost"], Value::from(3.5));
    let reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["evaluator"] == "ag.support-transfer@1")
        .expect("transfer analytic reading exists");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);
    assert_eq!(reading["regime"], "analytic-measurement");
    assert_eq!(
        reading["value"]["transferMeasurementPairing"],
        serde_json::json!([[0.25, 0.75]])
    );
    assert_eq!(reading["value"]["transferResidue"], Value::from(0.790569));
    assert_eq!(
        reading["value"]["wassersteinTransferCost"],
        Value::from(3.5)
    );
    assert_eq!(
        reading["value"]["nonConclusion"],
        "transfer readings do not prove absence of side effects or global repair safety"
    );
    let candidate = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| {
            reading["readingId"]
                .as_str()
                .is_some_and(|id| id.starts_with("theorem-candidate:transfer-lower-bound:"))
        })
        .expect("transfer lower bound theorem-candidate reading exists");
    assert_eq!(candidate["regime"], "theorem-candidate");
    assert_eq!(candidate["value"]["transferLowerBound"], Value::from(3.5));
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(|entry| {
                entry["assumption"] == "transfer_lower_bound" && entry["status"] == "assumed"
            })
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_support_transfer_missing_pairing_cell_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-support-transfer-missing-cell");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(serde_json::json!({
            "id": "atom:transfer-repair-path-secondary",
            "kind": "semantic",
            "subject": "repair:path:secondary",
            "object": "selected",
            "axis": "transfer",
            "predicate": "repairPath",
            "refs": ["src:repair-path"]
        }));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(serde_json::json!({
            "id": "atom:transfer-secondary-api",
            "kind": "semantic",
            "subject": "repair:path:secondary",
            "object": "support:api=0.5",
            "axis": "transfer",
            "predicate": "transferPairing",
            "refs": ["src:transfer-api"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:transfer-repair-path-secondary".to_string(),
        ));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String("atom:transfer-secondary-api".to_string()));
    let archmap_path = out_dir.join("archmap_v2_support_transfer_missing_cell.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(
        invariant["reason"],
        "transfer_model_missing:repair:path:secondary/support:data"
    );
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["evaluator"] != "ag.support-transfer@1"),
        "missing transfer pairing cells must not synthesize zero analytic readings"
    );
}

#[test]
fn cli_analyze_v2_support_transfer_missing_repair_path_row_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-support-transfer-missing-row");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(serde_json::json!({
            "id": "atom:transfer-repair-path-secondary",
            "kind": "semantic",
            "subject": "repair:path:secondary",
            "object": "selected",
            "axis": "transfer",
            "predicate": "repairPath",
            "refs": ["src:repair-path"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:transfer-repair-path-secondary".to_string(),
        ));
    let archmap_path = out_dir.join("archmap_v2_support_transfer_missing_row.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(
        invariant["reason"],
        "transfer_model_missing:repair:path:secondary/support:api,repair:path:secondary/support:data"
    );
}

#[test]
fn cli_analyze_v2_support_transfer_rejects_unknown_target() {
    let out_dir = temp_dir("ag-measurement-support-transfer-unknown-target");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"][1]["object"] = Value::String("support:missing=0.25".to_string());
    let archmap_path = out_dir.join("archmap_v2_support_transfer_unknown_target.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_strict_distance_rejects_not_computed_analytic_invariants() {
    let out_dir = temp_dir("ag-measurement-strict-transfer-missing-cost");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["id"] != "atom:transfer-ground-data")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:transfer-ground-data"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_support_transfer_missing_cost.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--strict-distance",
    ]);
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("not_computed analytic invariants")
            && stderr.contains("violated assumptions"),
        "strict-distance must reject incomplete analytic-only transfer evidence\n{stderr}"
    );
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(invariant["status"], "not_computed");
}

#[test]
fn cli_analyze_v2_support_transfer_rejects_duplicate_pairings() {
    let out_dir = temp_dir("ag-measurement-support-transfer-duplicate");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    let mut duplicate = archmap["atoms"][1].clone();
    duplicate["id"] = Value::String("atom:transfer-path-api-duplicate".to_string());
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(duplicate);
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:transfer-path-api-duplicate".to_string(),
        ));
    let archmap_path = out_dir.join("archmap_v2_support_transfer_duplicate.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_support_transfer_rejects_non_finite_values() {
    let out_dir = temp_dir("ag-measurement-support-transfer-nan");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"][1]["object"] = Value::String("support:api=NaN".to_string());
    let archmap_path = out_dir.join("archmap_v2_support_transfer_nan.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_support_transfer_rejects_malformed_profile_selector() {
    let out_dir = temp_dir("ag-measurement-support-transfer-bad-profile");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_transfer.json"));
    policy["measurementProfiles"][0]["resolutionSelector"] =
        Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_transfer_bad_profile.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_support_transfer.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_support_transfer_missing_ground_cost_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-support-transfer-missing-cost");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["id"] != "atom:transfer-ground-data")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:transfer-ground-data"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_support_transfer_missing_cost.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["reason"], "missing_ground_costs:support:data");
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_rejects_unknown_cell() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-unknown-cell");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    archmap["atoms"][0]["subject"] = Value::String("cell:missing".to_string());
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_unknown_cell.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_locks_archsig_viewer_gluing_geometry_golden_ux_fixture() {
    let root = ag_measurement_root();
    let manifest = read_json(&root.join("archsig_viewer_gluing_geometry_golden_ux.json"));
    assert_eq!(
        manifest["schema"],
        "archsig-viewer-gluing-geometry-golden-ux/v1"
    );

    let viewer_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("viewer/archsig-atom-viewer.html");
    let viewer_html = fs::read_to_string(&viewer_path).expect("viewer html can be read");
    for required in manifest["requiredViewerFunctions"]
        .as_array()
        .expect("requiredViewerFunctions is array")
    {
        let required = required
            .as_str()
            .expect("required viewer function is string");
        assert!(
            viewer_html.contains(required),
            "gluing geometry golden UX fixture requires viewer function {required}"
        );
    }

    for case in manifest["cases"].as_array().expect("cases is array") {
        let case_id = case["caseId"].as_str().expect("caseId is string");
        let out_dir = temp_dir(&format!("ag-gluing-golden-ux-{case_id}"));
        let archmap_path = if case["mutations"].is_array() {
            let mut archmap =
                read_json(&root.join(case["archmap"].as_str().expect("archmap is string")));
            for mutation in case["mutations"].as_array().expect("mutations is array") {
                let atom_id = mutation["atomId"].as_str().expect("atomId is string");
                let field = mutation["field"].as_str().expect("field is string");
                let value = mutation["value"].clone();
                let atom = archmap["atoms"]
                    .as_array_mut()
                    .expect("atoms is array")
                    .iter_mut()
                    .find(|atom| atom["id"] == atom_id)
                    .unwrap_or_else(|| panic!("{case_id} missing mutation atom {atom_id}"));
                atom[field] = value;
            }
            let archmap_path = out_dir.join(format!("{case_id}.archmap.json"));
            fs::write(
                &archmap_path,
                serde_json::to_vec_pretty(&archmap).expect("mutated archmap serializes"),
            )
            .expect("mutated archmap can be written");
            archmap_path
        } else {
            root.join(case["archmap"].as_str().expect("archmap is string"))
        };
        run_sig0(&[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join(case["lawPolicy"].as_str().expect("lawPolicy is string"))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ]);

        let report = read_json(&out_dir.join("archsig-insight-report.json"));
        let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
        let gluing = &report["gluingGeometry"];
        assert_eq!(gluing["schema"], "archsig-viewer-gluing-geometry/v1");
        assert_eq!(
            viewer["aatGeometryOverlays"]["gluingGeometry"], report["gluingGeometry"],
            "{case_id} viewer data must expose the same golden gluing geometry projection"
        );

        let expected = &case["expected"];
        if let Some(min_vertices) = expected["minNerveVertices"].as_u64() {
            assert!(
                gluing["nerve"]["vertices"]
                    .as_array()
                    .is_some_and(|items| items.len() >= min_vertices as usize),
                "{case_id} must render expected cover nerve vertices"
            );
        }
        if let Some(min_edges) = expected["minNerveEdges"].as_u64() {
            assert!(
                gluing["nerve"]["edges"]
                    .as_array()
                    .is_some_and(|items| items.len() >= min_edges as usize),
                "{case_id} must render expected cover nerve edges"
            );
        }
        if let Some(min_triangles) = expected["minNerveTriangles"].as_u64() {
            assert!(
                gluing["nerve"]["triangles"]
                    .as_array()
                    .is_some_and(|items| items.len() >= min_triangles as usize),
                "{case_id} must render packet-derived cover nerve triangles"
            );
            assert!(
                gluing["nerve"]["triangleSource"]
                    .as_str()
                    .is_some_and(|text| text.contains("not inferred by the viewer")),
                "{case_id} must keep triangle provenance out of viewer inference"
            );
        }
        if let Some(expected_h2) = expected["h2CoherenceVisualized"].as_bool() {
            assert_eq!(
                gluing["nerve"]["h2CoherenceVisualized"].as_bool(),
                Some(expected_h2),
                "{case_id} must preserve H2 silence boundary"
            );
        }
        if let Some(min_support_edges) = expected["minCocycleSupportEdges"].as_u64() {
            assert!(
                gluing["cocycleRibbon"]["supportEdges"]
                    .as_array()
                    .is_some_and(|items| items.len() >= min_support_edges as usize),
                "{case_id} must render cocycle support ribbon edges"
            );
        }
        if let Some(max_support_edges) = expected["maxCocycleSupportEdges"].as_u64() {
            let support_edges = gluing["cocycleRibbon"]["supportEdges"]
                .as_array()
                .expect("cocycle support edges are array");
            assert!(
                support_edges.len() <= max_support_edges as usize,
                "{case_id} must cap cocycle support ribbon edges"
            );
            assert_eq!(
                gluing["renderLimits"]["cocycleSupportEdges"].as_u64(),
                Some(max_support_edges),
                "{case_id} must expose the cocycle support edge render limit"
            );
            assert!(
                gluing["omittedGeometryCounts"]["cocycleSupportEdges"].is_u64(),
                "{case_id} must expose the cocycle support edge omitted count"
            );
        }
        if let Some(closure_gap_visible) = expected["closureGapVisible"].as_bool() {
            assert_eq!(
                gluing["cocycleRibbon"]["closureGapEncoding"]["visible"].as_bool(),
                Some(closure_gap_visible),
                "{case_id} must preserve fixed closure-gap visual encoding"
            );
        }
        if let Some(min_cages) = expected["minForbiddenCages"].as_u64() {
            assert!(
                gluing["forbiddenCages"]
                    .as_array()
                    .is_some_and(|items| items.len() >= min_cages as usize),
                "{case_id} must render forbidden support cages"
            );
        }
        if let Some(min_morphs) = expected["minRepairMorphs"].as_u64() {
            assert!(
                gluing["repairMorphs"]
                    .as_array()
                    .is_some_and(|items| items.len() >= min_morphs as usize),
                "{case_id} must render repair morph lower-bound paths"
            );
        }
        if let Some(min_refs) = expected["minRepairFromCageRefs"].as_u64() {
            assert!(
                gluing["repairMorphs"]
                    .as_array()
                    .is_some_and(|items| items.iter().any(|item| item["fromCageRefs"]
                        .as_array()
                        .is_some_and(|refs| refs.len() >= min_refs as usize)
                        && item["fromAtomRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty()))),
                "{case_id} repair morphs must be grounded in related forbidden cage support"
            );
        }
        if let Some(min_rows) = expected["minCurvatureFieldRows"].as_u64() {
            assert!(
                gluing["locusField"]["fieldRows"]
                    .as_array()
                    .is_some_and(|items| items.len() >= min_rows as usize),
                "{case_id} must render curvature support / mass field rows"
            );
        }
        if let Some(min_regions) = expected["minBlockedRegions"].as_u64() {
            assert!(
                gluing["locusField"]["blockedRegions"]
                    .as_array()
                    .is_some_and(|items| items.len() >= min_regions as usize),
                "{case_id} must keep blocked/unmeasured locus visibly separate"
            );
        }
        if let Some(min_rows) = expected["minAnalyticMassRows"].as_u64() {
            assert!(
                gluing["locusField"]["fieldRows"]
                    .as_array()
                    .is_some_and(|items| items
                        .iter()
                        .filter(|item| item["harmonicMass"].is_number()
                            && item["sourceReadingRef"].as_str().is_some())
                        .count()
                        >= min_rows as usize),
                "{case_id} must project analytic harmonic mass into the height field"
            );
        }
        if let Some(min_glyphs) = expected["minBlockedAnchorGlyphs"].as_u64() {
            assert!(
                gluing["atomGlyphs"].as_array().is_some_and(|items| items
                    .iter()
                    .filter(|item| {
                        item["semanticAnchor"] == "blocked_missing_anchor"
                            && item["shapeRole"] == "blocked_anchor_glyph"
                            && item["fiberShapeRole"].as_str().is_some()
                            && item["carrierColorRole"].as_str().is_some()
                    })
                    .count()
                    >= min_glyphs as usize),
                "{case_id} must render semantic-anchor gaps as blocker glyphs with fiber/carrier roles"
            );
        }
        assert!(
            viewer["aatGeometryOverlays"]["omittedGeometryCounts"].is_object(),
            "{case_id} must expose geometry omitted counts to the viewer payload"
        );

        let report_text = serde_json::to_string(&report).expect("report serializes");
        for required in expected["requiredNonClaims"]
            .as_array()
            .into_iter()
            .flatten()
        {
            let required = required.as_str().expect("required non-claim is string");
            assert!(
                report_text.contains(required),
                "{case_id} must keep non-claim boundary text {required}"
            );
        }

        for scene_id in expected["requiredScenes"].as_array().into_iter().flatten() {
            let scene_id = scene_id.as_str().expect("required scene id is string");
            let scene = viewer["viewerVisualScenes"]
                .as_array()
                .expect("viewerVisualScenes is array")
                .iter()
                .find(|scene| scene["sceneId"] == scene_id)
                .unwrap_or_else(|| panic!("{case_id} missing scene {scene_id}"));
            assert_eq!(
                scene["axisMappingImplemented"].as_bool(),
                Some(true),
                "{case_id} scene {scene_id} must use axisMapping as geometry-driving"
            );
            assert_eq!(
                scene["axisMetricBindings"]["x"].as_str(),
                Some("xValue"),
                "{case_id} scene {scene_id} must declare the renderer metric key for the X axis"
            );
            assert_eq!(
                scene["axisMetricBindings"]["y"].as_str(),
                Some("yValue"),
                "{case_id} scene {scene_id} must declare the renderer metric key for the Y axis"
            );
            assert_eq!(
                scene["axisMetricBindings"]["z"].as_str(),
                Some("zValue"),
                "{case_id} scene {scene_id} must declare the renderer metric key for the Z axis"
            );
            assert!(
                scene["visualEncodingLegend"]
                    .as_array()
                    .is_some_and(|items| items.len() >= 5),
                "{case_id} scene {scene_id} must expose complete visual encoding legend"
            );
        }
    }
}

#[test]
fn cli_locks_ag_measurement_cech_h1_visible_golden_fixture() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo_root = crate_root
        .parent()
        .and_then(Path::parent)
        .expect("crate root is tools/archsig inside repo");
    let fixture = read_json(&ag_measurement_root().join("archmap_v2_cech_h1_visible.json"));
    assert_eq!(fixture["schema"], "archmap/v2");
    assert_eq!(fixture["id"], "ag-measurement-cech-h1-visible-fixture");
    assert!(
        fixture["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .any(|atom| atom["axis"] == "cech" && atom["predicate"] == "mismatch"),
        "AG golden fixture must contain an explicit Cech mismatch atom"
    );

    let golden_corpus = fs::read_to_string(repo_root.join("docs/tool/golden_corpus.md"))
        .expect("golden corpus docs are readable");
    for snippet in [
        "archmap_v2_cech_h1_visible.json",
        "cli_analyze_v2_cech_h1_visible_fixture_measures_nonzero",
        "witness-blind / H1-visible",
    ] {
        assert!(
            golden_corpus.contains(snippet),
            "AG golden corpus docs must mention {snippet}"
        );
    }
}

#[test]
fn cli_locks_ag_measurement_square_free_golden_fixture() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo_root = crate_root
        .parent()
        .and_then(Path::parent)
        .expect("crate root is tools/archsig inside repo");
    let fixture = read_json(&ag_measurement_root().join("archmap_v2_square_free_repair.json"));
    assert_eq!(fixture["schema"], "archmap/v2");
    assert_eq!(fixture["id"], "ag-measurement-square-free-repair-fixture");
    assert!(
        fixture["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .any(|atom| atom["axis"] == "square-free" && atom["predicate"] == "nsdepthCertificate"),
        "AG square-free fixture must contain an explicit NSdepth certificate atom"
    );

    let golden_corpus = fs::read_to_string(repo_root.join("docs/tool/golden_corpus.md"))
        .expect("golden corpus docs are readable");
    for snippet in [
        "archmap_v2_square_free_repair.json",
        "law_policy_square_free.json",
        "cli_analyze_v2_square_free_repair_outputs_hitting_sets_and_nsdepth",
        "cli_analyze_v2_square_free_without_certificate_returns_unknown",
    ] {
        assert!(
            golden_corpus.contains(snippet),
            "AG golden corpus docs must mention {snippet}"
        );
    }
}

#[test]
fn cli_locks_ag_measurement_law_conflict_tor_golden_fixture() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo_root = crate_root
        .parent()
        .and_then(Path::parent)
        .expect("crate root is tools/archsig inside repo");
    let fixture = read_json(&ag_measurement_root().join("archmap_v2_law_conflict_tor.json"));
    assert_eq!(fixture["schema"], "archmap/v2");
    assert_eq!(fixture["id"], "ag-measurement-law-conflict-tor-fixture");
    assert!(
        fixture["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .any(|atom| atom["axis"] == "tor" && atom["predicate"] == "commonAmbient"),
        "AG Tor fixture must contain an explicit common ambient atom"
    );

    let golden_corpus = fs::read_to_string(repo_root.join("docs/tool/golden_corpus.md"))
        .expect("golden corpus docs are readable");
    for snippet in [
        "archmap_v2_law_conflict_tor.json",
        "law_policy_tor.json",
        "cli_analyze_v2_law_conflict_tor_outputs_conflict_classes",
        "cli_analyze_v2_law_conflict_tor_without_common_ambient_is_not_computed",
    ] {
        assert!(
            golden_corpus.contains(snippet),
            "AG golden corpus docs must mention {snippet}"
        );
    }
}

#[test]
fn cli_locks_ag_measurement_sheaf_laplacian_golden_fixture() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo_root = crate_root
        .parent()
        .and_then(Path::parent)
        .expect("crate root is tools/archsig inside repo");
    let fixture = read_json(&ag_measurement_root().join("archmap_v2_sheaf_laplacian.json"));
    assert_eq!(fixture["schema"], "archmap/v2");
    assert_eq!(fixture["id"], "ag-measurement-sheaf-laplacian-fixture");
    assert!(
        fixture["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .any(|atom| atom["axis"] == "laplacian" && atom["predicate"] == "cellularBoundary"),
        "AG Laplacian fixture must contain an explicit cellular boundary atom"
    );

    let golden_corpus = fs::read_to_string(repo_root.join("docs/tool/golden_corpus.md"))
        .expect("golden corpus docs are readable");
    for snippet in [
        "archmap_v2_sheaf_laplacian.json",
        "law_policy_laplacian.json",
        "cli_analyze_v2_sheaf_laplacian_outputs_analytic_hodge_reading",
        "near-flat analytic values are not structural lawfulness verdicts",
    ] {
        assert!(
            golden_corpus.contains(snippet),
            "AG golden corpus docs must mention {snippet}"
        );
    }
}

#[test]
fn cli_locks_ag_measurement_period_stokes_golden_fixture() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo_root = crate_root
        .parent()
        .and_then(Path::parent)
        .expect("crate root is tools/archsig inside repo");
    let fixture = read_json(&ag_measurement_root().join("archmap_v2_period_stokes.json"));
    assert_eq!(fixture["schema"], "archmap/v2");
    assert_eq!(fixture["id"], "ag-measurement-period-stokes-fixture");
    assert!(
        fixture["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .any(|atom| atom["axis"] == "period" && atom["predicate"] == "boundaryPeriod"),
        "AG Period fixture must contain an explicit Stokes boundary-period atom"
    );

    let golden_corpus = fs::read_to_string(repo_root.join("docs/tool/golden_corpus.md"))
        .expect("golden corpus docs are readable");
    for snippet in [
        "archmap_v2_period_stokes.json",
        "law_policy_period.json",
        "cli_analyze_v2_period_stokes_outputs_pairing_and_audit_reading",
        "model-relative analytic reading",
    ] {
        assert!(
            golden_corpus.contains(snippet),
            "AG golden corpus docs must mention {snippet}"
        );
    }
}

#[test]
fn cli_locks_ag_measurement_support_transfer_golden_fixture() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo_root = crate_root
        .parent()
        .and_then(Path::parent)
        .expect("crate root is tools/archsig inside repo");
    let fixture = read_json(&ag_measurement_root().join("archmap_v2_support_transfer.json"));
    assert_eq!(fixture["schema"], "archmap/v2");
    assert_eq!(fixture["id"], "ag-measurement-support-transfer-fixture");
    assert!(
        fixture["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .any(|atom| atom["axis"] == "transfer" && atom["predicate"] == "groundCost"),
        "AG Transfer fixture must contain explicit transfer ground-cost atoms"
    );

    let golden_corpus = fs::read_to_string(repo_root.join("docs/tool/golden_corpus.md"))
        .expect("golden corpus docs are readable");
    for snippet in [
        "archmap_v2_support_transfer.json",
        "law_policy_transfer.json",
        "cli_analyze_v2_support_transfer_outputs_residue_and_wasserstein_cost",
        "global repair safety",
    ] {
        assert!(
            golden_corpus.contains(snippet),
            "AG golden corpus docs must mention {snippet}"
        );
    }
}

#[test]
fn cli_analyze_v2_strict_distance_allows_implemented_analytic_only_evaluators() {
    let out_dir = temp_dir("ag-measurement-strict-analytic-only");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_support_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--strict-distance",
    ]);

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    );
    assert_eq!(summary["structuralVerdictSummary"]["rowCount"], 0);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .any(|reading| reading["evaluator"] == "ag.support-transfer@1")
    );
}

#[test]
fn cli_analyze_v2_rejects_unresolved_measurement_profile_refs() {
    let out_dir = temp_dir("ag-measurement-bad-profile");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_ag.json"));
    policy["measurementProfiles"][0]["coverRef"] = Value::String("cover:missing".to_string());
    let policy_path = out_dir.join("law_policy_bad_cover.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_rejects_archmap_v2_context_restriction_cycle() {
    let out_dir = temp_dir("ag-measurement-context-cycle");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    archmap["contexts"][2]["restrictsTo"] =
        Value::Array(vec![Value::String("ctx:order".to_string())]);
    let archmap_path = out_dir.join("archmap_v2_cycle.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");
    let report = out_dir.join("archmap-validation.json");

    run_sig0_expect_code(
        &[
            "archmap",
            "--input",
            archmap_path.to_str().expect("path is utf-8"),
            "--out",
            report.to_str().expect("path is utf-8"),
        ],
        1,
    );

    let json = read_json(&report);
    assert!(
        json["checks"].as_array().unwrap().iter().any(|check| {
            check["id"] == "archmap-v2-context-poset-refs" && check["result"] == "fail"
        }),
        "context restriction cycle must fail finite-poset validation"
    );
}

#[test]
fn archmap_v2_normalize_is_byte_deterministic() {
    let out_dir_a = temp_dir("ag-normalize-a");
    let out_dir_b = temp_dir("ag-normalize-b");
    let root = ag_measurement_root();

    for out_dir in [&out_dir_a, &out_dir_b] {
        run_sig0(&[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ]);
    }

    let first = fs::read(out_dir_a.join("normalized-archmap.json")).expect("first output exists");
    let second = fs::read(out_dir_b.join("normalized-archmap.json")).expect("second output exists");
    assert_eq!(
        first, second,
        "same ArchMap v2 input must normalize to byte-identical output"
    );
}

#[test]
fn archmap_v2_cross_doctrine_comparison_is_not_comparable() {
    let root = ag_measurement_root();
    let left_value = read_json(&root.join("archmap_v2.json"));
    let mut right_value = left_value.clone();
    right_value["extractionDoctrineRef"]["fingerprint"] =
        Value::String("sha256:other-doctrine".to_string());
    let left: ArchMapDocumentV2 = serde_json::from_value(left_value).expect("left archmap parses");
    let right: ArchMapDocumentV2 =
        serde_json::from_value(right_value).expect("right archmap parses");

    let result = compare_archmap_v2_doctrine(&left, &right);
    assert_eq!(result["status"], "not_comparable");
    assert_eq!(result["reason"], "cross_doctrine_not_comparable");
}

#[test]
fn cli_validates_archmap_v1_atom_contract() {
    let out_dir = temp_dir("archmap-v1-validation");
    let root = archmap_v1_root();
    let report = out_dir.join("archmap-validation.json");

    run_sig0(&[
        "archmap",
        "--input",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "archmap-validation-report-v1");
    assert_eq!(json["inputSchema"], "archmap/v1");
    assert_eq!(json["summary"]["result"], "pass");
    assert_eq!(json["summary"]["atomCount"], 3);
    assert_eq!(json["summary"]["moleculeCount"], 1);
}

#[test]
fn cli_locks_archmap_v1_output_replacement_golden_corpus_manifest() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let corpus = read_json(
        &crate_root.join("tests/fixtures/archmap_v1/output_replacement_golden_corpus.json"),
    );
    assert_eq!(
        corpus["schemaVersion"],
        "archsig-v1-output-replacement-golden-corpus/v1"
    );

    let complete_manifest_path = corpus["completeAcceptanceManifestPath"]
        .as_str()
        .expect("complete acceptance manifest path is present");
    let complete_manifest = read_json(&crate_root.join(complete_manifest_path));
    assert_eq!(
        complete_manifest["schemaVersion"],
        "archsig-v1-output-replacement-acceptance-manifest/v1"
    );
    assert_eq!(
        complete_manifest["legacyFixtureBoundary"]["currentCompletionEvidence"].as_bool(),
        Some(false),
        "v0 complete acceptance fixture must be quarantined from current completion evidence"
    );

    let known_executable_tests = BTreeSet::from([
        "cli_analyze_v1_emit_raw_artifacts_writes_typed_packet_detail_and_handoff",
        "practical_rust_service_example_runs_v1_analyze",
        "cli_analyze_v1_writes_typed_evaluator_results",
        "cli_analyze_v1_spectrum_detects_nonzero_curvature_from_typed_violation",
        "cli_analyze_v1_homotopy_surfaces_zero_nonzero_and_missing_filler",
        "cli_analyze_v1_structural_reading_review_surface_uses_typed_refs",
        "cli_analyze_v1_removed_field_only_artifacts_do_not_become_measured_results",
        "cli_analyze_v1_label_only_semantic_does_not_become_measured_replacement",
        "cli_analyze_v1_schema_only_input_does_not_become_measured_replacement",
        "cli_rejects_archmap_v1_unresolved_source_ref",
        "cli_analyze_v1_marks_incomplete_molecule_candidate_blocked",
        "cli_analyze_v1_strict_distance_rejects_missing_distance_profile_ref",
        "cli_analyze_v1_strict_distance_rejects_blocked_typed_results",
        "cli_analyze_v1_strict_distance_rejects_partial_canonical_family_bundle",
        "cli_analyze_v1_validation_failure_removes_stale_success_artifacts",
    ]);
    let positive_cases = corpus["positiveCases"]
        .as_array()
        .expect("positive cases are listed");
    let negative_cases = corpus["negativeCases"]
        .as_array()
        .expect("negative cases are listed");
    let positive_families = positive_cases
        .iter()
        .map(|case| {
            case["family"]
                .as_str()
                .expect("positive case family is present")
                .to_string()
        })
        .collect::<BTreeSet<_>>();
    let negative_families = negative_cases
        .iter()
        .map(|case| {
            case["family"]
                .as_str()
                .expect("negative case family is present")
                .to_string()
        })
        .collect::<BTreeSet<_>>();

    for family in complete_manifest["requiredPositiveFamilies"]
        .as_array()
        .expect("required positive families are listed")
    {
        let family = family.as_str().expect("family is string");
        assert!(
            positive_families.contains(family),
            "v1 golden corpus must include positive family {family}"
        );
    }
    for family in complete_manifest["requiredNegativeFamilies"]
        .as_array()
        .expect("required negative families are listed")
    {
        let family = family.as_str().expect("family is string");
        assert!(
            negative_families.contains(family),
            "v1 golden corpus must include negative family {family}"
        );
    }

    for case in positive_cases.iter().chain(negative_cases.iter()) {
        let executable_test = case["executableTest"]
            .as_str()
            .expect("golden corpus case must name the executable regression test");
        assert!(
            known_executable_tests.contains(executable_test),
            "golden corpus case references unknown executable regression test {executable_test}"
        );
        for field in ["archmapPath", "lawPolicyPath"] {
            if let Some(path) = case[field].as_str() {
                assert_repo_local_fixture_path(path);
                assert!(
                    crate_root.join(path).is_file(),
                    "golden corpus fixture path must exist: {path}"
                );
            }
        }
        if let Some(paths) = case["fixturePaths"].as_array() {
            for path in paths {
                let path = path.as_str().expect("fixture path is string");
                assert_repo_local_fixture_path(path);
                assert!(
                    crate_root.join(path).is_file(),
                    "golden corpus fixture path must exist: {path}"
                );
            }
        }
    }

    let required_surfaces = complete_manifest["requiredOutputSurfaces"]
        .as_array()
        .expect("required output surfaces are listed");
    let positive_case_surfaces = positive_cases
        .iter()
        .flat_map(|case| {
            case["requiredOutputSurfaces"]
                .as_array()
                .into_iter()
                .flatten()
        })
        .filter_map(Value::as_str)
        .collect::<BTreeSet<_>>();
    for surface in required_surfaces {
        let surface = surface.as_str().expect("surface is string");
        assert!(
            positive_case_surfaces.contains(surface),
            "v1 output replacement corpus positive cases must lock output surface {surface}"
        );
    }
}

#[test]
fn cli_locks_part4_output_contract_docs_skill_and_website_smoke() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo_root = crate_root
        .parent()
        .and_then(Path::parent)
        .expect("crate root is tools/archsig inside repo");

    for (path, required_snippets) in [
        (
            "docs/tool/golden_corpus.md",
            &[
                "distanceInsights",
                "distanceDiagnosis.homotopyInsights",
                "homotopyDistanceReadings",
                "representationMetricReadings",
                "partial canonical Part IV family",
            ][..],
        ),
        (
            "tools/archsig/skills/archsig-reader/SKILL.md",
            &[
                "distanceInsights",
                "distanceActionQueue",
                "Distance Diagnosis",
            ][..],
        ),
        (
            "tools/archsig/skills/archsig-reader/references/output-reading-guide.md",
            &[
                "distanceInsights",
                "distanceActionQueue",
                "homotopyDistanceReadings",
            ][..],
        ),
        (
            "website/archsig/manual/index.html",
            &[
                "architecture-distance.json",
                "distanceInsights",
                "homotopyDistanceReadings",
            ][..],
        ),
        (
            "website/archsig/reference/index.html",
            &[
                "architecture-distance.json",
                "archsig-architecture-distance/v1",
                "--strict-distance",
            ][..],
        ),
        (
            "tools/archsig/examples/practical-rust-service/README.md",
            &[
                "architecture-distance.json",
                "Strict distance guard",
                "incomplete canonical distance family states",
            ][..],
        ),
    ] {
        let body = fs::read_to_string(repo_root.join(path))
            .unwrap_or_else(|error| panic!("must read {path}: {error}"));
        for snippet in required_snippets {
            assert!(
                body.contains(snippet),
                "{path} must mention Part IV output contract snippet {snippet}"
            );
        }
    }
}

fn assert_repo_local_fixture_path(path: &str) {
    let path = Path::new(path);
    assert!(
        path.is_relative()
            && path
                .components()
                .all(|component| !matches!(component, Component::ParentDir | Component::RootDir)),
        "fixture path must stay repo-local without parent traversal: {}",
        path.display()
    );
}

#[test]
fn cli_rejects_v0_archmap_as_current_runtime_input() {
    let out_dir = temp_dir("archmap-v0-runtime-rejection");
    let root = fixture_root();
    let report = out_dir.join("archmap-validation.json");

    let output = run_sig0_output(&[
        "archmap",
        "--input",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--input must have schemaVersion archmap/v1"));
    assert!(
        !report.exists(),
        "v0 ArchMap rejection must not be reported as a current validation artifact"
    );
}

#[test]
fn cli_rejects_v0_law_policy_as_current_runtime_input() {
    let out_dir = temp_dir("law-policy-v0-runtime-rejection");
    let root = fixture_root();
    let report = out_dir.join("law-policy-validation.json");

    let output = run_sig0_output(&[
        "law-policy",
        "--input",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--input must have schemaVersion law-policy/v1"));
    assert!(
        !report.exists(),
        "v0 LawPolicy rejection must not be reported as a current validation artifact"
    );
}

#[test]
fn cli_analyze_rejects_v0_archmap_and_law_policy_runtime_inputs() {
    let out_dir = temp_dir("analyze-v0-runtime-rejection");
    let root = fixture_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--input must have schemaVersion archmap/v1"));
    assert!(
        !out_dir.join("archsig-analysis-summary.json").exists(),
        "v0 analyze rejection must not emit current success artifacts"
    );
}

#[test]
fn cli_pr_review_rejects_v0_archmap_and_law_policy_runtime_inputs() {
    let out_dir = temp_dir("pr-review-v0-runtime-rejection");
    let root = fixture_root();
    let review = pr_review_root();
    let report = out_dir.join("archsig-pr-review.json");

    let output = run_sig0_output(&[
        "pr-review",
        "--base-archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--delta-archmap",
        review
            .join("archmap_delta_v1_refs.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--base-archmap must have schemaVersion archmap/v1"));
    assert!(!report.exists());
}

#[test]
fn cli_analyze_v1_writes_normalized_archmap_for_valid_input() {
    let out_dir = temp_dir("analyze-v1-normalized");
    let root = archmap_v1_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(output.status.success());
    let json = read_json(&out_dir.join("normalized-archmap.json"));
    assert_eq!(json["schema"], "normalized-archmap/v1");
    assert_eq!(json["normalizerId"], "archmap-v1-aat-presentation@1");
    assert_eq!(json["summary"]["atomCount"], 3);
    assert_eq!(json["summary"]["normalizedAtomCount"], 3);
    assert_eq!(json["summary"]["generatedMoleculeCandidateCount"], 1);
    assert!(
        json["atoms"]
            .as_array()
            .is_some_and(|atoms| atoms.iter().any(|atom| atom["sourceAtomId"]
                == "atom:reservation-effect"
                && atom["atomKind"] == "effect"
                && atom["axis"] == "semantic"
                && atom["predicate"]["constructor"] == "effect"
                && atom["shapeCoordinateStatus"] == "resolved"
                && atom["valenceTemplateId"] == "valence:effect@1"))
    );
}

#[test]
fn cli_analyze_v1_writes_typed_evaluator_results() {
    let out_dir = temp_dir("analyze-v1-typed-results");
    let root = archmap_v1_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--emit-raw-artifacts",
    ]);

    assert!(output.status.success());
    let json = read_json(&out_dir.join("typed-evaluator-results.json"));
    assert_eq!(json["schema"], "typed-evaluator-results/v1");
    assert_eq!(json["summary"]["resultCount"], 6);
    assert!(
        json["summary"]["measuredPassCount"].as_u64().unwrap_or(0) > 0
            || json["summary"]["measuredViolationCount"]
                .as_u64()
                .unwrap_or(0)
                > 0
    );
    assert!(json["results"].as_array().is_some_and(|results| {
        results.iter().any(|result| {
            result["law"] == "solid.single-responsibility"
                && result["status"] == "measuredPass"
                && result["supportAtomRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
                && result["basisRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
        })
    }));
    assert!(
        json["positiveBoundedConclusions"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    );
    assert!(
        json["positiveBoundedConclusions"]
            .as_array()
            .is_some_and(|items| items
                .iter()
                .any(|item| item.as_str().is_some_and(|text| text
                    .starts_with("ACCEPTABLE_UNDER_EVIDENCE_CONTRACT")
                    || text.starts_with("SELECTED_VIOLATION_MEASURED_UNDER_EVIDENCE_CONTRACT"))))
    );
}

#[test]
fn cli_analyze_v1_marks_incomplete_molecule_candidate_blocked() {
    let out_dir = temp_dir("analyze-v1-blocked-molecule");
    let root = archmap_v1_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_blocked_molecule.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--emit-raw-artifacts",
    ]);

    assert!(output.status.success());
    let json = read_json(&out_dir.join("normalized-archmap.json"));
    assert_eq!(json["summary"]["blockedMoleculeCandidateCount"], 1);
    assert!(
        json["molecules"]
            .as_array()
            .is_some_and(|molecules| molecules
                .iter()
                .any(|molecule| molecule["sourceMoleculeId"] == "mol:single-atom"
                    && molecule["generatedMoleculeCandidateStatus"] == "blockedForNormalization"
                    && molecule["compositionStatus"] == "blockedForNormalization"))
    );
    let typed = read_json(&out_dir.join("typed-evaluator-results.json"));
    assert_eq!(typed["summary"]["blockedCount"], 6);
    assert!(
        typed["results"]
            .as_array()
            .is_some_and(|results| { results.iter().all(|result| result["status"] == "blocked") })
    );
    assert!(
        typed["replacementEvaluatorResults"]
            .as_array()
            .is_some_and(|results| {
                results.iter().any(|result| {
                    result["replacementId"] == "missing-evidence.reading@1"
                        && result["replacementForV0Field"] == "observationGaps"
                        && result["status"] == "blocked"
                        && result["blockerReason"]
                            .as_str()
                            .is_some_and(|reason| reason.contains("selected evaluator result"))
                })
            }),
        "missing evidence replacement must be derived from blocked evaluator requirements"
    );
    let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    assert!(
        packet["generatedObstructions"]
            .as_array()
            .is_some_and(|items| {
                items.len() == 6
                    && items.iter().all(|item| {
                        item["obstructionKind"] == "blockedObstructionCandidate"
                            && item["typedEvaluatorResultRef"]
                                .as_str()
                                .is_some_and(|reference| packet.pointer(reference).is_some())
                            && item["generatedLawInputRef"]
                                .as_str()
                                .is_some_and(|reference| packet.pointer(reference).is_some())
                            && item["signatureAxisRef"]
                                .as_str()
                                .is_some_and(|reference| packet.pointer(reference).is_some())
                    })
            }),
        "blocked typed evaluator results must materialize generated obstruction candidates"
    );
    assert!(
        packet["generatedRepairTargets"]
            .as_array()
            .is_some_and(|items| {
                items.len() == 6
                    && items.iter().all(|item| {
                        item["targetKind"] == "collectMissingEvidence"
                            && item["registryBasisRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && item["basisRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && item["signatureAxisRef"]
                                .as_str()
                                .is_some_and(|reference| packet.pointer(reference).is_some())
                            && item["localStatus"] == "locallyBlocked"
                            && item["generatedObstructionRef"]
                                .as_str()
                                .is_some_and(|reference| packet.pointer(reference).is_some())
                            && item["typedEvaluatorResultRef"]
                                .as_str()
                                .is_some_and(|reference| packet.pointer(reference).is_some())
                    })
            }),
        "blocked generated obstructions must materialize collectMissingEvidence repair targets"
    );
    assert_eq!(
        packet["architectureSpectrumReport"]["status"].as_str(),
        Some("needsCoverageReview")
    );
    assert!(
        packet["architectureSpectrumReport"]["coverageGaps"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && packet["curvatureSupportReadings"]
                .as_array()
                .is_some_and(|items| items.iter().all(|reading| {
                    reading["curvatureValue"]["status"] == "blockedByCoverageGap"
                        && reading["coverageGapRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })),
        "blocked typed evaluator results must become coverage gaps, not measured zero spectrum"
    );
    let architecture_distance = read_json(&out_dir.join("architecture-distance.json"));
    assert!(
        architecture_distance["distanceDiagnosis"]["curvatureInsights"]["blockedSupportCount"]
            .as_u64()
            == Some(6)
            && architecture_distance["distanceDiagnosis"]["curvatureInsights"]
                ["measuredZeroSupportCount"]
                .as_u64()
                == Some(0)
            && architecture_distance["obstructionMeasureReadings"]
                .as_array()
                .is_some_and(|items| {
                    items.len() == 6
                        && items.iter().all(|reading| {
                            reading["status"] == "blocked"
                                && reading["obstructionMeasure"]["measuredValue"].is_null()
                                && reading["coverageGapRefs"]
                                    .as_array()
                                    .is_some_and(|refs| !refs.is_empty())
                        })
        }),
        "primary curvature insights must preserve blocked support as blocked, not measured zero"
    );
    assert_eq!(
        architecture_distance["distanceInsights"]["policyObstructionReading"]["status"].as_str(),
        Some("selectedPolicyObstructionBlocked"),
        "blocked selected signature-distance axes must not be reported as policy obstruction absence"
    );
    let blocked_evidence_count = architecture_distance["distanceInsights"]["blockedEvidence"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    assert!(
        blocked_evidence_count > 0
            && architecture_distance["distanceInsights"]["distanceActionQueue"]
                .as_array()
                .is_some_and(|actions| {
                    actions
                        .iter()
                        .filter(|action| {
                            action["actionKind"] == "resolve-blocked-distance-evidence"
                        })
                        .count()
                        == blocked_evidence_count
                }),
        "distance action queue must retain every blocked evidence item"
    );
}

#[test]
fn cli_analyze_v1_spectrum_detects_nonzero_curvature_from_typed_violation() {
    let out_dir = temp_dir("analyze-v1-spectrum-nonzero");
    let root = archmap_v1_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_violation.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--emit-raw-artifacts",
    ]);

    assert!(output.status.success());
    let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    assert!(
        packet["curvatureSupportReadings"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|reading| {
                    reading["law"] == "domain.no-direct-infra-dependency"
                        && reading["curvatureValue"]["status"] == "measuredNonzero"
                        && reading["curvatureValue"]["value"] == 1
                        && reading["supportRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && reading["witnessRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
            }),
        "typed measuredViolation must produce nonzero curvature support"
    );
    assert!(
        packet["architectureSpectrumReport"]["topHotspots"]
            .as_array()
            .is_some_and(|hotspots| {
                hotspots.iter().any(|hotspot| {
                    hotspot["curvatureStatus"] == "measuredNonzero"
                        && hotspot["supportReadingRef"]
                            .as_str()
                            .is_some_and(|reference| packet.pointer(reference).is_some())
                })
            }),
        "ArchitectureSpectrumReport must surface nonzero hotspots with refs"
    );
    assert!(
        packet["architectureSpectrumReport"]["recurrentObstructions"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| {
                    item["transferEdgeRefs"].as_array().is_some_and(|refs| {
                        !refs.is_empty()
                            && refs.iter().all(|reference| {
                                packet
                                    .pointer(
                                        reference.as_str().expect("transfer edge ref is string"),
                                    )
                                    .is_some()
                            })
                    })
                })
            }),
        "nonzero transfer support must expose recurrent obstruction refs"
    );
    assert!(
        packet["architectureSpectrumReport"]["topWitnessClusters"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| {
                    item["transferEdgeRefs"].as_array().is_some_and(|refs| {
                        !refs.is_empty()
                            && refs.iter().all(|reference| {
                                packet
                                    .pointer(
                                        reference.as_str().expect("transfer edge ref is string"),
                                    )
                                    .is_some()
                            })
                    })
                })
            }),
        "nonzero witness clusters must reference existing transfer edges"
    );
    let architecture_distance = read_json(&out_dir.join("architecture-distance.json"));
    assert!(
        architecture_distance["operationDistanceReadings"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|reading| {
                    reading["law"] == "domain.no-direct-infra-dependency"
                        && reading["distanceFamily"] == "operationGeometry"
                        && reading["status"] == "blocked"
                        && reading["operationCost"]["status"] == "measured"
                        && reading["operationCost"]["measuredValue"] == 5
                        && reading["operationCost"]["sourceRef"]
                            == "distanceProfile.operationCosts.domain.no-direct-infra-dependency"
                        && reading["operationCost"]["includedInMeasuredValue"] == true
                        && reading["targetDistanceDecrease"]["status"] == "measured"
                        && reading["targetDistanceDecrease"]["measuredValue"] == 1
                        && reading["targetDistanceDecrease"]["signatureDistanceReadingRef"]
                            == "signature-distance:domain-no-direct-infra-dependency"
                        && reading["distanceToSelectedFlat"]["status"] == "measured"
                        && reading["distanceToSelectedFlat"]["measuredValue"] == 0
                        && reading["repairRoute"]["status"]
                            == "candidate-blocked-by-missing-transfer-risk-evidence"
                        && reading["repairRoute"]["preconditionRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && reading["repairRoute"]["transferRiskBlockerRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && reading["sideEffectBound"]["status"] == "blocked"
                        && reading["sideEffectBound"]["measuredValue"].is_null()
                        && reading["sideEffectBound"]["blockerRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
            }),
        "priced measuredViolation operationGeometry must keep operation cost and selected-flat distance while blocking missing side-effect evidence"
    );
    assert!(
        architecture_distance["distanceDiagnosis"]["curvatureInsights"]
            ["measuredNonzeroSupportCount"]
            .as_u64()
            == Some(1)
            && architecture_distance["distanceDiagnosis"]["curvatureInsights"]
                ["topCurvatureSupports"]
                .as_array()
                .is_some_and(|items| {
                    items.iter().any(|support| {
                        support["law"] == "domain.no-direct-infra-dependency"
                            && support["curvatureValue"]["status"] == "measuredNonzero"
                            && support["witnessRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && support["sourceRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                    })
                }),
        "primary curvature insights must expose measured nonzero support with witness and source refs"
    );
    let llm_packet = read_json(&out_dir.join("llm-interpretation-packet.json"));
    assert_eq!(
        llm_packet["architectureSpectrumReportSummary"]["reportRef"].as_str(),
        Some("archsig-analysis-packet.json#/architectureSpectrumReport")
    );
    assert!(
        llm_packet["architectureSpectrumReportSummary"]["topHotspotRefs"]
            .as_array()
            .is_some_and(|refs| {
                refs.iter().any(|reference| {
                    reference == "spectrum-hotspot:domain-no-direct-infra-dependency"
                })
            }),
        "LLM spectrum summary must keep nonzero hotspot visible"
    );
    let validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert!(
        validation["checks"].as_array().is_some_and(|checks| {
            checks.iter().any(|check| {
                check["checkId"] == "archsig.v1.architectureSpectrumReportSurface"
                    && check["result"] == "pass"
            })
        }),
        "analysis validation must lock v1 spectrum surface"
    );
}

#[test]
fn cli_analyze_v1_homotopy_surfaces_zero_nonzero_and_missing_filler() {
    let root = archmap_v1_root();
    for (fixture, expected_status, expected_loop_status) in [
        (
            "archmap_homotopy_zero.json",
            "measuredZeroWithinSelectedFillings",
            "measuredZero",
        ),
        (
            "archmap_homotopy_nonzero.json",
            "actionable",
            "measuredNonzero",
        ),
        (
            "archmap_homotopy_unmeasured_axis.json",
            "needsHomotopyEvidenceReview",
            "unmeasuredSelectedAxisDifference",
        ),
        (
            "archmap_homotopy_hole.json",
            "needsHomotopyEvidenceReview",
            "blockedByMissingFiller",
        ),
    ] {
        let out_dir = temp_dir(&format!("analyze-v1-homotopy-{expected_loop_status}"));
        let output = run_sig0_output(&[
            "analyze",
            "--archmap",
            root.join(fixture).to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
            "--emit-raw-artifacts",
        ]);

        assert!(output.status.success());
        let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
        let architecture_distance = read_json(&out_dir.join("architecture-distance.json"));
        let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
        let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
        let llm_packet = read_json(&out_dir.join("llm-interpretation-packet.json"));
        assert_eq!(
            packet["architectureHomotopyReport"]["status"].as_str(),
            Some(expected_status)
        );
        assert!(
            architecture_distance["homotopyDistanceReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
                && architecture_distance["architectureHomotopyReport"].is_object()
                && architecture_distance["distanceDiagnosis"]["homotopyInsights"]
                    ["homotopyDistanceReadingCount"]
                    .as_u64()
                    .is_some_and(|count| count > 0),
            "primary architecture-distance artifact must expose homotopy distance rows, HomotopyReport, and homotopy insights"
        );
        assert_eq!(
            summary["distanceDiagnosis"]["homotopyInsights"],
            architecture_distance["distanceDiagnosis"]["homotopyInsights"],
            "summary and primary architecture-distance artifact must read the same homotopy insight state"
        );
        assert_eq!(
            viewer["reportPane"]["distanceDiagnosis"]["homotopyInsights"],
            architecture_distance["distanceDiagnosis"]["homotopyInsights"],
            "viewer report pane must read the same homotopy insight state"
        );
        assert_eq!(
            llm_packet["distanceDiagnosisSummary"]["homotopyInsights"],
            architecture_distance["distanceDiagnosis"]["homotopyInsights"],
            "LLM packet must read the same homotopy insight state"
        );
        assert!(
            packet["homotopyHolonomyReadings"]
                .as_array()
                .is_some_and(|readings| {
                    readings.iter().any(|reading| {
                        reading["holonomyStatus"] == expected_loop_status
                            && reading["pathHomotopyDiagramRef"]
                                .as_str()
                                .is_some_and(|reference| packet.pointer(reference).is_some())
                    })
                }),
            "homotopy holonomy reading must expose expected status with refs"
        );
        let report = &packet["architectureHomotopyReport"];
        if expected_loop_status == "blockedByMissingFiller" {
            assert!(
                report["unfilledLoops"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && report["missingFillerEvidence"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && packet["homotopyDistanceReadings"]
                        .as_array()
                        .is_some_and(|items| {
                            items.iter().any(|reading| {
                                reading["measurementStatus"] == "blockedByMissingFiller"
                                    && reading["homotopyDistance"].is_null()
                                    && reading["observationGapLowerBound"]
                                        .as_i64()
                                        .is_some_and(|value| value > 0)
                            })
                        }),
                "missing filler must stay blocked and must not become measured zero"
            );
            assert!(
                architecture_distance["distanceDiagnosis"]["homotopyInsights"]
                    ["blockedFillerCount"]
                    .as_u64()
                    .is_some_and(|count| count > 0)
                    && architecture_distance["distanceDiagnosis"]["homotopyInsights"]
                        ["topMissingFillerBlockers"]
                        .as_array()
                        .is_some_and(|items| {
                            items.iter().any(|item| {
                                item["recommendedNextAction"]
                                    .as_str()
                                    .is_some_and(|action| action.contains("filler evidence"))
                                    && item["blockerRefs"].as_array().is_some_and(|refs| {
                                        refs.iter().any(|reference| {
                                            reference == "homotopy:filler-evidence-required"
                                        }) && !refs.is_empty()
                                    })
                                    && item["sourceRefs"]
                                        .as_array()
                                        .is_some_and(|refs| !refs.is_empty())
                            })
                        }),
                "blocked filler evidence must become source-linked next action in primary homotopy insights"
            );
        } else if expected_loop_status == "unmeasuredSelectedAxisDifference" {
            assert!(
                report["nonzeroHolonomyLoops"]
                    .as_array()
                    .is_some_and(Vec::is_empty)
                    && packet["homotopyDistanceReadings"]
                        .as_array()
                        .is_some_and(|items| {
                            items.iter().any(|reading| {
                                reading["measurementStatus"] == "blockedByCoverageGap"
                                    && reading["homotopyDistance"].is_null()
                                    && reading["observationGapLowerBound"]
                                        .as_i64()
                                        .is_some_and(|value| value > 0)
                            })
                        }),
                "semantic/runtime axis presence without selected nonzero evaluator support must stay unmeasured"
            );
            assert!(
                architecture_distance["distanceDiagnosis"]["homotopyInsights"]
                    ["blockedCoverageCount"]
                    .as_u64()
                    .is_some_and(|count| count > 0)
                    && architecture_distance["distanceDiagnosis"]["homotopyInsights"]
                        ["topCoverageGapBlockers"]
                        .as_array()
                        .is_some_and(|items| {
                            items.iter().any(|item| {
                                item["blockerRefs"].as_array().is_some_and(|refs| {
                                    refs.iter().any(|reference| {
                                        reference
                                            == "homotopy:selected-axis-coverage-required"
                                    })
                                })
                            })
                        }),
                "selected-axis coverage gap must remain visible in primary homotopy insights"
            );
        } else if expected_loop_status == "measuredNonzero" {
            assert!(
                report["nonzeroHolonomyLoops"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && report["topLocalCurvatureCells"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty()),
                "nonzero filled loop must surface holonomy and local curvature cells"
            );
            assert!(
                architecture_distance["distanceDiagnosis"]["homotopyInsights"]
                    ["measuredNonzeroLoopCount"]
                    .as_u64()
                    .is_some_and(|count| count > 0)
                    && architecture_distance["distanceDiagnosis"]["homotopyInsights"]
                        ["topMeasuredLoops"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty()),
                "measured nonzero homotopy loop must be primary insight, not raw-only packet detail"
            );
        } else {
            assert!(
                report["filledLoops"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && report["nonzeroHolonomyLoops"]
                        .as_array()
                        .is_some_and(Vec::is_empty),
                "zero filled loop must remain measured zero within selected filling"
            );
            assert!(
                architecture_distance["distanceDiagnosis"]["homotopyInsights"]
                    ["measuredZeroLoopCount"]
                    .as_u64()
                    .is_some_and(|count| count > 0),
                "measured zero loop must remain selected filled-loop zero in primary homotopy insights"
            );
        }
        let validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
        assert!(
            validation["checks"].as_array().is_some_and(|checks| {
                checks.iter().any(|check| {
                    check["checkId"] == "archsig.v1.architectureHomotopyReportSurface"
                        && check["result"] == "pass"
                })
            }),
            "analysis validation must lock v1 homotopy surface"
        );
    }
}

#[test]
fn cli_analyze_v1_homotopy_accepts_empty_molecule_support() {
    let out_dir = temp_dir("analyze-v1-homotopy-empty-support");
    let root = archmap_v1_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_no_molecule.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--emit-raw-artifacts",
    ]);

    assert!(output.status.success());
    let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    assert_eq!(
        packet["architectureHomotopyReport"]["status"].as_str(),
        Some("measuredZeroWithinSelectedFillings")
    );
    assert!(
        packet["pathHomotopyDiagramReadings"]
            .as_array()
            .is_some_and(Vec::is_empty)
            && packet["homotopyHolonomyReadings"]
                .as_array()
                .is_some_and(Vec::is_empty)
            && packet["stokesStyleReadings"]
                .as_array()
                .is_some_and(Vec::is_empty)
            && packet["homotopyDistanceReadings"]
                .as_array()
                .is_some_and(Vec::is_empty),
        "empty molecule support must be a valid empty homotopy surface"
    );
    let validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert!(
        validation["checks"].as_array().is_some_and(|checks| {
            checks.iter().any(|check| {
                check["checkId"] == "archsig.v1.architectureHomotopyReportSurface"
                    && check["result"] == "pass"
            })
        }),
        "empty molecule support must not fail homotopy validation"
    );
}

#[test]
fn cli_analyze_v1_structural_reading_review_surface_uses_typed_refs() {
    let out_dir = temp_dir("analyze-v1-structural-reading-review");
    let root = archmap_v1_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--emit-raw-artifacts",
    ]);

    assert!(output.status.success());
    let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    let surface = &packet["structuralReadingReviewSurface"];
    assert_eq!(
        surface["schemaVersion"].as_str(),
        Some("structural-reading-review-surface/v1")
    );
    assert!(
        surface["connectedReadingRefs"]
            .as_array()
            .is_some_and(|refs| {
                let expected = [
                    "representationMetricReadings",
                    "localCurvatureDiagramReadings",
                    "threeLayerFlatnessReadings",
                    "observationProjectionReadings",
                    "stateTransitionAlgebraReadings",
                    "effectRelationAlgebraReadings",
                    "synthesisBlockageReadings",
                    "operationPreconditionReadinessReadings",
                    "pathMultiplicityLossReadings",
                ]
                .into_iter()
                .flat_map(|field| {
                    packet[field]
                        .as_array()
                        .into_iter()
                        .flat_map(move |readings| {
                            (0..readings.len()).map(move |index| format!("/{field}/{index}"))
                        })
                })
                .collect::<Vec<_>>();
                !expected.is_empty()
                    && refs
                        .iter()
                        .filter_map(|reference| reference.as_str())
                        .collect::<Vec<_>>()
                        == expected
                    && expected
                        .iter()
                        .all(|pointer| packet.pointer(pointer).is_some())
            }),
        "structural review surface must connect exactly the structural packet refs"
    );
    for field in [
        "representationMetricReadings",
        "localCurvatureDiagramReadings",
        "threeLayerFlatnessReadings",
        "observationProjectionReadings",
        "stateTransitionAlgebraReadings",
        "effectRelationAlgebraReadings",
        "synthesisBlockageReadings",
        "operationPreconditionReadinessReadings",
        "pathMultiplicityLossReadings",
    ] {
        assert!(
            packet[field].as_array().is_some_and(|readings| {
                !readings.is_empty()
                    && readings.iter().all(|reading| {
                        reading["readingId"].as_str().is_some()
                            && reading["measurementStatus"].as_str().is_some()
                            && reading["normalizedAtomRefs"].as_array().is_some()
                            && reading["normalizedMoleculeRefs"].as_array().is_some()
                            && reading["typedEvaluatorResultRefs"]
                                .as_array()
                                .is_some_and(|refs| {
                                    !refs.is_empty()
                                        && refs.iter().all(|reference| {
                                            reference.as_str().is_some_and(|pointer| {
                                                packet.pointer(pointer).is_some()
                                            })
                                        })
                                })
                            && reading["coverageGapRefs"].as_array().is_some()
                    })
            }),
            "structural field {field} must expose typed / normalized refs"
        );
    }
    assert!(
        [
            "representationMetricReadings",
            "localCurvatureDiagramReadings",
            "threeLayerFlatnessReadings",
            "observationProjectionReadings",
            "stateTransitionAlgebraReadings",
            "effectRelationAlgebraReadings",
            "synthesisBlockageReadings",
            "operationPreconditionReadinessReadings",
            "pathMultiplicityLossReadings",
        ]
        .into_iter()
        .flat_map(|field| packet[field].as_array().into_iter().flatten())
        .all(|reading| {
            reading["measurementStatus"].as_str().is_some_and(|status| {
                status != "measuredZero"
                    && (status != "measured"
                        || reading["coverageGapRefs"]
                            .as_array()
                            .is_some_and(|refs| refs.is_empty()))
            })
        }),
        "structural rows must not use missing/proxy evidence as measured"
    );
    let validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert!(
        validation["checks"].as_array().is_some_and(|checks| {
            checks.iter().any(|check| {
                check["checkId"] == "archsig.v1.structuralReadingReviewSurface"
                    && check["result"] == "pass"
            })
        }),
        "analysis validation must lock v1 structural review surface"
    );
    let llm_packet = read_json(&out_dir.join("llm-interpretation-packet.json"));
    assert!(
        llm_packet["structuralReadingReviewSummary"]["topStructuralReadingRefs"]
            .as_array()
            .is_some_and(|refs| {
                !refs.is_empty()
                    && refs.iter().all(|reference| {
                        reference
                            .as_str()
                            .is_some_and(|pointer| packet.pointer(pointer).is_some())
                    })
            }),
        "LLM structural summary must keep resolvable packet refs"
    );
}

#[test]
fn cli_rejects_archmap_v1_unknown_atom_kind() {
    let out_dir = temp_dir("archmap-v1-unknown-kind");
    let root = archmap_v1_root();
    let report = out_dir.join("archmap-validation.json");

    let output = run_sig0_output(&[
        "archmap",
        "--input",
        root.join("archmap_unknown_kind.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "archmap-validation-report-v1");
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"].as_array().is_some_and(|checks| checks
            .iter()
            .any(|check| check["id"] == "archmap-v1-atom-kind-vocabulary"
                && check["result"] == "fail"))
    );
}

#[test]
fn cli_rejects_archmap_v1_unresolved_source_ref() {
    let out_dir = temp_dir("archmap-v1-bad-ref");
    let root = archmap_v1_root();
    let report = out_dir.join("archmap-validation.json");

    let output = run_sig0_output(&[
        "archmap",
        "--input",
        root.join("archmap_bad_ref.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let json = read_json(&report);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(json["checks"].as_array().is_some_and(|checks| {
        checks
            .iter()
            .any(|check| check["id"] == "archmap-v1-atom-refs-resolve" && check["result"] == "fail")
    }));
}

#[test]
fn cli_rejects_archmap_v1_unknown_predicate() {
    let out_dir = temp_dir("archmap-v1-unknown-predicate");
    let root = archmap_v1_root();
    let report = out_dir.join("archmap-validation.json");

    let output = run_sig0_output(&[
        "archmap",
        "--input",
        root.join("archmap_unknown_predicate.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let json = read_json(&report);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"].as_array().is_some_and(|checks| checks
            .iter()
            .any(|check| check["id"] == "archmap-v1-predicate-vocabulary"
                && check["result"] == "fail"))
    );
}

#[test]
fn cli_rejects_archmap_v1_legacy_root_field() {
    let out_dir = temp_dir("archmap-v1-legacy-field");
    let root = archmap_v1_root();
    let report = out_dir.join("archmap-validation.json");

    let output = run_sig0_output(&[
        "archmap",
        "--input",
        root.join("archmap_legacy_field.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    assert!(
        !report.exists(),
        "v1 legacy root field must stop before writing a validation report"
    );
}

#[test]
fn cli_validates_law_policy_v1_selector_contract() {
    let out_dir = temp_dir("law-policy-v1-validation");
    let root = archmap_v1_root();
    let report = out_dir.join("law-policy-validation.json");

    run_sig0(&[
        "law-policy",
        "--input",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "law-policy-validation-report-v1");
    assert_eq!(json["input"]["schema"], "law-policy/v1");
    assert_eq!(json["summary"]["result"], "pass");
    assert_eq!(json["summary"]["policyEntryCount"], 2);
    assert_eq!(json["summary"]["packEntryCount"], 1);
    assert_eq!(json["summary"]["expandedPolicyEntryCount"], 6);
    assert!(json["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-policy-v1-replacement-registry-manifest"
                && check["result"] == "pass"
        })
    }));
    assert!(json["expandedPolicies"].as_array().is_some_and(|entries| {
        entries.len() == 6
            && entries.iter().any(|entry| {
                entry["law"] == "solid.single-responsibility"
                    && entry["evaluator"] == "solid.single-responsibility@1"
            })
            && entries.iter().any(|entry| {
                entry["law"] == "solid.dependency-inversion"
                    && entry["evaluator"] == "solid.dependency-inversion@1"
            })
            && entries.iter().any(|entry| {
                entry["law"] == "domain.no-direct-infra-dependency"
                    && entry["evaluator"] == "domain.no-direct-infra-dependency@1"
            })
    }));
}

#[test]
fn cli_rejects_law_policy_v1_unknown_evaluator() {
    let out_dir = temp_dir("law-policy-v1-unknown-evaluator");
    let root = archmap_v1_root();
    let report = out_dir.join("law-policy-validation.json");

    let output = run_sig0_output(&[
        "law-policy",
        "--input",
        root.join("law_policy_unknown_evaluator.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "law-policy-validation-report-v1");
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"].as_array().is_some_and(|checks| checks
            .iter()
            .any(|check| check["id"] == "law-policy-v1-registry-vocabulary"
                && check["result"] == "fail"))
    );
}

#[test]
fn cli_rejects_law_policy_v1_unknown_pack() {
    let out_dir = temp_dir("law-policy-v1-unknown-pack");
    let root = archmap_v1_root();
    let report = out_dir.join("law-policy-validation.json");

    let output = run_sig0_output(&[
        "law-policy",
        "--input",
        root.join("law_policy_unknown_pack.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "law-policy-validation-report-v1");
    assert_eq!(json["summary"]["result"], "fail");
    assert!(json["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-policy-v1-registry-vocabulary" && check["result"] == "fail"
        })
    }));
}

#[test]
fn cli_rejects_law_policy_v1_unresolved_basis() {
    let out_dir = temp_dir("law-policy-v1-unknown-basis");
    let root = archmap_v1_root();
    let report = out_dir.join("law-policy-validation.json");

    let output = run_sig0_output(&[
        "law-policy",
        "--input",
        root.join("law_policy_unknown_basis.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "law-policy-validation-report-v1");
    assert_eq!(json["summary"]["result"], "fail");
    assert!(json["checks"].as_array().is_some_and(|checks| {
        checks
            .iter()
            .any(|check| check["id"] == "law-policy-v1-basis-recorded" && check["result"] == "fail")
    }));
}

#[test]
fn cli_rejects_law_policy_v1_dsl_field() {
    let out_dir = temp_dir("law-policy-v1-dsl-field");
    let root = archmap_v1_root();
    let report = out_dir.join("law-policy-validation.json");

    let output = run_sig0_output(&[
        "law-policy",
        "--input",
        root.join("law_policy_dsl_field.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    assert!(
        !report.exists(),
        "LawPolicy v1 DSL fields must stop before writing a validation report"
    );
}

#[test]
fn cli_rejects_law_policy_v1_unknown_distance_profile_ref() {
    let out_dir = temp_dir("law-policy-v1-unknown-distance-profile");
    let root = archmap_v1_root();
    let report = out_dir.join("law-policy-validation.json");
    let policy_path = out_dir.join("law_policy_unknown_distance_profile.json");
    let mut policy = read_json(&root.join("law_policy.json"));
    policy["distanceProfileRef"] = Value::from("distance-profile:unknown@1");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    let output = run_sig0_output(&[
        "law-policy",
        "--input",
        policy_path.to_str().expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "law-policy-validation-report-v1");
    assert_eq!(json["summary"]["result"], "fail");
    assert!(json["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-policy-v1-distance-profile-selector" && check["result"] == "fail"
        })
    }));
}

#[test]
fn cli_analyze_v1_writes_summary_viewer_and_manifest_artifacts() {
    let out_dir = temp_dir("analyze-v1-preflight");
    let root = archmap_v1_root();
    for stale_artifact in [
        "archsig-analysis-packet.json",
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
        "normalized-archmap.json",
        "typed-evaluator-results.json",
        "architecture-distance.json",
    ] {
        fs::write(out_dir.join(stale_artifact), "{}").expect("stale artifact can be written");
    }

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(output.status.success());
    assert_eq!(
        read_json(&out_dir.join("archmap-validation.json"))["schemaVersion"],
        "archmap-validation-report-v1"
    );
    assert_eq!(
        read_json(&out_dir.join("law-policy-validation.json"))["schemaVersion"],
        "law-policy-validation-report-v1"
    );
    assert_eq!(
        read_json(&out_dir.join("normalized-archmap.json"))["schema"],
        "normalized-archmap/v1"
    );
    assert_eq!(
        read_json(&out_dir.join("typed-evaluator-results.json"))["schema"],
        "typed-evaluator-results/v1"
    );
    let architecture_distance = read_json(&out_dir.join("architecture-distance.json"));
    assert_eq!(
        architecture_distance["schema"],
        "archsig-architecture-distance/v1"
    );
    assert_eq!(
        read_json(&out_dir.join("archsig-analysis-summary.json"))["schema"],
        "archsig-analysis-summary/v1"
    );
    assert_eq!(
        read_json(&out_dir.join("archsig-atom-viewer-data.json"))["schemaVersion"],
        "archsig-atom-viewer-data-v1"
    );
    assert_eq!(
        read_json(&out_dir.join("archsig-analysis-validation.json"))["schemaVersion"],
        "archsig-analysis-validation-report-v1"
    );
    assert_eq!(
        read_json(&out_dir.join("archsig-run-manifest.json"))["schemaVersion"],
        "archsig-run-manifest-v1"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    let viewer_data = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    assert!(
        summary["richReadingGuide"]["readingOrder"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| item == "richDominantFindings")
                    && items
                        .iter()
                        .any(|item| item == "structuralReadingReviewSummary")
            })
            && summary["richPacketRefs"]["structuralReadingRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && summary["actionQueue"]
                .as_array()
                .is_some_and(|items| items.iter().any(|item| {
                    item["kind"]
                        .as_str()
                        .is_some_and(|kind| kind == "spectrumHotspot")
                })),
        "v1 summary must expose rich packet refs and a conclusion-first reading guide"
    );
    assert_eq!(
        viewer_data["reportPane"]["richPacketRefs"], summary["richPacketRefs"],
        "viewer report pane must carry the same compact rich packet refs as summary"
    );
    assert!(
        viewer_data["reportPane"]["omittedDetailCounts"]["rawPacketArrays"]
            .as_str()
            .is_some_and(|text| text.contains("omitted from viewer data")),
        "viewer data must record that raw packet arrays are omitted from the projection"
    );
    assert!(
        !out_dir.join("archsig-analysis-packet.json").exists(),
        "raw v1 packet is omitted unless --emit-raw-artifacts is passed"
    );
    for reference in architecture_distance["primaryInsightsRefs"]
        .as_array()
        .expect("primary insight refs are emitted")
    {
        let Some(path) = reference
            .as_str()
            .expect("primary insight ref is string")
            .split('#')
            .next()
        else {
            panic!("primary insight ref has path before fragment");
        };
        assert!(
            out_dir.join(path).exists(),
            "default architecture-distance primary ref must point to generated artifact: {path}"
        );
    }
    assert!(
        architecture_distance["optionalRawArtifactRefs"]
            .as_array()
            .is_some_and(|refs| refs
                .iter()
                .any(|reference| reference
                    == "llm-interpretation-packet.json#/distanceInsightsSummary")
                && refs.iter().any(|reference| reference
                    == "llm-interpretation-packet.json#/distanceDiagnosisSummary")),
        "raw-only interpretation refs must be optional when raw artifacts are omitted"
    );
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert_eq!(
        manifest["architectureDistancePath"].as_str(),
        Some("architecture-distance.json")
    );
    assert!(
        manifest["generatedArtifacts"]
            .as_array()
            .is_some_and(|items| items
                .iter()
                .any(|item| item == "architecture-distance.json")),
        "manifest must record architecture-distance.json as a generated artifact"
    );
}

#[test]
fn cli_analyze_v1_emit_raw_artifacts_writes_typed_packet_detail_and_handoff() {
    let out_dir = temp_dir("analyze-v1-raw-artifacts");
    let root = archmap_v1_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--emit-raw-artifacts",
    ]);

    assert!(output.status.success());
    let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    let viewer_data = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    assert_eq!(packet["schema"], "archsig-analysis-packet/v1");
    assert_eq!(
        packet["inputRefs"]["typedEvaluatorResults"],
        "typed-evaluator-results.json"
    );
    assert_eq!(
        packet["architectureDistance"]["schema"],
        "archsig-architecture-distance/v1"
    );
    assert_eq!(
        packet["distanceDiagnosis"]["basis"], "architectureDistance",
        "v1 packet distanceDiagnosis must point at architecture distance, not typed counts"
    );
    let family_summaries = packet["architectureDistance"]["familySummaries"]
        .as_array()
        .expect("architecture distance family summaries are emitted");
    let part4_ledger = packet["part4DistanceCoverageLedger"]
        .as_array()
        .expect("Part IV distance coverage ledger is emitted");
    assert_eq!(
        family_summaries.len(),
        10,
        "architectureDistance must summarize every canonical distance family"
    );
    assert_eq!(
        family_summaries.len(),
        part4_ledger.len(),
        "architectureDistance family summaries must mirror the raw packet ledger"
    );
    for (index, (family_summary, ledger_entry)) in
        family_summaries.iter().zip(part4_ledger.iter()).enumerate()
    {
        assert_eq!(
            family_summary["sourceLedgerRef"],
            format!("packet:/part4DistanceCoverageLedger/{index}")
        );
        assert_eq!(
            family_summary["ledgerEntryId"],
            ledger_entry["ledgerEntryId"]
        );
        assert_eq!(
            family_summary["distanceFamily"],
            ledger_entry["distanceFamily"]
        );
        assert_eq!(
            family_summary["coverageStatus"],
            ledger_entry["coverageStatus"]
        );
        assert_eq!(
            family_summary["measurementStatus"],
            ledger_entry["measurementStatus"]
        );
        assert_eq!(family_summary["readingCount"], ledger_entry["readingCount"]);
        assert_eq!(
            family_summary["rawPacketRefs"],
            ledger_entry["rawPacketRefs"]
        );
    }
    assert_eq!(
        packet["architectureDistance"]["measurementStateSummary"]["missingCanonicalFamilyCount"]
            .as_u64(),
        Some(0),
        "canonical family bundle must not omit a Part IV distance family"
    );
    let measured_total_scope = &packet["architectureDistance"]["summary"]["measuredTotalScope"];
    assert_eq!(
        measured_total_scope["scope"].as_str(),
        Some("aggregated architecture-distance-point families only")
    );
    assert_eq!(
        string_set(&measured_total_scope["includedFamilies"]),
        BTreeSet::from([
            "atomGeometry".to_string(),
            "configurationGeometry".to_string(),
            "operationGeometry".to_string(),
            "signatureGeometry".to_string(),
        ]),
        "measuredTotal must state exactly which families are numerically aggregated"
    );
    assert_eq!(
        string_set(&measured_total_scope["nonAggregatedFamilies"]),
        BTreeSet::from([
            "boundedDiagnosticConclusion".to_string(),
            "curvatureGeometry".to_string(),
            "foundation".to_string(),
            "homotopyFillingGeometry".to_string(),
            "measurementBoundary".to_string(),
            "representationMetric".to_string(),
        ]),
        "non-aggregated canonical families must stay visible outside measuredTotal"
    );
    assert!(
        packet["replacementRegistry"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| {
                    item["replacementId"] == "semantic.interpretation@1"
                        && item["replacedV0Field"] == "semanticObservations"
                        && item["typedOutputPacketRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && item["positiveFixtures"]
                            .as_array()
                            .is_some_and(|fixtures| !fixtures.is_empty())
                        && item["negativeFixtures"]
                            .as_array()
                            .is_some_and(|fixtures| !fixtures.is_empty())
                })
            }),
        "v1 packet must expose replacement registry manifests"
    );
    for manifest in packet["replacementRegistry"]
        .as_array()
        .expect("replacement registry is array")
    {
        for refs_field in ["positiveFixtures", "negativeFixtures"] {
            for fixture in manifest[refs_field]
                .as_array()
                .expect("fixture field is array")
            {
                let fixture_path = Path::new(env!("CARGO_MANIFEST_DIR")).join(
                    fixture
                        .as_str()
                        .expect("fixture manifest entry is a string"),
                );
                assert!(
                    fixture_path.is_file(),
                    "replacement registry fixture path must exist: {}",
                    fixture_path.display()
                );
            }
        }
        for reference in manifest["typedOutputPacketRefs"]
            .as_array()
            .expect("typed output refs are array")
        {
            let pointer = reference
                .as_str()
                .expect("typed output packet ref is a string");
            assert!(
                packet.pointer(pointer).is_some(),
                "typed output packet ref must resolve in emitted packet: {pointer}"
            );
        }
    }
    assert_eq!(
        packet["replacementRegistryResolution"]["manifestCount"].as_u64(),
        Some(6)
    );
    assert!(
        packet["replacementEvaluatorResults"]
            .as_array()
            .is_some_and(|results| {
                results.iter().any(|result| {
                    result["replacementId"] == "projection.reading@1"
                        && result["replacementForV0Field"] == "projectionInfo"
                        && result["status"] == "measuredPass"
                        && result["basisRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && result["supportAtomRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && result["detailRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
            }),
        "replacement evaluator result must carry basis/support/detail refs"
    );
    assert!(
        packet["replacementEvaluatorResultsById"]["projection.reading@1"].is_object(),
        "packet must expose replacement evaluator results by id for registry refs"
    );
    assert!(
        packet["generatedLawInputs"]
            .as_array()
            .is_some_and(|items| {
                items.len() == 6
                    && items.iter().enumerate().all(|(index, item)| {
                        item["typedEvaluatorResultRef"] == format!("/typedEvaluatorResults/{index}")
                            && packet
                                .pointer(
                                    item["typedEvaluatorResultRef"]
                                        .as_str()
                                        .expect("typed result ref is string"),
                                )
                                .is_some()
                            && item["registryBasisRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && item["applicableLawAxes"]
                                .as_array()
                                .is_some_and(|axes| !axes.is_empty())
                    })
            }),
        "v1 packet must derive generatedLawInputs from typed evaluator results"
    );
    assert!(
        packet["signatureAxes"].as_array().is_some_and(|items| {
            items.len() == 6
                && items.iter().enumerate().all(|(index, item)| {
                    item["generatedLawInputRef"] == format!("/generatedLawInputs/{index}")
                        && packet
                            .pointer(
                                item["generatedLawInputRef"]
                                    .as_str()
                                    .expect("generated law input ref is string"),
                            )
                            .is_some()
                        && item["signatureDistanceReadingRefs"]
                            .as_array()
                            .is_some_and(|refs| {
                                !refs.is_empty()
                                    && refs.iter().all(|reference| {
                                        packet
                                            .pointer(
                                                reference
                                                    .as_str()
                                                    .expect("signature distance ref is string"),
                                            )
                                            .is_some()
                                    })
                            })
                        && item["registryBasisRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
        }),
        "v1 packet must derive signatureAxes from typed evaluator results and distance readings"
    );
    for field in [
        "generatedLawInputs",
        "signatureAxes",
        "generatedObstructions",
        "generatedRepairTargets",
        "architectureSpectrumReport",
        "curvatureSupportReadings",
        "curvatureTransferReadings",
        "curvatureMassReadings",
        "spectralAnalysisReadings",
        "spectralModeReadings",
        "spectralDrilldownReadings",
        "architectureHomotopyReport",
        "pathHomotopyDiagramReadings",
        "homotopyHolonomyReadings",
        "stokesStyleReadings",
        "homotopyDistanceReadings",
        "structuralReadingReviewSurface",
        "representationMetricReadings",
        "localCurvatureDiagramReadings",
        "threeLayerFlatnessReadings",
        "observationProjectionReadings",
        "stateTransitionAlgebraReadings",
        "effectRelationAlgebraReadings",
        "synthesisBlockageReadings",
        "operationPreconditionReadinessReadings",
        "pathMultiplicityLossReadings",
        "typedEvaluatorResults",
        "architectureDistanceSignatureReadings",
        "part4DistanceCoverageLedger",
    ] {
        let pointer = packet["generatedPacketRefs"][field]
            .as_str()
            .expect("generated packet ref is string");
        assert!(
            packet.pointer(pointer).is_some(),
            "generated packet ref must resolve: {pointer}"
        );
    }
    for removed_field in [
        "semanticObservations",
        "projectionInfo",
        "operationSquareEvidence",
        "spectrumMeasurementProfile",
        "homotopyMeasurementProfile",
        "concernHints",
        "observationGaps",
    ] {
        assert!(
            packet.get(removed_field).is_none(),
            "v1 packet must not restore removed v0 input field {removed_field}"
        );
    }
    assert!(
        packet["generatedPacketRefs"]
            .as_object()
            .is_some_and(|refs| !refs.contains_key("spectrumMeasurementProfile")
                && !refs.contains_key("homotopyMeasurementProfile")),
        "v1 generated packet refs must not restore v0 measurement profiles"
    );
    assert!(
        packet["architectureSpectrumReport"].is_object()
            && packet["curvatureSupportReadings"]
                .as_array()
                .is_some_and(|items| items.len() == 6)
            && packet["spectralModeReadings"]
                .as_array()
                .is_some_and(|items| items.len() == 6),
        "v1 packet must expose ArchitectureSpectrumReport and ACTS support / mode readings"
    );
    assert!(
        packet["architectureHomotopyReport"].is_object()
            && packet["pathHomotopyDiagramReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["homotopyHolonomyReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["stokesStyleReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["homotopyDistanceReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "v1 packet must expose ArchitectureHomotopyReport and homotopy reading families"
    );
    assert!(
        packet["structuralReadingReviewSurface"].is_object()
            && packet["structuralReadingReviewSurface"]["connectedReadingRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["representationMetricReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["observationProjectionReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["stateTransitionAlgebraReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["effectRelationAlgebraReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["synthesisBlockageReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["operationPreconditionReadinessReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && packet["pathMultiplicityLossReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "v1 packet must expose structural reading review surface and structural reading families"
    );
    assert!(
        summary["richDominantFindings"]["spectrumHotspots"]
            .as_array()
            .is_some_and(|items| {
                !items.is_empty()
                    && items.iter().all(|reference| {
                        reference
                            .as_str()
                            .and_then(|text| text.strip_prefix("packet:"))
                            .is_some_and(|pointer| packet.pointer(pointer).is_some())
                    })
            })
            && summary["richPacketRefs"]["architecturalHoleRefs"]
                .as_array()
                .is_some()
            && summary["richPacketRefs"]["structuralReadingRefs"]
                .as_array()
                .is_some_and(|items| {
                    !items.is_empty()
                        && items.iter().all(|reference| {
                            reference
                                .as_str()
                                .and_then(|text| text.strip_prefix("packet:"))
                                .is_some_and(|pointer| packet.pointer(pointer).is_some())
                        })
                }),
        "v1 summary rich refs must resolve into emitted raw packet when raw artifacts are retained"
    );
    assert!(
        summary["actionQueue"].as_array().is_some_and(|items| {
            items.iter().any(|item| item["kind"] == "spectrumHotspot")
                && items
                    .iter()
                    .any(|item| item["kind"] == "pathMultiplicityLoss")
                && items.iter().all(|item| {
                    item["detailRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
                })
        }),
        "v1 summary action queue must include compact spectrum, homotopy, and structural packet refs"
    );
    assert_eq!(
        viewer_data["analysisOverlays"]["richPacketRefs"], summary["richPacketRefs"],
        "viewer overlays must keep the same rich packet refs as summary"
    );
    assert_eq!(
        viewer_data["reportPane"]["richDominantFindings"], summary["richDominantFindings"],
        "viewer report pane must preserve rich dominant findings"
    );
    assert_eq!(
        packet["architectureSpectrumReport"]["status"].as_str(),
        Some("measuredZeroWithinSelectedSupport")
    );
    assert!(
        packet["architectureSpectrumReport"]["topHotspots"]
            .as_array()
            .is_some_and(|hotspots| {
                !hotspots.is_empty()
                    && hotspots.iter().all(|hotspot| {
                        hotspot["supportReadingRef"]
                            .as_str()
                            .is_some_and(|reference| packet.pointer(reference).is_some())
                            && hotspot["supportRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && hotspot["curvatureStatus"] == "measuredZero"
                    })
            }),
        "measured-zero spectrum hotspots must remain selected-support readings with refs"
    );
    let analysis_validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    for check_id in [
        "archsig.v1.architectureDistanceProfileRefsMatch",
        "archsig.v1.architectureDistanceBreakdownSums",
        "archsig.v1.architectureDistanceReadingCounts",
        "archsig.v1.architectureDistanceCanonicalBundle",
        "archsig.v1.replacementRegistryPresent",
        "archsig.v1.replacementRegistryResultsMatch",
        "archsig.v1.replacementRegistryOutputRefs",
        "archsig.v1.generatedLawInputsTraceTypedResults",
        "archsig.v1.signatureAxesTraceTypedResults",
        "archsig.v1.generatedObstructionsTraceTypedResults",
        "archsig.v1.generatedRepairTargetsTraceObstructions",
        "archsig.v1.generatedPacketRefsResolve",
        "archsig.v1.removedV0InputFieldsAbsent",
        "archsig.v1.architectureSpectrumReportSurface",
        "archsig.v1.architectureHomotopyReportSurface",
        "archsig.v1.structuralReadingReviewSurface",
    ] {
        assert!(
            analysis_validation["checks"]
                .as_array()
                .is_some_and(|checks| {
                    checks
                        .iter()
                        .any(|check| check["checkId"] == check_id && check["result"] == "pass")
                }),
            "analysis validation must include passing architecture distance check {check_id}"
        );
    }
    assert_eq!(
        read_json(&out_dir.join("archsig-analysis-detail-index.json"))["schemaVersion"],
        "archsig-analysis-detail-index-v1"
    );
    let detail_index = read_json(&out_dir.join("archsig-analysis-detail-index.json"));
    assert!(
        detail_index["entries"].as_array().is_some_and(|entries| {
            entries.iter().any(|entry| {
                entry["replacementId"] == "projection.reading@1"
                    && entry["resultRef"] == "replacementEvaluatorResults:projection.reading@1"
            })
        }),
        "replacement detail index entries must use replacementEvaluatorResults namespace"
    );
    assert!(
        detail_index["sections"].as_array().is_some_and(|sections| {
            [
                "generatedLawInputs",
                "part4DistanceCoverageLedger",
                "signatureAxes",
                "generatedObstructions",
                "generatedRepairTargets",
                "curvatureSupportReadings",
                "curvatureTransferReadings",
                "curvatureMassReadings",
                "spectralAnalysisReadings",
                "spectralModeReadings",
                "spectralDrilldownReadings",
                "architectureSpectrumReport.topHotspots",
                "architectureSpectrumReport.recurrentObstructions",
                "pathHomotopyDiagramReadings",
                "homotopyHolonomyReadings",
                "stokesStyleReadings",
                "homotopyDistanceReadings",
                "architectureHomotopyReport.filledLoops",
                "architectureHomotopyReport.unfilledLoops",
                "architectureHomotopyReport.nonzeroHolonomyLoops",
                "representationMetricReadings",
                "localCurvatureDiagramReadings",
                "threeLayerFlatnessReadings",
                "observationProjectionReadings",
                "stateTransitionAlgebraReadings",
                "effectRelationAlgebraReadings",
                "synthesisBlockageReadings",
                "operationPreconditionReadinessReadings",
                "pathMultiplicityLossReadings",
                "structuralReadingReviewSurface.connectedReadingRefs",
            ]
            .into_iter()
            .all(|name| sections.iter().any(|section| section["name"] == name))
        }),
        "v1 detail index must expose derived packet sections"
    );
    assert!(
        detail_index["entries"].as_array().is_some_and(|entries| {
            entries.iter().any(|entry| {
                entry["packetRef"] == "packet:/part4DistanceCoverageLedger/0"
                    && entry["resultRef"] == "part4DistanceCoverageLedger:part4-ledger:distance-aat"
            }) && entries.iter().any(|entry| {
                entry["packetRef"] == "packet:/generatedLawInputs/0"
                    && entry["typedEvaluatorResultRef"] == "/typedEvaluatorResults/0"
            }) && entries.iter().any(|entry| {
                entry["packetRef"] == "packet:/signatureAxes/0"
                    && entry["generatedLawInputRef"] == "/generatedLawInputs/0"
            }) && entries
                .iter()
                .any(|entry| entry["packetRef"] == "packet:/curvatureMassReadings/0")
                && entries
                    .iter()
                    .any(|entry| entry["packetRef"] == "packet:/spectralAnalysisReadings/0")
                && entries
                    .iter()
                    .any(|entry| entry["packetRef"] == "packet:/spectralDrilldownReadings/0")
                && entries.iter().any(|entry| {
                    entry["packetRef"] == "packet:/architectureSpectrumReport/topHotspots/0"
                })
                && entries
                    .iter()
                    .any(|entry| entry["packetRef"] == "packet:/pathHomotopyDiagramReadings/0")
                && entries
                    .iter()
                    .any(|entry| entry["packetRef"] == "packet:/homotopyHolonomyReadings/0")
                && entries
                    .iter()
                    .any(|entry| entry["packetRef"] == "packet:/stokesStyleReadings/0")
                && entries
                    .iter()
                    .any(|entry| entry["packetRef"] == "packet:/homotopyDistanceReadings/0")
                && entries.iter().any(|entry| {
                    entry["packetRef"] == "packet:/architectureHomotopyReport/filledLoops/0"
                })
                && entries.iter().any(|entry| {
                    entry["packetRef"] == "packet:/representationMetricReadings/0"
                        && entry["typedEvaluatorResultRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && entry["normalizedAtomRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && entry["coverageGapRefs"].as_array().is_some()
                })
                && entries.iter().any(|entry| {
                    entry["packetRef"]
                        == "packet:/structuralReadingReviewSurface/connectedReadingRefs/0"
                })
        }),
        "v1 detail index must include resolvable generated, spectrum, homotopy, and structural entries"
    );
    assert_eq!(
        read_json(&out_dir.join("llm-interpretation-packet.json"))["schema"],
        "llm-interpretation-packet/v1"
    );
    let llm_packet = read_json(&out_dir.join("llm-interpretation-packet.json"));
    assert_eq!(
        llm_packet["distanceDiagnosisSummary"]["basis"],
        "architectureDistance"
    );
    assert_eq!(
        llm_packet["replacementRegistryResolution"]["registryRef"].as_str(),
        Some("removed-v0-field-replacement-registry@1")
    );
    assert_eq!(
        llm_packet["richPacketRefs"], summary["richPacketRefs"],
        "LLM interpretation packet must guide readers to the same compact packet refs"
    );
    assert!(
        llm_packet["readingGuidance"]["readingOrder"]
            .as_array()
            .is_some_and(|items| items.iter().any(|item| item == "actionQueue"))
            && llm_packet["actionQueueSummary"]["topDetailRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "LLM packet must include rich reading guidance and compact action refs"
    );
    assert_eq!(
        llm_packet["architectureSpectrumReportSummary"]["status"].as_str(),
        Some("measuredZeroWithinSelectedSupport")
    );
    assert_eq!(
        llm_packet["architectureHomotopyReportSummary"]["reportRef"].as_str(),
        Some("archsig-analysis-packet.json#/architectureHomotopyReport")
    );
    assert!(
        llm_packet["architectureHomotopyReportSummary"]["topArchitecturalHoleRefs"]
            .as_array()
            .into_iter()
            .flatten()
            .chain(
                llm_packet["architectureHomotopyReportSummary"]["topNonzeroHolonomyRefs"]
                    .as_array()
                    .into_iter()
                    .flatten()
            )
            .all(|reference| {
                reference
                    .as_str()
                    .is_some_and(|pointer| packet.pointer(pointer).is_some())
            }),
        "LLM homotopy summary refs must resolve inside the analysis packet"
    );
    assert!(
        llm_packet["structuralReadingReviewSummary"]["topStructuralReadingRefs"]
            .as_array()
            .into_iter()
            .flatten()
            .all(|reference| {
                reference
                    .as_str()
                    .is_some_and(|pointer| packet.pointer(pointer).is_some())
            }),
        "LLM structural summary refs must resolve inside the analysis packet"
    );
    assert!(
        packet["nonConclusions"].as_array().is_some_and(|items| {
            items.iter().any(|item| {
                item.as_str()
                    .is_some_and(|text| text.contains("does not read v0 semanticObservations"))
            })
        }),
        "v1 packet must not promote removed v0 helper fields into positive readings"
    );
}

#[test]
fn cli_analyze_v1_label_only_semantic_does_not_become_measured_replacement() {
    let out_dir = temp_dir("analyze-v1-label-only-semantic");
    let root = archmap_v1_root();
    let archmap_path = root.join("replacement_negative/archmap_label_only_semantic.json");

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    let validation = read_json(&out_dir.join("archmap-validation.json"));
    assert_eq!(validation["summary"]["result"], "fail");
    assert!(validation["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "archmap-v1-atom-required-shapes" && check["result"] == "fail"
        })
    }));
    assert!(
        !out_dir.join("typed-evaluator-results.json").exists(),
        "label-only semantic text must stop before replacement evaluator measurement"
    );
}

#[test]
fn cli_analyze_v1_schema_only_input_does_not_become_measured_replacement() {
    let out_dir = temp_dir("analyze-v1-schema-only");
    let root = archmap_v1_root();
    let archmap_path = root.join("replacement_negative/archmap_schema_only.json");

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(
        output.status.success(),
        "schema-only v1 input is syntactically valid but must remain bounded incomplete"
    );
    let typed = read_json(&out_dir.join("typed-evaluator-results.json"));
    assert_eq!(typed["schema"], "typed-evaluator-results/v1");
    assert_eq!(
        typed["summary"]["measuredPassCount"].as_u64().unwrap_or(0)
            + typed["summary"]["measuredViolationCount"]
                .as_u64()
                .unwrap_or(0),
        0,
        "schema name alone must not become measured replacement evidence"
    );
    assert!(
        typed["summary"]["blockedCount"].as_u64().unwrap_or(0)
            + typed["summary"]["unknownCount"].as_u64().unwrap_or(0)
            + typed["summary"]["unmeasuredCount"].as_u64().unwrap_or(0)
            > 0,
        "schema-only input must remain blocked, unknown, or unmeasured"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["verdict"].as_str(),
        Some("BOUNDED_MEASUREMENT_INCOMPLETE"),
        "schema-only input must not report an acceptable measured conclusion"
    );
}

#[test]
fn cli_analyze_v1_removed_field_only_artifacts_do_not_become_measured_results() {
    let root = archmap_v1_root();
    for (removed_field, fixture) in [
        (
            "projectionInfo",
            "replacement_negative/archmap_projection_only_v0_field.json",
        ),
        (
            "operationSquareEvidence",
            "replacement_negative/archmap_operation_square_only_v0_field.json",
        ),
        (
            "observationGaps",
            "replacement_negative/archmap_observation_gaps_only_v0_field.json",
        ),
        (
            "concernHints",
            "replacement_negative/archmap_concern_only_v0_field.json",
        ),
        (
            "nonConclusions",
            "replacement_negative/archmap_non_conclusion_only_v0_field.json",
        ),
    ] {
        let out_dir = temp_dir(&format!("analyze-v1-removed-field-only-{}", removed_field));
        let archmap_path = root.join(fixture);

        let output = run_sig0_output(&[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ]);

        assert!(
            !output.status.success(),
            "removed v0 field {removed_field} must not be accepted as v1 input"
        );
        assert!(
            !out_dir.join("typed-evaluator-results.json").exists(),
            "removed field {removed_field} must stop before measured typed evaluator output"
        );
    }
}

#[test]
fn cli_analyze_v1_validation_failure_removes_stale_success_artifacts() {
    let out_dir = temp_dir("analyze-v1-stale-success-artifact-suppression");
    let root = archmap_v1_root();
    for stale_artifact in [
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
        "normalized-archmap.json",
        "typed-evaluator-results.json",
        "architecture-distance.json",
        "archsig-insight-report.json",
        "archsig-insight-brief.md",
        "archsig-analysis-packet.json",
        "archsig-analysis-detail-index.json",
        "archsig-analysis-validation.json",
        "llm-interpretation-packet.json",
    ] {
        fs::write(out_dir.join(stale_artifact), "{\"schema\":\"stale\"}")
            .expect("stale success artifact can be written");
    }

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("replacement_negative/archmap_label_only_semantic.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    assert_eq!(
        read_json(&out_dir.join("archmap-validation.json"))["summary"]["result"],
        "fail"
    );
    for stale_artifact in [
        "archsig-analysis-summary.json",
        "normalized-archmap.json",
        "typed-evaluator-results.json",
        "architecture-distance.json",
        "archsig-analysis-packet.json",
        "archsig-analysis-detail-index.json",
        "archsig-analysis-validation.json",
        "llm-interpretation-packet.json",
    ] {
        assert!(
            !out_dir.join(stale_artifact).exists(),
            "v1 validation failure must remove stale success artifact {stale_artifact}"
        );
    }
    assert_eq!(
        read_json(&out_dir.join("archsig-insight-report.json"))["insightCards"][0]["kind"],
        "validation_failure",
        "validation failure should replace stale insight report with a validation blocker projection"
    );
    assert_eq!(
        read_json(&out_dir.join("archsig-run-manifest.json"))["status"],
        "validation_failed"
    );
}

#[test]
fn cli_analyze_v1_strict_distance_rejects_missing_distance_profile_ref() {
    let out_dir = temp_dir("analyze-v1-strict-distance-missing-profile");
    let root = archmap_v1_root();
    let policy_path = out_dir.join("law_policy_without_distance_profile.json");
    let mut policy = read_json(&root.join("law_policy.json"));
    policy
        .as_object_mut()
        .expect("policy root is object")
        .remove("distanceProfileRef");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--strict-distance",
    ]);

    assert!(!output.status.success());
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("without distanceProfileRef"),
        "--strict-distance must require an explicit v1 distance profile selector\n{stderr}"
    );
    assert!(
        !out_dir.join("architecture-distance.json").exists(),
        "strict missing profile rejection must stop before architecture distance is emitted"
    );
    for artifact in [
        "normalized-archmap.json",
        "typed-evaluator-results.json",
        "archsig-analysis-validation.json",
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
    ] {
        assert!(
            !out_dir.join(artifact).exists(),
            "strict missing profile rejection must stop before writing {artifact}"
        );
    }
}

#[test]
fn cli_analyze_v1_strict_distance_rejects_blocked_typed_results() {
    let out_dir = temp_dir("analyze-v1-strict-distance-blocked");
    let root = archmap_v1_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_blocked_molecule.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--strict-distance",
    ]);

    assert!(!output.status.success());
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("blocked, unknown, unmeasured, or replacement-blocked distance statuses"),
        "--strict-distance must reject incomplete v1 typed distance support"
    );
    assert_eq!(
        read_json(&out_dir.join("typed-evaluator-results.json"))["summary"]["blockedCount"],
        6
    );
}

#[test]
fn cli_analyze_v1_strict_distance_rejects_partial_canonical_family_bundle() {
    let out_dir = temp_dir("analyze-v1-strict-distance-partial-family-bundle");
    let root = practical_rust_service_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap/archmap.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy/law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--strict-distance",
    ]);

    assert!(!output.status.success());
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("incomplete canonical distance family states"),
        "--strict-distance must reject partial canonical family bundles\n{stderr}"
    );
    let architecture_distance = read_json(&out_dir.join("architecture-distance.json"));
    assert_eq!(
        architecture_distance["measurementStateSummary"]["status"].as_str(),
        Some("partial"),
        "strict rejection must match the emitted canonical distance family state"
    );
}

#[test]
fn practical_rust_service_example_runs_v1_analyze() {
    let out_dir = temp_dir("practical-rust-service-v1-analyze");
    let root = practical_rust_service_root();

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap/archmap.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy/law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
        "--emit-raw-artifacts",
    ]);

    assert!(output.status.success());
    let archmap_validation = read_json(&out_dir.join("archmap-validation.json"));
    assert_eq!(archmap_validation["summary"]["atomCount"], 29);
    assert_eq!(archmap_validation["summary"]["moleculeCount"], 4);
    assert_eq!(archmap_validation["summary"]["result"], "pass");
    let normalized = read_json(&out_dir.join("normalized-archmap.json"));
    assert_eq!(normalized["summary"]["normalizedAtomCount"], 29);
    assert_eq!(normalized["summary"]["generatedMoleculeCandidateCount"], 4);
    assert!(normalized["molecules"].as_array().is_some_and(|molecules| {
        [
            "mol:domain-invariants",
            "mol:inventory-store-adapter",
            "mol:runtime-smoke-flow",
        ]
        .into_iter()
        .all(|source_molecule_id| {
            molecules
                .iter()
                .any(|molecule| molecule["sourceMoleculeId"] == source_molecule_id)
        })
    }));
    let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    assert_eq!(packet["schema"], "archsig-analysis-packet/v1");
    let typed = read_json(&out_dir.join("typed-evaluator-results.json"));
    assert!(
        typed["replacementEvaluatorResults"]
            .as_array()
            .is_some_and(|results| {
                results.iter().any(|result| {
                    result["replacementId"] == "semantic.interpretation@1"
                        && result["replacementForV0Field"] == "semanticObservations"
                        && result["status"] == "measuredPass"
                        && result["supportAtomRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && result["supportMoleculeRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
            }),
        "practical fixture must resolve semanticObservations through semantic atoms, not v0 helper fields"
    );
    let architecture_distance = read_json(&out_dir.join("architecture-distance.json"));
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    let llm_packet = read_json(&out_dir.join("llm-interpretation-packet.json"));
    assert_eq!(summary["schema"], "archsig-analysis-summary/v1");
    assert_eq!(
        architecture_distance["schema"],
        "archsig-architecture-distance/v1"
    );
    assert_eq!(
        architecture_distance["summary"]["profileRef"],
        "distance-profile:practical-rust-service@1"
    );
    assert_eq!(
        architecture_distance["familySummaries"], packet["architectureDistance"]["familySummaries"],
        "primary architecture-distance artifact and raw packet must expose the same canonical family bundle"
    );
    assert_eq!(
        architecture_distance["measurementStateSummary"],
        packet["architectureDistance"]["measurementStateSummary"],
        "primary architecture-distance artifact and raw packet must expose the same measurement state summary"
    );
    assert_eq!(
        architecture_distance["measurementStateSummary"]["familyCount"].as_u64(),
        Some(10),
        "practical fixture must expose all canonical distance families"
    );
    assert_eq!(
        architecture_distance["measurementStateSummary"]["missingCanonicalFamilyCount"].as_u64(),
        Some(0),
        "strict-distance practical fixture must not omit canonical distance families"
    );
    assert_eq!(
        string_set(&architecture_distance["summary"]["measuredTotalScope"]["includedFamilies"]),
        BTreeSet::from([
            "atomGeometry".to_string(),
            "configurationGeometry".to_string(),
            "operationGeometry".to_string(),
            "signatureGeometry".to_string(),
        ]),
        "measuredTotal must be scoped to architecture-distance-point families"
    );
    assert!(
        string_set(
            &architecture_distance["summary"]["measuredTotalScope"]["nonAggregatedFamilies"]
        )
        .is_superset(&BTreeSet::from([
            "curvatureGeometry".to_string(),
            "homotopyFillingGeometry".to_string(),
            "representationMetric".to_string(),
        ])),
        "derived Part IV families must be visible as non-aggregated canonical distance families"
    );
    assert!(
        architecture_distance["familySummaries"]
            .as_array()
            .is_some_and(|families| families
                .iter()
                .zip(
                    packet["part4DistanceCoverageLedger"]
                        .as_array()
                        .expect("raw packet ledger is emitted")
                        .iter()
                )
                .enumerate()
                .all(|(index, (family_summary, ledger_entry))| {
                    family_summary["sourceLedgerRef"]
                        == format!("packet:/part4DistanceCoverageLedger/{index}")
                        && family_summary["ledgerEntryId"] == ledger_entry["ledgerEntryId"]
                        && family_summary["distanceFamily"] == ledger_entry["distanceFamily"]
                        && family_summary["measurementStatus"] == ledger_entry["measurementStatus"]
                        && family_summary["readingCount"] == ledger_entry["readingCount"]
                })),
        "primary architecture-distance family bundle must mirror the raw packet ledger"
    );
    let first_atom_distance = &architecture_distance["atomDistanceReadings"][0];
    assert_eq!(
        string_set(&Value::Array(
            first_atom_distance["part4DefinitionReadings"]
                .as_array()
                .expect("atom Part IV definition readings are emitted")
                .iter()
                .map(|reading| reading["componentKind"].clone())
                .collect::<Vec<_>>()
        )),
        BTreeSet::from([
            "carrier".to_string(),
            "fiber".to_string(),
            "semanticAnchor".to_string(),
            "valence".to_string(),
        ]),
        "atom distance must expose Fiber / Carrier / Valence / Semantic Anchor rows"
    );
    assert_eq!(
        first_atom_distance["atomLayoutDistance"]["definitionRef"].as_str(),
        Some("definitions:2.5"),
        "atom layout distance must remain the composed atom-pair distance"
    );
    let first_configuration_distance = &architecture_distance["configurationDistanceReadings"][0];
    assert_eq!(
        first_configuration_distance["configurationIndexedDistance"]["definitionRef"].as_str(),
        Some("definitions:3.1"),
        "configuration-indexed distance must be explicit"
    );
    assert_eq!(
        first_configuration_distance["contextDistance"]["definitionRef"].as_str(),
        Some("definitions:3.2"),
        "context distance must be explicit"
    );
    assert!(
        first_configuration_distance["typedHypergraph"]["hyperedges"]
            .as_array()
            .is_some_and(|hyperedges| !hyperedges.is_empty()),
        "configuration distance must expose typed hypergraph evidence"
    );
    assert!(
        first_configuration_distance["selectedPairDistances"]
            .as_array()
            .is_some_and(|pairs| pairs.len() > 1
                && pairs.iter().all(|pair| {
                    pair["configurationIndexedDistance"]["shortestPathHyperedgeRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
                        && pair["contextDistance"]["contextUnionRefs"]
                            .as_array()
                            .is_some()
                })),
        "configuration distance must materialize explicit atom-pair shortest paths, not infer a first/last endpoint"
    );
    assert!(
        first_configuration_distance["basis"]
            .as_str()
            .is_some_and(|basis| !basis.contains("configuration size")),
        "configuration distance must not read as a molecule-size proxy"
    );
    assert!(
        first_configuration_distance["moleculeContributionRate"].is_object(),
        "configuration distance must expose molecule contribution rate"
    );
    assert!(
        summary["distanceDiagnosis"]["atomConfigurationInsights"]["topMovedAtomPairs"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && viewer["reportPane"]["distanceDiagnosis"]["atomConfigurationInsights"]
                ["topMovedMolecules"]
                .as_array()
                .is_some_and(|items| items
                    .iter()
                    .all(|item| item["sourceRefs"].as_array().is_some_and(|refs| !refs.is_empty())
                        && item["topSelectedPairDistances"]
                            .as_array()
                            .is_some_and(|pairs| !pairs.is_empty())))
            && llm_packet["distanceDiagnosisSummary"]["atomConfigurationInsights"]
                ["topMovedAtomPairs"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "summary, viewer, and LLM packet must expose top atom-pair and molecule distance insights"
    );
    let operation_distance_readings = architecture_distance["operationDistanceReadings"]
        .as_array()
        .expect("primary operation distance readings are emitted");
    assert!(
        operation_distance_readings.iter().any(|reading| {
            reading["law"] == "solid.dependency-inversion"
                && reading["status"] == "measured"
                && reading["measuredValue"] == 0
                && reading["operationCost"]["sourceRef"]
                    == "distanceProfile.operationCosts.solid.dependency-inversion"
                && reading["operationCost"]["includedInMeasuredValue"] == false
                && reading["targetDistanceDecrease"]["measuredValue"] == 0
                && reading["distanceToSelectedFlat"]["measuredValue"] == 0
                && reading["repairRoute"]["status"] == "not-required"
                && reading["repairRoute"]["sourceRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
                && reading["repairRoute"]["preconditionRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
                && reading["repairRoute"]["transferRiskRefs"]
                    .as_array()
                    .is_some_and(|refs| refs.is_empty())
                && reading["sideEffectBound"]["measuredValue"] == 0
                && reading["part4DefinitionReadings"]
                    .as_array()
                    .is_some_and(|rows| {
                        [
                            "operationCost",
                            "targetDistanceDecrease",
                            "distanceToSelectedFlat",
                            "repairRoute",
                            "sideEffectBound",
                        ]
                        .into_iter()
                        .all(|component| rows.iter().any(|row| row["componentKind"] == component))
                    })
                && reading["evidenceBoundary"]
                    .as_str()
                    .is_some_and(|boundary| {
                        boundary.contains("not automatic repair safety")
                            && boundary.contains("does not generate atoms")
                    })
        }),
        "practical fixture must expose a profile-driven operation / repair / flatness / side-effect primary row even when the selected law already passes"
    );
    assert!(
        summary["distanceDiagnosis"]["operationInsights"]["topOperationCandidates"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && viewer["reportPane"]["distanceDiagnosis"]["operationInsights"]
                ["topOperationCandidates"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && llm_packet["distanceDiagnosisSummary"]["operationInsights"]["topOperationCandidates"]
                .as_array()
            .is_some_and(|items| !items.is_empty()),
        "summary, viewer, and LLM packet must expose operation family insights"
    );
    assert!(
        architecture_distance["obstructionMeasureReadings"]
            .as_array()
            .is_some_and(|items| {
                items.len() == 6
                    && items.iter().all(|reading| {
                        reading["part4DefinitionRef"] == "definitions:6.1"
                            && reading["status"] == "measured"
                            && reading["obstructionMeasure"]["status"] == "measuredZero"
                            && reading["supportRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && reading["witnessRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && reading["sourceRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                    })
            })
            && architecture_distance["curvatureSupportReadings"]
                .as_array()
                .is_some_and(|items| items.len() == 6)
            && architecture_distance["curvatureTransferReadings"]
                .as_array()
                .is_some_and(|items| items.len() == 1)
            && architecture_distance["curvatureMassReadings"]
                .as_array()
                .is_some_and(|items| items.len() == 1),
        "primary architecture-distance artifact must expose obstruction measure, curvature support, transport, and mass rows"
    );
    assert!(
        summary["distanceDiagnosis"]["curvatureInsights"]["status"] == "measured-zero"
            && summary["distanceDiagnosis"]["curvatureInsights"]["measuredZeroSupportCount"]
                == 6
            && summary["distanceDiagnosis"]["curvatureInsights"]["blockedSupportCount"] == 0
            && summary["distanceDiagnosis"]["curvatureInsights"]["curvatureTransport"]
                ["spectralRadiusKind"]
                == "measuredZeroWithinSelectedSupport"
            && viewer["reportPane"]["distanceDiagnosis"]["curvatureInsights"]
                ["topCurvatureSupports"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && llm_packet["distanceDiagnosisSummary"]["curvatureInsights"]
                ["topCurvatureSupports"]
                .as_array()
                .is_some_and(|items| {
                    items.iter().all(|support| {
                        support["recommendedNextAction"]
                            .as_str()
                            .is_some_and(|action| action.contains("selected-support zero"))
                    })
                }),
        "summary, viewer, and LLM packet must expose curvature zero/nonzero/blocked counts without turning zero curvature into global lawfulness"
    );
    assert!(
        architecture_distance["representationMetricReadings"]
            .as_array()
            .is_some_and(|items| {
                items.len() == 1
                    && items.iter().all(|reading| {
                        reading["distanceFamily"] == "representationMetric"
                            && reading["status"] == "partial"
                            && reading["structuralDistance"]["status"] == "measured"
                            && reading["analyticDistance"]["status"] == "boundedProxy"
                            && reading["lipschitzUpperBound"]["status"] == "blockedByProxy"
                            && reading["biLipschitzFaithfulness"]["status"] == "blocked"
                            && reading["blockerRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && reading["coverageBlockerRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && reading["witnessCompletenessBlockerRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && reading["sourceRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && reading["part4DefinitionReadings"]
                                .as_array()
                                .is_some_and(|rows| {
                                    ["representationStability", "representationFaithfulness"]
                                        .into_iter()
                                        .all(|component| {
                                            rows.iter().any(|row| row["componentKind"] == component)
                                        })
                                })
                    })
            }),
        "primary representation metric rows must expose structural distance, bounded analytic proxy, blocked Lipschitz upper-bound, and blocked faithfulness"
    );
    assert!(
        summary["distanceDiagnosis"]["representationInsights"]["status"] == "partial"
            && summary["distanceDiagnosis"]["representationInsights"]
                ["measuredStructuralDistanceCount"]
                == 1
            && summary["distanceDiagnosis"]["representationInsights"]["boundedProxyAnalyticCount"]
                == 1
            && summary["distanceDiagnosis"]["representationInsights"]["blockedFaithfulnessCount"]
                == 1
            && viewer["reportPane"]["distanceDiagnosis"]["representationInsights"]
                ["topRepresentationMetrics"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && llm_packet["distanceDiagnosisSummary"]["representationInsights"]
                ["topRepresentationMetrics"]
                .as_array()
                .is_some_and(|items| {
                    items.iter().all(|reading| {
                        reading["recommendedNextAction"]
                            .as_str()
                            .is_some_and(|action| action.contains("proxy telemetry"))
                    })
                }),
        "summary, viewer, and LLM packet must expose representation proxy / faithfulness blockers instead of measured analytic distance"
    );
    assert!(
        architecture_distance["homotopyDistanceReadings"]
            .as_array()
            .is_some_and(|items| {
                items.len() == 4
                    && items.iter().all(|reading| {
                        reading["distanceFamily"] == "homotopyFillingGeometry"
                            && reading["status"] == "blocked"
                            && reading["measurementStatus"] == "blockedByCoverageGap"
                            && reading["homotopyDistance"]["status"] == "blocked"
                            && reading["fillingCost"]["status"] == "blocked"
                            && reading["observationGapLowerBound"]["status"] == "measured"
                            && reading["selectedDehnArea"]["status"] == "blocked"
                            && reading["sourceRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && reading["moleculeRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && reading["blockerRefs"].as_array().is_some_and(|refs| {
                                refs.iter().any(|reference| {
                                    reference == "homotopy:selected-axis-coverage-required"
                                })
                            })
                            && reading["part4DefinitionReadings"]
                                .as_array()
                                .is_some_and(|rows| {
                                    [
                                        "homotopyDistance",
                                        "fillingCost",
                                        "observationGapLowerBound",
                                        "selectedDehnArea",
                                    ]
                                    .into_iter()
                                    .all(|component| {
                                        rows.iter().any(|row| row["componentKind"] == component)
                                    })
                                })
                    })
            }),
        "primary homotopy rows must expose homotopy distance, filling cost, observation gap lower bound, selected Dehn area, and source refs"
    );
    assert!(
        summary["distanceDiagnosis"]["homotopyInsights"]["status"] == "partial"
            && summary["distanceDiagnosis"]["homotopyInsights"]["blockedCoverageCount"] == 4
            && summary["distanceDiagnosis"]["homotopyInsights"]["blockedReadingCount"] == 4
            && summary["distanceDiagnosis"]["homotopyInsights"]["observationGapLowerBoundTotal"]
                == 4
            && viewer["reportPane"]["distanceDiagnosis"]["homotopyInsights"]["topBlockedReadings"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && llm_packet["distanceDiagnosisSummary"]["homotopyInsights"]["topCoverageGapBlockers"]
                .as_array()
                .is_some_and(|items| {
                    items.iter().all(|item| {
                        item["recommendedNextAction"]
                            .as_str()
                            .is_some_and(|action| action.contains("coverage gap"))
                            && item["sourceRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                    })
                }),
        "summary, viewer, and LLM packet must expose homotopy blocked coverage as source-linked next action"
    );
    assert_eq!(
        architecture_distance["profile"]["signatureViolationWeight"].as_i64(),
        Some(2),
        "selected distance profile must contribute registry-owned weights"
    );
    assert_eq!(
        architecture_distance["profile"]["operationCosts"]["domain.no-direct-infra-dependency"]
            .as_i64(),
        Some(6),
        "selected distance profile must contribute registry-owned operation costs"
    );
    assert!(
        architecture_distance["summary"]["measuredTotal"]
            .as_i64()
            .is_some_and(|total| {
                total
                    > typed["summary"]["measuredViolationCount"]
                        .as_i64()
                        .unwrap_or(0)
            }),
        "architecture distance must not collapse to typed evaluator violation count"
    );
    assert_eq!(
        summary["conclusion"]["plainConclusion"].as_str(),
        Some("違反なし")
    );
    assert_eq!(
        summary["distanceDiagnosis"]["basis"].as_str(),
        Some("architectureDistance")
    );
    assert_eq!(
        viewer["reportPane"]["distanceDiagnosis"]["basis"].as_str(),
        Some("architectureDistance")
    );
    assert_eq!(
        llm_packet["distanceDiagnosisSummary"]["basis"].as_str(),
        Some("architectureDistance")
    );
    assert_eq!(
        summary["distanceInsights"], architecture_distance["distanceInsights"],
        "summary must read the same distanceInsights object as architecture-distance"
    );
    assert_eq!(
        viewer["reportPane"]["distanceInsights"], architecture_distance["distanceInsights"],
        "viewer report pane must read the same distanceInsights object as architecture-distance"
    );
    assert_eq!(
        llm_packet["distanceInsightsSummary"], architecture_distance["distanceInsights"],
        "LLM packet must read the same distanceInsights object as architecture-distance"
    );
    let distance_insights = &architecture_distance["distanceInsights"];
    assert!(
        distance_insights["architecturalCenter"]["status"] == "measured"
            && distance_insights["architecturalCenter"]["moleculeRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
            && distance_insights["architecturalCenter"]["atomRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
            && distance_insights["architecturalCenter"]["sourceRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
            && distance_insights["architecturalCenter"]["measuredValue"]
                .as_i64()
                .is_some_and(|value| value > 0),
        "distanceInsights must expose the structural center with molecule, atom, source refs, and measured distance"
    );
    assert!(
        distance_insights["changeSensitiveAreas"]
            .as_array()
            .is_some_and(|areas| {
                areas.iter().any(|area| {
                    area["areaKind"] == "configuration-molecule"
                        && area["sourceRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && area["moleculeRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                }) && areas.iter().any(|area| {
                    area["areaKind"] == "operation-route"
                        && area["sourceRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
            }),
        "distanceInsights must expose change-sensitive configuration and operation areas"
    );
    assert_eq!(
        distance_insights["policyObstructionReading"]["status"].as_str(),
        Some("selectedPolicyObstructionMeasuredZero"),
        "practical fixture should distinguish structural concentration from selected zero policy obstruction"
    );
    assert!(
        distance_insights["blockedEvidence"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| {
                    item["evidenceKind"] == "homotopy-coverage-gap"
                        && item["blockerRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && item["sourceRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && item["moleculeRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                }) && items.iter().any(|item| {
                    item["evidenceKind"] == "representation-metric"
                        && item["atomRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && item["moleculeRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
            }),
        "distanceInsights must connect blocked evidence to source, atom, and molecule refs"
    );
    assert!(
        distance_insights["comparisonNeeded"]["baselineRequired"] == true
            && distance_insights["comparisonNeeded"]["claimsNeedingBaseline"]
                .as_array()
                .is_some_and(|claims| !claims.is_empty())
            && distance_insights["distanceActionQueue"]
                .as_array()
                .is_some_and(|items| {
                    items.iter().any(|item| {
                        item["actionKind"] == "resolve-blocked-distance-evidence"
                            && item["blockerRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && item["sourceRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                    })
                }),
        "distanceInsights must keep baseline-dependent claims explicit and convert blockers into distance action queue rows"
    );
    assert_public_artifact_omits_part4("summary", &summary);
    assert_public_artifact_omits_part4("viewer", &viewer);
    assert_public_artifact_omits_part4("llm packet", &llm_packet);
}

#[test]
fn cli_pr_review_accepts_v1_archmap_and_law_policy() {
    let out_dir = temp_dir("pr-review-v1");
    let root = archmap_v1_root();
    let review = pr_review_root();
    let report = out_dir.join("archsig-pr-review-v1.json");

    let output = run_sig0_output(&[
        "pr-review",
        "--base-archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--delta-archmap",
        review
            .join("archmap_delta_v1_refs.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(output.status.success());
    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "archsig-pr-review-report-v1");
    assert_eq!(
        json["reviewKind"],
        "v1-output-replacement-structural-pr-review"
    );
    assert_eq!(
        json["canonicalInputs"]["baseArchMap"]["schema"],
        "archmap/v1"
    );
    assert_eq!(
        json["canonicalInputs"]["lawPolicy"]["schema"],
        "law-policy/v1"
    );
    assert_eq!(json["typedEvaluatorSummary"]["resultCount"], 6);
    assert_eq!(
        json["v1Analysis"]["base"]["packetSchema"],
        "archsig-analysis-packet/v1"
    );
    assert!(
        json["v1Analysis"]["base"]["structuralPacketRefs"]["structuralReadingReviewSurface"]
            .as_str()
            .is_some_and(|reference| reference == "/structuralReadingReviewSurface")
            && json["v1Analysis"]["base"]["structuralReadingRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty()),
        "pr-review must expose v1 derived structural packet refs"
    );
    assert!(
        json["deltaPacketRefIntersections"]
            .as_array()
            .is_some_and(|items| items.iter().all(|item| {
                item["matchedPacketRefCount"].as_u64().unwrap_or(0) > 0
                    && item["status"] == "matchedDerivedPacketRefs"
            })),
        "v1 PR delta refs must intersect typed / derived packet refs"
    );
    assert!(
        json["prStructuralDiagnosis"]["safeChangeBudget"]["status"]
            .as_str()
            .is_some_and(|status| status == "boundedNoNewSelectedObstruction"
                || status == "blockedByIncompleteTypedSupport"),
        "base-only PR review must not treat bounded incomplete support as measured zero"
    );
    assert_eq!(
        json["prStructuralDiagnosis"]["endpointDistanceMovement"]["status"],
        "blockedWithoutAfterArchMap",
        "missing head ArchMap is blocked, not measured zero"
    );
}

#[test]
fn cli_pr_review_v1_reads_after_and_path_archmap_structural_diagnosis() {
    let out_dir = temp_dir("pr-review-v1-after-archmap");
    let root = archmap_v1_root();
    let review = pr_review_root();
    let report = out_dir.join("archsig-pr-review-v1.json");

    let output = run_sig0_output(&[
        "pr-review",
        "--base-archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--after-archmap",
        root.join("archmap_violation.json")
            .to_str()
            .expect("path is utf-8"),
        "--path-archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--delta-archmap",
        review
            .join("archmap_delta_v1_refs.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(output.status.success());
    let json = read_json(&report);
    assert_eq!(
        json["canonicalInputs"]["afterArchMap"]["schema"],
        "archmap/v1"
    );
    assert_eq!(
        json["v1Analysis"]["after"]["packetSchema"],
        "archsig-analysis-packet/v1"
    );
    assert_eq!(
        json["v1Analysis"]["path"]
            .as_array()
            .expect("path analyses are array")
            .len(),
        1
    );
    assert_eq!(
        json["prStructuralDiagnosis"]["endpointDistanceMovement"]["status"],
        "measuredFromSuppliedBaseAndAfterArchMap"
    );
    assert_eq!(
        json["prStructuralDiagnosis"]["totalPathMovement"]["status"],
        "measuredFromSuppliedIntermediateArchMaps"
    );
    assert_eq!(
        json["prStructuralDiagnosis"]["hiddenExcursionBoundary"]["status"],
        "boundedBySuppliedIntermediateArchMaps"
    );
    assert!(
        json["prStructuralDiagnosis"]["safeChangeBudget"]["status"]
            .as_str()
            .is_some_and(|status| status == "needsReviewForIncreasedDistance"
                || status == "blockedByIncompleteTypedSupport"),
        "after/path review must surface distance movement or blocked typed support without claiming safety"
    );
}

#[test]
fn cli_pr_review_v1_matches_head_only_delta_refs() {
    let out_dir = temp_dir("pr-review-v1-after-only-delta");
    let root = archmap_v1_root();
    let review = pr_review_root();
    let report = out_dir.join("archsig-pr-review-v1.json");

    let output = run_sig0_output(&[
        "pr-review",
        "--base-archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--after-archmap",
        root.join("archmap_violation.json")
            .to_str()
            .expect("path is utf-8"),
        "--delta-archmap",
        review
            .join("archmap_delta_v1_after_refs.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(output.status.success());
    let json = read_json(&report);
    let intersection = json["deltaPacketRefIntersections"]
        .as_array()
        .expect("intersections are array")
        .first()
        .expect("head-only delta has one ref");
    assert_eq!(intersection["deltaRef"], "atom:direct-store-dependency");
    assert_eq!(intersection["status"], "matchedDerivedPacketRefs");
    assert!(
        intersection["snapshotMatches"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| item["analysisLabel"] == "after")
                    && !items.iter().any(|item| item["analysisLabel"] == "base")
            }),
        "head-only delta ref must match the after analysis snapshot, not only base"
    );
}

#[test]
fn cli_pr_review_v1_rejects_invalid_delta_refs_and_path_without_after() {
    let out_dir = temp_dir("pr-review-v1-invalid-delta");
    let root = archmap_v1_root();
    let malformed_delta = out_dir.join("archmap_delta_missing_refs.json");
    fs::write(
        &malformed_delta,
        r#"{
  "schemaVersion": "archmap-delta-v0",
  "deltaId": "delta:missing-refs"
}"#,
    )
    .expect("malformed delta fixture can be written");
    let report = out_dir.join("archsig-pr-review-v1.json");

    let missing_refs = run_sig0_output(&[
        "pr-review",
        "--base-archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--delta-archmap",
        malformed_delta.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!missing_refs.status.success());
    assert!(
        String::from_utf8_lossy(&missing_refs.stderr)
            .contains("changedObservationRefs must be a non-empty string array")
    );

    let review = pr_review_root();
    let path_without_after = run_sig0_output(&[
        "pr-review",
        "--base-archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--path-archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--delta-archmap",
        review
            .join("archmap_delta_v1_refs.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    assert!(!path_without_after.status.success());
    assert!(
        String::from_utf8_lossy(&path_without_after.stderr)
            .contains("--path-archmap requires --after-archmap")
    );
}

#[test]
fn cli_pr_review_v1_rejects_invalid_archmap_or_law_policy_contract() {
    let out_dir = temp_dir("pr-review-v1-invalid-contract");
    let root = archmap_v1_root();
    let review = pr_review_root();
    let report = out_dir.join("archsig-pr-review-v1.json");

    let invalid_archmap = run_sig0_output(&[
        "pr-review",
        "--base-archmap",
        root.join("archmap_legacy_field.json")
            .to_str()
            .expect("path is utf-8"),
        "--delta-archmap",
        review
            .join("archmap_delta_v1_refs.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);
    assert!(!invalid_archmap.status.success());
    assert!(
        String::from_utf8_lossy(&invalid_archmap.stderr)
            .contains("failed ArchMap v1 validation for pr-review")
    );

    let invalid_policy = run_sig0_output(&[
        "pr-review",
        "--base-archmap",
        root.join("archmap.json").to_str().expect("path is utf-8"),
        "--delta-archmap",
        review
            .join("archmap_delta_v1_refs.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_dsl_field.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);
    assert!(!invalid_policy.status.success());
    assert!(
        String::from_utf8_lossy(&invalid_policy.stderr)
            .contains("failed LawPolicy v1 validation for pr-review")
    );
}

#[test]
fn cli_help_exposes_only_llm_atom_archmap_surface() {
    let output = run_sig0_output(&["--help"]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("Part IV"),
        "current v1 CLI help must describe architecture distance without Part IV public wording\n{stdout}"
    );

    for command in [
        "archmap",
        "law-policy",
        "pr-review",
        "analyze",
        "schema-catalog",
    ] {
        assert!(
            stdout.contains(command),
            "ArchSig help must expose retained command {command}\n{stdout}"
        );
    }

    for removed in [
        "archmap-generate",
        "interpretation-profile",
        "archsig-analysis",
        "aat-analysis",
        "analysis-summary",
        "summary",
        "codebase-inspection",
        "llm-native-workflow",
        "north-star-workflow",
    ] {
        assert!(
            !stdout.contains(removed),
            "ArchSig help must not expose removed v0 runtime surface {removed}\n{stdout}"
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
#[ignore = "legacy v0 analysis-summary command is no longer current runtime surface"]
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
    let packet = read_json(&root.join("archsig_analysis_packet.json"));
    let measured_axis_refs = signature_measured_axis_refs(&packet);
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
    assert!(
        json["distanceDiagnosis"]["verdict"]
            .as_str()
            .is_some_and(|value| value == "distanceBlockedByCoverageOrEvidence")
            && json["distanceDiagnosis"]["topMovedAtoms"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && json["distanceDiagnosis"]["topMovedAxes"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && json["distanceDiagnosis"]["detailRefs"]
                .as_array()
                .is_some_and(|items| items.iter().any(|item| {
                    item.as_str()
                        .is_some_and(|value| value.contains("/signatureDistanceReadings"))
                })),
        "analysis-summary must expose Part IV distance diagnosis with detail refs"
    );
    assert_part4_distance_diagnosis_refs_resolve(&json, &packet);
    assert!(
        json["distanceDiagnosis"]["repairDistance"]["readingId"]
            .as_str()
            .is_some()
            && json["distanceDiagnosis"]["repairDistance"]["operationDeltaRef"]
                .as_str()
                .is_some()
            && json["distanceDiagnosis"]["curvatureDistance"]["readingId"]
                .as_str()
                .is_some(),
        "analysis-summary distanceDiagnosis must expose non-null raw packet ids for repair and curvature distances"
    );
    assert!(
        json["distanceDiagnosis"]["topMovedAxes"]
            .as_array()
            .into_iter()
            .flatten()
            .all(|axis| {
                axis["axisDistance"]["measuredValue"]
                    .as_i64()
                    .is_some_and(|value| value > 0)
            }),
        "topMovedAxes must only report positive measured movement axes"
    );
    assert!(
        unmeasured_surface_excludes_measured_axes(&json["distanceDiagnosis"], &measured_axis_refs),
        "analysis-summary distanceDiagnosis must not report measured or zero signature axes as unmeasured"
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
#[ignore = "legacy v0 analysis-summary command is no longer current runtime surface"]
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
#[ignore = "legacy v0 analysis-summary command is no longer current runtime surface"]
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
#[ignore = "legacy v0 codebase-inspection command is no longer current runtime surface"]
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
#[ignore = "legacy v0 analysis-summary command is no longer current runtime surface"]
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
#[ignore = "legacy compatibility aliases are intentionally removed from current runtime surface"]
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
        "--emit-raw-artifacts",
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
        "--emit-raw-artifacts",
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
#[ignore = "legacy v0 analyze fixture is no longer current runtime surface"]
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
        "archsig-analysis-validation.json",
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
    ];
    for file in expected {
        assert!(
            out_dir.join(file).is_file(),
            "analyze workflow must write {file}"
        );
    }
    for omitted_file in [
        "archsig-analysis-packet.json",
        "archsig-analysis-detail-index.json",
        "llm-interpretation-packet.json",
    ] {
        assert!(
            !out_dir.join(omitted_file).exists(),
            "analyze workflow must omit raw artifact {omitted_file} by default"
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
    let analysis_validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert_eq!(
        analysis_validation["summary"]["result"].as_str(),
        Some("pass")
    );
    let analysis_summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    let expected_packet = read_json(&root.join("archsig_analysis_packet.json"));
    let expected_measured_axis_refs = signature_measured_axis_refs(&expected_packet);
    assert_eq!(
        analysis_summary["packet"]["schemaVersion"].as_str(),
        Some("archsig-analysis-packet-v0")
    );
    assert_eq!(
        analysis_summary["validation"]["analysis"]["result"].as_str(),
        Some("pass")
    );
    let viewer_data = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    assert_eq!(
        viewer_data["schemaVersion"].as_str(),
        Some("archsig-atom-viewer-data-v0")
    );
    assert!(
        viewer_data["atomNodes"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "viewer data must project ArchMap atom observations"
    );
    assert_eq!(
        viewer_data["sourceArtifactRefs"]["archmap"].as_str(),
        archmap.to_str()
    );
    assert_eq!(
        viewer_data["sourceArtifactRefs"]["lawPolicy"].as_str(),
        law_policy.to_str()
    );
    assert_eq!(
        viewer_data["layoutSettings"]["nodeLimit"].as_u64(),
        Some(20_000)
    );
    assert_eq!(
        viewer_data["layoutSettings"]["edgeLimit"].as_u64(),
        Some(30_000)
    );
    assert_eq!(
        viewer_data["layoutSettings"]["sourceRefSampleLimit"].as_u64(),
        Some(3)
    );
    assert!(
        viewer_data["moleculeGroups"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "viewer data must project ArchMap molecule groups"
    );
    assert!(
        viewer_data["atomEdges"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "viewer data must project bounded molecule-to-atom edges"
    );
    assert!(
        viewer_data["analysisOverlays"]["signatureAxes"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "viewer data must carry selected analysis overlays"
    );
    assert_eq!(
        viewer_data["aatGeometryOverlays"]["schemaVersion"].as_str(),
        Some("archsig-aat-geometry-overlays-v0")
    );
    assert!(
        viewer_data["aatGeometryOverlays"]["curvatureSupports"]
            .as_array()
            .is_some(),
        "viewer data must carry computed AAT curvature geometry projection"
    );
    assert!(
        viewer_data["aatGeometryOverlays"]["holonomyReadings"]
            .as_array()
            .is_some(),
        "viewer data must carry computed AAT path and holonomy geometry projection"
    );
    assert!(
        viewer_data["aatGeometryOverlays"]["generatedMolecules"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && viewer_data["aatGeometryOverlays"]["viewerDistanceInputs"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "viewer data must carry generated molecule and AtomShape distance inputs"
    );
    assert!(
        viewer_data["aatGeometryOverlays"]["diagnosticDistanceReadings"]["signatureDistances"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && viewer_data["aatGeometryOverlays"]["diagnosticDistanceBoundary"]
                .as_str()
                .is_some_and(|text| text.contains("viewerDistanceInputs are visual layout support")),
        "viewer data must separate diagnostic Part IV distances from layout distance inputs"
    );
    let viewer_distance = viewer_data["aatGeometryOverlays"]["viewerDistanceInputs"]
        .as_array()
        .and_then(|items| items.first())
        .expect("viewer distance input is projected");
    assert!(
        viewer_distance["sourceRef"].as_str().is_some()
            && viewer_distance["targetRef"].as_str().is_some()
            && viewer_distance["distanceValue"].as_i64().is_some()
            && viewer_distance["coordinateComponents"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "viewer distance inputs must retain source/target refs, distance value, and AtomShape coordinate components for layout"
    );
    assert_eq!(
        viewer_data["reportPane"]["overview"]["summaryVerdict"]["readingMode"].as_str(),
        Some("measurementOverSuppliedArchMapAndLawPolicy")
    );
    assert!(
        viewer_data["reportPane"]["topFindings"].is_object()
            && viewer_data["reportPane"]["distanceInsights"].is_object()
            && viewer_data["reportPane"]["distanceDiagnosis"].is_object()
            && viewer_data["reportPane"]["actionQueue"].is_array()
            && viewer_data["reportPane"]["coverageAndBoundaries"].is_object()
            && viewer_data["reportPane"]["artifacts"].is_object(),
        "viewer data report pane must carry overview, top findings, distance insights, distance diagnosis, action queue, coverage, and artifact sections"
    );
    assert_eq!(
        viewer_data["reportPane"]["distanceInsights"], analysis_summary["distanceInsights"],
        "viewer report pane must read the same distanceInsights object as the compact summary"
    );
    assert_eq!(
        viewer_data["reportPane"]["distanceDiagnosis"], analysis_summary["distanceDiagnosis"],
        "viewer report pane must read the same Part IV distanceDiagnosis as the compact summary"
    );
    assert!(
        unmeasured_surface_excludes_measured_axes(
            &viewer_data["reportPane"]["distanceDiagnosis"],
            &expected_measured_axis_refs
        ),
        "viewer report pane must not report measured or zero signature axes as unmeasured"
    );
    assert_eq!(
        viewer_data["reportPane"]["artifacts"]["summary"].as_str(),
        Some("archsig-analysis-summary.json")
    );
    assert_eq!(
        viewer_data["reportPane"]["artifacts"]["manifest"].as_str(),
        Some("archsig-run-manifest.json")
    );
    assert_eq!(
        viewer_data["omittedDetailCounts"]["rawPacketDetail"].as_str(),
        Some("raw packet is not embedded in viewer data")
    );
    let run_manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert_eq!(
        run_manifest["schemaVersion"].as_str(),
        Some("archsig-run-manifest-v0")
    );
    assert_eq!(
        run_manifest["rawArtifactRetention"].as_str(),
        Some("omitted")
    );
    assert_eq!(run_manifest["commandName"].as_str(), Some("analyze"));
    assert_eq!(run_manifest["archmapInputPath"].as_str(), archmap.to_str());
    assert_eq!(
        run_manifest["lawPolicyInputPath"].as_str(),
        law_policy.to_str()
    );
    assert_eq!(
        run_manifest["validationResultSummary"]["analysis"]["result"].as_str(),
        Some("pass")
    );
    assert!(
        run_manifest["omittedArtifacts"]
            .as_array()
            .expect("omitted artifacts are array")
            .iter()
            .any(|artifact| artifact == "archsig-analysis-packet.json"),
        "manifest must record omitted raw analysis packet"
    );
    assert!(
        run_manifest.get("rawArtifactPaths").is_none(),
        "manifest must not advertise raw artifact paths when raw retention is omitted"
    );
    assert!(
        viewer_data.get("schemaVersion").is_some()
            && viewer_data.get("sourceArtifactRefs").is_some()
            && viewer_data.get("layoutSettings").is_some()
            && viewer_data.get("atomNodes").is_some()
            && viewer_data.get("moleculeGroups").is_some()
            && viewer_data.get("atomEdges").is_some()
            && viewer_data.get("analysisOverlays").is_some()
            && viewer_data.get("aatGeometryOverlays").is_some()
            && viewer_data.get("reportPane").is_some()
            && viewer_data.get("omittedDetailCounts").is_some(),
        "viewer data shape must contain the schema sections owned by archsig-atom-viewer-data-v0"
    );
    for raw_packet_field in [
        "aatConcepts",
        "architectureState",
        "moleculeReadings",
        "obstructionCircuits",
        "signatureAxes",
        "llmInterpretationPacket",
    ] {
        assert!(
            viewer_data.get(raw_packet_field).is_none(),
            "viewer data must not copy raw packet field {raw_packet_field}"
        );
    }
    assert!(
        analysis_validation.get("packet").is_none(),
        "analysis validation must not embed the full analysis packet"
    );
}

#[test]
#[ignore = "legacy Part IV v0 profile fallback is no longer current runtime surface"]
fn cli_analyze_strict_distance_requires_part4_profile() {
    let out_dir = temp_dir("analyze-strict-distance");
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
        "--strict-distance",
    ]);

    let legacy_policy_path = out_dir.join("law_policy_without_part4_distance_profile.json");
    let mut legacy_policy = read_json(&law_policy);
    legacy_policy
        .as_object_mut()
        .expect("LawPolicy is an object")
        .remove("part4DistanceProfile");
    fs::write(
        &legacy_policy_path,
        serde_json::to_vec_pretty(&legacy_policy).expect("legacy policy serializes"),
    )
    .expect("legacy policy can be written");

    let legacy_out_dir = out_dir.join("legacy-profile");
    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        legacy_policy_path
            .to_str()
            .expect("legacy law policy path is utf-8"),
        "--out-dir",
        legacy_out_dir.to_str().expect("legacy output dir is utf-8"),
        "--strict-distance",
    ]);

    assert!(
        !output.status.success(),
        "strict-distance must reject LawPolicy without part4DistanceProfile"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--strict-distance")
            && stderr.contains("part4DistanceProfile")
            && stderr.contains("legacy profile fallback is disabled"),
        "strict-distance error should identify missing Part IV profile\n{stderr}"
    );
    for file in [
        "archmap-validation.json",
        "law-policy-validation.json",
        "archsig-analysis-validation.json",
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
    ] {
        assert!(
            legacy_out_dir.join(file).is_file(),
            "strict-distance failure should still write diagnostic artifact {file}"
        );
    }
    let law_policy_validation = read_json(&legacy_out_dir.join("law-policy-validation.json"));
    assert_eq!(
        law_policy_validation["summary"]["result"].as_str(),
        Some("warn"),
        "legacy profile should be visible in the emitted LawPolicy validation report"
    );
}

#[test]
#[ignore = "legacy Part IV v0 profile fallback is no longer current runtime surface"]
fn cli_analyze_strict_distance_uses_part4_profile_weights() {
    let out_dir = temp_dir("analyze-strict-distance-weights");
    let root = fixture_root();
    let archmap = root.join("archmap.json");
    let law_policy = root.join("law_policy.json");
    let weighted_policy_path = out_dir.join("law_policy_weighted_part4.json");
    let mut weighted_policy = read_json(&law_policy);
    let signature_weights = weighted_policy["part4DistanceProfile"]["signatureWeights"]
        .as_array_mut()
        .expect("fixture LawPolicy has signature weights");
    for weight in signature_weights {
        if weight["axisRef"] == "sig-axis:semantic-inconsistency" {
            weight["weight"] = Value::from(5);
        }
    }
    let atom_weights = weighted_policy["part4DistanceProfile"]["atomWeights"]
        .as_array_mut()
        .expect("fixture LawPolicy has atom weights");
    for weight in atom_weights {
        if weight["axisRef"] == "atom.carrier" {
            weight["weight"] = Value::from(3);
        }
    }
    fs::write(
        &weighted_policy_path,
        serde_json::to_vec_pretty(&weighted_policy).expect("weighted policy serializes"),
    )
    .expect("weighted policy can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        weighted_policy_path
            .to_str()
            .expect("weighted law policy path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("output directory path is utf-8"),
        "--strict-distance",
        "--emit-raw-artifacts",
    ]);

    let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    let semantic_axis = packet["signatureDistanceReadings"][0]["axisDistances"]
        .as_array()
        .expect("axisDistances are present")
        .iter()
        .find(|axis| axis["signatureAxisRef"] == "sig-axis:semantic-inconsistency")
        .expect("semantic axis distance is present");

    assert_eq!(
        semantic_axis["axisDistance"]["measuredValue"].as_i64(),
        Some(5000),
        "strict-distance analyze must use selected signature weight"
    );
    assert!(
        semantic_axis["axisDistance"]["evaluatorBasisRefs"]
            .as_array()
            .into_iter()
            .flatten()
            .any(|basis| basis.as_str() == Some("profileWeight:sig-axis:semantic-inconsistency=5")),
        "axis distance must expose the selected profile weight in evaluator basis"
    );
    assert_eq!(
        summary["distanceDiagnosis"]["topMovedAxes"][0]["axisDistance"]["measuredValue"].as_i64(),
        Some(5000),
        "summary topMovedAxes must reflect the weighted raw packet distance"
    );

    let carrier_component = packet["atomDistanceReadings"]
        .as_array()
        .expect("atom distance readings are present")
        .iter()
        .flat_map(|reading| {
            reading["componentDistances"]
                .as_array()
                .into_iter()
                .flatten()
        })
        .find(|component| component["componentKind"] == "carrier")
        .expect("carrier component distance is present");
    assert_eq!(
        carrier_component["weight"].as_i64(),
        Some(1050),
        "strict-distance analyze must use selected atom component weight"
    );
    assert!(
        carrier_component["evaluatorBasisRefs"]
            .as_array()
            .into_iter()
            .flatten()
            .any(|basis| basis.as_str() == Some("profileWeight:carrier:1050")),
        "atom component distance must expose the selected profile weight in evaluator basis"
    );
}

#[test]
fn atom_viewer_uses_atom_shape_distance_inputs_for_molecule_layout() {
    let viewer_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("viewer/archsig-atom-viewer.html");
    let viewer = fs::read_to_string(&viewer_path).expect("viewer html can be read");

    for required in [
        "geometry.viewerDistanceInputs",
        "atomToViewerDistances",
        "viewerDistances",
        "function viewerDistanceProfile",
        "function viewerDistanceEmbedding",
        "function componentAxisVector",
        "distanceProfile.meanDistance",
        "distanceProfile.offset",
        "function renderViewerDistanceBonds",
        "AtomShape distance from molecule center",
    ] {
        assert!(
            viewer.contains(required),
            "atom viewer must use AtomShape viewerDistanceInputs in molecule layout: missing {required}"
        );
    }
}

#[test]
fn atom_viewer_reads_insight_report_surface_contract() {
    let viewer_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("viewer/archsig-atom-viewer.html");
    let viewer = fs::read_to_string(&viewer_path).expect("viewer html can be read");

    for required in [
        "Insight Queue",
        "Suggested Next Inspections",
        "Decision Bar",
        "Read this first",
        "copy source refs",
        "Start tour",
        "viewerVisualScenes",
        "axisMapping",
        "sceneForMode",
        "modeForScene",
        "sceneNodeColor",
        "renderSceneLayers",
        "sceneLayerMesh",
        "renderGluingGeometry",
        "renderNerveGeometry",
        "renderCocycleRibbon",
        "renderLocusField",
        "renderForbiddenCages",
        "renderRepairMorphs",
        "renderAtomGlyphOverlays",
        "atomGlyphGeometry",
        "atomGlyphColor",
        "updateRepairMorphAnimation",
        "sceneAxisPosition",
        "legendSwatchColor",
        "legendValueText",
        "gluingGeometry.",
        "value=\"obstructions\"",
        "LineDashedMaterial",
        "ConeGeometry",
        "repairMorphArrow",
        "cocycleSupportEdges",
        "thicknessRole",
        "visualEncodingChannel",
        "thickness",
        "window.__archsigViewerDebug",
        "sceneColorHex",
        "handleReportAction",
        "const reportEl = document.getElementById(\"report\")",
        "startGuidedTour",
        "showTourStep",
        "data-tour-id",
        "data-tour-next",
        "navigator.clipboard.writeText",
        "data-scene-id",
        "data-copy-source-refs",
        "Boolean(data?.decisionBar)",
        "evidenceDetailShape",
        "holonomyLikeGapMarker",
        "blockedUnmeasuredRegion",
        "forbiddenSupportCage",
        "not automatic repair",
    ] {
        assert!(
            viewer.contains(required),
            "atom viewer must read the insight report surface contract: missing {required}"
        );
    }
}

#[test]
#[ignore = "legacy large v0 ArchMap viewer projection is no longer current runtime surface"]
fn cli_analyze_bounds_atom_viewer_data_for_large_repo_projection() {
    let out_dir = temp_dir("analyze-large-viewer-data");
    let root = fixture_root();
    let archmap_path = out_dir.join("large-archmap.json");
    let mut archmap = read_json(&root.join("archmap.json"));
    expand_large_archmap_for_viewer_projection(&mut archmap);
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("large archmap serializes"),
    )
    .expect("large archmap can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("output directory path is utf-8"),
    ]);

    let viewer_data = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    let node_limit = viewer_data["layoutSettings"]["nodeLimit"]
        .as_u64()
        .expect("node limit is number") as usize;
    let molecule_limit = viewer_data["layoutSettings"]["moleculeGroupLimit"]
        .as_u64()
        .expect("molecule limit is number") as usize;
    let edge_limit = viewer_data["layoutSettings"]["edgeLimit"]
        .as_u64()
        .expect("edge limit is number") as usize;
    let source_ref_sample_limit = viewer_data["layoutSettings"]["sourceRefSampleLimit"]
        .as_u64()
        .expect("source ref sample limit is number") as usize;
    let label_limit = viewer_data["layoutSettings"]["labelLimit"]
        .as_u64()
        .expect("label limit is number") as usize;

    let atom_nodes = viewer_data["atomNodes"]
        .as_array()
        .expect("atom nodes are array");
    let molecule_groups = viewer_data["moleculeGroups"]
        .as_array()
        .expect("molecule groups are array");
    let atom_edges = viewer_data["atomEdges"]
        .as_array()
        .expect("atom edges are array");

    assert_eq!(node_limit, 20_000);
    assert_eq!(molecule_limit, 120);
    assert_eq!(edge_limit, 30_000);
    assert!(atom_nodes.len() <= node_limit);
    assert_eq!(molecule_groups.len(), molecule_limit);
    assert!(atom_edges.len() <= edge_limit);
    if atom_nodes.len() == node_limit {
        assert!(
            atom_nodes
                .iter()
                .any(|node| node["nodeId"] == "atom:synthetic:late-hotspot"),
            "top-N priority selection must retain high-priority late atoms instead of taking only the first N"
        );
    }

    for node in atom_nodes {
        assert!(
            node["sourceRefSamples"]
                .as_array()
                .is_some_and(|samples| samples.len() <= source_ref_sample_limit),
            "atom source refs must be bounded samples"
        );
        assert!(
            node["sourceRefCount"].as_u64().is_some_and(
                |count| count >= node["sourceRefSamples"].as_array().unwrap().len() as u64
            ),
            "atom source ref count must preserve omitted source ref context"
        );
        assert!(
            node["labels"]
                .as_array()
                .is_some_and(|labels| labels.len() <= label_limit),
            "atom labels must be bounded"
        );
    }
    for group in molecule_groups {
        assert!(
            group["sourceRefSamples"]
                .as_array()
                .is_some_and(|samples| samples.len() <= source_ref_sample_limit),
            "molecule source refs must be bounded samples"
        );
        assert!(
            group["labels"]
                .as_array()
                .is_some_and(|labels| labels.len() <= label_limit),
            "molecule labels must be bounded"
        );
    }

    let total_atom_count = archmap["atomObservations"]
        .as_array()
        .expect("expanded archmap atom observations are array")
        .len();
    assert_eq!(
        viewer_data["omittedDetailCounts"]["atomNodes"].as_u64(),
        Some(total_atom_count.saturating_sub(node_limit) as u64),
        "viewer data must record omitted atom node count"
    );
    assert!(
        viewer_data["omittedDetailCounts"]["moleculeGroups"]
            .as_u64()
            .is_some_and(|count| count > 0),
        "viewer data must record omitted molecule group count"
    );
    assert!(
        viewer_data["omittedDetailCounts"]["sourceRefs"]
            .as_u64()
            .is_some_and(|count| count > 0),
        "viewer data must record omitted source ref count"
    );
    assert!(
        viewer_data["omittedDetailCounts"]["omittedReasons"]
            .as_array()
            .is_some_and(|reasons| !reasons.is_empty()),
        "viewer data must explain why detail was omitted"
    );
}

#[test]
#[ignore = "legacy v0 raw packet FieldSig handoff is no longer current runtime surface"]
fn cli_analyze_emit_raw_artifacts_writes_field_sig_handoff_packet() {
    let out_dir = temp_dir("analyze-workflow-raw-artifacts");
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
        "--emit-raw-artifacts",
    ]);

    for file in [
        "archsig-analysis-packet.json",
        "archsig-analysis-detail-index.json",
        "llm-interpretation-packet.json",
    ] {
        assert!(
            out_dir.join(file).is_file(),
            "--emit-raw-artifacts must write {file}"
        );
    }
    let analysis_packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    assert_eq!(
        analysis_packet["schemaVersion"],
        "archsig-analysis-packet-v0"
    );
    assert_part4_cross_surface_axis_status_consistency(&analysis_packet);
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
        analysis_packet["generatedAtomShapes"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && analysis_packet["generatedMolecules"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && analysis_packet["generatedLawInputs"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && analysis_packet["generatedObstructions"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && analysis_packet["generatedRepairTargets"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && analysis_packet["viewerDistanceInputs"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "analysis packet must materialize generated AtomShape, molecule, law input, obstruction, repair target, and viewer distance surfaces"
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
    assert!(
        analysis_validation["summary"]["generatedAtomShapeCount"]
            .as_u64()
            .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["generatedMoleculeCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["generatedLawInputCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["generatedObstructionCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["generatedRepairTargetCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["viewerDistanceInputCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["configurationDistanceReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["signatureDistanceReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["operationDistanceReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["obstructionMeasureReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && analysis_validation["summary"]["curvatureMassReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0),
        "validation summary must count generated middle-layer, viewer distance, configuration distance, signature distance, operation distance, obstruction measure, and curvature mass surfaces"
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
    let run_manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert_eq!(run_manifest["rawArtifactRetention"].as_str(), Some("full"));
    assert_eq!(
        run_manifest["rawArtifactPaths"]["analysisPacket"].as_str(),
        Some("archsig-analysis-packet.json")
    );
}

#[test]
#[ignore = "legacy v0 generated-atom acceptance fixture is no longer current runtime surface"]
fn atom_generated_acceptance_fixture_materializes_local_middle_layer() {
    let out_dir = temp_dir("atom-generated-acceptance");
    let root = atom_generated_acceptance_root();
    let manifest = read_json(&root.join("manifest.json"));
    assert_eq!(
        manifest["schemaVersion"],
        "archsig-atom-generated-acceptance-manifest-v0"
    );
    assert!(
        manifest["nonConclusions"].as_array().is_some_and(|items| {
            items.iter().any(|item| {
                item.as_str()
                    .is_some_and(|text| text.contains("not Lean theorem proofs"))
            })
        }),
        "acceptance fixture must preserve generated-surface non-conclusions"
    );

    let archmap = root.join(
        manifest["archmapPath"]
            .as_str()
            .expect("manifest archmap path is present"),
    );
    let law_policy = root.join(
        manifest["lawPolicyPath"]
            .as_str()
            .expect("manifest law policy path is present"),
    );
    let packet_path = out_dir.join("archsig-analysis-packet.json");
    let validation_path = out_dir.join("archsig-analysis-validation.json");

    run_sig0(&[
        "archsig-analysis",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        law_policy.to_str().expect("law policy path is utf-8"),
        "--out",
        packet_path.to_str().expect("packet path is utf-8"),
        "--validation-out",
        validation_path.to_str().expect("validation path is utf-8"),
    ]);

    let packet = read_json(&packet_path);
    let validation = read_json(&validation_path);
    assert_eq!(validation["summary"]["result"], "pass");
    let expectations = &manifest["expectations"];
    let minimum_generated_molecules = expectations["generatedMolecules"]
        .as_u64()
        .expect("generatedMolecules expectation is present")
        as usize;
    let minimum_generated_law_inputs = expectations["generatedLawInputs"]
        .as_u64()
        .expect("generatedLawInputs expectation is present")
        as usize;
    let minimum_generated_repair_targets = expectations["generatedRepairTargets"]
        .as_u64()
        .expect("generatedRepairTargets expectation is present")
        as usize;
    let minimum_applicable_law_axes = expectations["applicableLawAxes"]
        .as_u64()
        .expect("applicableLawAxes expectation is present")
        as usize;
    let minimum_viewer_distance_inputs = expectations["viewerDistanceInputs"]
        .as_u64()
        .expect("viewerDistanceInputs expectation is present")
        as usize;
    let expected_local_statuses = expectations["localStatuses"]
        .as_array()
        .expect("localStatuses expectation is present");

    assert!(
        packet["generatedMolecules"]
            .as_array()
            .is_some_and(|items| items.len() >= minimum_generated_molecules),
        "atom-generated acceptance must materialize generated molecules"
    );
    assert!(
        packet["generatedLawInputs"]
            .as_array()
            .is_some_and(|items| {
                items.len() >= minimum_generated_law_inputs
                    && items.iter().any(|item| {
                        item["applicableLawAxes"]
                            .as_array()
                            .is_some_and(|axes| axes.len() >= minimum_applicable_law_axes)
                            && item["localStatuses"].as_array().is_some_and(|statuses| {
                                statuses.iter().any(|status| status == "localSatisfied")
                            })
                    })
            }),
        "generated law inputs must expose applicable law axes and localSatisfied status"
    );
    for expected_status in expected_local_statuses {
        let expected_status = expected_status
            .as_str()
            .expect("local status expectation is string");
        let present = packet["generatedLawInputs"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| {
                    item["localStatuses"].as_array().is_some_and(|statuses| {
                        statuses.iter().any(|status| status == expected_status)
                    })
                })
            })
            || packet["generatedObstructions"]
                .as_array()
                .is_some_and(|items| {
                    items.iter().any(|item| {
                        item["localStatus"] == expected_status
                            || item["blockerStatus"] == expected_status
                    })
                });
        assert!(
            present,
            "atom-generated acceptance must expose expected local status {expected_status}"
        );
    }
    assert!(
        packet["generatedObstructions"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| {
                    item["localStatus"] == "localViolated"
                        && item["blockerStatus"] == "locallyBlocked"
                })
            }),
        "generated obstructions must expose localViolated and locallyBlocked status"
    );
    assert!(
        packet["generatedRepairTargets"]
            .as_array()
            .is_some_and(|items| {
                items.len() >= minimum_generated_repair_targets
                    && items.iter().any(|item| {
                        item["targetKind"] == "shapeLevelGeneratedRepairTarget"
                            && item["generatedObstructionRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && item["generatedMoleculeRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && item["atomShapeRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                            && item["requiredPortOrSlot"] == "portOrSlotOrValenceMismatch"
                            && item["evidenceBoundary"]
                                .as_str()
                                .is_some_and(|text| text.contains("not a free-form recommendation"))
                    })
            }),
        "generated repair targets must localize repair candidates to generated obstruction, molecule, and AtomShape refs"
    );
    assert!(
        packet["viewerDistanceInputs"]
            .as_array()
            .is_some_and(|items| items.len() >= minimum_viewer_distance_inputs),
        "atom-generated acceptance must expose viewer distance inputs"
    );
    let viewer_distance_inputs = packet["viewerDistanceInputs"]
        .as_array()
        .expect("viewerDistanceInputs are present");
    let mut covered_distance_pairs = BTreeSet::<(String, String, String)>::new();
    for distance in viewer_distance_inputs {
        let molecule_ref = distance["generatedMoleculeRef"]
            .as_str()
            .expect("viewer distance input has generatedMoleculeRef")
            .to_string();
        let shape_refs = distance["atomShapeRefs"]
            .as_array()
            .expect("viewer distance input has atomShapeRefs");
        assert_eq!(
            shape_refs.len(),
            2,
            "viewer distance input must compare exactly two AtomShape refs"
        );
        let left = shape_refs[0]
            .as_str()
            .expect("left AtomShape ref is string")
            .to_string();
        let right = shape_refs[1]
            .as_str()
            .expect("right AtomShape ref is string")
            .to_string();
        let expected_delta_sum = distance["coordinateComponents"]
            .as_array()
            .expect("viewer distance has coordinateComponents")
            .iter()
            .map(|component| {
                component
                    .as_str()
                    .and_then(|text| text.rsplit_once("delta="))
                    .and_then(|(_prefix, delta)| delta.parse::<i64>().ok())
                    .expect("coordinate component carries numeric delta")
            })
            .sum::<i64>();
        assert_eq!(
            distance["distanceValue"].as_i64(),
            Some(expected_delta_sum),
            "viewer distance value must equal the sum of AtomShape coordinate deltas"
        );
        let (left, right) = ordered_test_pair(left, right);
        covered_distance_pairs.insert((molecule_ref, left, right));
    }
    for molecule in packet["generatedMolecules"]
        .as_array()
        .expect("generatedMolecules are present")
    {
        let molecule_ref = molecule["generatedMoleculeId"]
            .as_str()
            .expect("generated molecule id is present")
            .to_string();
        let shape_refs = molecule["atomShapeRefs"]
            .as_array()
            .expect("generated molecule has atomShapeRefs")
            .iter()
            .map(|shape_ref| {
                shape_ref
                    .as_str()
                    .expect("AtomShape ref is string")
                    .to_string()
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        for left_index in 0..shape_refs.len() {
            for right_index in (left_index + 1)..shape_refs.len() {
                let (left, right) = ordered_test_pair(
                    shape_refs[left_index].clone(),
                    shape_refs[right_index].clone(),
                );
                assert!(
                    covered_distance_pairs.contains(&(molecule_ref.clone(), left, right)),
                    "viewerDistanceInputs must cover every generated molecule AtomShape pair"
                );
            }
        }
    }
}

fn ordered_test_pair(left: String, right: String) -> (String, String) {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

#[test]
#[ignore = "legacy v0 validation-failure summary behavior is no longer current runtime surface"]
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
    for file in [
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
    ] {
        assert!(
            out_dir.join(file).is_file(),
            "analyze should still write {file} before returning validation failure"
        );
    }
    assert!(
        !out_dir.join("archsig-analysis-packet.json").exists(),
        "analyze should still omit raw packet by default on validation failure"
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
#[ignore = "legacy v0 archsig-analysis step command is no longer current runtime surface"]
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
#[ignore = "legacy v0 semantic monodromy fixture is no longer current runtime surface"]
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
#[ignore = "legacy v0 operation square fixture is no longer current runtime surface"]
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
            "representation-metric-faithfulness-boundary" => {
                let minimum = case["minimumRepresentationMetricReadings"]
                    .as_u64()
                    .expect("minimum representation metric readings is present");
                let readings = packet["representationMetricReadings"]
                    .as_array()
                    .expect("representation metric readings are array");
                assert!(
                    readings.len() as u64 >= minimum
                        && readings.iter().all(|reading| {
                            reading["biLipschitzFaithfulness"]["status"] == "blocked"
                                && reading["biLipschitzFaithfulness"]["blockerRefs"]
                                    .as_array()
                                    .is_some_and(|items| !items.is_empty())
                                && reading["analyticDistance"]["reading"].as_str().is_some_and(
                                    |text| text.contains("not an architecture quality score"),
                                )
                        }),
                    "representation metric readings must keep faithfulness lower bounds blocked by coverage / witness completeness"
                );
                assert!(
                    validation["summary"]["representationMetricReadingCount"]
                        .as_u64()
                        .is_some_and(|count| count >= minimum)
                        && packet["llmInterpretationPacket"]["representationMetricSummary"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty()),
                    "ACTS validation and LLM summary must expose representation metric readings"
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
#[ignore = "legacy v0 complete ArchMap acceptance fixture is no longer current runtime surface"]
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
        "--emit-raw-artifacts",
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
    let archsig_validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    for check_id in [
        "archsig-analysis-packet-part4-distance-foundation",
        "archsig-analysis-packet-atom-distance-readings",
        "archsig-analysis-packet-configuration-distance-readings",
        "archsig-analysis-packet-signature-distance-readings",
        "archsig-analysis-packet-operation-distance-readings",
        "archsig-analysis-packet-obstruction-measure-readings",
        "archsig-analysis-packet-curvature-mass-readings",
        "archsig-analysis-packet-homotopy-distance-readings",
        "archsig-analysis-packet-representation-metric-readings",
        "archsig-analysis-packet-measurement-depth",
        "archsig-analysis-packet-proxy-regression-guardrails",
    ] {
        assert!(
            has_check_result(&archsig_validation, check_id, "pass"),
            "complete-first fixture validation must include passing Part IV anti-proxy check {check_id}"
        );
    }
    assert!(
        archsig_validation["summary"]["part4SupportingDistanceCount"]
            .as_u64()
            .is_some_and(|count| count >= 7)
            && archsig_validation["summary"]["atomDistanceReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && archsig_validation["summary"]["configurationDistanceReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && archsig_validation["summary"]["signatureDistanceReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && archsig_validation["summary"]["operationDistanceReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && archsig_validation["summary"]["obstructionMeasureReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && archsig_validation["summary"]["curvatureMassReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && archsig_validation["summary"]["homotopyDistanceReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0)
            && archsig_validation["summary"]["representationMetricReadingCount"]
                .as_u64()
                .is_some_and(|count| count > 0),
        "complete-first fixture must be the golden corpus for all major Part IV distance surfaces"
    );

    let packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    assert_part4_cross_surface_axis_status_consistency(&packet);
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
    let measured_axis_refs = signature_measured_axis_refs(&packet);
    assert!(
        unmeasured_surface_excludes_measured_axes(
            &summary["distanceDiagnosis"],
            &measured_axis_refs
        ),
        "complete-first summary must not report measured or zero signature axes as unmeasured"
    );
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
#[ignore = "legacy v0 pr-review path is no longer current runtime surface"]
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
        "--after-archmap",
        review
            .join("after_archmap.json")
            .to_str()
            .expect("after archmap path is utf-8"),
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
        json["canonicalInputs"]["afterArchMap"]["schemaVersion"],
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
    let drift = &json["prDriftReadings"][0];
    assert_eq!(
        drift["endpointSignatureDistance"]["status"], "measured",
        "PR endpoint distance must be measured from base/head ArchSig packets"
    );
    assert_eq!(
        drift["endpointSignatureDistance"]["measuredValue"], 1000,
        "semantic axis moves from one witness to zero under the head ArchMap"
    );
    assert_eq!(
        drift["totalPathMovement"]["pathGranularity"], "twoPointBaseHead",
        "endpoint distance and total movement must stay separated"
    );
    assert_eq!(
        drift["hiddenExcursionStatus"], "blockedWithoutIntermediateArchMapPathSnapshots",
        "without path snapshots, hidden excursion absence is blocked rather than inferred"
    );
    assert!(
        drift["topMovedAtoms"]
            .as_array()
            .is_some_and(|atoms| atoms.iter().any(|atom| {
                atom["atomObservationRef"] == "atom:contract:create-user"
                    && atom["sourceRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
            })),
        "top moved atoms must retain source-backed refs"
    );
    assert!(
        drift["topMovedAxes"]
            .as_array()
            .is_some_and(|axes| axes.iter().any(|axis| {
                axis["axisRef"] == "sig-axis:semantic-inconsistency"
                    && axis["sourceRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
            })),
        "top moved axes must be source-backed"
    );
    assert_eq!(
        drift["safeChangeBudget"]["status"], "blockedByCoverageGap",
        "coverage gaps must limit safe change budget rather than being rounded to zero"
    );
    assert!(
        json["architectureNavigationReport"]["recommendedReviewFocus"]
            .as_array()
            .is_some_and(|focus| focus
                .iter()
                .any(|item| { item == "coverage-gaps-limit-safe-change-budget" })),
        "navigation report must surface coverage-limited review focus"
    );
    assert!(json.get("nonConclusions").is_none());

    let path_report = out_dir.join("archsig-pr-review-with-path.json");
    run_sig0(&[
        "pr-review",
        "--base-archmap",
        minimal
            .join("archmap.json")
            .to_str()
            .expect("base archmap path is utf-8"),
        "--after-archmap",
        review
            .join("after_archmap.json")
            .to_str()
            .expect("after archmap path is utf-8"),
        "--path-archmap",
        minimal
            .join("archmap.json")
            .to_str()
            .expect("path archmap path is utf-8"),
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
        path_report.to_str().expect("path report path is utf-8"),
    ]);
    let path_json = read_json(&path_report);
    assert_eq!(
        path_json["canonicalInputs"]["pathArchMaps"]
            .as_array()
            .map(Vec::len),
        Some(1),
        "path ArchMap snapshots must be retained in canonical input provenance"
    );
    assert_eq!(
        path_json["prDriftReadings"][0]["hiddenExcursionStatus"],
        "measuredFromSuppliedIntermediateArchMapSnapshots"
    );
    assert_eq!(
        path_json["prDriftReadings"][0]["totalPathMovement"]["pathGranularity"],
        "suppliedIntermediateSnapshots"
    );
}

#[test]
#[ignore = "legacy v0 negative fixture corpus is no longer current runtime surface"]
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
#[ignore = "legacy v0 atom observation regression fixture is no longer current runtime surface"]
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
            .is_empty(),
        "expressiveness ArchMap lacks complete witness families and must not construct concern-only obstruction"
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
            "archmap-v1",
            "archmap-v2",
            "law-policy",
            "law-policy-v1",
            "measurement-profile-v1",
            "law-evaluator-registry-v1",
            "law-policy-validation-report",
            "normalized-archmap-v1",
            "normalized-archmap-v2",
            "typed-evaluator-results-v1",
            "architecture-distance-v1",
            "archsig-measurement-packet-v1",
            "archsig-analysis-packet",
            "archsig-analysis-packet-v1",
            "archsig-analysis-packet-validation-report",
            "archsig-run-manifest",
            "archsig-atom-viewer-data",
        ]
    );
    for entry in artifacts {
        let artifact_id = entry["artifactId"].as_str().expect("artifact id");
        let expected_role = match artifact_id {
            "archmap"
            | "archmap-validation-report"
            | "law-policy"
            | "law-policy-validation-report"
            | "archsig-analysis-packet"
            | "archsig-analysis-packet-validation-report" => "legacy",
            _ => "primary",
        };
        assert_eq!(
            entry["artifactRole"].as_str(),
            Some(expected_role),
            "unexpected artifact role for {artifact_id}"
        );
    }
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "architecture-distance-v1"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        description.contains("primary curvature geometry readings")
                    })
        }),
        "schema catalog must describe architecture-distance-v1 curvature primary surface"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "architecture-distance-v1"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        description.contains("primary homotopy filling geometry readings")
                    })
        }),
        "schema catalog must describe architecture-distance-v1 homotopy primary surface"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "architecture-distance-v1"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        description.contains("primary representation metric readings")
                    })
        }),
        "schema catalog must describe architecture-distance-v1 representation primary surface"
    );
}

#[test]
fn archsig_atom_viewer_static_app_is_packaged_asset() {
    let viewer_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("viewer/archsig-atom-viewer.html");
    let html = fs::read_to_string(&viewer_path).expect("atom viewer static html can be read");
    assert!(viewer_path.is_file(), "fixed Atom Viewer app must exist");
    assert!(
        html.contains("https://unpkg.com/three@"),
        "viewer must load CDN Three.js runtime"
    );
    assert!(
        html.contains("WebGPURenderer.js") && html.contains("WebGLRenderer"),
        "viewer must prefer WebGPU and keep a WebGL fallback"
    );
    assert!(
        html.contains("type=\"file\"")
            && html.contains("dragover")
            && html.contains("./archsig-atom-viewer-data.json"),
        "viewer must support file picker, drag-and-drop, and default viewer data loading"
    );
    assert!(
        html.contains("./archsig-analysis-summary.json")
            && html.contains("./archsig-run-manifest.json")
            && html.contains("rawArtifactPaths")
            && html.contains("analysisDetailIndex"),
        "viewer report pane must integrate summary, manifest, and raw artifact links when present"
    );
    for section in [
        "Overview",
        "Insight Queue",
        "Distance Diagnosis",
        "Suggested Next Inspections",
        "Coverage And Boundaries",
        "Artifacts",
        "Validation Status",
        "Omitted Detail",
    ] {
        assert!(
            html.contains(section),
            "viewer report pane must render {section}"
        );
    }
    assert!(
        html.contains("renderDistanceDiagnosis")
            && html.contains("compactRepresentationMetricValues")
            && html.contains("representationMetric")
            && html.contains("distanceBoundary")
            && html.contains("nonClaims")
            && html.contains("detailRefs"),
        "viewer must render distanceDiagnosis with boundary, non-claims, and detail refs"
    );
    assert!(
        html.contains("atomEdges")
            && html.contains("moleculeGroups")
            && html.contains("analysisOverlays"),
        "viewer must render atoms, molecules, edges, and overlays"
    );
    assert!(
        !html.contains("archsig-analysis-packet.json"),
        "viewer must not embed or load the raw analysis packet"
    );
}

#[test]
#[ignore = "legacy v0 Part IV negative corpus is no longer current runtime surface"]
fn part4_negative_fixture_corpus_tracks_distance_surface_regressions() {
    let corpus = read_json(&negative_root().join("part4_distance_surface_negative_cases.json"));
    let cases = corpus["cases"]
        .as_array()
        .expect("Part IV negative corpus has cases");
    for expected in [
        "stale-axis-namespace",
        "profile-weight-ignored",
        "missing-operation-cost-not-promoted",
        "summary-distance-id-null",
        "stale-detail-ref",
    ] {
        assert!(
            cases
                .iter()
                .any(|case| case["caseId"].as_str() == Some(expected)),
            "negative corpus must track {expected}"
        );
    }
    assert!(
        cases.iter().all(|case| {
            case["sourceIssue"]
                .as_str()
                .is_some_and(|issue| issue.starts_with('#'))
                && case["assertion"].as_str().is_some()
                && case["fixtureKind"].as_str().is_some()
        }),
        "each negative case must record source issue, fixture kind, and assertion"
    );

    let policy_cases =
        read_json(&negative_root().join("part4_distance_policy_negative_cases.json"));
    let policy_cases = policy_cases["cases"]
        .as_array()
        .expect("Part IV policy negative corpus has cases");
    assert!(
        policy_cases.len() >= 3,
        "policy negative corpus must contain executable validation cases"
    );
    for case in policy_cases {
        let out_dir = temp_dir(case["caseId"].as_str().expect("negative case has caseId"));
        let root = fixture_root();
        let policy_path = out_dir.join("law_policy_negative.json");
        let mut policy = read_json(&root.join("law_policy.json"));
        apply_part4_policy_negative_mutation(&mut policy, case);
        fs::write(
            &policy_path,
            serde_json::to_vec_pretty(&policy).expect("negative policy serializes"),
        )
        .expect("negative policy can be written");

        let output = run_sig0_output(&[
            "analyze",
            "--archmap",
            root.join("archmap.json")
                .to_str()
                .expect("archmap path is utf-8"),
            "--law-policy",
            policy_path
                .to_str()
                .expect("negative law policy path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("negative out dir is utf-8"),
            "--strict-distance",
        ]);

        assert!(
            !output.status.success(),
            "negative policy case must fail strict-distance: {}",
            case["caseId"]
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        let expected = case["expectedStderr"]
            .as_str()
            .expect("negative case declares expected stderr");
        assert!(
            stderr.contains(expected),
            "negative policy case {} stderr should contain {expected}\n{stderr}",
            case["caseId"]
        );
    }
}

fn apply_part4_policy_negative_mutation(policy: &mut Value, case: &Value) {
    let mutation = &case["mutation"];
    let kind = mutation["kind"]
        .as_str()
        .expect("negative case mutation has kind");
    match kind {
        "removeSignatureWeight" => {
            let axis_ref = mutation["axisRef"]
                .as_str()
                .expect("removeSignatureWeight has axisRef");
            let weights = policy["part4DistanceProfile"]["signatureWeights"]
                .as_array_mut()
                .expect("fixture policy has signatureWeights");
            weights.retain(|weight| weight["axisRef"].as_str() != Some(axis_ref));
        }
        "addAtomWeight" => {
            let axis_ref = mutation["axisRef"]
                .as_str()
                .expect("addAtomWeight has axisRef");
            let weight = mutation["weight"]
                .as_i64()
                .expect("addAtomWeight has weight");
            let weights = policy["part4DistanceProfile"]["atomWeights"]
                .as_array_mut()
                .expect("fixture policy has atomWeights");
            weights.push(serde_json::json!({
                "axisRef": axis_ref,
                "weight": weight,
                "sourceRef": "fixture:negative-part4-distance-policy"
            }));
        }
        "setSignatureWeight" => {
            let axis_ref = mutation["axisRef"]
                .as_str()
                .expect("setSignatureWeight has axisRef");
            let value = Value::from(
                mutation["weight"]
                    .as_i64()
                    .expect("setSignatureWeight has weight"),
            );
            let weights = policy["part4DistanceProfile"]["signatureWeights"]
                .as_array_mut()
                .expect("fixture policy has signatureWeights");
            let weight = weights
                .iter_mut()
                .find(|weight| weight["axisRef"].as_str() == Some(axis_ref))
                .expect("fixture policy has target signature weight");
            weight["weight"] = value;
        }
        other => panic!("unknown Part IV negative policy mutation kind: {other}"),
    }
}

#[test]
fn archsig_release_workflow_packages_output_viewer_contract() {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repo root");
    let release_workflow =
        fs::read_to_string(repo_root.join(".github/workflows/archsig-release.yml"))
            .expect("release workflow can be read");
    assert!(
        release_workflow.contains("package/archsig-atom-viewer.html")
            && release_workflow.contains("package/viewer/archsig-atom-viewer.html")
            && release_workflow.contains("test -s package/archsig-atom-viewer.html"),
        "release workflow must package and verify the fixed Atom Viewer app"
    );
    assert!(
        release_workflow.contains("package/docs/artifacts-and-boundaries.md")
            && release_workflow.contains("package/skills"),
        "release workflow must ship docs and skills that describe the output contract"
    );
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

fn run_sig0_expect_code(args: &[&str], expected_code: i32) {
    let output = run_sig0_output(args);
    assert_eq!(
        output.status.code(),
        Some(expected_code),
        "archsig {:?} exit code mismatch\nstdout:\n{}\nstderr:\n{}",
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

fn invariant_by_id<'a>(packet: &'a Value, invariant_id: &str) -> &'a Value {
    packet["computedInvariants"]
        .as_array()
        .expect("computedInvariants is array")
        .iter()
        .find(|invariant| invariant["invariantId"] == invariant_id)
        .unwrap_or_else(|| panic!("missing computed invariant {invariant_id}"))
}

fn assert_public_artifact_omits_part4(label: &str, value: &Value) {
    let text = serde_json::to_string(value).expect("json value serializes");
    assert!(
        !text.contains("Part IV"),
        "{label} must not expose Part IV as public v1 summary wording"
    );
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

fn string_set(value: &Value) -> BTreeSet<String> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|item| item.as_str().map(str::to_string))
        .collect()
}

fn unmeasured_surface_excludes_measured_axes(
    distance_diagnosis: &Value,
    measured_axis_refs: &BTreeSet<String>,
) -> bool {
    let unmeasured_axes = string_set(&distance_diagnosis["unmeasuredAxes"]);
    let measured_axis_aliases = measured_axis_refs
        .iter()
        .flat_map(|axis| axis_aliases(axis))
        .collect::<BTreeSet<_>>();
    let unmeasured_axis_aliases = unmeasured_axes
        .iter()
        .flat_map(|axis| axis_aliases(axis))
        .collect::<BTreeSet<_>>();
    unmeasured_axis_aliases
        .intersection(&measured_axis_aliases)
        .next()
        .is_none()
}

fn axis_aliases(axis_ref: &str) -> BTreeSet<String> {
    let mut aliases = BTreeSet::from([axis_ref.to_string()]);
    if let Some(suffix) = axis_ref.strip_prefix("sig-axis:") {
        aliases.insert(format!("axis:{suffix}"));
    }
    if let Some(suffix) = axis_ref.strip_prefix("axis:") {
        aliases.insert(format!("sig-axis:{suffix}"));
    }
    aliases
}

fn assert_part4_distance_diagnosis_refs_resolve(summary: &Value, packet: &Value) {
    let refs = summary["distanceDiagnosis"]["detailRefs"]
        .as_array()
        .expect("distanceDiagnosis detailRefs is array");
    assert!(
        !refs.is_empty(),
        "distanceDiagnosis detailRefs must be nonempty"
    );
    for reference in refs {
        let reference = reference
            .as_str()
            .expect("distanceDiagnosis detail ref is string");
        let pointer = reference
            .strip_prefix("packet:")
            .expect("distanceDiagnosis detail ref uses packet: prefix");
        let target = packet.pointer(pointer).unwrap_or_else(|| {
            panic!("distanceDiagnosis detail ref must resolve into raw packet: {reference}")
        });
        assert!(
            !target.as_array().is_some_and(Vec::is_empty),
            "distanceDiagnosis detail ref must not resolve to an empty packet section: {reference}"
        );
    }
}

fn signature_measured_axis_refs(packet: &Value) -> BTreeSet<String> {
    packet["signatureDistanceReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .flat_map(|reading| string_set(&reading["measuredAxisRefs"]))
        .collect()
}

fn assert_part4_cross_surface_axis_status_consistency(packet: &Value) {
    let diagnostic_scope = &packet["part4DistanceFoundation"]["diagnosticScope"];
    let scope_measured_axes = string_set(&diagnostic_scope["measuredAxisRefs"]);
    let scope_unmeasured_axes = string_set(&diagnostic_scope["unmeasuredAxisRefs"]);
    let scope_measured_axis_aliases = scope_measured_axes
        .iter()
        .flat_map(|axis| axis_aliases(axis))
        .collect::<BTreeSet<_>>();
    let scope_unmeasured_axis_aliases = scope_unmeasured_axes
        .iter()
        .flat_map(|axis| axis_aliases(axis))
        .collect::<BTreeSet<_>>();
    let overlap = scope_measured_axes
        .intersection(&scope_unmeasured_axes)
        .cloned()
        .collect::<Vec<_>>();
    assert!(
        overlap.is_empty(),
        "DiagnosticScope must not classify axes as both measured and unmeasured: {overlap:?}"
    );
    assert!(
        diagnostic_scope["blockerRefs"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .all(|blocker| !blocker.starts_with("issue:#")),
        "DiagnosticScope blockerRefs must not keep closed implementation issue placeholders"
    );
    let stale_unmeasured_blockers = diagnostic_scope["blockerRefs"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .filter_map(|blocker| blocker.strip_prefix("unmeasuredAxis:"))
        .filter(|axis| {
            axis_aliases(axis)
                .into_iter()
                .any(|axis| scope_measured_axis_aliases.contains(&axis))
        })
        .map(str::to_string)
        .collect::<Vec<_>>();
    assert!(
        stale_unmeasured_blockers.is_empty(),
        "DiagnosticScope blockerRefs must not keep unmeasured-axis blockers for measured axes: {stale_unmeasured_blockers:?}"
    );

    let signature_measured_axes = signature_measured_axis_refs(packet);
    let signature_measured_axis_aliases = signature_measured_axes
        .iter()
        .flat_map(|axis| axis_aliases(axis))
        .collect::<BTreeSet<_>>();
    let signature_unmeasured_axes = packet["signatureDistanceReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .flat_map(|reading| {
            string_set(&reading["unmeasuredAxisRefs"])
                .into_iter()
                .chain(string_set(&reading["incomparableAxisRefs"]))
        })
        .filter(|axis| !signature_measured_axes.contains(axis))
        .collect::<BTreeSet<_>>();

    let missing_measured = signature_measured_axes
        .difference(&scope_measured_axes)
        .cloned()
        .collect::<Vec<_>>();
    assert!(
        missing_measured.is_empty(),
        "DiagnosticScope measuredAxisRefs must include measured or zero signature axes: {missing_measured:?}"
    );
    let stale_unmeasured = scope_unmeasured_axis_aliases
        .intersection(&signature_measured_axis_aliases)
        .cloned()
        .collect::<Vec<_>>();
    assert!(
        stale_unmeasured.is_empty(),
        "measured or zero signature axes must not remain in DiagnosticScope unmeasuredAxisRefs: {stale_unmeasured:?}"
    );
    let missing_unmeasured = signature_unmeasured_axes
        .difference(&scope_unmeasured_axes)
        .cloned()
        .collect::<Vec<_>>();
    assert!(
        missing_unmeasured.is_empty(),
        "DiagnosticScope unmeasuredAxisRefs must include non-measured signature axes: {missing_unmeasured:?}"
    );
    assert!(
        packet["llmInterpretationPacket"]["distanceDiagnosisSummary"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .any(|summary| summary.contains("diagnosticScope measuredAxes=")
                && summary.contains("boundary=evaluator-synchronized")),
        "LLM distanceDiagnosisSummary must expose the evaluator-synchronized DiagnosticScope status"
    );
}

fn expand_large_archmap_for_viewer_projection(archmap: &mut Value) {
    archmap["sourceInventoryRef"] = Value::Null;
    let base_atom = archmap["atomObservations"][0].clone();
    let base_molecule = archmap["moleculeObservations"][0].clone();
    let mut declared_source_refs = Vec::new();
    let mut atoms = archmap["atomObservations"]
        .as_array()
        .expect("fixture atom observations are array")
        .clone();
    for index in 0..319 {
        let mut atom = base_atom.clone();
        atom["atomObservationId"] = Value::String(format!("atom:synthetic:{index:03}"));
        atom["atomFamily"] = Value::String(if index % 5 == 0 {
            "boundary".to_string()
        } else {
            "existence".to_string()
        });
        atom["subjectRef"] = Value::String(format!("component.synthetic.{index:03}"));
        atom["predicate"] = Value::String(format!("synthetic component {index:03} exists"));
        atom["objectRefs"] = serde_json::json!([format!("component.synthetic.{index:03}")]);
        atom["confidence"] = Value::String("low".to_string());
        let source_refs = synthetic_source_refs(index, 5);
        append_declared_source_refs(&mut declared_source_refs, &source_refs);
        atom["sourceRefs"] = source_refs;
        atom["projectionRefs"] = serde_json::json!([format!("projection:synthetic:{index:03}")]);
        atoms.push(atom);
    }
    let mut late_hotspot = base_atom;
    late_hotspot["atomObservationId"] = Value::String("atom:synthetic:late-hotspot".to_string());
    late_hotspot["atomFamily"] = Value::String("boundary".to_string());
    late_hotspot["subjectRef"] = Value::String("component.synthetic.late-hotspot".to_string());
    late_hotspot["predicate"] =
        Value::String("late hotspot component crosses key boundary".to_string());
    late_hotspot["objectRefs"] = serde_json::json!([
        "component.synthetic.late-hotspot",
        "boundary.synthetic.hotspot"
    ]);
    late_hotspot["confidence"] = Value::String("high".to_string());
    let hotspot_source_refs = synthetic_source_refs(999, 12);
    append_declared_source_refs(&mut declared_source_refs, &hotspot_source_refs);
    late_hotspot["sourceRefs"] = hotspot_source_refs;
    late_hotspot["projectionRefs"] = serde_json::json!([
        "projection:synthetic:late-hotspot",
        "projection:synthetic:boundary"
    ]);
    atoms.push(late_hotspot);
    archmap["atomObservations"] = Value::Array(atoms);

    let mut molecules = archmap["moleculeObservations"]
        .as_array()
        .expect("fixture molecule observations are array")
        .clone();
    for index in 0..160 {
        let mut molecule = base_molecule.clone();
        molecule["moleculeObservationId"] = Value::String(format!("molecule:synthetic:{index:03}"));
        molecule["moleculeFamily"] = Value::String(if index % 4 == 0 {
            "boundary-subsystem".to_string()
        } else {
            "responsibility".to_string()
        });
        molecule["roleName"] = Value::String(format!("synthetic subsystem {index:03}"));
        let first = (index * 2) % 319;
        molecule["atomObservationRefs"] = serde_json::json!([
            format!("atom:synthetic:{first:03}"),
            format!("atom:synthetic:{:03}", (first + 1) % 319),
            format!("atom:synthetic:{:03}", (first + 2) % 319),
            "atom:synthetic:late-hotspot"
        ]);
        molecule["confidence"] = Value::String(if index % 4 == 0 {
            "high".to_string()
        } else {
            "medium".to_string()
        });
        let source_refs = synthetic_source_refs(index + 500, 6);
        append_declared_source_refs(&mut declared_source_refs, &source_refs);
        molecule["sourceRefs"] = source_refs;
        molecules.push(molecule);
    }
    archmap["moleculeObservations"] = Value::Array(molecules);

    archmap["sourceUniverse"]["includedRefs"]
        .as_array_mut()
        .expect("source universe included refs are array")
        .extend(declared_source_refs);
}

fn synthetic_source_refs(seed: usize, count: usize) -> Value {
    Value::Array(
        (0..count)
            .map(|offset| {
                serde_json::json!({
                    "artifactId": format!("synthetic-src-{seed}-{offset}"),
                    "kind": "file",
                    "path": format!("src/synthetic/{seed}/{offset}.ts"),
                    "symbol": format!("symbol_{seed}_{offset}"),
                    "line": offset + 1
                })
            })
            .collect(),
    )
}

fn append_declared_source_refs(target: &mut Vec<Value>, source_refs: &Value) {
    target.extend(
        source_refs
            .as_array()
            .expect("synthetic source refs are array")
            .iter()
            .cloned(),
    );
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
    let part4_distance = &json["part4DistanceFoundation"];
    assert!(
        part4_distance["profile"]["profileId"]
            .as_str()
            .is_some_and(|profile| profile.starts_with("part4-distance-profile:"))
            && part4_distance["profile"]["unmeasuredPolicy"]
                .as_str()
                .is_some_and(|policy| policy.contains("not zero"))
            && part4_distance["diagnosticScope"]["observedAtomRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
            && part4_distance["supportingDistances"]
                .as_array()
                .is_some_and(|items| items.len() >= 7),
        "Part IV distance foundation must expose profile, diagnostic scope, and all unmeasured distance contract rows"
    );
    assert!(
        part4_distance["supportingDistances"]
            .as_array()
            .expect("supporting distances are array")
            .iter()
            .all(|entry| {
                let curvature_geometry_is_evaluator_backed = entry["distanceFamily"]
                    == "curvatureGeometry"
                    && entry["value"]["status"] != "unmeasured";
                let homotopy_filling_is_evaluator_backed = entry["distanceFamily"]
                    == "homotopyFillingGeometry"
                    && entry["value"]["status"] != "unmeasured";
                let representation_metric_is_evaluator_backed = entry["distanceFamily"]
                    == "representationMetric"
                    && entry["value"]["status"] != "unmeasured";
                if entry["distanceFamily"] == "atomGeometry"
                    || entry["distanceFamily"] == "configurationGeometry"
                    || entry["distanceFamily"] == "signatureGeometry"
                    || entry["distanceFamily"] == "operationGeometry"
                    || curvature_geometry_is_evaluator_backed
                    || homotopy_filling_is_evaluator_backed
                    || representation_metric_is_evaluator_backed
                {
                    (entry["value"]["status"] == "measured"
                        || entry["value"]["status"] == "zero"
                        || entry["value"]["status"] == "blocked")
                        && entry["value"]["evaluatorBasisRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && (entry["value"]["status"] != "blocked"
                            || entry["value"]["blockerRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty()))
                } else {
                    entry["value"]["status"] != "zero"
                        && entry["value"]["status"] != "measured"
                        && entry["value"]["blockerRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                }
            })
            && part4_distance["statusSummary"]["blockedCount"]
                .as_u64()
                .is_some_and(|count| count >= 7)
            && part4_distance["statusSummary"]["unmeasuredCount"]
                .as_u64()
                .is_some_and(|count| count == 0)
            && part4_distance["statusSummary"]["schemaFoundationOnlyCount"] == 0,
        "Part IV foundation must route atom/configuration/signature/operation/curvature/homotopy/representation geometry through evaluator readings while preserving semantic/gap blockers"
    );
    let atom_distance_readings = json["atomDistanceReadings"]
        .as_array()
        .expect("atom distance readings are array");
    assert!(
        !atom_distance_readings.is_empty()
            && atom_distance_readings.iter().any(|entry| {
                entry["semanticAnchorDistance"]["status"] == "unmeasured"
                    && entry["atomLayoutDistanceBundle"]["status"] == "blocked"
            })
            && atom_distance_readings.iter().any(|entry| {
                entry["semanticAnchorDistance"]["status"] == "zero"
                    || entry["semanticAnchorDistance"]["status"] == "measured"
            }),
        "Atom distance readings must measure fiber/carrier/valence while preserving missing semantic anchors as blocked, not zero"
    );
    assert!(
        atom_distance_readings.iter().all(|entry| {
            entry["viewerDistanceInputRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
                && entry["evidenceBoundary"].as_str().is_some_and(|boundary| {
                    boundary.contains("viewer layout distance refs remain separate")
                })
        }),
        "Atom diagnostic distance must retain separated viewer layout refs without reading them as diagnostic values"
    );
    let configuration_distance_readings = json["configurationDistanceReadings"]
        .as_array()
        .expect("configuration distance readings are array");
    assert!(
        !configuration_distance_readings.is_empty()
            && configuration_distance_readings.iter().any(|entry| {
                entry["highContextOverlap"] == true
                    && entry["configurationIndexedDistance"]["status"] == "measured"
                    && entry["configurationDistanceBundle"]["status"] == "blocked"
                    && entry["configurationDistanceBundle"]["blockerRefs"]
                        .as_array()
                        .is_some_and(|refs| {
                            refs.iter().any(|value| {
                                value
                                    .as_str()
                                    .is_some_and(|s| s.starts_with("observationGap:"))
                            })
                        })
            }),
        "Configuration distance readings must compute hypergraph/context distances while preserving observation gaps as blockers"
    );
    assert!(
        configuration_distance_readings.iter().all(|entry| {
            entry["typedHyperedges"].as_array().is_some_and(|edges| {
                !edges.is_empty()
                    && edges.iter().all(|edge| {
                        edge["hyperedgeId"].as_str().is_some()
                            && edge["hyperedgeKind"].as_str().is_some()
                            && edge["atomRefs"]
                                .as_array()
                                .is_some_and(|refs| refs.len() >= 2)
                            && edge["sourceRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                    })
            }) && entry["configurationIndexedDistance"]["evaluatorBasisRefs"]
                .as_array()
                .is_some_and(|refs| {
                    refs.iter()
                        .any(|value| value.as_str().is_some_and(|s| s.starts_with("hyperedge:")))
                        && refs.iter().any(|value| {
                            value
                                .as_str()
                                .is_some_and(|s| s.starts_with("shortestPath:"))
                        })
                })
        }),
        "Configuration distance readings must retain typed hyperedge and shortest-path evaluator basis refs"
    );
    let signature_distance_readings = json["signatureDistanceReadings"]
        .as_array()
        .expect("signature distance readings are array");
    assert!(
        !signature_distance_readings.is_empty()
            && signature_distance_readings.iter().all(|reading| {
                reading["axisDistances"].as_array().is_some_and(|axes| {
                    !axes.is_empty()
                        && axes.iter().all(|axis| {
                            axis["rhoI"]["evaluatorBasisRefs"]
                                .as_array()
                                .is_some_and(|refs| {
                                    refs.iter().any(|value| {
                                        value.as_str().is_some_and(|s| s.starts_with("rho_i:"))
                                    })
                                })
                                && axis["axisDistance"]["evaluatorBasisRefs"]
                                    .as_array()
                                    .is_some_and(|refs| {
                                        refs.iter().any(|value| {
                                            value
                                                .as_str()
                                                .is_some_and(|s| s.starts_with("axisValue:"))
                                        })
                                    })
                        })
                }) && reading["measuredAxisRefs"].as_array().is_some()
                    && reading["unmeasuredAxisRefs"].as_array().is_some()
                    && reading["incomparableAxisRefs"].as_array().is_some()
                    && reading["safeRegionMargin"]["status"] == "blocked"
                    && reading["pathDrift"]["status"] == "blocked"
                    && reading["hiddenExcursionStatus"]
                        .as_str()
                        .is_some_and(|status| status.contains("Coverage"))
            }),
        "Signature distance readings must expose rho_i, axis distances, axis partitions, safe-region margin, and drift blockers"
    );
    let operation_distance_readings = json["operationDistanceReadings"]
        .as_array()
        .expect("operation distance readings are array");
    assert!(
        !operation_distance_readings.is_empty()
            && operation_distance_readings.iter().all(|reading| {
                reading["operationCost"]["evaluatorBasisRefs"]
                    .as_array()
                    .is_some_and(|refs| {
                        refs.iter().any(|value| {
                            value
                                .as_str()
                                .is_some_and(|s| s.starts_with("operationCost:"))
                        })
                    })
                    && reading["targetDistanceDecrease"]["evaluatorBasisRefs"]
                        .as_array()
                        .is_some_and(|refs| {
                            refs.iter().any(|value| {
                                value
                                    .as_str()
                                    .is_some_and(|s| s.starts_with("targetDecrease:"))
                            })
                        })
                    && reading["sideEffectBound"]["status"] == "blocked"
                    && reading["transferRiskRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
                    && reading["evidenceBoundary"]
                        .as_str()
                        .is_some_and(|boundary| boundary.contains("not automatic repair safety"))
            }),
        "Operation distance readings must retain operation cost, target decrease, transfer risk, and side-effect blockers"
    );
    assert!(
        json["repairOperationCandidates"]
            .as_array()
            .is_some_and(|items| {
                items.iter().all(|candidate| {
                    candidate["part4DistanceRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
                })
            })
            && json["operationDeltas"].as_array().is_some_and(|items| {
                !items.is_empty()
                    && items.iter().all(|delta| {
                        delta["part4DistanceRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                    })
            }),
        "repair candidates and operation deltas must retain Part IV operation distance refs"
    );
    let obstruction_measure_readings = json["obstructionMeasureReadings"]
        .as_array()
        .expect("obstruction measure readings are array");
    assert!(
        !obstruction_measure_readings.is_empty()
            && obstruction_measure_readings.iter().all(|reading| {
                reading["measureValue"]["status"] == "measured"
                    || (reading["measureValue"]["status"] == "blocked"
                        && reading["measureValue"]["blockerRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty()))
            })
            && obstruction_measure_readings.iter().any(|reading| {
                reading["evidenceBoundary"]
                    .as_str()
                    .is_some_and(|boundary| boundary.contains("missing witnesses remain blockers"))
            }),
        "Obstruction measure readings must be witness-backed and keep missing witnesses as blockers, not zero curvature"
    );
    let curvature_mass_readings = json["curvatureMassReadings"]
        .as_array()
        .expect("curvature mass readings are array");
    assert!(
        !curvature_mass_readings.is_empty()
            && curvature_mass_readings.iter().all(|reading| {
                reading["obstructionMeasureReadingRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
                    && reading["curvatureMass"]["evaluatorBasisRefs"]
                        .as_array()
                        .is_some_and(|refs| {
                            refs.iter().any(|value| {
                                value
                                    .as_str()
                                    .is_some_and(|s| s.starts_with("curv_mass_U:"))
                            })
                        })
                    && reading["targetAxisDecrease"]["evaluatorBasisRefs"]
                        .as_array()
                        .is_some_and(|refs| {
                            refs.iter().any(|value| {
                                value.as_str().is_some_and(|s| {
                                    s.starts_with("curvatureTransport:targetAxisDecrease")
                                })
                            })
                        })
                    && reading["protectedAxisMovement"]["evaluatorBasisRefs"]
                        .as_array()
                        .is_some_and(|refs| {
                            refs.iter().any(|value| {
                                value.as_str().is_some_and(|s| {
                                    s.starts_with("curvatureTransport:protectedAxisMovement")
                                })
                            })
                        })
                    && reading["complexityTransferDistanceRefs"]
                        .as_array()
                        .is_some_and(|refs| !refs.is_empty())
            }),
        "Curvature mass readings must expose selected measure refs, target decrease, protected-axis movement, and complexity-transfer distance refs"
    );
    assert!(
        json["curvatureSupportReadings"]
            .as_array()
            .is_some_and(|items| {
                !items.is_empty()
                    && items.iter().all(|reading| {
                        reading["part4DistanceRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                    })
            })
            && json["curvatureTransferReadings"]
                .as_array()
                .is_some_and(|items| {
                    !items.is_empty()
                        && items.iter().all(|reading| {
                            reading["part4DistanceRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                        })
                })
            && json["architectureSpectrumReport"]["curvatureMassReadingRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty()),
        "existing curvature support, transfer, and spectrum report surfaces must retain Part IV curvature distance refs"
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
            let nonzero_edge_count = entry["transferOperator"]["nonzeroEdgeCount"]
                .as_u64()
                .unwrap_or_default();
            entry["profileRef"].as_str().is_some()
                && entry["transferOperator"]["nonzeroEdgeCount"]
                    .as_u64()
                    .is_some()
                && entry["transferOperator"]["entryRule"].as_str().is_some()
                && entry["transferEdges"]
                    .as_array()
                    .is_some_and(|items| nonzero_edge_count == 0 || !items.is_empty())
                && entry["recurrentObstructionModes"]
                    .as_array()
                    .is_some_and(|items| nonzero_edge_count == 0 || !items.is_empty())
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
    let has_positive_transfer_edges = curvature_transfer.iter().any(|entry| {
        entry["transferOperator"]["nonzeroEdgeCount"]
            .as_u64()
            .is_some_and(|count| count > 0)
    });
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
            .is_some_and(|items| !has_positive_transfer_edges || !items.is_empty()),
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
        "representationMetricReadings",
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
                    && reading["part4DistanceRefs"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "representation strength readings must carry strength classes and assumptions"
    );
    assert!(
        json["representationMetricReadings"]
            .as_array()
            .expect("representation metric readings are array")
            .iter()
            .all(|reading| {
                reading["representationMetricReadingId"].as_str().is_some()
                    && reading["representationRef"].as_str().is_some()
                    && reading["representationFamily"].as_str().is_some()
                    && reading["structuralDistance"]["evaluatorBasisRefs"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["analyticDistance"]["reading"]
                        .as_str()
                        .is_some_and(|text| text.contains("not an architecture quality score"))
                    && reading["lipschitzStability"]["evaluatorBasisRefs"]
                        .as_array()
                        .is_some()
                    && reading["biLipschitzFaithfulness"]["status"] == "blocked"
                    && reading["biLipschitzFaithfulness"]["blockerRefs"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["coverageBlockerRefs"].as_array().is_some()
                    && reading["witnessCompletenessBlockerRefs"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["evidenceBoundary"]
                        .as_str()
                        .is_some_and(|text| text.contains("not structural faithfulness"))
            }),
        "representation metric readings must expose selected structural/analytic distance, Lipschitz stability, and blocked faithfulness lower bounds"
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
                && json["llmInterpretationPacket"]["distanceDiagnosisSummary"]
                    .as_array()
                    .is_some_and(|items| {
                        items.iter().any(|item| {
                            item.as_str().is_some_and(|text| {
                                text.contains("diagnostic distance is Part IV evaluator output")
                            })
                        })
                    })
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
