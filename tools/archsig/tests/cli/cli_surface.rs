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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_ag.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
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
fn archmap_v2_cross_doctrine_comparison_degenerates_to_comparable() {
    let root = ag_measurement_root();
    let left_value = read_json(&root.join("archmap_v2.json"));
    let right_value = left_value.clone();
    let left: ArchMapDocumentV2 = serde_json::from_value(left_value).expect("left archmap parses");
    let right: ArchMapDocumentV2 =
        serde_json::from_value(right_value).expect("right archmap parses");

    let result = compare_archmap_v2_doctrine(&left, &right);
    assert_eq!(result["status"], "comparable");
    assert_eq!(result["reason"], "fixed_tool_doctrine");
}

#[test]
fn archmap_v2_cross_doctrine_comparison_rejects_noncanonical_input() {
    let root = ag_measurement_root();
    let left_value = read_json(&root.join("archmap_v2.json"));
    let mut right_value = left_value.clone();
    right_value["extractionDoctrineRef"] = json!({
        "doctrineId": "doctrine:custom@1",
        "fingerprint": "sha256:other-doctrine",
        "components": ["custom"]
    });
    let left: ArchMapDocumentV2 = serde_json::from_value(left_value).expect("left archmap parses");
    let right: ArchMapDocumentV2 =
        serde_json::from_value(right_value).expect("right archmap parses");

    let result = compare_archmap_v2_doctrine(&left, &right);
    assert_eq!(result["status"], "not_comparable");
    assert_eq!(result["reason"], "invalid_fixed_doctrine");
    assert_eq!(result["leftCanonical"], true);
    assert_eq!(result["rightCanonical"], false);
}

#[test]
fn practical_rust_service_example_runs_current_analyze() {
    let out_dir = temp_dir("practical-rust-service-current-analyze");
    let root = practical_rust_service_root();

    // Mirror the demo script's base act: same LawPolicy, base law surface.
    let mut policy = read_json(&root.join("law_policy/law_policy.json"));
    policy["lawSurfaceRef"] = json!("law-surface:practical-rust-base-v052");
    let policy_path = out_dir.join("law_policy_base.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("base policy serializes"),
    )
    .expect("base policy writes");

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap/archmap.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        root.join("law_policy/measurement_profile.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("law_policy/measurement_profile_drift.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_policy/law_surface_base.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(
        output.status.success(),
        "current practical sample analyze must pass\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let archmap_validation = read_json(&out_dir.join("archmap-validation.json"));
    assert_eq!(archmap_validation["summary"]["atomCount"], 70);
    assert_eq!(archmap_validation["summary"]["contextCount"], 7);
    assert_eq!(archmap_validation["summary"]["coverCount"], 1);
    assert_eq!(archmap_validation["summary"]["result"], "pass");

    let normalized = read_json(&out_dir.join("normalized-archmap.json"));
    assert_eq!(normalized["schema"], "normalized-archmap/v0.5.4");
    assert_eq!(normalized["summary"]["normalizedAtomCount"], 70);
    assert_eq!(normalized["summary"]["contextCount"], 7);
    assert_eq!(normalized["summary"]["coverCount"], 1);

    let measurement_packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        measurement_packet["schema"],
        "archsig-measurement-packet/v0.5.4"
    );
    assert_eq!(
        measurement_packet["packetId"],
        "measurement:practical-rust-commerce-fulfillment/v0.5.4"
    );
    let verdict_rows = measurement_packet["structuralVerdict"]
        .as_array()
        .expect("structural verdict rows");
    assert_eq!(
        verdict_rows.len(),
        4,
        "base act carries the cech row plus the ArchMap-derived SAGA rows"
    );
    assert!(
        verdict_rows.iter().any(|row| {
            row["evaluator"] == "ag.cech-obstruction" && row["verdict"] == "measured_zero"
        }),
        "practical sample must expose the selected AG structural verdict"
    );
    assert!(
        verdict_rows
            .iter()
            .all(|row| row["verdictData"].is_object()),
        "SAGA rows must be derived from the validated ArchMap and law inputs"
    );
    assert!(
        measurement_packet["computedInvariants"]
            .as_array()
            .is_some_and(|rows| rows.iter().any(|row| row["atomCount"] == 70
                && row["contextCount"] == 7
                && row["coverCount"] == 1)),
        "measurement packet must preserve the finite-poset-site shape counts"
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert_eq!(summary["schema"], "archsig-analysis-summary/v0.5.4");
    assert_eq!(
        summary["conclusion"],
        ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
    );
    assert_eq!(summary["structuralVerdictSummary"]["rowCount"], 4);
    assert_eq!(summary["structuralVerdictSummary"]["nonTerminalCount"], 0);

    assert_eq!(manifest["schema"], "archsig-run-manifest/v0.5.4");
    assert_eq!(manifest["mode"], "measurement");
    assert_eq!(manifest["toolVersion"], "0.5.4");
    assert!(
        manifest["runId"]
            .as_str()
            .is_some_and(|run_id| run_id.starts_with("run:") && run_id.len() == 16)
    );
    assert!(manifest["inputDigests"]["profileFingerprint"]["sha256"].is_string());
    for (artifact_key, artifact_path) in [
        ("normalizedArchmap", "normalized-archmap.json"),
        ("measurementPacket", "archsig-measurement-packet.json"),
    ] {
        assert_eq!(
            manifest["artifactDigests"][artifact_key]["path"],
            artifact_path
        );
        assert!(
            manifest["artifactDigests"][artifact_key]["sha256"]
                .as_str()
                .is_some_and(|digest| digest.len() == 64)
        );
    }
    assert!(
        manifest["generatedArtifacts"]
            .as_array()
            .is_some_and(|artifacts| [
                "archsig-measurement-packet.json",
                "archsig-analysis-summary.json",
                "archsig-insight-report.json",
                "archsig-atom-viewer-data.json",
            ]
            .into_iter()
            .all(|name| artifacts.iter().any(|artifact| artifact == name))),
        "manifest must list the current practical demo artifacts"
    );
}

#[test]
fn cli_analyze_current_run_removes_stale_retired_artifacts() {
    let out_dir = temp_dir("current-analyze-removes-stale-retired-artifacts");
    let root = ag_measurement_root();
    let retired_artifacts = [
        ["typed", "evaluator", "results.json"].join("-"),
        ["architecture", "distance.json"].join("-"),
        ["archsig", "analysis", "packet.json"].join("-"),
        ["archsig", "analysis", "detail", "index.json"].join("-"),
        ["llm", "interpretation", "packet.json"].join("-"),
    ];
    for artifact in &retired_artifacts {
        fs::write(out_dir.join(artifact), "{}").expect("stale artifact fixture writes");
    }

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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    for artifact in &retired_artifacts {
        assert!(
            !out_dir.join(artifact).exists(),
            "current analyze must remove stale retired artifact {artifact}"
        );
    }
    assert!(out_dir.join("archsig-measurement-packet.json").exists());
    assert!(out_dir.join("archsig-run-manifest.json").exists());

    let overwrite_attempt = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(overwrite_attempt.status.code(), Some(2));

    let failure_out_dir = temp_dir("current-analyze-validation-failure");
    for artifact in &retired_artifacts {
        fs::write(failure_out_dir.join(artifact), "{}").expect("stale artifact fixture writes");
    }
    let malformed_profile = failure_out_dir.join("malformed-profile.json");
    fs::write(&malformed_profile, "{\n").expect("malformed profile writes");
    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        malformed_profile.to_str().expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        failure_out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    for artifact in &retired_artifacts {
        assert!(
            !failure_out_dir.join(artifact).exists(),
            "failed input validation must remove stale retired artifact {artifact}"
        );
    }
    assert!(
        !failure_out_dir
            .join("archsig-measurement-packet.json")
            .exists(),
        "failed input validation must not leave a stale measurement packet"
    );
    assert!(
        !failure_out_dir.join("archsig-run-manifest.json").exists(),
        "failed input validation must not leave a stale run manifest"
    );
}

#[test]
fn cli_analyze_derives_and_checks_a_saga_triple_face() {
    let out_dir = temp_dir("practical-rust-service-derived-triple");
    let root = practical_rust_service_root();
    let shared_atom_id = "atom:derived-shared-triple-face";
    let mut archmap = read_json(&root.join("archmap/archmap_head.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("ArchMap atoms are an array")
        .push(json!({
            "id": shared_atom_id,
            "kind": "semantic",
            "subject": "ctx:application",
            "axis": "cech",
            "predicate": "sectionValue",
            "object": "section=money:shared-triple-face",
            "refs": ["ctx:application"]
        }));
    for context_id in ["ctx:application", "ctx:domain", "ctx:shared"] {
        let context = archmap["contexts"]
            .as_array_mut()
            .expect("ArchMap contexts are an array")
            .iter_mut()
            .find(|context| context["id"] == context_id)
            .expect("selected context exists");
        context["atoms"]
            .as_array_mut()
            .expect("context atoms are an array")
            .push(json!(shared_atom_id));
    }
    let archmap_path = out_dir.join("archmap-derived-triple.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("derived triple ArchMap serializes"),
    )
    .expect("derived triple ArchMap writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("ArchMap path is utf-8"),
        "--law-policy",
        root.join("law_policy/law_policy.json")
            .to_str()
            .expect("LawPolicy path is utf-8"),
        "--measurement-profile",
        root.join("law_policy/measurement_profile.json")
            .to_str()
            .expect("measurement profile path is utf-8"),
        "--measurement-profile",
        root.join("law_policy/measurement_profile_drift.json")
            .to_str()
            .expect("drift profile path is utf-8"),
        "--law-surface",
        root.join("law_policy/law_surface.json")
            .to_str()
            .expect("law surface path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("output path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let class = packet["computedInvariants"]
        .as_array()
        .expect("computed invariants are an array")
        .iter()
        .find(|invariant| invariant["invariantId"] == "saga-descent:residual-class")
        .expect("derived triple must unlock the residual class invariant");
    assert_eq!(class["kind"], "residual-class-support");
    assert_eq!(class["evaluator"], "ag.saga-descent");
    assert_eq!(
        class["residualClassSupport"]["cocycle"]["certificateKind"],
        "checked-triple-cocycle-zero"
    );
    assert!(
        class["residualClassSupport"]["cocycle"]["tripleOverlapRefs"]
            .as_array()
            .is_some_and(|faces| !faces.is_empty())
    );
}

#[test]
fn cli_analyze_practical_service_outputs_are_byte_deterministic_with_known_digests() {
    let first_out = temp_dir("practical-rust-service-determinism-a");
    let second_out = temp_dir("practical-rust-service-determinism-b");
    let root = practical_rust_service_root();
    let args = |out_dir: &Path| {
        vec![
            "analyze".to_string(),
            "--archmap".to_string(),
            root.join("archmap/archmap_head.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--law-policy".to_string(),
            root.join("law_policy/law_policy.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--measurement-profile".to_string(),
            root.join("law_policy/measurement_profile.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--measurement-profile".to_string(),
            root.join("law_policy/measurement_profile_drift.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--law-surface".to_string(),
            root.join("law_policy/law_surface.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--out-dir".to_string(),
            out_dir.to_str().expect("path is utf-8").to_string(),
        ]
    };
    let first_args = args(&first_out);
    let second_args = args(&second_out);
    let first_arg_refs = first_args.iter().map(String::as_str).collect::<Vec<_>>();
    let second_arg_refs = second_args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&first_arg_refs);
    run_sig0(&second_arg_refs);

    for artifact in [
        "normalized-archmap.json",
        "archsig-measurement-packet.json",
        "archsig-analysis-summary.json",
        "archsig-insight-report.json",
        "archsig-insight-brief.md",
        "archsig-atom-viewer-data.json",
        "archsig-measurement-view-model.json",
        "archsig-run-manifest.json",
        "archmap-validation.json",
        "law-policy-validation.json",
        "law-surface-validation.json",
        "archsig-analysis-validation.json",
    ] {
        assert_eq!(
            fs::read(first_out.join(artifact)).expect("first artifact is readable"),
            fs::read(second_out.join(artifact)).expect("second artifact is readable"),
            "{artifact} must be byte-identical across repeated analyze runs"
        );
    }

    let manifest = read_json(&first_out.join("archsig-run-manifest.json"));
    assert_eq!(manifest["toolVersion"], "0.5.4");
    assert_eq!(manifest["runId"], "run:99469edc79b5");
    assert_eq!(
        manifest["inputDigests"]["archmap"]["sha256"],
        "eb07048f1dfa6e4c919c6da43e614128b97b69578230620c778225e19d15b37e"
    );
    assert_eq!(
        manifest["inputDigests"]["lawPolicy"]["sha256"],
        "840659c0ea8b483d77acb970bbce259ee30c5bd996aa9e6dd8e74e103292dbe9"
    );
    assert_eq!(
        manifest["inputDigests"]["measurementProfile"]["sha256"],
        "c20e6fa2f3f7bd33b8685bafef5d89f62fa4f419c6f67cabf179e80176a32539"
    );
    assert_eq!(
        manifest["inputDigests"]["measurementProfiles"]
            .as_array()
            .map(Vec::len),
        Some(2)
    );
    assert_eq!(
        manifest["inputDigests"]["profileFingerprint"]["sha256"],
        "724f89f73c2bf9e2aa72effeb6df4eece0332a3d1a0b5f625349fd298d83adb3"
    );
    assert_eq!(
        manifest["inputDigests"]["siteCoverDigest"]["sha256"],
        "e3ae81e46a9aa93d0d990d4aaa9b02d86c150ff51aa24c8c5914f63e7e9bd35b"
    );
    assert_eq!(
        manifest["inputDigests"]["siteCoverDigest"]["basis"],
        "normalized contexts + covers + derived finite cover nerve"
    );
}

#[test]
fn cli_analyze_outputs_do_not_embed_local_absolute_input_paths() {
    let input_dir = temp_dir("practical-rust-service-absolute-inputs");
    let first_out = temp_dir("practical-rust-service-absolute-output-a");
    let second_out = temp_dir("practical-rust-service-absolute-output-b");
    let root = practical_rust_service_root();
    let archmap_path = input_dir.join("archmap.json");
    let law_policy_path = input_dir.join("law_policy.json");
    let measurement_profile_path = input_dir.join("measurement_profile.json");
    fs::copy(root.join("archmap/archmap_head.json"), &archmap_path)
        .expect("archmap fixture copies to absolute temp path");
    fs::copy(root.join("law_policy/law_policy.json"), &law_policy_path)
        .expect("law policy fixture copies to absolute temp path");
    fs::copy(
        root.join("law_policy/measurement_profile.json"),
        &measurement_profile_path,
    )
    .expect("measurement profile fixture copies to absolute temp path");
    fs::copy(
        root.join("law_policy/measurement_profile_drift.json"),
        input_dir.join("measurement_profile_drift.json"),
    )
    .expect("drift profile fixture copies to absolute temp path");
    fs::copy(
        root.join("law_policy/law_surface.json"),
        input_dir.join("law_surface.json"),
    )
    .expect("law surface fixture copies to absolute temp path");

    let args = |out_dir: &Path| {
        vec![
            "analyze".to_string(),
            "--archmap".to_string(),
            archmap_path.to_str().expect("path is utf-8").to_string(),
            "--law-policy".to_string(),
            law_policy_path.to_str().expect("path is utf-8").to_string(),
            "--measurement-profile".to_string(),
            measurement_profile_path
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--measurement-profile".to_string(),
            input_dir
                .join("measurement_profile_drift.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--law-surface".to_string(),
            input_dir
                .join("law_surface.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--out-dir".to_string(),
            out_dir.to_str().expect("path is utf-8").to_string(),
        ]
    };
    let first_args = args(&first_out);
    let second_args = args(&second_out);
    let first_arg_refs = first_args.iter().map(String::as_str).collect::<Vec<_>>();
    let second_arg_refs = second_args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&first_arg_refs);
    run_sig0(&second_arg_refs);

    for artifact in [
        "normalized-archmap.json",
        "archsig-measurement-packet.json",
        "archsig-analysis-summary.json",
        "archsig-insight-report.json",
        "archsig-insight-brief.md",
        "archsig-atom-viewer-data.json",
        "archsig-measurement-view-model.json",
        "archsig-run-manifest.json",
    ] {
        let first = fs::read(first_out.join(artifact)).expect("first artifact is readable");
        let second = fs::read(second_out.join(artifact)).expect("second artifact is readable");
        assert_eq!(
            first, second,
            "{artifact} must be byte-identical across repeated absolute-path analyze runs"
        );
        let text = String::from_utf8_lossy(&first);
        let forbidden_markers = [
            format!("{}/", ["", "Users"].join("/")),
            format!("{}/", ["", "private"].join("/")),
            [".", "codex"].join(""),
            ["Hello", "Lean"].join(""),
            ["Algebraic", "Architecture", "TheoryV2"].join(""),
        ];
        for forbidden in forbidden_markers {
            assert!(
                !text.contains(&forbidden),
                "{artifact} must not expose local workspace marker {forbidden}"
            );
        }
    }

    let manifest = read_json(&first_out.join("archsig-run-manifest.json"));
    let _: ArchSigRunManifestV1 =
        serde_json::from_value(manifest.clone()).expect("v2 manifest matches schema struct");
    assert_eq!(manifest["archmapInputPath"], "input:archmap.json");
    assert_eq!(manifest["lawPolicyInputPath"], "input:law_policy.json");
    assert_eq!(
        manifest["inputDigests"]["archmap"]["path"],
        "input:archmap.json"
    );
    assert_eq!(
        manifest["inputDigests"]["lawPolicy"]["path"],
        "input:law_policy.json"
    );
    assert_eq!(
        manifest["validationResultSummary"]["analysis"]["result"],
        "pass"
    );
}

#[test]
fn cli_analyze_stamp_appends_opt_in_run_id_suffix() {
    let out_dir = temp_dir("practical-rust-service-stamp");
    let root = practical_rust_service_root();
    let args = vec![
        "analyze".to_string(),
        "--archmap".to_string(),
        root.join("archmap/archmap_head.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-policy".to_string(),
        root.join("law_policy/law_policy.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--measurement-profile".to_string(),
        root.join("law_policy/measurement_profile.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--measurement-profile".to_string(),
        root.join("law_policy/measurement_profile_drift.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-surface".to_string(),
        root.join("law_policy/law_surface.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--out-dir".to_string(),
        out_dir.to_str().expect("path is utf-8").to_string(),
        "--stamp".to_string(),
    ];
    let arg_refs = args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&arg_refs);

    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert!(
        manifest["runId"]
            .as_str()
            .is_some_and(|run_id| run_id.starts_with("run:99469edc79b5-stamp:")),
        "stamp opt-in should append a wall-clock suffix to the deterministic input-derived prefix"
    );
}

#[test]
fn cli_help_exposes_only_archsig_analysis_surface() {
    let output = run_sig0_output(&["--help"]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("Part IV"),
        "current v1 CLI help must describe architecture distance without Part IV public wording\n{stdout}"
    );

    for command in ["law-policy", "analyze", "schema-catalog"] {
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
            !help_command_names(&stdout).contains(removed),
            "ArchSig help still exposes removed command {removed}\n{stdout}"
        );
    }
}

#[test]
fn cli_rejects_implicit_scan_default() {
    let output = run_sig0_output(&[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("ArchMap/LawPolicy/measurement-packet primary")
            && stderr.contains("archsig analyze"),
        "implicit scan should be rejected with the analyze boundary\n{stderr}"
    );
}

#[test]
fn removed_legacy_commands_are_not_accepted() {
    for command in removed_commands().iter().copied().chain(["pr-review"]) {
        let output = run_sig0_output(&[command, "--help"]);
        assert!(
            !output.status.success(),
            "removed command {command} should not be accepted"
        );
    }
}

#[test]
fn removed_legacy_analyze_flags_are_not_accepted() {
    let root = ag_measurement_root();
    for flag in [
        ["--strict", "distance"].join("-"),
        ["--emit", "raw", "artifacts"].join("-"),
    ] {
        let out_dir = temp_dir(&format!("removed-analyze-flag-{flag}"));
        let output = run_sig0_output(&[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_ag.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
            flag.as_str(),
        ]);
        assert!(
            !output.status.success(),
            "removed analyze flag {flag} should not be accepted"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("unexpected argument") || stderr.contains("unrecognized option"),
            "removed analyze flag {flag} should fail as an unknown flag\n{stderr}"
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
    let unique_ids = ids.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(
        unique_ids.len(),
        ids.len(),
        "schema catalog artifact IDs must be unique"
    );
    let schema_names = artifacts
        .iter()
        .map(|entry| entry["schemaName"].as_str().expect("schema name"))
        .collect::<Vec<_>>();
    let unique_schema_names = schema_names.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(
        unique_schema_names.len(),
        schema_names.len(),
        "schema catalog schema names must be unique"
    );
    assert_eq!(
        ids,
        vec![
            "archmap-current",
            "aat-atom-vocabulary/v0.5.5",
            "aat-atom-vocabulary-binding/v0.5.4",
            "law-equation-surface/v0.5.4",
            "law-policy/v0.5.4",
            "archsig-policy-bundle/v0.5.4",
            "measurement-profile/v0.5.4",
            "law-evaluator-registry/v0.5.4",
            "normalized-archmap-current",
            "archsig-measurement-packet/v0.5.4",
            "archsig-boundary-statement/v0.5.4",
            "archsig-gate-policy/v0.5.4",
            "archsig-gate-report/v0.5.4",
            "archmap-diff/v0.5.4",
            "archsig-comparison-report/v0.5.7",
            "archsig-run-manifest/v0.5.4",
            "archsig-atom-viewer-data/v0.5.4",
            "archsig-measurement-view-model/v0.5.4",
        ]
    );
    for entry in artifacts {
        let artifact_id = entry["artifactId"].as_str().expect("artifact id");
        let expected_role = match artifact_id {
            "aat-atom-vocabulary-binding/v0.5.4" => "primary",
            _ => "primary",
        };
        assert_eq!(entry["artifactRole"].as_str(), Some(expected_role));
    }
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "aat-atom-vocabulary/v0.5.5"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        description.contains("artifact-side projection")
                            && description.contains("allowed ArchMap atom kind tokens")
                            && description.contains("fixed AAT canonical doctrine")
                    })
                && entry["compatibilityBoundary"]["nonConclusions"]
                    .as_array()
                    .is_some_and(|items| {
                        items.iter().any(|item| {
                            item.as_str()
                                .is_some_and(|text| text.contains("semantic correctness"))
                        })
                    })
        }),
        "schema catalog must describe the AAT atom vocabulary artifact boundary"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-boundary-statement/v0.5.4"
                && entry["schemaName"] == "archsig-boundary-statement/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        description.contains("typed scoped qualifier contract")
                            && description.contains("nonConclusions as a compatibility view")
                    })
                && entry["compatibilityBoundary"]["nonConclusions"]
                    .as_array()
                    .is_some_and(|items| {
                        items.iter().any(|item| {
                            item.as_str()
                                .is_some_and(|text| text.contains("measured_zero"))
                        })
                    })
        }),
        "schema catalog must describe the BoundaryStatement v1 artifact boundary"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-measurement-packet/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        ARCHSIG_SAGA_CONCLUSION_CODES
                            .iter()
                            .all(|code| description.contains(code))
                            && [
                                "ag.saga-descent",
                                "checked triple-cocycle certificate",
                                "MeasurementProfile-selected normalized covers",
                                "classTransport",
                            ]
                            .iter()
                            .all(|field| description.contains(field))
                    })
        }),
        "schema catalog must register SAGA conclusionCode values"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-gate-policy/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        description
                            .contains("violated_assumption_dependency must map exactly to block")
                            && description.contains("cannot map to plain pass")
                    })
        }),
        "schema catalog must register the exact gate action for violated assumption dependency"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-gate-report/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        ARCHSIG_GATE_REPORT_DECISIONS
                            .iter()
                            .all(|decision| description.contains(decision))
                    })
        }),
        "schema catalog must register gate decision values"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-comparison-report/v0.5.7"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        ARCHSIG_COMPARISON_CONCLUSION_CODES
                            .iter()
                            .all(|code| description.contains(code))
                            && ARCHSIG_COMPARISON_CLASS_TRANSPORT_CONCLUSION_CODES
                                .iter()
                                .all(|code| description.contains(code))
                            && description.contains("derived-class-zero-preservation@1")
                    })
        }),
        "schema catalog must register comparison conclusionCode values"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-run-manifest/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        ARCHSIG_ANALYSIS_CONCLUSION_CODES
                            .iter()
                            .all(|code| description.contains(code))
                    })
        }),
        "schema catalog must register analyze conclusionCode values"
    );
}

#[test]
fn cli_policy_bundle_fingerprints_and_analyze_handoff_are_fail_closed() {
    let out_dir = temp_dir("policy-bundle");
    let root = ag_measurement_root();
    let law_policy = out_dir.join("law_policy_ag.json");
    let law_surface = out_dir.join("law_surface_ag_v052.json");
    let measurement_profile = out_dir.join("measurement_profile_ag.json");
    fs::copy(root.join("law_policy_ag.json"), &law_policy).expect("policy copies");
    fs::copy(root.join("law_surface_ag_v052.json"), &law_surface).expect("surface copies");
    fs::copy(
        root.join("measurement_profile_ag.json"),
        &measurement_profile,
    )
    .expect("profile copies");
    let bundle = out_dir.join("policy_bundle.json");
    run_sig0(&[
        "policy-bundle",
        "--law-policy",
        law_policy.to_str().expect("policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
        "--out",
        bundle.to_str().expect("bundle path is utf-8"),
    ]);
    let bundle_json = read_json(&bundle);
    assert_eq!(bundle_json["schema"], "archsig-policy-bundle/v0.5.4");
    assert!(
        bundle_json["componentFingerprints"]["lawPolicy"]
            .as_str()
            .is_some_and(|value| value.starts_with("sha256:"))
    );

    let validation = out_dir.join("policy-bundle-validation.json");
    run_sig0(&[
        "policy-bundle",
        "--policy-bundle",
        bundle.to_str().expect("bundle path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
    ]);
    assert_eq!(read_json(&validation)["summary"]["result"], "pass");
    let overwrite_validation = run_sig0_raw_output(&[
        "policy-bundle",
        "--policy-bundle",
        bundle.to_str().expect("bundle path is utf-8"),
        "--out",
        bundle.to_str().expect("bundle output path is utf-8"),
    ]);
    assert_eq!(overwrite_validation.status.code(), Some(2));

    let analyze_dir = out_dir.join("analyze");
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--policy-bundle",
        bundle.to_str().expect("bundle path is utf-8"),
        "--out-dir",
        analyze_dir.to_str().expect("analyze path is utf-8"),
    ]);
    assert_eq!(
        read_json(&analyze_dir.join("archsig-measurement-packet.json"))["componentFingerprints"],
        bundle_json["componentFingerprints"]
    );
    assert_eq!(
        read_json(&analyze_dir.join("archsig-run-manifest.json"))["componentFingerprints"],
        bundle_json["componentFingerprints"]
    );

    let mut mismatched = bundle_json.clone();
    mismatched["componentFingerprints"]["lawPolicy"] = json!("sha256:wrong");
    let mismatched_path = out_dir.join("policy_bundle_mismatched.json");
    fs::write(
        &mismatched_path,
        serde_json::to_vec_pretty(&mismatched).expect("mismatched bundle serializes"),
    )
    .expect("mismatched bundle writes");
    let mismatched_output = run_sig0_raw_output(&[
        "policy-bundle",
        "--policy-bundle",
        mismatched_path.to_str().expect("mismatched path is utf-8"),
        "--out",
        out_dir
            .join("mismatched-validation.json")
            .to_str()
            .expect("mismatched validation path is utf-8"),
    ]);
    assert_eq!(mismatched_output.status.code(), Some(1));

    let analyze_mismatched_dir = out_dir.join("analyze-mismatched-bundle");
    let analyze_mismatched_output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--policy-bundle",
        mismatched_path
            .to_str()
            .expect("mismatched bundle path is utf-8"),
        "--out-dir",
        analyze_mismatched_dir
            .to_str()
            .expect("mismatched analyze path is utf-8"),
    ]);
    assert_eq!(analyze_mismatched_output.status.code(), Some(2));
    assert!(
        !analyze_mismatched_dir
            .join("archsig-measurement-packet.json")
            .exists(),
        "analyze must not emit a measurement packet for a mismatched policy bundle"
    );

    let mut unknown_policy = read_json(&law_policy);
    unknown_policy["unexpected"] = json!(true);
    let unknown_policy_path = out_dir.join("law_policy_unknown.json");
    fs::write(
        &unknown_policy_path,
        serde_json::to_vec_pretty(&unknown_policy).expect("unknown policy serializes"),
    )
    .expect("unknown policy writes");
    let unknown_output = run_sig0_raw_output(&[
        "policy-bundle",
        "--law-policy",
        unknown_policy_path
            .to_str()
            .expect("unknown policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
        "--out",
        out_dir
            .join("unknown-policy-bundle.json")
            .to_str()
            .expect("unknown bundle path is utf-8"),
    ]);
    assert_eq!(unknown_output.status.code(), Some(2));

    let overwrite_output = run_sig0_raw_output(&[
        "policy-bundle",
        "--law-policy",
        law_policy.to_str().expect("policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
        "--out",
        law_policy.to_str().expect("policy output path is utf-8"),
    ]);
    assert_eq!(overwrite_output.status.code(), Some(2));

    let stdout_creation = run_sig0_raw_output(&[
        "policy-bundle",
        "--law-policy",
        law_policy.to_str().expect("policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
    ]);
    assert_eq!(stdout_creation.status.code(), Some(2));
}

#[test]
fn cli_tor_policy_bundle_preserves_explicit_law_pair() {
    let out_dir = temp_dir("policy-bundle-tor");
    let root = ag_measurement_root();
    let law_policy = out_dir.join("law_policy_tor.json");
    let law_surface = out_dir.join("law_surface_ag_v052.json");
    let measurement_profile = out_dir.join("measurement_profile_tor.json");
    fs::copy(root.join("law_policy_tor.json"), &law_policy).expect("policy copies");
    fs::copy(root.join("law_surface_ag_v052.json"), &law_surface).expect("surface copies");
    fs::copy(
        root.join("measurement_profile_tor.json"),
        &measurement_profile,
    )
    .expect("profile copies");
    let bundle = out_dir.join("policy_bundle_tor.json");

    run_sig0(&[
        "policy-bundle",
        "--law-policy",
        law_policy.to_str().expect("policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
        "--out",
        bundle.to_str().expect("bundle path is utf-8"),
    ]);

    let analyze_dir = out_dir.join("analyze");
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--policy-bundle",
        bundle.to_str().expect("bundle path is utf-8"),
        "--out-dir",
        analyze_dir.to_str().expect("analyze path is utf-8"),
    ]);

    let validation = read_json(&analyze_dir.join("law-policy-validation.json"));
    assert_eq!(validation["summary"]["result"], "pass");
    assert_eq!(
        validation["expandedPolicies"][0]["lawPair"],
        json!(["law:checkout", "law:inventory"])
    );
    assert!(
        !validation["expandedPolicies"][0]
            .as_object()
            .expect("expanded policy is an object")
            .contains_key("law")
    );

    let packet = read_json(&analyze_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1")["commonAmbient"]
            ["lawPair"],
        json!(["law:checkout", "law:inventory"])
    );
}
