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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_laplacian.json")
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

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.sheaf-laplacian"
    );
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "finite_laplacian_analytic_reading_computed"
    );
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        1,
        "curvature hotspot reading must not add a structural verdict row"
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
        .find(|reading| reading["evaluator"] == "ag.sheaf-laplacian")
        .expect("laplacian analytic reading exists");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);
    assert_eq!(reading["claimStatus"], "certified");
    assert_eq!(reading["fidelity"], "proxy");
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
    let hotspot = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["value"]["readingKind"] == "curvature-transfer-perron-hotspot@1")
        .expect("curvature hotspot theorem-candidate reading exists");
    assert_eq!(hotspot["regime"], "theorem-candidate");
    assert_eq!(hotspot["structuralVerdictRef"], Value::Null);
    assert_eq!(
        hotspot["value"]["sourceProxyReadingKind"],
        "graph-laplacian-hodge-proxy@1"
    );
    assert_eq!(
        hotspot["value"]["hotspots"],
        serde_json::json!([
            {"cell": "cell:left", "hotspotWeight": 0.707107},
            {"cell": "cell:right", "hotspotWeight": 0.707107}
        ])
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_harmonic_debt_requires_cost_model_for_lower_bound() {
    let root = ag_measurement_root();
    let out_dir = temp_dir("ag-measurement-harmonic-debt");
    let mut policy = read_json(&root.join("law_policy_laplacian.json"));
    policy["measurementProfileRef"] = json!("profile:ag-harmonic-debt@1");
    policy["policies"][0]["evaluator"] = json!("ag.harmonic-debt");
    let policy_path = out_dir.join("law_policy_harmonic_debt.json");
    let profile_path = out_dir.join("measurement_profile_harmonic_debt.json");
    let surface_path = root.join("law_surface_ag_v052.json");
    fs::write(&policy_path, serde_json::to_vec_pretty(&policy).unwrap()).unwrap();
    fs::copy(
        root.join("measurement_profile_harmonic_debt.json"),
        &profile_path,
    )
    .unwrap();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_sheaf_laplacian.json")
            .to_str()
            .unwrap(),
        "--law-policy",
        policy_path.to_str().unwrap(),
        "--measurement-profile",
        profile_path.to_str().unwrap(),
        "--law-surface",
        surface_path.to_str().unwrap(),
        "--out-dir",
        out_dir.to_str().unwrap(),
    ]);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert!(
        packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row["evaluator"] != "ag.harmonic-debt"),
        "harmonic debt must stay out of structural verdicts"
    );
    let invariant = invariant_by_id(&packet, "harmonic-debt:profile:ag-harmonic-debt@1");
    assert_eq!(invariant["harmonicDebtNorm"], json!(0.707107));
    assert_eq!(invariant["essentialRepairLowerBound"], json!(0.353553));
    assert_eq!(invariant["lowerBoundStatus"], "cost_model_supplied");
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/8.7")
    );
    let reading = packet["analyticReadings"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.harmonic-debt")
        .unwrap();
    assert_eq!(reading["claimStatus"], "certified");
    assert_eq!(reading["fidelity"], "faithful");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);

    let no_cost_out = temp_dir("ag-measurement-harmonic-debt-no-cost");
    let no_cost_profile = read_json(&profile_path);
    let mut no_cost_profile = no_cost_profile;
    no_cost_profile["analytic"]
        .as_object_mut()
        .unwrap()
        .remove("costModel");
    let no_cost_profile_path = no_cost_out.join("measurement_profile_harmonic_debt.json");
    fs::write(
        &no_cost_profile_path,
        serde_json::to_vec_pretty(&no_cost_profile).unwrap(),
    )
    .unwrap();
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_sheaf_laplacian.json")
            .to_str()
            .unwrap(),
        "--law-policy",
        policy_path.to_str().unwrap(),
        "--measurement-profile",
        no_cost_profile_path.to_str().unwrap(),
        "--law-surface",
        surface_path.to_str().unwrap(),
        "--out-dir",
        no_cost_out.to_str().unwrap(),
    ]);
    let no_cost_packet = read_json(&no_cost_out.join("archsig-measurement-packet.json"));
    let no_cost_invariant =
        invariant_by_id(&no_cost_packet, "harmonic-debt:profile:ag-harmonic-debt@1");
    assert_eq!(
        no_cost_invariant["lowerBoundStatus"],
        "cost_model_not_supplied"
    );
    assert_eq!(no_cost_invariant["status"], "silence_by_design");
    assert_eq!(
        no_cost_invariant["whatNext"],
        "supply analytic.costModel with a positive Lipschitz constant and harmonic resolution before evaluating essentialRepairLowerBound"
    );
    assert!(no_cost_invariant.get("essentialRepairLowerBound").is_none());
    let no_cost_reading = no_cost_packet["analyticReadings"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.harmonic-debt")
        .unwrap();
    assert!(
        no_cost_reading["value"]
            .get("essentialRepairLowerBound")
            .is_none()
    );
    assert_eq!(
        no_cost_reading["value"]["whatNext"],
        no_cost_invariant["whatNext"]
    );
    assert!(
        !no_cost_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/8.7")
    );
    assert!(
        no_cost_packet["boundaryStatements"]
            .as_array()
            .unwrap()
            .iter()
            .any(|statement| {
                statement["kind"] == "silence_by_design"
                    && statement["reason"] == "cost_model_not_supplied"
                    && statement["text"].as_str().is_some_and(|text| {
                        text.contains("analytic.costModel")
                            && text.contains("essentialRepairLowerBound")
                    })
            }),
        "missing cost model must remain a typed silence_by_design boundary"
    );
    let no_cost_gate_report = no_cost_out.join("gate-report.json");
    run_sig0(&[
        "gate",
        "--packet",
        no_cost_out
            .join("archsig-measurement-packet.json")
            .to_str()
            .unwrap(),
        "--policy",
        root.join("gate_policy_conservative.json").to_str().unwrap(),
        "--out",
        no_cost_gate_report.to_str().unwrap(),
    ]);
    let no_cost_gate = read_json(&no_cost_gate_report);
    assert_eq!(no_cost_gate["decision"], "PASS_WITHIN_GATE_POLICY");
    let no_cost_mapping = no_cost_gate["ruleOutcomes"][0]["appliedMapping"]
        .as_array()
        .unwrap()
        .iter()
        .find(|mapping| mapping["rowRef"] == "analytic:harmonic-debt:profile:ag-harmonic-debt@1")
        .expect("analytic cost-model silence reaches gate mapping");
    assert_eq!(no_cost_mapping["action"], "pass_with_boundary");
    assert_eq!(no_cost_mapping["boundaryOverrideApplied"], true);

    let invalid_out = temp_dir("ag-measurement-harmonic-debt-invalid-cost");
    let mut invalid_profile = read_json(&profile_path);
    invalid_profile["analytic"]["costModel"]["kind"] = json!("unbounded-cost");
    let invalid_profile_path = invalid_out.join("measurement_profile_harmonic_debt.json");
    fs::write(
        &invalid_profile_path,
        serde_json::to_vec_pretty(&invalid_profile).unwrap(),
    )
    .unwrap();
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_sheaf_laplacian.json")
                .to_str()
                .unwrap(),
            "--law-policy",
            policy_path.to_str().unwrap(),
            "--measurement-profile",
            invalid_profile_path.to_str().unwrap(),
            "--law-surface",
            surface_path.to_str().unwrap(),
            "--out-dir",
            invalid_out.to_str().unwrap(),
        ],
        2,
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_laplacian.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_laplacian.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
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
    let (policy, mut profile) =
        read_fixture_policy_profile(&root.join("law_policy_laplacian.json"));
    profile["resolutionSelector"] = Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_laplacian_bad_profile.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_sheaf_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
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
    let (policy, mut profile) =
        read_fixture_policy_profile(&root.join("law_policy_laplacian.json"));
    profile["witnessFamily"] = json!([
        {"law": "ag.sheaf-laplacian", "variable": "cell:left"},
        {"law": "ag.sheaf-laplacian", "variable": "cell:right"},
        {"law": "ag.sheaf-laplacian", "variable": "cell:extra"}
    ]);
    let policy_path = out_dir.join("law_policy_laplacian_missing_witness.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_sheaf_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_laplacian.json")
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

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(packet["structuralVerdict"][0]["verdictData"]["zero"], false);

    let zero_out_dir = temp_dir("ag-measurement-sheaf-laplacian-exact-zero-color");
    let mut zero_archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    zero_archmap["atoms"][0]["object"] = Value::String("0".to_string());
    zero_archmap["atoms"][1]["object"] = Value::String("0".to_string());
    let zero_archmap_path = zero_out_dir.join("archmap_v2_sheaf_laplacian_exact_zero.json");
    fs::write(
        &zero_archmap_path,
        serde_json::to_vec_pretty(&zero_archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_laplacian.json")
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
        zero_out_dir.to_str().expect("path is utf-8"),
    ]);
    let zero_report = read_json(&zero_out_dir.join("archsig-insight-report.json"));
    assert!(
        zero_report["gluingGeometry"]["locusField"]["fieldRows"]
            .as_array()
            .expect("fieldRows is array")
            .iter()
            .filter(|row| row["status"] == "analytic_reading")
            .all(|row| row["colorRole"] == "analytic_reading"),
        "exact-zero analytic curvature rows must stay in the analytic lane, not measured_zero"
    );
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_laplacian.json")
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_period.json")
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
        .find(|reading| reading["evaluator"] == "ag.period-stokes")
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
fn cli_analyze_v2_period_stokes_audit_mismatch_is_analytic_residual() {
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

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_period.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_period.json")
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

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        0,
        "legacy analytic period-stokes residual must not generate structural verdict rows"
    );
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(
        invariant["stokesAudit"]["status"], "residual_nonzero",
        "legacy analytic period-stokes must report nonzero residual without crashing"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_audit_outputs_structural_verdicts() {
    let root_out = temp_dir("ag-measurement-period-stokes-audit");
    let root = ag_measurement_root();

    for (case, coefficient, boundary_value, expected_verdict, expected_status) in [
        (
            "zero",
            "Q",
            "chain:sigma=3",
            "measured_zero",
            "fixed_coefficient_stokes_audit_computed",
        ),
        (
            "nonzero",
            "Q",
            "chain:sigma=4",
            "measured_nonzero",
            "fixed_coefficient_stokes_audit_computed",
        ),
        (
            "float-only",
            "R",
            "chain:sigma=3",
            "unknown",
            "strict_coefficient_unresolved",
        ),
    ] {
        let out_dir = root_out.join(case);
        fs::create_dir_all(&out_dir).expect("case dir exists");
        let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
        archmap["atoms"][3]["object"] = Value::String(boundary_value.to_string());
        let archmap_path = out_dir.join("archmap.json");
        fs::write(
            &archmap_path,
            serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
        )
        .expect("archmap fixture can be written");
        let (mut policy, mut profile) =
            read_fixture_policy_profile(&root.join("law_policy_period.json"));
        profile["coefficient"] = Value::String(coefficient.to_string());
        profile["effCoeff"] = Value::String("fixed-coefficient-stokes-audit@1".to_string());
        profile["resolutionSelector"] =
            Value::String("finite-poset-period-stokes-audit@1".to_string());
        profile["zeroPredicate"] = Value::String("stokes-residual-zero@1".to_string());
        profile["nonZeroPredicate"] = Value::String("stokes-residual-nonzero@1".to_string());
        profile["certSelector"] = Value::String("finite-certificate@1".to_string());
        profile["witnessFamily"] = json!([
            {"law": "ag.period-stokes-audit", "variable": "cycle:alpha"},
            {"law": "ag.period-stokes-audit", "variable": "cycle:beta"}
        ]);
        policy["policies"][0]["law"] = Value::String("ag.period-stokes-audit".to_string());
        policy["policies"][0]["evaluator"] = Value::String("ag.period-stokes-audit".to_string());
        let policy_path = out_dir.join("law_policy.json");
        write_test_policy_and_profile(&policy_path, policy, profile);

        run_sig0(&[
            "analyze",
            "--archmap",
            archmap_path.to_str().unwrap(),
            "--law-policy",
            policy_path.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--law-surface",
            policy_path
                .with_file_name("law_surface.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().unwrap(),
        ]);

        let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
        let structural = packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array");
        assert_eq!(
            structural.len(),
            1,
            "period-stokes-audit must add exactly one structural verdict row"
        );
        assert_eq!(structural[0]["evaluator"], "ag.period-stokes-audit");
        assert_eq!(structural[0]["verdict"], expected_verdict);
        assert_eq!(
            structural[0]["verdictData"]["methodStatus"],
            expected_status
        );
        let invariant = invariant_by_id(&packet, "period-stokes-audit:profile:ag-period-stokes@1");
        assert_eq!(invariant["evaluator"], "ag.period-stokes-audit");
        assert_eq!(invariant["stokesAudit"]["coefficient"], coefficient);
        assert!(
            packet["analyticReadings"]
                .as_array()
                .expect("analytic readings is array")
                .iter()
                .any(|reading| reading["evaluator"] == "ag.period-stokes"
                    && reading["structuralVerdictRef"] == Value::Null
                    && reading["value"]["readingKind"] == "strict-period-pairing@1"),
            "strict-period-pairing must remain an analytic reading separate from the structural verdict"
        );
    }
}

#[test]
fn cli_analyze_v2_common_structural_verdict_discipline_locks_measurement_evaluators() {
    let root_out = temp_dir("ag-measurement-common-structural-verdict-discipline");
    let mut observed_new_structural_evaluators = BTreeSet::new();

    for (case, evaluator, archmap, policy, profile) in [
        (
            "restriction",
            "ag.restriction-compatibility",
            restriction_archmap("compatible"),
            restriction_policy(),
            restriction_profile(),
        ),
        (
            "section",
            "ag.section-factorization",
            section_archmap("lawful"),
            section_policy(),
            section_profile(),
        ),
        (
            "coherence",
            "ag.coherence-obstruction",
            coherence_triangle_archmap(true),
            coherence_policy("F2", false),
            coherence_profile("F2", false),
        ),
        (
            "boundary-residue",
            "ag.boundary-residue",
            boundary_residue_archmap("zero"),
            boundary_residue_policy(),
            boundary_residue_profile(),
        ),
    ] {
        let packet = run_generated_ag_measurement_case(&root_out, case, archmap, policy, profile);
        assert_common_structural_verdict_discipline(&packet, evaluator);
        observed_new_structural_evaluators.insert(evaluator.to_string());
    }

    let root = ag_measurement_root();
    let mut period_archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    period_archmap["atoms"][3]["object"] = Value::String("chain:sigma=3".to_string());
    let (mut period_policy, mut period_profile) =
        read_fixture_policy_profile(&root.join("law_policy_period.json"));
    period_profile["coefficient"] = Value::String("Q".to_string());
    period_profile["effCoeff"] = Value::String("fixed-coefficient-stokes-audit@1".to_string());
    period_profile["resolutionSelector"] =
        Value::String("finite-poset-period-stokes-audit@1".to_string());
    period_profile["zeroPredicate"] = Value::String("stokes-residual-zero@1".to_string());
    period_profile["nonZeroPredicate"] = Value::String("stokes-residual-nonzero@1".to_string());
    period_profile["certSelector"] = Value::String("finite-certificate@1".to_string());
    period_profile["witnessFamily"] = json!([
        {"law": "ag.period-stokes-audit", "variable": "cycle:alpha"},
        {"law": "ag.period-stokes-audit", "variable": "cycle:beta"}
    ]);
    period_policy["policies"][0]["law"] = Value::String("ag.period-stokes-audit".to_string());
    period_policy["policies"][0]["evaluator"] = Value::String("ag.period-stokes-audit".to_string());
    let period_packet = run_generated_ag_measurement_case(
        &root_out,
        "period-stokes-audit",
        period_archmap,
        period_policy,
        period_profile,
    );
    assert_common_structural_verdict_discipline(&period_packet, "ag.period-stokes-audit");
    observed_new_structural_evaluators.insert("ag.period-stokes-audit".to_string());

    assert_eq!(
        observed_new_structural_evaluators,
        BTreeSet::from([
            "ag.restriction-compatibility".to_string(),
            "ag.section-factorization".to_string(),
            "ag.coherence-obstruction".to_string(),
            "ag.boundary-residue".to_string(),
            "ag.period-stokes-audit".to_string(),
        ]),
        "PRD M common must limit new structural verdict evaluators to M2/M3/M5/M6/M9"
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_period.json")
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_period.json")
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
            .all(|reading| reading["evaluator"] != "ag.period-stokes"),
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_period.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_period.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_period.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
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
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_period.json"));
    profile["resolutionSelector"] = Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_period_bad_profile.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_period_stokes.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
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
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_period.json"));
    profile["witnessFamily"] = json!([
        {"law": "ag.period-stokes", "variable": "cycle:alpha"},
        {"law": "ag.period-stokes", "variable": "cycle:beta"},
        {"law": "ag.period-stokes", "variable": "cycle:extra"}
    ]);
    let policy_path = out_dir.join("law_policy_period_missing_witness.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_period_stokes.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
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
    assert_eq!(
        invariant["supportLocalizedPremise"]["matrixCompletion"],
        "only supplied repairPath x target support pairings are admitted; any missing pairing blocks computation"
    );
    assert_eq!(
        invariant["supportLocalizedPremise"]["requiredPairingCount"],
        Value::from(2)
    );
    assert_eq!(
        invariant["supportLocalizedPremise"]["repairPathSupports"],
        serde_json::json!([{
            "repairPath": "repair:path:core",
            "supportTargets": ["support:api", "support:data"],
            "atomRef": "atom:transfer-repair-path-core"
        }])
    );
    let reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["evaluator"] == "ag.support-transfer")
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
        reading["value"]["supportLocalizedPremise"]["nonConclusion"],
        "no unconditional transfer matrix is inferred for support-disjoint or unobserved paths"
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
fn cli_analyze_v2_support_transfer_blocks_support_disjoint_pairing() {
    let out_dir = temp_dir("ag-measurement-support-transfer-support-disjoint");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"][0]["object"] = Value::String("support:api".to_string());
    let archmap_path = out_dir.join("archmap_v2_support_transfer_support_disjoint.json");
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
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

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(invariant["status"], "not_computed");
    assert!(
        invariant["reason"]
            .as_str()
            .is_some_and(|reason| reason.contains("support_localized_premise_violated"))
    );
    assert_eq!(invariant["supportLocalizedPremise"]["status"], "violated");
    assert_eq!(
        invariant["supportLocalizedPremise"]["blockedPairings"],
        serde_json::json!(["repair:path:core/support:data"])
    );
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["value"]["readingKind"] != "support-localized-transfer@1"),
        "support-disjoint pairings must not fill a transfer matrix"
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
            "object": "support:api,support:data",
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
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
            .all(|reading| reading["evaluator"] != "ag.support-transfer"),
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
            "object": "support:api,support:data",
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_transfer.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_transfer.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_transfer.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
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
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_transfer.json"));
    profile["resolutionSelector"] = Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_transfer_bad_profile.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_support_transfer.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_laplacian.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_rejects_unresolved_measurement_profile_refs() {
    let out_dir = temp_dir("ag-measurement-bad-profile");
    let root = ag_measurement_root();
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    profile["coverRef"] = Value::String("cover:missing".to_string());
    let policy_path = out_dir.join("law_policy_bad_cover.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_selects_multiple_measurement_profiles_at_runtime() {
    let out_dir = temp_dir("ag-measurement-multiple-profiles");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_ag.json"));
    let primary_profile = read_json(&root.join("measurement_profile_ag.json"));
    let mut secondary_profile = primary_profile.clone();
    secondary_profile["profileId"] = json!("profile:ag-secondary@1");
    policy["policies"][0]["profileRef"] = json!("profile:ag-secondary@1");
    let policy_path = out_dir.join("law_policy_multiple_profiles.json");
    let primary_path = out_dir.join("measurement_profile_primary.json");
    let secondary_path = out_dir.join("measurement_profile_secondary.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy writes");
    fs::write(
        &primary_path,
        serde_json::to_vec_pretty(&primary_profile).expect("primary profile serializes"),
    )
    .expect("primary profile writes");
    fs::write(
        &secondary_path,
        serde_json::to_vec_pretty(&secondary_profile).expect("secondary profile serializes"),
    )
    .expect("secondary profile writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        primary_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        secondary_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let profile_ids = packet["profiles"]
        .as_array()
        .expect("multi-profile packet carries profiles")
        .iter()
        .filter_map(|profile| profile["profileId"].as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        profile_ids,
        BTreeSet::from(["profile:ag-default@1", "profile:ag-secondary@1"])
    );
    assert!(invariant_by_id(&packet, "cech-cohomology:profile:ag-secondary@1").is_object());
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert_eq!(
        manifest["measurementProfileInputPaths"]
            .as_array()
            .map(Vec::len),
        Some(2)
    );
    assert_eq!(
        manifest["inputDigests"]["measurementProfiles"]
            .as_array()
            .map(Vec::len),
        Some(2)
    );

    let mut incompatible_profile = secondary_profile;
    incompatible_profile["coverRef"] = json!("cover:missing");
    let incompatible_path = out_dir.join("measurement_profile_incompatible.json");
    fs::write(
        &incompatible_path,
        serde_json::to_vec_pretty(&incompatible_profile).expect("incompatible profile serializes"),
    )
    .expect("incompatible profile writes");
    let incompatible_out = temp_dir("ag-measurement-multiple-profiles-incompatible");
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json").to_str().unwrap(),
            "--law-policy",
            policy_path.to_str().unwrap(),
            "--law-surface",
            root.join("law_surface_ag_v052.json").to_str().unwrap(),
            "--measurement-profile",
            primary_path.to_str().unwrap(),
            "--measurement-profile",
            incompatible_path.to_str().unwrap(),
            "--out-dir",
            incompatible_out.to_str().unwrap(),
        ],
        2,
    );
}
