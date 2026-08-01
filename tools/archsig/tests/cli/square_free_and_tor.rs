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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_square_free.json")
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
        "ag.square-free-repair"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "nsdepth_certificate_computed"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["certRef"],
        "computedInvariants/square-free-repair:profile:ag-square-free@1"
    );
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        1,
        "repair inspection reading must not add a structural verdict row"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(repair["obstructionIdeal"]["id"], "I_Ob^U");
    assert_eq!(
        repair["minimalForbiddenSupports"],
        serde_json::json!([["x_checkout", "x_inventory"], ["x_inventory", "x_payment"]])
    );
    assert!(
        repair["obstructionIdeal"]["generators"]
            .as_array()
            .expect("declared generators are array")
            .iter()
            .all(|generator| {
                generator["supportAtomRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
            }),
        "the observed square-free fixture must realize every declared generator"
    );
    assert_eq!(
        repair["alexanderDualRepair"]["minimalHittingSets"],
        serde_json::json!([["x_inventory"], ["x_checkout", "x_payment"]])
    );
    assert_eq!(
        repair["deltaComplex"]["reducedHomology"]["betti"],
        serde_json::json!([
            {"degree": 0, "dimension": 1},
            {"degree": 1, "dimension": 0}
        ])
    );
    assert_eq!(repair["nsdepthCertificate"]["status"], "computed");
    assert_eq!(repair["nsdepthCertificate"]["nsdepth"], Value::from(2));
    assert_eq!(
        repair["nsdepthCertificate"]["verifiedMinimalForbiddenSupports"],
        serde_json::json!([["x_checkout", "x_inventory"], ["x_inventory", "x_payment"]])
    );
    assert_eq!(
        repair["nsdepthCertificate"]["certificateRef"],
        "computedInvariants/square-free-repair:profile:ag-square-free@1"
    );
    assert_eq!(
        repair["nsdepthCertificate"]["supportAtomRefs"],
        serde_json::json!([
            "atom:support-checkout-inventory",
            "atom:support-inventory-payment"
        ])
    );
    let nsdepth_assumption = packet["assumptions"]
        .as_array()
        .expect("assumptions are array")
        .iter()
        .find(|row| row["theoremRef"] == "part3/7.2B")
        .expect("NSdepth assumption ledger row exists");
    assert_eq!(nsdepth_assumption["status"], "checked");
    assert_eq!(
        nsdepth_assumption["checkedBy"],
        "ag.square-free-repair:computedInvariants/square-free-repair:profile:ag-square-free@1"
    );
    assert!(
        nsdepth_assumption["assumedBy"].is_null(),
        "ArchSig-computed NSdepth certificate must not be downgraded to an assumption"
    );
    let arrangement = invariant_by_id(&packet, "lawful-locus-arrangement:profile:ag-square-free@1");
    assert_eq!(
        arrangement["method"],
        "finite-delta-coordinate-arrangement@1"
    );
    assert_eq!(
        arrangement["facets"],
        serde_json::json!([["x_checkout", "x_payment"], ["x_inventory"]])
    );
    assert_eq!(arrangement["dimension"], Value::from(2));
    assert_eq!(arrangement["irreducibleComponentCount"], Value::from(2));
    assert_eq!(
        arrangement["components"],
        serde_json::json!([
            {
                "componentId": "lawful-locus-component:1",
                "facet": ["x_checkout", "x_payment"],
                "vanishingCoords": ["x_inventory"],
                "dimension": 2
            },
            {
                "componentId": "lawful-locus-component:2",
                "facet": ["x_inventory"],
                "vanishingCoords": ["x_checkout", "x_payment"],
                "dimension": 1
            }
        ])
    );
    assert!(
        arrangement["nonConclusions"]
            .as_array()
            .expect("arrangement nonConclusions is array")
            .iter()
            .any(|entry| entry
                .as_str()
                .is_some_and(|text| text.contains("does not evaluate section-specific"))),
        "lawful locus arrangement must not become a section-level verdict"
    );
    let facet_link = invariant_by_id(&packet, "delta-facet-link-reading:profile:ag-square-free@1");
    assert_eq!(
        facet_link["method"],
        "finite-delta-facet-link-neutral-reading@1"
    );
    assert_eq!(
        facet_link["facetDimensionReading"],
        serde_json::json!({
            "facets": [
                {
                    "facetId": "delta-facet:1",
                    "facet": ["x_checkout", "x_payment"],
                    "dimension": 2
                },
                {
                    "facetId": "delta-facet:2",
                    "facet": ["x_inventory"],
                    "dimension": 1
                }
            ],
            "minDimension": 1,
            "maxDimension": 2
        })
    );
    assert_eq!(facet_link["isPure"], Value::Bool(false));
    assert_eq!(
        facet_link["linkBoundaryReading"],
        serde_json::json!([
            {
                "vertex": "x_checkout",
                "linkFaces": [[], ["x_payment"]],
                "boundaryRanks": [],
                "componentCount": 1
            },
            {
                "vertex": "x_inventory",
                "linkFaces": [[]],
                "boundaryRanks": [],
                "componentCount": 0
            },
            {
                "vertex": "x_payment",
                "linkFaces": [[], ["x_checkout"]],
                "boundaryRanks": [],
                "componentCount": 1
            }
        ])
    );
    assert_eq!(
        facet_link["linkReducedBetti"],
        serde_json::json!([
            {
                "vertex": "x_checkout",
                "betti": [{"degree": 0, "dimension": 0}]
            },
            {
                "vertex": "x_inventory",
                "betti": [{"degree": 0, "dimension": 0}]
            },
            {
                "vertex": "x_payment",
                "betti": [{"degree": 0, "dimension": 0}]
            }
        ])
    );
    let facet_link_text =
        serde_json::to_string(&facet_link).expect("facet/link invariant serializes");
    let banned_terms = [
        "depth".to_string(),
        ["Reis", "ner"].concat(),
        ["Cohen", "-", "Macaulay"].concat(),
        "Krull".to_string(),
        ["sr", "Depth"].concat(),
    ];
    for banned in banned_terms {
        assert!(
            !facet_link_text.contains(&banned),
            "facet/link neutral reading must not contain banned term {banned}"
        );
    }
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["value"]["readingKind"] != "ag.nullstellensatz-depth-monotone"),
        "nsdepth monotone proxy is not authored in ArchMap input after R2"
    );
    let repair_reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["value"]["readingKind"] == "repair-lower-bound-inspection@1")
        .expect("repair lower-bound inspection reading exists");
    assert_eq!(repair_reading["regime"], "theorem-candidate");
    assert_eq!(repair_reading["structuralVerdictRef"], Value::Null);
    assert_eq!(
        repair_reading["value"]["minimalHittingSets"],
        serde_json::json!([["x_inventory"], ["x_checkout", "x_payment"]])
    );
    assert_eq!(
        repair_reading["value"]["nonClaim"],
        "not automatic repair; not operation semantics"
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(summary["conclusion"], ARCHSIG_REPAIR_TARGETS_IDENTIFIED);
    assert_eq!(
        summary["readThisFirst"]["conclusion"],
        ARCHSIG_REPAIR_TARGETS_IDENTIFIED
    );
    assert!(
        summary["readThisFirst"]["whatItMeans"]
            .as_str()
            .is_some_and(|text| text.contains("combinatorial repair target supports"))
    );
    assert!(
        summary["readThisFirst"]["boundary"]
            .as_str()
            .is_some_and(|text| {
                text.contains("Principle 5.3 boundary")
                    && text.contains("not automatic semantic repairs")
            })
    );
    let report = read_json(&out_dir.join("archsig-insight-report.json"));
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
}

#[test]
fn cli_analyze_v2_square_free_uses_law_surface_witnesses() {
    let out_dir = temp_dir("ag-measurement-square-free-witness-family");
    let root = ag_measurement_root();
    let (policy, profile) = read_fixture_policy_profile(&root.join("law_policy_square_free.json"));
    let policy_path = out_dir.join("law_policy_square_free_missing_witness.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_square_free_repair.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
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

#[test]
fn cli_analyze_v2_square_free_ignores_undeclared_observed_variables() {
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

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_square_free.json")
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

#[test]
fn cli_analyze_v2_square_free_uses_profile_only_for_runtime_caps() {
    let out_dir = temp_dir("ag-measurement-square-free-too-many-witnesses");
    let root = ag_measurement_root();
    let (policy, mut profile) =
        read_fixture_policy_profile(&root.join("law_policy_square_free.json"));
    profile["witnessFamily"] = Value::Array(
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
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_square_free_repair.json")
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
fn cli_analyze_v2_square_free_observation_does_not_supply_generators() {
    let root = ag_measurement_root();
    let baseline_out = run_analyze_fixture_lock(
        "ag-measurement-square-free-law-surface-baseline",
        "archmap_v2_square_free_repair.json",
        "law_policy_square_free.json",
        "law_surface_ag_v052.json",
    );
    let extra_out = temp_dir("ag-measurement-square-free-observation-extra");
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(json!({
            "id": "atom:support-checkout-inventory-extra",
            "kind": "relation",
            "subject": "x_checkout",
            "object": "x_inventory",
            "axis": "square-free",
            "predicate": "support",
            "refs": ["src:checkout", "src:inventory"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(json!("atom:support-checkout-inventory-extra"));
    let archmap_path = extra_out.join("archmap-extra-support.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture writes");
    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        extra_out.to_str().expect("path is utf-8"),
    ]);

    let baseline = read_json(&baseline_out.join("archsig-measurement-packet.json"));
    let extra = read_json(&extra_out.join("archsig-measurement-packet.json"));
    let baseline_repair = invariant_by_id(&baseline, "square-free-repair:profile:ag-square-free@1");
    let extra_repair = invariant_by_id(&extra, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(
        baseline_repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .iter()
            .map(|generator| generator["support"].clone())
            .collect::<Vec<_>>(),
        extra_repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .iter()
            .map(|generator| generator["support"].clone())
            .collect::<Vec<_>>(),
        "observed support atoms must not change the declared obstruction ideal"
    );
    assert_eq!(
        baseline_repair["minimalForbiddenSupports"],
        extra_repair["minimalForbiddenSupports"]
    );
    assert_eq!(
        baseline_repair["alexanderDualRepair"]["minimalHittingSets"],
        extra_repair["alexanderDualRepair"]["minimalHittingSets"]
    );
    assert!(
        extra_repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .iter()
            .any(|generator| generator["supportAtomRefs"]
                .as_array()
                .unwrap()
                .contains(&json!("atom:support-checkout-inventory-extra")))
    );
}

#[test]
fn cli_analyze_v2_square_free_requires_explicit_law_surface() {
    let out_dir = temp_dir("ag-measurement-square-free-missing-law-surface");
    let root = ag_measurement_root();
    let output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_square_free_repair.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires --law-surface"));
}

#[test]
fn cli_analyze_v2_square_free_law_surface_generator_change_is_observed() {
    let out_dir = temp_dir("ag-measurement-square-free-law-surface-change");
    let root = ag_measurement_root();
    let mut surface = read_json(&root.join("law_surface_ag_v052.json"));
    surface["laws"][0]["forbiddenSupportGenerators"]
        .as_array_mut()
        .expect("forbidden support generators are array")
        .push(json!({"support": ["x_checkout", "x_payment"]}));
    let surface_path = out_dir.join("law_surface_changed.json");
    fs::write(
        &surface_path,
        serde_json::to_vec_pretty(&surface).expect("law surface serializes"),
    )
    .expect("law surface fixture writes");
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
        "--measurement-profile",
        root.join("measurement_profile_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert!(manifest["inputDigests"]["lawSurface"]["sha256"].is_string());
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(
        repair["minimalForbiddenSupports"].as_array().unwrap().len(),
        3
    );
    assert!(
        repair["minimalForbiddenSupports"]
            .as_array()
            .unwrap()
            .iter()
            .any(|support| support == &json!(["x_checkout", "x_payment"]))
    );
}

#[test]
fn cli_analyze_v2_tor_requires_explicit_law_surface() {
    let out_dir = temp_dir("ag-measurement-tor-missing-law-surface");
    let root = ag_measurement_root();
    let output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires --law-surface"));
}

#[test]
fn cli_analyze_v2_cech_requires_explicit_law_surface() {
    let out_dir = temp_dir("ag-measurement-cech-missing-law-surface");
    let root = ag_measurement_root();
    let output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_h1.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires --law-surface"));
}

#[test]
fn cli_analyze_v2_section_requires_explicit_law_surface() {
    let out_dir = temp_dir("ag-measurement-section-missing-law-surface");
    let archmap_path = out_dir.join("archmap.json");
    let policy_path = out_dir.join("law_policy.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&section_archmap("lawful")).expect("archmap serializes"),
    )
    .expect("archmap is written");
    write_test_policy_and_profile(&policy_path, section_policy(), section_profile());
    let output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires --law-surface"));
}

#[test]
fn cli_analyze_v2_square_free_without_observed_support_keeps_declared_generators() {
    let root = ag_measurement_root();
    let archmap_path = root.join("archmap_v2_square_free_repair_unobserved.json");
    let first_out = run_square_free_analysis("ag-measurement-square-free-zero-a", &archmap_path);
    let second_out = run_square_free_analysis("ag-measurement-square-free-zero-b", &archmap_path);
    assert_byte_identical_analysis_artifacts(&first_out, &second_out);

    let packet = read_json(&first_out.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "square_free_observation_empty"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(
        repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .len(),
        2
    );
    assert!(
        repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .iter()
            .all(|generator| generator["supportAtomRefs"].as_array().unwrap().is_empty())
    );
    let unobserved_boundaries = packet["boundaryStatements"]
        .as_array()
        .expect("boundary statements are array")
        .iter()
        .filter(|statement| statement["reason"] == "declared_generator_unobserved")
        .collect::<Vec<_>>();
    assert_eq!(unobserved_boundaries.len(), 2);
    assert!(unobserved_boundaries.iter().all(|statement| {
        statement["kind"] == "silence_by_design"
            && statement["scopeRefs"].as_array().is_some_and(|refs| {
                refs.iter().any(|reference| {
                    reference
                        .as_str()
                        .is_some_and(|reference| reference.starts_with("structuralVerdict/"))
                })
            })
    }));
    let certificate = &repair["nsdepthCertificate"];
    assert_eq!(
        certificate["certificateRef"],
        "computedInvariants/square-free-repair:profile:ag-square-free@1"
    );
    assert_eq!(certificate["supportAtomRefs"], json!([]));
    let summary = read_json(&first_out.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE
    );
    assert!(summary["translationRule"]["theoremRef"].is_null());
    assert_eq!(
        summary["readThisFirst"]["whatItMeans"],
        "ArchSig produced a profile-relative foundation result for the selected measurement surface."
    );
    let report = read_json(&first_out.join("archsig-insight-report.json"));
    assert!(
        report["gluingGeometry"]["forbiddenCages"]
            .as_array()
            .is_some_and(Vec::is_empty)
    );
    assert!(
        report["gluingGeometry"]["repairMorphs"]
            .as_array()
            .is_some_and(Vec::is_empty)
    );
}

#[test]
fn cli_square_free_mixed_observation_keeps_nonzero_gate_blocking() {
    let root = ag_measurement_root();
    let out_dir = temp_dir("ag-measurement-square-free-mixed-observation");
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["id"] != "atom:support-inventory-payment")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:support-inventory-payment"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_square_free_mixed.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("mixed ArchMap serializes"),
    )
    .expect("mixed ArchMap writes");

    let run_dir = run_square_free_analysis("ag-square-free-mixed", &archmap_path);
    let packet = read_json(&run_dir.join("archsig-measurement-packet.json"));
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    let generators = repair["obstructionIdeal"]["generators"]
        .as_array()
        .expect("square-free generators are array");
    assert_eq!(generators.len(), 2);
    assert!(generators.iter().any(|generator| {
        generator["supportAtomRefs"]
            .as_array()
            .is_some_and(|refs| refs.is_empty())
    }));
    assert!(generators.iter().any(|generator| {
        generator["supportAtomRefs"]
            .as_array()
            .is_some_and(|refs| !refs.is_empty())
    }));
    let unobserved_boundaries = packet["boundaryStatements"]
        .as_array()
        .expect("boundary statements are array")
        .iter()
        .filter(|statement| statement["reason"] == "declared_generator_unobserved")
        .collect::<Vec<_>>();
    assert_eq!(unobserved_boundaries.len(), 1);
    assert!(
        unobserved_boundaries[0]["scopeRefs"]
            .as_array()
            .is_some_and(|refs| refs.iter().all(|reference| {
                !reference
                    .as_str()
                    .is_some_and(|reference| reference.starts_with("structuralVerdict/"))
            }))
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );

    let report = run_square_free_gate(&run_dir, 1);
    let mapping = report["ruleOutcomes"][0]["appliedMapping"]
        .as_array()
        .expect("absolute gate mappings")
        .iter()
        .find(|mapping| {
            mapping["rowRef"]
                .as_str()
                .is_some_and(|row_ref| row_ref.contains("ag-square-free-repair"))
        })
        .expect("mixed square-free gate mapping");
    assert_eq!(mapping["verdict"], "measured_nonzero");
    assert_eq!(mapping["action"], "block");
    assert_eq!(mapping["boundaryOverrideApplied"], false);

    assert_eq!(
        report["decision"], "BLOCKED_BY_GATE_POLICY",
        "mixed observation must remain blocking even with one silence_by_design statement"
    );
    let geometry =
        read_json(&run_dir.join("archsig-insight-report.json"))["gluingGeometry"].clone();
    assert_eq!(geometry["forbiddenCages"].as_array().map(Vec::len), Some(1));
    assert!(
        geometry["forbiddenCages"][0]["atomRefs"]
            .as_array()
            .is_some_and(|refs| !refs.is_empty())
    );
}

#[test]
fn cli_square_free_observation_drives_conservative_gate_sequence() {
    let root = ag_measurement_root();
    let sequence_dir = temp_dir("ag-measurement-square-free-gate-sequence");
    let mut clean_archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    clean_archmap["atoms"] = Value::Array(
        clean_archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["predicate"] != "support")
            .cloned()
            .collect(),
    );
    clean_archmap["contexts"][0]["atoms"] = Value::Array(
        clean_archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| {
                !matches!(
                    atom.as_str(),
                    Some("atom:support-checkout-inventory" | "atom:support-inventory-payment")
                )
            })
            .cloned()
            .collect(),
    );
    let clean_archmap_path = sequence_dir.join("archmap_square_free_clean.json");
    fs::write(
        &clean_archmap_path,
        serde_json::to_vec_pretty(&clean_archmap).expect("clean ArchMap serializes"),
    )
    .expect("clean ArchMap writes");

    let clean_run = run_square_free_analysis("ag-square-free-gate-clean", &clean_archmap_path);
    let blocked_run = run_analyze_fixture_lock_with_surface(
        "ag-square-free-gate-blocked",
        "archmap_v2_square_free_repair.json",
        "law_policy_square_free.json",
        "law_surface_ag_v052.json",
    );
    let repaired_archmap_path = sequence_dir.join("archmap_square_free_repaired.json");
    let repaired_archmap = read_json(&root.join("archmap_v2_square_free_repair_unobserved.json"));
    fs::write(
        &repaired_archmap_path,
        serde_json::to_vec_pretty(&repaired_archmap).expect("repaired ArchMap serializes"),
    )
    .expect("repaired ArchMap writes");
    assert_ne!(clean_archmap_path, repaired_archmap_path);
    let repaired_run =
        run_square_free_analysis("ag-square-free-gate-repaired", &repaired_archmap_path);

    let clean_gate = run_square_free_gate(&clean_run, 0);
    let blocked_gate = run_square_free_gate(&blocked_run, 1);
    let repaired_gate = run_square_free_gate(&repaired_run, 0);

    assert_eq!(clean_gate["decision"], "PASS_WITHIN_GATE_POLICY");
    assert_eq!(blocked_gate["decision"], "BLOCKED_BY_GATE_POLICY");
    assert_eq!(repaired_gate["decision"], "PASS_WITHIN_GATE_POLICY");
    for report in [&clean_gate, &repaired_gate] {
        let mapping = report["ruleOutcomes"][0]["appliedMapping"]
            .as_array()
            .expect("absolute gate mappings")
            .iter()
            .find(|mapping| {
                mapping["rowRef"]
                    .as_str()
                    .is_some_and(|row_ref| row_ref.contains("ag-square-free-repair"))
            })
            .expect("square-free gate mapping");
        assert_eq!(mapping["verdict"], "measured_zero");
        assert_eq!(mapping["action"], "pass_with_boundary");
        assert_eq!(mapping["boundaryOverrideApplied"], true);
    }
    let blocked_mapping = blocked_gate["ruleOutcomes"][0]["appliedMapping"]
        .as_array()
        .expect("blocked absolute gate mappings")
        .iter()
        .find(|mapping| {
            mapping["rowRef"]
                .as_str()
                .is_some_and(|row_ref| row_ref.contains("ag-square-free-repair"))
        })
        .expect("blocked square-free gate mapping");
    assert_eq!(blocked_mapping["verdict"], "measured_nonzero");
    assert_eq!(blocked_mapping["action"], "block");
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
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

    let validation = read_json(&out_dir.join("law-policy-validation.json"));
    let expanded = &validation["expandedPolicies"][0];
    assert!(
        !expanded
            .as_object()
            .expect("expanded policy is an object")
            .contains_key("law")
    );
    assert_eq!(
        expanded["lawPair"],
        json!(["law:checkout", "law:inventory"])
    );
    assert_eq!(
        expanded["sourceSelector"],
        "lawPair:law:checkout,law:inventory"
    );

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.law-conflict-tor"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "finite_monomial_tor_taylor_computed"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["certRef"],
        "computedInvariants/law-conflict-tor:profile:ag-law-conflict-tor@1"
    );
    assert!(
        packet["structuralVerdict"][0]["dependsOnAssumptions"]
            .as_array()
            .expect("dependsOnAssumptions is array")
            .iter()
            .any(|assumption_id| assumption_id.as_str().is_some_and(
                |id| id.starts_with("assumption:part8-9-1-coefficient-compatibility:")
            )),
        "Tor verdict must depend on the common ambient coefficient compatibility ledger row"
    );
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        1,
        "Hilbert interference reading must not add a structural verdict row"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert!(
        summary["translationRule"]["concreteSupportRefs"]
            .as_array()
            .is_some_and(|refs| {
                refs.iter().any(|reference| reference == "src:ambient")
                    && refs
                        .iter()
                        .any(|reference| reference == "src:checkout-policy")
                    && refs
                        .iter()
                        .any(|reference| reference == "ctx:tor-common-ambient")
            })
    );
    assert_eq!(tor["method"], "finite-monomial-tor-taylor@1");
    assert_eq!(
        tor["claimScope"],
        "degree-1 square-free monomial Tor over the selected common ambient pair"
    );
    assert_eq!(tor["resolutionSelectorEffective"], true);
    assert_eq!(
        tor["commonAmbient"]["ambientRef"],
        "ambient:checkout-inventory"
    );
    let tor_object = tor.as_object().expect("Tor invariant is object");
    assert!(
        !tor_object.contains_key("coefficientRef")
            && !tor_object.contains_key("comparisonMorphismRef"),
        "M15 must expose coefficient compatibility through the assumption ledger, not new Tor schema fields"
    );
    assert_eq!(
        tor["lawConflicts"],
        serde_json::json!([{
            "conflictId": "LawConflict_1:1",
            "degree": 1,
            "support": ["x_checkout", "x_inventory", "x_payment"],
            "multidegree": ["x_checkout", "x_inventory", "x_payment"],
            "sharedSupport": ["x_inventory"],
            "leftLaw": "law:checkout",
            "leftGeneratorRef": "law-surface:law:checkout:1",
            "rightLaw": "law:inventory",
            "rightGeneratorRef": "law-surface:law:inventory:1",
            "contextRefs": ["ctx:tor-common-ambient"],
            "sourceRefs": ["src:checkout-policy", "src:inventory-policy"]
        }])
    );
    assert_eq!(
        tor["torByDegree"],
        serde_json::json!([{
            "degree": 1,
            "classCount": 1,
            "coefficient": "F2",
            "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
        }])
    );
    assert_eq!(tor["proxyComparison"]["proxyClassCount"], Value::from(1));
    assert_eq!(tor["proxyComparison"]["taylorClassCount"], Value::from(1));
    assert!(
        tor["boundaryNote"]
            .as_str()
            .is_some_and(|note| note.contains("higher Tor_i") && note.contains("F2")),
        "Tor boundary note must keep higher Tor and field-coefficient boundaries visible"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(|row| row["theoremRef"] == "part8/9.1-coefficient-compatibility"
                && row["assumption"]
                    == "common ambient coefficient compatibility under the selected single F2 coefficient model"
                && row["status"] == "checked"
                && row["checkedBy"]
                    == "measurement-profile:profile:ag-law-conflict-tor@1.coefficient:F2"),
        "Tor assumption ledger must record checked coefficient compatibility for the selected common ambient"
    );
    let hilbert = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["value"]["readingKind"] == "hilbert-interference-series@1")
        .expect("Hilbert interference audit reading exists");
    assert_eq!(hilbert["regime"], "analytic-measurement");
    assert_eq!(hilbert["structuralVerdictRef"], Value::Null);
    assert_eq!(
        hilbert["value"]["regimeBoundary"],
        "audit-only in the selected graded square-free monomial Taylor regime"
    );
    assert_eq!(
        hilbert["value"]["series"],
        serde_json::json!([{"degree": 1, "coefficient": 1}])
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "MEASURED_AG_OBSTRUCTION_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_disjoint_supports_are_not_computed() {
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
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
fn cli_analyze_v2_law_conflict_tor_undeclared_nested_support_is_unmeasured() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-nested");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][1]["object"] = Value::String("x_checkout,x_inventory,x_inventory".to_string());
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
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
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unmeasured");
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert!(tor["lawConflicts"].as_array().unwrap().is_empty());
}

#[test]
fn cli_analyze_v2_law_conflict_tor_taylor_reduces_proxy_overcount() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-taylor-overcount");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][2]["object"] = Value::String("x_checkout,x_inventory,x_payment".to_string());
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(json!({
            "id": "atom:checkout-law-generator-2",
            "kind": "relation",
            "subject": "law:checkout",
            "object": "x_inventory,x_payment",
            "axis": "tor",
            "predicate": "lawIdealGenerator",
            "refs": ["src:checkout-policy"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String("atom:checkout-law-generator-2".to_string()));
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_taylor_overcount.json");
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
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
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(tor["method"], "finite-monomial-tor-taylor@1");
    assert_eq!(tor["proxyComparison"]["proxyClassCount"], Value::from(1));
    assert_eq!(tor["proxyComparison"]["taylorClassCount"], Value::from(1));
    assert_eq!(
        tor["lawConflicts"][0]["multidegree"],
        serde_json::json!(["x_checkout", "x_inventory", "x_payment"])
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_preserves_common_ambient_law_pair_order() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-reversed-law-pair");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][0]["object"] = Value::String("law:inventory,law:checkout".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_reversed_law_pair.json");
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
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
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(
        tor["commonAmbient"]["lawPair"],
        serde_json::json!(["law:inventory", "law:checkout"])
    );
    assert_eq!(tor["lawConflicts"][0]["leftLaw"], "law:inventory");
    assert_eq!(tor["lawConflicts"][0]["rightLaw"], "law:checkout");
    assert_eq!(
        tor["lawConflicts"][0]["leftGeneratorRef"],
        "law-surface:law:inventory:1"
    );
    assert_eq!(
        tor["lawConflicts"][0]["rightGeneratorRef"],
        "law-surface:law:checkout:1"
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_non_square_free_is_unmeasured() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-non-square-free");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][1]["object"] = Value::String("x_checkout,x_inventory,x_inventory".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_non_square_free.json");
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
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
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unmeasured");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "non_square_free_monomial"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(tor["method"], "finite-monomial-tor-taylor@1");
    assert_eq!(tor["torByDegree"][0]["status"], "unmeasured");
    assert_eq!(tor["torByDegree"][0]["classCount"], Value::Null);
    assert_eq!(tor["proxyComparison"]["taylorClassCount"], Value::Null);
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["value"]["readingKind"] != "hilbert-interference-series@1"),
        "Hilbert interference reading must stay absent outside the square-free monomial regime"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(|row| row["theoremRef"] == "part5/5.5"
                && row["assumption"]
                    == "finite square-free monomial law ideals selected for degree-1 Taylor Tor"
                && row["status"] == "violated"),
        "non-square-free generators must violate the square-free Taylor premise"
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_tor.json")
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
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
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
        "no_common_ambient"
    );
    assert!(
        packet["structuralVerdict"][0]["dependsOnAssumptions"]
            .as_array()
            .expect("dependsOnAssumptions is array")
            .iter()
            .any(|assumption_id| assumption_id.as_str().is_some_and(
                |id| id.starts_with("assumption:part8-9-1-coefficient-compatibility:")
            )),
        "not-computed Tor verdict still records the coefficient compatibility dependency"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(tor["status"], "not_computed");
    assert_eq!(tor["reason"], "no_common_ambient");
    assert_ne!(
        packet["structuralVerdict"][0]["verdict"], "measured_zero",
        "violated common ambient / coefficient compatibility must not degrade to measured_zero"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(
                |row| row["theoremRef"] == "part8/9.1-coefficient-compatibility"
                    && row["status"] == "violated"
                    && row["assumedBy"] == "measurement-profile:profile:ag-law-conflict-tor@1"
            ),
        "missing common ambient must mark coefficient compatibility violated in the assumption ledger"
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_uses_law_surface_witnesses() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-witness-family");
    let root = ag_measurement_root();
    let (policy, profile) = read_fixture_policy_profile(&root.join("law_policy_tor.json"));
    let policy_path = out_dir.join("law_policy_tor_missing_witness.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
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

#[test]
fn cli_analyze_v2_law_conflict_tor_selects_only_declared_law_pair() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-explicit-law-pair");
    let root = ag_measurement_root();
    let (policy, profile) = read_fixture_policy_profile(&root.join("law_policy_tor.json"));
    let policy_path = out_dir.join("law_policy_tor.json");
    let surface_path = out_dir.join("law_surface_with_unselected_law.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    let mut surface = read_json(&root.join("law_surface_ag_v052.json"));
    surface["laws"].as_array_mut().unwrap().push(json!({
        "lawId": "law:shipping",
        "conditionType": "closed-equational",
        "witnessVariables": [{
            "variable": "x_shipping",
            "binding": {
                "archmapVariable": "x_shipping",
                "axis": "square-free",
                "predicate": "support"
            }
        }],
        "forbiddenSupportGenerators": [{"support": ["x_shipping"]}]
    }));
    fs::write(
        &surface_path,
        serde_json::to_vec_pretty(&surface).expect("law surface serializes"),
    )
    .expect("law surface is written");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert!(
        tor["witnessVariables"]
            .as_array()
            .expect("Tor witness variables are an array")
            .iter()
            .all(|variable| variable != "x_shipping"),
        "an unselected law declared with a law: prefix must not enter the Tor witness family"
    );
    assert_eq!(
        tor["witnessVariables"],
        json!(["x_checkout", "x_inventory", "x_payment"])
    );
    assert_eq!(
        tor["lawIdeals"]
            .as_array()
            .expect("Tor law ideals are an array")
            .iter()
            .map(|ideal| ideal["law"].clone())
            .collect::<Vec<_>>(),
        vec![json!("law:checkout"), json!("law:inventory")]
    );
}

#[test]
fn cli_law_policy_rejects_malformed_tor_law_pairs() {
    let root = ag_measurement_root();
    for (name, pair, evaluator, expected_evidence) in [
        (
            "missing",
            None,
            Some("ag.law-conflict-tor"),
            "ag.law-conflict-tor requires an explicit lawPair declaration",
        ),
        (
            "one",
            Some(vec!["law:checkout"]),
            Some("ag.law-conflict-tor"),
            "lawPair must contain exactly two distinct non-empty law ids",
        ),
        (
            "duplicate",
            Some(vec!["law:checkout", "law:checkout"]),
            Some("ag.law-conflict-tor"),
            "lawPair must contain exactly two distinct non-empty law ids",
        ),
        (
            "wrong-evaluator",
            Some(vec!["law:checkout", "law:inventory"]),
            Some("ag.square-free-repair"),
            "lawPair is reserved for the ag.law-conflict-tor evaluator",
        ),
    ] {
        let out_dir = temp_dir(&format!("ag-law-policy-tor-pair-{name}"));
        let mut policy = read_json(&root.join("law_policy_tor.json"));
        let entry = policy["policies"][0]
            .as_object_mut()
            .expect("Tor policy entry is an object");
        if let Some(pair) = pair {
            entry.insert("lawPair".to_string(), json!(pair));
        } else {
            entry.remove("lawPair");
        }
        entry.insert("evaluator".to_string(), json!(evaluator));
        let policy_path = out_dir.join("law_policy.json");
        fs::write(
            &policy_path,
            serde_json::to_vec_pretty(&policy).expect("policy serializes"),
        )
        .expect("policy writes");
        fs::write(
            out_dir.join("measurement_profile.json"),
            fs::read(root.join("measurement_profile_tor.json")).expect("profile reads"),
        )
        .expect("profile writes");
        let report_path = out_dir.join("law-policy-validation.json");

        run_sig0_expect_code(
            &[
                "law-policy",
                "--law-policy",
                policy_path.to_str().expect("policy path is utf-8"),
                "--measurement-profile",
                test_measurement_profile_path(Path::new(
                    policy_path.to_str().expect("policy path is utf-8"),
                ))
                .to_str()
                .expect("profile path is utf-8"),
                "--law-surface",
                root.join("law_surface_ag_v052.json")
                    .to_str()
                    .expect("surface path is utf-8"),
                "--out",
                report_path.to_str().expect("report path is utf-8"),
            ],
            1,
        );
        let report = read_json(&report_path);
        assert_eq!(report["summary"]["result"], "fail");
        assert!(report["checks"].as_array().is_some_and(|checks| {
            checks.iter().any(|check| {
                check["id"] == "law-policy-schema052-entry-shape"
                    && check["examples"].as_array().is_some_and(|examples| {
                        examples
                            .iter()
                            .any(|example| example["evidence"] == expected_evidence)
                    })
            })
        }));
    }
}

#[test]
fn cli_law_policy_rejects_non_closed_tor_law_surface() {
    let out_dir = temp_dir("ag-law-policy-tor-non-closed");
    let root = ag_measurement_root();
    let mut surface = read_json(&root.join("law_surface_ag_v052.json"));
    for law_id in ["law:checkout", "law:inventory"] {
        surface["laws"]
            .as_array_mut()
            .expect("law surface laws are an array")
            .iter_mut()
            .find(|law| law["lawId"] == law_id)
            .expect("Tor law exists")
            .as_object_mut()
            .expect("Tor law is an object")
            .insert("conditionType".to_string(), json!("constructible"));
    }
    let surface_path = out_dir.join("law_surface_non_closed.json");
    fs::write(
        &surface_path,
        serde_json::to_vec_pretty(&surface).expect("surface serializes"),
    )
    .expect("surface writes");
    let report_path = out_dir.join("law-policy-validation.json");

    run_sig0_expect_code(
        &[
            "law-policy",
            "--law-policy",
            root.join("law_policy_tor.json")
                .to_str()
                .expect("policy path is utf-8"),
            "--measurement-profile",
            root.join("measurement_profile_tor.json")
                .to_str()
                .expect("profile path is utf-8"),
            "--law-surface",
            surface_path.to_str().expect("surface path is utf-8"),
            "--out",
            report_path.to_str().expect("report path is utf-8"),
        ],
        1,
    );
    let report = read_json(&report_path);
    assert!(report["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-policy-schema052-law-surface-resolution"
                && check["result"] == "fail"
        })
    }));
}

#[test]
fn cli_analyze_v2_square_free_requires_explicit_law() {
    let out_dir = temp_dir("ag-measurement-square-free-missing-law");
    let root = ag_measurement_root();
    let (mut policy, profile) =
        read_fixture_policy_profile(&root.join("law_policy_square_free.json"));
    policy["policies"][0]
        .as_object_mut()
        .expect("policy entry is an object")
        .remove("law");
    let policy_path = out_dir.join("law_policy_square_free_missing_law.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    let report_path = out_dir.join("law-policy-validation.json");
    run_sig0_expect_code(
        &[
            "law-policy",
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            root.join("measurement_profile_square_free.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out",
            report_path.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let report = read_json(&report_path);
    assert!(report["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-policy-schema052-entry-shape"
                && check["examples"].as_array().is_some_and(|examples| {
                    examples.iter().any(|example| {
                        example["evidence"]
                            == "ag.square-free-repair requires an explicit law selector"
                    })
                })
        })
    }));
}

#[test]
fn cli_analyze_v2_law_conflict_tor_rejects_unsupported_resolution_selector() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-bad-resolution");
    let root = ag_measurement_root();
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_tor.json"));
    profile["resolutionSelector"] = Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_tor_bad_resolution.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_law_conflict_tor.json")
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
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_tor.json")
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
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_ignores_undeclared_observed_variables() {
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

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
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
