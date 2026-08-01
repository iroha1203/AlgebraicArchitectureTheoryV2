#[test]
fn cli_analyze_rejects_measurement_profile_witness_family() {
    let out_dir = temp_dir("ag-measurement-profile-witness-family-rejected");
    let root = ag_measurement_root();
    let policy_path = out_dir.join("law_policy.json");
    let profile_path = out_dir.join("measurement_profile.json");
    let mut profile = read_json(&root.join("measurement_profile_ag.json"));
    profile["witnessFamily"] = json!([
        {"law": "ag.cech-obstruction", "variable": "e_order_shared"}
    ]);
    fs::write(
        &policy_path,
        fs::read(root.join("law_policy_ag.json")).expect("policy fixture reads"),
    )
    .expect("policy fixture writes");
    fs::write(
        &profile_path,
        serde_json::to_vec_pretty(&profile).expect("profile serializes"),
    )
    .expect("profile writes");
    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        profile_path.to_str().expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("unknown field `witnessFamily`"));
    assert!(!out_dir.join("archsig-measurement-packet.json").exists());
}

#[test]
fn cli_analyze_rejects_input_output_aliases() {
    let out_dir = temp_dir("ag-measurement-input-output-alias");
    let root = ag_measurement_root();
    let archmap_path = out_dir.join("normalized-archmap.json");
    fs::copy(root.join("archmap_v2.json"), &archmap_path).expect("archmap fixture copies");
    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("profile path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("law surface path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("output directory is utf-8"),
    ]);
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("output path must differ from input path")
    );
}

#[test]
fn cli_analyze_v2_writes_measurement_packet_foundation() {
    let out_dir = temp_dir("ag-measurement-analyze");
    let root = ag_measurement_root();
    let profile_path = out_dir.join("measurement_profile_ceiling.json");
    let mut profile = read_json(&root.join("measurement_profile_ag.json"));
    profile["diagnosticCeiling"] = json!("descent");
    fs::write(
        &profile_path,
        serde_json::to_vec_pretty(&profile).expect("ceiling profile serializes"),
    )
    .expect("ceiling profile writes");
    let law_surface_path = out_dir.join("law_surface.json");
    let mut law_surface = read_json(&root.join("law_surface_ag_v052.json"));
    law_surface["quotientSheafCondition"] = json!({"mode": "assumed"});
    fs::write(
        &law_surface_path,
        serde_json::to_vec_pretty(&law_surface).expect("stage3 law surface serializes"),
    )
    .expect("stage3 law surface writes");

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
        profile_path.to_str().expect("path is utf-8"),
        "--law-surface",
        law_surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let normalized = read_json(&out_dir.join("normalized-archmap.json"));
    assert_eq!(normalized["schema"], "normalized-archmap/v0.5.4");
    assert_eq!(
        normalized["summary"]["doctrineFingerprint"],
        "sha256:aat-canonical-doctrine-schema052"
    );

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["schema"], "archsig-measurement-packet/v0.5.4");
    assert!(packet["profile"].is_object());
    assert!(packet["structuralVerdict"].is_array());
    assert!(packet["computedInvariants"].is_array());
    assert!(packet["analyticReadings"].is_array());
    assert!(packet["assumptions"].is_array());
    assert!(packet["boundaryStatements"].is_array());
    assert!(packet["nonConclusions"].is_array());
    assert!(
        packet["nonConclusions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|text| {
                text.as_str().is_some_and(|text| {
                    text.contains("silence_by_design: diagnostic ceiling descent")
                })
            })
    );
    let boundary_texts = packet["boundaryStatements"]
        .as_array()
        .unwrap()
        .iter()
        .map(|statement| statement["text"].as_str().expect("boundary text"))
        .collect::<BTreeSet<_>>();
    assert!(
        packet["nonConclusions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|text| { boundary_texts.contains(text.as_str().expect("nonConclusion text")) }),
        "compat nonConclusions must be reproduced as boundaryStatements text"
    );
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .unwrap()
            .iter()
            .any(|statement| statement["kind"] == "not_applicable"
                && statement["scopeRefs"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|scope_ref| scope_ref == "candidate-regime:stability-placeholder")),
        "analytic-only theorem candidate must be represented as a not_applicable boundary"
    );
    let boundary_kinds = packet["boundaryStatements"]
        .as_array()
        .unwrap()
        .iter()
        .map(|statement| statement["kind"].as_str().expect("boundary kind"))
        .collect::<BTreeSet<_>>();
    assert!(
        boundary_kinds.is_subset(&BTreeSet::from([
            "silence_by_design",
            "out_of_selected_vocabulary",
            "unmeasured_support",
            "violated_assumption",
            "blocked_method",
            "not_applicable",
        ])),
        "M8 must reuse existing BoundaryStatementV1 kinds"
    );
    for (id, kind, reason_text, scope_text) in [
        (
            "boundary:m8:higher-hn-silence",
            "silence_by_design",
            "higher_hn_n_ge_3_part_iv_scope_boundary",
            "Cohomological readings in degrees n>=3",
        ),
        (
            "boundary:m8:non-abelian-stack-gerbe-vocabulary",
            "out_of_selected_vocabulary",
            "non_abelian_stack_gerbe_outside_abelian_f2_vocabulary",
            "Non-abelian stack/gerbe degree-2 descent data",
        ),
        (
            "boundary:m8:higher-tor-unmeasured-support",
            "unmeasured_support",
            "higher_tor_i_ge_2_unmeasured_support",
            "Higher Tor_i for i>=2",
        ),
    ] {
        assert!(
            packet["boundaryStatements"].as_array().unwrap().iter().any(
                |statement| statement["id"] == id
                    && statement["kind"] == kind
                    && statement["reason"] == reason_text
                    && statement["scopeRefs"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|scope_ref| scope_ref == packet["packetId"].as_str().unwrap())
                    && statement["text"]
                        .as_str()
                        .is_some_and(|text| text.contains(scope_text))
            ),
            "M8 typed boundary {id} must keep its own kind and scope"
        );
    }
    assert!(
        packet["nonConclusions"]
            .as_array()
            .unwrap()
            .iter()
            .filter_map(Value::as_str)
            .all(|text| {
                !text.contains("Cohomological readings in degrees n>=3")
                    && !text.contains("Non-abelian stack/gerbe degree-2 descent data")
                    && !text.contains("Higher Tor_i")
            }),
        "M8 silence must be a typed boundary, not a nonConclusions headline"
    );
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structuralVerdict is array")
            .len(),
        1,
        "M8 typed boundary must not generate a structural verdict"
    );
    assert!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structuralVerdict is array")
            .iter()
            .all(|row| row["verdictData"]["methodStatus"] != "depends_on_violated_assumption"),
        "M8 typed boundary must not trigger assumption dependency propagation"
    );
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
    assert_eq!(viewer["schema"], "archsig-atom-viewer-data/v0.5.4");
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
fn cli_representative_json_artifacts_omit_absolute_sheaf_cohomology_notation() {
    let base_run = run_analyze_fixture_lock(
        "full-sheaf-output-lint-base",
        "archmap_v2.json",
        "law_policy_ag.json",
        "law_surface_ag_v052.json",
    );
    let head_run = run_analyze_fixture_lock(
        "full-sheaf-output-lint-head",
        "archmap_v2.json",
        "law_policy_ag.json",
        "law_surface_ag_v052.json",
    );

    let comparison_dir = temp_dir("full-sheaf-output-lint-comparison");
    run_sig0(&[
        "compare",
        "--base-run",
        base_run.to_str().expect("base run path is utf-8"),
        "--head-run",
        head_run.to_str().expect("head run path is utf-8"),
        "--out-dir",
        comparison_dir
            .to_str()
            .expect("comparison output path is utf-8"),
    ]);

    let gate_report_path = temp_dir("full-sheaf-output-lint-gate").join("archsig-gate-report.json");
    run_sig0(&[
        "gate",
        "--packet",
        head_run
            .join("archsig-measurement-packet.json")
            .to_str()
            .expect("packet path is utf-8"),
        "--policy",
        ag_measurement_root()
            .join("gate_policy_conservative.json")
            .to_str()
            .expect("gate policy path is utf-8"),
        "--out",
        gate_report_path
            .to_str()
            .expect("gate report path is utf-8"),
    ]);

    let output_surfaces = [
        (
            "measurement packet",
            head_run.join("archsig-measurement-packet.json"),
        ),
        (
            "analysis summary",
            head_run.join("archsig-analysis-summary.json"),
        ),
        (
            "comparison report",
            comparison_dir.join("archsig-comparison-report.json"),
        ),
        ("gate report", gate_report_path),
    ];
    for (surface, path) in output_surfaces {
        let content = fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!(
                "{surface} output must be readable at {}: {error}",
                path.display()
            )
        });
        assert!(
            !has_absolute_sheaf_cohomology_notation(&content),
            "{surface} must not emit absolute H^n(X, ...) sheaf notation"
        );
    }

    let period_run = run_analyze_fixture_lock(
        "full-sheaf-output-lint-period",
        "archmap_v2_period_stokes.json",
        "law_policy_period.json",
        "law_surface_ag_v052.json",
    );
    let period_packet = read_json(&period_run.join("archsig-measurement-packet.json"));
    assert_eq!(period_packet["profile"]["coefficient"], "R");
    let period_m8 = period_packet["boundaryStatements"]
        .as_array()
        .expect("period boundaryStatements is array")
        .iter()
        .filter(|statement| {
            statement["id"]
                .as_str()
                .is_some_and(|id| id.starts_with("boundary:m8:"))
        })
        .collect::<Vec<_>>();
    assert_eq!(period_m8.len(), 2);
    for (id, kind, reason) in [
        (
            "boundary:m8:higher-hn-silence",
            "silence_by_design",
            "higher_hn_n_ge_3_part_iv_scope_boundary",
        ),
        (
            "boundary:m8:higher-tor-unmeasured-support",
            "unmeasured_support",
            "higher_tor_i_ge_2_unmeasured_support",
        ),
    ] {
        let statement = period_m8
            .iter()
            .find(|statement| statement["id"] == id)
            .unwrap_or_else(|| panic!("period M8 boundary {id} is missing"));
        assert_eq!(statement["kind"], kind);
        assert_eq!(statement["reason"], reason);
        assert_eq!(
            statement["scopeRefs"],
            json!([period_packet["packetId"]
                .as_str()
                .expect("packet id is string")])
        );
    }
    assert!(
        period_m8
            .iter()
            .any(|statement| { statement["id"] == "boundary:m8:higher-hn-silence" })
    );
    assert!(
        period_m8
            .iter()
            .any(|statement| { statement["id"] == "boundary:m8:higher-tor-unmeasured-support" })
    );
    assert!(
        !period_m8.iter().any(|statement| {
            statement["id"] == "boundary:m8:non-abelian-stack-gerbe-vocabulary"
        })
    );
    assert!(period_m8.iter().all(|statement| {
        statement["reason"]
            .as_str()
            .is_some_and(|reason| !reason.contains("F2"))
            && statement["text"]
                .as_str()
                .is_some_and(|text| !text.contains("F2"))
    }));

    assert!(has_absolute_sheaf_cohomology_notation("H^1(X, Ob_U)"));
    assert!(has_absolute_sheaf_cohomology_notation("H^n(X, Ob_U)"));
    assert!(!has_absolute_sheaf_cohomology_notation(
        "selected cover H^1"
    ));
    assert!(!has_absolute_sheaf_cohomology_notation("coverRelativeH1"));
}

#[test]
fn cli_r13_two_vertex_circle_nerve_fixture_locks_body_worked_example() {
    let fixture = read_json(&ag_measurement_root().join("circle_nerve_two_vertex_body_v052.json"));
    assert_eq!(fixture["schema"], "ag-circle-nerve-fixture/v0.5.4");
    assert_eq!(fixture["provenance"]["kind"], "body-worked-example");
    assert_eq!(fixture["coefficient"]["ring"], "Z");
    assert_eq!(fixture["coefficient"]["quotient"], "F2");
    assert_eq!(fixture["coefficient"]["ideal"], "(2)");
    assert_eq!(fixture["coefficient"]["oneIsNonzero"], true);
    assert_eq!(fixture["vertices"], json!(["v_minus", "v_plus"]));
    let edges = fixture["edges"].as_array().expect("circle edges");
    assert_eq!(edges.len(), 2);
    assert_eq!(edges[0]["source"], "v_minus");
    assert_eq!(edges[0]["target"], "v_plus");
    assert_eq!(edges[0]["id"], "e_plus");
    assert_eq!(edges[0]["value"], 1);
    assert_eq!(edges[1]["source"], "v_plus");
    assert_eq!(edges[1]["target"], "v_minus");
    assert_eq!(edges[1]["id"], "e_minus");
    assert_eq!(edges[1]["value"], 0);
    assert_eq!(
        edges
            .iter()
            .map(|edge| edge["value"].as_u64().expect("F2 edge value") as u8)
            .fold(0, |sum, value| sum ^ value),
        1,
        "the residual has nonzero reverse-edge parity in F2"
    );
    assert_eq!(fixture["higherSimplices"], json!([]));
    assert_eq!(fixture["expected"]["cocycle"], true);
    assert_eq!(fixture["expected"]["classNonzero"], true);
}

#[test]
fn cli_r9_numeric_locks_preserve_ag_measurement_values_and_verdicts() {
    let pseudo_circle = run_analyze_fixture_lock_with_surface(
        "r9-pseudo-circle-h1",
        "archmap_v2_cech_h1_visible.json",
        "law_policy_cech_h1.json",
        "law_surface_cech_h1_v052.json",
    );
    let pseudo_circle_packet = read_json(&pseudo_circle.join("archsig-measurement-packet.json"));
    assert_eq!(
        pseudo_circle_packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    let pseudo_circle_invariant = invariant_by_id(
        &pseudo_circle_packet,
        "cech-cohomology:profile:ag-default@1",
    );
    assert_eq!(pseudo_circle_invariant["dimensions"]["H1"], 1);
    assert_eq!(pseudo_circle_invariant["coefficient"], "F2");

    let circle_nerve_a = run_analyze_fixture_lock_with_surface(
        "r9-circle-nerve-a",
        "archmap_v2_cech_b8_toy.json",
        "law_policy_cech_b8.json",
        "law_surface_cech_b8_v052.json",
    );
    let circle_nerve_b = run_analyze_fixture_lock_with_surface(
        "r9-circle-nerve-b",
        "archmap_v2_cech_b8_toy.json",
        "law_policy_cech_b8.json",
        "law_surface_cech_b8_v052.json",
    );
    assert_byte_identical_analysis_artifacts(&circle_nerve_a, &circle_nerve_b);
    let circle_nerve_packet = read_json(&circle_nerve_a.join("archsig-measurement-packet.json"));
    assert_eq!(
        circle_nerve_packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    let circle_nerve =
        invariant_by_id(&circle_nerve_packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(circle_nerve["dimensions"]["H1"], 1);
    assert_eq!(circle_nerve["observedCocycle"]["classNonzero"], true);
    assert_eq!(
        circle_nerve["observedCocycle"]["mismatchSupportRefs"],
        json!(["atom:b8-cocycle-P"])
    );

    let square_free = run_analyze_fixture_lock_with_surface(
        "r9-square-free-hitting-sets",
        "archmap_v2_square_free_repair.json",
        "law_policy_square_free.json",
        "law_surface_ag_v052.json",
    );
    let square_free_packet = read_json(&square_free.join("archsig-measurement-packet.json"));
    let square_free_invariant = invariant_by_id(
        &square_free_packet,
        "square-free-repair:profile:ag-square-free@1",
    );
    assert_eq!(
        square_free_invariant["alexanderDualRepair"]["minimalHittingSets"],
        json!([["x_inventory"], ["x_checkout", "x_payment"]]),
    );
    assert_eq!(
        square_free_packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );

    let tor = run_analyze_fixture_lock_with_surface(
        "r9-tor-one",
        "archmap_v2_law_conflict_tor.json",
        "law_policy_tor.json",
        "law_surface_ag_v052.json",
    );
    let tor_packet = read_json(&tor.join("archsig-measurement-packet.json"));
    assert_eq!(
        tor_packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    let tor_invariant = invariant_by_id(
        &tor_packet,
        "law-conflict-tor:profile:ag-law-conflict-tor@1",
    );
    assert_eq!(
        tor_invariant["torByDegree"],
        json!([{
            "degree": 1,
            "classCount": 1,
            "coefficient": "F2",
            "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
        }])
    );
    assert_eq!(tor_invariant["lawConflicts"][0]["degree"], 1);
    assert_eq!(tor_invariant["proxyComparison"]["taylorClassCount"], 1);
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
        root.join("law_policy_cech_h1.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_h1_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.cech-obstruction"
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
        3,
        "fully observed square with three mismatched edges (odd cycle sum) carries the class"
    );
    assert_eq!(cech["observedEdgeCount"], 4);
    assert_eq!(cech["unobservedEdgeRefs"].as_array().map(Vec::len), Some(0));
    assert_eq!(
        cech["observedCocycle"]["mismatchSupportRefs"],
        json!([
            "atom:bottom-cech-section-value",
            "atom:left-cech-section-value",
            "atom:right-cech-section-value",
            "atom:top-cech-section-value"
        ])
    );
    assert_eq!(
        cech["classSupport"]["edgeRefs"],
        json!([
            "ctx:left->ctx:bottom",
            "ctx:right->ctx:bottom",
            "ctx:top->ctx:right"
        ])
    );
    assert_eq!(
        cech["classSupport"]["supportAtomRefs"],
        json!([
            "atom:bottom-cech-section-value",
            "atom:left-cech-section-value",
            "atom:right-cech-section-value",
            "atom:top-cech-section-value"
        ])
    );
    assert_eq!(cech["nerveShape"]["b1"], Value::from(1));
    assert_eq!(cech["nerveShape"]["oneSkeletonB1"], Value::from(1));
    assert_eq!(
        cech["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"],
        false
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["tripleOverlapsEmpty"]["status"],
        "discharged_by_check"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionMapsSurjective"]["status"],
        "not_discharged"
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
    let mut stable_cech_row = packet["structuralVerdict"][0].clone();
    stable_cech_row
        .as_object_mut()
        .expect("structural row is object")
        .remove("dependsOnAssumptions");
    assert_eq!(
        stable_cech_row,
        json!({
            "verdictRef": "structuralVerdict/ag-cech-obstruction/surface-cech-surface-v052/finite-f2-cech-computed",
            "evaluator": "ag.cech-obstruction",
            "law": "surface:cech-surface-v052",
            "target": {
                "kind": "cover-relative-cech-h1-class",
                "coverRef": "cover:order-inventory",
                "coefficient": "F2",
                "scopeSize": {
                    "contexts": 4,
                    "edges": 4,
                    "triangles": 0
                },
                "classRef": "computedInvariants/cech-cohomology:profile:ag-default@1"
            },
            "verdict": "measured_nonzero",
            "verdictData": {
                "inScope": true,
                "zero": false,
                "nonZero": true,
                "methodStatus": "finite_f2_cech_computed",
                "certRef": "computedInvariants/cech-cohomology:profile:ag-default@1"
            },
            "evidence": {
                "computedInvariantRefs": ["cech-cohomology:profile:ag-default@1"],
                "sourceRefs": [
                    "ctx:bottom",
                    "ctx:left",
                    "ctx:right",
                    "ctx:top",
                    "src:bottom",
                    "src:cover",
                    "src:left",
                    "src:right",
                    "src:top"
                ]
            },
            "reason": "finite F2 Cech 1-cocycle is not a coboundary on the selected cover"
        }),
        "ledger transparency must keep the Cech structural verdict payload stable apart from the v0.5.4 target/evidence additions"
    );
    let cech_fixture_path = "input:archmap_v2_cech_h1_visible.json";
    let computed_without_capacity = Value::Array(
        packet["computedInvariants"]
            .as_array()
            .expect("computedInvariants is array")
            .iter()
            .filter(|row| row["invariantId"] != "topological-debt-capacity:profile:ag-default@1")
            .map(|row| {
                let mut row = row.clone();
                let object = row.as_object_mut().expect("computed invariant is object");
                assert!(
                    object.contains_key("kind")
                        && object.contains_key("value")
                        && object.contains_key("representation"),
                    "computed invariant must expose measurement packet typed invariant fields"
                );
                object.remove("kind");
                object.remove("value");
                object.remove("representation");
                row
            })
            .collect(),
    );
    assert_eq!(
        computed_without_capacity,
        json!([
            {
                "archmapRef": cech_fixture_path,
                "atomCount": 8,
                "contextCount": 4,
                "coverCount": 1,
                "doctrineFingerprint": "sha256:aat-canonical-doctrine-schema052",
                "invariantId": "finite-poset-site-shape",
                "evaluator": "ag.foundation"
            },
            {
                "claimScope": "selected-cover 1-skeleton Cech cochain calculation",
                "coefficient": "F2",
                "contextCount": 4,
                "coverNerveProjection": {
                    "coverRef": "cover:order-inventory",
                    "edges": [
                        {
                            "edgeId": "ctx:left->ctx:bottom",
                            "objectKind": "nerveEdge",
                            "sectionObservation": "observed",
                            "source": "selected cover restriction edge",
                            "sourceContextRef": "ctx:left",
                            "supportAtomRefs": ["atom:bottom-cech-section-value", "atom:left-cech-section-value"],
                            "targetContextRef": "ctx:bottom",
                            "value": 1
                        },
                        {
                            "edgeId": "ctx:right->ctx:bottom",
                            "objectKind": "nerveEdge",
                            "sectionObservation": "observed",
                            "source": "selected cover restriction edge",
                            "sourceContextRef": "ctx:right",
                            "supportAtomRefs": ["atom:bottom-cech-section-value", "atom:right-cech-section-value"],
                            "targetContextRef": "ctx:bottom",
                            "value": 1
                        },
                        {
                            "edgeId": "ctx:top->ctx:left",
                            "objectKind": "nerveEdge",
                            "sectionObservation": "observed",
                            "source": "selected cover restriction edge",
                            "sourceContextRef": "ctx:top",
                            "supportAtomRefs": [],
                            "targetContextRef": "ctx:left",
                            "value": 0
                        },
                        {
                            "edgeId": "ctx:top->ctx:right",
                            "objectKind": "nerveEdge",
                            "sectionObservation": "observed",
                            "source": "selected cover restriction edge",
                            "sourceContextRef": "ctx:top",
                            "supportAtomRefs": ["atom:right-cech-section-value", "atom:top-cech-section-value"],
                            "targetContextRef": "ctx:right",
                            "value": 1
                        }
                    ],
                    "faceSource": "selected cover triple-overlap sharedAtomRefs recorded in archsig-measurement-packet/v0.5.4; not inferred by the viewer",
                    "faces": [],
                    "h2CoherenceVisualized": false,
                    "vertices": [
                        {
                            "atomRefs": ["atom:bottom", "atom:bottom-cech-section-value"],
                            "contextRef": "ctx:bottom",
                            "objectKind": "nerveVertex"
                        },
                        {
                            "atomRefs": ["atom:left", "atom:left-cech-section-value"],
                            "contextRef": "ctx:left",
                            "objectKind": "nerveVertex"
                        },
                        {
                            "atomRefs": ["atom:right", "atom:right-cech-section-value"],
                            "contextRef": "ctx:right",
                            "objectKind": "nerveVertex"
                        },
                        {
                            "atomRefs": ["atom:top", "atom:top-cech-section-value"],
                            "contextRef": "ctx:top",
                            "objectKind": "nerveVertex"
                        }
                    ]
                },
                "dimensions": {
                    "H0": 1,
                    "H1": 1
                },
                "evaluator": "ag.cech-obstruction",
                "invariantId": "cech-cohomology:profile:ag-default@1",
                "method": "finite-f2-incidence-graph-cochain@1",
                "methodStatus": "finite_f2_cech_computed",
                "observedEdgeCount": 4,
                "unobservedEdgeRefs": [],
                "observedCocycle": {
                    "classNonzero": true,
                    "mismatchSupportRefs": [
                        "atom:bottom-cech-section-value",
                        "atom:left-cech-section-value",
                        "atom:right-cech-section-value",
                        "atom:top-cech-section-value"
                    ],
                    "representative": [
                        {
                            "edge": "ctx:left->ctx:bottom",
                            "sourceContext": "ctx:left",
                            "supportAtomRefs": ["atom:bottom-cech-section-value", "atom:left-cech-section-value"],
                            "targetContext": "ctx:bottom",
                            "value": 1
                        },
                        {
                            "edge": "ctx:right->ctx:bottom",
                            "sourceContext": "ctx:right",
                            "supportAtomRefs": ["atom:bottom-cech-section-value", "atom:right-cech-section-value"],
                            "targetContext": "ctx:bottom",
                            "value": 1
                        },
                        {
                            "edge": "ctx:top->ctx:right",
                            "sourceContext": "ctx:top",
                            "supportAtomRefs": ["atom:right-cech-section-value", "atom:top-cech-section-value"],
                            "targetContext": "ctx:right",
                            "value": 1
                        }
                    ]
                },
                "classSupport": {
                    "kind": "selected-cover-edge-support",
                    "edgeRefs": [
                        "ctx:left->ctx:bottom",
                        "ctx:right->ctx:bottom",
                        "ctx:top->ctx:right"
                    ],
                    "supportAtomRefs": [
                        "atom:bottom-cech-section-value",
                        "atom:left-cech-section-value",
                        "atom:right-cech-section-value",
                        "atom:top-cech-section-value"
                    ]
                },
                "nerveShape": {
                    "b1": 1,
                    "oneSkeletonB1": 1,
                    "capacityLowerBound": 0,
                    "isForest": false,
                    "eulerCharacteristic": 0
                },
                "theorem12_4Discharge": {
                    "theoremRef": "part4/12.4",
                    "isForest": {
                        "holds": false,
                        "status": "not_discharged",
                        "checkedBy": Value::Null
                    },
                    "tripleOverlapsEmpty": {
                        "holds": true,
                        "status": "discharged_by_check",
                        "checkedBy": "selected cover has no projected triple-overlap faces"
                    },
                    "restrictionMapsSurjective": {
                        "holds": false,
                        "status": "not_discharged",
                        "checkedBy": Value::Null
                    },
                    "restrictionSurjectivityWitnesses": [],
                    "coverShapeExcludesGluingObstruction": false,
                    "conclusionCode": Value::Null
                },
                "boundaryNote": "COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION is relative to the selected abelian coefficient sheaf; non-abelian torsor, stacky descent, and gerbe obstructions are not excluded.",
                "rankD0": 3,
                "reason": "selected cover has a non-empty Cech 1-skeleton for ag.cech-obstruction",
                "restrictionEdgeCount": 4,
                "selectedCoverRef": "cover:order-inventory",
                "selectedH2": {
                    "dimension": 0,
                    "reason": "no selected 2-simplices are present in the finite incidence graph complex",
                    "status": "computed_for_selected_1_skeleton"
                },
                "status": "computed"
            }
        ]),
        "ledger transparency must not change computed invariants for the same Cech input"
    );
    assert_eq!(
        packet["suppliedData"],
        json!([
            {
                "suppliedId": "supplied:archmap",
                "kind": "archmap",
                "sourceArtifactRef": "input:archmap_v2_cech_h1_visible.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "archmap/v0.5.4-validation",
                    "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
                }
            },
            {
                "suppliedId": "supplied:law-policy",
                "kind": "law-policy",
                "sourceArtifactRef": "input:law_policy_cech_h1.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "law-policy/v0.5.4-validation",
                    "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
                }
            },
            {
                "suppliedId": "supplied:measurement-profile",
                "kind": "measurement-profile",
                "sourceArtifactRef": "input:measurement_profile_ag.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "measurement-profile/v0.5.4-validation",
                    "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
                }
            },
            {
                "suppliedId": "supplied:law-surface",
                "kind": "law-equation-surface",
                "sourceArtifactRef": "input:law_surface_cech_h1_v052.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "law-equation-surface/v0.5.4-validation",
                    "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
                }
            }
        ]),
        "measurement packet must carry non-empty suppliedData ledger for all supplied input artifacts"
    );
    let capacity = invariant_by_id(&packet, "topological-debt-capacity:profile:ag-default@1");
    assert_eq!(capacity["evaluator"], "ag.cech-obstruction");
    assert_eq!(capacity["status"], "computed");
    assert_eq!(capacity["structuralVerdictRef"], Value::Null);
    assert_eq!(capacity["dimensions"]["dimC0"], Value::from(4));
    assert_eq!(capacity["dimensions"]["dimC1"], Value::from(4));
    assert_eq!(capacity["dimensions"]["dimC2"], Value::from(0));
    assert_eq!(capacity["capacityLowerBound"], Value::from(0));
    assert_eq!(capacity["eulerCharacteristic"], Value::from(0));
    assert_eq!(capacity["b1NerveReading"]["oneSkeletonB1"], Value::from(1));
    assert_eq!(capacity["b1NerveReading"]["nerveComplexB1"], Value::from(1));
    assert_eq!(
        capacity["measuredCechVerdictEcho"]["h1ClassNonzero"],
        Value::Bool(true)
    );
    assert!(
        capacity["b1NerveReading"]["nonClaim"]
            .as_str()
            .is_some_and(|text| text.contains("not concrete H1 class existence claims")),
        "capacity reading must not claim concrete H1 class existence"
    );
    assert!(
        capacity["boundaryNote"]
            .as_str()
            .is_some_and(|text| text.contains("Part IV principle 11.3")),
        "cohomological non-claim boundary must be scoped to Part IV"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part4/12.3"
                    && entry["assumption"] == "constant coefficient nerve b1 comparison"
                    && entry["status"] == "checked"
            }),
        "b1 nerve reading must be relative to a checked constant coefficient assumption"
    );
    assert_eq!(
        packet["analyticReadings"],
        json!([
            {
                "readingId": "candidate-regime:stability-placeholder",
                "evaluator": "ag.foundation",
                "claimStatus": "candidate",
                "fidelity": "proxy",
                "value": {
                    "reason": "theorem-candidate readings are analytic-only until a follow-up evaluator computes them",
                    "state": "not_evaluated"
                },
                "regime": "theorem-candidate",
                "structuralVerdictRef": Value::Null
            }
        ]),
        "ledger transparency must not change analytic readings for the same Cech input"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part4/12.4"
                    && entry["assumption"]
                        == "selected Cech nerve is a forest with no triple-overlap faces"
                    && entry["status"] == "assumed"
            }),
        "cycle/no-triple Cech nerve must not check the theorem 12.4 forest premise"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part4/12.4"
                    && entry["assumption"] == "restriction maps are surjective"
                    && entry["status"] == "assumed"
            }),
        "surjective restriction must remain assumed even when other structural premises are visible"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    );
}
