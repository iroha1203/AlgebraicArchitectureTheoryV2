fn run_cech_h1_analyze(case_id: &str, archmap: Value) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    let archmap_path = out_dir.join("archmap.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("cech archmap serializes"),
    )
    .expect("cech archmap writes");
    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
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
    out_dir
}

fn strip_cech_section_atoms(archmap: &mut Value, subjects: &[&str]) {
    let removed = archmap["atoms"]
        .as_array()
        .expect("atoms are array")
        .iter()
        .filter(|atom| {
            atom["predicate"] == "sectionValue"
                && atom["subject"]
                    .as_str()
                    .is_some_and(|subject| subjects.contains(&subject))
        })
        .map(|atom| atom["id"].as_str().expect("atom id").to_string())
        .collect::<BTreeSet<_>>();
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms are array")
        .retain(|atom| !atom["id"].as_str().is_some_and(|id| removed.contains(id)));
    for context in archmap["contexts"].as_array_mut().expect("contexts") {
        context["atoms"]
            .as_array_mut()
            .expect("context atoms")
            .retain(|atom| !atom.as_str().is_some_and(|id| removed.contains(id)));
    }
}

#[test]
fn cli_analyze_v2_cech_all_sections_unobserved_is_silence_not_measured_zero() {
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    strip_cech_section_atoms(
        &mut archmap,
        &["ctx:top", "ctx:left", "ctx:right", "ctx:bottom"],
    );
    let out_dir = run_cech_h1_analyze("ag-cech-all-sections-unobserved", archmap);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let row = &packet["structuralVerdict"][0];
    assert_eq!(row["evaluator"], "ag.cech-obstruction");
    assert_eq!(row["verdict"], "not_computed");
    assert_eq!(row["verdictData"]["methodStatus"], "sections_not_observed");
    assert_eq!(row["verdictData"]["zero"], false);
    assert_eq!(
        row["target"]["scopeSize"],
        json!({"contexts": 0, "edges": 0, "triangles": 0}),
        "unmeasured cech row must not claim a positive measured scope"
    );
    let invariant = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["observedEdgeCount"], 0);
    assert_eq!(
        invariant["unobservedEdgeRefs"].as_array().map(Vec::len),
        Some(4)
    );
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .is_some_and(|rows| rows.iter().any(|statement| {
                statement["kind"] == "silence_by_design"
                    && statement["reason"] == "sections_not_observed"
                    && statement["text"]
                        .as_str()
                        .is_some_and(|text| text.contains("supply section observations"))
            })),
        "all-unobserved cech run must carry a silence_by_design boundary with whatNext"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"], "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE",
        "no NO_MEASURED_H1 conclusion may be drawn from unobserved sections"
    );
}

#[test]
fn cli_analyze_v2_cech_partially_observed_edges_measure_observed_and_stay_silent_elsewhere() {
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    strip_cech_section_atoms(&mut archmap, &["ctx:top", "ctx:right"]);
    let out_dir = run_cech_h1_analyze("ag-cech-partially-observed", archmap);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let row = &packet["structuralVerdict"][0];
    assert_eq!(row["evaluator"], "ag.cech-obstruction");
    assert_eq!(
        row["verdict"], "measured_zero",
        "a single observed mismatch edge extends to a coboundary; the old nonzero relied on unobserved zeros"
    );
    let invariant = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(invariant["observedEdgeCount"], 1);
    let unobserved = invariant["unobservedEdgeRefs"]
        .as_array()
        .expect("unobserved edge refs");
    assert_eq!(unobserved.len(), 3);
    let silence = packet["boundaryStatements"]
        .as_array()
        .expect("boundary statements")
        .iter()
        .find(|statement| statement["reason"] == "sections_not_observed_on_selected_edges")
        .expect("partial observation must emit an unobserved-edges silence statement");
    assert_eq!(silence["kind"], "silence_by_design");
    for edge in unobserved {
        let edge = edge.as_str().expect("edge id");
        assert!(
            silence["text"]
                .as_str()
                .is_some_and(|text| text.contains(edge)),
            "silence text must list unobserved edge {edge}"
        );
    }
    assert!(
        silence["scopeRefs"]
            .as_array()
            .is_some_and(|refs| refs.iter().any(|scope| scope == &row["verdictRef"])),
        "measured_zero row must be qualified by the unobserved-edges silence"
    );
}

#[test]
fn cli_analyze_v2_cech_effectivity_ledger_checks_forest_no_triple_only() {
    let out_dir = temp_dir("ag-measurement-cech-effectivity-ledger");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    let right_context = archmap["contexts"]
        .as_array_mut()
        .expect("contexts is array")
        .iter_mut()
        .find(|context| context["id"] == "ctx:right")
        .expect("right context exists");
    right_context["restrictsTo"] = json!([]);
    let bottom_section_value = archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .iter_mut()
        .find(|atom| atom["id"] == "atom:bottom-cech-section-value")
        .expect("bottom section value atom exists");
    bottom_section_value["object"] = json!("section=left-local");
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .extend([
            json!({
                "id": "atom:surj-top-left",
                "kind": "semantic",
                "subject": "ctx:top->ctx:left",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
            json!({
                "id": "atom:surj-top-right",
                "kind": "semantic",
                "subject": "ctx:top->ctx:right",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
            json!({
                "id": "atom:surj-left-bottom",
                "kind": "semantic",
                "subject": "ctx:left->ctx:bottom",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
        ]);
    let archmap_path = out_dir.join("archmap_v2_cech_forest_no_triple.json");
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
        root.join("law_policy_cech_forest.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_forest_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let cech_row = &packet["structuralVerdict"][0];
    assert_eq!(cech_row["evaluator"], "ag.cech-obstruction");
    assert_eq!(
        cech_row["verdict"], "measured_zero",
        "ledger transparency must not change the Cech verdict calculation"
    );
    assert_eq!(cech_row["verdictData"]["zero"], true);
    assert_eq!(
        cech_row["verdictData"]["methodStatus"],
        "finite_f2_cech_computed"
    );
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(cech["dimensions"]["H1"], Value::from(0));
    assert_eq!(cech["observedCocycle"]["classNonzero"], false);
    assert!(
        cech["coverNerveProjection"]["faces"]
            .as_array()
            .is_some_and(Vec::is_empty),
        "forest/no-triple fixture must have no projected triple-overlap face"
    );

    let assumptions = packet["assumptions"].as_array().unwrap();
    for assumption in [
        "local lawful sections form an effective Ob_U-torsor",
        "local adjustment action is fixed and effective",
        "coefficient object satisfies descent",
    ] {
        assert!(
            assumptions.iter().any(|entry| {
                entry["theoremRef"] == "part4/11.1"
                    && entry["assumption"] == assumption
                    && entry["status"] == "assumed"
            }),
            "theorem 11.1 premise must be visible in the CBI ledger: {assumption}"
        );
    }
    assert!(
        assumptions.iter().any(|entry| {
            entry["theoremRef"] == "part4/12.4"
                && entry["assumption"] == "restriction maps are surjective"
                && entry["status"] == "checked"
        }),
        "surjective restriction must be discharged by the finite selected restriction check"
    );
    assert!(
        assumptions.iter().any(|entry| {
            entry["theoremRef"] == "part4/12.4"
                && entry["assumption"]
                    == "selected Cech nerve is a forest with no triple-overlap faces"
                && entry["status"] == "checked"
        }),
        "forest/no-triple structural premise must be checked from the selected cover nerve"
    );
    assert_eq!(cech["nerveShape"]["isForest"], true);
    assert_eq!(cech["nerveShape"]["b1"], Value::from(0));
    assert_eq!(
        cech["theorem12_4Discharge"]["isForest"]["status"],
        "discharged_by_check"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["tripleOverlapsEmpty"]["status"],
        "discharged_by_check"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionMapsSurjective"]["status"],
        "discharged_by_check"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionSurjectivityWitnesses"]
            .as_array()
            .expect("restriction witnesses are array")
            .len(),
        3
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"],
        true
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["conclusionCode"],
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
    );
    assert!(
        cech["boundaryNote"].as_str().is_some_and(|text| {
            text.contains("non-abelian torsor")
                && text.contains("stacky descent")
                && text.contains("gerbe obstructions")
        }),
        "cover-shape exclusion must keep the non-abelian boundary visible"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
    );
    assert!(
        summary["readThisFirst"]["whatItMeans"]
            .as_str()
            .is_some_and(|text| text.contains("restriction-surjectivity witnesses"))
    );
    assert!(
        summary["readThisFirst"]["boundary"]
            .as_str()
            .is_some_and(|text| text.contains("Non-abelian torsor"))
    );
}

#[test]
fn cli_analyze_v2_cech_surjectivity_witness_requires_edge_coverage() {
    let out_dir = temp_dir("ag-measurement-cech-surjectivity-coverage");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    let right_context = archmap["contexts"]
        .as_array_mut()
        .expect("contexts is array")
        .iter_mut()
        .find(|context| context["id"] == "ctx:right")
        .expect("right context exists");
    right_context["restrictsTo"] = json!([]);
    let bottom_section_value = archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .iter_mut()
        .find(|atom| atom["id"] == "atom:bottom-cech-section-value")
        .expect("bottom section value atom exists");
    bottom_section_value["object"] = json!("section=left-local");
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .extend([
            json!({
                "id": "atom:surj-top-left",
                "kind": "semantic",
                "subject": "ctx:top->ctx:left",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
            json!({
                "id": "atom:surj-top-left-duplicate",
                "kind": "semantic",
                "subject": "ctx:top->ctx:left",
                "object": "finite-preimage-witness-duplicate",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
            json!({
                "id": "atom:surj-left-bottom",
                "kind": "semantic",
                "subject": "ctx:left->ctx:bottom",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
        ]);
    let archmap_path = out_dir.join("archmap_v2_cech_duplicate_surj_witness.json");
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
        root.join("law_policy_cech_forest.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_forest_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionSurjectivityWitnesses"]
            .as_array()
            .expect("restriction witnesses are array")
            .len(),
        2,
        "only canonical finite-preimage witnesses are admitted"
    );
    assert!(
        cech["theorem12_4Discharge"]["restrictionSurjectivityWitnesses"]
            .as_array()
            .expect("restriction witnesses are array")
            .iter()
            .all(|witness| witness["witnessObject"] == "finite-preimage-witness"),
        "a non-canonical witness object must not enter the checked witness set"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionMapsSurjective"]["status"], "not_discharged",
        "witness count alone must not discharge missing selected edge coverage"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"],
        false
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_ne!(
        summary["conclusion"],
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
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
            "path": "docs/tool/ag_measurement_input_contract.md",
            "section": "B.8.2"
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
    let incomplete_dir = out_dir.join("incomplete-boundary-face");
    fs::create_dir_all(&incomplete_dir).expect("incomplete face dir exists");
    let incomplete_archmap_path = incomplete_dir.join("archmap_v2_cech_triple_overlap.json");
    fs::write(
        &incomplete_archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("incomplete face archmap fixture can be written");
    run_sig0(&[
        "analyze",
        "--archmap",
        incomplete_archmap_path.to_str().expect("path is utf-8"),
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
        incomplete_dir.to_str().expect("path is utf-8"),
    ]);
    let incomplete_packet = read_json(&incomplete_dir.join("archsig-measurement-packet.json"));
    let incomplete_capacity = invariant_by_id(
        &incomplete_packet,
        "topological-debt-capacity:profile:ag-default@1",
    );
    assert_eq!(incomplete_capacity["dimensions"]["dimC1"], Value::from(4));
    assert_eq!(incomplete_capacity["dimensions"]["dimC2"], Value::from(1));
    assert_eq!(
        incomplete_capacity["b1NerveReading"]["oneSkeletonB1"],
        Value::from(1)
    );
    assert_eq!(
        incomplete_capacity["b1NerveReading"]["nerveComplexB1"],
        Value::from(1),
        "incomplete projected face boundary must not silently add missing selected C1 edges"
    );
    let top_context = archmap["contexts"]
        .as_array_mut()
        .expect("contexts is array")
        .iter_mut()
        .find(|context| context["id"] == "ctx:top")
        .expect("ctx:top exists");
    top_context["restrictsTo"]
        .as_array_mut()
        .expect("ctx:top restrictsTo is array")
        .push(Value::String("ctx:bottom".to_string()));
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
        root.join("law_policy_cech_positive_capacity.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_positive_capacity_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structuralVerdict is array")
            .iter()
            .filter(|row| row["evaluator"] == "ag.cech-obstruction")
            .count(),
        1,
        "Topological Debt Capacity must not add a structural verdict row"
    );
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    let cech_row = packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array")
        .iter()
        .find(|row| row["evaluator"] == "ag.cech-obstruction")
        .expect("Cech structural verdict is present");
    assert_eq!(cech_row["verdict"], "not_computed");
    assert_eq!(
        cech_row["verdictData"]["methodStatus"],
        "triple_overlap_faces_unmeasured"
    );
    assert_eq!(
        cech_row["verdictData"]["zero"],
        false,
        "a selected triple-overlap face must not be reported as a measured zero"
    );
    assert_eq!(cech_row["verdictData"]["nonZero"], false);
    assert_eq!(cech["status"], "not_computed");
    assert_eq!(cech["methodStatus"], "triple_overlap_faces_unmeasured");
    assert_eq!(cech["observedCocycle"]["classNonzero"], false);
    assert_eq!(cech_row["verdictData"]["certRef"], Value::Null);
    let faces = cech["coverNerveProjection"]["faces"]
        .as_array()
        .expect("cover nerve faces are array");
    assert_eq!(
        cech["theorem12_4Discharge"]["tripleOverlapsEmpty"]["status"],
        "not_discharged"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"],
        false
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_ne!(
        summary["conclusion"],
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
    );
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
        "selected cover triple-overlap sharedAtomRefs recorded in archsig-measurement-packet/v0.5.4; not inferred by the viewer"
    );
    let capacity = invariant_by_id(&packet, "topological-debt-capacity:profile:ag-default@1");
    assert_eq!(
        capacity["structuralVerdictRef"],
        Value::Null,
        "Topological Debt Capacity must remain a computedInvariant reading"
    );
    assert_eq!(capacity["dimensions"]["dimC0"], Value::from(4));
    assert_eq!(capacity["dimensions"]["dimC1"], Value::from(5));
    assert_eq!(capacity["dimensions"]["dimC2"], Value::from(1));
    assert_eq!(capacity["capacityLowerBound"], Value::from(0));
    assert_eq!(capacity["eulerCharacteristic"], Value::from(0));
    assert_eq!(
        capacity["b1NerveReading"]["oneSkeletonB1"],
        Value::from(2),
        "extra top-bottom edge creates an additional graph cycle before the selected 2-face is quotiented"
    );
    assert_eq!(
        capacity["b1NerveReading"]["nerveComplexB1"],
        Value::from(1),
        "selected triple-overlap face must fill one graph cycle in the nerve complex reading"
    );
    assert!(
        capacity["b1NerveReading"]["distinction"]
            .as_str()
            .is_some_and(|text| text.contains("oneSkeletonB1 counts graph cycles")),
        "b1 reading must label the graph-vs-complex distinction"
    );
    assert_eq!(cech["coverNerveProjection"]["h2CoherenceVisualized"], false);
    assert_eq!(cech["selectedH2"]["dimension"], Value::Null);
    assert_eq!(
        cech["selectedH2"]["status"],
        "not_measured_for_triple_overlap_faces"
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
        "triple-overlap faces keep theorem 12.4 forest/no-triple premise assumed"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part8/B.8.2-triple-overlap-faces"
                    && entry["assumption"]
                        == "selected graph-only Cech H1 calculation has no triple-overlap faces"
                    && entry["status"] == "violated"
            }),
        "a triple-overlap face must block the graph-only Cech H1 measurement"
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
        "surjective restriction must remain assumed even when triple-overlap faces are present"
    );
}

#[test]
fn cli_analyze_v2_restriction_compatibility_measures_support_inclusion() {
    let root_out = temp_dir("ag-measurement-restriction-compatibility");

    let zero_dir = root_out.join("zero");
    fs::create_dir_all(&zero_dir).expect("zero dir exists");
    let zero_archmap = zero_dir.join("archmap.json");
    let zero_policy = zero_dir.join("law_policy.json");
    fs::write(
        &zero_archmap,
        serde_json::to_vec_pretty(&restriction_archmap("compatible")).expect("archmap serializes"),
    )
    .expect("zero archmap is written");
    write_test_policy_and_profile(&zero_policy, restriction_policy(), restriction_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        zero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_dir.to_str().unwrap(),
    ]);
    let zero_packet = read_json(&zero_dir.join("archsig-measurement-packet.json"));
    let zero_row = restriction_row(&zero_packet);
    assert_eq!(zero_row["verdict"], "measured_zero");
    assert_eq!(zero_row["verdictData"]["zero"], true);
    assert_eq!(
        zero_row["verdictData"]["methodStatus"],
        "finite_support_inclusion_computed"
    );
    let zero_invariant = invariant_by_id(
        &zero_packet,
        "restriction-compatibility:profile:ag-restriction@1",
    );
    assert_eq!(zero_invariant["method"], "finite-support-inclusion@1");
    assert_eq!(zero_invariant["edgeChecks"][0]["status"], "compatible");
    assert!(
        zero_packet["assumptions"]
            .as_array()
            .expect("restriction assumptions are array")
            .iter()
            .any(|row| {
                row["theoremRef"] == "archsig-contract:ag-restriction-compatibility"
                    && row["status"] == "checked"
            }),
        "restriction compatibility contract ID must be emitted and checked"
    );

    let nonzero_dir = root_out.join("nonzero");
    fs::create_dir_all(&nonzero_dir).expect("nonzero dir exists");
    let nonzero_archmap = nonzero_dir.join("archmap.json");
    let nonzero_policy = nonzero_dir.join("law_policy.json");
    fs::write(
        &nonzero_archmap,
        serde_json::to_vec_pretty(&restriction_archmap("violated")).expect("archmap serializes"),
    )
    .expect("nonzero archmap is written");
    write_test_policy_and_profile(&nonzero_policy, restriction_policy(), restriction_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        nonzero_archmap.to_str().unwrap(),
        "--law-policy",
        nonzero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(nonzero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        nonzero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        nonzero_dir.to_str().unwrap(),
    ]);
    let nonzero_packet = read_json(&nonzero_dir.join("archsig-measurement-packet.json"));
    let nonzero_row = restriction_row(&nonzero_packet);
    assert_eq!(nonzero_row["verdict"], "measured_nonzero");
    assert_eq!(nonzero_row["verdictData"]["nonZero"], true);
    let nonzero_invariant = invariant_by_id(
        &nonzero_packet,
        "restriction-compatibility:profile:ag-restriction@1",
    );
    assert_eq!(nonzero_invariant["edgeChecks"][0]["status"], "violated");
    assert_eq!(
        nonzero_invariant["edgeChecks"][0]["violations"][0]["generatorRef"],
        "atom:gen-source-x"
    );
    assert!(
        nonzero_invariant["edgeChecks"][0]["violations"][0]["sourceRefs"]
            .as_array()
            .unwrap()
            .iter()
            .any(|source_ref| source_ref == "src:source-generator"),
        "violated edge must carry source refs"
    );
    assert!(
        nonzero_invariant["boundaryNote"].as_str().is_some_and(
            |note| note.contains("sheaf image 再定義で消えうる、理論対象の defect ではない")
        ),
        "presentation-relative boundary must be explicit"
    );
    assert!(
        nonzero_packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| matches!(
                row["verdict"].as_str().unwrap(),
                "measured_zero" | "measured_nonzero" | "unmeasured" | "unknown" | "not_computed"
            )),
        "restriction evaluator must reuse the existing five verdict values"
    );

    let missing_dir = root_out.join("missing");
    fs::create_dir_all(&missing_dir).expect("missing dir exists");
    let missing_archmap = missing_dir.join("archmap.json");
    let missing_policy = missing_dir.join("law_policy.json");
    fs::write(
        &missing_archmap,
        serde_json::to_vec_pretty(&restriction_archmap("missing-target"))
            .expect("archmap serializes"),
    )
    .expect("missing archmap is written");
    write_test_policy_and_profile(&missing_policy, restriction_policy(), restriction_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        missing_archmap.to_str().unwrap(),
        "--law-policy",
        missing_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(missing_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        missing_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        missing_dir.to_str().unwrap(),
    ]);
    let missing_packet = read_json(&missing_dir.join("archsig-measurement-packet.json"));
    let missing_row = restriction_row(&missing_packet);
    assert_eq!(missing_row["verdict"], "not_computed");
    assert_eq!(
        missing_row["verdictData"]["methodStatus"],
        "restriction_generator_missing"
    );

    let empty_dir = root_out.join("empty");
    fs::create_dir_all(&empty_dir).expect("empty dir exists");
    let empty_archmap = empty_dir.join("archmap.json");
    let empty_policy = empty_dir.join("law_policy.json");
    fs::write(
        &empty_archmap,
        serde_json::to_vec_pretty(&restriction_archmap("empty-edges")).expect("archmap serializes"),
    )
    .expect("empty archmap is written");
    write_test_policy_and_profile(&empty_policy, restriction_policy(), restriction_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        empty_archmap.to_str().unwrap(),
        "--law-policy",
        empty_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(empty_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        empty_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        empty_dir.to_str().unwrap(),
    ]);
    let empty_packet = read_json(&empty_dir.join("archsig-measurement-packet.json"));
    let empty_row = restriction_row(&empty_packet);
    assert_eq!(empty_row["verdict"], "not_computed");
    assert_eq!(
        empty_row["verdictData"]["methodStatus"],
        "empty_selected_restriction_edges"
    );

    let bad_profile_dir = root_out.join("bad-profile");
    fs::create_dir_all(&bad_profile_dir).expect("bad profile dir exists");
    let bad_policy = bad_profile_dir.join("law_policy.json");
    let mut profile = restriction_profile();
    profile["effCoeff"] = Value::String("finite-linear-algebra@1".to_string());
    write_test_policy_and_profile(&bad_policy, restriction_policy(), profile);
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            zero_archmap.to_str().unwrap(),
            "--law-policy",
            bad_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(bad_policy.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            bad_profile_dir.to_str().unwrap(),
        ],
        2,
    );

    let missing_witness_family_dir = root_out.join("missing-witness-family");
    fs::create_dir_all(&missing_witness_family_dir).expect("missing witness family dir exists");
    let missing_witness_family_policy = missing_witness_family_dir.join("law_policy.json");
    let profile = section_profile();
    write_test_policy_and_profile(&missing_witness_family_policy, section_policy(), profile);
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            zero_archmap.to_str().unwrap(),
            "--law-policy",
            missing_witness_family_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                missing_witness_family_policy.to_str().unwrap(),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            missing_witness_family_dir.to_str().unwrap(),
        ],
        2,
    );

    for (case, assignment) in [
        ("missing-equals", "x"),
        ("unknown-variable", "z=1"),
        ("non-boolean", "x=maybe"),
        ("duplicate-variable", "x=1,x=0"),
        ("empty-assignment", ""),
    ] {
        let malformed_dir = root_out.join(format!("malformed-{case}"));
        fs::create_dir_all(&malformed_dir).expect("malformed dir exists");
        let malformed_archmap = malformed_dir.join("archmap.json");
        let malformed_policy = malformed_dir.join("law_policy.json");
        let mut archmap = section_archmap("lawful");
        archmap["atoms"][2]["object"] = Value::String(assignment.to_string());
        fs::write(
            &malformed_archmap,
            serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
        )
        .expect("malformed archmap is written");
        write_test_policy_and_profile(&malformed_policy, section_policy(), section_profile());
        run_sig0_expect_code(
            &[
                "analyze",
                "--archmap",
                malformed_archmap.to_str().unwrap(),
                "--law-policy",
                malformed_policy.to_str().unwrap(),
                "--measurement-profile",
                test_measurement_profile_path(Path::new(malformed_policy.to_str().unwrap()))
                    .to_str()
                    .expect("path is utf-8"),
                "--out-dir",
                malformed_dir.to_str().unwrap(),
            ],
            2,
        );
    }
}

#[test]
fn cli_analyze_v2_boundary_residue_measures_mayer_vietoris_d0() {
    let root_out = temp_dir("ag-measurement-boundary-residue");

    let zero_dir = root_out.join("zero");
    fs::create_dir_all(&zero_dir).expect("zero dir exists");
    let zero_archmap = zero_dir.join("archmap.json");
    let zero_policy = zero_dir.join("law_policy.json");
    fs::write(
        &zero_archmap,
        serde_json::to_vec_pretty(&boundary_residue_archmap("zero")).expect("archmap serializes"),
    )
    .expect("zero archmap is written");
    write_test_policy_and_profile(
        &zero_policy,
        boundary_residue_policy(),
        boundary_residue_profile(),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        zero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_dir.to_str().unwrap(),
    ]);
    let zero_packet = read_json(&zero_dir.join("archsig-measurement-packet.json"));
    let zero_row = boundary_residue_row(&zero_packet);
    assert_eq!(zero_row["verdict"], "measured_zero");
    assert_eq!(zero_row["verdictData"]["zero"], true);
    assert_eq!(
        zero_row["verdictData"]["methodStatus"],
        "finite_mayer_vietoris_d0_computed"
    );
    let zero_invariant = invariant_by_id(
        &zero_packet,
        "boundary-residue:profile:ag-boundary-residue@1",
    );
    assert_eq!(zero_invariant["method"], "finite-mayer-vietoris-d0@1");
    assert_eq!(zero_invariant["imageMembership"], true);
    assert_eq!(zero_invariant["restrictionMatrix"]["rank"], Value::from(1));
    assert!(
        zero_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/P1-2-coefficient" && row["status"] == "checked"),
        "F2 coefficient must be checked in the ledger"
    );
    assert!(
        zero_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/P1-2-z-zero" && row["status"] == "assumed"),
        "Z-zero lifting must stay assumed"
    );

    let sum_dir = root_out.join("sum-zero");
    fs::create_dir_all(&sum_dir).expect("sum-zero dir exists");
    let sum_archmap = sum_dir.join("archmap.json");
    let sum_policy = sum_dir.join("law_policy.json");
    fs::write(
        &sum_archmap,
        serde_json::to_vec_pretty(&boundary_residue_archmap("sum-zero"))
            .expect("archmap serializes"),
    )
    .expect("sum-zero archmap is written");
    write_test_policy_and_profile(
        &sum_policy,
        boundary_residue_policy(),
        boundary_residue_profile(),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        sum_archmap.to_str().unwrap(),
        "--law-policy",
        sum_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(sum_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        sum_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        sum_dir.to_str().unwrap(),
    ]);
    let sum_packet = read_json(&sum_dir.join("archsig-measurement-packet.json"));
    let sum_row = boundary_residue_row(&sum_packet);
    assert_eq!(sum_row["verdict"], "measured_zero");
    let sum_invariant = invariant_by_id(
        &sum_packet,
        "boundary-residue:profile:ag-boundary-residue@1",
    );
    assert_eq!(sum_invariant["imageMembership"], true);
    assert_eq!(sum_invariant["restrictionMatrix"]["rank"], Value::from(2));

    let nonzero_dir = root_out.join("nonzero");
    fs::create_dir_all(&nonzero_dir).expect("nonzero dir exists");
    let nonzero_archmap = nonzero_dir.join("archmap.json");
    let nonzero_policy = nonzero_dir.join("law_policy.json");
    fs::write(
        &nonzero_archmap,
        serde_json::to_vec_pretty(&boundary_residue_archmap("nonzero"))
            .expect("archmap serializes"),
    )
    .expect("nonzero archmap is written");
    write_test_policy_and_profile(
        &nonzero_policy,
        boundary_residue_policy(),
        boundary_residue_profile(),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        nonzero_archmap.to_str().unwrap(),
        "--law-policy",
        nonzero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(nonzero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        nonzero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        nonzero_dir.to_str().unwrap(),
    ]);
    let nonzero_packet = read_json(&nonzero_dir.join("archsig-measurement-packet.json"));
    let nonzero_row = boundary_residue_row(&nonzero_packet);
    assert_eq!(nonzero_row["verdict"], "measured_nonzero");
    assert_eq!(nonzero_row["verdictData"]["nonZero"], true);
    let nonzero_invariant = invariant_by_id(
        &nonzero_packet,
        "boundary-residue:profile:ag-boundary-residue@1",
    );
    assert_eq!(nonzero_invariant["imageMembership"], false);
    assert!(
        nonzero_invariant["boundaryNote"]
            .as_str()
            .is_some_and(|note| note.contains("no pi1 or monodromy verdict")),
        "boundary note must not revive pi1 / monodromy verdicts"
    );
    assert!(
        nonzero_packet["analyticReadings"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row["evaluator"] != "ag.boundary-residue"),
        "boundary-residue must be structural only and not a period/modelRelative analytic reading"
    );
    assert_eq!(
        nonzero_packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["evaluator"] == "ag.boundary-residue")
            .count(),
        1,
        "M6 must generate exactly one structural verdict row"
    );

    for (case, expected_status) in [
        ("missing-classification", "boundary_classification_absent"),
        ("missing-mismatch", "boundary_mismatch_section_absent"),
        ("missing-matrix", "boundary_restriction_matrix_absent"),
        ("duplicate-role", "boundary_classification_absent"),
    ] {
        let out_dir = root_out.join(case);
        fs::create_dir_all(&out_dir).expect("case dir exists");
        let archmap_path = out_dir.join("archmap.json");
        let policy_path = out_dir.join("law_policy.json");
        fs::write(
            &archmap_path,
            serde_json::to_vec_pretty(&boundary_residue_archmap(case)).expect("archmap serializes"),
        )
        .expect("case archmap is written");
        write_test_policy_and_profile(
            &policy_path,
            boundary_residue_policy(),
            boundary_residue_profile(),
        );
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
        let row = boundary_residue_row(&packet);
        assert_eq!(row["verdict"], "not_computed");
        assert_eq!(row["verdictData"]["methodStatus"], expected_status);
        if case == "missing-classification" {
            assert!(
                packet["assumptions"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|row| row["theoremRef"] == "part8/P1-2-d0" && row["status"] == "violated"),
                "d0 assumption must not be checked when classification is absent"
            );
        }
    }

    for case in [
        "invalid-boundary-column",
        "invalid-core-mismatch",
        "unknown-variable",
    ] {
        let out_dir = root_out.join(case);
        fs::create_dir_all(&out_dir).expect("invalid case dir exists");
        let archmap_path = out_dir.join("archmap.json");
        let policy_path = out_dir.join("law_policy.json");
        fs::write(
            &archmap_path,
            serde_json::to_vec_pretty(&boundary_residue_archmap(case)).expect("archmap serializes"),
        )
        .expect("invalid case archmap is written");
        write_test_policy_and_profile(
            &policy_path,
            boundary_residue_policy(),
            boundary_residue_profile(),
        );
        run_sig0_expect_code(
            &[
                "analyze",
                "--archmap",
                archmap_path.to_str().unwrap(),
                "--law-policy",
                policy_path.to_str().unwrap(),
                "--measurement-profile",
                test_measurement_profile_path(Path::new(policy_path.to_str().unwrap()))
                    .to_str()
                    .expect("path is utf-8"),
                "--out-dir",
                out_dir.to_str().unwrap(),
            ],
            2,
        );
    }

    let z_zero_dir = root_out.join("z-zero");
    fs::create_dir_all(&z_zero_dir).expect("z-zero dir exists");
    let z_zero_policy = z_zero_dir.join("law_policy.json");
    let mut profile = boundary_residue_profile();
    profile["coefficient"] = Value::String("Z".to_string());
    write_test_policy_and_profile(&z_zero_policy, boundary_residue_policy(), profile);
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        z_zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(z_zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        z_zero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        z_zero_dir.to_str().unwrap(),
    ]);
    let z_zero_packet = read_json(&z_zero_dir.join("archsig-measurement-packet.json"));
    let z_zero_row = boundary_residue_row(&z_zero_packet);
    assert_eq!(z_zero_row["verdict"], "unknown");
    assert_eq!(
        z_zero_row["verdictData"]["methodStatus"],
        "finite_mayer_vietoris_d0_obstruction_only"
    );
    assert!(
        z_zero_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/P1-2-coefficient" && row["status"] == "assumed"),
        "non-F2 coefficient mode must record the F2 parity projection as assumed"
    );

    let z_nonzero_dir = root_out.join("z-nonzero");
    fs::create_dir_all(&z_nonzero_dir).expect("z-nonzero dir exists");
    let z_nonzero_policy = z_nonzero_dir.join("law_policy.json");
    let mut profile = boundary_residue_profile();
    profile["coefficient"] = Value::String("Z".to_string());
    write_test_policy_and_profile(&z_nonzero_policy, boundary_residue_policy(), profile);
    run_sig0(&[
        "analyze",
        "--archmap",
        nonzero_archmap.to_str().unwrap(),
        "--law-policy",
        z_nonzero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(z_nonzero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        z_nonzero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        z_nonzero_dir.to_str().unwrap(),
    ]);
    let z_nonzero_packet = read_json(&z_nonzero_dir.join("archsig-measurement-packet.json"));
    let z_nonzero_row = boundary_residue_row(&z_nonzero_packet);
    assert_eq!(z_nonzero_row["verdict"], "measured_nonzero");
    assert_eq!(
        z_nonzero_row["verdictData"]["methodStatus"],
        "finite_mayer_vietoris_d0_obstruction_only"
    );
}

#[test]
fn cli_analyze_v2_section_factorization_checks_selected_section() {
    let root_out = temp_dir("ag-measurement-section-factorization");
    let root = ag_measurement_root();

    let zero_dir = root_out.join("zero");
    fs::create_dir_all(&zero_dir).expect("zero dir exists");
    let zero_archmap = zero_dir.join("archmap.json");
    let zero_policy = zero_dir.join("law_policy.json");
    fs::write(
        &zero_archmap,
        serde_json::to_vec_pretty(&section_archmap("lawful")).expect("archmap serializes"),
    )
    .expect("zero archmap is written");
    write_test_policy_and_profile(&zero_policy, section_policy(), section_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_dir.to_str().unwrap(),
    ]);
    let zero_packet = read_json(&zero_dir.join("archsig-measurement-packet.json"));
    let zero_row = section_row(&zero_packet);
    assert_eq!(zero_row["verdict"], "measured_zero");
    assert_eq!(zero_row["verdictData"]["zero"], true);
    assert_eq!(
        zero_row["verdictData"]["methodStatus"],
        "finite_section_pullback_computed"
    );
    let zero_invariant =
        invariant_by_id(&zero_packet, "section-factorization:profile:ag-section@1");
    assert_eq!(
        zero_invariant["sectionAssignment"]["assignmentStatus"],
        "total"
    );
    assert_eq!(
        zero_invariant["sectionAssignment"]["activeSupport"],
        json!(["x"])
    );
    assert!(
        zero_invariant["minimalForbiddenSupports"][0]["supportRef"]
            .as_str()
            .is_some_and(|reference| reference.starts_with("law-surface:"))
    );
    assert_eq!(zero_invariant["violatedForbiddenSupports"], json!([]));
    assert!(
        zero_packet["assumptions"]
            .as_array()
            .expect("section assumptions are array")
            .iter()
            .any(|row| {
                row["theoremRef"] == "archsig-contract:ag-section-factorization"
                    && row["status"] == "checked"
            }),
        "section factorization contract ID must be emitted and checked"
    );
    assert!(
        zero_invariant["boundaryNote"]
            .as_str()
            .is_some_and(|note| note.contains("section-relative lawful only")
                && note.contains("exactness without No-Cancellation")),
        "section-relative boundary must be explicit"
    );
    assert!(
        zero_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| {
                row["theoremRef"] == "part8/P0-3"
                    && row["checkedBy"]
                        .as_str()
                        .is_some_and(|checked_by| checked_by.contains("law-surface:"))
            }),
        "I_Ob^U presentation ledger must be checked by selected raw support atoms"
    );

    let nonzero_dir = root_out.join("nonzero");
    fs::create_dir_all(&nonzero_dir).expect("nonzero dir exists");
    let nonzero_archmap = nonzero_dir.join("archmap.json");
    let nonzero_policy = nonzero_dir.join("law_policy.json");
    fs::write(
        &nonzero_archmap,
        serde_json::to_vec_pretty(&section_archmap("unlawful")).expect("archmap serializes"),
    )
    .expect("nonzero archmap is written");
    write_test_policy_and_profile(&nonzero_policy, section_policy(), section_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        nonzero_archmap.to_str().unwrap(),
        "--law-policy",
        nonzero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(nonzero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        nonzero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        nonzero_dir.to_str().unwrap(),
    ]);
    let nonzero_packet = read_json(&nonzero_dir.join("archsig-measurement-packet.json"));
    let nonzero_row = section_row(&nonzero_packet);
    assert_eq!(nonzero_row["verdict"], "measured_nonzero");
    assert_eq!(nonzero_row["verdictData"]["nonZero"], true);
    let nonzero_invariant = invariant_by_id(
        &nonzero_packet,
        "section-factorization:profile:ag-section@1",
    );
    assert_eq!(
        nonzero_invariant["violatedForbiddenSupports"][0]["support"],
        json!(["x", "y"])
    );
    assert!(
        nonzero_packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| matches!(
                row["verdict"].as_str().unwrap(),
                "measured_zero" | "measured_nonzero" | "unmeasured" | "unknown" | "not_computed"
            )),
        "section evaluator must reuse the existing five verdict values"
    );

    let partial_dir = root_out.join("partial");
    fs::create_dir_all(&partial_dir).expect("partial dir exists");
    let partial_archmap = partial_dir.join("archmap.json");
    let partial_policy = partial_dir.join("law_policy.json");
    fs::write(
        &partial_archmap,
        serde_json::to_vec_pretty(&section_archmap("partial")).expect("archmap serializes"),
    )
    .expect("partial archmap is written");
    write_test_policy_and_profile(&partial_policy, section_policy(), section_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        partial_archmap.to_str().unwrap(),
        "--law-policy",
        partial_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(partial_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        partial_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        partial_dir.to_str().unwrap(),
    ]);
    let partial_packet = read_json(&partial_dir.join("archsig-measurement-packet.json"));
    let partial_row = section_row(&partial_packet);
    assert_eq!(partial_row["verdict"], "unknown");
    assert_eq!(
        partial_row["verdictData"]["methodStatus"],
        "section_assignment_partial_undecidable"
    );

    let absent_dir = root_out.join("absent");
    fs::create_dir_all(&absent_dir).expect("absent dir exists");
    let absent_archmap = absent_dir.join("archmap.json");
    let absent_policy = absent_dir.join("law_policy.json");
    fs::write(
        &absent_archmap,
        serde_json::to_vec_pretty(&section_archmap("absent")).expect("archmap serializes"),
    )
    .expect("absent archmap is written");
    write_test_policy_and_profile(&absent_policy, section_policy(), section_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        absent_archmap.to_str().unwrap(),
        "--law-policy",
        absent_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(absent_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        absent_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        absent_dir.to_str().unwrap(),
    ]);
    let absent_packet = read_json(&absent_dir.join("archsig-measurement-packet.json"));
    let absent_row = section_row(&absent_packet);
    assert_eq!(absent_row["verdict"], "not_computed");
    assert_eq!(
        absent_row["verdictData"]["methodStatus"],
        "section_assignment_absent"
    );
    assert!(
        absent_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| {
                row["theoremRef"] == "part8/P0-3-boundary" && row["status"] == "assumed"
            }),
        "No-Cancellation/exactness must stay in the assumption ledger"
    );

    let missing_generator_dir = root_out.join("missing-generator");
    fs::create_dir_all(&missing_generator_dir).expect("missing generator dir exists");
    let missing_generator_archmap = missing_generator_dir.join("archmap.json");
    let missing_generator_policy = missing_generator_dir.join("law_policy.json");
    fs::write(
        &missing_generator_archmap,
        serde_json::to_vec_pretty(&section_archmap("missing-generator"))
            .expect("archmap serializes"),
    )
    .expect("missing generator archmap is written");
    write_test_policy_and_profile(
        &missing_generator_policy,
        section_policy(),
        section_profile(),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        missing_generator_archmap.to_str().unwrap(),
        "--law-policy",
        missing_generator_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(missing_generator_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        missing_generator_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        missing_generator_dir.to_str().unwrap(),
    ]);
    let missing_generator_packet =
        read_json(&missing_generator_dir.join("archsig-measurement-packet.json"));
    let missing_generator_row = section_row(&missing_generator_packet);
    assert_eq!(missing_generator_row["verdict"], "not_computed");
    assert_eq!(
        missing_generator_row["verdictData"]["methodStatus"],
        "obstruction_generators_absent"
    );
    assert!(
        missing_generator_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/P0-3" && row["status"] == "violated"),
        "missing raw support evidence must not be treated as an empty ideal"
    );

    let bad_profile_dir = root_out.join("bad-profile");
    fs::create_dir_all(&bad_profile_dir).expect("bad profile dir exists");
    let bad_policy = bad_profile_dir.join("law_policy.json");
    let mut profile = section_profile();
    profile["zeroPredicate"] = Value::String("rank-zero@1".to_string());
    write_test_policy_and_profile(&bad_policy, section_policy(), profile);
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            zero_archmap.to_str().unwrap(),
            "--law-policy",
            bad_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(bad_policy.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            bad_profile_dir.to_str().unwrap(),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_coherence_obstruction_measures_h2_nonzero_with_representative() {
    let out_dir = temp_dir("ag-measurement-coherence-h2-nonzero");
    let archmap_path = out_dir.join("archmap_coherence_h2_nonzero.json");
    let policy_path = out_dir.join("law_policy_coherence.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&coherence_boundary_archmap(true)).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");
    write_test_policy_and_profile(
        &policy_path,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
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
    let coherence = packet["structuralVerdict"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.coherence-obstruction")
        .expect("H2 coherence row is present");
    assert_eq!(coherence["verdict"], "measured_nonzero");
    assert_eq!(coherence["verdictData"]["nonZero"], true);
    assert_eq!(
        coherence["verdictData"]["methodStatus"],
        "finite_f2_h2_coherence_computed"
    );
    let invariant = invariant_by_id(&packet, "coherence-obstruction:profile:ag-coherence@1");
    assert_eq!(invariant["cohomologyQuotient"], "ker d^2/im d^1");
    assert!(
        !serde_json::to_string(invariant)
            .expect("invariant serializes")
            .contains("ker d^1/im d^0"),
        "H2 invariant prose must not use the H1 quotient"
    );
    assert_eq!(invariant["cocycleGate"]["passed"], true);
    assert_eq!(
        invariant["representative"]
            .as_array()
            .expect("representative is array")
            .len(),
        1,
        "tetrahedron-boundary fixture carries a concrete H2 representative"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["assumption"]
                == "banded abelian F2 coefficient object for selected H2 coherence"
                && entry["status"] == "checked"),
        "coefficient=F2 must be checked in the CBI ledger"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["assumption"]
                == "Leray / acyclicity comparison from selected Cech complex to sheaf cohomology"
                && entry["status"] == "assumed"),
        "Leray comparison must stay assumed"
    );

    let zero_cochain_dir = temp_dir("ag-measurement-coherence-h2-nonzero-zero-cochain");
    let zero_cochain_archmap_path = zero_cochain_dir.join("archmap_coherence_h2_zero_cochain.json");
    let zero_cochain_policy_path = zero_cochain_dir.join("law_policy_coherence.json");
    fs::write(
        &zero_cochain_archmap_path,
        serde_json::to_vec_pretty(&coherence_boundary_zero_cochain_archmap())
            .expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");
    write_test_policy_and_profile(
        &zero_cochain_policy_path,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_cochain_archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        zero_cochain_policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            zero_cochain_policy_path.to_str().expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        zero_cochain_policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_cochain_dir.to_str().expect("path is utf-8"),
    ]);
    let zero_cochain_packet = read_json(&zero_cochain_dir.join("archsig-measurement-packet.json"));
    let zero_cochain_row = coherence_row(&zero_cochain_packet);
    assert_eq!(
        zero_cochain_row["verdict"], "measured_nonzero",
        "H2 quotient must be nonzero even when the supplied witness cochain is zero"
    );
    let zero_cochain_invariant = invariant_by_id(
        &zero_cochain_packet,
        "coherence-obstruction:profile:ag-coherence@1",
    );
    assert_eq!(zero_cochain_invariant["h2Dimension"], Value::from(1));
    assert!(
        !zero_cochain_invariant["representative"]
            .as_array()
            .expect("representative is array")
            .is_empty(),
        "nonzero H2 quotient must surface a representative independent of the zero witness cochain"
    );
}

#[test]
fn cli_analyze_v2_coherence_obstruction_distinguishes_zero_silence_and_banding_boundary() {
    let root_out = temp_dir("ag-measurement-coherence-statuses");

    let zero_dir = root_out.join("zero");
    fs::create_dir_all(&zero_dir).expect("zero dir exists");
    let zero_archmap = zero_dir.join("archmap.json");
    let zero_policy = zero_dir.join("law_policy.json");
    fs::write(
        &zero_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(true)).expect("archmap serializes"),
    )
    .expect("zero archmap is written");
    write_test_policy_and_profile(
        &zero_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        zero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_dir.to_str().unwrap(),
    ]);
    let zero_packet = read_json(&zero_dir.join("archsig-measurement-packet.json"));
    let zero_row = coherence_row(&zero_packet);
    assert_eq!(zero_row["verdict"], "measured_zero");
    assert_eq!(zero_row["verdictData"]["zero"], true);
    let zero_invariant =
        invariant_by_id(&zero_packet, "coherence-obstruction:profile:ag-coherence@1");
    assert_eq!(zero_invariant["cocycleGate"]["passed"], true);

    let unmeasured_dir = root_out.join("unmeasured");
    fs::create_dir_all(&unmeasured_dir).expect("unmeasured dir exists");
    let unmeasured_archmap = unmeasured_dir.join("archmap.json");
    let unmeasured_policy = unmeasured_dir.join("law_policy.json");
    fs::write(
        &unmeasured_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(false)).expect("archmap serializes"),
    )
    .expect("unmeasured archmap is written");
    write_test_policy_and_profile(
        &unmeasured_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        unmeasured_archmap.to_str().unwrap(),
        "--law-policy",
        unmeasured_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(unmeasured_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        unmeasured_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        unmeasured_dir.to_str().unwrap(),
    ]);
    let unmeasured_packet = read_json(&unmeasured_dir.join("archsig-measurement-packet.json"));
    let unmeasured_row = coherence_row(&unmeasured_packet);
    assert_eq!(unmeasured_row["verdict"], "unmeasured");
    assert_eq!(
        unmeasured_row["verdictData"]["methodStatus"],
        "coherence_witness_absent"
    );

    let empty_dir = root_out.join("empty");
    fs::create_dir_all(&empty_dir).expect("empty dir exists");
    let empty_archmap = empty_dir.join("archmap.json");
    let empty_policy = empty_dir.join("law_policy.json");
    fs::write(
        &empty_archmap,
        serde_json::to_vec_pretty(&coherence_empty_archmap()).expect("archmap serializes"),
    )
    .expect("empty archmap is written");
    write_test_policy_and_profile(
        &empty_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        empty_archmap.to_str().unwrap(),
        "--law-policy",
        empty_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(empty_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        empty_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        empty_dir.to_str().unwrap(),
    ]);
    let empty_packet = read_json(&empty_dir.join("archsig-measurement-packet.json"));
    let empty_row = coherence_row(&empty_packet);
    assert_eq!(empty_row["verdict"], "not_computed");
    assert_eq!(
        empty_row["verdictData"]["methodStatus"],
        "empty_selected_2_skeleton"
    );

    let banding_dir = root_out.join("banding");
    fs::create_dir_all(&banding_dir).expect("banding dir exists");
    let banding_archmap = banding_dir.join("archmap.json");
    let banding_policy = banding_dir.join("law_policy.json");
    fs::write(
        &banding_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(true)).expect("archmap serializes"),
    )
    .expect("banding archmap is written");
    write_test_policy_and_profile(
        &banding_policy,
        coherence_policy("Aut(Dec_U)", false),
        coherence_profile("Aut(Dec_U)", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        banding_archmap.to_str().unwrap(),
        "--law-policy",
        banding_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(banding_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        banding_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        banding_dir.to_str().unwrap(),
    ]);
    let banding_packet = read_json(&banding_dir.join("archsig-measurement-packet.json"));
    let banding_row = coherence_row(&banding_packet);
    assert_eq!(banding_row["verdict"], "not_computed");
    assert_eq!(
        banding_row["verdictData"]["methodStatus"],
        "banding_violated"
    );
    assert!(
        banding_packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| matches!(
                row["verdict"].as_str().unwrap(),
                "measured_zero" | "measured_nonzero" | "unmeasured" | "unknown" | "not_computed"
            )),
        "coherence evaluator must reuse the existing five verdict values"
    );

    let non_cocycle_dir = root_out.join("non-cocycle");
    fs::create_dir_all(&non_cocycle_dir).expect("non-cocycle dir exists");
    let non_cocycle_archmap = non_cocycle_dir.join("archmap.json");
    let non_cocycle_policy = non_cocycle_dir.join("law_policy.json");
    fs::write(
        &non_cocycle_archmap,
        serde_json::to_vec_pretty(&coherence_filled_tetrahedron_archmap())
            .expect("archmap serializes"),
    )
    .expect("non-cocycle archmap is written");
    write_test_policy_and_profile(
        &non_cocycle_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        non_cocycle_archmap.to_str().unwrap(),
        "--law-policy",
        non_cocycle_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(non_cocycle_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        non_cocycle_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        non_cocycle_dir.to_str().unwrap(),
    ]);
    let non_cocycle_packet = read_json(&non_cocycle_dir.join("archsig-measurement-packet.json"));
    let non_cocycle_row = coherence_row(&non_cocycle_packet);
    assert_eq!(non_cocycle_row["verdict"], "not_computed");
    assert_eq!(
        non_cocycle_row["verdictData"]["methodStatus"], "not_2_cocycle",
        "d2 h = 0 must gate im d1 membership before a nonzero verdict can be emitted"
    );
    let non_cocycle_invariant = invariant_by_id(
        &non_cocycle_packet,
        "coherence-obstruction:profile:ag-coherence@1",
    );
    assert_eq!(non_cocycle_invariant["cocycleGate"]["passed"], false);

    let incomplete_dir = root_out.join("incomplete");
    fs::create_dir_all(&incomplete_dir).expect("incomplete dir exists");
    let incomplete_archmap = incomplete_dir.join("archmap.json");
    let incomplete_policy = incomplete_dir.join("law_policy.json");
    fs::write(
        &incomplete_archmap,
        serde_json::to_vec_pretty(&coherence_incomplete_triangle_archmap())
            .expect("archmap serializes"),
    )
    .expect("incomplete archmap is written");
    write_test_policy_and_profile(
        &incomplete_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        incomplete_archmap.to_str().unwrap(),
        "--law-policy",
        incomplete_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(incomplete_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        incomplete_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        incomplete_dir.to_str().unwrap(),
    ]);
    let incomplete_packet = read_json(&incomplete_dir.join("archsig-measurement-packet.json"));
    let incomplete_row = coherence_row(&incomplete_packet);
    assert_eq!(incomplete_row["verdict"], "not_computed");
    assert_eq!(
        incomplete_row["verdictData"]["methodStatus"],
        "incomplete_selected_2_skeleton"
    );

    let oversized_dir = root_out.join("oversized");
    fs::create_dir_all(&oversized_dir).expect("oversized dir exists");
    let oversized_archmap = oversized_dir.join("archmap.json");
    let oversized_policy = oversized_dir.join("law_policy.json");
    fs::write(
        &oversized_archmap,
        serde_json::to_vec_pretty(&coherence_oversized_archmap()).expect("archmap serializes"),
    )
    .expect("oversized archmap is written");
    write_test_policy_and_profile(
        &oversized_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        oversized_archmap.to_str().unwrap(),
        "--law-policy",
        oversized_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(oversized_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        oversized_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        oversized_dir.to_str().unwrap(),
    ]);
    let oversized_packet = read_json(&oversized_dir.join("archsig-measurement-packet.json"));
    let oversized_row = coherence_row(&oversized_packet);
    assert_eq!(oversized_row["verdict"], "not_computed");
    assert_eq!(
        oversized_row["verdictData"]["methodStatus"],
        "selected_cover_too_large"
    );

    let missing_family_dir = root_out.join("missing-family");
    fs::create_dir_all(&missing_family_dir).expect("missing-family dir exists");
    let missing_family_archmap = missing_family_dir.join("archmap.json");
    let missing_family_policy = missing_family_dir.join("law_policy.json");
    let mut missing_family_profile = coherence_profile("F2", false);
    missing_family_profile["witnessFamily"] = Value::Array(vec![]);
    fs::write(
        &missing_family_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(true)).expect("archmap serializes"),
    )
    .expect("missing-family archmap is written");
    write_test_policy_and_profile(
        &missing_family_policy,
        coherence_policy("F2", false),
        missing_family_profile,
    );
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            missing_family_archmap.to_str().unwrap(),
            "--law-policy",
            missing_family_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(missing_family_policy.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            missing_family_dir.to_str().unwrap(),
        ],
        2,
    );

    let bad_selector_dir = root_out.join("bad-selector");
    fs::create_dir_all(&bad_selector_dir).expect("bad-selector dir exists");
    let bad_selector_archmap = bad_selector_dir.join("archmap.json");
    let bad_selector_policy = bad_selector_dir.join("law_policy.json");
    let mut bad_selector_profile = coherence_profile("F2", false);
    bad_selector_profile["resolutionSelector"] = Value::String("taylor@1".to_string());
    fs::write(
        &bad_selector_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(true)).expect("archmap serializes"),
    )
    .expect("bad-selector archmap is written");
    write_test_policy_and_profile(
        &bad_selector_policy,
        coherence_policy("F2", false),
        bad_selector_profile,
    );
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            bad_selector_archmap.to_str().unwrap(),
            "--law-policy",
            bad_selector_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(bad_selector_policy.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            bad_selector_dir.to_str().unwrap(),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_insight_artifacts_redact_local_source_refs() {
    let out_dir = temp_dir("ag-measurement-insight-source-redaction");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    let private_ref = "/workspace/local-only/internal.rs";
    archmap["sources"][private_ref] = json!({
        "kind": "rust",
        "path": private_ref,
        "symbol": "InternalOnly",
        "line": 1
    });
    let atoms = archmap["atoms"].as_array_mut().expect("atoms are array");
    let mismatch = atoms
        .iter_mut()
        .find(|atom| atom["id"] == "atom:left-cech-section-value")
        .expect("section value atom exists");
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
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    archmap["atoms"][0]["kind"] = Value::String("unknown-legacy-kind".to_string());
    let archmap_path = out_dir.join("archmap_v2_bad_atom_kind.json");
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
        root.join("law_policy_ag.json")
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
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert_eq!(report["insightCards"][0]["kind"], "validation_failure");
    assert_eq!(manifest["mode"], "validation-failure");
    assert_eq!(
        manifest["conclusionCode"],
        "VALIDATION_FAILED_BEFORE_MEASUREMENT"
    );
    assert_eq!(manifest["toolVersion"], "0.5.4");
    assert!(
        manifest["runId"]
            .as_str()
            .is_some_and(|run_id| run_id.starts_with("run:") && run_id.len() == 16)
    );
    assert!(manifest["inputDigests"]["archmap"]["sha256"].is_string());
    assert!(manifest["inputDigests"]["lawPolicy"]["sha256"].is_string());
}

#[test]
fn cli_analyze_v2_cech_rejects_unsupported_measurement_profile_selectors() {
    let out_dir = temp_dir("ag-measurement-cech-bad-profile");
    let root = ag_measurement_root();
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    profile["coefficient"] = Value::String("Z".to_string());
    let policy_path = out_dir.join("law_policy_bad_cech_selector.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_cech_h1_visible.json")
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
fn cli_analyze_v2_cech_requires_matching_witness_family() {
    let out_dir = temp_dir("ag-measurement-cech-witness-family");
    let root = ag_measurement_root();
    let (policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    let policy_path = out_dir.join("law_policy_missing_cech_witness.json");
    let mut policy = policy;
    policy["lawSurfaceRef"] = json!("law-surface:cech-h1-v052");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_h1_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
}

#[test]
fn cli_analyze_v2_cech_ignores_unanchored_mismatch_support() {
    let out_dir = temp_dir("ag-measurement-cech-unanchored-support");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    for atom in archmap["atoms"].as_array_mut().expect("atoms are array") {
        if atom["predicate"] == "sectionValue" {
            atom["object"] = Value::String("section=bottom-local".to_string());
        }
    }
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
fn cli_analyze_v2_topological_debt_capacity_does_not_claim_h1_class() {
    let out_dir = temp_dir("ag-measurement-cech-positive-capacity-no-class");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    for atom in archmap["atoms"].as_array_mut().expect("atoms are array") {
        if atom["predicate"] == "sectionValue" {
            atom["object"] = Value::String("section=bottom-local".to_string());
        }
    }
    let top_context = archmap["contexts"]
        .as_array_mut()
        .expect("contexts is array")
        .iter_mut()
        .find(|context| context["id"] == "ctx:top")
        .expect("ctx:top exists");
    top_context["restrictsTo"]
        .as_array_mut()
        .expect("ctx:top restrictsTo is array")
        .push(Value::String("ctx:bottom".to_string()));
    let archmap_path = out_dir.join("archmap_v2_positive_capacity_no_class.json");
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
        root.join("law_policy_cech_positive_capacity.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_positive_capacity_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(cech["observedCocycle"]["classNonzero"], false);
    let capacity = invariant_by_id(&packet, "topological-debt-capacity:profile:ag-default@1");
    assert_eq!(capacity["capacityLowerBound"], Value::from(1));
    assert_eq!(capacity["b1NerveReading"]["oneSkeletonB1"], Value::from(2));
    assert_eq!(capacity["b1NerveReading"]["nerveComplexB1"], Value::from(2));
    assert_eq!(
        capacity["measuredCechVerdictEcho"]["h1ClassNonzero"],
        Value::Bool(false)
    );
    assert!(
        capacity["b1NerveReading"]["nonClaim"]
            .as_str()
            .is_some_and(|text| text.contains("not concrete H1 class existence claims")),
        "positive capacity must remain a non-claim about concrete H1 class existence"
    );
}
