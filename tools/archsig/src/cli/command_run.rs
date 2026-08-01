pub(crate) fn run() -> Result<ExitCode, Box<dyn Error>> {
    let args = Args::parse();

    match args.command {
        Some(Command::LawPolicy {
            law_policy,
            measurement_profile,
            law_surface,
            out,
        }) => {
            reject_output_overwrite(&law_policy, &out)?;
            reject_output_overwrite(&measurement_profile, &out)?;
            reject_output_overwrite(&law_surface, &out)?;
            let (_, profile, profile_failed) =
                validate_measurement_profile_command_input(&measurement_profile)?;
            let law_surface_raw = read_json(&law_surface)?;
            require_schema(&law_surface_raw, LAW_EQUATION_SURFACE_V1_SCHEMA, "--law-surface")?;
            let law_surface_document: LawEquationSurfaceV1 =
                serde_json::from_value(law_surface_raw)?;
            let (_, law_surface_failed) = validate_law_surface_command_input(&law_surface)?;
            let (report, policy_failed) = validate_law_policy_command_input(
                &law_policy,
                &profile,
                &law_surface_document,
            )?;
            write_json(out, &report)?;
            Ok(if policy_failed || profile_failed || law_surface_failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::LawSurface { law_surface, out }) => {
            reject_output_overwrite(&law_surface, &out)?;
            let (report, failed) = validate_law_surface_command_input(&law_surface)?;
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::MeasurementProfile {
            measurement_profile,
            out,
        }) => {
            reject_output_overwrite(&measurement_profile, &out)?;
            let (report, _, failed) = validate_measurement_profile_command_input(&measurement_profile)?;
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::Gate {
            packet,
            policy,
            comparison,
            out,
        }) => {
            reject_output_overwrite(&packet, &out)?;
            reject_output_overwrite(&policy, &out)?;
            if let Some(comparison) = &comparison {
                reject_output_overwrite(comparison, &out)?;
            }
            let (report, exit_code) = build_gate_report_v1(&packet, &policy, comparison.as_deref())?;
            write_json(out, &report)?;
            Ok(ExitCode::from(exit_code as u8))
        }
        Some(Command::Compare {
            base_run,
            head_run,
            out_dir,
        }) => {
            reject_compare_output_alias(&base_run, &head_run, &out_dir)?;
            reject_compare_output_overwrite(&out_dir)?;
            let (archmap_diff, comparison_report) =
                build_comparison_artifacts_v1(&base_run, &head_run)?;
            std::fs::create_dir_all(&out_dir)?;
            write_json(Some(out_dir.join("archmap-diff.json")), &archmap_diff)?;
            write_json(
                Some(out_dir.join("archsig-comparison-report.json")),
                &comparison_report,
            )?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::PolicyBundle {
            policy_bundle,
            law_policy,
            law_surface,
            measurement_profile,
            id,
            out,
        }) => {
            if let Some(bundle_path) = policy_bundle {
                reject_output_overwrite(&bundle_path, &out)?;
                let resolved = resolve_and_verify_policy_bundle(&bundle_path, None, None, None)?;
                write_json(out, &resolved.report)?;
                Ok(if resolved.report["summary"]["result"] == "pass" {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(1)
                })
            } else {
                let law_policy = law_policy.ok_or(
                    "--law-policy, --law-surface, and --measurement-profile are required when creating a policy bundle",
                )?;
                let law_surface = law_surface.ok_or(
                    "--law-policy, --law-surface, and --measurement-profile are required when creating a policy bundle",
                )?;
                let measurement_profile = measurement_profile.ok_or(
                    "--law-policy, --law-surface, and --measurement-profile are required when creating a policy bundle",
                )?;
                let out = out.ok_or(
                    "--out is required when creating a policy bundle so component references remain resolvable",
                )?;
                reject_output_overwrite(&law_policy, &Some(out.clone()))?;
                reject_output_overwrite(&law_surface, &Some(out.clone()))?;
                reject_output_overwrite(&measurement_profile, &Some(out.clone()))?;
                let bundle = build_policy_bundle(
                    &law_policy,
                    &law_surface,
                    &measurement_profile,
                    Some(&out),
                    &id,
                )?;
                write_json(Some(out), &bundle)?;
                Ok(ExitCode::SUCCESS)
            }
        }
        Some(Command::Analyze {
            archmap,
            law_policy,
            law_surface,
            measurement_profiles,
            policy_bundle,
            out_dir,
            stamp,
        }) => {
            let policy_bundle_input = policy_bundle.clone();
            let (law_policy, law_surface, measurement_profile_paths, bundle_fingerprints) =
                if let Some(bundle_path) = policy_bundle {
                    let resolved = resolve_and_verify_policy_bundle(&bundle_path, None, None, None)?;
                    if resolved.report["summary"]["result"] != "pass" {
                        return Err("policy bundle fingerprint validation failed".into());
                    }
                    (
                        resolved.law_policy,
                        Some(resolved.law_surface),
                        vec![resolved.measurement_profile],
                        Some(serde_json::json!(resolved.bundle.component_fingerprints)),
                    )
                } else {
                    (
                        law_policy.ok_or("--law-policy is required without --policy-bundle")?,
                        law_surface,
                        measurement_profiles
                            .ok_or("--measurement-profile is required without --policy-bundle")?,
                        None,
                    )
                };
            let measurement_profile = measurement_profile_paths
                .first()
                .cloned()
                .ok_or("at least one --measurement-profile is required")?;
            let archmap_validation_path = out_dir.join("archmap-validation.json");
            let law_policy_validation_path = out_dir.join("law-policy-validation.json");
            let analysis_summary_path = out_dir.join("archsig-analysis-summary.json");
            let atom_viewer_data_path = out_dir.join("archsig-atom-viewer-data.json");
            let view_model_path = out_dir.join("archsig-measurement-view-model.json");
            let run_manifest_path = out_dir.join("archsig-run-manifest.json");
            let normalized_archmap_path = out_dir.join("normalized-archmap.json");
            let measurement_packet_path = out_dir.join("archsig-measurement-packet.json");
            let insight_report_path = out_dir.join("archsig-insight-report.json");
            let insight_brief_path = out_dir.join("archsig-insight-brief.md");
            let analysis_validation_path = out_dir.join("archsig-analysis-validation.json");
            let law_surface_validation_path = out_dir.join("law-surface-validation.json");
            let mut analyze_input_paths = vec![archmap.clone(), law_policy.clone()];
            analyze_input_paths.extend(law_surface.iter().cloned());
            analyze_input_paths.extend(measurement_profile_paths.iter().cloned());
            analyze_input_paths.extend(policy_bundle_input);
            let analyze_output_paths = vec![
                archmap_validation_path.clone(),
                law_policy_validation_path.clone(),
                analysis_summary_path.clone(),
                atom_viewer_data_path.clone(),
                view_model_path.clone(),
                run_manifest_path.clone(),
                normalized_archmap_path.clone(),
                measurement_packet_path.clone(),
                insight_report_path.clone(),
                insight_brief_path.clone(),
                analysis_validation_path.clone(),
                law_surface_validation_path.clone(),
            ];
            for input in &analyze_input_paths {
                for output in &analyze_output_paths {
                    reject_output_overwrite(input, &Some(output.clone()))?;
                }
            }

            std::fs::create_dir_all(&out_dir)?;
            reject_analyze_output_overwrite(&out_dir)?;
            remove_analyze_success_artifacts(&out_dir)?;

            let (archmap_preflight, archmap_failed) =
                validate_archmap_command_input(&archmap)?;
            let archmap_document: ArchMapDocumentV2 = read_json(&archmap)?;
            let mut measurement_profile_documents = Vec::new();
            let mut measurement_profile_failed = false;
            for path in &measurement_profile_paths {
                let (_report, document, failed) = validate_measurement_profile_command_input(path)?;
                measurement_profile_documents.push(document);
                measurement_profile_failed |= failed;
            }
            let _measurement_profile_document = measurement_profile_documents
                .first()
                .cloned()
                .ok_or("at least one --measurement-profile is required")?;
            let measurement_profile_catalog = measurement_profile_documents
                .iter()
                .map(|profile| (profile.profile_id.clone(), profile.clone()))
                .collect::<BTreeMap<_, _>>();
            if measurement_profile_catalog.len() != measurement_profile_documents.len() {
                return Err("--measurement-profile inputs must have unique profileId values".into());
            }
            let law_surface_preflight = law_surface
                .as_ref()
                .map(validate_law_surface_command_input)
                .transpose()?;
            let law_surface_document = law_surface
                .as_ref()
                .map(read_json)
                .transpose()?
                .map(serde_json::from_value::<LawEquationSurfaceV1>)
                .transpose()?;
            let law_policy_document: LawPolicyDocumentV1 = read_json(&law_policy)?;
            let law_policy_report = archsig::validate_law_policy_v1_report_with_profiles(
                &law_policy_document,
                &stable_input_ref(&law_policy),
                &measurement_profile_catalog,
                law_surface_document.as_ref(),
            );
            let law_policy_failed = law_policy_report.summary.result == "fail";
            let law_policy_preflight = serde_json::to_value(law_policy_report)?;
            let law_surface_failed = law_surface_preflight
                .as_ref()
                .is_some_and(|(_, failed)| *failed);
            let archmap_input_ref = artifact_input_ref(&archmap);
            let law_policy_input_ref = artifact_input_ref(&law_policy);
            let law_surface_input_ref = law_surface
                .as_ref()
                .map(|path| artifact_input_ref(path));
            let measurement_profile_input_ref = artifact_input_ref(&measurement_profile);
            let measurement_profile_input_refs = measurement_profile_paths
                .iter()
                .map(|path| artifact_input_ref(path))
                .collect::<Vec<_>>();
            let archmap_contract_input: Value = read_json(&archmap)?;
            let law_policy_contract_input: Value = read_json(&law_policy)?;
            let measurement_profile_contract_inputs = measurement_profile_paths
                .iter()
                .map(read_json)
                .collect::<Result<Vec<_>, _>>()?;
            let mut validation_generated_artifacts =
                vec!["archmap-validation.json", "law-policy-validation.json"];
            if law_surface_preflight.is_some() {
                validation_generated_artifacts.push("law-surface-validation.json");
            }
            let mut failure_generated_artifacts = validation_generated_artifacts.clone();
            failure_generated_artifacts.extend([
                "archsig-insight-report.json",
                "archsig-insight-brief.md",
                "archsig-atom-viewer-data.json",
                "archsig-run-manifest.json",
            ]);
            let mut measurement_generated_artifacts = validation_generated_artifacts.clone();
            measurement_generated_artifacts.extend([
                "normalized-archmap.json",
                "archsig-measurement-packet.json",
                "archsig-analysis-validation.json",
                "archsig-analysis-summary.json",
                "archsig-insight-report.json",
                "archsig-insight-brief.md",
                "archsig-atom-viewer-data.json",
                "archsig-measurement-view-model.json",
                "archsig-run-manifest.json",
            ]);
            let component_fingerprints = bundle_fingerprints.or(Some(serde_json::json!(
                build_component_fingerprints(&law_policy, law_surface.as_deref().ok_or(
                    "analyze requires --law-surface for LawPolicy v0.5.4",
                )?, &measurement_profile)?
            )));
            let run_contract = AnalyzeRunContract::from_inputs(
                &archmap,
                &law_policy,
                law_surface.as_deref(),
                &measurement_profile_paths
                .iter()
                .map(PathBuf::as_path)
                .collect::<Vec<_>>(),
                contract_profile_fingerprint(
                    &law_policy_contract_input,
                    &measurement_profile_contract_inputs,
                )?,
                contract_site_cover_digest(&archmap_contract_input)?,
                component_fingerprints,
                stamp,
            )?;
            write_json(
                Some(archmap_validation_path),
                &with_run_contract(&archmap_preflight, &run_contract)?,
            )?;
            write_json(
                Some(law_policy_validation_path),
                &with_run_contract(&law_policy_preflight, &run_contract)?,
            )?;
            if let Some((law_surface_report, _)) = &law_surface_preflight {
                write_json(
                    Some(law_surface_validation_path.clone()),
                    &with_run_contract(law_surface_report, &run_contract)?,
                )?;
            }
            if archmap_failed
                || law_policy_failed
                || measurement_profile_failed
                || law_surface_failed
            {
                let mut insight_report = build_validation_failure_insight_report(
                    &archmap_preflight,
                    &law_policy_preflight,
                    law_surface_preflight
                        .as_ref()
                        .map(|(report, _)| report),
                );
                let insight_brief = build_insight_brief_v1(&insight_report);
                attach_run_contract(&mut insight_report, &run_contract);
                let mut viewer_data = build_validation_failure_viewer_data(&insight_report);
                attach_run_contract(&mut viewer_data, &run_contract);
                write_json(Some(insight_report_path), &insight_report)?;
                std::fs::write(insight_brief_path, insight_brief)?;
                write_json(Some(atom_viewer_data_path), &viewer_data)?;
                write_json(
                    Some(run_manifest_path),
                    &serde_json::json!({
                        "schema": "archsig-run-manifest/v0.5.4",
                        "toolVersion": run_contract.tool_version.clone(),
                        "runId": run_contract.run_id.clone(),
                        "inputDigests": run_contract.input_digests.clone(),
                        "artifactDigests": {},
                        "componentFingerprints": run_contract.component_fingerprints.clone(),
                        "commandName": "analyze",
                        "mode": "validation-failure",
                        "conclusionCode": ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT,
                        "archmapInputPath": archmap_input_ref,
                        "lawPolicyInputPath": law_policy_input_ref,
                        "lawSurfaceInputPath": law_surface_input_ref,
                        "measurementProfileInputPath": measurement_profile_input_ref,
                        "measurementProfileInputPaths": measurement_profile_input_refs,
                        "rawArtifactRetention": "not-computed",
                        "generatedArtifacts": failure_generated_artifacts,
                        "omittedArtifacts": [
                            "normalized-archmap.json",
                            "archsig-measurement-packet.json",
                            "archsig-analysis-validation.json",
                            "archsig-analysis-summary.json",
                            "archsig-measurement-view-model.json",
                        ],
                        "artifactLinks": {
                            "insightReport": "archsig-insight-report.json",
                            "insightBrief": "archsig-insight-brief.md",
                            "viewerData": "archsig-atom-viewer-data.json"
                        },
                        "validationReports": {
                            "archmap": "archmap-validation.json",
                            "lawPolicy": "law-policy-validation.json",
                            "lawSurface": law_surface_preflight.as_ref().map(|_| "law-surface-validation.json"),
                            "analysis": null
                        },
                        "rawArtifactPaths": null,
                        "validationResultSummary": {
                            "archmap": validation_result_summary(&archmap_preflight),
                            "lawPolicy": validation_result_summary(&law_policy_preflight),
                            "lawSurface": law_surface_preflight.as_ref().map(|(report, _)| validation_result_summary(report)),
                            "analysis": validation_result_summary_from_counts("not_computed", 0, 0)
                        },
                        "nonConclusions": [
                            "Validation failure insight is a pre-normalization projection and does not contain measurement packet claims.",
                            "No measurement packet, structural verdict, or AG invariant was computed after failed preflight validation."
                        ]
                    }),
                )?;
                eprintln!(
                    "archsig analyze wrote validation insight artifacts to {} and stopped before normalization",
                    out_dir.display()
                );
                if law_surface.is_none() {
                    eprintln!("analyze requires --law-surface for LawPolicy v0.5.4");
                }
                return Ok(ExitCode::from(2));
            }
            let normalized_archmap = normalize_archmap_v2(&archmap_document, &archmap_input_ref);
            let measurement_packet = match build_foundation_measurement_packet_v1(
                &normalized_archmap,
                &archmap_document,
                &law_policy_document,
                law_surface_document.as_ref(),
                &measurement_profile_catalog,
                &archmap_input_ref,
                &law_policy_input_ref,
                law_surface_input_ref.as_deref(),
                &measurement_profile_input_ref,
            )
            {
                Ok(packet) => packet,
                Err(message) => {
                    let mut runtime_failure_generated_artifacts = validation_generated_artifacts.clone();
                    runtime_failure_generated_artifacts.extend([
                        "archsig-analysis-validation.json",
                        "archsig-run-manifest.json",
                    ]);
                    let analysis_failure = serde_json::json!({
                        "schema": "archsig-measurement-packet-validation-report/v0.5.4",
                        "packetSchema": "archsig-measurement-packet/v0.5.4",
                        "checks": [{
                            "id": "analysis-execution-plan",
                            "result": "fail",
                            "message": message.clone()
                        }],
                        "summary": {
                            "result": "fail",
                            "failedCheckCount": 1,
                            "warningCheckCount": 0
                        }
                    });
                    write_json(
                        Some(analysis_validation_path),
                        &with_run_contract(&analysis_failure, &run_contract)?,
                    )?;
                    write_json(
                        Some(run_manifest_path),
                        &serde_json::json!({
                            "schema": "archsig-run-manifest/v0.5.4",
                            "toolVersion": run_contract.tool_version.clone(),
                            "runId": run_contract.run_id.clone(),
                            "inputDigests": run_contract.input_digests.clone(),
                            "artifactDigests": {},
                            "componentFingerprints": run_contract.component_fingerprints.clone(),
                            "commandName": "analyze",
                            "mode": "analysis-failure",
                            "conclusionCode": "ANALYSIS_FAILED_BEFORE_MEASUREMENT",
                            "archmapInputPath": archmap_input_ref,
                            "lawPolicyInputPath": law_policy_input_ref,
                            "lawSurfaceInputPath": law_surface_input_ref,
                            "measurementProfileInputPath": measurement_profile_input_ref,
                            "measurementProfileInputPaths": measurement_profile_input_refs,
                            "rawArtifactRetention": "not-computed",
                            "generatedArtifacts": runtime_failure_generated_artifacts,
                            "omittedArtifacts": [
                                "normalized-archmap.json",
                                "archsig-measurement-packet.json",
                                "archsig-analysis-summary.json",
                                "archsig-insight-report.json",
                                "archsig-insight-brief.md",
                                "archsig-atom-viewer-data.json"
                            ],
                            "validationReports": {
                                "archmap": "archmap-validation.json",
                                "lawPolicy": "law-policy-validation.json",
                                "lawSurface": law_surface_preflight.as_ref().map(|_| "law-surface-validation.json"),
                                "analysis": "archsig-analysis-validation.json"
                            },
                            "validationResultSummary": {
                                "archmap": validation_result_summary(&archmap_preflight),
                                "lawPolicy": validation_result_summary(&law_policy_preflight),
                                "lawSurface": law_surface_preflight.as_ref().map(|(report, _)| validation_result_summary(report)),
                                "analysis": validation_result_summary_from_counts("fail", 1, 0)
                            },
                            "nonConclusions": [
                                "Execution-plan failure occurred after input validation and before normalization.",
                                "No measurement packet, structural verdict, or AG invariant was computed."
                            ]
                        }),
                    )?;
                    eprintln!("archsig analyze execution plan failed before measurement: {message}");
                    return Ok(ExitCode::from(2));
                }
            };
            write_json(
                Some(normalized_archmap_path.clone()),
                &with_run_contract(&normalized_archmap, &run_contract)?,
            )?;
            let packet_value = with_run_contract(&measurement_packet, &run_contract)?;
            let packet_validation = validate_measurement_packet_value_v1(&packet_value);
            let packet_failed = packet_validation.iter().any(|check| check.result == "fail");
            let packet_failed_check_count = packet_validation
                .iter()
                .filter(|check| check.result == "fail")
                .count();
            let packet_warning_check_count = packet_validation
                .iter()
                .filter(|check| check.result == "warn")
                .count();
            write_json(
                Some(measurement_packet_path.clone()),
                &packet_value,
            )?;
            let measurement_summary = build_measurement_summary_v1(&measurement_packet);
            let insight_report = build_insight_report_v1(
                &normalized_archmap,
                &measurement_packet,
                &measurement_summary,
            );
            let insight_brief = build_insight_brief_v1(&insight_report);
            let measurement_viewer_data = build_measurement_viewer_data_v1(
                &normalized_archmap,
                &archmap_document,
                &measurement_packet,
                &measurement_summary,
                &insight_report,
            );
            let mut measurement_viewer_data =
                with_run_contract(&measurement_viewer_data, &run_contract)?;
            measurement_viewer_data["inputDigests"]["measurementPacket"] = serde_json::json!({
                "path": "input:archsig-measurement-packet.json",
                "sha256": canonical_json_file_digest(&measurement_packet_path)?
            });
            write_json(
                Some(analysis_validation_path),
                &with_run_contract(&serde_json::json!({
                    "schema": "archsig-measurement-packet-validation-report/v0.5.4",
                    "packetSchema": measurement_packet.schema,
                    "checks": packet_validation,
                    "summary": {
                        "result": if packet_failed { "fail" } else { "pass" },
                        "failedCheckCount": packet_failed_check_count,
                        "warningCheckCount": packet_warning_check_count
                    }
                }), &run_contract)?,
            )?;
            write_json(
                Some(analysis_summary_path),
                &with_run_contract(&measurement_summary, &run_contract)?,
            )?;
            write_json(
                Some(atom_viewer_data_path),
                &measurement_viewer_data,
            )?;
            let packet_value = serde_json::to_value(&measurement_packet)?;
            let view_model = build_measurement_view_model_v1(
                &packet_value,
                &normalized_archmap,
                &measurement_summary,
            );
            let mut view_model = with_run_contract(&view_model, &run_contract)?;
            view_model["inputDigests"]["measurementPacket"] = serde_json::json!({
                "path": "input:archsig-measurement-packet.json",
                "sha256": canonical_json_file_digest(&measurement_packet_path)?
            });
            write_json(Some(view_model_path), &view_model)?;
            write_json(
                Some(insight_report_path),
                &with_run_contract(&insight_report, &run_contract)?,
            )?;
            std::fs::write(insight_brief_path, insight_brief)?;
            write_json(
                Some(run_manifest_path),
                &serde_json::json!({
                    "schema": "archsig-run-manifest/v0.5.4",
                    "toolVersion": run_contract.tool_version.clone(),
                    "runId": run_contract.run_id.clone(),
                    "inputDigests": run_contract.input_digests.clone(),
                    "artifactDigests": {
                        "normalizedArchmap": {
                            "path": "normalized-archmap.json",
                            "sha256": canonical_json_file_digest(&normalized_archmap_path)?
                        },
                        "measurementPacket": {
                            "path": "archsig-measurement-packet.json",
                            "sha256": canonical_json_file_digest(&measurement_packet_path)?
                        }
                    },
                    "componentFingerprints": run_contract.component_fingerprints.clone(),
                    "commandName": "analyze",
                    "mode": "measurement",
                    "conclusionCode": null,
                    "archmapInputPath": archmap_input_ref,
                    "lawPolicyInputPath": law_policy_input_ref,
                    "lawSurfaceInputPath": law_surface_input_ref,
                    "measurementProfileInputPath": measurement_profile_input_ref,
                    "measurementProfileInputPaths": measurement_profile_input_refs,
                    "rawArtifactRetention": "omitted",
                    "generatedArtifacts": measurement_generated_artifacts,
                    "omittedArtifacts": [],
                    "artifactLinks": {
                        "measurementPacket": "archsig-measurement-packet.json",
                        "summary": "archsig-analysis-summary.json",
                        "insightReport": "archsig-insight-report.json",
                        "insightBrief": "archsig-insight-brief.md",
                        "viewerData": "archsig-atom-viewer-data.json",
                        "viewModel": "archsig-measurement-view-model.json"
                    },
                    "validationReports": {
                        "archmap": "archmap-validation.json",
                        "lawPolicy": "law-policy-validation.json",
                        "lawSurface": law_surface_preflight.as_ref().map(|_| "law-surface-validation.json"),
                        "analysis": "archsig-analysis-validation.json"
                    },
                    "rawArtifactPaths": null,
                    "validationResultSummary": {
                        "archmap": validation_result_summary(&archmap_preflight),
                        "lawPolicy": validation_result_summary(&law_policy_preflight),
                        "lawSurface": law_surface_preflight.as_ref().map(|(report, _)| validation_result_summary(report)),
                        "analysis": validation_result_summary_from_counts(
                            if packet_failed { "fail" } else { "pass" },
                            packet_failed_check_count,
                            packet_warning_check_count
                        )
                    },
                    "nonConclusions": [
                        "Finite-poset-site run manifest records the v0.5.4 AG measurement foundation artifacts.",
                        "Foundation packet rows are not completed AG invariant evaluator computation."
                    ]
                }),
            )?;
            Ok(if packet_failed {
                ExitCode::from(2)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::SchemaCatalog { out }) => {
            let catalog: SchemaVersionCatalogV0 = static_schema_version_catalog();
            write_json(out, &catalog)?;
            Ok(ExitCode::SUCCESS)
        }
        None => Err("ArchSig is ArchMap/LawPolicy/measurement-packet primary; use `archsig analyze` for the main analysis path.".into()),
    }
}
