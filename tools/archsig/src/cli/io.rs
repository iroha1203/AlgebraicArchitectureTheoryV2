pub(crate) fn write_json<T: serde::Serialize>(
    out: Option<PathBuf>,
    value: &T,
) -> Result<(), Box<dyn Error>> {
    match out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent)?;
                }
            }
            let mut file = File::create(path)?;
            serde_json::to_writer_pretty(&mut file, value)?;
            writeln!(file)?;
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            serde_json::to_writer_pretty(&mut handle, value)?;
            writeln!(handle)?;
        }
    }
    Ok(())
}
pub(crate) fn read_json<T: serde::de::DeserializeOwned>(path: &PathBuf) -> Result<T, Box<dyn Error>> {
    Ok(serde_json::from_reader(File::open(path)?)?)
}

pub(crate) fn report_analyze_validation_failures(
    out_dir: &Path,
    archmap_validation: &ArchMapValidationReportV0,
    law_policy_validation: &LawPolicyValidationReportV0,
    analysis_validation: &ArchSigAnalysisPacketValidationReportV0,
) {
    if archmap_validation.summary.result != "fail"
        && law_policy_validation.summary.result != "fail"
        && analysis_validation.summary.result != "fail"
    {
        return;
    }

    eprintln!(
        "archsig analyze produced artifacts in {} but validation failed:",
        out_dir.display()
    );

    if archmap_validation.summary.result == "fail" {
        eprintln!(
            "  archmap-validation.json: fail ({} failed check(s))",
            archmap_validation.summary.failed_check_count
        );
        let archmap_groups = [
            (
                "sourceInventoryChecks",
                archmap_validation.source_inventory_checks.as_slice(),
            ),
            (
                "sourceRefChecks",
                archmap_validation.source_ref_checks.as_slice(),
            ),
            (
                "claimBoundaryChecks",
                archmap_validation.claim_boundary_checks.as_slice(),
            ),
            (
                "semanticCoverageChecks",
                archmap_validation.semantic_coverage_checks.as_slice(),
            ),
            (
                "formalPromotionGuardrailChecks",
                archmap_validation
                    .formal_promotion_guardrail_checks
                    .as_slice(),
            ),
            (
                "atomicObservationChecks",
                archmap_validation.atomic_observation_checks.as_slice(),
            ),
            (
                "responsibilityChecks",
                archmap_validation.responsibility_checks.as_slice(),
            ),
        ];
        for (group, checks) in archmap_groups {
            for check in checks.iter().filter(|check| check.result == "fail") {
                eprintln!(
                    "    - {group}/{}: {}",
                    check.id,
                    check.reason.as_deref().unwrap_or(&check.title)
                );
            }
        }
    }

    if law_policy_validation.summary.result == "fail" {
        eprintln!(
            "  law-policy-validation.json: fail ({} failed check(s))",
            law_policy_validation.summary.failed_check_count
        );
        for check in law_policy_validation
            .checks
            .iter()
            .filter(|check| check.result == "fail")
        {
            eprintln!(
                "    - checks/{}: {}",
                check.id,
                check.reason.as_deref().unwrap_or(&check.title)
            );
        }
    }

    if analysis_validation.summary.result == "fail" {
        eprintln!(
            "  archsig-analysis-validation.json: fail ({} failed check(s))",
            analysis_validation.summary.failed_check_count
        );
        for check in analysis_validation
            .checks
            .iter()
            .filter(|check| check.result == "fail")
        {
            eprintln!(
                "    - checks/{}: {}",
                check.id,
                check.reason.as_deref().unwrap_or(&check.title)
            );
        }
    }
}

pub(crate) fn read_optional_json(path: Option<&PathBuf>) -> Result<Option<serde_json::Value>, Box<dyn Error>> {
    path.map(read_json).transpose()
}

pub(crate) fn require_schema(
    document: &serde_json::Value,
    expected: &str,
    field_name: &str,
) -> Result<(), Box<dyn Error>> {
    let actual = document
        .get("schemaVersion")
        .or_else(|| document.get("schema"))
        .and_then(|value| value.as_str());
    if actual != Some(expected) {
        return Err(format!("{field_name} must have schemaVersion {expected}").into());
    }
    Ok(())
}
