//! `CheckedInputs` から `CheckedRobustnessTask` / `CheckedChevalleyTask` / `CheckedObservationTask` への lowering。

use super::lower::lower_point_domain;
use super::lower_expr::{conv_err, law_source_ref, lower_scalar_lit};
use super::lower_family::{lower_family, lower_param_named_polys, lower_shigure_origin};
use super::lower_morphism::{ensure_snapshot_exists, resolve_decl, select_named_decl};
use crate::ir::observation::{
    CandidateObservationDecl, CheckedObservationTask, LawReadoutSpec, ObservationTaskSpec,
};
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::robustness::{
    CandidateSelector, CheckedChevalleyTask, CheckedRobustnessTask, ChevalleyTaskSpec,
    RationalFiberProbe, RobustnessTaskSpec,
};
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::ir::validate::ValidationError;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{ShigureCandidateSelector, ShigureScalarLit};
use std::collections::{BTreeMap, BTreeSet};

fn lower_lit_vec(
    lits: &[ShigureScalarLit],
    coeff_domain: &CoeffDomain,
    context: &str,
) -> Result<Vec<ScalarLit>, ValidationError> {
    lits.iter()
        .enumerate()
        .map(|(i, lit)| lower_scalar_lit(lit, coeff_domain, &format!("{context}[{i}]")))
        .collect()
}

fn lower_candidate_selector(
    sel: &ShigureCandidateSelector,
    coeff_domain: &CoeffDomain,
    context: &str,
) -> Result<CandidateSelector, ValidationError> {
    match sel {
        ShigureCandidateSelector::ById(id) => Ok(CandidateSelector::ById(id.clone())),
        ShigureCandidateSelector::ByValues(pairs) => {
            let mut map = BTreeMap::new();
            for (k, lit) in pairs {
                map.insert(
                    k.clone(),
                    lower_scalar_lit(lit, coeff_domain, &format!("{context}.{k}"))?,
                );
            }
            Ok(CandidateSelector::ByValues(map))
        }
    }
}

pub(super) fn convert_robustness_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedRobustnessTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) = select_named_decl(&shigure.robustness_tasks, task_name, "shigure robustness")?;
    let fam_decl = resolve_decl(
        &shigure.families,
        &decl.family,
        "shigure family",
        &decl.name,
    )?;
    let (family, mut origins) = lower_family(fam_decl, shigure, archmap, snapshot_id)?;
    origins.insert(law_source_ref(&decl.name));

    let base_value = lower_lit_vec(
        &decl.base_value,
        &family.coeff_domain,
        &format!("{}.base_value", decl.name),
    )?;
    let fine_base_value = decl
        .fine_base_value
        .as_ref()
        .map(|v| {
            lower_lit_vec(
                v,
                &family.coeff_domain,
                &format!("{}.fine_base_value", decl.name),
            )
        })
        .transpose()?;
    let designated_candidate = decl
        .designated_candidate
        .as_ref()
        .map(|s| {
            lower_candidate_selector(
                s,
                &family.coeff_domain,
                &format!("{}.designated_candidate", decl.name),
            )
        })
        .transpose()?;

    CheckedRobustnessTask::validate(RobustnessTaskSpec {
        name: decl.name.clone(),
        family,
        point_domain: lower_point_domain(&decl.point_domain),
        base_value,
        designated_candidate,
        check_universal_ring: decl.check_universal_ring,
        fine_base_value,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: vec![],
        },
    })
}

pub(super) fn convert_chevalley_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedChevalleyTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) = select_named_decl(&shigure.chevalley_tasks, task_name, "shigure chevalley")?;
    let fam_decl = resolve_decl(
        &shigure.families,
        &decl.family,
        "shigure family",
        &decl.name,
    )?;
    let (family, mut origins) = lower_family(fam_decl, shigure, archmap, snapshot_id)?;
    origins.insert(law_source_ref(&decl.name));

    let base_value = decl
        .base_value
        .as_ref()
        .map(|v| {
            lower_lit_vec(
                v,
                &family.coeff_domain,
                &format!("{}.base_value", decl.name),
            )
        })
        .transpose()?;
    let designated_candidate = decl
        .designated_candidate
        .as_ref()
        .map(|s| {
            lower_candidate_selector(
                s,
                &family.coeff_domain,
                &format!("{}.designated_candidate", decl.name),
            )
        })
        .transpose()?;

    let mut probes = Vec::with_capacity(decl.probes.len());
    for p in &decl.probes {
        let mut u_assignments = BTreeMap::new();
        for (k, lit) in &p.u_assignments {
            u_assignments.insert(
                k.clone(),
                lower_scalar_lit(
                    lit,
                    &family.coeff_domain,
                    &format!("{}.probe.{}.{k}", decl.name, p.name),
                )?,
            );
        }
        let mut c_assignments = BTreeMap::new();
        for (k, lit) in &p.c_assignments {
            c_assignments.insert(
                k.clone(),
                lower_scalar_lit(
                    lit,
                    &family.coeff_domain,
                    &format!("{}.probe.{}.{k}", decl.name, p.name),
                )?,
            );
        }
        probes.push(RationalFiberProbe {
            name: p.name.clone(),
            u_assignments,
            c_assignments,
        });
    }

    CheckedChevalleyTask::validate(ChevalleyTaskSpec {
        name: decl.name.clone(),
        family,
        point_domain: lower_point_domain(&decl.point_domain),
        base_value,
        designated_candidate,
        rational_fiber_probes: probes,
        check_global_regular_section: decl.check_global_regular_section,
        check_universal_ring: decl.check_universal_ring,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: vec![],
        },
    })
}

pub(super) fn convert_observation_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedObservationTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) = select_named_decl(
        &shigure.observation_tasks,
        task_name,
        "shigure observations",
    )?;
    let fam_decl = resolve_decl(
        &shigure.families,
        &decl.family,
        "shigure family",
        &decl.name,
    )?;
    let (family, mut origins) = lower_family(fam_decl, shigure, archmap, snapshot_id)?;
    let task_ref = law_source_ref(&decl.name);
    origins.insert(task_ref.clone());

    let base_value = lower_lit_vec(
        &decl.base_value,
        &family.coeff_domain,
        &format!("{}.base_value", decl.name),
    )?;
    let u_set: BTreeSet<String> = family.realizations.u_vars.iter().cloned().collect();

    let mut observations = Vec::with_capacity(decl.observations.len());
    for obs in &decl.observations {
        let obs_refs = lower_shigure_origin(
            &obs.origin,
            archmap,
            &decl.name,
            &format!("{}.observe.{}", decl.name, obs.id),
        )?;
        let primary_origin: SourceRef = obs_refs[0].clone();
        for r in obs_refs {
            origins.insert(r);
        }
        let components = lower_param_named_polys(
            &obs.components,
            &family.coeff_domain,
            &u_set,
            &primary_origin,
            &format!("{}.observe.{}", decl.name, obs.id),
        )?;
        observations.push(CandidateObservationDecl {
            id: obs.id.clone(),
            components,
            cost: obs.cost.clone(),
            origin: primary_origin,
        });
    }

    let law_readout = decl
        .law_readout
        .as_ref()
        .map(|lr| {
            let components = lower_param_named_polys(
                &lr.components,
                &family.coeff_domain,
                &u_set,
                &task_ref,
                &format!("{}.law_readout.{}", decl.name, lr.name),
            )?;
            Ok::<_, ValidationError>(LawReadoutSpec {
                name: lr.name.clone(),
                components,
                provenance: Provenance {
                    origins: vec![task_ref.clone()],
                    clauses: vec![],
                },
            })
        })
        .transpose()?;

    CheckedObservationTask::validate(ObservationTaskSpec {
        name: decl.name.clone(),
        family,
        point_domain: lower_point_domain(&decl.point_domain),
        base_value,
        observations,
        law_readout,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: vec![],
        },
    })
}
