//! `CheckedInputs` から `CheckedOccurrenceTask` への lowering（Phase 5 / 第17章）。

use super::lower_expr::{conv_err, resolve_observed_symbolic};
use super::lower_morphism::{ensure_snapshot_exists, select_named_decl};
use super::lower_phase4_lift_artin::lower_p4_origins;
use crate::algebra::congruence::{OpOutputRecord, PredicateRecord, PredicateRecordKind};
use crate::ir::occurrence::{
    CheckedOccurrenceTask, OccurrenceInitialReadoutSpec, OccurrenceOpSpec, OccurrenceReadingSpec,
    OccurrenceRelSpec, OccurrenceSortSpec, OccurrenceTaskSpec,
};
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::validate::ValidationError;
use archsig_input::archmap::CheckedArchMap;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{
    OccurrencePredKind, ShigureOccurrenceReading, ShigureSymbolicValue,
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn lower_symbolic_value(
    val: &ShigureSymbolicValue,
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    fallback_ref: &SourceRef,
    slot_label: &str,
    origins: &mut BTreeSet<SourceRef>,
    missing_slots: &mut Vec<String>,
) -> Result<Option<String>, ValidationError> {
    match val {
        ShigureSymbolicValue::Literal(s) => Ok(Some(s.clone())),
        ShigureSymbolicValue::ObservedField { entity, field, .. } => {
            let (resolved, refs) =
                resolve_observed_symbolic(archmap, snapshot_id, entity, field, fallback_ref)?;
            for r in refs {
                origins.insert(r);
            }
            if resolved.is_none() {
                missing_slots.push(if field.starts_with(&format!("{entity}.")) {
                    field.clone()
                } else {
                    format!("{entity}.{field}")
                });
            }
            Ok(resolved)
        }
        ShigureSymbolicValue::Missing => {
            missing_slots.push(slot_label.to_owned());
            Ok(None)
        }
    }
}

fn lower_readings(
    raw: &[ShigureOccurrenceReading],
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    fallback_ref: &SourceRef,
    decl_name: &str,
    origins: &mut BTreeSet<SourceRef>,
    missing_slots: &mut Vec<String>,
) -> Result<Vec<OccurrenceReadingSpec>, ValidationError> {
    let mut out = Vec::with_capacity(raw.len());
    for r in raw {
        let mut values = BTreeMap::new();
        for (elem, val_opt) in &r.values {
            let lowered = match val_opt {
                Some(v) => lower_symbolic_value(
                    v,
                    archmap,
                    snapshot_id,
                    fallback_ref,
                    &format!("{decl_name}.{}.{elem}", r.name),
                    origins,
                    missing_slots,
                )?,
                None => None,
            };
            values.insert(elem.clone(), lowered);
        }
        out.push(OccurrenceReadingSpec {
            name: r.name.clone(),
            sort: r.sort.clone(),
            values,
        });
    }
    Ok(out)
}

pub(super) fn convert_occurrence_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedOccurrenceTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) = select_named_decl(&shigure.occurrence_tasks, task_name, "shigure occurrence")?;
    let (mut origins, primary_ref) =
        lower_p4_origins(&decl.origins, archmap, &decl.name, &decl.name)?;
    let mut missing_slots = Vec::new();

    let sorts = decl
        .sorts
        .iter()
        .map(|s| OccurrenceSortSpec {
            name: s.name.clone(),
            elements: s.elements.clone(),
            is_fixed_value: s.is_fixed_value,
        })
        .collect();

    let operations = decl
        .operations
        .iter()
        .map(|op| OccurrenceOpSpec {
            name: op.name.clone(),
            arg_sorts: op.arg_sorts.clone(),
            out_sort: op.out_sort.clone(),
            is_total: op.is_total,
        })
        .collect();

    let relations = decl
        .relations
        .iter()
        .map(|rel| OccurrenceRelSpec {
            name: rel.name.clone(),
            arg_sorts: rel.arg_sorts.clone(),
        })
        .collect();

    let mut op_records = Vec::with_capacity(decl.op_records.len());
    for (idx, rec) in decl.op_records.iter().enumerate() {
        if let Some(output) = lower_symbolic_value(
            &rec.output,
            archmap,
            snapshot_id,
            &primary_ref,
            &format!("{}.op_record.{}.{idx}", decl.name, rec.op_name),
            &mut origins,
            &mut missing_slots,
        )? {
            op_records.push(OpOutputRecord {
                op_name: rec.op_name.clone(),
                arg_sorts: rec.arg_sorts.clone(),
                out_sort: rec.out_sort.clone(),
                args: rec.args.clone(),
                output,
                positive: true,
            });
        }
    }

    let pred_records = decl
        .pred_records
        .iter()
        .map(|rec| PredicateRecord {
            name: rec.name.clone(),
            kind: match rec.kind {
                OccurrencePredKind::Domain => PredicateRecordKind::Domain,
                OccurrencePredKind::Relation => PredicateRecordKind::Relation,
            },
            arg_sorts: rec.arg_sorts.clone(),
            args: rec.args.clone(),
            positive: rec.holds,
        })
        .collect();

    let base_readings = lower_readings(
        &decl.base_readings,
        archmap,
        snapshot_id,
        &primary_ref,
        &decl.name,
        &mut origins,
        &mut missing_slots,
    )?;
    let explicit_contexts = lower_readings(
        &decl.explicit_contexts,
        archmap,
        snapshot_id,
        &primary_ref,
        &decl.name,
        &mut origins,
        &mut missing_slots,
    )?;

    let mut initial_readouts = Vec::with_capacity(decl.initial_readouts.len());
    for ro in &decl.initial_readouts {
        let mut values = BTreeMap::new();
        for (elem, sym) in &ro.values {
            let slot_name = format!("{}.initial_readout.{}.{elem}", decl.name, ro.sort);
            let Some(val) = lower_symbolic_value(
                sym,
                archmap,
                snapshot_id,
                &primary_ref,
                &slot_name,
                &mut origins,
                &mut missing_slots,
            )?
            else {
                return Err(conv_err(format!(
                    "initial_readout for `{}.{elem}` has unobserved value",
                    ro.sort
                )));
            };
            values.insert(elem.clone(), val);
        }
        initial_readouts.push(OccurrenceInitialReadoutSpec {
            sort: ro.sort.clone(),
            values,
        });
    }

    CheckedOccurrenceTask::validate(OccurrenceTaskSpec {
        name: decl.name.clone(),
        sorts,
        operations,
        relations,
        identity_requests: decl.identity_requests.clone(),
        op_records,
        pred_records,
        base_readings,
        context_closed_17_5: decl.context_closed_17_5,
        explicit_contexts,
        preserve_full_domains: decl.preserve_full_domains.clone(),
        initial_readouts,
        provenance: Provenance::new(origins.into_iter().collect(), Vec::new()),
        max_congruence_steps: decl.max_congruence_steps,
        max_partitions: decl.max_partitions,
        undeclared_unobserved_slots: missing_slots,
    })
}
