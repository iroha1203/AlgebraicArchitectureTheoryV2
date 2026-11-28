//! `partial.rs` 用の開領域（`OpenDomainSpec`）検証ロジック。

use crate::ir::partial::{OpenDomainSpec, OpenOpTable, OpenRelTable};
use crate::ir::partial_validate::{validate_formula_refs, validate_typed_args};
use crate::ir::validate::{
    ValidationError, require_non_empty, validate_coeff_domain, validate_scalar_lit,
};
use std::collections::{BTreeMap, BTreeSet};

fn validate_open_carriers(
    carriers: &BTreeMap<String, Vec<String>>,
    scope: &str,
) -> Result<BTreeMap<String, BTreeSet<String>>, ValidationError> {
    let mut result = BTreeMap::new();
    for (s, elems) in carriers {
        require_non_empty(s, &format!("open_domain.{scope}_sort.name"))?;
        let mut set = BTreeSet::new();
        for e in elems {
            require_non_empty(e, &format!("open_domain.{scope}_sort.element"))?;
            if !set.insert(e.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "open_domain_element",
                    name: format!("{s}.{e}"),
                });
            }
        }
        result.insert(s.clone(), set);
    }
    Ok(result)
}

fn validate_open_op_tables<'a>(
    ops: &'a [OpenOpTable],
    carriers: &BTreeMap<String, BTreeSet<String>>,
    scope: &str,
) -> Result<BTreeMap<&'a str, &'a OpenOpTable>, ValidationError> {
    let mut map = BTreeMap::new();
    for op in ops {
        require_non_empty(&op.name, &format!("open_domain.{scope}_op.name"))?;
        for s in op.arg_sorts.iter().chain(std::iter::once(&op.out_sort)) {
            if !carriers.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: s.clone(),
                    context: format!("open_domain {scope}_op `{}`", op.name),
                });
            }
        }
        if map.insert(op.name.as_str(), op).is_some() {
            return Err(ValidationError::DuplicateDecl {
                kind: "open_domain_op",
                name: op.name.clone(),
            });
        }
        for (args, out_opt) in &op.entries {
            validate_typed_args(
                args,
                &op.arg_sorts,
                carriers,
                &format!("open_domain.{scope}.{}", op.name),
            )?;
            if let Some(out) = out_opt
                && !carriers[&op.out_sort].contains(out)
            {
                return Err(ValidationError::UnknownRef {
                    kind: "occurrence",
                    name: out.clone(),
                    context: format!("open_domain {scope}_op `{}` output", op.name),
                });
            }
        }
    }
    Ok(map)
}

fn validate_open_rel_tables<'a>(
    rels: &'a [OpenRelTable],
    carriers: &BTreeMap<String, BTreeSet<String>>,
    scope: &str,
) -> Result<BTreeMap<&'a str, &'a OpenRelTable>, ValidationError> {
    let mut map = BTreeMap::new();
    for rel in rels {
        require_non_empty(&rel.name, &format!("open_domain.{scope}_rel.name"))?;
        for s in &rel.arg_sorts {
            if !carriers.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: s.clone(),
                    context: format!("open_domain {scope}_rel `{}`", rel.name),
                });
            }
        }
        if map.insert(rel.name.as_str(), rel).is_some() {
            return Err(ValidationError::DuplicateDecl {
                kind: "open_domain_rel",
                name: rel.name.clone(),
            });
        }
        for args in &rel.entries {
            validate_typed_args(
                args,
                &rel.arg_sorts,
                carriers,
                &format!("open_domain.{scope}.{}", rel.name),
            )?;
        }
    }
    Ok(map)
}

pub(super) fn validate_open_domain(od: &OpenDomainSpec) -> Result<(), ValidationError> {
    let amb_carriers = validate_open_carriers(&od.ambient_carriers, "ambient")?;
    let sub_carriers = validate_open_carriers(&od.substructure_carriers, "substructure")?;

    for (s, sub_set) in &sub_carriers {
        let Some(amb_set) = amb_carriers.get(s) else {
            return Err(ValidationError::UnknownRef {
                kind: "ambient_sort",
                name: s.clone(),
                context: "open_domain".to_owned(),
            });
        };
        for e in sub_set {
            if !amb_set.contains(e) {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "substructure element `{e}` in sort `{s}` is not contained in ambient carrier"
                    ),
                });
            }
        }
    }
    for s in amb_carriers.keys() {
        if !sub_carriers.contains_key(s) {
            return Err(ValidationError::UnknownRef {
                kind: "substructure_sort",
                name: s.clone(),
                context: "open_domain".to_owned(),
            });
        }
    }

    let sub_ops = validate_open_op_tables(&od.substructure_ops, &sub_carriers, "substructure")?;
    let amb_ops = validate_open_op_tables(&od.ambient_ops, &amb_carriers, "ambient")?;
    for (name, sub_op) in &sub_ops {
        let Some(amb_op) = amb_ops.get(name) else {
            return Err(ValidationError::UnknownRef {
                kind: "ambient_op",
                name: (*name).to_owned(),
                context: "open_domain".to_owned(),
            });
        };
        if sub_op.arg_sorts != amb_op.arg_sorts || sub_op.out_sort != amb_op.out_sort {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "open_domain op `{name}` signature differs between substructure and ambient"
                ),
            });
        }
    }
    for name in amb_ops.keys() {
        if !sub_ops.contains_key(name) {
            return Err(ValidationError::UnknownRef {
                kind: "substructure_op",
                name: (*name).to_owned(),
                context: "open_domain".to_owned(),
            });
        }
    }

    let sub_rels = validate_open_rel_tables(&od.substructure_rels, &sub_carriers, "substructure")?;
    let amb_rels = validate_open_rel_tables(&od.ambient_rels, &amb_carriers, "ambient")?;
    for (name, sub_rel) in &sub_rels {
        let Some(amb_rel) = amb_rels.get(name) else {
            return Err(ValidationError::UnknownRef {
                kind: "ambient_rel",
                name: (*name).to_owned(),
                context: "open_domain".to_owned(),
            });
        };
        if sub_rel.arg_sorts != amb_rel.arg_sorts {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "open_domain rel `{name}` signature differs between substructure and ambient"
                ),
            });
        }
    }
    for name in amb_rels.keys() {
        if !sub_rels.contains_key(name) {
            return Err(ValidationError::UnknownRef {
                kind: "substructure_rel",
                name: (*name).to_owned(),
                context: "open_domain".to_owned(),
            });
        }
    }

    for fc in &od.fiber_checks {
        if !sub_ops.contains_key(fc.op_name.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "operation",
                name: fc.op_name.clone(),
                context: "open_domain.fiber_check".to_owned(),
            });
        }
        let Some(amb_op) = amb_ops.get(fc.op_name.as_str()) else {
            return Err(ValidationError::UnknownRef {
                kind: "operation",
                name: fc.op_name.clone(),
                context: "open_domain.fiber_check".to_owned(),
            });
        };
        if !amb_carriers.contains_key(&fc.arg_sort) {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: fc.arg_sort.clone(),
                context: "open_domain.fiber_check.arg_sort".to_owned(),
            });
        }
        let Some(target_set) = sub_carriers.get(&fc.target_sort) else {
            return Err(ValidationError::UnknownRef {
                kind: "substructure_sort",
                name: fc.target_sort.clone(),
                context: "open_domain.fiber_check.target_sort".to_owned(),
            });
        };
        if amb_op.arg_sorts.as_slice() != [fc.arg_sort.as_str()]
            || amb_op.out_sort != fc.target_sort
        {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "open_domain fiber_check op `{}` must have unary signature `{}` -> `{}`",
                    fc.op_name, fc.arg_sort, fc.target_sort
                ),
            });
        }
        for t in &fc.known_targets {
            if !target_set.contains(t) {
                return Err(ValidationError::UnknownRef {
                    kind: "occurrence",
                    name: t.clone(),
                    context: "open_domain.fiber_check.known_targets".to_owned(),
                });
            }
        }
    }

    require_non_empty(&od.positive_or_law.name, "open_domain.positive_or_law.name")?;
    let amb_op_arities: BTreeMap<&str, usize> = amb_ops
        .iter()
        .map(|(&k, op)| (k, op.arg_sorts.len()))
        .collect();
    let amb_rel_arities: BTreeMap<&str, usize> = amb_rels
        .iter()
        .map(|(&k, rel)| (k, rel.arg_sorts.len()))
        .collect();
    let empty_slots = BTreeSet::new();
    if let Some(ant) = &od.positive_or_law.antecedent {
        validate_formula_refs(
            ant,
            &amb_op_arities,
            &amb_rel_arities,
            &amb_carriers,
            &empty_slots,
        )?;
    }
    validate_formula_refs(
        &od.positive_or_law.conclusion,
        &amb_op_arities,
        &amb_rel_arities,
        &amb_carriers,
        &empty_slots,
    )?;

    if let Some(ar) = &od.affine_restriction {
        validate_coeff_domain(&ar.coeff_domain, "open_domain.affine_restriction")?;
        if ar.m_matrix.len() != ar.b_rhs.len() {
            return Err(ValidationError::ArityMismatch {
                context: "affine_restriction m_matrix/b_rhs".to_owned(),
                expected: ar.m_matrix.len(),
                actual: ar.b_rhs.len(),
            });
        }
        for row in &ar.m_matrix {
            if row.len() != ar.num_vars {
                return Err(ValidationError::ArityMismatch {
                    context: "affine_restriction m_matrix cols".to_owned(),
                    expected: ar.num_vars,
                    actual: row.len(),
                });
            }
            for v in row {
                validate_scalar_lit(v, &ar.coeff_domain, "affine_restriction.M")?;
            }
        }
        for v in &ar.b_rhs {
            validate_scalar_lit(v, &ar.coeff_domain, "affine_restriction.b")?;
        }
        for row in &ar.r_matrix {
            if row.len() != ar.num_vars {
                return Err(ValidationError::ArityMismatch {
                    context: "affine_restriction r_matrix cols".to_owned(),
                    expected: ar.num_vars,
                    actual: row.len(),
                });
            }
            for v in row {
                validate_scalar_lit(v, &ar.coeff_domain, "affine_restriction.R")?;
            }
        }
    }
    Ok(())
}
