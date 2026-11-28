//! `partial.rs` 用の部分提示・開領域・定量化階層 IR の検証ロジック。

use crate::ir::partial::{
    AffinePartialPresentation, BackgroundConstraint, CheckedPartialTask, FinitePartialPresentation,
    OpenDomainSpec, PartialEvalLawSpec, PartialFormula, PartialOpSignature, PartialPredSignature,
    PartialRecordKind, PartialRepresentation, PartialTaskSpec, PartialTerm, PartialTruth,
    PartialValue, QuantifierHierarchySpec,
};
use crate::ir::validate::{
    ValidationError, require_non_empty, validate_coeff_domain, validate_provenance,
    validate_scalar_lit,
};
use std::collections::{BTreeMap, BTreeSet};

pub fn validate_partial_task(spec: PartialTaskSpec) -> Result<CheckedPartialTask, ValidationError> {
    require_non_empty(&spec.name, "partial.name")?;
    validate_provenance(&spec.provenance, &format!("partial `{}`", spec.name))?;

    let mut seen_law_names = BTreeSet::new();
    for law in &spec.eval_laws {
        require_non_empty(&law.name, "partial.eval_law.name")?;
        if !seen_law_names.insert(law.name.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "partial_eval_law",
                name: law.name.clone(),
            });
        }
    }

    match &spec.representation {
        PartialRepresentation::FiniteTable(fin) => validate_finite_partial(fin, &spec.eval_laws)?,
        PartialRepresentation::Affine(aff) => validate_affine_partial(aff)?,
        PartialRepresentation::UnsupportedClass { description } => {
            require_non_empty(description, "partial.unsupported_class.description")?;
        }
    }

    if let Some(q) = &spec.quantifier_spec {
        validate_quantifier_spec(q)?;
    }

    if let Some(od) = &spec.open_domain {
        validate_open_domain(od)?;
    }

    Ok(CheckedPartialTask {
        name: spec.name,
        representation: spec.representation,
        eval_laws: spec.eval_laws,
        quantifier_spec: spec.quantifier_spec,
        open_domain: spec.open_domain,
        provenance: spec.provenance,
        undeclared_unobserved_slots: spec.undeclared_unobserved_slots,
    })
}

fn validate_quantifier_spec(q: &QuantifierHierarchySpec) -> Result<(), ValidationError> {
    if q.candidates.is_empty() && q.completions.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: "quantifier_spec cannot have both empty candidates and empty completions"
                .to_owned(),
        });
    }
    let mut cand_set = BTreeSet::new();
    for c in &q.candidates {
        require_non_empty(c, "partial.quantifier.candidate")?;
        if !cand_set.insert(c.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "quantifier_candidate",
                name: c.clone(),
            });
        }
    }
    let mut comp_ids = BTreeSet::new();
    for comp in &q.completions {
        require_non_empty(&comp.id, "partial.quantifier.completion.id")?;
        if !comp_ids.insert(comp.id.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "quantifier_completion",
                name: comp.id.clone(),
            });
        }
        for vc in &comp.valid_candidates {
            if !cand_set.contains(vc.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "candidate",
                    name: vc.clone(),
                    context: format!("quantifier completion `{}`", comp.id),
                });
            }
        }
    }
    Ok(())
}

fn validate_finite_partial(
    fin: &FinitePartialPresentation,
    eval_laws: &[PartialEvalLawSpec],
) -> Result<(), ValidationError> {
    let mut sort_elems: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (s, elems) in &fin.sorts {
        require_non_empty(s, "partial.sort.name")?;
        let mut set = BTreeSet::new();
        for e in elems {
            require_non_empty(e, "partial.sort.element")?;
            if !set.insert(e.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "partial_sort_element",
                    name: format!("{s}.{e}"),
                });
            }
        }
        sort_elems.insert(s.clone(), set);
    }

    let mut slot_sorts: BTreeMap<String, String> = BTreeMap::new();
    let mut slot_domains: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for slot in &fin.slots {
        require_non_empty(&slot.name, "partial.slot.name")?;
        if slot_sorts.contains_key(&slot.name) {
            return Err(ValidationError::DuplicateDecl {
                kind: "partial_slot",
                name: slot.name.clone(),
            });
        }
        let Some(carrier) = sort_elems.get(&slot.sort) else {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: slot.sort.clone(),
                context: format!("slot `{}`", slot.name),
            });
        };
        if slot.domain_values.is_empty() {
            return Err(ValidationError::ConversionError {
                detail: format!("slot `{}` has empty domain_values", slot.name),
            });
        }
        let mut dom_set = BTreeSet::new();
        for v in &slot.domain_values {
            if !carrier.contains(v) {
                return Err(ValidationError::UnknownRef {
                    kind: "occurrence",
                    name: v.clone(),
                    context: format!("slot `{}` domain_values (sort `{}`)", slot.name, slot.sort),
                });
            }
            if !dom_set.insert(v.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "slot_domain_value",
                    name: format!("{}.{v}", slot.name),
                });
            }
        }
        slot_sorts.insert(slot.name.clone(), slot.sort.clone());
        slot_domains.insert(slot.name.clone(), dom_set);
    }

    let mut ops_map: BTreeMap<&str, &PartialOpSignature> = BTreeMap::new();
    for op in &fin.operations {
        require_non_empty(&op.name, "partial.operation.name")?;
        if ops_map.insert(op.name.as_str(), op).is_some() {
            return Err(ValidationError::DuplicateDecl {
                kind: "partial_operation",
                name: op.name.clone(),
            });
        }
        for s in &op.arg_sorts {
            if !sort_elems.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: s.clone(),
                    context: format!("partial operation `{}`", op.name),
                });
            }
        }
        if !sort_elems.contains_key(&op.out_sort) {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: op.out_sort.clone(),
                context: format!("partial operation `{}`", op.name),
            });
        }
    }

    let mut rels_map: BTreeMap<&str, &PartialPredSignature> = BTreeMap::new();
    for rel in &fin.relations {
        require_non_empty(&rel.name, "partial.relation.name")?;
        if rels_map.insert(rel.name.as_str(), rel).is_some() {
            return Err(ValidationError::DuplicateDecl {
                kind: "partial_relation",
                name: rel.name.clone(),
            });
        }
        for s in &rel.arg_sorts {
            if !sort_elems.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: s.clone(),
                    context: format!("partial relation `{}`", rel.name),
                });
            }
        }
    }

    for bg in &fin.background_constraints {
        match bg {
            BackgroundConstraint::SlotEquality(a, b) | BackgroundConstraint::SlotNotEqual(a, b) => {
                let sa = slot_sorts
                    .get(a)
                    .ok_or_else(|| ValidationError::UnknownRef {
                        kind: "slot",
                        name: a.clone(),
                        context: "partial.background_constraint".to_owned(),
                    })?;
                let sb = slot_sorts
                    .get(b)
                    .ok_or_else(|| ValidationError::UnknownRef {
                        kind: "slot",
                        name: b.clone(),
                        context: "partial.background_constraint".to_owned(),
                    })?;
                if sa != sb {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "background constraint between slots `{a}` ({sa}) and `{b}` ({sb}) has mismatched sorts"
                        ),
                    });
                }
            }
            BackgroundConstraint::OperationInjective(op)
            | BackgroundConstraint::OperationSurjective(op) => {
                if !ops_map.contains_key(op.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "operation",
                        name: op.clone(),
                        context: "partial.background_constraint".to_owned(),
                    });
                }
            }
        }
    }

    let mut rec_ids = BTreeSet::new();
    for rec in &fin.records {
        require_non_empty(&rec.id, "partial.record.id")?;
        if !rec_ids.insert(rec.id.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "partial_record",
                name: rec.id.clone(),
            });
        }
        match &rec.kind {
            PartialRecordKind::OpValue {
                op_name,
                args,
                value,
            } => {
                let op =
                    ops_map
                        .get(op_name.as_str())
                        .ok_or_else(|| ValidationError::UnknownRef {
                            kind: "operation",
                            name: op_name.clone(),
                            context: format!("record `{}`", rec.id),
                        })?;
                validate_typed_args(args, &op.arg_sorts, &sort_elems, &rec.id)?;
                match value {
                    PartialValue::Known(v) => {
                        if !sort_elems[&op.out_sort].contains(v) {
                            return Err(ValidationError::UnknownRef {
                                kind: "occurrence",
                                name: v.clone(),
                                context: format!("record `{}` out_sort `{}`", rec.id, op.out_sort),
                            });
                        }
                    }
                    PartialValue::ExplicitAbsent => {}
                    PartialValue::UnobservedSlot(s) => {
                        let ss = slot_sorts
                            .get(s)
                            .ok_or_else(|| ValidationError::UnknownRef {
                                kind: "slot",
                                name: s.clone(),
                                context: format!("record `{}`", rec.id),
                            })?;
                        if ss != &op.out_sort {
                            return Err(ValidationError::ConversionError {
                                detail: format!(
                                    "record `{}` slot `{s}` has sort `{ss}`, expected `{}`",
                                    rec.id, op.out_sort
                                ),
                            });
                        }
                    }
                }
            }
            PartialRecordKind::OpDomain {
                op_name,
                args,
                defined,
            } => {
                let op =
                    ops_map
                        .get(op_name.as_str())
                        .ok_or_else(|| ValidationError::UnknownRef {
                            kind: "operation",
                            name: op_name.clone(),
                            context: format!("record `{}`", rec.id),
                        })?;
                validate_typed_args(args, &op.arg_sorts, &sort_elems, &rec.id)?;
                if let PartialTruth::UnobservedSlot(s) = defined
                    && !slot_sorts.contains_key(s)
                {
                    return Err(ValidationError::UnknownRef {
                        kind: "slot",
                        name: s.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
            }
            PartialRecordKind::OpGraph {
                op_name,
                args,
                output,
                present,
            } => {
                let op =
                    ops_map
                        .get(op_name.as_str())
                        .ok_or_else(|| ValidationError::UnknownRef {
                            kind: "operation",
                            name: op_name.clone(),
                            context: format!("record `{}`", rec.id),
                        })?;
                validate_typed_args(args, &op.arg_sorts, &sort_elems, &rec.id)?;
                if !sort_elems[&op.out_sort].contains(output) {
                    return Err(ValidationError::UnknownRef {
                        kind: "occurrence",
                        name: output.clone(),
                        context: format!("record `{}` op_graph output", rec.id),
                    });
                }
                if let PartialTruth::UnobservedSlot(s) = present
                    && !slot_sorts.contains_key(s)
                {
                    return Err(ValidationError::UnknownRef {
                        kind: "slot",
                        name: s.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
            }
            PartialRecordKind::Relation {
                rel_name,
                args,
                holds,
            } => {
                let rel =
                    rels_map
                        .get(rel_name.as_str())
                        .ok_or_else(|| ValidationError::UnknownRef {
                            kind: "relation",
                            name: rel_name.clone(),
                            context: format!("record `{}`", rec.id),
                        })?;
                validate_typed_args(args, &rel.arg_sorts, &sort_elems, &rec.id)?;
                if let PartialTruth::UnobservedSlot(s) = holds
                    && !slot_sorts.contains_key(s)
                {
                    return Err(ValidationError::UnknownRef {
                        kind: "slot",
                        name: s.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                }
            }
            PartialRecordKind::SlotAssignment { slot, value } => {
                let Some(dom) = slot_domains.get(slot) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "slot",
                        name: slot.clone(),
                        context: format!("record `{}`", rec.id),
                    });
                };
                if !dom.contains(value) {
                    return Err(ValidationError::UnknownRef {
                        kind: "occurrence",
                        name: value.clone(),
                        context: format!("record `{}` slot `{slot}` assignment", rec.id),
                    });
                }
            }
        }
    }

    let op_arities: BTreeMap<&str, usize> = ops_map
        .iter()
        .map(|(&k, v)| (k, v.arg_sorts.len()))
        .collect();
    let rel_arities: BTreeMap<&str, usize> = rels_map
        .iter()
        .map(|(&k, v)| (k, v.arg_sorts.len()))
        .collect();
    let sort_names: BTreeSet<&str> = sort_elems.keys().map(String::as_str).collect();
    let slot_name_set: BTreeSet<&str> = slot_sorts.keys().map(String::as_str).collect();

    for law in eval_laws {
        if let Some(ant) = &law.antecedent {
            validate_formula_refs(ant, &op_arities, &rel_arities, &sort_names, &slot_name_set)?;
        }
        validate_formula_refs(
            &law.conclusion,
            &op_arities,
            &rel_arities,
            &sort_names,
            &slot_name_set,
        )?;
    }

    Ok(())
}

fn validate_typed_args(
    args: &[String],
    arg_sorts: &[String],
    sort_elems: &BTreeMap<String, BTreeSet<String>>,
    rec_id: &str,
) -> Result<(), ValidationError> {
    if args.len() != arg_sorts.len() {
        return Err(ValidationError::ArityMismatch {
            context: format!("partial record `{rec_id}`"),
            expected: arg_sorts.len(),
            actual: args.len(),
        });
    }
    for (s, a) in arg_sorts.iter().zip(args) {
        if !sort_elems[s].contains(a) {
            return Err(ValidationError::UnknownRef {
                kind: "occurrence",
                name: a.clone(),
                context: format!("partial record `{rec_id}` sort `{s}`"),
            });
        }
    }
    Ok(())
}

fn validate_formula_refs(
    formula: &PartialFormula,
    op_arities: &BTreeMap<&str, usize>,
    rel_arities: &BTreeMap<&str, usize>,
    sorts: &BTreeSet<&str>,
    slots: &BTreeSet<&str>,
) -> Result<(), ValidationError> {
    match formula {
        PartialFormula::Eq(a, b) => {
            validate_term_refs(a, op_arities, slots)?;
            validate_term_refs(b, op_arities, slots)
        }
        PartialFormula::Rel { rel_name, args } => {
            let Some(&arity) = rel_arities.get(rel_name.as_str()) else {
                return Err(ValidationError::UnknownRef {
                    kind: "relation",
                    name: rel_name.clone(),
                    context: "partial.formula".to_owned(),
                });
            };
            if args.len() != arity {
                return Err(ValidationError::ArityMismatch {
                    context: format!("formula relation `{rel_name}`"),
                    expected: arity,
                    actual: args.len(),
                });
            }
            for a in args {
                validate_term_refs(a, op_arities, slots)?;
            }
            Ok(())
        }
        PartialFormula::Graph {
            op_name,
            args,
            output,
        } => {
            let Some(&arity) = op_arities.get(op_name.as_str()) else {
                return Err(ValidationError::UnknownRef {
                    kind: "operation",
                    name: op_name.clone(),
                    context: "partial.formula".to_owned(),
                });
            };
            if args.len() != arity {
                return Err(ValidationError::ArityMismatch {
                    context: format!("formula graph `{op_name}`"),
                    expected: arity,
                    actual: args.len(),
                });
            }
            for a in args {
                validate_term_refs(a, op_arities, slots)?;
            }
            validate_term_refs(output, op_arities, slots)
        }
        PartialFormula::Defined { op_name, args } => {
            let Some(&arity) = op_arities.get(op_name.as_str()) else {
                return Err(ValidationError::UnknownRef {
                    kind: "operation",
                    name: op_name.clone(),
                    context: "partial.formula".to_owned(),
                });
            };
            if args.len() != arity {
                return Err(ValidationError::ArityMismatch {
                    context: format!("formula defined `{op_name}`"),
                    expected: arity,
                    actual: args.len(),
                });
            }
            for a in args {
                validate_term_refs(a, op_arities, slots)?;
            }
            Ok(())
        }
        PartialFormula::Not(inner) => {
            validate_formula_refs(inner, op_arities, rel_arities, sorts, slots)
        }
        PartialFormula::Exists { sort, body, .. } | PartialFormula::Forall { sort, body, .. } => {
            if !sorts.contains(sort.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: sort.clone(),
                    context: "partial.formula quantifier".to_owned(),
                });
            }
            validate_formula_refs(body, op_arities, rel_arities, sorts, slots)
        }
        PartialFormula::And(list) | PartialFormula::Or(list) => {
            for f in list {
                validate_formula_refs(f, op_arities, rel_arities, sorts, slots)?;
            }
            Ok(())
        }
    }
}

fn validate_term_refs(
    term: &PartialTerm,
    op_arities: &BTreeMap<&str, usize>,
    slots: &BTreeSet<&str>,
) -> Result<(), ValidationError> {
    match term {
        PartialTerm::Var(_) | PartialTerm::Const(_) => Ok(()),
        PartialTerm::Slot(s) => {
            if !slots.contains(s.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "slot",
                    name: s.clone(),
                    context: "partial.term".to_owned(),
                });
            }
            Ok(())
        }
        PartialTerm::App { op_name, args } => {
            let Some(&arity) = op_arities.get(op_name.as_str()) else {
                return Err(ValidationError::UnknownRef {
                    kind: "operation",
                    name: op_name.clone(),
                    context: "partial.term".to_owned(),
                });
            };
            if args.len() != arity {
                return Err(ValidationError::ArityMismatch {
                    context: format!("term app `{op_name}`"),
                    expected: arity,
                    actual: args.len(),
                });
            }
            for a in args {
                validate_term_refs(a, op_arities, slots)?;
            }
            Ok(())
        }
        PartialTerm::Let { bound, body, .. } => {
            validate_term_refs(bound, op_arities, slots)?;
            validate_term_refs(body, op_arities, slots)
        }
        PartialTerm::BinOp { lhs, rhs, .. } => {
            validate_term_refs(lhs, op_arities, slots)?;
            validate_term_refs(rhs, op_arities, slots)
        }
    }
}

fn validate_affine_partial(aff: &AffinePartialPresentation) -> Result<(), ValidationError> {
    validate_coeff_domain(&aff.coeff_domain, "partial.affine")?;
    let mut coord_set = BTreeSet::new();
    for c in &aff.coord_names {
        require_non_empty(c, "partial.affine.coord_name")?;
        if !coord_set.insert(c.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "affine_coord",
                name: c.clone(),
            });
        }
    }
    let n = aff.coord_names.len();
    if aff.x0.len() != n || aff.direction_t.len() != n {
        return Err(ValidationError::ArityMismatch {
            context: "partial.affine x0/direction_t rows".to_owned(),
            expected: n,
            actual: aff.x0.len(),
        });
    }
    let t_cols = aff.direction_t.first().map_or(0, Vec::len);
    for row in &aff.direction_t {
        if row.len() != t_cols {
            return Err(ValidationError::ArityMismatch {
                context: "partial.affine direction_t column count".to_owned(),
                expected: t_cols,
                actual: row.len(),
            });
        }
        for v in row {
            validate_scalar_lit(v, &aff.coeff_domain, "partial.affine.T")?;
        }
    }
    for v in &aff.x0 {
        validate_scalar_lit(v, &aff.coeff_domain, "partial.affine.x0")?;
    }
    let mut bg_rec_ids = BTreeSet::new();
    for (id, row, rhs) in aff.background_rows.iter().chain(&aff.record_rows) {
        require_non_empty(id, "partial.affine.row.id")?;
        if !bg_rec_ids.insert(id.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "affine_row",
                name: id.clone(),
            });
        }
        validate_affine_row(id, row, rhs, n, &aff.coeff_domain)?;
    }
    let mut eq_ids = BTreeSet::new();
    for (id, row, rhs) in &aff.eval_equations {
        require_non_empty(id, "partial.affine.eval_equation.id")?;
        if !eq_ids.insert(id.as_str()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "affine_eval_equation",
                name: id.clone(),
            });
        }
        validate_affine_row(id, row, rhs, n, &aff.coeff_domain)?;
    }
    Ok(())
}

fn validate_affine_row(
    id: &str,
    row: &[crate::ir::term::ScalarLit],
    rhs: &crate::ir::term::ScalarLit,
    n: usize,
    domain: &crate::ir::term::CoeffDomain,
) -> Result<(), ValidationError> {
    if row.len() != n {
        return Err(ValidationError::ArityMismatch {
            context: format!("partial.affine row `{id}`"),
            expected: n,
            actual: row.len(),
        });
    }
    for v in row {
        validate_scalar_lit(v, domain, &format!("partial.affine row `{id}`"))?;
    }
    validate_scalar_lit(rhs, domain, &format!("partial.affine rhs `{id}`"))
}

fn validate_open_domain(od: &OpenDomainSpec) -> Result<(), ValidationError> {
    for (s, sub_elems) in &od.substructure_carriers {
        let Some(amb_elems) = od.ambient_carriers.get(s) else {
            return Err(ValidationError::UnknownRef {
                kind: "ambient_sort",
                name: s.clone(),
                context: "open_domain".to_owned(),
            });
        };
        let amb_set: BTreeSet<&str> = amb_elems.iter().map(String::as_str).collect();
        for e in sub_elems {
            if !amb_set.contains(e.as_str()) {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "substructure element `{e}` in sort `{s}` is not contained in ambient carrier"
                    ),
                });
            }
        }
    }

    let mut sub_ops = BTreeMap::new();
    for op in &od.substructure_ops {
        require_non_empty(&op.name, "open_domain.substructure_op.name")?;
        for s in op.arg_sorts.iter().chain(std::iter::once(&op.out_sort)) {
            if !od.substructure_carriers.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "substructure_sort",
                    name: s.clone(),
                    context: format!("open_domain substructure_op `{}`", op.name),
                });
            }
        }
        if sub_ops
            .insert(op.name.as_str(), op.arg_sorts.len())
            .is_some()
        {
            return Err(ValidationError::DuplicateDecl {
                kind: "open_domain_sub_op",
                name: op.name.clone(),
            });
        }
    }

    let mut amb_ops = BTreeMap::new();
    for op in &od.ambient_ops {
        require_non_empty(&op.name, "open_domain.ambient_op.name")?;
        for s in op.arg_sorts.iter().chain(std::iter::once(&op.out_sort)) {
            if !od.ambient_carriers.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "ambient_sort",
                    name: s.clone(),
                    context: format!("open_domain ambient_op `{}`", op.name),
                });
            }
        }
        if amb_ops
            .insert(op.name.as_str(), op.arg_sorts.len())
            .is_some()
        {
            return Err(ValidationError::DuplicateDecl {
                kind: "open_domain_amb_op",
                name: op.name.clone(),
            });
        }
    }

    let mut sub_rels = BTreeMap::new();
    for rel in &od.substructure_rels {
        require_non_empty(&rel.name, "open_domain.substructure_rel.name")?;
        for s in &rel.arg_sorts {
            if !od.substructure_carriers.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "substructure_sort",
                    name: s.clone(),
                    context: format!("open_domain substructure_rel `{}`", rel.name),
                });
            }
        }
        if sub_rels
            .insert(rel.name.as_str(), rel.arg_sorts.len())
            .is_some()
        {
            return Err(ValidationError::DuplicateDecl {
                kind: "open_domain_sub_rel",
                name: rel.name.clone(),
            });
        }
    }

    let mut amb_rels = BTreeMap::new();
    for rel in &od.ambient_rels {
        require_non_empty(&rel.name, "open_domain.ambient_rel.name")?;
        for s in &rel.arg_sorts {
            if !od.ambient_carriers.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "ambient_sort",
                    name: s.clone(),
                    context: format!("open_domain ambient_rel `{}`", rel.name),
                });
            }
        }
        if amb_rels
            .insert(rel.name.as_str(), rel.arg_sorts.len())
            .is_some()
        {
            return Err(ValidationError::DuplicateDecl {
                kind: "open_domain_amb_rel",
                name: rel.name.clone(),
            });
        }
    }

    for fc in &od.fiber_checks {
        if !sub_ops.contains_key(fc.op_name.as_str()) || !amb_ops.contains_key(fc.op_name.as_str())
        {
            return Err(ValidationError::UnknownRef {
                kind: "operation",
                name: fc.op_name.clone(),
                context: "open_domain.fiber_check".to_owned(),
            });
        }
        if !od.ambient_carriers.contains_key(&fc.arg_sort) {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: fc.arg_sort.clone(),
                context: "open_domain.fiber_check.arg_sort".to_owned(),
            });
        }
        let Some(sub_targets) = od.substructure_carriers.get(&fc.target_sort) else {
            return Err(ValidationError::UnknownRef {
                kind: "substructure_sort",
                name: fc.target_sort.clone(),
                context: "open_domain.fiber_check.target_sort".to_owned(),
            });
        };
        let target_set: BTreeSet<&str> = sub_targets.iter().map(String::as_str).collect();
        for t in &fc.known_targets {
            if !target_set.contains(t.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "occurrence",
                    name: t.clone(),
                    context: "open_domain.fiber_check.known_targets".to_owned(),
                });
            }
        }
    }

    require_non_empty(&od.positive_or_law.name, "open_domain.positive_or_law.name")?;
    let amb_sorts: BTreeSet<&str> = od.ambient_carriers.keys().map(String::as_str).collect();
    let empty_slots = BTreeSet::new();
    if let Some(ant) = &od.positive_or_law.antecedent {
        validate_formula_refs(ant, &amb_ops, &amb_rels, &amb_sorts, &empty_slots)?;
    }
    validate_formula_refs(
        &od.positive_or_law.conclusion,
        &amb_ops,
        &amb_rels,
        &amb_sorts,
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
