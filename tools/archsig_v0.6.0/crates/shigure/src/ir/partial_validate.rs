//! `partial.rs` 用の部分提示・開領域・定量化階層 IR の検証ロジック。

use crate::ir::partial::{
    AffinePartialPresentation, BackgroundConstraint, CheckedPartialTask, FinitePartialPresentation,
    PartialEvalLawSpec, PartialFormula, PartialOpSignature, PartialPredSignature,
    PartialRecordKind, PartialRepresentation, PartialTaskSpec, PartialTerm, PartialTruth,
    PartialValue, QuantifierHierarchySpec,
};
use crate::ir::partial_open_validate::validate_open_domain;
use crate::ir::validate::{
    ValidationError, require_non_empty, validate_coeff_domain, validate_nonempty_provenance,
    validate_scalar_lit,
};
use std::collections::{BTreeMap, BTreeSet};

pub fn validate_partial_task(
    mut spec: PartialTaskSpec,
) -> Result<CheckedPartialTask, ValidationError> {
    require_non_empty(&spec.name, "partial.name")?;
    validate_nonempty_provenance(&spec.provenance, &format!("partial `{}`", spec.name))?;

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

    match &mut spec.representation {
        PartialRepresentation::FiniteTable(fin) => {
            if fin.max_completions == 0 {
                fin.max_completions = crate::limits::active_limits().max_completions;
            }
            validate_finite_partial(fin, &spec.eval_laws)?;
        }
        PartialRepresentation::Affine(aff) => {
            if !spec.eval_laws.is_empty() {
                return Err(ValidationError::ConversionError {
                    detail: "affine partial presentation must specify evaluation laws via `eval_equations` rather than `eval_laws`"
                        .to_owned(),
                });
            }
            validate_affine_partial(aff)?;
        }
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

    Ok(CheckedPartialTask::from_validated(
        spec.name,
        spec.representation,
        spec.eval_laws,
        spec.quantifier_spec,
        spec.open_domain,
        spec.provenance,
        spec.undeclared_unobserved_slots,
    ))
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
    let slot_name_set: BTreeSet<&str> = slot_sorts.keys().map(String::as_str).collect();

    for law in eval_laws {
        if let Some(ant) = &law.antecedent {
            validate_formula_refs(ant, &op_arities, &rel_arities, &sort_elems, &slot_name_set)?;
        }
        validate_formula_refs(
            &law.conclusion,
            &op_arities,
            &rel_arities,
            &sort_elems,
            &slot_name_set,
        )?;
    }

    Ok(())
}

pub(super) fn validate_typed_args(
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

pub(super) fn validate_formula_refs(
    formula: &PartialFormula,
    op_arities: &BTreeMap<&str, usize>,
    rel_arities: &BTreeMap<&str, usize>,
    sorts: &BTreeMap<String, BTreeSet<String>>,
    slots: &BTreeSet<&str>,
) -> Result<(), ValidationError> {
    let bound_vars = BTreeSet::new();
    validate_formula_refs_with_vars(formula, op_arities, rel_arities, sorts, slots, &bound_vars)
}

fn validate_formula_refs_with_vars(
    formula: &PartialFormula,
    op_arities: &BTreeMap<&str, usize>,
    rel_arities: &BTreeMap<&str, usize>,
    sorts: &BTreeMap<String, BTreeSet<String>>,
    slots: &BTreeSet<&str>,
    bound_vars: &BTreeSet<&str>,
) -> Result<(), ValidationError> {
    match formula {
        PartialFormula::Eq(a, b) => {
            validate_term_refs(a, op_arities, slots, bound_vars)?;
            validate_term_refs(b, op_arities, slots, bound_vars)
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
                validate_term_refs(a, op_arities, slots, bound_vars)?;
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
                validate_term_refs(a, op_arities, slots, bound_vars)?;
            }
            validate_term_refs(output, op_arities, slots, bound_vars)
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
                validate_term_refs(a, op_arities, slots, bound_vars)?;
            }
            Ok(())
        }
        PartialFormula::Not(inner) => validate_formula_refs_with_vars(
            inner,
            op_arities,
            rel_arities,
            sorts,
            slots,
            bound_vars,
        ),
        PartialFormula::Exists {
            var,
            sort,
            restricted_domain,
            body,
        }
        | PartialFormula::Forall {
            var,
            sort,
            restricted_domain,
            body,
        } => {
            require_non_empty(var, "partial.formula.quantifier.var")?;
            let Some(carrier) = sorts.get(sort.as_str()) else {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: sort.clone(),
                    context: "partial.formula quantifier".to_owned(),
                });
            };
            if let Some(dom) = restricted_domain {
                for elem in dom {
                    if !carrier.contains(elem) {
                        return Err(ValidationError::UnknownRef {
                            kind: "occurrence",
                            name: elem.clone(),
                            context: format!("partial.formula quantifier sort `{sort}`"),
                        });
                    }
                }
            }
            let mut next_bound = bound_vars.clone();
            next_bound.insert(var.as_str());
            validate_formula_refs_with_vars(
                body,
                op_arities,
                rel_arities,
                sorts,
                slots,
                &next_bound,
            )
        }
        PartialFormula::And(list) | PartialFormula::Or(list) => {
            for f in list {
                validate_formula_refs_with_vars(
                    f,
                    op_arities,
                    rel_arities,
                    sorts,
                    slots,
                    bound_vars,
                )?;
            }
            Ok(())
        }
    }
}

fn validate_term_refs(
    term: &PartialTerm,
    op_arities: &BTreeMap<&str, usize>,
    slots: &BTreeSet<&str>,
    bound_vars: &BTreeSet<&str>,
) -> Result<(), ValidationError> {
    match term {
        PartialTerm::Var(v) => {
            require_non_empty(v, "partial.term.var")?;
            if !bound_vars.contains(v.as_str()) {
                return Err(ValidationError::UnknownRef {
                    kind: "bound_var",
                    name: v.clone(),
                    context: "partial.term".to_owned(),
                });
            }
            Ok(())
        }
        PartialTerm::Const(c) => require_non_empty(c, "partial.term.const"),
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
                validate_term_refs(a, op_arities, slots, bound_vars)?;
            }
            Ok(())
        }
        PartialTerm::Let { var, bound, body } => {
            require_non_empty(var, "partial.term.let.var")?;
            validate_term_refs(bound, op_arities, slots, bound_vars)?;
            let mut next_bound = bound_vars.clone();
            next_bound.insert(var.as_str());
            validate_term_refs(body, op_arities, slots, &next_bound)
        }
        PartialTerm::BinOp { lhs, rhs, .. } => {
            validate_term_refs(lhs, op_arities, slots, bound_vars)?;
            validate_term_refs(rhs, op_arities, slots, bound_vars)
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
        if t_cols == 0 && !scalar_is_zero(v) {
            return Err(ValidationError::ConversionError {
                detail: "partial.affine with zero direction_t columns requires zero x0".to_owned(),
            });
        }
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

fn scalar_is_zero(lit: &crate::ir::term::ScalarLit) -> bool {
    use num_traits::Zero;
    match lit {
        crate::ir::term::ScalarLit::Z(n) => n.is_zero(),
        crate::ir::term::ScalarLit::Q { num, .. } => num.is_zero(),
        crate::ir::term::ScalarLit::Fp { value, .. } => value.is_zero(),
    }
}
