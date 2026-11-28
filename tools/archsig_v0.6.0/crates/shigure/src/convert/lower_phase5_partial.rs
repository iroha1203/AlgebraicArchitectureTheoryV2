//! `CheckedInputs` から `CheckedPartialTask` への lowering（Phase 5 / 第18章）。

use super::lower::lower_coeff_domain;
use super::lower_expr::{conv_err, lower_scalar_lit, resolve_observed_coord};
use super::lower_morphism::{ensure_snapshot_exists, select_named_decl};
use super::lower_phase4_lift_artin::lower_p4_origins;
use super::lower_phase5_occ::lower_symbolic_value;
use crate::ir::partial::{
    AffinePartialPresentation, AffineRestrictionSpec, BackgroundConstraint, CheckedPartialTask,
    FiberCoverageCheckSpec, FinitePartialPresentation, OpenDomainSpec, OpenOpTable, OpenRelTable,
    PartialArithOp, PartialEvalLawSpec, PartialFormula, PartialOpSignature, PartialPredSignature,
    PartialRecordKind, PartialRecordSpec, PartialRepresentation, PartialSlotDecl, PartialTaskSpec,
    PartialTerm, PartialTruth, PartialValue, QuantifierCompletionSpec, QuantifierHierarchySpec,
    validate_partial_task,
};
use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::ir::validate::ValidationError;
use archsig_input::archmap::CheckedArchMap;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{
    ShigureAffinePartial, ShigureBackgroundConstraint, ShigureFinitePartial,
    ShigureMemberCoordValue, ShigureOpenDomain, ShigurePartialArithOp, ShigurePartialEvalLaw,
    ShigurePartialFormula, ShigurePartialRecordKind, ShigurePartialRepresentation,
    ShigurePartialTerm, ShigurePartialTruth, ShigurePartialValue,
};
use std::collections::{BTreeMap, BTreeSet};

enum TermLowerFrame<'a> {
    Visit(&'a ShigurePartialTerm),
    BuildApp { op_name: &'a str, argc: usize },
    BuildLet(&'a str),
    BuildBinOp(PartialArithOp),
}

fn lower_partial_term(term: &ShigurePartialTerm) -> PartialTerm {
    let mut work = vec![TermLowerFrame::Visit(term)];
    let mut values: Vec<PartialTerm> = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            TermLowerFrame::Visit(node) => match node {
                ShigurePartialTerm::Var(v) => values.push(PartialTerm::Var(v.clone())),
                ShigurePartialTerm::Const(c) => values.push(PartialTerm::Const(c.clone())),
                ShigurePartialTerm::Slot(s) => values.push(PartialTerm::Slot(s.clone())),
                ShigurePartialTerm::App { op_name, args } => {
                    work.push(TermLowerFrame::BuildApp {
                        op_name: op_name.as_str(),
                        argc: args.len(),
                    });
                    for a in args.iter().rev() {
                        work.push(TermLowerFrame::Visit(a));
                    }
                }
                ShigurePartialTerm::Let { var, bound, body } => {
                    work.push(TermLowerFrame::BuildLet(var.as_str()));
                    work.push(TermLowerFrame::Visit(body));
                    work.push(TermLowerFrame::Visit(bound));
                }
                ShigurePartialTerm::BinOp { op, lhs, rhs } => {
                    let arith = match op {
                        ShigurePartialArithOp::Add => PartialArithOp::Add,
                        ShigurePartialArithOp::Sub => PartialArithOp::Sub,
                        ShigurePartialArithOp::Mul => PartialArithOp::Mul,
                    };
                    work.push(TermLowerFrame::BuildBinOp(arith));
                    work.push(TermLowerFrame::Visit(rhs));
                    work.push(TermLowerFrame::Visit(lhs));
                }
            },
            TermLowerFrame::BuildApp { op_name, argc } => {
                let start = values.len().saturating_sub(argc);
                let args = values.split_off(start);
                values.push(PartialTerm::App {
                    op_name: op_name.to_owned(),
                    args,
                });
            }
            TermLowerFrame::BuildLet(var) => {
                let body = values.pop().expect("let body");
                let bound = values.pop().expect("let bound");
                values.push(PartialTerm::Let {
                    var: var.to_owned(),
                    bound: Box::new(bound),
                    body: Box::new(body),
                });
            }
            TermLowerFrame::BuildBinOp(op) => {
                let rhs = values.pop().expect("binop rhs");
                let lhs = values.pop().expect("binop lhs");
                values.push(PartialTerm::BinOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                });
            }
        }
    }
    values.pop().expect("root lowered partial term")
}

enum FormulaLowerFrame<'a> {
    Visit(&'a ShigurePartialFormula),
    BuildNot,
    BuildAnd(usize),
    BuildOr(usize),
    BuildQuant {
        is_exists: bool,
        var: &'a str,
        sort: &'a str,
        restricted: &'a Option<Vec<String>>,
    },
}

fn lower_partial_formula(f: &ShigurePartialFormula) -> PartialFormula {
    let mut work = vec![FormulaLowerFrame::Visit(f)];
    let mut values: Vec<PartialFormula> = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            FormulaLowerFrame::Visit(node) => match node {
                ShigurePartialFormula::Eq(a, b) => {
                    values.push(PartialFormula::Eq(
                        lower_partial_term(a),
                        lower_partial_term(b),
                    ));
                }
                ShigurePartialFormula::Rel { rel_name, args } => {
                    values.push(PartialFormula::Rel {
                        rel_name: rel_name.clone(),
                        args: args.iter().map(lower_partial_term).collect(),
                    });
                }
                ShigurePartialFormula::Graph {
                    op_name,
                    args,
                    output,
                } => {
                    values.push(PartialFormula::Graph {
                        op_name: op_name.clone(),
                        args: args.iter().map(lower_partial_term).collect(),
                        output: lower_partial_term(output),
                    });
                }
                ShigurePartialFormula::Defined { op_name, args } => {
                    values.push(PartialFormula::Defined {
                        op_name: op_name.clone(),
                        args: args.iter().map(lower_partial_term).collect(),
                    });
                }
                ShigurePartialFormula::Not(inner) => {
                    work.push(FormulaLowerFrame::BuildNot);
                    work.push(FormulaLowerFrame::Visit(inner));
                }
                ShigurePartialFormula::And(list) => {
                    work.push(FormulaLowerFrame::BuildAnd(list.len()));
                    for item in list.iter().rev() {
                        work.push(FormulaLowerFrame::Visit(item));
                    }
                }
                ShigurePartialFormula::Or(list) => {
                    work.push(FormulaLowerFrame::BuildOr(list.len()));
                    for item in list.iter().rev() {
                        work.push(FormulaLowerFrame::Visit(item));
                    }
                }
                ShigurePartialFormula::Exists {
                    var,
                    sort,
                    restricted_domain,
                    body,
                } => {
                    work.push(FormulaLowerFrame::BuildQuant {
                        is_exists: true,
                        var: var.as_str(),
                        sort: sort.as_str(),
                        restricted: restricted_domain,
                    });
                    work.push(FormulaLowerFrame::Visit(body));
                }
                ShigurePartialFormula::Forall {
                    var,
                    sort,
                    restricted_domain,
                    body,
                } => {
                    work.push(FormulaLowerFrame::BuildQuant {
                        is_exists: false,
                        var: var.as_str(),
                        sort: sort.as_str(),
                        restricted: restricted_domain,
                    });
                    work.push(FormulaLowerFrame::Visit(body));
                }
            },
            FormulaLowerFrame::BuildNot => {
                let inner = values.pop().expect("not inner");
                values.push(PartialFormula::Not(Box::new(inner)));
            }
            FormulaLowerFrame::BuildAnd(count) => {
                let start = values.len().saturating_sub(count);
                let items = values.split_off(start);
                values.push(PartialFormula::And(items));
            }
            FormulaLowerFrame::BuildOr(count) => {
                let start = values.len().saturating_sub(count);
                let items = values.split_off(start);
                values.push(PartialFormula::Or(items));
            }
            FormulaLowerFrame::BuildQuant {
                is_exists,
                var,
                sort,
                restricted,
            } => {
                let body = Box::new(values.pop().expect("quantifier body"));
                let out = if is_exists {
                    PartialFormula::Exists {
                        var: var.to_owned(),
                        sort: sort.to_owned(),
                        restricted_domain: restricted.clone(),
                        body,
                    }
                } else {
                    PartialFormula::Forall {
                        var: var.to_owned(),
                        sort: sort.to_owned(),
                        restricted_domain: restricted.clone(),
                        body,
                    }
                };
                values.push(out);
            }
        }
    }
    values.pop().expect("root lowered partial formula")
}

fn lower_eval_law(law: &ShigurePartialEvalLaw) -> PartialEvalLawSpec {
    PartialEvalLawSpec {
        name: law.name.clone(),
        antecedent: law.antecedent.as_ref().map(lower_partial_formula),
        conclusion: lower_partial_formula(&law.conclusion),
        is_required_law: law.is_required_law,
    }
}

fn lower_truth(t: &ShigurePartialTruth) -> PartialTruth {
    match t {
        ShigurePartialTruth::True => PartialTruth::True,
        ShigurePartialTruth::ExplicitAbsent => PartialTruth::ExplicitAbsent,
        ShigurePartialTruth::UnobservedSlot(s) => PartialTruth::UnobservedSlot(s.clone()),
    }
}

fn lower_finite_partial(
    fin: &ShigureFinitePartial,
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    fallback_ref: &SourceRef,
    decl_name: &str,
    origins: &mut BTreeSet<SourceRef>,
    missing_slots: &mut Vec<String>,
) -> Result<FinitePartialPresentation, ValidationError> {
    let sorts: BTreeMap<String, Vec<String>> = fin.sorts.iter().cloned().collect();
    let operations = fin
        .operations
        .iter()
        .map(|op| PartialOpSignature {
            name: op.name.clone(),
            arg_sorts: op.arg_sorts.clone(),
            out_sort: op.out_sort.clone(),
            is_total: op.is_total,
        })
        .collect();
    let relations = fin
        .relations
        .iter()
        .map(|r| PartialPredSignature {
            name: r.name.clone(),
            arg_sorts: r.arg_sorts.clone(),
        })
        .collect();
    let slots = fin
        .slots
        .iter()
        .map(|s| PartialSlotDecl {
            name: s.name.clone(),
            sort: s.sort.clone(),
            domain_values: s.domain_values.clone(),
        })
        .collect();
    let background_constraints = fin
        .background_constraints
        .iter()
        .map(|bg| match bg {
            ShigureBackgroundConstraint::SlotEquality(a, b) => {
                BackgroundConstraint::SlotEquality(a.clone(), b.clone())
            }
            ShigureBackgroundConstraint::SlotNotEqual(a, b) => {
                BackgroundConstraint::SlotNotEqual(a.clone(), b.clone())
            }
            ShigureBackgroundConstraint::OperationInjective(op) => {
                BackgroundConstraint::OperationInjective(op.clone())
            }
            ShigureBackgroundConstraint::OperationSurjective(op) => {
                BackgroundConstraint::OperationSurjective(op.clone())
            }
        })
        .collect();

    let mut records = Vec::with_capacity(fin.records.len());
    for rec in &fin.records {
        let kind = match &rec.kind {
            ShigurePartialRecordKind::OpValue {
                op_name,
                args,
                value,
            } => {
                let lowered_val = match value {
                    ShigurePartialValue::Known(sym) => {
                        let Some(val) = lower_symbolic_value(
                            sym,
                            archmap,
                            snapshot_id,
                            fallback_ref,
                            &format!("{decl_name}.record.{}", rec.id),
                            origins,
                            missing_slots,
                        )?
                        else {
                            continue;
                        };
                        PartialValue::Known(val)
                    }
                    ShigurePartialValue::ExplicitAbsent => PartialValue::ExplicitAbsent,
                    ShigurePartialValue::UnobservedSlot(s) => {
                        PartialValue::UnobservedSlot(s.clone())
                    }
                };
                PartialRecordKind::OpValue {
                    op_name: op_name.clone(),
                    args: args.clone(),
                    value: lowered_val,
                }
            }
            ShigurePartialRecordKind::OpDomain {
                op_name,
                args,
                defined,
            } => PartialRecordKind::OpDomain {
                op_name: op_name.clone(),
                args: args.clone(),
                defined: lower_truth(defined),
            },
            ShigurePartialRecordKind::OpGraph {
                op_name,
                args,
                output,
                present,
            } => PartialRecordKind::OpGraph {
                op_name: op_name.clone(),
                args: args.clone(),
                output: output.clone(),
                present: lower_truth(present),
            },
            ShigurePartialRecordKind::Relation {
                rel_name,
                args,
                holds,
            } => PartialRecordKind::Relation {
                rel_name: rel_name.clone(),
                args: args.clone(),
                holds: lower_truth(holds),
            },
            ShigurePartialRecordKind::SlotAssignment { slot, value } => {
                PartialRecordKind::SlotAssignment {
                    slot: slot.clone(),
                    value: value.clone(),
                }
            }
        };
        records.push(PartialRecordSpec {
            id: rec.id.clone(),
            kind,
        });
    }

    Ok(FinitePartialPresentation {
        sorts,
        operations,
        relations,
        slots,
        background_constraints,
        records,
        max_completions: fin.max_completions,
    })
}

pub(super) fn lower_required_scalar(
    val: &ShigureMemberCoordValue,
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    coeff_domain: &CoeffDomain,
    fallback_ref: &SourceRef,
    context: &str,
    origins: &mut BTreeSet<SourceRef>,
) -> Result<ScalarLit, ValidationError> {
    match val {
        ShigureMemberCoordValue::Literal(lit) => lower_scalar_lit(lit, coeff_domain, context),
        ShigureMemberCoordValue::ObservedField { entity, field, .. } => {
            let (cv, refs) = resolve_observed_coord(
                archmap,
                snapshot_id,
                entity,
                field,
                coeff_domain,
                fallback_ref,
            )?;
            for r in refs {
                origins.insert(r);
            }
            match cv {
                CoordValue::Observed(lit) => Ok(lit),
                CoordValue::Missing | CoordValue::Symbolic => {
                    let field_display = if field.starts_with(&format!("{entity}.")) {
                        field.clone()
                    } else {
                        format!("{entity}.{field}")
                    };
                    Err(conv_err(format!(
                        "observed field `{field_display}` in {context} is missing or non-scalar"
                    )))
                }
            }
        }
        ShigureMemberCoordValue::Missing => Err(conv_err(format!(
            "explicit `missing` value is not permitted in {context}"
        ))),
    }
}

fn lower_affine_partial(
    aff: &ShigureAffinePartial,
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    fallback_ref: &SourceRef,
    origins: &mut BTreeSet<SourceRef>,
) -> Result<AffinePartialPresentation, ValidationError> {
    let coeff_domain = lower_coeff_domain(&aff.coeff_domain);
    let x0 = aff
        .x0
        .iter()
        .enumerate()
        .map(|(i, v)| {
            lower_required_scalar(
                v,
                archmap,
                snapshot_id,
                &coeff_domain,
                fallback_ref,
                &format!("affine.x0[{i}]"),
                origins,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut direction_t = Vec::with_capacity(aff.direction_t.len());
    for (r, row) in aff.direction_t.iter().enumerate() {
        let lowered_row = row
            .iter()
            .enumerate()
            .map(|(c, v)| {
                lower_required_scalar(
                    v,
                    archmap,
                    snapshot_id,
                    &coeff_domain,
                    fallback_ref,
                    &format!("affine.direction_t[{r}][{c}]"),
                    origins,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        direction_t.push(lowered_row);
    }
    let lower_rows = |rows: &[archsig_input::law::shigure::ShigureAffineRow],
                      label: &str,
                      origins: &mut BTreeSet<SourceRef>|
     -> Result<Vec<(String, Vec<ScalarLit>, ScalarLit)>, ValidationError> {
        let mut out = Vec::with_capacity(rows.len());
        for row in rows {
            let coeffs = row
                .coeffs
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    lower_required_scalar(
                        v,
                        archmap,
                        snapshot_id,
                        &coeff_domain,
                        fallback_ref,
                        &format!("{label}.{}.coeff[{i}]", row.id),
                        origins,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let rhs = lower_required_scalar(
                &row.rhs,
                archmap,
                snapshot_id,
                &coeff_domain,
                fallback_ref,
                &format!("{label}.{}.rhs", row.id),
                origins,
            )?;
            out.push((row.id.clone(), coeffs, rhs));
        }
        Ok(out)
    };
    let background_rows = lower_rows(&aff.background_rows, "affine.background_row", origins)?;
    let record_rows = lower_rows(&aff.record_rows, "affine.record_row", origins)?;
    let eval_equations = lower_rows(&aff.eval_equations, "affine.eval_eq", origins)?;
    Ok(AffinePartialPresentation {
        coeff_domain,
        coord_names: aff.coord_names.clone(),
        x0,
        direction_t,
        background_rows,
        record_rows,
        eval_equations,
    })
}

fn lower_open_domain(od: &ShigureOpenDomain) -> Result<OpenDomainSpec, ValidationError> {
    let lower_ops = |ops: &[archsig_input::law::shigure::ShigureOpenOpTable]| -> Vec<OpenOpTable> {
        ops.iter()
            .map(|op| OpenOpTable {
                name: op.name.clone(),
                arg_sorts: op.arg_sorts.clone(),
                out_sort: op.out_sort.clone(),
                entries: op.entries.iter().cloned().collect(),
            })
            .collect()
    };
    let lower_rels =
        |rels: &[archsig_input::law::shigure::ShigureOpenRelTable]| -> Vec<OpenRelTable> {
            rels.iter()
                .map(|r| OpenRelTable {
                    name: r.name.clone(),
                    arg_sorts: r.arg_sorts.clone(),
                    entries: r.entries.iter().cloned().collect(),
                })
                .collect()
        };
    let affine_restriction = match &od.affine_restriction {
        Some(ar) => {
            let dom = lower_coeff_domain(&ar.coeff_domain);
            let m_matrix = ar
                .m_matrix
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|v| lower_scalar_lit(v, &dom, "open_domain.affine_restriction.M"))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
            let b_rhs = ar
                .b_rhs
                .iter()
                .map(|v| lower_scalar_lit(v, &dom, "open_domain.affine_restriction.b"))
                .collect::<Result<Vec<_>, _>>()?;
            let r_matrix = ar
                .r_matrix
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|v| lower_scalar_lit(v, &dom, "open_domain.affine_restriction.R"))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
            Some(AffineRestrictionSpec {
                coeff_domain: dom,
                m_matrix,
                b_rhs,
                r_matrix,
                num_vars: ar.num_vars,
            })
        }
        None => None,
    };
    Ok(OpenDomainSpec {
        substructure_carriers: od.substructure_sorts.iter().cloned().collect(),
        ambient_carriers: od.ambient_sorts.iter().cloned().collect(),
        substructure_ops: lower_ops(&od.substructure_ops),
        ambient_ops: lower_ops(&od.ambient_ops),
        substructure_rels: lower_rels(&od.substructure_rels),
        ambient_rels: lower_rels(&od.ambient_rels),
        fiber_checks: od
            .fiber_checks
            .iter()
            .map(|fc| FiberCoverageCheckSpec {
                op_name: fc.op_name.clone(),
                arg_sort: fc.arg_sort.clone(),
                target_sort: fc.target_sort.clone(),
                known_targets: fc.known_targets.clone(),
            })
            .collect(),
        positive_or_law: lower_eval_law(&od.positive_or_law),
        affine_restriction,
    })
}

pub(super) fn convert_partial_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedPartialTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) = select_named_decl(&shigure.partial_tasks, task_name, "shigure partial")?;
    let (mut origins, primary_ref) =
        lower_p4_origins(&decl.origins, archmap, &decl.name, &decl.name)?;
    let mut missing_slots = Vec::new();

    let representation = match &decl.representation {
        ShigurePartialRepresentation::FiniteTable(fin) => {
            PartialRepresentation::FiniteTable(lower_finite_partial(
                fin,
                archmap,
                snapshot_id,
                &primary_ref,
                &decl.name,
                &mut origins,
                &mut missing_slots,
            )?)
        }
        ShigurePartialRepresentation::Affine(aff) => PartialRepresentation::Affine(
            lower_affine_partial(aff, archmap, snapshot_id, &primary_ref, &mut origins)?,
        ),
        ShigurePartialRepresentation::UnsupportedClass { description } => {
            PartialRepresentation::UnsupportedClass {
                description: description.clone(),
            }
        }
    };

    let eval_laws = decl.eval_laws.iter().map(lower_eval_law).collect();
    let quantifier_spec = decl
        .quantifier_spec
        .as_ref()
        .map(|q| QuantifierHierarchySpec {
            candidates: q.candidates.clone(),
            completions: q
                .completions
                .iter()
                .map(|c| QuantifierCompletionSpec {
                    id: c.id.clone(),
                    slot_values: c.slot_values.iter().cloned().collect(),
                    valid_candidates: c.valid_candidates.clone(),
                    output_value: c.output_value.clone(),
                })
                .collect(),
            max_steps: q.max_steps,
        });
    let open_domain = decl
        .open_domain
        .as_ref()
        .map(lower_open_domain)
        .transpose()?;

    validate_partial_task(PartialTaskSpec {
        name: decl.name.clone(),
        representation,
        eval_laws,
        quantifier_spec,
        open_domain,
        provenance: Provenance::new(origins.into_iter().collect(), Vec::new()),
        undeclared_unobserved_slots: missing_slots,
    })
}
