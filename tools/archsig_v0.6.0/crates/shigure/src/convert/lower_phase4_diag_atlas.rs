//! `CheckedInputs` から `CheckedDiagnosticsTask` / `CheckedAtlasTask` への lowering（Phase 4 / AC2）。

use super::lower::lower_coeff_domain;
use super::lower_expr::{conv_err, lower_poly_expr, lower_scalar_lit, resolve_observed_coord};
use super::lower_morphism::{ensure_snapshot_exists, select_named_decl};
use super::lower_phase4_lift_artin::{
    lower_p4_coord_to_poly, lower_p4_coord_vec, lower_p4_named_polys, lower_p4_origins,
};
use crate::ir::atlas::{
    AtlasEvalConditionSpec, AtlasRefinementSpec, AtlasTaskSpec, AtomicOpCompareSpec,
    CheckedAtlasTask, ExtendedLanguageCheckSpec, ExtendedOperationCheckSpec, ForgetfulReadingSpec,
    GraphEdgeSpec, validate_atlas_task,
};
use crate::ir::diagnostics::{
    ChartSupportSpec, CheckedDiagnosticsTask, CoeffChangeComparisonSpec, CollisionComparisonSpec,
    DiagnosticsReadoutSpec, DiagnosticsTaskSpec, DimensionRealizationSpec, ExplicitZComplexSpec,
    NamedBasePointSpec, NamedRPointSpec, NerveEdgeSpec, NerveFaceSpec, PolyLawReadoutSpec,
    RPointProbeSpec, StaticLawReadoutSpec, SupportedNerveSpec, validate_diagnostics_task,
};
use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::ValidationError;
use archsig_input::archmap::CheckedArchMap;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{
    ShigureDiagnosticsReadout, ShigureExtendedOperationCheck, ShigureGraphEdge,
    ShigurePolyOrObserved, ShigureScalarLit, ShigureSupportedNerve,
};
use std::collections::BTreeSet;

fn lower_supported_nerve(raw: &ShigureSupportedNerve) -> SupportedNerveSpec {
    SupportedNerveSpec {
        charts: raw
            .charts
            .iter()
            .map(|c| ChartSupportSpec {
                name: c.name.clone(),
                support: c.support.clone(),
            })
            .collect(),
        edges: raw
            .edges
            .iter()
            .map(|e| NerveEdgeSpec {
                name: e.name.clone(),
                left: e.left.clone(),
                right: e.right.clone(),
            })
            .collect(),
        faces: raw
            .faces
            .iter()
            .map(|f| NerveFaceSpec {
                name: f.name.clone(),
                e0: f.e0.clone(),
                e1: f.e1.clone(),
                e2: f.e2.clone(),
            })
            .collect(),
    }
}

fn infer_static_lit_domain(lit: &ShigureScalarLit) -> CoeffDomain {
    match lit {
        ShigureScalarLit::Int(_) => CoeffDomain::Z,
        ShigureScalarLit::Rat { .. } => CoeffDomain::Q,
        ShigureScalarLit::Fp { modulus, .. } => CoeffDomain::Fp(modulus.clone()),
    }
}

pub(super) fn convert_diagnostics_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedDiagnosticsTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) =
        select_named_decl(&shigure.diagnostics_tasks, task_name, "shigure diagnostics")?;
    let diagnostic_coeff = lower_coeff_domain(&decl.diagnostic_coeff);
    let (mut origins, primary_ref) =
        lower_p4_origins(&decl.origins, archmap, &decl.name, &decl.name)?;
    let nerve = lower_supported_nerve(&decl.nerve);
    let empty = BTreeSet::new();

    let (readout, poly_base_domain) = match &decl.readout {
        ShigureDiagnosticsReadout::Static {
            sources,
            targets,
            reading,
            laws,
            ..
        } => {
            let mut lowered_laws = Vec::with_capacity(laws.len());
            for law in laws {
                let mut vals = Vec::with_capacity(law.values.len());
                for (s, lit) in &law.values {
                    let ldom = infer_static_lit_domain(lit);
                    vals.push((
                        s.clone(),
                        lower_scalar_lit(
                            lit,
                            &ldom,
                            &format!("{}.law.{}.{s}", decl.name, law.law_name),
                        )?,
                    ));
                }
                lowered_laws.push(StaticLawReadoutSpec {
                    law_name: law.law_name.clone(),
                    values: vals,
                });
            }
            (
                DiagnosticsReadoutSpec::Static {
                    sources: sources.clone(),
                    targets: targets.clone(),
                    reading: reading.clone(),
                    laws: lowered_laws,
                },
                None,
            )
        }
        ShigureDiagnosticsReadout::Polynomial {
            base_domain,
            base_vars,
            base_relations,
            sources,
            laws,
            ..
        } => {
            let bdom = lower_coeff_domain(base_domain);
            let bv_set: BTreeSet<String> = base_vars.iter().cloned().collect();
            let brels = lower_p4_named_polys(
                base_relations,
                &bdom,
                &bv_set,
                &empty,
                &empty,
                &primary_ref,
                &format!("{}.base_relations", decl.name),
            )?;
            let mut lowered_laws = Vec::with_capacity(laws.len());
            for law in laws {
                let mut vals = Vec::with_capacity(law.values.len());
                for (s, val) in &law.values {
                    let expr = match val {
                        ShigurePolyOrObserved::Poly(p) => lower_poly_expr(
                            p,
                            &bdom,
                            &bv_set,
                            &empty,
                            &empty,
                            None,
                            &format!("{}.poly_law.{}.{s}", decl.name, law.law_name),
                        )?,
                        ShigurePolyOrObserved::ObservedField { entity, field, .. } => {
                            let (cv, refs) = resolve_observed_coord(
                                archmap,
                                snapshot_id,
                                entity,
                                field,
                                &bdom,
                                &primary_ref,
                            )?;
                            let first_ref = refs.first().cloned();
                            for r in refs {
                                origins.insert(r);
                            }
                            match cv {
                                CoordValue::Observed(lit) => PolyExpr::Const(lit),
                                CoordValue::Missing => PolyExpr::Unobserved {
                                    slot: if field.starts_with(&format!("{entity}.")) {
                                        field.clone()
                                    } else {
                                        format!("{entity}.{field}")
                                    },
                                    origin: first_ref.or_else(|| Some(primary_ref.clone())),
                                },
                                CoordValue::Symbolic => {
                                    return Err(conv_err(format!(
                                        "unexpected symbolic coord value for observed field `{entity}.{field}`"
                                    )));
                                }
                            }
                        }
                        ShigurePolyOrObserved::Missing => PolyExpr::Unobserved {
                            slot: format!("{}.poly_law.{}.{s}", decl.name, law.law_name),
                            origin: Some(primary_ref.clone()),
                        },
                    };
                    vals.push((s.clone(), expr));
                }
                lowered_laws.push(PolyLawReadoutSpec {
                    law_name: law.law_name.clone(),
                    values: vals,
                });
            }
            (
                DiagnosticsReadoutSpec::Polynomial {
                    base_domain: bdom.clone(),
                    base_vars: base_vars.clone(),
                    base_relations: brels,
                    sources: sources.clone(),
                    laws: lowered_laws,
                },
                Some(bdom),
            )
        }
    };

    let coeff_change = decl
        .coeff_change
        .as_ref()
        .map(|cc| CoeffChangeComparisonSpec {
            target_domain: lower_coeff_domain(&cc.target_domain),
            compare_codomain_regeneration: cc.compare_codomain_regeneration,
            explicit_z_complex: cc
                .explicit_z_complex
                .as_ref()
                .map(|ez| ExplicitZComplexSpec {
                    dim0: ez.dim0,
                    dim1: ez.dim1,
                    d0: ez.d0.clone(),
                    designated_cocycle: ez.designated_cocycle.clone(),
                }),
        });

    let collisions = decl
        .collisions
        .iter()
        .map(|c| CollisionComparisonSpec {
            label: c.label.clone(),
            law_name: c.law_name.clone(),
            fine_partition: c.fine_partition.clone(),
            coarse_partition: c.coarse_partition.clone(),
            alternative_merge_paths: c.alternative_merge_paths.clone(),
        })
        .collect();

    let r_point_probe = decl
        .r_point_probe
        .as_ref()
        .map(|rp| {
            let bdom = poly_base_domain
                .as_ref()
                .ok_or_else(|| conv_err("r_point_probe requires poly_readout"))?;
            let mut points = Vec::with_capacity(rp.points.len());
            for pt in &rp.points {
                let mut coords = Vec::with_capacity(pt.coords.len());
                for (v, vals) in &pt.coords {
                    coords.push((
                        v.clone(),
                        lower_p4_coord_vec(
                            vals,
                            archmap,
                            snapshot_id,
                            bdom,
                            &primary_ref,
                            &format!("{}.r_point.{}.{v}", decl.name, pt.label),
                            &mut origins,
                        )?,
                    ));
                }
                points.push(NamedRPointSpec {
                    label: pt.label.clone(),
                    coords,
                });
            }
            Ok::<_, ValidationError>(RPointProbeSpec {
                ring_var: rp.ring_var.clone(),
                ring_max_deg: rp.ring_max_deg,
                points,
            })
        })
        .transpose()?;

    let dimension_realization = decl
        .dimension_realization
        .as_ref()
        .map(|dr| {
            let bdom = lower_coeff_domain(&dr.base_domain);
            let bv_set: BTreeSet<String> = dr.base_vars.iter().cloned().collect();
            let vanishing_polys = lower_p4_named_polys(
                &dr.vanishing_polys,
                &bdom,
                &bv_set,
                &empty,
                &empty,
                &primary_ref,
                &format!("{}.dim_real.vanishing", decl.name),
            )?;
            let mut inv = lower_p4_named_polys(
                std::slice::from_ref(&dr.invertible_poly),
                &bdom,
                &bv_set,
                &empty,
                &empty,
                &primary_ref,
                &format!("{}.dim_real.invertible", decl.name),
            )?;
            let invertible_poly = inv
                .pop()
                .ok_or_else(|| conv_err("missing invertible_poly"))?;
            let mut probe_points = Vec::with_capacity(dr.probe_points.len());
            for pt in &dr.probe_points {
                let mut coords = Vec::with_capacity(pt.coords.len());
                for (v, val) in &pt.coords {
                    coords.push((
                        v.clone(),
                        lower_p4_coord_to_poly(
                            val,
                            archmap,
                            snapshot_id,
                            &bdom,
                            &primary_ref,
                            &format!("{}.dim_real.probe.{}.{v}", decl.name, pt.label),
                            &mut origins,
                        )?,
                    ));
                }
                probe_points.push(NamedBasePointSpec {
                    label: pt.label.clone(),
                    coords,
                });
            }
            Ok::<_, ValidationError>(DimensionRealizationSpec {
                base_domain: bdom,
                base_vars: dr.base_vars.clone(),
                vanishing_polys,
                invertible_poly,
                probe_points,
            })
        })
        .transpose()?;

    validate_diagnostics_task(DiagnosticsTaskSpec {
        name: decl.name.clone(),
        diagnostic_coeff,
        nerve,
        readout,
        coeff_change,
        collisions,
        r_point_probe,
        dimension_realization,
        max_partitions: decl.max_partitions,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: Vec::new(),
        },
    })
}

fn lower_graph_edges(
    edges: &[ShigureGraphEdge],
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    coeff_domain: &CoeffDomain,
    fallback_ref: &SourceRef,
    prefix: &str,
    origins: &mut BTreeSet<SourceRef>,
) -> Result<Vec<GraphEdgeSpec>, ValidationError> {
    let mut out = Vec::with_capacity(edges.len());
    for e in edges {
        let offset = lower_p4_coord_to_poly(
            &e.offset,
            archmap,
            snapshot_id,
            coeff_domain,
            fallback_ref,
            &format!("{prefix}.edge.{}.offset", e.name),
            origins,
        )?;
        out.push(GraphEdgeSpec {
            name: e.name.clone(),
            from: e.from.clone(),
            to: e.to.clone(),
            offset,
        });
    }
    Ok(out)
}

pub(super) fn convert_atlas_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedAtlasTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) = select_named_decl(&shigure.atlas_tasks, task_name, "shigure atlas")?;
    let coeff_domain = lower_coeff_domain(&decl.coeff_domain);
    let (mut origins, primary_ref) =
        lower_p4_origins(&decl.origins, archmap, &decl.name, &decl.name)?;
    let empty = BTreeSet::new();

    let edges = lower_graph_edges(
        &decl.edges,
        archmap,
        snapshot_id,
        &coeff_domain,
        &primary_ref,
        &decl.name,
        &mut origins,
    )?;
    let mu = lower_p4_coord_to_poly(
        &decl.mu,
        archmap,
        snapshot_id,
        &coeff_domain,
        &primary_ref,
        &format!("{}.mu", decl.name),
        &mut origins,
    )?;

    let mut base_lambdas = Vec::with_capacity(decl.base_lambdas.len());
    for (v, val) in &decl.base_lambdas {
        base_lambdas.push((
            v.clone(),
            lower_p4_coord_to_poly(
                val,
                archmap,
                snapshot_id,
                &coeff_domain,
                &primary_ref,
                &format!("{}.base_lambdas.{v}", decl.name),
                &mut origins,
            )?,
        ));
    }

    let refinement = decl
        .refinement
        .as_ref()
        .map(|r| {
            let fine_edges = lower_graph_edges(
                &r.fine_edges,
                archmap,
                snapshot_id,
                &coeff_domain,
                &primary_ref,
                &format!("{}.refinement", decl.name),
                &mut origins,
            )?;
            let eval_condition = r
                .eval_condition
                .as_ref()
                .map(|ec| {
                    let mut scope: BTreeSet<String> = decl.vertices.iter().cloned().collect();
                    scope.extend(decl.edges.iter().map(|e| e.name.clone()));
                    Ok::<_, ValidationError>(AtlasEvalConditionSpec {
                        evaluations: lower_p4_named_polys(
                            &ec.evaluations,
                            &coeff_domain,
                            &scope,
                            &empty,
                            &empty,
                            &primary_ref,
                            &format!("{}.refinement.eval_condition.eval", decl.name),
                        )?,
                        equations: lower_p4_named_polys(
                            &ec.equations,
                            &coeff_domain,
                            &scope,
                            &empty,
                            &empty,
                            &primary_ref,
                            &format!("{}.refinement.eval_condition.eq", decl.name),
                        )?,
                        invertibles: lower_p4_named_polys(
                            &ec.invertibles,
                            &coeff_domain,
                            &scope,
                            &empty,
                            &empty,
                            &primary_ref,
                            &format!("{}.refinement.eval_condition.inv", decl.name),
                        )?,
                    })
                })
                .transpose()?;
            let forgetful_reading = r
                .forgetful_reading
                .as_ref()
                .map(|fg| {
                    let fg_vars: BTreeSet<String> =
                        [fg.forgotten_var.clone()].into_iter().collect();
                    let eval_expr = lower_poly_expr(
                        &fg.eval_expr,
                        &coeff_domain,
                        &fg_vars,
                        &empty,
                        &empty,
                        None,
                        &format!("{}.forgetful_reading.eval_expr", decl.name),
                    )?;
                    let condition_eq = lower_poly_expr(
                        &fg.condition_eq,
                        &coeff_domain,
                        &fg_vars,
                        &empty,
                        &empty,
                        None,
                        &format!("{}.forgetful_reading.condition_eq", decl.name),
                    )?;
                    let sample_values = lower_p4_coord_vec(
                        &fg.sample_values,
                        archmap,
                        snapshot_id,
                        &coeff_domain,
                        &primary_ref,
                        &format!("{}.forgetful_reading.sample_values", decl.name),
                        &mut origins,
                    )?;
                    Ok::<_, ValidationError>(ForgetfulReadingSpec {
                        forgotten_var: fg.forgotten_var.clone(),
                        eval_expr,
                        condition_eq,
                        sample_values,
                    })
                })
                .transpose()?;
            Ok::<_, ValidationError>(AtlasRefinementSpec {
                fine_vertices: r.fine_vertices.clone(),
                fine_edges,
                vertex_map: r.vertex_map.clone(),
                edge_map: r.edge_map.clone(),
                common_sources: r.common_sources.clone(),
                coarse_reading: r.coarse_reading.clone(),
                fine_reading: r.fine_reading.clone(),
                coarse_nerve: lower_supported_nerve(&r.coarse_nerve),
                fine_nerve: lower_supported_nerve(&r.fine_nerve),
                nerve_chart_map: r.nerve_chart_map.clone(),
                nerve_edge_map: r.nerve_edge_map.clone(),
                nerve_face_map: r.nerve_face_map.clone(),
                eval_condition,
                forgetful_reading,
            })
        })
        .transpose()?;

    let extended_language_check = decl
        .extended_language_check
        .as_ref()
        .map(|ext| {
            let sv_set: BTreeSet<String> = ext.state_vars.iter().cloned().collect();
            let mut adapter_map = Vec::with_capacity(ext.adapter_map.len());
            for (v, expr) in &ext.adapter_map {
                adapter_map.push((
                    v.clone(),
                    lower_poly_expr(
                        expr,
                        &coeff_domain,
                        &sv_set,
                        &empty,
                        &empty,
                        None,
                        &format!("{}.adapter_map.{v}", decl.name),
                    )?,
                ));
            }
            let mut atomic_ops = Vec::with_capacity(ext.atomic_ops.len());
            for op in &ext.atomic_ops {
                let arg_set: BTreeSet<String> = op.arg_vars.iter().cloned().collect();
                let mut bu = Vec::with_capacity(op.before_updates.len());
                for (v, expr) in &op.before_updates {
                    bu.push((
                        v.clone(),
                        lower_poly_expr(
                            expr,
                            &coeff_domain,
                            &sv_set,
                            &arg_set,
                            &empty,
                            None,
                            &format!("{}.atomic_op.{}.before.{v}", decl.name, op.name),
                        )?,
                    ));
                }
                let mut au = Vec::with_capacity(op.after_updates.len());
                for (v, expr) in &op.after_updates {
                    au.push((
                        v.clone(),
                        lower_poly_expr(
                            expr,
                            &coeff_domain,
                            &sv_set,
                            &arg_set,
                            &empty,
                            None,
                            &format!("{}.atomic_op.{}.after.{v}", decl.name, op.name),
                        )?,
                    ));
                }
                atomic_ops.push(AtomicOpCompareSpec {
                    name: op.name.clone(),
                    arg_vars: op.arg_vars.clone(),
                    before_updates: bu,
                    after_updates: au,
                });
            }
            let mut extended_checks = Vec::with_capacity(ext.extended_checks.len());
            for chk in &ext.extended_checks {
                match chk {
                    ShigureExtendedOperationCheck::ProtocolSequence {
                        name,
                        extended_state_vars,
                        initial_state,
                        before_steps,
                        after_steps,
                        before_read,
                        after_read,
                        intermediate_laws,
                        ..
                    } => {
                        let esv: BTreeSet<String> = extended_state_vars.iter().cloned().collect();
                        let mut init = Vec::with_capacity(initial_state.len());
                        for (v, val) in initial_state {
                            init.push((
                                v.clone(),
                                lower_p4_coord_to_poly(
                                    val,
                                    archmap,
                                    snapshot_id,
                                    &coeff_domain,
                                    &primary_ref,
                                    &format!("{}.protocol_sequence.{name}.init.{v}", decl.name),
                                    &mut origins,
                                )?,
                            ));
                        }
                        let mut b_steps = Vec::with_capacity(before_steps.len());
                        for (i, st) in before_steps.iter().enumerate() {
                            let mut row = Vec::with_capacity(st.len());
                            for (v, expr) in st {
                                row.push((
                                    v.clone(),
                                    lower_poly_expr(
                                        expr,
                                        &coeff_domain,
                                        &esv,
                                        &empty,
                                        &empty,
                                        None,
                                        &format!("{}.protocol.{name}.before[{i}].{v}", decl.name),
                                    )?,
                                ));
                            }
                            b_steps.push(row);
                        }
                        let mut a_steps = Vec::with_capacity(after_steps.len());
                        for (i, st) in after_steps.iter().enumerate() {
                            let mut row = Vec::with_capacity(st.len());
                            for (v, expr) in st {
                                row.push((
                                    v.clone(),
                                    lower_poly_expr(
                                        expr,
                                        &coeff_domain,
                                        &esv,
                                        &empty,
                                        &empty,
                                        None,
                                        &format!("{}.protocol.{name}.after[{i}].{v}", decl.name),
                                    )?,
                                ));
                            }
                            a_steps.push(row);
                        }
                        let bread = lower_poly_expr(
                            before_read,
                            &coeff_domain,
                            &esv,
                            &empty,
                            &empty,
                            None,
                            &format!("{}.protocol.{name}.before_read", decl.name),
                        )?;
                        let aread = lower_poly_expr(
                            after_read,
                            &coeff_domain,
                            &esv,
                            &empty,
                            &empty,
                            None,
                            &format!("{}.protocol.{name}.after_read", decl.name),
                        )?;
                        let ilaws = lower_p4_named_polys(
                            intermediate_laws,
                            &coeff_domain,
                            &esv,
                            &empty,
                            &empty,
                            &primary_ref,
                            &format!("{}.protocol.{name}.intermediate_laws", decl.name),
                        )?;
                        extended_checks.push(ExtendedOperationCheckSpec::ProtocolSequence {
                            name: name.clone(),
                            extended_state_vars: extended_state_vars.clone(),
                            initial_state: init,
                            before_steps: b_steps,
                            after_steps: a_steps,
                            before_read: Box::new(bread),
                            after_read: Box::new(aread),
                            intermediate_laws: ilaws,
                        });
                    }
                    ShigureExtendedOperationCheck::RuntimeArgOp {
                        name,
                        before_updates,
                        after_updates,
                        sample_state,
                        ..
                    } => {
                        let mut bu = Vec::with_capacity(before_updates.len());
                        for (v, expr) in before_updates {
                            bu.push((
                                v.clone(),
                                lower_poly_expr(
                                    expr,
                                    &coeff_domain,
                                    &sv_set,
                                    &empty,
                                    &empty,
                                    None,
                                    &format!("{}.runtime_arg_op.{name}.before.{v}", decl.name),
                                )?,
                            ));
                        }
                        let mut au = Vec::with_capacity(after_updates.len());
                        for (v, expr) in after_updates {
                            au.push((
                                v.clone(),
                                lower_poly_expr(
                                    expr,
                                    &coeff_domain,
                                    &sv_set,
                                    &empty,
                                    &empty,
                                    None,
                                    &format!("{}.runtime_arg_op.{name}.after.{v}", decl.name),
                                )?,
                            ));
                        }
                        let mut ss = Vec::with_capacity(sample_state.len());
                        for (v, val) in sample_state {
                            ss.push((
                                v.clone(),
                                lower_p4_coord_to_poly(
                                    val,
                                    archmap,
                                    snapshot_id,
                                    &coeff_domain,
                                    &primary_ref,
                                    &format!("{}.runtime_arg_op.{name}.sample.{v}", decl.name),
                                    &mut origins,
                                )?,
                            ));
                        }
                        extended_checks.push(ExtendedOperationCheckSpec::RuntimeArgOp {
                            name: name.clone(),
                            before_updates: bu,
                            after_updates: au,
                            sample_state: ss,
                        });
                    }
                }
            }
            Ok::<_, ValidationError>(ExtendedLanguageCheckSpec {
                state_vars: ext.state_vars.clone(),
                adapter_map,
                atomic_ops,
                extended_checks,
            })
        })
        .transpose()?;

    validate_atlas_task(AtlasTaskSpec {
        name: decl.name.clone(),
        coeff_domain,
        vertices: decl.vertices.clone(),
        edges,
        mu,
        base_lambdas,
        allowed_vertices: decl.allowed_vertices.clone(),
        allowed_edges: decl.allowed_edges.clone(),
        compare_to_q: decl.compare_to_q,
        refinement,
        extended_language_check,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: Vec::new(),
        },
    })
}
