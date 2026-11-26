//! `CheckedInputs` から `CheckedLiftTask` / `CheckedArtinTask` への lowering（Phase 4 / AC2）。

use super::lower::lower_coeff_domain;
use super::lower_expr::{
    conv_err, law_source_ref, lower_poly_expr, lower_scalar_lit, resolve_observed_coord,
};
use super::lower_family::lower_shigure_origin;
use super::lower_morphism::{ensure_snapshot_exists, select_named_decl};
use crate::ir::artin::{
    ArtinTaskSpec, AuxiliaryDefSpec, BaseChangeSpec, CheckedArtinTask, CompositeStageSpec,
    validate_artin_task,
};
use crate::ir::change::NamedPoly;
use crate::ir::lift::{
    AffineAllowedSpec, CheckedLiftTask, DeclarationContextSpec, DeclarationCoverSpec,
    FiniteEtaleDescentSpec, LiftTaskSpec, RawReadComparisonSpec, RedundantLawComparisonSpec,
    RelativeReadingSpec, RingParamSpec, SquareZeroSpec, TwoContextCechSpec, validate_lift_task,
};
use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::ValidationError;
use archsig_input::archmap::CheckedArchMap;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{
    ShigureMemberCoordValue, ShigureNamedPoly, ShigureOriginRef, ShigureScalarLit,
    ShigureSquareZeroSpec,
};
use std::collections::BTreeSet;

pub(super) fn lower_p4_origins(
    raw: &[ShigureOriginRef],
    archmap: &CheckedArchMap,
    decl_name: &str,
    context: &str,
) -> Result<(BTreeSet<SourceRef>, SourceRef), ValidationError> {
    let mut origins = BTreeSet::new();
    let mut primary: Option<SourceRef> = None;
    for orig in raw {
        let refs = lower_shigure_origin(orig, archmap, decl_name, context)?;
        if primary.is_none()
            && let Some(first) = refs.first()
        {
            primary = Some(first.clone());
        }
        for r in refs {
            origins.insert(r);
        }
    }
    let primary_ref = primary.unwrap_or_else(|| law_source_ref(decl_name));
    origins.insert(law_source_ref(decl_name));
    Ok((origins, primary_ref))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_p4_coord_to_poly(
    val: &ShigureMemberCoordValue,
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    coeff_domain: &CoeffDomain,
    fallback_ref: &SourceRef,
    slot_label: &str,
    origins: &mut BTreeSet<SourceRef>,
) -> Result<PolyExpr, ValidationError> {
    match val {
        ShigureMemberCoordValue::Literal(lit) => Ok(PolyExpr::Const(lower_scalar_lit(
            lit,
            coeff_domain,
            slot_label,
        )?)),
        ShigureMemberCoordValue::ObservedField { entity, field, .. } => {
            let (cv, refs) = resolve_observed_coord(
                archmap,
                snapshot_id,
                entity,
                field,
                coeff_domain,
                fallback_ref,
            )?;
            let first_ref = refs.first().cloned();
            for r in refs {
                origins.insert(r);
            }
            match cv {
                CoordValue::Observed(lit) => Ok(PolyExpr::Const(lit)),
                CoordValue::Missing => Ok(PolyExpr::Unobserved {
                    slot: if field.starts_with(&format!("{entity}.")) {
                        field.clone()
                    } else {
                        format!("{entity}.{field}")
                    },
                    origin: first_ref.or_else(|| Some(fallback_ref.clone())),
                }),
                CoordValue::Symbolic => Err(conv_err(format!(
                    "unexpected symbolic coord value for observed field `{entity}.{field}`"
                ))),
            }
        }
        ShigureMemberCoordValue::Missing => Ok(PolyExpr::Unobserved {
            slot: slot_label.to_owned(),
            origin: Some(fallback_ref.clone()),
        }),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_p4_coord_vec(
    vals: &[ShigureMemberCoordValue],
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    coeff_domain: &CoeffDomain,
    fallback_ref: &SourceRef,
    prefix: &str,
    origins: &mut BTreeSet<SourceRef>,
) -> Result<Vec<PolyExpr>, ValidationError> {
    vals.iter()
        .enumerate()
        .map(|(i, v)| {
            lower_p4_coord_to_poly(
                v,
                archmap,
                snapshot_id,
                coeff_domain,
                fallback_ref,
                &format!("{prefix}[{i}]"),
                origins,
            )
        })
        .collect()
}

pub(super) fn lower_p4_named_polys(
    items: &[ShigureNamedPoly],
    coeff_domain: &CoeffDomain,
    state_vars: &BTreeSet<String>,
    arg_vars: &BTreeSet<String>,
    param_vars: &BTreeSet<String>,
    origin_ref: &SourceRef,
    scope: &str,
) -> Result<Vec<NamedPoly>, ValidationError> {
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        let expr = lower_poly_expr(
            &item.expr,
            coeff_domain,
            state_vars,
            arg_vars,
            param_vars,
            None,
            &format!("{scope}.{}", item.name),
        )?;
        out.push(NamedPoly {
            name: item.name.clone(),
            expr,
            provenance: Some(origin_ref.clone()),
        });
    }
    Ok(out)
}

fn lower_lit_vec(
    lits: &[ShigureScalarLit],
    coeff_domain: &CoeffDomain,
    context: &str,
) -> Result<Vec<ScalarLit>, ValidationError> {
    lits.iter()
        .enumerate()
        .map(|(i, l)| lower_scalar_lit(l, coeff_domain, &format!("{context}[{i}]")))
        .collect()
}

fn lower_square_zero_spec(
    raw: &ShigureSquareZeroSpec,
    coeff_domain: &CoeffDomain,
    context: &str,
) -> Result<SquareZeroSpec, ValidationError> {
    match raw {
        ShigureSquareZeroSpec::TruncatedPoly {
            var_name,
            base_degree,
            ..
        } => Ok(SquareZeroSpec::TruncatedPoly {
            var_name: var_name.clone(),
            base_degree: *base_degree,
        }),
        ShigureSquareZeroSpec::ExplicitTable {
            r_prime_basis,
            r_prime_one,
            r_prime_mul,
            r_base_basis,
            r_base_one,
            r_base_mul,
            projection,
            ..
        } => {
            let mut rpm = Vec::with_capacity(r_prime_mul.len());
            for (i, mat) in r_prime_mul.iter().enumerate() {
                let mut rows = Vec::with_capacity(mat.len());
                for (j, row) in mat.iter().enumerate() {
                    rows.push(lower_lit_vec(
                        row,
                        coeff_domain,
                        &format!("{context}.r_prime_mul[{i}][{j}]"),
                    )?);
                }
                rpm.push(rows);
            }
            let mut rbm = Vec::with_capacity(r_base_mul.len());
            for (i, mat) in r_base_mul.iter().enumerate() {
                let mut rows = Vec::with_capacity(mat.len());
                for (j, row) in mat.iter().enumerate() {
                    rows.push(lower_lit_vec(
                        row,
                        coeff_domain,
                        &format!("{context}.r_base_mul[{i}][{j}]"),
                    )?);
                }
                rbm.push(rows);
            }
            let mut proj = Vec::with_capacity(projection.len());
            for (i, row) in projection.iter().enumerate() {
                proj.push(lower_lit_vec(
                    row,
                    coeff_domain,
                    &format!("{context}.projection[{i}]"),
                )?);
            }
            Ok(SquareZeroSpec::ExplicitTable {
                r_prime_basis: r_prime_basis.clone(),
                r_prime_one: lower_lit_vec(
                    r_prime_one,
                    coeff_domain,
                    &format!("{context}.r_prime_one"),
                )?,
                r_prime_mul: rpm,
                r_base_basis: r_base_basis.clone(),
                r_base_one: lower_lit_vec(
                    r_base_one,
                    coeff_domain,
                    &format!("{context}.r_base_one"),
                )?,
                r_base_mul: rbm,
                projection: proj,
            })
        }
    }
}

pub(super) fn convert_lift_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedLiftTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) = select_named_decl(&shigure.lift_tasks, task_name, "shigure lift")?;
    let coeff_domain = lower_coeff_domain(&decl.coeff_domain);
    let (mut origins, primary_ref) =
        lower_p4_origins(&decl.origins, archmap, &decl.name, &decl.name)?;

    let var_set: BTreeSet<String> = decl.variables.iter().cloned().collect();
    let param_set: BTreeSet<String> = decl.ring_params.iter().map(|p| p.name.clone()).collect();
    let empty = BTreeSet::new();

    let mut ring_params = Vec::with_capacity(decl.ring_params.len());
    for rp in &decl.ring_params {
        let coords = lower_p4_coord_vec(
            &rp.value_in_r_prime,
            archmap,
            snapshot_id,
            &coeff_domain,
            &primary_ref,
            &format!("{}.ring_param.{}", decl.name, rp.name),
            &mut origins,
        )?;
        ring_params.push(RingParamSpec {
            name: rp.name.clone(),
            value_in_r_prime: coords,
        });
    }

    let laws = lower_p4_named_polys(
        &decl.laws,
        &coeff_domain,
        &var_set,
        &empty,
        &param_set,
        &primary_ref,
        &format!("{}.laws", decl.name),
    )?;

    let extension = lower_square_zero_spec(
        &decl.extension,
        &coeff_domain,
        &format!("{}.extension", decl.name),
    )?;

    let mut base_point = Vec::with_capacity(decl.base_point.len());
    for (v, vals) in &decl.base_point {
        base_point.push((
            v.clone(),
            lower_p4_coord_vec(
                vals,
                archmap,
                snapshot_id,
                &coeff_domain,
                &primary_ref,
                &format!("{}.base_point.{v}", decl.name),
                &mut origins,
            )?,
        ));
    }

    let ambient_lift = decl
        .ambient_lift
        .as_ref()
        .map(|al| {
            let mut out = Vec::with_capacity(al.len());
            for (v, vals) in al {
                out.push((
                    v.clone(),
                    lower_p4_coord_vec(
                        vals,
                        archmap,
                        snapshot_id,
                        &coeff_domain,
                        &primary_ref,
                        &format!("{}.ambient_lift.{v}", decl.name),
                        &mut origins,
                    )?,
                ));
            }
            Ok::<_, ValidationError>(out)
        })
        .transpose()?;

    let relative_reading = decl
        .relative_reading
        .as_ref()
        .map(|rel| {
            let obs_set: BTreeSet<String> = rel.obs_vars.iter().cloned().collect();
            let obs_laws = lower_p4_named_polys(
                &rel.obs_laws,
                &coeff_domain,
                &obs_set,
                &empty,
                &param_set,
                &primary_ref,
                &format!("{}.obs_laws", decl.name),
            )?;
            let mut reading_map = Vec::with_capacity(rel.reading_map.len());
            for (ov, expr) in &rel.reading_map {
                reading_map.push((
                    ov.clone(),
                    lower_poly_expr(
                        expr,
                        &coeff_domain,
                        &var_set,
                        &empty,
                        &param_set,
                        None,
                        &format!("{}.reading_map.{ov}", decl.name),
                    )?,
                ));
            }
            let mut designated_obs_lift = Vec::with_capacity(rel.designated_obs_lift.len());
            for (ov, vals) in &rel.designated_obs_lift {
                designated_obs_lift.push((
                    ov.clone(),
                    lower_p4_coord_vec(
                        vals,
                        archmap,
                        snapshot_id,
                        &coeff_domain,
                        &primary_ref,
                        &format!("{}.designated_obs_lift.{ov}", decl.name),
                        &mut origins,
                    )?,
                ));
            }
            let raw_read_diff = rel
                .raw_read_diff
                .as_ref()
                .map(|rr| {
                    Ok::<_, ValidationError>(RawReadComparisonSpec {
                        label: rr.label.clone(),
                        expr: lower_poly_expr(
                            &rr.expr,
                            &coeff_domain,
                            &var_set,
                            &empty,
                            &param_set,
                            None,
                            &format!("{}.raw_read_diff", decl.name),
                        )?,
                        negated: rr.negated,
                    })
                })
                .transpose()?;
            Ok::<_, ValidationError>(RelativeReadingSpec {
                obs_vars: rel.obs_vars.clone(),
                obs_laws,
                reading_map,
                designated_obs_lift,
                raw_read_diff,
            })
        })
        .transpose()?;

    let declaration_cover = decl
        .declaration_cover
        .as_ref()
        .map(|cov| {
            let mut contexts = Vec::with_capacity(cov.contexts.len());
            for c in &cov.contexts {
                let obs = lower_p4_named_polys(
                    &c.observations,
                    &coeff_domain,
                    &var_set,
                    &empty,
                    &param_set,
                    &primary_ref,
                    &format!("{}.context.{}.obs", decl.name, c.name),
                )?;
                contexts.push(DeclarationContextSpec {
                    name: c.name.clone(),
                    vars: c.vars.clone(),
                    laws: c.laws.clone(),
                    observations: obs,
                });
            }
            let two_context_cech = cov.two_context_cech.as_ref().map(|tc| TwoContextCechSpec {
                left_context: tc.left_context.clone(),
                right_context: tc.right_context.clone(),
                shared_vars: tc.shared_vars.clone(),
            });
            Ok::<_, ValidationError>(DeclarationCoverSpec {
                contexts,
                two_context_cech,
            })
        })
        .transpose()?;

    let affine_allowed = decl.affine_allowed.as_ref().map(|a| AffineAllowedSpec {
        allowed_vars: a.allowed_vars.clone(),
        finite_displacement: a.finite_displacement,
    });

    let redundant_comparison = decl
        .redundant_comparison
        .as_ref()
        .map(|rc| {
            let ref_laws = lower_p4_named_polys(
                &rc.reference_laws,
                &coeff_domain,
                &var_set,
                &empty,
                &param_set,
                &primary_ref,
                &format!("{}.redundant_comparison", decl.name),
            )?;
            Ok::<_, ValidationError>(RedundantLawComparisonSpec {
                reference_laws: ref_laws,
            })
        })
        .transpose()?;

    let etale_descent = decl
        .etale_descent
        .as_ref()
        .map(|ed| FiniteEtaleDescentSpec {
            base_var: ed.base_var.clone(),
            cover_var: ed.cover_var.clone(),
            degree: ed.degree,
            base_invertible: ed.base_invertible,
        });

    validate_lift_task(LiftTaskSpec {
        name: decl.name.clone(),
        coeff_domain,
        variables: decl.variables.clone(),
        ring_params,
        laws,
        extension,
        base_point,
        ambient_lift,
        relative_reading,
        declaration_cover,
        affine_allowed,
        redundant_comparison,
        etale_descent,
        max_syzygy_pairs: decl.max_syzygy_pairs,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: Vec::new(),
        },
    })
}

pub(super) fn convert_artin_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedArtinTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let (_, decl) = select_named_decl(&shigure.artin_tasks, task_name, "shigure artin")?;
    let coeff_domain = lower_coeff_domain(&decl.coeff_domain);
    let (mut origins, primary_ref) =
        lower_p4_origins(&decl.origins, archmap, &decl.name, &decl.name)?;

    let empty = BTreeSet::new();
    let obs_set: BTreeSet<String> = decl.obs_vars.iter().cloned().collect();
    let obs_relations = lower_p4_named_polys(
        &decl.obs_relations,
        &coeff_domain,
        &obs_set,
        &empty,
        &empty,
        &primary_ref,
        &format!("{}.obs_relations", decl.name),
    )?;

    let mut available = obs_set.clone();
    let mut aux_defs = Vec::with_capacity(decl.aux_defs.len());
    for aux in &decl.aux_defs {
        let expr = lower_poly_expr(
            &aux.expr,
            &coeff_domain,
            &available,
            &empty,
            &empty,
            None,
            &format!("{}.aux_def.{}", decl.name, aux.name),
        )?;
        available.insert(aux.name.clone());
        aux_defs.push(AuxiliaryDefSpec {
            name: aux.name.clone(),
            expr,
        });
    }

    let extra_laws = lower_p4_named_polys(
        &decl.extra_laws,
        &coeff_domain,
        &available,
        &empty,
        &empty,
        &primary_ref,
        &format!("{}.extra_laws", decl.name),
    )?;

    let mut base_point = Vec::with_capacity(decl.base_point.len());
    for (v, val) in &decl.base_point {
        base_point.push((
            v.clone(),
            lower_p4_coord_to_poly(
                val,
                archmap,
                snapshot_id,
                &coeff_domain,
                &primary_ref,
                &format!("{}.base_point.{v}", decl.name),
                &mut origins,
            )?,
        ));
    }

    let composite_stage = decl
        .composite_stage
        .as_ref()
        .map(|cs| {
            let mut stage_avail = available.clone();
            let mut stage_aux = Vec::with_capacity(cs.aux_defs.len());
            for aux in &cs.aux_defs {
                let expr = lower_poly_expr(
                    &aux.expr,
                    &coeff_domain,
                    &stage_avail,
                    &empty,
                    &empty,
                    None,
                    &format!("{}.composite_stage.aux_def.{}", decl.name, aux.name),
                )?;
                stage_avail.insert(aux.name.clone());
                stage_aux.push(AuxiliaryDefSpec {
                    name: aux.name.clone(),
                    expr,
                });
            }
            let stage_laws = lower_p4_named_polys(
                &cs.extra_laws,
                &coeff_domain,
                &stage_avail,
                &empty,
                &empty,
                &primary_ref,
                &format!("{}.composite_stage.extra_laws", decl.name),
            )?;
            Ok::<_, ValidationError>(CompositeStageSpec {
                aux_defs: stage_aux,
                extra_laws: stage_laws,
            })
        })
        .transpose()?;

    let base_change = decl.base_change.as_ref().map(|bc| BaseChangeSpec {
        target_domain: lower_coeff_domain(&bc.target_domain),
        test_order: bc.test_order,
    });

    validate_artin_task(ArtinTaskSpec {
        name: decl.name.clone(),
        coeff_domain,
        obs_vars: decl.obs_vars.clone(),
        obs_relations,
        aux_defs,
        extra_laws,
        base_point,
        max_order: decl.max_order,
        max_artin_dim: decl.max_artin_dim,
        composite_stage,
        base_change,
        non_noetherian_infinite: decl.non_noetherian_infinite,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: Vec::new(),
        },
    })
}
