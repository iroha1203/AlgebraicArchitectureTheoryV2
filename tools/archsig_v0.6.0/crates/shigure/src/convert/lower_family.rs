//! `ShigureFamilySpec` → `FamilySpec` の厳密な lowering（由来・欠測保持）。

use super::lower::{
    ensure_editable_only_after, lower_change_spec, lower_coeff_domain, lower_comparison_pair,
    lower_presentation,
};
use super::lower_expr::{
    law_source_ref, lower_poly_expr, lower_scalar_lit, lower_shigure_origin_kind,
    resolve_archmap_origin, resolve_observed_coord,
};
use super::lower_morphism::resolve_decl;
use crate::ir::change::NamedPoly;
use crate::ir::family::{
    CandidateFamilySpec, CandidateMember, CandidateSpace, FamilySpec, GoodnessSpec,
    PreservationGoodnessSource, RawSequenceCheck, ReadingComparisonSpec, RealizationFamilySpec,
    RealizationMember, RealizationSpace,
};
use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::ValidationError;
use archsig_input::archmap::CheckedArchMap;
use archsig_input::law::shigure::{
    CheckedShigureDecls, ShigureCandidateSpace, ShigureFamilySpec, ShigureGoodnessSpec,
    ShigureMemberCoordValue, ShigureNamedPoly, ShigureOriginRef, ShigurePreservationSource,
    ShigureRealizationSpace,
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn lower_shigure_origin(
    origin: &ShigureOriginRef,
    archmap: &CheckedArchMap,
    law_decl: &str,
    context: &str,
) -> Result<Vec<SourceRef>, ValidationError> {
    match origin {
        ShigureOriginRef::Explicit { kind, id, .. } => Ok(vec![
            SourceRef::new(id, lower_shigure_origin_kind(*kind)).with_law_declaration(law_decl),
        ]),
        ShigureOriginRef::ArchMap { id, .. } => resolve_archmap_origin(archmap, id, context),
    }
}

pub(super) fn lower_param_named_polys(
    items: &[ShigureNamedPoly],
    coeff_domain: &CoeffDomain,
    allowed_params: &BTreeSet<String>,
    origin_ref: &SourceRef,
    scope_prefix: &str,
) -> Result<Vec<NamedPoly>, ValidationError> {
    let empty = BTreeSet::new();
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        let ctx = format!("{scope_prefix}.{}", item.name);
        let expr = lower_poly_expr(
            &item.expr,
            coeff_domain,
            &empty,
            &empty,
            allowed_params,
            None,
            &ctx,
        )?;
        out.push(NamedPoly {
            name: item.name.clone(),
            expr,
            provenance: Some(origin_ref.clone()),
        });
    }
    Ok(out)
}

fn lower_member_assignments(
    raw_assigns: &BTreeMap<String, ShigureMemberCoordValue>,
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    coeff_domain: &CoeffDomain,
    fallback_ref: &SourceRef,
    context: &str,
    collected_origins: &mut BTreeSet<SourceRef>,
) -> Result<BTreeMap<String, CoordValue>, ValidationError> {
    let mut out = BTreeMap::new();
    for (var, val) in raw_assigns {
        let cv = match val {
            ShigureMemberCoordValue::Literal(lit) => CoordValue::Observed(lower_scalar_lit(
                lit,
                coeff_domain,
                &format!("{context}.{var}"),
            )?),
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
                    collected_origins.insert(r);
                }
                cv
            }
            ShigureMemberCoordValue::Missing => CoordValue::Missing,
        };
        out.insert(var.clone(), cv);
    }
    Ok(out)
}

fn lower_preservation_source(
    pres: &ShigurePreservationSource,
    shigure: &CheckedShigureDecls,
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
    allowed_vars: &BTreeSet<String>,
    context: &str,
    collected_origins: &mut BTreeSet<SourceRef>,
) -> Result<PreservationGoodnessSource, ValidationError> {
    let cmp_decl = resolve_decl(
        &shigure.comparisons,
        &pres.comparison,
        "shigure comparison",
        context,
    )?;
    let spec_decl = resolve_decl(
        &shigure.change_specs,
        &pres.change_spec,
        "shigure change_spec",
        context,
    )?;
    let b_decl = resolve_decl(
        &shigure.presentations,
        &cmp_decl.before,
        "presentation",
        &cmp_decl.name,
    )?;
    let a_decl = resolve_decl(
        &shigure.presentations,
        &cmp_decl.after,
        "presentation",
        &cmp_decl.name,
    )?;
    let spec_params: BTreeSet<String> = spec_decl
        .parameters
        .iter()
        .map(|p| p.name.clone())
        .collect();
    let empty = BTreeSet::new();
    let before = lower_presentation(b_decl, archmap, snapshot_id, &empty, Some(&spec_params))?;
    let after = lower_presentation(a_decl, archmap, snapshot_id, &spec_params, None)?;
    let pair = lower_comparison_pair(cmp_decl, before, after, &spec_params)?;
    let change_spec = lower_change_spec(spec_decl);
    let coeff_domain = &change_spec.coeff_domain;
    ensure_editable_only_after(&change_spec, &pair.after.name)?;

    for o in pair
        .before
        .provenance
        .origins
        .iter()
        .chain(&pair.after.provenance.origins)
        .chain(&change_spec.provenance.origins)
    {
        collected_origins.insert(o.clone());
    }

    let mut param_bindings = BTreeMap::new();
    for (param, expr) in &pres.param_bindings {
        let ctx = format!("{context}.preservation.bind.{param}");
        let lowered =
            lower_poly_expr(expr, coeff_domain, &empty, &empty, allowed_vars, None, &ctx)?;
        param_bindings.insert(param.clone(), lowered);
    }

    Ok(PreservationGoodnessSource {
        pair,
        change_spec,
        param_bindings,
    })
}

pub(super) fn lower_family(
    decl: &ShigureFamilySpec,
    shigure: &CheckedShigureDecls,
    archmap: &CheckedArchMap,
    snapshot_id: Option<&str>,
) -> Result<(FamilySpec, BTreeSet<SourceRef>), ValidationError> {
    let coeff_domain = lower_coeff_domain(&decl.coeff_domain);
    let fam_ref = law_source_ref(&decl.name);
    let mut origins = BTreeSet::from([fam_ref.clone()]);
    let empty = BTreeSet::new();

    let u_set: BTreeSet<String> = decl.realizations.u_vars.iter().cloned().collect();
    let c_set: BTreeSet<String> = decl.candidates.c_vars.iter().cloned().collect();

    let mut reading_q = Vec::with_capacity(decl.realizations.reading_q.len());
    for (idx, expr) in decl.realizations.reading_q.iter().enumerate() {
        reading_q.push(lower_poly_expr(
            expr,
            &coeff_domain,
            &empty,
            &empty,
            &u_set,
            None,
            &format!("{}.reading_q[{idx}]", decl.name),
        )?);
    }

    let real_space = match &decl.realizations.space {
        ShigureRealizationSpace::FiniteMembers(members) => {
            let mut out = Vec::with_capacity(members.len());
            for m in members {
                let refs = lower_shigure_origin(
                    &m.origin,
                    archmap,
                    &decl.name,
                    &format!("{}.realizations.{}", decl.name, m.id),
                )?;
                let primary_origin = refs[0].clone();
                for r in refs {
                    origins.insert(r);
                }
                let assignments = lower_member_assignments(
                    &m.assignments,
                    archmap,
                    snapshot_id,
                    &coeff_domain,
                    &primary_origin,
                    &format!("{}.realizations.{}", decl.name, m.id),
                    &mut origins,
                )?;
                let presentation = m
                    .presentation
                    .as_ref()
                    .map(|p_name| {
                        let p_decl = resolve_decl(
                            &shigure.presentations,
                            p_name,
                            "presentation",
                            &format!("{}.{}", decl.name, m.id),
                        )?;
                        let lowered =
                            lower_presentation(p_decl, archmap, snapshot_id, &empty, None)?;
                        for o in &lowered.provenance.origins {
                            origins.insert(o.clone());
                        }
                        Ok::<_, ValidationError>(lowered)
                    })
                    .transpose()?;
                out.push(RealizationMember {
                    id: m.id.clone(),
                    assignments,
                    is_raw_candidate: m.is_raw_candidate,
                    presentation,
                    origin: primary_origin,
                });
            }
            RealizationSpace::FiniteMembers(out)
        }
        ShigureRealizationSpace::PolynomialScheme {
            equations,
            invertibles,
            is_raw_candidate,
            origin,
        } => {
            let refs = lower_shigure_origin(
                origin,
                archmap,
                &decl.name,
                &format!("{}.realizations.scheme", decl.name),
            )?;
            let primary_origin = refs[0].clone();
            for r in refs {
                origins.insert(r);
            }
            let eqs = lower_param_named_polys(
                equations,
                &coeff_domain,
                &u_set,
                &primary_origin,
                &format!("{}.realizations.equation", decl.name),
            )?;
            let invs = lower_param_named_polys(
                invertibles,
                &coeff_domain,
                &u_set,
                &primary_origin,
                &format!("{}.realizations.invertible", decl.name),
            )?;
            RealizationSpace::PolynomialScheme {
                equations: eqs,
                invertibles: invs,
                is_raw_candidate: *is_raw_candidate,
                origin: primary_origin,
            }
        }
    };

    let mut pi = Vec::with_capacity(decl.candidates.pi.len());
    for (idx, expr) in decl.candidates.pi.iter().enumerate() {
        pi.push(lower_poly_expr(
            expr,
            &coeff_domain,
            &empty,
            &empty,
            &c_set,
            None,
            &format!("{}.pi[{idx}]", decl.name),
        )?);
    }

    let cand_space = match &decl.candidates.space {
        ShigureCandidateSpace::FiniteMembers(members) => {
            let mut out = Vec::with_capacity(members.len());
            for m in members {
                let refs = lower_shigure_origin(
                    &m.origin,
                    archmap,
                    &decl.name,
                    &format!("{}.candidates.{}", decl.name, m.id),
                )?;
                let primary_origin = refs[0].clone();
                for r in refs {
                    origins.insert(r);
                }
                let assignments = lower_member_assignments(
                    &m.assignments,
                    archmap,
                    snapshot_id,
                    &coeff_domain,
                    &primary_origin,
                    &format!("{}.candidates.{}", decl.name, m.id),
                    &mut origins,
                )?;
                out.push(CandidateMember {
                    id: m.id.clone(),
                    assignments,
                    origin: primary_origin,
                });
            }
            CandidateSpace::FiniteMembers(out)
        }
        ShigureCandidateSpace::PolynomialScheme {
            equations,
            invertibles,
            origin,
        } => {
            let refs = lower_shigure_origin(
                origin,
                archmap,
                &decl.name,
                &format!("{}.candidates.scheme", decl.name),
            )?;
            let primary_origin = refs[0].clone();
            for r in refs {
                origins.insert(r);
            }
            let eqs = lower_param_named_polys(
                equations,
                &coeff_domain,
                &c_set,
                &primary_origin,
                &format!("{}.candidates.equation", decl.name),
            )?;
            let invs = lower_param_named_polys(
                invertibles,
                &coeff_domain,
                &c_set,
                &primary_origin,
                &format!("{}.candidates.invertible", decl.name),
            )?;
            CandidateSpace::PolynomialScheme {
                equations: eqs,
                invertibles: invs,
                origin: primary_origin,
            }
        }
    };

    let goodness = match &decl.goodness {
        ShigureGoodnessSpec::Direct {
            equations,
            invertibles,
            preservation,
            raw_sequence,
        } => {
            let uc_set: BTreeSet<String> = u_set.union(&c_set).cloned().collect();
            let eqs = lower_param_named_polys(
                equations,
                &coeff_domain,
                &uc_set,
                &fam_ref,
                &format!("{}.goodness.equation", decl.name),
            )?;
            let invs = lower_param_named_polys(
                invertibles,
                &coeff_domain,
                &uc_set,
                &fam_ref,
                &format!("{}.goodness.invertible", decl.name),
            )?;
            let pres = preservation
                .as_ref()
                .map(|p| {
                    lower_preservation_source(
                        p,
                        shigure,
                        archmap,
                        snapshot_id,
                        &uc_set,
                        &decl.name,
                        &mut origins,
                    )
                })
                .transpose()?;
            let seq = raw_sequence
                .as_ref()
                .map(|rs| {
                    let mut start_state = BTreeMap::new();
                    for (coord, lit) in &rs.start_state {
                        start_state.insert(
                            coord.clone(),
                            lower_scalar_lit(
                                lit,
                                &coeff_domain,
                                &format!("{}.raw_sequence.start_state.{coord}", decl.name),
                            )?,
                        );
                    }
                    let mut steps = Vec::with_capacity(rs.steps.len());
                    for (idx, (op, args)) in rs.steps.iter().enumerate() {
                        let mut lits = Vec::with_capacity(args.len());
                        for a in args {
                            lits.push(lower_scalar_lit(
                                a,
                                &coeff_domain,
                                &format!("{}.raw_sequence.step[{idx}]", decl.name),
                            )?);
                        }
                        steps.push((op.clone(), lits));
                    }
                    Ok::<_, ValidationError>(RawSequenceCheck {
                        start_phase: rs.start_phase.clone(),
                        start_state,
                        steps,
                        observation_name: rs.observation_name.clone(),
                        baseline_step_index: rs.baseline_step_index,
                        provenance: Provenance {
                            origins: vec![fam_ref.clone()],
                            clauses: vec![],
                        },
                    })
                })
                .transpose()?;
            GoodnessSpec::Direct {
                equations: eqs,
                invertibles: invs,
                preservation: pres,
                raw_sequence: seq,
            }
        }
        ShigureGoodnessSpec::Existential {
            witness_vars,
            equations,
            invertibles,
            preservation,
        } => {
            let mut ucw_set: BTreeSet<String> = u_set.union(&c_set).cloned().collect();
            for w in witness_vars {
                ucw_set.insert(w.clone());
            }
            let eqs = lower_param_named_polys(
                equations,
                &coeff_domain,
                &ucw_set,
                &fam_ref,
                &format!("{}.goodness.equation", decl.name),
            )?;
            let invs = lower_param_named_polys(
                invertibles,
                &coeff_domain,
                &ucw_set,
                &fam_ref,
                &format!("{}.goodness.invertible", decl.name),
            )?;
            let pres = preservation
                .as_ref()
                .map(|p| {
                    lower_preservation_source(
                        p,
                        shigure,
                        archmap,
                        snapshot_id,
                        &ucw_set,
                        &decl.name,
                        &mut origins,
                    )
                })
                .transpose()?;
            GoodnessSpec::Existential {
                witness_vars: witness_vars.clone(),
                equations: eqs,
                invertibles: invs,
                preservation: pres,
            }
        }
    };

    let reading_comparison = decl
        .reading_comparison
        .as_ref()
        .map(|rc| {
            let fine_b_set: BTreeSet<String> = rc.fine_b_vars.iter().cloned().collect();
            let mut fine_q: Vec<PolyExpr> = Vec::with_capacity(rc.fine_q.len());
            for (i, expr) in rc.fine_q.iter().enumerate() {
                fine_q.push(lower_poly_expr(
                    expr,
                    &coeff_domain,
                    &empty,
                    &empty,
                    &u_set,
                    None,
                    &format!("{}.reading_comparison.fine_q[{i}]", decl.name),
                )?);
            }
            let mut coarsen_r: Vec<PolyExpr> = Vec::with_capacity(rc.coarsen_r.len());
            for (i, expr) in rc.coarsen_r.iter().enumerate() {
                coarsen_r.push(lower_poly_expr(
                    expr,
                    &coeff_domain,
                    &empty,
                    &empty,
                    &fine_b_set,
                    None,
                    &format!("{}.reading_comparison.coarsen_r[{i}]", decl.name),
                )?);
            }
            Ok::<_, ValidationError>(ReadingComparisonSpec {
                name: rc.name.clone(),
                fine_b_vars: rc.fine_b_vars.clone(),
                fine_q,
                coarsen_r,
                provenance: Provenance {
                    origins: vec![fam_ref.clone()],
                    clauses: vec![],
                },
            })
        })
        .transpose()?;

    let spec = FamilySpec {
        name: decl.name.clone(),
        coeff_domain,
        realizations: RealizationFamilySpec {
            name: decl.realizations.name.clone(),
            u_vars: decl.realizations.u_vars.clone(),
            b_vars: decl.realizations.b_vars.clone(),
            reading_q,
            space: real_space,
        },
        candidates: CandidateFamilySpec {
            name: decl.candidates.name.clone(),
            c_vars: decl.candidates.c_vars.clone(),
            pi,
            space: cand_space,
        },
        goodness,
        reading_comparison,
        provenance: Provenance {
            origins: origins.iter().cloned().collect(),
            clauses: vec![],
        },
    };
    Ok((spec, origins))
}
