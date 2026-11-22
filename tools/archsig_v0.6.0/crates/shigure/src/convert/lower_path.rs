//! `CheckedInputs` から `CheckedPathTask` への厳密な lowering。

use super::lower::{
    lower_change_spec, lower_comparison_pair, lower_eval_condition, lower_law_kind,
    lower_presentation,
};
use super::lower_expr::{conv_err, law_source_ref, lower_poly_expr, lower_scalar_lit};
use super::lower_morphism::{
    collect_eval_origins, ensure_snapshot_exists, lower_direction, lower_morphism_body,
    resolve_decl, select_named_decl,
};
use crate::ir::change::NamedPoly;
use crate::ir::morphism::MorphismDirection;
use crate::ir::path::{
    CheckedPathTask, ModelEndpoint, OneStepRule, PathKind, PathQueryMode, PathSpec,
    ProtocolExecutionSpec,
};
use crate::ir::presentation::StateLaw;
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::validate::ValidationError;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{
    ShigureModelEndpoint, ShigurePathKind, ShigurePathQueryMode, ShigureStateLawDecl,
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn convert_path_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedPathTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let (_, decl) = select_named_decl(&shigure.paths, task_name, "shigure path")?;
    let archmap = inputs.archmap();
    ensure_snapshot_exists(archmap, snapshot_id, "ShigureConverter::with_snapshot")?;

    let spec_decl = resolve_decl(
        &shigure.change_specs,
        &decl.change_spec,
        "shigure change_spec",
        &decl.name,
    )?;
    let change_spec = lower_change_spec(spec_decl);
    let param_names: BTreeSet<String> = change_spec
        .parameters
        .iter()
        .map(|p| p.name.clone())
        .collect();
    let empty_params = BTreeSet::new();

    let path_ref = law_source_ref(&decl.name);
    let mut origins: BTreeSet<SourceRef> = BTreeSet::from([path_ref.clone()]);
    for o in &change_spec.provenance.origins {
        origins.insert(o.clone());
    }

    let eval_condition = decl
        .eval_condition
        .as_ref()
        .map(|ec_name| {
            let ec = resolve_decl(
                &shigure.eval_conditions,
                ec_name,
                "eval_condition",
                &decl.name,
            )?;
            lower_eval_condition(ec, &change_spec.coeff_domain, &param_names)
        })
        .transpose()?;
    collect_eval_origins(eval_condition.as_ref(), &mut origins);

    let kind = match decl.kind {
        ShigurePathKind::FixedProtocolChangePath => PathKind::FixedProtocolChangePath,
        ShigurePathKind::EnlargedProtocolExecutionPath => PathKind::EnlargedProtocolExecutionPath,
    };
    let direction = lower_direction(decl.direction);

    let mut vertices = BTreeMap::new();
    for (v_name, pres_name) in &decl.vertices {
        let pres_decl = resolve_decl(
            &shigure.presentations,
            pres_name,
            "presentation",
            &decl.name,
        )?;
        let pres = lower_presentation(pres_decl, archmap, snapshot_id, &param_names, None)?;
        for o in &pres.provenance.origins {
            origins.insert(o.clone());
        }
        vertices.insert(v_name.clone(), pres);
    }

    let lower_ep =
        |ep: &ShigureModelEndpoint, label: &str| -> Result<ModelEndpoint, ValidationError> {
            let mut param_values = BTreeMap::new();
            for (p_name, lit) in &ep.param_values {
                let ctx = format!("{}.{label}.param.{p_name}", decl.name);
                param_values.insert(
                    p_name.clone(),
                    lower_scalar_lit(lit, &change_spec.coeff_domain, &ctx)?,
                );
            }
            Ok(ModelEndpoint {
                vertex: ep.vertex.clone(),
                param_values,
            })
        };
    let start = decl
        .start
        .as_ref()
        .map(|ep| lower_ep(ep, "start"))
        .transpose()?;
    let end = decl
        .end
        .as_ref()
        .map(|ep| lower_ep(ep, "end"))
        .transpose()?;

    let mut rules = Vec::with_capacity(decl.rules.len());
    for r in &decl.rules {
        let from_p = vertices
            .get(&r.from_vertex)
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "path vertex",
                name: r.from_vertex.clone(),
                context: format!("{}.rule.{}", decl.name, r.name),
            })?;
        let to_p = vertices
            .get(&r.to_vertex)
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "path vertex",
                name: r.to_vertex.clone(),
                context: format!("{}.rule.{}", decl.name, r.name),
            })?;
        let (m_src, m_tgt) = match direction {
            MorphismDirection::StateMap => (from_p, to_p),
            MorphismDirection::TimeOrder => (to_p, from_p),
        };
        let mut param_guards = Vec::with_capacity(r.param_guards.len());
        for (g_name, g_expr, _) in &r.param_guards {
            let ctx = format!("{}.rule.{}.guard.{g_name}", decl.name, r.name);
            let expr = lower_poly_expr(
                g_expr,
                &change_spec.coeff_domain,
                &empty_params,
                &empty_params,
                &param_names,
                None,
                &ctx,
            )?;
            param_guards.push(NamedPoly {
                name: g_name.clone(),
                expr,
                provenance: Some(path_ref.clone()),
            });
        }
        let mut param_updates = BTreeMap::new();
        for (p_name, u_expr) in &r.param_updates {
            let ctx = format!("{}.rule.{}.update.{p_name}", decl.name, r.name);
            let expr = lower_poly_expr(
                u_expr,
                &change_spec.coeff_domain,
                &empty_params,
                &empty_params,
                &param_names,
                None,
                &ctx,
            )?;
            param_updates.insert(p_name.clone(), expr);
        }
        let morphism = lower_morphism_body(
            &r.morphism,
            &shigure.comparisons,
            m_src,
            m_tgt,
            &param_names,
            None,
            &path_ref,
            &format!("{}.rule.{}", decl.name, r.name),
        )?;
        let r_ec = r
            .eval_condition
            .as_ref()
            .map(|ec_name| {
                let ec = resolve_decl(
                    &shigure.eval_conditions,
                    ec_name,
                    "eval_condition",
                    &decl.name,
                )?;
                lower_eval_condition(ec, &change_spec.coeff_domain, &param_names)
            })
            .transpose()?;
        collect_eval_origins(r_ec.as_ref(), &mut origins);
        rules.push(OneStepRule {
            name: r.name.clone(),
            from_vertex: r.from_vertex.clone(),
            to_vertex: r.to_vertex.clone(),
            param_guards,
            param_updates,
            morphism,
            eval_condition: r_ec,
            provenance: Some(path_ref.clone()),
        });
    }

    let query_mode = match &decl.query_mode {
        ShigurePathQueryMode::Find => PathQueryMode::Find,
        ShigurePathQueryMode::Concatenate { first, second } => PathQueryMode::Concatenate {
            first: first.clone(),
            second: second.clone(),
        },
        ShigurePathQueryMode::Subdivide { target_edge } => {
            let s_ep = start
                .as_ref()
                .ok_or_else(|| conv_err("`mode subdivide` requires `start` and `end` endpoints"))?;
            let e_ep = end
                .as_ref()
                .ok_or_else(|| conv_err("`mode subdivide` requires `start` and `end` endpoints"))?;
            let start_p =
                vertices
                    .get(&s_ep.vertex)
                    .ok_or_else(|| ValidationError::UnknownRef {
                        kind: "path vertex",
                        name: s_ep.vertex.clone(),
                        context: format!("{}.subdivide", decl.name),
                    })?;
            let end_p = vertices
                .get(&e_ep.vertex)
                .ok_or_else(|| ValidationError::UnknownRef {
                    kind: "path vertex",
                    name: e_ep.vertex.clone(),
                    context: format!("{}.subdivide", decl.name),
                })?;
            let (m_src, m_tgt) = match direction {
                MorphismDirection::StateMap => (start_p, end_p),
                MorphismDirection::TimeOrder => (end_p, start_p),
            };
            let target_morph = lower_morphism_body(
                target_edge,
                &shigure.comparisons,
                m_src,
                m_tgt,
                &param_names,
                None,
                &path_ref,
                &format!("{}.subdivide", decl.name),
            )?;
            PathQueryMode::Subdivide {
                target_edge: target_morph,
            }
        }
    };

    let protocol = decl
        .protocol
        .as_ref()
        .map(|raw_proto| {
            let cmp = resolve_decl(
                &shigure.comparisons,
                &raw_proto.comparison,
                "shigure comparison",
                &decl.name,
            )?;
            let before_decl = resolve_decl(
                &shigure.presentations,
                &cmp.before,
                "presentation",
                &cmp.name,
            )?;
            let after_decl = resolve_decl(
                &shigure.presentations,
                &cmp.after,
                "presentation",
                &cmp.name,
            )?;
            let before = lower_presentation(
                before_decl,
                archmap,
                snapshot_id,
                &empty_params,
                Some(&param_names),
            )?;
            let after = lower_presentation(after_decl, archmap, snapshot_id, &param_names, None)?;
            for o in before
                .provenance
                .origins
                .iter()
                .chain(&after.provenance.origins)
            {
                origins.insert(o.clone());
            }
            let comparison = lower_comparison_pair(cmp, before, after, &param_names)?;
            let lower_proto_laws = |laws: &[ShigureStateLawDecl],
                                    phase: &str,
                                    label: &str|
             -> Result<Vec<StateLaw>, ValidationError> {
                let ph =
                    comparison
                        .after
                        .phase(phase)
                        .ok_or_else(|| ValidationError::UnknownRef {
                            kind: "after phase",
                            name: phase.to_owned(),
                            context: format!("{}.protocol.{label}", decl.name),
                        })?;
                let coords: BTreeSet<String> = ph.coords.iter().map(|c| c.name.clone()).collect();
                let mut out = Vec::with_capacity(laws.len());
                for l in laws {
                    let ctx = format!("{}.protocol.{label}.{}", decl.name, l.name);
                    let polynomial = lower_poly_expr(
                        &l.expr,
                        &change_spec.coeff_domain,
                        &coords,
                        &empty_params,
                        &param_names,
                        None,
                        &ctx,
                    )?;
                    out.push(StateLaw {
                        name: l.name.clone(),
                        kind: lower_law_kind(l.kind),
                        polynomial,
                        provenance: Some(path_ref.clone()),
                    });
                }
                Ok(out)
            };
            let start_laws =
                lower_proto_laws(&raw_proto.start_laws, &raw_proto.start_phase, "start_law")?;
            let end_laws = lower_proto_laws(&raw_proto.end_laws, &raw_proto.end_phase, "end_law")?;
            Ok::<_, ValidationError>(ProtocolExecutionSpec {
                comparison,
                start_phase: raw_proto.start_phase.clone(),
                start_laws,
                end_phase: raw_proto.end_phase.clone(),
                end_laws,
                allowed_ops: raw_proto.allowed_ops.clone(),
            })
        })
        .transpose()?;

    CheckedPathTask::validate(PathSpec {
        name: decl.name.clone(),
        kind,
        direction,
        query_mode,
        length: decl.length,
        vertices,
        rules,
        start,
        end,
        protocol,
        change_spec,
        eval_condition,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: vec![],
        },
    })
}
