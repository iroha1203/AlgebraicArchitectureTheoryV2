//! `CheckedInputs` から `CheckedDiagramTask` への厳密な lowering。

use super::lower::{lower_change_spec, lower_eval_condition, lower_presentation};
use super::lower_expr::{conv_err, law_source_ref};
use super::lower_morphism::{
    collect_eval_origins, ensure_snapshot_exists, lower_direction, lower_morphism_body,
    resolve_decl, select_named_decl,
};
use crate::ir::diagram::{
    CheckedDiagramTask, DiagramEdge, DiagramRelation, DiagramSpec, DiagramVertex,
};
use crate::ir::morphism::MorphismDirection;
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::validate::ValidationError;
use archsig_input::input::CheckedInputs;
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn convert_diagram_task(
    inputs: &CheckedInputs,
    task_name: Option<&str>,
    snapshot_id: Option<&str>,
) -> Result<CheckedDiagramTask, ValidationError> {
    let shigure = inputs.law().shigure();
    if shigure.is_empty() {
        return Err(conv_err(
            "no `shigure` declarations found in CheckedLaw input",
        ));
    }
    let (_, decl) = select_named_decl(&shigure.diagrams, task_name, "shigure diagram")?;
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

    let diagram_ref = law_source_ref(&decl.name);
    let mut origins: BTreeSet<SourceRef> = BTreeSet::from([diagram_ref.clone()]);
    for o in &change_spec.provenance.origins {
        origins.insert(o.clone());
    }

    let mut vertex_map = BTreeMap::new();
    let mut vertices = Vec::with_capacity(decl.vertices.len());
    for v in &decl.vertices {
        let pres_decl = resolve_decl(
            &shigure.presentations,
            &v.presentation,
            "presentation",
            &decl.name,
        )?;
        let pres = if v.is_fixed {
            lower_presentation(
                pres_decl,
                archmap,
                snapshot_id,
                &empty_params,
                Some(&param_names),
            )?
        } else {
            lower_presentation(pres_decl, archmap, snapshot_id, &param_names, None)?
        };
        for o in &pres.provenance.origins {
            origins.insert(o.clone());
        }
        let dv = DiagramVertex {
            name: v.name.clone(),
            presentation: pres,
            is_fixed: v.is_fixed,
            provenance: Some(law_source_ref(&pres_decl.name)),
        };
        vertex_map.insert(v.name.clone(), dv.presentation.clone());
        vertices.push(dv);
    }

    let direction = lower_direction(decl.direction);
    let mut edges = Vec::with_capacity(decl.edges.len());
    for e in &decl.edges {
        let src_p = vertex_map
            .get(&e.source)
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "diagram vertex",
                name: e.source.clone(),
                context: format!("{}.edge.{}", decl.name, e.name),
            })?;
        let tgt_p = vertex_map
            .get(&e.target)
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "diagram vertex",
                name: e.target.clone(),
                context: format!("{}.edge.{}", decl.name, e.name),
            })?;
        let (morph_src, morph_tgt) = match direction {
            MorphismDirection::StateMap => (src_p, tgt_p),
            MorphismDirection::TimeOrder => (tgt_p, src_p),
        };
        let (allowed, forbidden) = if e.is_fixed {
            (&empty_params, Some(&param_names))
        } else {
            (&param_names, None)
        };
        let morphism = lower_morphism_body(
            &e.morphism,
            &shigure.comparisons,
            morph_src,
            morph_tgt,
            allowed,
            forbidden,
            &diagram_ref,
            &format!("{}.edge.{}", decl.name, e.name),
        )?;
        if let Some(p) = &morphism.provenance {
            origins.insert(p.clone());
        }
        edges.push(DiagramEdge {
            name: e.name.clone(),
            source: e.source.clone(),
            target: e.target.clone(),
            morphism,
            is_fixed: e.is_fixed,
            provenance: Some(diagram_ref.clone()),
        });
    }

    let relations = decl
        .relations
        .iter()
        .map(|r| DiagramRelation {
            name: r.name.clone(),
            lhs: r.lhs.clone(),
            rhs: r.rhs.clone(),
            provenance: Some(diagram_ref.clone()),
        })
        .collect();

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

    let mut edge_eval_conditions = BTreeMap::new();
    for (edge_name, ec_name) in &decl.edge_eval_conditions {
        let ec_decl = resolve_decl(
            &shigure.eval_conditions,
            ec_name,
            "eval_condition",
            &decl.name,
        )?;
        let ec = lower_eval_condition(ec_decl, &change_spec.coeff_domain, &param_names)?;
        collect_eval_origins(Some(&ec), &mut origins);
        edge_eval_conditions.insert(edge_name.clone(), ec);
    }

    CheckedDiagramTask::validate(DiagramSpec {
        name: decl.name.clone(),
        direction,
        vertices,
        edges,
        relations,
        change_spec,
        eval_condition,
        edge_eval_conditions,
        provenance: Provenance {
            origins: origins.into_iter().collect(),
            clauses: vec![],
        },
    })
}
