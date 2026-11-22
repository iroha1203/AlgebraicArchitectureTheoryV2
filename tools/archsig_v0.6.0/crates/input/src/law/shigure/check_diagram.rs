//! `shigure diagram` 宣言の静的検査。

use super::ast_ext::*;
use super::check::{CResult, DeclCategory, check_presentation_vars, resolve_shigure_ref};
use super::check_ext_common::{
    ScopedMorphismMeta, check_eval_cond_against_domain_params, check_morphism_body,
    check_scoped_change_spec_targets,
};
use super::*;
use crate::law::ast::Span;
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use std::collections::{BTreeMap, HashMap, HashSet};

#[allow(clippy::too_many_arguments)]
pub(super) fn check_diagram<E: InputError>(
    raw: &RawDiagramTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    decls: &CheckedShigureDecls,
    reading_edges: &mut Vec<(usize, usize, Span)>,
    control: &Control,
) -> CResult<ShigureDiagramTask, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let change_spec_name = resolve_shigure_ref(
        &raw.change_spec,
        DeclCategory::ChangeSpec,
        r_idx,
        reading_name,
        checker,
        index,
        reading_edges,
    )?;
    let spec = &decls.change_specs[&change_spec_name];
    let param_set: HashSet<&str> = spec.parameters.iter().map(|p| p.name.as_str()).collect();

    let eval_condition = match &raw.eval_condition {
        Some(q) => {
            let ec_name = resolve_shigure_ref(
                q,
                DeclCategory::EvalCondition,
                r_idx,
                reading_name,
                checker,
                index,
                reading_edges,
            )?;
            let ec = &decls.eval_conditions[&ec_name];
            check_eval_cond_against_domain_params(
                ec,
                &spec.coeff_domain,
                &param_set,
                raw.span,
                control,
            )?;
            Some(ec_name)
        }
        None => None,
    };

    let mut vertices_by_name: HashMap<String, (&ShigurePresentation, bool)> = HashMap::new();
    let mut vertices_by_pres: BTreeMap<&str, Vec<(&ShigurePresentation, bool)>> = BTreeMap::new();
    let mut vertices = Vec::with_capacity(raw.vertices.len());
    for v in &raw.vertices {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if vertices_by_name.contains_key(&v.name.name) {
            return duplicate(
                v.name.span,
                format!("duplicate diagram vertex `{}`", v.name.name),
            );
        }
        let pres_name = resolve_shigure_ref(
            &v.presentation,
            DeclCategory::Presentation,
            r_idx,
            reading_name,
            checker,
            index,
            reading_edges,
        )?;
        let pres = &decls.presentations[&pres_name];
        if pres.coeff_domain != spec.coeff_domain {
            return Err(Box::new(Issue::law(
                Code::Type,
                v.span,
                format!(
                    "diagram vertex `{}` presentation coefficient domain does not match `change_spec`",
                    v.name.name
                ),
            ))
            .into());
        }
        let allowed = if v.is_fixed { None } else { Some(&param_set) };
        check_presentation_vars(pres, allowed, control)?;
        vertices_by_name.insert(v.name.name.clone(), (pres, v.is_fixed));
        vertices_by_pres
            .entry(pres.name.as_str())
            .or_default()
            .push((pres, v.is_fixed));
        vertices.push(ShigureDiagramVertex {
            name: v.name.name.clone(),
            presentation: pres_name,
            is_fixed: v.is_fixed,
            span: v.span,
        });
    }

    let mut edges_by_name: HashMap<String, (String, String)> = HashMap::new();
    let mut checked_bodies: Vec<(ShigureDiagramEdge, usize)> = Vec::with_capacity(raw.edges.len());
    let mut edge_bodies: Vec<(ShigureMorphismBody, &ShigurePresentation, bool)> =
        Vec::with_capacity(raw.edges.len());

    for e in &raw.edges {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if edges_by_name.contains_key(&e.name.name) {
            return duplicate(
                e.name.span,
                format!("duplicate diagram edge `{}`", e.name.name),
            );
        }
        let Some(&(src_p, src_fixed)) = vertices_by_name.get(&e.source.name) else {
            return reference(
                e.source.span,
                format!(
                    "unknown diagram vertex `{}` in edge `{}`",
                    e.source.name, e.name.name
                ),
            );
        };
        let Some(&(tgt_p, tgt_fixed)) = vertices_by_name.get(&e.target.name) else {
            return reference(
                e.target.span,
                format!(
                    "unknown diagram vertex `{}` in edge `{}`",
                    e.target.name, e.name.name
                ),
            );
        };
        if e.is_fixed && (!src_fixed || !tgt_fixed) {
            return Err(Box::new(Issue::law(
                Code::Type,
                e.span,
                format!(
                    "fixed diagram edge `{}` must connect two fixed vertices",
                    e.name.name
                ),
            ))
            .into());
        }
        let (morph_src_p, morph_tgt_p) = match raw.direction {
            ShigureDirection::StateMap => (src_p, tgt_p),
            ShigureDirection::TimeOrder => (tgt_p, src_p),
        };
        let allowed = if e.is_fixed { None } else { Some(&param_set) };
        let body = check_morphism_body(
            &e.morphism,
            r_idx,
            reading_name,
            checker,
            index,
            decls,
            reading_edges,
            morph_src_p,
            morph_tgt_p,
            allowed,
            e.span,
            &format!("diagram edge `{}`", e.name.name),
            control,
        )?;
        edges_by_name.insert(
            e.name.name.clone(),
            (e.source.name.clone(), e.target.name.clone()),
        );
        let meta_idx = edge_bodies.len();
        edge_bodies.push((body.clone(), morph_src_p, e.is_fixed));
        checked_bodies.push((
            ShigureDiagramEdge {
                name: e.name.name.clone(),
                source: e.source.name.clone(),
                target: e.target.name.clone(),
                is_fixed: e.is_fixed,
                morphism: body,
                span: e.span,
            },
            meta_idx,
        ));
    }
    let morphs: Vec<ScopedMorphismMeta<'_>> = edge_bodies
        .iter()
        .map(|(body, src_p, is_fixed)| ScopedMorphismMeta::from_body(body, src_p, decls, *is_fixed))
        .collect();
    let edges: Vec<ShigureDiagramEdge> = checked_bodies.into_iter().map(|(edge, _)| edge).collect();

    check_scoped_change_spec_targets(spec, &vertices_by_pres, &morphs, "diagram", control)?;

    let mut seen_rels = HashSet::new();
    let mut relations = Vec::with_capacity(raw.relations.len());
    for rel in &raw.relations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !seen_rels.insert(rel.name.name.clone()) {
            return duplicate(
                rel.name.span,
                format!("duplicate diagram relation `{}`", rel.name.name),
            );
        }
        let check_chain = |chain: &[Ident],
                           side: &str|
         -> CResult<(String, String, Vec<String>), E> {
            if chain.is_empty() {
                return Err(Box::new(Issue::law(
                    Code::Type,
                    rel.span,
                    format!(
                        "diagram relation `{}` {side} edge chain must be non-empty",
                        rel.name.name
                    ),
                ))
                .into());
            }
            let mut names = Vec::with_capacity(chain.len());
            let Some((start, mut cur_end)) = edges_by_name.get(&chain[0].name).cloned() else {
                return reference(
                    chain[0].span,
                    format!(
                        "unknown diagram edge `{}` in relation `{}`",
                        chain[0].name, rel.name.name
                    ),
                );
            };
            names.push(chain[0].name.clone());
            for id in &chain[1..] {
                E::checkpoint(control, Checkpoint::LawSemantics)?;
                let Some((src, tgt)) = edges_by_name.get(&id.name) else {
                    return reference(
                        id.span,
                        format!(
                            "unknown diagram edge `{}` in relation `{}`",
                            id.name, rel.name.name
                        ),
                    );
                };
                if *src != cur_end {
                    return Err(Box::new(Issue::law(
                            Code::Type,
                            id.span,
                            format!(
                                "diagram relation `{}` {side} chain is not composable at `{}`: expected source `{cur_end}`, got `{src}`",
                                rel.name.name, id.name
                            ),
                        ))
                        .into());
                }
                cur_end = tgt.clone();
                names.push(id.name.clone());
            }
            Ok((start, cur_end, names))
        };
        let (l_start, l_end, lhs) = check_chain(&rel.lhs, "lhs")?;
        let (r_start, r_end, rhs) = check_chain(&rel.rhs, "rhs")?;
        if l_start != r_start || l_end != r_end {
            return Err(Box::new(Issue::law(
                Code::Type,
                rel.span,
                format!(
                    "diagram relation `{}` endpoints mismatch: lhs `{l_start} -> {l_end}` vs rhs `{r_start} -> {r_end}`",
                    rel.name.name
                ),
            ))
            .into());
        }
        relations.push(ShigureDiagramRelation {
            name: rel.name.name.clone(),
            lhs,
            rhs,
            span: rel.span,
        });
    }

    let mut edge_eval_conditions = BTreeMap::new();
    for item in &raw.edge_eval_conditions {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !edges_by_name.contains_key(&item.edge.name) {
            return reference(
                item.edge.span,
                format!(
                    "unknown diagram edge `{}` in edge_eval_condition",
                    item.edge.name
                ),
            );
        }
        if edge_eval_conditions.contains_key(&item.edge.name) {
            return duplicate(
                item.edge.span,
                format!(
                    "duplicate edge_eval_condition for edge `{}`",
                    item.edge.name
                ),
            );
        }
        let ec_name = resolve_shigure_ref(
            &item.eval_condition,
            DeclCategory::EvalCondition,
            r_idx,
            reading_name,
            checker,
            index,
            reading_edges,
        )?;
        let ec = &decls.eval_conditions[&ec_name];
        check_eval_cond_against_domain_params(
            ec,
            &spec.coeff_domain,
            &param_set,
            item.span,
            control,
        )?;
        edge_eval_conditions.insert(item.edge.name.clone(), ec_name);
    }

    Ok(ShigureDiagramTask {
        name: full_name,
        reading: reading_name.to_owned(),
        direction: raw.direction,
        vertices,
        edges,
        relations,
        change_spec: change_spec_name,
        eval_condition,
        edge_eval_conditions,
        span: raw.span,
    })
}
