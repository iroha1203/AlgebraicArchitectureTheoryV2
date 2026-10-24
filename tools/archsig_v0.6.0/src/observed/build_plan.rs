//! buildの同じ元Architectureへ、対象・操作・全読取り・方程式を接続する。
use super::{
    architecture_result::{self, Architecture},
    circuit_pattern::{self, Diagram as Patterns},
    construction_result::{ConstructionData as D, ConstructionType as T},
    control::{Checkpoint, Control},
    environment::Environment,
    equation_family,
    input::CheckedInputs,
    internal_arrow_diagram::{self, Diagram as Arrows},
    law_table::{self, Table},
    native_source::Boundary,
    object_component_diagram::{self, Diagram as Objects},
    observable_layout::{self, Layout},
    predicate_invariant::{self, Invariant as Predicate},
    request::Request,
    result::*,
    view_invariant::{self, Diagram as Views},
};
use std::sync::Arc;

fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}

/// Optionは実際に構成できた中間結果だけを表す。構成条件の判断はこの後に行う。
#[derive(Debug)]
pub(super) struct Plan {
    pub architecture: Architecture,
    pub objects: Option<Objects>,
    pub patterns: Option<Patterns>,
    pub arrows: Option<Arrows>,
    pub laws: Option<Arc<Table>>,
    pub polynomial: Option<Arc<Layout>>,
    pub finite: Option<Arc<Layout>>,
    pub equations: Option<NodeRef>,
    pub views: Option<Views>,
    pub predicates: Vec<Predicate>,
    pub boundary: Boundary,
}

fn retained_objects(g: &Graph, table: &Table) -> Result<Objects, ValidationFailure> {
    let r = table.component_source();
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("buildの元Law表に対象族がない".into());
    };
    let D::ObjectComponents(d) = &v.data else {
        return Err("buildの元Law表が別の対象構成を参照した".into());
    };
    d.position(r.0)?;
    let (_, architecture, objects) = d.retained_components();
    if architecture != table.architecture || objects.base != r {
        return Err("buildの元Law表のArchitectureまたは対象族が違う".into());
    }
    Ok(objects)
}

pub(super) fn prepare(
    env: &Environment<'_>,
    g: &mut Graph,
    inputs: Arc<CheckedInputs>,
    request: &Request,
    c: &mut Control,
) -> Result<Plan, ValidationFailure> {
    tick(c)?;
    let architecture = architecture_result::build(inputs.clone(), env, g, request, c)?;
    prepare_architecture(env, g, inputs, architecture, c)
}

pub(super) fn prepare_architecture(
    env: &Environment<'_>,
    g: &mut Graph,
    inputs: Arc<CheckedInputs>,
    architecture: Architecture,
    c: &mut Control,
) -> Result<Plan, ValidationFailure> {
    tick(c)?;
    let reference = architecture.reference;
    let mut objects = None;
    let mut patterns = None;
    let mut arrows = None;
    let mut laws = None;
    let mut polynomial = None;
    let mut finite = None;
    let mut equations = None;
    let mut views = None;
    let mut predicates = vec![];
    if architecture.complete {
        tick(c)?;
        laws = law_table::retain(env, g, inputs.clone(), reference, c)?.map(Arc::new);
        objects = if let Some(table) = &laws {
            Some(retained_objects(g, table)?)
        } else {
            object_component_diagram::retain(g, inputs.clone(), reference, c)?
        };
        if let Some(objects) = &objects {
            patterns =
                circuit_pattern::retain(env, g, inputs.clone(), reference, Some(objects.base), c)?;
            arrows = Some(internal_arrow_diagram::retain(
                g,
                inputs.clone(),
                reference,
                objects,
                architecture.universe,
                c,
            )?);
            views = Some(view_invariant::retain(env, g, objects.base, c)?);
        }
        if let Some(table) = &laws {
            let layout = Arc::new(observable_layout::retain(env, g, table.clone(), c)?);
            if layout.data.complete {
                equations = equation_family::retain(env, g, layout.clone(), c)?;
            }
            polynomial = Some(layout);
            if equations.is_none() {
                finite = observable_layout::retain_finite(env, g, table.clone(), inputs, c)?
                    .map(Arc::new);
                if let Some(layout) = &finite
                    && layout.data.complete
                {
                    equations = equation_family::retain(env, g, layout.clone(), c)?;
                }
            }
            predicates = predicate_invariant::retain(env, g, table.clone(), c)?;
        }
    }
    let mut dependencies = vec![reference, architecture.universe];
    if let Some(objects) = &objects {
        dependencies.extend(objects.objects.iter().copied());
        dependencies.extend(objects.architectures.iter().copied());
        dependencies.extend(objects.readings.iter().map(|r| r.expression));
    }
    if let Some(patterns) = &patterns {
        dependencies.extend(patterns.rows.iter().map(|r| r.pattern));
    }
    if let Some(arrows) = &arrows {
        for row in &arrows.rows {
            dependencies.push(row.subject);
            dependencies.extend(row.candidate);
            dependencies.extend(row.evidence.iter().copied());
            dependencies.extend(row.operation);
        }
    }
    dependencies.extend(equations);
    if let Some(views) = &views {
        for axis in &views.axes {
            dependencies.extend([axis.invariant, axis.signature]);
        }
        for pending in &views.pending {
            dependencies.extend(pending.expressions.iter().copied());
        }
    }
    for predicate in &predicates {
        dependencies.push(predicate.invariant);
        dependencies.extend(predicate.evaluations.iter().copied());
    }
    dependencies.sort_by_key(|r| r.0);
    dependencies.dedup();
    g.expect(reference, &NodeType::Construction(T::Architecture))?;
    let boundary = Boundary::capture(env, g, reference, dependencies, c)?;
    tick(c)?;
    Ok(Plan {
        architecture,
        objects,
        patterns,
        arrows,
        laws,
        polynomial,
        finite,
        equations,
        views,
        predicates,
        boundary,
    })
}

#[cfg(test)]
#[path = "build_plan_tests.rs"]
mod tests;
