//! 元Lawの共通添字を、全標準対象の実評価・命題列へ接続する。
use super::{
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
    },
    control::{Checkpoint, Control},
    environment::{Environment, numeric_parameters},
    input::CheckedInputs,
    law_evaluation as frames,
    polynomial_law_diagram::{Diagram, FamilyPlan, Original},
    result::*,
};
use crate::types::Type;
use std::sync::Arc;
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ObjectRow {
    pub object: NodeRef,
    pub architecture: NodeRef,
    pub origins: Vec<NodeRef>,
    pub evaluations: Vec<NodeRef>,
    pub holds: Vec<NodeRef>,
}
#[derive(Clone, Debug)]
pub(super) struct Table {
    pub architecture: NodeRef,
    pub indices: Vec<NodeRef>,
    pub objects: Vec<ObjectRow>,
    pub support: Vec<Fact>,
    pub scope: Scope,
    pub reasons: Vec<Reason>,
    component_source: NodeRef,
    plan: FamilyPlan,
}
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}
fn refs(
    env: &Environment<'_>,
    g: &Graph,
    rs: impl IntoIterator<Item = NodeRef>,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    for r in rs {
        tick(c)?;
        let n = g.get(r)?;
        env.recheck_node(g, n, r.0)?;
    }
    Ok(())
}
fn templates(d: &Diagram) -> Vec<&Original> {
    d.originals.iter().filter(|o| o.row.is_none()).collect()
}
// 共通添字は記号的な元Lawに固定し、閉じたLawの実評価は唯一の具体行へ結ぶ。
fn evaluated_origin<'a>(
    g: &Graph,
    diagram: &'a Diagram,
    template: &'a Original,
) -> Result<&'a Original, ValidationFailure> {
    if !template.parameters.is_empty() {
        return Ok(template);
    }
    let mut rows = diagram
        .originals
        .iter()
        .filter(|o| o.instance == template.instance && o.row.is_some());
    let Some(row) = rows.next() else {
        return Ok(template);
    };
    if row.row != Some(0) || rows.next().is_some() {
        return Err("全Law表の閉じたLawに唯一の具体行がない".into());
    }
    matching(g, template, row)?;
    Ok(row)
}
fn components(
    g: &Graph,
    source: NodeRef,
    architecture: NodeRef,
) -> Result<
    (
        Arc<ArchitectureWitness>,
        super::object_component_diagram::Diagram,
    ),
    ValidationFailure,
> {
    let Some(Payload::Construction(v)) = &g.get(source)?.payload else {
        return Err("全Law表の対象計画がnativeでない".into());
    };
    let D::ObjectComponents(data) = &v.data else {
        return Err("全Law表の対象計画が別構成".into());
    };
    data.position(source.0)?;
    let (a, r, outputs) = data.retained_components();
    if r != architecture || outputs.base != source {
        return Err("全Law表の対象計画が別Architecture/base".into());
    }
    let actual = native::architecture_origin(g, architecture, 0)?;
    if !Arc::ptr_eq(actual, &a) {
        return Err("全Law表の対象族が別由来".into());
    }
    Ok((a, outputs))
}
fn matching(g: &Graph, base: &Original, target: &Original) -> Result<(), ValidationFailure> {
    if base.instance != target.instance
        || base.parameters != target.parameters
        || base.bindings.len() != target.bindings.len()
    {
        return Err("全Law表の元添字/parameter/固定束縛数が違う".into());
    }
    let a = frames::origin(g, base.reference)?.ok_or("全Law表の元Lawがない")?;
    let b = frames::origin(g, target.reference)?.ok_or("全Law表の対象Lawがない")?;
    if a.declaration != b.declaration || !Arc::ptr_eq(&a.architecture, &b.architecture) {
        return Err("全Law表の対象Lawが別宣言/入力".into());
    }
    for (a, b) in base.bindings.iter().zip(&target.bindings) {
        g.tick()?;
        if a.name != b.name || a.ty != b.ty || g.scalar(a.value)? != g.scalar(b.value)? {
            return Err("全Law表の元参照束縛/順序/型/値が違う".into());
        }
    }
    Ok(())
}
fn cell(
    env: &Environment<'_>,
    g: &Graph,
    origin: NodeRef,
    architecture: NodeRef,
    evaluation: NodeRef,
    holds: NodeRef,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    refs(env, g, [origin, architecture, evaluation, holds], c)?;
    g.expect(origin, &NodeType::LawInstance)?;
    g.expect(evaluation, &NodeType::Evaluation(Type::Bool))?;
    g.expect(holds, &NodeType::Proposition)?;
    let e = g.get(evaluation)?;
    let p = g.get(holds)?;
    match &p.payload {
        Some(Payload::Construction(v)) => match &v.data {
            D::LawFamily(d)
                if d.template == origin
                    && d.architecture == architecture
                    && matches!(d.kind,super::law_family::Kind::Proposition{evaluation:r,..} if r==evaluation) =>
            {
                let Some(Payload::Construction(v)) = &e.payload else {
                    return Err("全Law表の族命題に族評価がない".into());
                };
                if !matches!(&v.data,D::LawFamily(x) if x.template==origin && x.architecture==architecture && matches!(x.kind,super::law_family::Kind::Evaluation{..}))
                {
                    return Err("全Law表の族評価が別Law/対象".into());
                }
            }
            D::OutsideLaw(d)
                if d.origin == origin
                    && d.architecture == architecture
                    && matches!(d.kind,super::law_inapplicable::Kind::Proposition{evaluation:r} if r==evaluation) =>
            {
                let Some(Payload::Construction(v)) = &e.payload else {
                    return Err("全Law表の非適用命題に実評価がない".into());
                };
                if !matches!(&v.data,D::OutsideLaw(x) if x.origin==origin && x.architecture==architecture && matches!(x.kind,super::law_inapplicable::Kind::Evaluation{..}))
                {
                    return Err("全Law表の非適用評価が別Law/対象".into());
                }
            }
            _ => return Err("全Law表の命題が別のLaw/評価/対象".into()),
        },
        Some(Payload::Proposition { instance }) => {
            let context = g.context_at(holds.0);
            let index = context.instance.ok_or("全Law表の命題に実instanceがない")?;
            let record = g.instances.get(index).ok_or("全Law表の実instanceがない")?;
            if record.source != origin
                || record.caller != g.context_at(architecture.0)
                || g.context_at(evaluation.0) != context
                || p.arguments != [*instance, evaluation]
                || frames::architecture(g, index, g.nodes.len())? != Some(architecture)
            {
                return Err("全Law表の実行producer/元Law/対象が違う".into());
            }
            if !matches!(&e.payload,Some(Payload::Evaluation{environment:Some(a),..}) if *a==architecture)
            {
                return Err("全Law表の実評価環境が違う".into());
            }
        }
        _ => return Err("全Law表の実命題がない".into()),
    }
    if p.judgment.is_none() {
        return Err("全Law表の命題判断がない".into());
    }
    Ok(())
}
impl Table {
    pub(super) fn component_source(&self) -> NodeRef { self.component_source }
    pub(super) fn diagrams(&self) -> Result<Vec<Diagram>, ValidationFailure> {
        self.plan.diagrams()
    }
    pub(super) fn recheck(
        &self,
        env: &Environment<'_>,
        g: &Graph,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        tick(c)?;
        refs(env, g, [self.architecture, self.component_source], c)?;
        let (a, objects) = components(g, self.component_source, self.architecture)?;
        let planned = self.plan.recheck(env, g, self.architecture, c)?;
        if !Arc::ptr_eq(&a, &planned) {
            return Err("全Law表のLaw計画と対象計画が別由来".into());
        }
        let ds = self.plan.diagrams()?;
        if ds.len() != objects.objects.len()
            || self.objects.len() != ds.len()
            || objects.architectures.len() != ds.len()
        {
            return Err("全Law表の全対象coverageが違う".into());
        }
        let base = templates(ds.first().ok_or("全Law表にbase対象がない")?);
        if self.indices != base.iter().map(|t| t.reference).collect::<Vec<_>>() {
            return Err("全Law表の元全添字/順序が違う".into());
        }
        refs(env, g, self.indices.iter().copied(), c)?;
        let mut support = g.get(self.architecture)?.support.clone();
        let mut scope = g.get(self.architecture)?.scope.clone();
        let mut reasons = vec![];
        for (object, (actual, diagram)) in self.objects.iter().zip(&ds).enumerate() {
            tick(c)?;
            if actual.object != objects.objects[object]
                || actual.architecture != objects.architectures[object]
            {
                return Err("全Law表の対象identity/順序/Architectureが違う".into());
            }
            g.expect(actual.object, &NodeType::Construction(T::ObjectComponent))?;
            refs(env, g, [actual.object, actual.architecture], c)?;
            for r in [actual.object, actual.architecture] {
                support.extend(g.get(r)?.support.iter().cloned());
                scope.merge(&g.get(r)?.scope);
            }
            let ts = templates(diagram);
            if ts.len() != base.len()
                || actual.origins.len() != base.len()
                || actual.evaluations.len() != base.len()
                || actual.holds.len() != base.len()
            {
                return Err("全Law表のLaw行coverage/順序が違う".into());
            }
            for (i, (original, target)) in base.iter().zip(ts).enumerate() {
                tick(c)?;
                matching(g, original, target)?;
                let target = evaluated_origin(g, diagram, target)?;
                if actual.origins[i] != target.reference {
                    return Err("全Law表の具体行/元Lawの対応が違う".into());
                }
                let o = frames::origin(g, target.reference)?.ok_or("全Law表の元対象Lawがない")?;
                if o.object != object || !Arc::ptr_eq(&o.architecture, &a) {
                    return Err("全Law表の対象Lawが別の対象".into());
                }
                cell(
                    env,
                    g,
                    target.reference,
                    actual.architecture,
                    actual.evaluations[i],
                    actual.holds[i],
                    c,
                )?;
                for r in [target.reference, actual.evaluations[i], actual.holds[i]] {
                    support.extend(g.get(r)?.support.iter().cloned());
                    scope.merge(&g.get(r)?.scope);
                }
                reasons.extend(g.get(actual.holds[i])?.reasons.iter().cloned());
            }
        }
        support.sort();
        support.dedup();
        reasons.sort_by_key(|r| r.wire().canonical());
        reasons.dedup();
        if self.support != support || self.scope != scope || self.reasons != reasons {
            return Err("全Law表の支持/Scope/理由が実表と違う".into());
        }
        tick(c)
    }
}
pub(super) fn retain(
    env: &Environment<'_>,
    g: &mut Graph,
    inputs: Arc<CheckedInputs>,
    architecture: NodeRef,
    c: &mut Control,
) -> Result<Option<Table>, ValidationFailure> {
    tick(c)?;
    if g.active != g.context_at(architecture.0) {
        return Err("全Law表の生成が元ArchitectureのRequestでない".into());
    }
    refs(env, g, [architecture], c)?;
    let Some(objects) =
        super::object_component_diagram::retain(g, inputs.clone(), architecture, c)?
    else {
        return Ok(None);
    };
    let plan = super::polynomial_law_diagram::retain_table_plan(g, inputs, architecture, c)?;
    let ds = plan.diagrams()?;
    let base = templates(ds.first().ok_or("全Law表のbase計画がない")?);
    let indices = base.iter().map(|t| t.reference).collect::<Vec<_>>();
    if ds.len() != objects.objects.len() || ds.len() != objects.architectures.len() {
        return Err("全Law表の元対象計画数が違う".into());
    }
    let mut rows = vec![];
    let mut support = g.get(architecture)?.support.clone();
    let mut scope = g.get(architecture)?.scope.clone();
    let mut reasons = vec![];
    for (object, d) in ds.iter().enumerate() {
        tick(c)?;
        let ts = templates(d);
        if ts.len() != base.len() {
            return Err("全Law表の元Law添字が対象間で違う".into());
        }
        let mut row = ObjectRow {
            object: objects.objects[object],
            architecture: objects.architectures[object],
            origins: vec![],
            evaluations: vec![],
            holds: vec![],
        };
        for r in [row.object, row.architecture] {
            support.extend(g.get(r)?.support.iter().cloned());
            scope.merge(&g.get(r)?.scope);
        }
        for (original, t) in base.iter().zip(ts) {
            tick(c)?;
            matching(g, original, t)?;
            let t = evaluated_origin(g, d, t)?;
            let answer = if !t.parameters.is_empty() {
                let answer = super::law_family::check(env, g, t.reference, row.architecture, c)?;
                if answer.is_none() && t.parameters.iter().all(|(_, ty)| numeric_parameters::numeric_width(ty).is_some()) {
                    let origin = frames::origin(g, t.reference)?.ok_or("全Law表の元Lawに由来がない")?;
                    if origin.outside {
                        super::law_inapplicable::check(env, g, t.reference, row.architecture, c)?
                    } else {
                        super::law_proposition::check(env, g, t.reference, row.architecture, c)?.answer
                    }
                } else { answer }
            } else {
                let origin = frames::origin(g, t.reference)?.ok_or("全Law表の元Lawに由来がない")?;
                if origin.outside {
                    super::law_inapplicable::check(env, g, t.reference, row.architecture, c)?
                } else {
                    super::law_proposition::check(env, g, t.reference, row.architecture, c)?.answer
                }
            };
            let Some(answer) = answer else {
                return Ok(None);
            };
            let e = *answer
                .outputs
                .get("evaluation")
                .ok_or("全Law表の実Evaluationがない")?;
            let p = answer.claim.ok_or("全Law表の実holdsがない")?;
            cell(env, g, t.reference, row.architecture, e, p, c)?;
            row.origins.push(t.reference);
            row.evaluations.push(e);
            row.holds.push(p);
            for r in [t.reference, e, p] {
                support.extend(g.get(r)?.support.iter().cloned());
                scope.merge(&g.get(r)?.scope);
            }
            reasons.extend(g.get(p)?.reasons.iter().cloned());
            tick(c)?;
        }
        rows.push(row);
    }
    support.sort();
    support.dedup();
    reasons.sort_by_key(|r| r.wire().canonical());
    reasons.dedup();
    let table = Table {
        architecture,
        indices,
        objects: rows,
        support,
        scope,
        reasons,
        component_source: objects.base,
        plan,
    };
    table.recheck(env, g, c)?;
    tick(c)?;
    Ok(Some(table))
}
#[cfg(test)]
#[path = "law_table_tests.rs"]
mod tests;
