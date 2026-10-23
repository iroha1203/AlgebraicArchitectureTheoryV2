//! 既存の有限D・indicator・全対象表示を、共通の元Law添字へ結ぶ。
use super::super::{equation_presentation_node::Part as E, law_evaluation as frames};
use super::*;
fn matching(
    g: &Graph,
    template: &super::super::polynomial_law_diagram::Original,
    original: &finite_law_diagram::Original,
    object: usize,
) -> Result<(), ValidationFailure> {
    if template.instance != original.instance
        || template.bindings.len() + template.parameters.len() != original.bindings.len()
    {
        return Err("有限配置の元添字/全parameter束縛数が違う".into());
    }
    let base = frames::origin(g, template.reference)?.ok_or("有限配置の共通Law由来がない")?;
    let target = frames::origin(g, original.row)?.ok_or("有限配置の具体Law由来がない")?;
    if base.declaration != target.declaration
        || !Arc::ptr_eq(&base.architecture, &target.architecture)
        || target.object != object
    {
        return Err("有限配置の宣言/入力/対象が違う".into());
    }
    for binding in &template.bindings {
        g.tick()?;
        let mut found = original.bindings.iter().filter(|b| b.name == binding.name);
        let actual = found.next().ok_or("有限配置の元参照束縛がない")?;
        if found.next().is_some()
            || actual.ty != binding.ty
            || g.scalar(actual.value)? != g.scalar(binding.value)?
        {
            return Err("有限配置の元参照束縛/型/値が違う".into());
        }
    }
    for (name, ty) in &template.parameters {
        g.tick()?;
        let mut found = original.bindings.iter().filter(|b| &b.name == name);
        let actual = found.next().ok_or("有限配置の値parameter束縛がない")?;
        if found.next().is_some() || &actual.ty != ty || &g.scalar(actual.value)?.ty() != ty {
            return Err("有限配置の値parameter束縛/型が違う".into());
        }
    }
    Ok(())
}
pub(super) fn compute(
    env: &Environment<'_>,
    g: &Graph,
    table: &Table,
    plan: &finite_law_diagram::FamilyPlan,
    c: &mut Control,
) -> Result<Data, ValidationFailure> {
    tick(c)?;
    table.recheck(env, g, c)?;
    plan.recheck(env, g, table.architecture, c)?;
    let ds = plan.diagrams()?;
    let templates = table.diagrams()?;
    let canonical = templates.first().ok_or("有限配置の元Law計画がない")?;
    let base = ds.first().ok_or("有限配置のbase表示がない")?;
    if ds.len() != table.objects.len() {
        return Err("有限配置の全対象数が違う".into());
    }
    let (universe, anchor) = universe(g, table.architecture)?;
    let mut support = table.support.clone();
    let mut scope = table.scope.clone();
    let mut reasons = table.reasons.clone();
    check_refs(
        env,
        g,
        [universe],
        &mut support,
        &mut scope,
        &mut reasons,
        c,
    )?;
    let mut factors = vec![];
    if ds.iter().any(|d| !d.nu.is_empty()) {
        factors.push(base.ring);
    }
    let mut objects = vec![];
    let mut complete = true;
    for (object, (d, row)) in ds.iter().zip(&table.objects).enumerate() {
        tick(c)?;
        if d.ring != base.ring
            || d.domain != base.domain
            || d.target != base.target
            || d.points != base.points
            || d.nu.len() != d.columns.len()
            || d.nu.len() != d.components.len()
            || d.nu.len() != d.witnesses.len()
        {
            return Err("有限配置の共有D/環/全成分のcoverageが違う".into());
        }
        let reference = d
            .presentation
            .ok_or("有限配置の元EquationPresentationがない")?;
        check_refs(
            env,
            g,
            [reference],
            &mut support,
            &mut scope,
            &mut reasons,
            c,
        )?;
        let Some(Payload::Construction(v)) = &g.get(reference)?.payload else {
            return Err("有限配置の元表示がnativeでない".into());
        };
        let D::FiniteLaw(data) = &v.data else {
            return Err("有限配置の元表示が有限表示でない".into());
        };
        let Some(E::Presentation {
            domain,
            ring,
            coordinates,
            witnesses,
            evaluation: _,
            context,
            ..
        }) = data.equation_part()
        else {
            return Err("有限配置の元表示が別構成".into());
        };
        if *domain != d.domain
            || *ring != d.ring
            || coordinates.len() != d.nu.len()
            || witnesses != &d.witnesses
            || Some(*context) != d.context
        {
            return Err("有限配置の元表示/全座標/証拠が違う".into());
        }
        // 元Presentationのoptional εはoperandの実読取りだけを公開する。
        // 有限νの実代入は既存の恒値関数であり、非適用/guard=falseでも生bodyを読まず得られる。
        complete &= d.evaluation.is_some() && d.epsilon.iter().all(Option::is_some);
        let mut refs = vec![d.domain, d.ring, d.target, d.required, reference, *context];
        refs.extend(d.evaluation);
        let mut judgments = vec![vec![]; table.indices.len()];
        for original in &d.originals {
            tick(c)?;
            let template = canonical
                .originals
                .iter()
                .find(|o| o.row.is_none() && o.instance == original.instance)
                .ok_or("有限配置の共通Law添字がない")?;
            matching(g, template, original, object)?;
            let at = table
                .indices
                .iter()
                .position(|r| *r == template.reference)
                .ok_or("有限配置の元Lawが共通表にない")?;
            let mut readings = d
                .readings
                .iter()
                .filter(|r| r.instance == original.row && r.column == original.column);
            let reading = readings.next().ok_or("有限配置の元Law実読取りがない")?;
            if readings.next().is_some() {
                return Err("有限配置の元Law読取りが重複".into());
            }
            complete &= !reading.reading.condition_failed && !reading.reading.condition_pending;
            judgments[at].push(reading.reading.holds);
            refs.extend([original.row, original.body]);
            refs.extend(original.guard);
            refs.extend(original.bindings.iter().map(|b| b.value));
            refs.extend(reading.body);
            refs.extend(reading.holds);
        }
        for (index, values) in judgments.iter().enumerate() {
            tick(c)?;
            let actual = if values.contains(&Some(false)) {
                Decision::Refuted
            } else if values.iter().all(|v| *v == Some(true)) {
                Decision::Established
            } else {
                Decision::Undetermined
            };
            if g.get(row.holds[index])?
                .judgment
                .as_ref()
                .map(|j| &j.status)
                != Some(&actual)
            {
                return Err("有限配置の全列の原式判断が実EvaluatorのLaw表と違う".into());
            }
        }
        let mut output = vec![];
        for (i, q) in coordinates.iter().enumerate() {
            tick(c)?;
            let column = *d.columns.get(i).ok_or("有限配置のcolumnがない")?;
            let (instance, component) = d.components.get(i).ok_or("有限配置の元成分がない")?;
            let original = d
                .originals
                .iter()
                .find(|o| o.column == column && o.instance == *instance && o.row == q.instance)
                .ok_or("有限配置の元Law/columnが違う")?;
            let expected = match component {
                Some(component) => component.as_slice(),
                None => &[],
            };
            if q.component != expected || Some(&q.nu) != d.nu.get(i) {
                return Err("有限配置の元成分/νが違う".into());
            }
            let template = canonical
                .originals
                .iter()
                .find(|o| o.row.is_none() && o.instance == original.instance)
                .ok_or("有限配置の元添字がない")?;
            let factor = factors
                .iter()
                .position(|r| *r == d.ring)
                .ok_or("有限配置の共有環がfactorにない")?;
            let witness = *witnesses.get(i).ok_or("有限配置の成分証拠がない")?;
            refs.extend([q.instance, q.lhs, q.rhs, q.nu, witness]);
            refs.extend(q.epsilon);
            let epsilon = *d.epsilon.get(i).ok_or("有限配置の実代入欄がない")?;
            if q.epsilon.is_some() && q.epsilon != epsilon {
                return Err("有限配置のoperand実読取りとindicator代入が違う".into());
            }
            refs.extend(epsilon);
            output.push(Coordinate {
                index: template.reference,
                factor: Some(factor),
                source: Source::Finite(FiniteCoordinate {
                    object,
                    original: original.clone(),
                    value: q.clone(),
                    witness,
                    epsilon,
                }),
            });
        }
        refs.sort_by_key(|r| r.0);
        refs.dedup();
        check_refs(env, g, refs, &mut support, &mut scope, &mut reasons, c)?;
        objects.push(Object {
            object: row.object,
            architecture: row.architecture,
            context: d.context,
            presentations: vec![Some(reference)],
            coordinates: output,
            unavailable: None,
            status: if d.evaluation.is_some() && d.epsilon.iter().all(Option::is_some) {
                EquationPresentationStatus::Ready
            } else {
                EquationPresentationStatus::Undetermined
            },
        });
    }
    support.sort();
    support.dedup();
    reasons.sort_by_key(|r| r.wire().canonical());
    reasons.dedup();
    tick(c)?;
    Ok(Data {
        architecture: table.architecture,
        universe,
        anchor,
        indices: table.indices.clone(),
        factors,
        objects,
        support,
        scope,
        reasons,
        complete,
    })
}
