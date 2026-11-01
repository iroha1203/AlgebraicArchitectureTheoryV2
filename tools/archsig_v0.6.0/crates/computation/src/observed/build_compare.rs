//! 同じ完全patternの読取りを、同じnative DAGの実評価・残差から比較する。
use super::{
    build_plan::Plan, construction_result::ConstructionData as D, environment::Environment,
    observable_layout::Reading, result::*, value_equality,
};
use archsig_common::control::{Checkpoint, Control};
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectEvaluation)?;
    Ok(())
}
fn all(values: impl IntoIterator<Item = Option<bool>>) -> Option<bool> {
    let mut known = true;
    for value in values {
        match value {
            Some(false) => return Some(false),
            None => known = false,
            Some(true) => (),
        }
    }
    known.then_some(true)
}
fn evaluation(
    env: &Environment<'_>,
    g: &Graph,
    left: NodeRef,
    right: NodeRef,
    c: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        let l = g.get(left)?;
        let r = g.get(right)?;
        if l.ty != r.ty {
            return Err("build互換性の評価型が違う".into());
        }
        let parts = |n: &Node| -> Result<
            (&'static str, Option<NodeRef>, Vec<NodeRef>),
            ValidationFailure,
        > {
            match &n.payload {
                Some(Payload::Evaluation {
                    applicability,
                    value,
                    parts,
                    ..
                }) => Ok((
                    *applicability,
                    *value,
                    parts
                        .iter()
                        .flat_map(|p| p.children.iter().copied())
                        .collect(),
                )),
                Some(Payload::Construction(v)) => match &v.data {
                    D::OutsideLaw(d) => match d.kind {
                        super::law_inapplicable::Kind::Evaluation { value } => {
                            Ok(("not_applicable", Some(value), vec![]))
                        }
                        _ => Err("build互換性の非適用評価が別種".into()),
                    },
                    D::LawFamily(d) => match &d.kind {
                        super::law_family::Kind::Evaluation { rows, .. } => Ok((
                            "applicable",
                            None,
                            rows.iter().map(|r| r.evaluation).collect(),
                        )),
                        _ => Err("build互換性の全域評価が別種".into()),
                    },
                    _ => Err("build互換性の元Evaluationが別構成".into()),
                },
                _ => Err("build互換性の元Evaluationがない".into()),
            }
        };
        let (la, lv, lc) = parts(l)?;
        let (ra, rv, rc) = parts(r)?;
        if la == "undetermined" || ra == "undetermined" {
            return Ok(None);
        }
        if la != ra {
            return Ok(Some(false));
        }
        if let (Some(lv), Some(rv)) = (lv, rv) {
            return value_equality::equal(
                g.scalar(lv)?,
                g.scalar(rv)?,
                env.indexes.inputs.law(),
                c,
            );
        }
        if !l.reasons.is_empty() || !r.reasons.is_empty() {
            return Ok(None);
        }
        if lc.len() != rc.len() {
            return Err("build互換性の全row数が違う".into());
        }
        // 有限族の全rowを比較する。集約Boolだけで関数を比較しない。
        let mut checked = vec![];
        for (left, right) in lc.into_iter().zip(rc) {
            checked.push(evaluation(env, g, left, right, c)?);
        }
        Ok(all(checked))
    })
}
fn residual(
    env: &Environment<'_>,
    g: &Graph,
    left: NodeRef,
    right: NodeRef,
    c: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    tick(c)?;
    let (Some(Payload::Construction(l)), Some(Payload::Construction(r))) =
        (&g.get(left)?.payload, &g.get(right)?.payload)
    else {
        return Err("build互換性の残差がnative環の値でない".into());
    };
    match (&l.data, &r.data) {
        (D::PolynomialLaw(l), D::PolynomialLaw(r)) => {
            if l.guarded_parameter_family() || r.guarded_parameter_family() {
                return Ok(None);
            }
            match (l.parameter_difference(c)?, r.parameter_difference(c)?) {
                (Some((lr, left)), Some((rr, right))) => {
                    if lr != rr {
                        return Err("build互換性の数値族が別環に属する".into());
                    }
                    return Ok(Some(left == right));
                }
                (Some((ring, _)), None) => {
                    if r.polynomial().map(|p| p.0) != Some(ring) {
                        return Err("build互換性の残差が別環に属する".into());
                    }
                    return Ok(Some(false));
                }
                (None, Some((ring, _))) => {
                    if l.polynomial().map(|p| p.0) != Some(ring) {
                        return Err("build互換性の残差が別環に属する".into());
                    }
                    return Ok(Some(false));
                }
                (None, None) => (),
            }
            let ((lr, ls), (rr, rs)) = (
                l.polynomial().ok_or("左残差が多項式でない")?,
                r.polynomial().ok_or("右残差が多項式でない")?,
            );
            if lr != rr {
                return Err("build互換性の残差が別環に属する".into());
            }
            if ls.len() != rs.len() {
                return Ok(Some(false));
            }
            let mut values = vec![];
            for ((l, lp), (r, rp)) in ls.iter().zip(rs) {
                tick(c)?;
                if lp != rp {
                    return Ok(Some(false));
                }
                values.push(value_equality::equal(
                    g.scalar(*l)?,
                    g.scalar(*r)?,
                    env.indexes.inputs.law(),
                    c,
                )?);
            }
            Ok(all(values))
        }
        (D::FiniteLaw(l), D::FiniteLaw(r)) => {
            let ((lr, ls), (rr, rs)) = (
                l.function_values().ok_or("左残差が有限関数でない")?,
                r.function_values().ok_or("右残差が有限関数でない")?,
            );
            if lr != rr || ls.len() != rs.len() {
                return Err("build互換性の有限残差域が違う".into());
            }
            let mut values = vec![];
            for (&l, &r) in ls.iter().zip(rs) {
                tick(c)?;
                values.push(value_equality::equal(
                    g.scalar(l)?,
                    g.scalar(r)?,
                    env.indexes.inputs.law(),
                    c,
                )?);
            }
            Ok(all(values))
        }
        _ => Err("build互換性の残差表示が違う".into()),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Comparison {
    pub source: NodeRef,
    pub target: NodeRef,
    pub inputs: Vec<NodeRef>,
    pub equal: Option<bool>,
}
pub(super) fn compare(
    env: &Environment<'_>,
    g: &Graph,
    plan: &Plan,
    c: &Control,
) -> Result<Vec<Comparison>, ValidationFailure> {
    plan.boundary.recheck(env, g, plan.boundary.start(), c)?;
    let objects = plan.objects.as_ref().ok_or("build互換性に全対象族がない")?;
    let patterns = plan
        .patterns
        .as_ref()
        .ok_or("build互換性に完全patternがない")?;
    let laws = plan.laws.as_ref().ok_or("build互換性に全Law表がない")?;
    let views = plan.views.as_ref().ok_or("build互換性に関数不変量がない")?;
    let layout = plan
        .polynomial
        .as_ref()
        .filter(|l| l.data.complete)
        .or_else(|| plan.finite.as_ref().filter(|l| l.data.complete))
        .ok_or("build互換性に全域残差の表示がない")?;
    layout.recheck(env, g, c)?;
    let pattern = |r: NodeRef| {
        let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
            return Err("build patternがnativeでない".to_string());
        };
        let D::CircuitPattern(d) = &v.data else {
            return Err("build patternが別構成".to_string());
        };
        Ok(d)
    };
    let mut out = vec![];
    for a in 0..objects.objects.len() {
        for b in a + 1..objects.objects.len() {
            tick(c)?;
            let pa = patterns
                .rows
                .get(a)
                .ok_or("buildの元patternがない")?
                .pattern;
            let pb = patterns
                .rows
                .get(b)
                .ok_or("buildの先patternがない")?
                .pattern;
            if !pattern(pa)?.same_pattern(pattern(pb)?) {
                continue;
            }
            let numeric_family = |index: NodeRef,
                                  c: &Control|
             -> Result<
                Option<super::environment::numeric_law_function::Family>,
                ValidationFailure,
            > {
                let position = |object: usize| {
                    layout.data.objects[object]
                        .coordinates
                        .iter()
                        .find_map(|q| {
                            if q.index != index {
                                return None;
                            }
                            if let super::observable_layout::Source::Polynomial(p) = &q.source {
                                Some(p.position)
                            } else {
                                None
                            }
                        })
                };
                if let (Some(left), Some(right)) = (position(a), position(b)) {
                    let readings = plan.architecture.witness.readings();
                    let names = readings.instances()[left.instance]
                        .declaration()
                        .parameters
                        .iter()
                        .map(|(name, _)| (name.clone(), name.clone()))
                        .collect::<Vec<_>>();
                    let finite =
                        |object: usize| -> Result<Vec<(String, Scalar)>, ValidationFailure> {
                            let coordinate = layout.data.objects[object]
                                .coordinates
                                .iter()
                                .find(|q| q.index == index)
                                .ok_or("数値族の元座標がない")?;
                            let super::observable_layout::Source::Polynomial(q) =
                                &coordinate.source
                            else {
                                return Err("数値族が多項式の座標でない".into());
                            };
                            let origin = super::law_evaluation::origin(g, q.instance)?
                                .ok_or("数値族の元束縛がない")?;
                            let instance = &readings.instances()[q.position.instance];
                            origin
                                .bindings
                                .iter()
                                .filter(|binding| {
                                    instance.parameters().iter().any(|p| p.name == binding.name)
                                })
                                .map(|binding| {
                                    Ok((binding.name.clone(), g.scalar(binding.value)?.clone()))
                                })
                                .collect()
                        };
                    let source_bound = finite(a)?;
                    let target_bound = finite(b)?;
                    let family = super::environment::numeric_law_function::compare_bound(
                        env.indexes.inputs,
                        [readings, readings],
                        [left, right],
                        &names,
                        [&source_bound, &target_bound],
                        c,
                    )
                    .map_err(|e| match e {
                        crate::construction::ConstructionFailure::Stopped(s) => {
                            ValidationFailure::Stop(s)
                        }
                        e => format!("数値guardの全域互換性: {e:?}").into(),
                    })?;
                    return Ok(Some(family));
                }
                Ok(None)
            };
            let mut inputs = vec![objects.objects[a], objects.objects[b], pa, pb];
            let mut values = vec![];
            for axis in &views.axes {
                let Some(Payload::Construction(v)) = &g.get(axis.invariant)?.payload else {
                    return Err("buildの関数不変量がない".into());
                };
                let D::ViewInvariant(d) = &v.data else {
                    return Err("buildの関数不変量が別構成".into());
                };
                let left = *d.evaluations().get(a).ok_or("buildの元view評価がない")?;
                let right = *d.evaluations().get(b).ok_or("buildの先view評価がない")?;
                inputs.extend([axis.invariant, left, right]);
                values.push(evaluation(env, g, left, right, c)?);
            }
            if !views.pending.is_empty() {
                values.push(None)
            }
            let left = laws.objects.get(a).ok_or("buildの元Law行がない")?;
            let right = laws.objects.get(b).ok_or("buildの先Law行がない")?;
            for (column, (&l, &r)) in left.evaluations.iter().zip(&right.evaluations).enumerate() {
                inputs.extend([l, r]);
                let mut equal = evaluation(env, g, l, r, c)?;
                let index = laws.indices[column];
                if equal.is_none()
                    && super::law_evaluation::origin(g, index)?
                        .is_some_and(|o| o.zero_residual || o.guarded_family)
                    && let Some(family) = numeric_family(index, c)?
                {
                    equal = all([family.applicable, family.equivalent]);
                }
                values.push(equal);
            }
            let left = &layout.data.objects[a].coordinates;
            let right = &layout.data.objects[b].coordinates;
            if left.len() != right.len() {
                return Err("build互換性の全残差座標数が違う".into());
            }
            for (l, r) in left.iter().zip(right) {
                tick(c)?;
                if l.index != r.index || l.factor != r.factor {
                    return Err("build互換性の残差添字が違う".into());
                }
                match (l.value(Reading::Residual), r.value(Reading::Residual)) {
                    (Some(left), Some(right)) => {
                        inputs.extend([left, right]);
                        let mut equal = residual(env, g, left, right, c)?;
                        if equal.is_none()
                            && super::law_evaluation::origin(g, l.index)?
                                .is_some_and(|o| o.guarded_family)
                            && let Some(family) = numeric_family(l.index, c)?
                        {
                            equal = family.value_equal;
                        }
                        values.push(equal);
                    }
                    _ => values.push(None),
                }
            }
            inputs.sort_by_key(|r| r.0);
            inputs.dedup();
            out.push(Comparison {
                source: objects.objects[a],
                target: objects.objects[b],
                inputs,
                equal: all(values),
            });
        }
    }
    Ok(out)
}
