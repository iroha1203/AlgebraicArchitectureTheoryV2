//! 同じ元Law表・成分残差・完全patternからcircuitの反証条件を準備する。
use super::{
    build_plan::Plan,
    construction_result::ConstructionData as D,
    control::{Checkpoint, Control},
    environment::Environment,
    numeric,
    object_equation_presentation::EquationGuard,
    observable_layout::{Reading, Source},
    result::*,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Case {
    pub object: NodeRef,
    pub pattern: NodeRef,
    pub index: NodeRef,
    pub component: Vec<usize>,
    pub lhs: NodeRef,
    pub rhs: NodeRef,
    pub evaluation: NodeRef,
    pub architecture: NodeRef,
    pub bindings: Vec<Binding>,
    pub location: crate::issue::Location,
    pub epsilon: NodeRef,
    pub when: Option<bool>,
    pub guard: Option<NodeRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Detector {
    pub index: NodeRef,
    pub component: Vec<usize>,
    pub parameters: Vec<(String, crate::types::Type)>,
    pub cases: Vec<Case>,
}

fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectLawCircuits)?;
    Ok(())
}

/// 閉じた多項式の実値だけを読む。非定数式を非零の値と見なさない。
fn constant_nonzero(
    g: &Graph,
    r: NodeRef,
    ty: &crate::types::Type,
    c: &mut Control,
) -> Result<Option<bool>, ValidationFailure> {
    tick(c)?;
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("circuitの成分残差がnative値でない".into());
    };
    if let D::FiniteLaw(data) = &v.data {
        let (_, values) = data
            .function_values()
            .ok_or("circuitの有限残差が関数でない")?;
        let mut result = None;
        for r in values {
            tick(c)?;
            let value = g.scalar(*r)?;
            let nonzero = value != &numeric::zero(&value.ty(), c)?;
            if result.is_some_and(|old| old != nonzero) {
                return Ok(None);
            }
            result = Some(nonzero);
        }
        return Ok(result);
    }
    let D::PolynomialLaw(data) = &v.data else {
        return Err("circuitの成分残差が既存の環表示でない".into());
    };
    let (_, terms) = data.polynomial().ok_or("circuitの残差に多項式がない")?;
    let zero = numeric::zero(ty, c)?;
    let mut nonzero = false;
    for (coefficient, powers) in terms {
        tick(c)?;
        if powers.iter().any(|n| *n != 0) {
            return Ok(None);
        }
        if matches!(g.get(*coefficient)?.ty, NodeType::Expression(_)) { return Ok(None); }
        let coefficient = g.scalar(*coefficient)?;
        if coefficient.ty() != *ty {
            return Err("circuitの成分残差の係数型が違う".into());
        }
        if coefficient != &zero {
            nonzero = true;
        }
    }
    Ok(Some(nonzero))
}

/// Noneはこの閉じた成分経路の非適用。未計算値をreject detectorへ補わない。
pub(super) fn closed(
    env: &Environment<'_>,
    g: &Graph,
    plan: &Plan,
    c: &mut Control,
) -> Result<Option<Vec<Detector>>, ValidationFailure> {
    plan.boundary.recheck(env, g, plan.boundary.start(), c)?;
    let (Some(table), Some(patterns)) = (&plan.laws, &plan.patterns) else {
        return Ok(None);
    };
    let Some(layout) = plan
        .polynomial
        .as_ref()
        .filter(|l| l.data.complete)
        .or_else(|| plan.finite.as_ref().filter(|l| l.data.complete))
    else {
        return Ok(None);
    };
    layout.recheck(env, g, c)?;
    let Some(first) = layout.data.objects.first() else {
        return Err("circuitのbase座標がない".into());
    };
    let mut detectors = vec![];
    let diagrams = table.diagrams()?;
    for (ordinal, coordinate) in first.coordinates.iter().enumerate() {
        tick(c)?;
        let (index, component) = match &coordinate.source {
            Source::Polynomial(q) => (q.instance, q.component.clone()),
            Source::Finite(q) => (q.value.instance, q.value.component.clone()),
        };
        let column = table
            .indices
            .iter()
            .position(|r| *r == coordinate.index)
            .ok_or("circuitの元Law添字がない")?;
        let mut cases = vec![];
        let parameters = if let Source::Polynomial(q) = &coordinate.source && q.row.is_none() {
            let original = diagrams.first().and_then(|d| d.originals.iter().find(|o| o.reference == coordinate.index))
                .ok_or("circuitの元parameter宣言がない")?;
            let parameters = &original.parameters;
            // guardの自由引数もwhenの型域へ保持する。本文の差が定数でも消さない。
            if original.guard.is_some() { parameters.clone() } else if let Some(reference) = q.nu
                && let Some(Payload::Construction(value)) = &g.get(reference)?.payload
                && let D::PolynomialLaw(data) = &value.data
                && data.parameter_family(parameters) { parameters.clone() } else { vec![] }
        } else { vec![] };
        for (object, row) in layout.data.objects.iter().enumerate() {
            tick(c)?;
            let current = row
                .coordinates
                .get(ordinal)
                .ok_or("circuitの対象成分がない")?;
            if current.index != coordinate.index {
                return Err("circuitの対象Law添字が違う".into());
            }
            let (instance, lhs, rhs, actual_component, ty, guard) = match &current.source {
                Source::Polynomial(p) => (
                    p.instance,
                    p.lhs,
                    p.rhs,
                    &p.component,
                    p.ty.clone(),
                    Some(&p.guard),
                ),
                Source::Finite(p) => (
                    p.value.instance,
                    p.value.lhs,
                    p.value.rhs,
                    &p.value.component,
                    crate::types::Type::Z,
                    None,
                ),
            };
            if actual_component != &component {
                return Err("circuitの対象成分pathが違う".into());
            }
            let origin =
                super::law_evaluation::origin(g, instance)?.ok_or("circuitの元Law由来がない")?;
            if origin.outside || !origin.body_allowed {
                continue;
            }
            let mut never_refutes = false;
            if let Some(guard) = guard {
                match guard {
                    EquationGuard::AlwaysFalse | EquationGuard::OutsideObject => continue,
                    EquationGuard::AlwaysTrue => (),
                    EquationGuard::StateDependent | EquationGuard::Undetermined => {
                        let Some(residual) = current.value(Reading::Residual) else {
                            return Ok(None);
                        };
                        if !origin.zero_residual
                            || constant_nonzero(g, residual, &ty, c)? != Some(false)
                        {
                            return Ok(None);
                        }
                        never_refutes = true;
                    }
                }
            }
            let Some(epsilon) = current.value(Reading::Epsilon) else {
                return Ok(None);
            };
            let when = if never_refutes {
                Some(false)
            } else if !parameters.is_empty() {
                let Some(Payload::Construction(value)) = &g.get(epsilon)?.payload else { return Ok(None) };
                let D::PolynomialLaw(data) = &value.data else { return Ok(None) };
                if !data.parameter_family(&parameters) { return Ok(None); }
                None
            } else {
                let Some(value) = constant_nonzero(g, epsilon, &ty, c)? else { return Ok(None) };
                Some(value)
            };
            let pattern = patterns
                .rows
                .get(object)
                .ok_or("circuitのpattern行がない")?;
            let source = table.objects.get(object).ok_or("circuitの元評価行がない")?;
            if pattern.object != row.object || source.object != row.object {
                return Err("circuitの対象とpattern/元評価が違う".into());
            }
            let mut evaluation = source.evaluations[column];
            if let Some(Payload::Construction(v)) = &g.get(evaluation)?.payload
                && let D::LawFamily(data) = &v.data
                && let super::law_family::Kind::Evaluation { rows, .. } = &data.kind
            {
                let mut matching = vec![];
                for candidate in rows {
                    tick(c)?;
                    let row = super::law_evaluation::origin(g, candidate.law)?
                        .ok_or("circuitの実引数行がない")?;
                    let mut same = row.bindings.len() == origin.bindings.len();
                    for (left, right) in row.bindings.iter().zip(&origin.bindings) {
                        tick(c)?;
                        same &= left.name == right.name
                            && left.ty == right.ty
                            && g.scalar(left.value)? == g.scalar(right.value)?;
                    }
                    if same {
                        matching.push(candidate.evaluation);
                    }
                }
                let [actual] = matching.as_slice() else {
                    return Err("circuitの実引数に対応する評価が一つでない".into());
                };
                evaluation = *actual;
            }
            let location = crate::issue::Location::Law {
                span: env.inputs.law().exprs[origin.body].span,
            };
            cases.push(Case {
                object: row.object,
                pattern: pattern.pattern,
                index,
                component: component.clone(),
                lhs,
                rhs,
                evaluation,
                epsilon,
                when,
                guard: origin.guard_reference,
                architecture: source.architecture,
                bindings: origin.bindings,
                location,
            });
        }
        detectors.push(Detector {
            index,
            component,
            parameters,
            cases,
        });
    }
    Ok(Some(detectors))
}
