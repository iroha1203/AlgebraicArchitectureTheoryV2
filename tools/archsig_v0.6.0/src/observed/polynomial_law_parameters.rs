//! 未束縛の数値引数を持つscalar多項式族。引数を有限標本や全称真偽に置換しない。
use super::*;
use crate::construction::readings::{InstanceApplication, ObjectEvaluationPosition};
use crate::observed::object_equation_presentation::{
    ParameterEquation, parameter_source_difference,
};

fn observation_free_difference(source: &ParameterEquation) -> bool {
    source.difference.constant.terms.iter().all(|term| term.variables.is_empty())
}

fn difference(
    parts: &mut Vec<Part>,
    base: usize,
    original: &Original,
    ty: &Type,
    lhs: NodeRef,
    rhs: NodeRef,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    push(
        parts,
        base,
        Part::Transform {
            quantifiers: original.quantifiers.clone(),
            operation: Transform::Difference,
            parameters: original.parameters.clone(),
            ty: ty.clone(),
            operands: vec![lhs, rhs],
            bindings: vec![],
            position: None,
        },
        c,
    )
}

pub(super) fn sources(
    inputs: &CheckedInputs,
    a: &ArchitectureWitness,
    c: &mut Control,
) -> Result<Option<Vec<(usize, ParameterEquation)>>, ValidationFailure> {
    let mut equations = vec![];
    let mut varying = false;
    for (i, instance) in a.readings().instances().iter().enumerate() {
        tick(c)?;
        if instance.declaration().kind != "law" {
            continue;
        }
        if instance
            .parameters()
            .iter()
            .any(|p| !matches!(p.ty, Type::Z | Type::Q))
        {
            return Ok(None);
        }
        let Some(source) = parameter_source_difference(inputs, instance, c)
            .map_err(|e| construction_failure(&e))?
        else {
            return Ok(None);
        };
        if source.ring.symbols.iter().any(|s| s.value.is_none()) {
            return Ok(None);
        }
        if instance.applications().iter().any(|a| match a {
            InstanceApplication::NotApplicable => false,
            InstanceApplication::Applicable { conditions } => !conditions.is_empty(),
        }) {
            return Ok(None);
        }
        varying |= !source.difference.parameters.is_empty();
        equations.push((i, source));
    }
    Ok(varying.then_some(equations))
}

pub(super) fn plans(
    inputs: &CheckedInputs,
    a: &Arc<ArchitectureWitness>,
    reference: NodeRef,
    equations: &[(usize, ParameterEquation)],
    parts: &mut Vec<Part>,
    base: usize,
    c: &mut Control,
) -> Result<Vec<Diagram>, ValidationFailure> {
    use super::super::equation_presentation_node::{self as common, Coordinate as C, Part as E};
    let shared = family::basis_from_rings(
        equations.iter().map(|(_, source)| &source.ring),
        parts,
        base,
        c,
    )?;
    let bases: Vec<_> = shared
        .iter()
        .map(|b| {
            Ok((
                b.ty.clone(),
                b.scalar,
                b.ring,
                b.domain,
                b.evaluation.ok_or("数値族の共有観測代入がない")?,
            ))
        })
        .collect::<Result<_, ValidationFailure>>()?;
    let mut result = vec![];
    for object in 0..a.readings().objects().len() {
        tick(c)?;
        let originals = super::sources::symbolic(inputs, a.readings(), parts, base, c)?;
        let mut out = Diagram {
            unavailable: None,
            context: None,
            presentations: vec![],
            originals,
            rings: vec![],
            domains: vec![],
            bases: vec![],
            required: vec![],
            evaluations: vec![],
            coordinates: vec![],
            readings: vec![],
            status: EquationPresentationStatus::Ready,
        };
        for (ordinal, (instance, source)) in equations.iter().enumerate() {
            let original = out
                .originals
                .iter()
                .find(|o| o.instance == *instance)
                .ok_or("数値族の元Lawがない")?;
            let ((lhs, ty), (rhs, _)) = original.operands.clone().ok_or("数値族の左右式がない")?;
            let (_, _, ring, _, _) = bases
                .iter()
                .find(|b| b.0 == ty)
                .ok_or("数値族の共有環がない")?;
            let expression = push(
                parts,
                base,
                Part::Transform {
                    quantifiers: original.quantifiers.clone(),
                    operation: Transform::Difference,
                    parameters: original.parameters.clone(),
                    ty: ty.clone(),
                    operands: vec![lhs, rhs],
                    bindings: vec![],
                    position: None,
                },
                c,
            )?;
            let variables = shared
                .iter()
                .find(|b| b.ring == *ring)
                .ok_or("数値族の共有環がない")?
                .variables
                .len();
            let nu = if source.difference.parameters.is_empty() {
                family::polynomial(
                    parts,
                    base,
                    &source.difference.constant,
                    *ring,
                    &ty,
                    &source.ring,
                    Some(&shared),
                    c,
                )?
            } else if !observation_free_difference(source) {
                // 差Dの全引数を零へ同時代入したD(0)は観測多項式。
                // D-D(0)へ定数項を戻して、元式由来の引数係数を作る。
                let mut bindings = vec![];
                for (name, parameter_type) in &original.parameters {
                    let zero = super::super::numeric::zero(parameter_type, c)?;
                    let value = push(parts, base, Part::Scalar(zero), c)?;
                    bindings.push(Binding { name: name.clone(), ty: parameter_type.clone(), value });
                }
                let at_zero = push(parts, base, Part::Transform {
                    quantifiers: original.quantifiers.clone(),
                    operation: Transform::Substitute,
                    parameters: vec![],
                    ty: ty.clone(),
                    operands: vec![expression],
                    bindings,
                    position: None,
                }, c)?;
                let mut coefficient = difference(parts, base, original, &ty, expression, at_zero, c)?;
                let mut field = source.difference.constant.clone();
                if let Some(term) = field.terms.iter().find(|term| term.variables.is_empty()) {
                    let negative = super::super::numeric::unary(
                        crate::law::ast::UnOp::Neg, term.coefficient.scalar(), c,
                    )?;
                    let constant = push(parts, base, Part::Scalar(negative), c)?;
                    coefficient = difference(parts, base, original, &ty, coefficient, constant, c)?;
                    field.terms.retain(|term| !term.variables.is_empty());
                }
                let reference = family::polynomial(
                    parts,
                    base,
                    &field,
                    *ring,
                    &ty,
                    &source.ring,
                    Some(&shared),
                    c,
                )?;
                let Part::Polynomial { terms, .. } = &parts[reference.0 - base] else {
                    return Err("数値族の観測項が多項式でない".into());
                };
                let mut terms = terms.clone();
                if reference.0 != base + parts.len() - 1 {
                    return Err("数値族の観測項が末尾にない".into());
                }
                parts.pop();
                terms.push((coefficient, vec![0; variables]));
                terms.sort_by(|a, b| a.1.cmp(&b.1));
                push(
                    parts,
                    base,
                    Part::Polynomial {
                        ring: *ring,
                        parameters: original.parameters.clone(),
                        terms,
                    },
                    c,
                )?
            } else {
                push(
                    parts,
                    base,
                    Part::Polynomial {
                        ring: *ring,
                        parameters: original.parameters.clone(),
                        terms: vec![(expression, vec![0; variables])],
                    },
                    c,
                )?
            };
            let outside = matches!(
                a.readings().instances()[*instance].applications()[object],
                InstanceApplication::NotApplicable
            );
            let epsilon = if outside {
                None
            } else if observation_free_difference(source) {
                Some(nu)
            } else if source.difference.parameters.is_empty() {
                let values = source
                    .ring
                    .symbols
                    .iter()
                    .map(|s| s.value.clone())
                    .collect::<Vec<_>>();
                let value = source
                    .difference
                    .constant
                    .evaluate(&values, c)
                    .map_err(|e| construction_failure(&e))?
                    .ok_or("数値族の実観測代入がない")?;
                let p = EquationPolynomial::constant(value.scalar().clone(), c)
                    .map_err(|e| construction_failure(&e))?;
                Some(polynomial(parts, base, &p, *ring, &ty, variables, c)?)
            } else {
                Some(push(
                    parts,
                    base,
                    Part::Polynomial {
                        ring: *ring,
                        parameters: original.parameters.clone(),
                        terms: vec![(expression, vec![0; variables])],
                    },
                    c,
                )?)
            };
            let residual = if outside {
                let zero = EquationPolynomial::constant(super::super::numeric::zero(&ty, c)?, c)
                    .map_err(|e| construction_failure(&e))?;
                polynomial(parts, base, &zero, *ring, &ty, variables, c)?
            } else {
                epsilon.ok_or("適用された数値族の実差がない")?
            };
            let witness = push(
                parts,
                base,
                Part::Ideal {
                    ring: *ring,
                    parameters: if source.difference.parameters.is_empty() {
                        vec![]
                    } else {
                        original.parameters.clone()
                    },
                    generators: vec![nu],
                    required: false,
                },
                c,
            )?;
            let role = match &inputs.law().declarations
                [&a.readings().instances()[*instance].declaration().name]
                .signature
            {
                Signature::Law { role, .. } => *role,
                _ => return Err("数値族のLaw宣言がない".into()),
            };
            out.coordinates.push(Coordinate {
                occurrence: ordinal,
                instance: original.reference,
                lhs,
                rhs,
                position: ObjectEvaluationPosition {
                    object,
                    instance: *instance,
                },
                row: None,
                case: 0,
                component: vec![],
                ty,
                required: role == Role::Required,
                ring: Some(*ring),
                left: None,
                right: None,
                nu: Some(nu),
                epsilon,
                residual: Some(residual),
                witness: Some(witness),
                guard: if outside {
                    EquationGuard::OutsideObject
                } else {
                    EquationGuard::AlwaysTrue
                },
                status: if outside {
                    EquationPresentationStatus::NotApplicable
                } else {
                    EquationPresentationStatus::Ready
                },
            });
        }
        let mut quantifiers = vec![];
        for original in &out.originals {
            for quantifier in &original.quantifiers {
                tick(c)?;
                if !quantifiers.contains(quantifier) {
                    quantifiers.push(quantifier.clone());
                }
            }
        }
        let mut positions = shared
            .iter()
            .flat_map(|b| b.variables.iter().map(|v| v.field.clone()))
            .collect::<Vec<_>>();
        positions.sort();
        positions.dedup();
        let dependencies = common::dependencies(inputs, &positions, c, |value| {
            let at = base
                .checked_add(parts.len())
                .ok_or("数値族Contextの生成番号が範囲外")?;
            parts.push(Part::Scalar(value));
            Ok(NodeRef(at))
        })?;
        let context = push(
            parts,
            base,
            Part::Equation(E::Context {
                base: reference,
                carrier: common::carrier(a, c)?,
                dependencies: dependencies.slots,
                laws: out.originals.iter().map(|o| o.reference).collect(),
                quantifiers: quantifiers.clone(),
            }),
            c,
        )?;
        out.context = Some(context);
        for (ty, scalar, ring, domain, evaluation) in &bases {
            let mut polynomials = vec![];
            for q in out.coordinates.iter().filter(|q| {
                q.required && q.ring == Some(*ring) && q.guard != EquationGuard::OutsideObject
            }) {
                let source = &equations[q.occurrence].1;
                // 全引数の値で生成されるidealは、定数項と各独立軸の係数で生成される。
                if !source.difference.constant.terms.is_empty()
                    && !polynomials.iter().any(
                        |(p, r): &(
                            EquationPolynomial,
                            &super::super::object_equation_presentation::EquationRing,
                        )| {
                            p == &source.difference.constant && *r == &source.ring
                        },
                    )
                {
                    polynomials.push((source.difference.constant.clone(), &source.ring));
                }
                for (_, coefficient) in &source.difference.parameters {
                    let p = EquationPolynomial::constant(coefficient.clone(), c)
                        .map_err(|e| construction_failure(&e))?;
                    if !p.terms.is_empty()
                        && !polynomials.iter().any(|(previous, _)| previous == &p)
                    {
                        polynomials.push((p, &source.ring));
                    }
                }
            }
            let mut generators = vec![];
            for (p, original) in &polynomials {
                generators.push(family::polynomial(
                    parts,
                    base,
                    p,
                    *ring,
                    ty,
                    original,
                    Some(&shared),
                    c,
                )?);
            }
            let required = push(
                parts,
                base,
                Part::Ideal {
                    ring: *ring,
                    parameters: vec![],
                    generators,
                    required: true,
                },
                c,
            )?;
            let coordinates = out
                .coordinates
                .iter()
                .filter(|q| q.ring == Some(*ring))
                .collect::<Vec<_>>();
            let presentation = push(
                parts,
                base,
                Part::Equation(E::Presentation {
                    instances: coordinates.iter().map(|q| q.instance).collect(),
                    domain: *domain,
                    ring: *ring,
                    coordinates: coordinates
                        .iter()
                        .map(|q| C {
                            instance: q.instance,
                            component: vec![],
                            lhs: q.lhs,
                            rhs: q.rhs,
                            nu: q.nu.unwrap(),
                            epsilon: q.epsilon,
                        })
                        .collect(),
                    witnesses: coordinates.iter().map(|q| q.witness.unwrap()).collect(),
                    required,
                    evaluation: Some(*evaluation),
                    context,
                    quantifiers: quantifiers.clone(),
                    omissions: vec![],
                }),
                c,
            )?;
            out.rings.push(*ring);
            out.bases.push(*scalar);
            out.domains.push(*domain);
            out.evaluations.push(Some(*evaluation));
            out.required.push(required);
            out.presentations.push(Some(presentation));
        }
        result.push(out);
    }
    Ok(result)
}
