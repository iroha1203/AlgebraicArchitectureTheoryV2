//! 未束縛の数値引数を持つscalar多項式族。引数を有限標本や全称真偽に置換しない。
use super::*;
use crate::construction::readings::{InstanceApplication, ObjectEvaluationPosition};
use crate::observed::object_equation_presentation::{
    ParameterEquation, parameter_source_difference,
};

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
        if instance.parameters().is_empty()
            || instance
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
        // この経路の係数は元数値引数だけに依存する。観測slotは別の多項式経路で扱う。
        if !source.ring.symbols.is_empty() {
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
    let mut bases = vec![];
    for (_, source) in equations {
        let ty = &source.ring.ty;
        if bases.iter().any(|(t, _, _, _, _)| t == ty) {
            continue;
        }
        let scalar = push(parts, base, Part::Base(ty.clone()), c)?;
        let ring = push(
            parts,
            base,
            Part::Ring {
                base: scalar,
                variables: vec![],
            },
            c,
        )?;
        let domain = push(
            parts,
            base,
            Part::Domain {
                ring,
                ty: Type::Unit,
            },
            c,
        )?;
        let evaluation = push(
            parts,
            base,
            Part::Evaluation {
                source: ring,
                target: scalar,
                images: vec![],
            },
            c,
        )?;
        bases.push((ty.clone(), scalar, ring, domain, evaluation));
    }
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
            let difference = push(
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
            let nu = if source.difference.parameters.is_empty() {
                polynomial(parts, base, &source.difference.constant, *ring, &ty, 0, c)?
            } else {
                push(
                    parts,
                    base,
                    Part::Polynomial {
                        ring: *ring,
                        terms: vec![(difference, vec![])],
                    },
                    c,
                )?
            };
            let outside = matches!(
                a.readings().instances()[*instance].applications()[object],
                InstanceApplication::NotApplicable
            );
            let residual = if outside {
                let zero = EquationPolynomial::constant(super::super::numeric::zero(&ty, c)?, c)
                    .map_err(|e| construction_failure(&e))?;
                polynomial(parts, base, &zero, *ring, &ty, 0, c)?
            } else {
                nu
            };
            let witness = push(
                parts,
                base,
                Part::Ideal {
                    ring: *ring,
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
                epsilon: (!outside).then_some(nu),
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
        let quantifiers = out
            .originals
            .iter()
            .flat_map(|o| o.quantifiers.iter().cloned())
            .collect::<Vec<_>>();
        let context = push(
            parts,
            base,
            Part::Equation(E::Context {
                base: reference,
                carrier: common::carrier(a, c)?,
                dependencies: vec![],
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
                    && !polynomials.contains(&source.difference.constant)
                {
                    polynomials.push(source.difference.constant.clone());
                }
                for (_, coefficient) in &source.difference.parameters {
                    let p = EquationPolynomial::constant(coefficient.clone(), c)
                        .map_err(|e| construction_failure(&e))?;
                    if !p.terms.is_empty() && !polynomials.contains(&p) {
                        polynomials.push(p);
                    }
                }
            }
            let mut generators = vec![];
            for p in &polynomials {
                generators.push(polynomial(parts, base, p, *ring, ty, 0, c)?);
            }
            let required = push(
                parts,
                base,
                Part::Ideal {
                    ring: *ring,
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
