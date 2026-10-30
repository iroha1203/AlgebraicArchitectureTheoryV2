//! 未束縛の数値引数を持つscalar多項式族。引数を有限標本や全称真偽に置換しない。
use super::*;
use crate::construction::readings::{InstanceApplication, ObjectEvaluationPosition};
use crate::observed::object_equation_presentation::{
    ParameterEquation, parameter_source_difference_bound,
};

fn observation_free_difference(source: &ParameterEquation) -> bool {
    source.difference.constant.terms.iter().all(|term| term.variables.is_empty())
        && source.difference.parameters.iter().all(|(_, coefficient)| coefficient.terms.iter().all(|term| term.variables.is_empty()))
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
    let mut symbolic = false;
    for (i, instance) in a.readings().instances().iter().enumerate() {
        tick(c)?;
        if instance.declaration().kind != "law" {
            continue;
        }
        if instance.applications().iter().any(|a| match a {
            InstanceApplication::NotApplicable => false,
            InstanceApplication::Applicable { conditions } => !conditions.is_empty(),
        }) {
            return Ok(None);
        }
        let mut cases: Vec<Vec<(String, Scalar)>> = vec![vec![]];
        for parameter in instance.parameters() {
            tick(c)?;
            match &parameter.ty {
                ty if numeric_parameters::numeric_width(ty).is_some() => (),
                Type::Unit | Type::Bool | Type::Fp(_) | Type::Tuple(_) | Type::Option(_) | Type::Data(_) | Type::Set(_) => {
                    if !super::super::finite::completion_supported(&parameter.ty, inputs.law(), c)? { return Ok(None); }
                    let values = super::super::finite::values(&parameter.ty, inputs.law(), c,
                        &mut |_| Err("有限値型に参照rosterはない".into()), &mut |_| {})?;
                    let mut next = vec![];
                    for case in cases {
                        for value in &values.values {
                            tick(c)?;
                            let mut case = case.clone();
                            case.push((parameter.name.clone(), value.clone()));
                            next.push(case);
                        }
                    }
                    cases = next;
                }
                _ => return Ok(None),
            }
        }
        for finite in cases {
            tick(c)?;
            let source = match parameter_source_difference_bound(inputs, instance, &finite, c)
                .map_err(|e| construction_failure(&e))?
            {
                Some(source) => source,
                None => {
                    let Some(source) =
                        super::super::object_equation_presentation::parameter_source_on_guard_fiber(
                            inputs,
                            a.readings(),
                            i,
                            &finite,
                            c,
                        )
                        .map_err(|e| construction_failure(&e))?
                    else {
                        return Ok(None);
                    };
                    source
                }
            };
            // 正規化で数値軸が消えても、有限値で固定した各ケースの元量化を保持する。
            symbolic |= source.guard.dynamic()
                || !source.difference.parameters.is_empty()
                || (!source.finite.is_empty()
                    && instance
                        .parameters()
                        .iter()
                        .any(|p| numeric_parameters::numeric_width(&p.ty).is_some()));
            equations.push((i, source));
        }
    }
    Ok(symbolic.then_some(equations))
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
                b.evaluation,
            ))
        })
        .collect::<Result<_, ValidationFailure>>()?;
    let mut result = vec![];
    let mut indicators = vec![];
    for object in 0..a.readings().objects().len() {
        tick(c)?;
        let originals = super::sources::symbolic_bound(inputs, a.readings(), equations, parts, base, c)?;
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
            let original = out.originals.get(ordinal).ok_or("数値族の元Lawがない")?;
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
            } else if source.difference.parameters.iter().any(|(_, coefficient)| coefficient.terms.iter().any(|term| !term.variables.is_empty())) {
                parameter_polynomial(inputs, original, source, *ring, &ty, &shared, parts, base, c)?
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
            let missing = source.ring.symbols.iter().any(|s| s.value.is_none());
            let epsilon = if outside || source.guard.is_false() || missing {
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
            let residual = if outside || source.guard.is_false() || source.guard.zero_at(object,c)? {
                let zero = EquationPolynomial::constant(super::super::numeric::zero(&ty, c)?, c)
                    .map_err(|e| construction_failure(&e))?;
                Some(polynomial(parts, base, &zero, *ring, &ty, variables, c)?)
            } else if source.guard.pending_at(object).is_some() {
                None
            } else if source.guard.dynamic() {
                match epsilon {
                    Some(epsilon) => Some(guarded_residual(parts, base, original, epsilon, &ty, &mut indicators, c)?),
                    None => None,
                }
            } else {
                epsilon
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
                residual,
                witness: Some(witness),
                guard: if outside {
                    EquationGuard::OutsideObject
                } else if source.guard.is_false() {
                    EquationGuard::AlwaysFalse
                } else if source.guard.dynamic() {
                    EquationGuard::Undetermined
                } else {
                    EquationGuard::AlwaysTrue
                },
                status: if outside || source.guard.is_false() {
                    EquationPresentationStatus::NotApplicable
                } else if missing || source.guard.pending_at(object).is_some() {
                    EquationPresentationStatus::Undetermined
                } else {
                    EquationPresentationStatus::Ready
                },
            });
            if !outside
                && !source.guard.is_false()
                && (missing || source.guard.pending_at(object).is_some())
            {
                out.status = EquationPresentationStatus::Undetermined;
            }
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
        for (_, source) in equations {
            positions.extend(source.guard.support_at(object).iter().filter(|f| f.field.is_some()).cloned());
            if let Some(pending) = source.guard.pending_at(object) { positions.extend(pending.missing.iter().cloned()); }
        }
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
                dependencies: dependencies.slots.clone(),
                laws: out.originals.iter().map(|o| o.reference).collect(),
                quantifiers: quantifiers.clone(),
            }),
            c,
        )?;
        out.context = Some(context);
        for (ty, scalar, ring, domain, evaluation) in &bases {
            let mut polynomials = vec![];
            for q in out.coordinates.iter().filter(|q| {
                q.required && q.ring == Some(*ring) && q.guard == EquationGuard::AlwaysTrue
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
                    let p = coefficient.clone();
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
            let mut missing_positions = coordinates.iter()
                .filter(|q| !matches!(q.guard, EquationGuard::AlwaysFalse | EquationGuard::OutsideObject) && q.epsilon.is_none())
                .flat_map(|q| equations[q.occurrence].1.ring.symbols.iter())
                .filter(|s| s.value.is_none())
                .map(|s| Fact { snapshot: s.slot.snapshot.clone(), subject: s.slot.subject.clone(), field: Some(s.slot.field.clone()), atom: None })
                .collect::<Vec<_>>();
            for q in &coordinates {
                if let Some(pending) = equations[q.occurrence].1.guard.pending_at(object) {
                    missing_positions.extend(pending.missing.iter().cloned());
                }
            }
            missing_positions.sort();
            missing_positions.dedup();
            let mut omissions = dependencies.missing_reasons(inputs, &missing_positions,
                &out.originals.iter().flat_map(|o| std::iter::once(o.body).chain(o.guard)).collect::<Vec<_>>(),
                Witness::Architecture(a.clone()).request(), c)?;
            let request_witness = Witness::Architecture(a.clone());
            let request = request_witness.request();
            for q in &coordinates {
                if let Some(pending) = equations[q.occurrence]
                    .1
                    .guard
                    .pending_at(object)
                    .filter(|pending| pending.unsupported_numeric)
                {
                    omissions.push(Reason {
                        kind: ReasonKind::UnsupportedAlgorithm {
                            question: request.kind,
                            operand_types: out.originals[q.occurrence]
                                .parameters
                                .iter()
                                .map(|(_, ty)| ty.clone())
                                .collect(),
                            method: "numeric guard decision".into(),
                        },
                        request: request.id.clone(),
                        dependencies: std::iter::once(out.originals[q.occurrence].body)
                            .chain(out.originals[q.occurrence].guard)
                            .collect(),
                        missing: vec![],
                        location: Some(pending.location.clone()),
                    });
                }
            }
            sort_reasons(&mut omissions);
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
                    evaluation: *evaluation,
                    context,
                    quantifiers: quantifiers.clone(),
                    omissions,
                }),
                c,
            )?;
            out.rings.push(*ring);
            out.bases.push(*scalar);
            out.domains.push(*domain);
            out.evaluations.push(*evaluation);
            out.required.push(required);
            out.presentations.push(Some(presentation));
        }
        result.push(out);
    }
    Ok(result)
}

fn parameter_polynomial(
    inputs: &CheckedInputs, original: &Original, source: &ParameterEquation,
    ring: NodeRef, ty: &Type, shared: &[family::Basis], parts: &mut Vec<Part>, base: usize, c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let constant = family::polynomial(parts, base, &source.difference.constant, ring, ty, &source.ring, Some(shared), c)?;
    let Part::Polynomial { terms, .. } = &parts[constant.0 - base] else { return Err("引数族の定数項が多項式でない".into()) };
    let mut result = terms.clone();
    let Part::Source { location: Location::Law { span }, .. } = &parts[original.body.0 - base] else { return Err("引数族の元bodyがない".into()) };
    let span = *span;
    for (parameter, coefficient) in &source.difference.parameters {
        tick(c)?;
        let (expression, node) = inputs.law().exprs.iter().enumerate().find(|(id, expression)| {
            inputs.law().expr_type(*id) == Some(ty) && expression.span.0 >= span.0 && expression.span.1 <= span.1 &&
                matches!(&expression.kind, crate::law::ast::ExprKind::Dotted(names) if names.len() == 1 && names[0].name == parameter.name)
        }).ok_or("引数族の元parameter参照がない")?;
        let argument = push(parts, base, Part::Source { quantifiers: original.quantifiers.clone(), instance: original.instance, row: original.row,
            expression, location: Location::Law { span: node.span }, ty: ty.clone(), parameters: original.parameters.clone(), bindings: original.bindings.clone() }, c)?;
        let polynomial = family::polynomial(parts, base, coefficient, ring, ty, &source.ring, Some(shared), c)?;
        let Part::Polynomial { terms, .. } = &parts[polynomial.0 - base] else { return Err("引数係数が多項式でない".into()) };
        for (scalar, powers) in terms.clone() {
            let product = push(parts, base, Part::Transform { quantifiers: original.quantifiers.clone(), operation: Transform::Multiply,
                parameters: original.parameters.clone(), ty: ty.clone(), operands: vec![argument, scalar], bindings: vec![], position: None }, c)?;
            // 同じ単項式の係数は差を用いて正確に加える。
            if let Some((previous, _)) = result.iter_mut().find(|(_, old)| old == &powers) {
                let zero = push(parts, base, Part::Scalar(super::super::numeric::zero(ty, c)?), c)?;
                let negative = difference(parts, base, original, ty, zero, product, c)?;
                *previous = difference(parts, base, original, ty, *previous, negative, c)?;
            } else { result.push((product, powers)); }
        }
    }
    result.sort_by(|a, b| a.1.cmp(&b.1));
    push(parts, base, Part::Polynomial { ring, parameters: original.parameters.clone(), terms: result }, c)
}

// Bool全域の型付き写像 false→0,true→1 を元guardへ後合成し、εへ掛ける。
// 既存StateMap/compose/multiplyの表示だけで、各引数での条件付き残差を保持する。
fn guarded_residual(
    parts: &mut Vec<Part>,
    base: usize,
    original: &Original,
    epsilon: NodeRef,
    ty: &Type,
    indicators: &mut Vec<(Type, NodeRef)>,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let Some(index) = epsilon.0.checked_sub(base) else {
        return Err("条件付きεが計画外".into());
    };
    let Some(Part::Polynomial { ring, terms, .. }) = parts.get(index).cloned() else {
        return Err("条件付きεが多項式でない".into());
    };
    if terms.is_empty() {
        return Ok(epsilon);
    }
    let guard = original.guard.ok_or("条件付き数値族の元guardがない")?;
    let map = if let Some((_, map)) = indicators.iter().find(|(kind, _)| kind == ty) {
        *map
    } else {
        let no = push(parts, base, Part::Scalar(Scalar::Bool(false)), c)?;
        let yes = push(parts, base, Part::Scalar(Scalar::Bool(true)), c)?;
        let source = push(
            parts,
            base,
            Part::ReadingDomain {
                ty: Type::Bool,
                elements: Some(vec![no, yes]),
            },
            c,
        )?;
        let target = push(
            parts,
            base,
            Part::ReadingDomain {
                ty: ty.clone(),
                elements: None,
            },
            c,
        )?;
        let zero = push(
            parts,
            base,
            Part::Scalar(super::super::numeric::zero(ty, c)?),
            c,
        )?;
        let one = push(
            parts,
            base,
            Part::Scalar(super::super::numeric::literal("1", ty, c)?),
            c,
        )?;
        let map = push(
            parts,
            base,
            Part::FiniteMap {
                source,
                target,
                pairs: vec![(no, zero), (yes, one)],
            },
            c,
        )?;
        indicators.push((ty.clone(), map));
        map
    };
    let indicator = push(
        parts,
        base,
        Part::Transform {
            quantifiers: original.quantifiers.clone(),
            operation: Transform::Compose,
            parameters: original.parameters.clone(),
            ty: ty.clone(),
            operands: vec![guard, map],
            bindings: vec![],
            position: None,
        },
        c,
    )?;
    let mut guarded = vec![];
    for (coefficient, powers) in terms {
        tick(c)?;
        let coefficient = push(
            parts,
            base,
            Part::Transform {
                quantifiers: original.quantifiers.clone(),
                operation: Transform::Multiply,
                parameters: original.parameters.clone(),
                ty: ty.clone(),
                operands: vec![indicator, coefficient],
                bindings: vec![],
                position: None,
            },
            c,
        )?;
        guarded.push((coefficient, powers));
    }
    push(
        parts,
        base,
        Part::Polynomial {
            ring,
            terms: guarded,
            parameters: original.parameters.clone(),
        },
        c,
    )
}
