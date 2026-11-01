//! 全標準対象で同じ原始slotの型別K[X]を使うnative計画。
use super::*;
use crate::observed::{
    numeric_transport::NumericTransportValue, object_equation_presentation::EquationRing,
};

pub(super) struct Basis {
    pub ty: Type,
    pub scalar: NodeRef,
    pub ring: NodeRef,
    pub domain: NodeRef,
    pub evaluation: Option<NodeRef>,
    pub(super) variables: Vec<Variable>,
}
fn variable(
    s: &crate::observed::object_equation_presentation::EquationSymbol,
    ty: &Type,
) -> Variable {
    Variable {
        field: Fact {
            snapshot: s.slot.snapshot.clone(),
            subject: s.slot.subject.clone(),
            field: Some(s.slot.field.clone()),
            atom: None,
        },
        component: s.slot.component.clone(),
        ty: ty.clone(),
    }
}
fn basis(
    cores: &[(Option<Arc<EquationPresentation>>, Option<Unavailable>)],
    parts: &mut Vec<Part>,
    base: usize,
    c: &Control,
) -> Result<Vec<Basis>, ValidationFailure> {
    basis_from_rings(
        cores
            .iter()
            .flat_map(|(core, _)| core.iter().flat_map(|c| c.rings())),
        parts,
        base,
        c,
    )
}
pub(super) fn basis_from_rings<'a>(
    rings: impl IntoIterator<Item = &'a EquationRing>,
    parts: &mut Vec<Part>,
    base: usize,
    c: &Control,
) -> Result<Vec<Basis>, ValidationFailure> {
    let mut groups: Vec<(Type, Vec<(Variable, Option<NumericTransportValue>)>)> = vec![];
    for ring in rings {
        tick(c)?;
        if !matches!(ring.ty, Type::Z | Type::Q | Type::Fp(_)) {
            return Err(internal!("共有多項式の係数型がscalarでない").into());
        }
        let at = match groups.iter().position(|g| g.0 == ring.ty) {
            Some(at) => at,
            None => {
                groups.push((ring.ty.clone(), vec![]));
                groups.len() - 1
            }
        };
        let slots = &mut groups[at].1;
        for symbol in &ring.symbols {
            tick(c)?;
            let v = variable(symbol, &ring.ty);
            if let Some((_, previous)) = slots.iter().find(|(s, _)| s == &v) {
                if previous != &symbol.value {
                    return Err(internal!("共有原始slotの実観測値が対象で違う").into());
                }
            } else {
                slots.push((v, symbol.value.clone()));
            }
        }
    }
    let mut result = vec![];
    for (ty, slots) in groups {
        tick(c)?;
        let scalar = push(parts, base, Part::Base(ty.clone()), c)?;
        let variables: Vec<_> = slots.iter().map(|(v, _)| v.clone()).collect();
        let ring = push(
            parts,
            base,
            Part::Ring {
                base: scalar,
                variables: variables.clone(),
            },
            c,
        )?;
        let domain_ty = match variables.len() {
            0 => Type::Unit,
            1 => ty.clone(),
            n => Type::Tuple(vec![ty.clone(); n]),
        };
        let domain = push(
            parts,
            base,
            Part::Domain {
                ring,
                ty: domain_ty,
            },
            c,
        )?;
        let evaluation = if slots.iter().all(|(_, v)| v.is_some()) {
            let mut images = vec![];
            for (_, value) in &slots {
                tick(c)?;
                let value = value
                    .as_ref()
                    .ok_or(internal!("共有評価の実観測値がない"))?;
                let p = EquationPolynomial::constant(value.scalar().clone(), c)
                    .map_err(|e| construction_failure(&e))?;
                images.push(super::polynomial(parts, base, &p, scalar, &ty, 0, c)?);
            }
            Some(push(
                parts,
                base,
                Part::Evaluation {
                    source: ring,
                    target: scalar,
                    images,
                },
                c,
            )?)
        } else {
            None
        };
        result.push(Basis {
            ty,
            scalar,
            ring,
            domain,
            evaluation,
            variables,
        });
    }
    tick(c)?;
    Ok(result)
}
pub(super) fn polynomial(
    parts: &mut Vec<Part>,
    base: usize,
    p: &EquationPolynomial,
    ring: NodeRef,
    ty: &Type,
    original: &EquationRing,
    shared: Option<&[Basis]>,
    c: &Control,
) -> Result<NodeRef, ValidationFailure> {
    let Some(shared) = shared else {
        return super::polynomial(parts, base, p, ring, ty, original.symbols.len(), c);
    };
    let basis = shared
        .iter()
        .find(|b| b.ty == *ty)
        .ok_or(internal!("多項式の共有係数環がない"))?;
    if basis.ring != ring {
        return Err(internal!("多項式が別の共有環を参照した").into());
    }
    let mut mapping = vec![];
    for symbol in &original.symbols {
        tick(c)?;
        let v = variable(symbol, ty);
        mapping.push(
            basis
                .variables
                .iter()
                .position(|s| s == &v)
                .ok_or(internal!("元原始slotの共有記号がない"))?,
        );
    }
    let mut mapped = p.clone();
    for term in &mut mapped.terms {
        for v in &mut term.variables {
            tick(c)?;
            *v = *mapping
                .get(*v)
                .ok_or(internal!("元多項式の局所記号が域外"))?;
        }
        term.variables.sort_unstable();
    }
    super::polynomial(parts, base, &mapped, ring, ty, basis.variables.len(), c)
}
impl Source {
    pub(super) fn compute_family(
        inputs: Arc<CheckedInputs>,
        a: Arc<ArchitectureWitness>,
        reference: NodeRef,
        base: usize,
        c: &Control,
    ) -> Result<Self, ValidationFailure> {
        tick(c)?;
        if inputs.sources() != Witness::Architecture(a.clone()).inputs().sources() {
            return Err(internal!("共有多項式族の元三入力とArchitectureが違う").into());
        }
        if let Some(equations) = parameters::sources(&inputs, &a, c)? {
            let mut parts = vec![];
            let mut outputs =
                parameters::plans(&inputs, &a, reference, &equations, &mut parts, base, c)?;
            if outputs.is_empty() {
                return Err(internal!("数値族のbase対象がない").into());
            }
            let first = outputs.remove(0);
            let (support, scope) = metadata(&inputs, &a, None, c)?;
            return Ok(Self {
                inputs,
                architecture: a,
                reference,
                object: 0,
                core: None,
                base,
                parts,
                outputs: first,
                owned_outputs: Some(outputs),
                support,
                scope,
            });
        }
        let mut cores = vec![];
        for object in 0..a.readings().objects().len() {
            tick(c)?;
            cores.push(calculate(inputs.clone(), &a, object, c)?);
        }
        let mut parts = vec![];
        let shared = basis(&cores, &mut parts, base, c)?;
        let mut outputs = vec![];
        let mut support = vec![];
        let mut scope = Scope::default();
        for (core, reason) in &cores {
            tick(c)?;
            let out = match (core, reason) {
                (Some(core), None) => {
                    let mut out = object_plan(core, &inputs, base, &mut parts, Some(&shared), c)?;
                    append_presentations(
                        &inputs,
                        &a,
                        reference,
                        core,
                        &mut parts,
                        &mut out,
                        base,
                        Some(&shared),
                        c,
                    )?;
                    out
                }
                (None, Some(reason)) => {
                    let at = base
                        .checked_add(parts.len())
                        .ok_or(internal!("共有多項式の生成位置が域外"))?;
                    let (extra, out) = symbolic_plan(&inputs, &a, reason.clone(), at, c)?;
                    parts.extend(extra);
                    out
                }
                _ => return Err(internal!("共有多項式族の元計算状態が不正").into()),
            };
            let (facts, s) = metadata(&inputs, &a, core.as_deref(), c)?;
            support.extend(facts);
            scope.merge(&s);
            outputs.push(out);
        }
        support.sort_by_key(|f| f.wire().canonical());
        support.dedup();
        if outputs.is_empty() {
            return Err(internal!("共有多項式族のbase対象がない").into());
        }
        let first = outputs.remove(0);
        let core = cores.first().and_then(|(core, _)| core.clone());
        tick(c)?;
        Ok(Self {
            inputs,
            architecture: a,
            reference,
            object: 0,
            core,
            base,
            parts,
            outputs: first,
            owned_outputs: Some(outputs),
            support,
            scope,
        })
    }
}
