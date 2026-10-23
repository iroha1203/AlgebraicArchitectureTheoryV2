//! 型別の共有多項式を、共通Uとroot存在Atom上のblock座標へ配置する。
use super::{
    construction_result::{self as native, ConstructionData as D, ConstructionType as T},
    control::{Checkpoint, Control},
    environment::Environment,
    law_table::Table,
    object_equation_presentation::{EquationGuard, EquationPresentationStatus},
    polynomial_law_diagram::{Coordinate as SourceCoordinate, Unavailable},
    result::*,
};
use std::sync::Arc;
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Coordinate {
    pub index: NodeRef,
    pub factor: Option<usize>,
    pub source: SourceCoordinate,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Object {
    pub object: NodeRef,
    pub architecture: NodeRef,
    pub context: Option<NodeRef>,
    pub presentations: Vec<Option<NodeRef>>,
    pub coordinates: Vec<Coordinate>,
    pub unavailable: Option<Unavailable>,
    pub status: EquationPresentationStatus,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Data {
    pub architecture: NodeRef,
    pub universe: NodeRef,
    pub anchor: Fact,
    pub indices: Vec<NodeRef>,
    pub factors: Vec<NodeRef>,
    pub objects: Vec<Object>,
    pub support: Vec<Fact>,
    pub scope: Scope,
    pub reasons: Vec<Reason>,
    pub complete: bool,
}
#[derive(Clone, Debug)]
pub(super) struct Layout {
    pub data: Data,
    table: Arc<Table>,
}
#[derive(Clone, Copy, Debug)]
pub(super) enum Reading {
    Nu,
    Epsilon,
    Residual,
}
/// 零と、指定座標の値がまだ生成されていないことを区別する。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Placed {
    Zero { ring: NodeRef },
    Value { ring: NodeRef, reference: NodeRef },
    Uncomputed { ring: NodeRef },
}
/// 生成元と全表の再検査に成功した配置だけから読取りを作る。
pub(super) struct Checked<'a> {
    data: &'a Data,
    atoms: &'a [Fact],
}
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::EquationPresentation)?;
    Ok(())
}
fn check_refs(
    env: &Environment<'_>,
    g: &Graph,
    rs: impl IntoIterator<Item = NodeRef>,
    support: &mut Vec<Fact>,
    scope: &mut Scope,
    reasons: &mut Vec<Reason>,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    for r in rs {
        tick(c)?;
        let n = g.get(r)?;
        env.recheck_node(g, n, r.0)?;
        support.extend(n.support.iter().cloned());
        scope.merge(&n.scope);
        reasons.extend(n.reasons.iter().cloned());
    }
    Ok(())
}
fn universe(g: &Graph, architecture: NodeRef) -> Result<(NodeRef, Fact), ValidationFailure> {
    let a = native::architecture_origin(g, architecture, 0)?;
    let anchor = a.construction().root().clone();
    if anchor.field.is_some() || anchor.atom.is_some() {
        return Err("Observableのrootが存在Atomでない".into());
    }
    let mut result = None;
    for (i, n) in g.nodes.iter().enumerate().take(architecture.0) {
        g.tick()?;
        if matches!(&n.payload,Some(Payload::Construction(v)) if matches!(&v.data,D::AtomUniverse(atoms) if atoms==a.construction().universe()))
        {
            result = Some(NodeRef(i));
            break;
        }
    }
    let r = result.ok_or("Observableの元AtomUniverseがない")?;
    if !a.construction().universe().contains(&anchor) {
        return Err("Observableのroot存在Atomが共通Uにない".into());
    }
    Ok((r, anchor))
}
fn compute(
    env: &Environment<'_>,
    g: &Graph,
    table: &Table,
    c: &mut Control,
) -> Result<Data, ValidationFailure> {
    tick(c)?;
    table.recheck(env, g, c)?;
    let diagrams = table.diagrams()?;
    let base = diagrams.first().ok_or("Observableのbase表示がない")?;
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
    g.expect(universe, &NodeType::Construction(T::AtomUniverse))?;
    let mut factors = vec![];
    for d in &diagrams {
        for &ring in &d.rings {
            tick(c)?;
            g.expect(ring, &NodeType::Construction(T::Ring))?;
            if !factors.contains(&ring) {
                factors.push(ring);
            }
        }
    }
    let mut objects = vec![];
    let mut complete = true;
    let mut types = vec![];
    let mut keys = None;
    for (object, (d, row)) in diagrams.iter().zip(&table.objects).enumerate() {
        tick(c)?;
        let mut coordinates = vec![];
        let mut object_keys = vec![];
        let mut refs = d
            .context
            .into_iter()
            .chain(d.presentations.iter().flatten().copied())
            .chain(d.rings.iter().copied())
            .chain(d.domains.iter().copied())
            .chain(d.bases.iter().copied())
            .chain(d.required.iter().copied())
            .chain(d.evaluations.iter().flatten().copied())
            .collect::<Vec<_>>();
        complete &= d.unavailable.is_none()
            && d.status == EquationPresentationStatus::Ready
            && d.presentations.len() == d.rings.len()
            && d.presentations.iter().all(Option::is_some);
        for q in &d.coordinates {
            tick(c)?;
            let original = d
                .originals
                .iter()
                .find(|o| o.reference == q.instance)
                .ok_or("Observableの元Law出現がない")?;
            if q.position.object != object
                || q.position.instance != original.instance
                || q.row != original.row
            {
                return Err("Observableの元対象/parameter行/出現が違う".into());
            }
            let index = base
                .originals
                .iter()
                .find(|o| o.row.is_none() && o.instance == original.instance)
                .ok_or("Observableの共通Law添字がない")?;
            if !table.indices.contains(&index.reference) {
                return Err("Observableの座標が共通Law表にない".into());
            }
            let factor = q
                .ring
                .map(|ring| {
                    factors
                        .iter()
                        .position(|r| *r == ring)
                        .ok_or("Observableの元環がfactorにない")
                })
                .transpose()?;
            if let Some(ring) = q.ring {
                if let Some((_, previous)) = types.iter().find(|(ty, _)| *ty == q.ty) {
                    if *previous != ring {
                        return Err("Observableの同型別共有環が対象間で違う".into());
                    }
                } else {
                    types.push((q.ty.clone(), ring));
                }
            }
            // 未生成の原式値を、対象外の既知residual零で埋めない。
            complete &= factor.is_some()
                && q.nu.is_some()
                && q.epsilon.is_some()
                && q.residual.is_some()
                && q.witness.is_some()
                && matches!(
                    q.status,
                    EquationPresentationStatus::Ready | EquationPresentationStatus::NotApplicable
                )
                && q.guard != EquationGuard::Undetermined;
            let canonical_row = if index.parameters.is_empty() {
                Some(0)
            } else {
                q.row
            };
            object_keys.push((
                original.instance,
                canonical_row,
                q.case,
                q.component.clone(),
                factor,
            ));
            refs.extend([q.instance, q.lhs, q.rhs]);
            refs.extend(q.ring);
            refs.extend(q.left);
            refs.extend(q.right);
            refs.extend(q.nu);
            refs.extend(q.epsilon);
            refs.extend(q.residual);
            refs.extend(q.witness);
            coordinates.push(Coordinate {
                index: index.reference,
                factor,
                source: q.clone(),
            });
        }
        if let Some(base_keys) = &keys {
            complete &= *base_keys == object_keys;
        } else {
            keys = Some(object_keys);
        }
        refs.sort_by_key(|r| r.0);
        refs.dedup();
        check_refs(env, g, refs, &mut support, &mut scope, &mut reasons, c)?;
        objects.push(Object {
            object: row.object,
            architecture: row.architecture,
            context: d.context,
            presentations: d.presentations.clone(),
            coordinates,
            unavailable: d.unavailable.clone(),
            status: d.status.clone(),
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
impl Layout {
    pub(super) fn recheck(
        &self,
        env: &Environment<'_>,
        g: &Graph,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        if self.data != compute(env, g, &self.table, c)? {
            return Err("Observableのfactor/全座標/由来/支持/Scope/完成状態が元計画と違う".into());
        }
        tick(c)
    }
    pub(super) fn checked<'a>(
        &'a self,
        env: &Environment<'_>,
        g: &'a Graph,
        c: &mut Control,
    ) -> Result<Checked<'a>, ValidationFailure> {
        self.recheck(env, g, c)?;
        let Some(Payload::Construction(v)) = &g.get(self.data.universe)?.payload else {
            return Err("Observableの共通Uがnativeでない".into());
        };
        let D::AtomUniverse(atoms) = &v.data else {
            return Err("Observableの共通Uが別構成".into());
        };
        Ok(Checked {
            data: &self.data,
            atoms,
        })
    }
}
impl Checked<'_> {
    pub(super) fn is_complete(&self) -> bool {
        self.data.complete
    }
    /// factor間の配置は単位的環準同型ではなく、block積内の座標の指定である。
    pub(super) fn at(
        &self,
        object: usize,
        coordinate: usize,
        reading: Reading,
        factor: usize,
        atom: &Fact,
        c: &mut Control,
    ) -> Result<Placed, ValidationFailure> {
        tick(c)?;
        let ring = *self
            .data
            .factors
            .get(factor)
            .ok_or("Observableのfactorが域外")?;
        let row = self
            .data
            .objects
            .get(object)
            .ok_or("Observableの対象が域外")?;
        let q = row
            .coordinates
            .get(coordinate)
            .ok_or("Observableの座標が域外")?;
        if !self.atoms.contains(atom) {
            return Err("ObservableのAtomが共通U外".into());
        }
        if atom != &self.data.anchor || q.factor.is_some_and(|f| f != factor) {
            return Ok(Placed::Zero { ring });
        }
        let value = match reading {
            Reading::Nu => q.source.nu,
            Reading::Epsilon => q.source.epsilon,
            Reading::Residual => q.source.residual,
        };
        Ok(match (q.factor, value) {
            (Some(_), Some(reference)) => Placed::Value { ring, reference },
            _ => Placed::Uncomputed { ring },
        })
    }
}
pub(super) fn retain(
    env: &Environment<'_>,
    g: &Graph,
    table: Arc<Table>,
    c: &mut Control,
) -> Result<Layout, ValidationFailure> {
    let data = compute(env, g, &table, c)?;
    tick(c)?;
    Ok(Layout { data, table })
}
#[cfg(test)]
#[path = "polynomial_observable_tests.rs"]
mod tests;
