//! Scope ownership at a retain/record boundary. No Graph, registry, or evaluator
//! is owned here. A retained execution supplies one identity source for its run.
use super::{environment::CapturedDomain, result::*};
use archsig_common::internal::InternalError;
use std::sync::Arc;

/// An execution token owns no values. Keeping it alive prevents identity reuse
/// even if an independent retained run starts its local counter at one again.
#[derive(Clone, Debug)]
pub(super) struct EventId {
    execution: Arc<()>,
    ordinal: u64,
}
impl PartialEq for EventId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.execution, &other.execution) && self.ordinal == other.ordinal
    }
}
impl Eq for EventId {}
impl PartialOrd for EventId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for EventId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (Arc::as_ptr(&self.execution) as usize, self.ordinal)
            .cmp(&(Arc::as_ptr(&other.execution) as usize, other.ordinal))
    }
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ActivationId(EventId);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct DomainId(EventId);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum ProducerId {
    Fresh(EventId),
    // Storage position in an immutable domain, not a displayed Set ordinal.
    Member(DomainId, usize),
}
#[derive(Default, Debug)]
pub(super) struct Identities {
    execution: Arc<()>,
    ordinal: u64,
}
impl Identities {
    fn next(&mut self) -> Result<EventId, InternalError> {
        self.ordinal = self
            .ordinal
            .checked_add(1)
            .ok_or_else(|| internal!("実行identityの上限"))?;
        Ok(EventId {
            execution: self.execution.clone(),
            ordinal: self.ordinal,
        })
    }
    pub fn activation(&mut self) -> Result<ActivationId, InternalError> {
        self.next().map(ActivationId)
    }
    pub fn producer(&mut self) -> Result<ProducerId, InternalError> {
        self.next().map(ProducerId::Fresh)
    }
    pub fn domain(
        &mut self,
        captured: &CapturedDomain,
    ) -> Result<Option<OwnedDomain>, InternalError> {
        if matches!(captured, CapturedDomain::Pending) {
            return Ok(None);
        }
        Ok(Some(OwnedDomain(Arc::new(DomainData {
            identity: DomainId(self.next()?),
            values: DomainValues::Captured(captured.clone()),
        }))))
    }
    /// Recorded ordinary members already own immutable Scalars. Moving those
    /// handles closes a finite domain without cloning any Scalar contents.
    pub fn shared_domain(
        &mut self,
        members: Vec<Arc<Scalar>>,
    ) -> Result<OwnedDomain, InternalError> {
        let identity = DomainId(self.next()?);
        let rows = members
            .into_iter()
            .enumerate()
            .map(|(position, scalar)| (ProducerId::Member(identity.clone(), position), scalar))
            .collect::<Vec<_>>();
        Ok(OwnedDomain(Arc::new(DomainData {
            identity,
            values: DomainValues::Shared(rows.into()),
        })))
    }
    pub fn recorded_domain(
        &mut self,
        members: Vec<(ProducerId, Arc<Scalar>)>,
    ) -> Result<OwnedDomain, InternalError> {
        Ok(OwnedDomain(Arc::new(DomainData {
            identity: DomainId(self.next()?),
            values: DomainValues::Shared(members.into()),
        })))
    }
}

/// Identity is an actual domain event. Equal/shared member storage is separate.
#[derive(Clone, Debug)]
pub(super) struct OwnedDomain(Arc<DomainData>);
#[derive(Debug)]
struct DomainData {
    identity: DomainId,
    values: DomainValues,
    // Deliberately no Scope/member metadata: a nested Scope cannot form an Arc
    // cycle by adding its domain descriptor to a member's binder Scope.
}
#[derive(Debug)]
enum DomainValues {
    Captured(CapturedDomain),
    Shared(Arc<[(ProducerId, Arc<Scalar>)]>),
}
impl PartialEq for OwnedDomain {
    fn eq(&self, other: &Self) -> bool {
        self.0.identity == other.0.identity
    }
}
impl Eq for OwnedDomain {}
impl OwnedDomain {
    pub fn identity(&self) -> DomainId {
        self.0.identity.clone()
    }
    pub fn captured(&self) -> Option<&CapturedDomain> {
        match &self.0.values {
            DomainValues::Captured(captured) => Some(captured),
            DomainValues::Shared(_) => None,
        }
    }
    pub fn len(&self) -> Option<usize> {
        match &self.0.values {
            DomainValues::Captured(CapturedDomain::Finite(members)) => Some(members.len()),
            DomainValues::Shared(members) => Some(members.len()),
            _ => None,
        }
    }
    pub fn member(&self, position: usize) -> Option<OwnedMember> {
        self.len()
            .filter(|len| position < *len)
            .map(|_| OwnedMember {
                domain: self.clone(),
                position,
            })
    }
}
#[derive(Clone, Debug)]
pub(super) struct OwnedMember {
    domain: OwnedDomain,
    position: usize,
}
impl OwnedMember {
    pub fn producer(&self) -> ProducerId {
        match &self.domain.0.values {
            DomainValues::Shared(members) => members[self.position].0.clone(),
            _ => ProducerId::Member(self.domain.identity(), self.position),
        }
    }
    pub fn shared_scalar(&self) -> Option<&Arc<Scalar>> {
        match &self.domain.0.values {
            DomainValues::Shared(members) => Some(&members[self.position].1),
            _ => None,
        }
    }
    pub fn value(&self) -> &Scalar {
        match &self.domain.0.values {
            DomainValues::Captured(CapturedDomain::Finite(members)) => &members[self.position],
            DomainValues::Shared(members) => members[self.position].1.as_ref(),
            _ => unreachable!("member is constructed only from a finite domain"),
        }
    }
}

pub(super) type OwnedScope = ScopeOf<OwnedDomain, ActivationId, (ProducerId, usize)>;
pub(super) type OwnedQuantifier = QuantifierOf<OwnedDomain, ActivationId, (ProducerId, usize)>;

/// Prepare reference conversion before a commit; merge this prepared value in
/// the existing retained callback. retain() needs no Control or Graph read and
/// can preserve already committed observations when a subsequent checkpoint stops.
#[derive(Clone, Debug, Default)]
pub(super) struct BodyScopeRetention {
    scope: OwnedScope,
}
impl BodyScopeRetention {
    pub fn retain(&mut self, prepared: OwnedScope) {
        self.scope.merge(&prepared);
    }
    pub fn scope(&self) -> &OwnedScope {
        &self.scope
    }
    pub fn into_scope(self) -> OwnedScope {
        self.scope
    }
}

#[cfg(test)]
mod tests;
