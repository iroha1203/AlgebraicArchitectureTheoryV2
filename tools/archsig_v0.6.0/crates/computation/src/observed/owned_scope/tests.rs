use super::*;
use crate::observed::call::Context;
use archsig_common::{
    control::{Checkpoint, Control},
    types::Type,
};
use archsig_input::{law::ast::QuantKind, result::Signal};

fn descriptor(domain: Option<OwnedDomain>, context: Option<ActivationId>) -> OwnedQuantifier {
    OwnedQuantifier {
        kind: QuantKind::Forall,
        name: "x".into(),
        ty: Type::Bool,
        occurrence: (10, 20),
        domain,
        context,
        assembly_instance: None,
    }
}
fn recorded() -> Scope {
    let mut scope = Scope::from_quantifiers(vec![Quantifier {
        kind: QuantKind::Forall,
        name: "x".into(),
        ty: Type::Bool,
        occurrence: (10, 20),
        domain: Some(NodeRef(3)),
        context: Some(Context {
            iteration: Some(0),
            ..Context::default()
        }),
        assembly_instance: Some((NodeRef(7), 0)),
    }]);
    scope.readings.insert("reading".into());
    scope.snapshots.insert("snapshot".into());
    scope.modes.insert("finite".into());
    scope
}

#[test]
fn owned_scope_roundtrip_shares_metadata_and_preserves_recorded_wire() {
    let raw = recorded();
    let mut ids = Identities::default();
    let domain = ids
        .domain(&CapturedDomain::Finite(Arc::from([Scalar::Bool(true)])))
        .unwrap()
        .unwrap();
    let activation = ids.activation().unwrap();
    let producer = ids.producer().unwrap();
    let owned = raw
        .try_map_references::<InternalError, _, _, _>(
            |_| Ok(domain.clone()),
            |_| Ok(activation.clone()),
            |(_, index)| Ok((producer.clone(), *index)),
        )
        .unwrap();
    assert!(raw.shares_metadata(&owned));
    let mut retained = BodyScopeRetention::default();
    retained.retain(owned.clone());
    retained.retain(owned);
    assert!(raw.shares_metadata(retained.scope()));
    assert_eq!(retained.scope().quantifiers.len(), 1);
    let roundtrip = retained
        .scope()
        .try_map_references::<InternalError, _, _, _>(
            |_| Ok(NodeRef(3)),
            |_| {
                Ok(Context {
                    iteration: Some(0),
                    ..Context::default()
                })
            },
            |(_, index)| Ok((NodeRef(7), *index)),
        )
        .unwrap();
    assert_eq!(raw, roundtrip);
    assert_eq!(raw.wire(), roundtrip.wire());
    let mut changed = retained.into_scope();
    changed.readings.insert("other".into());
    assert!(!raw.readings.contains("other"));
    assert!(!raw.shares_metadata(&changed));
}

#[test]
fn owned_scope_fresh_domains_and_reused_members_keep_distinct_producer_identity() {
    let captured = CapturedDomain::Finite(Arc::from([Scalar::Bool(true)]));
    let mut ids = Identities::default();
    let first = ids.domain(&captured).unwrap().unwrap();
    let second = ids.domain(&captured).unwrap().unwrap();
    assert_ne!(first, second);
    assert_eq!(first, first.clone());
    let (Some(CapturedDomain::Finite(a)), Some(CapturedDomain::Finite(b))) =
        (first.captured(), second.captured())
    else {
        panic!()
    };
    assert!(Arc::ptr_eq(a, b));
    let member = first.member(0).unwrap();
    assert_eq!(member.producer(), first.member(0).unwrap().producer());
    assert_ne!(member.producer(), second.member(0).unwrap().producer());
    assert_ne!(member.producer(), ids.producer().unwrap());
    assert!(std::ptr::eq(member.value(), &a[0]));
    let activation = ids.activation().unwrap();
    let mut scope = OwnedScope::from_quantifiers(vec![descriptor(
        Some(first.clone()),
        Some(activation.clone()),
    )]);
    scope.add_quantifier(descriptor(Some(first), Some(activation.clone())));
    scope.add_quantifier(descriptor(Some(second), Some(activation)));
    assert_eq!(scope.quantifiers.len(), 2);
}

#[test]
fn owned_scope_unknown_and_known_empty_share_the_existing_placeholder_rule() {
    let mut ids = Identities::default();
    assert!(ids.domain(&CapturedDomain::Pending).unwrap().is_none());
    let empty = ids
        .domain(&CapturedDomain::Finite(Arc::from([])))
        .unwrap()
        .unwrap();
    assert!(empty.member(0).is_none());
    let activation = ids.activation().unwrap();
    let mut scope = OwnedScope::from_quantifiers(vec![descriptor(None, Some(activation.clone()))]);
    scope.add_quantifier(descriptor(Some(empty), Some(activation)));
    assert_eq!(scope.quantifiers.len(), 1);
    assert!(scope.quantifiers[0].domain.is_some());
    scope.add_quantifier(descriptor(None, Some(ids.activation().unwrap())));
    assert_eq!(scope.quantifiers.len(), 2);
}

#[test]
fn owned_scope_reused_scratch_context_does_not_collapse_unknown_body_domains() {
    let raw = Scope::from_quantifiers(vec![Quantifier {
        domain: None,
        assembly_instance: None,
        ..recorded().quantifiers[0].clone()
    }]);
    let mut ids = Identities::default();
    let mut retained = BodyScopeRetention::default();
    for _ in 0..2 {
        let activation = ids.activation().unwrap();
        let prepared = raw
            .try_map_references::<InternalError, _, _, _>(
                |_| unreachable!(),
                |_| Ok(activation.clone()),
                |_| unreachable!(),
            )
            .unwrap();
        retained.retain(prepared);
    }
    assert_eq!(retained.scope().quantifiers.len(), 2);
    assert_ne!(
        retained.scope().quantifiers[0].context,
        retained.scope().quantifiers[1].context
    );
    assert!(
        retained
            .scope()
            .source_compatible(&OwnedScope::from_quantifiers(vec![descriptor(None, None)]))
    );
    // A separate run cannot collide by resetting the local ordinal either.
    let mut independent = Identities::default();
    assert_ne!(
        retained.scope().quantifiers[0].context.clone().unwrap(),
        independent.activation().unwrap()
    );
}

#[test]
fn owned_scope_nested_domains_have_no_member_metadata_cycle() {
    let mut ids = Identities::default();
    let outer = ids
        .domain(&CapturedDomain::Finite(Arc::from([Scalar::Bool(true)])))
        .unwrap()
        .unwrap();
    let inner = ids
        .domain(&CapturedDomain::Finite(Arc::from([Scalar::Bool(false)])))
        .unwrap()
        .unwrap();
    let weak_outer = Arc::downgrade(&outer.0);
    let weak_inner = Arc::downgrade(&inner.0);
    let member = inner.member(0).unwrap();
    let mut scope = OwnedScope::from_quantifiers(vec![descriptor(
        Some(outer.clone()),
        Some(ids.activation().unwrap()),
    )]);
    let mut nested = descriptor(Some(inner.clone()), Some(ids.activation().unwrap()));
    nested.name = "y".into();
    nested.occurrence = (30, 40);
    scope.add_quantifier(nested);
    drop(outer);
    drop(inner);
    drop(scope);
    assert!(weak_outer.upgrade().is_none());
    assert!(weak_inner.upgrade().is_some());
    assert_eq!(member.value(), &Scalar::Bool(false));
    drop(member);
    assert!(weak_inner.upgrade().is_none());
}

#[test]
fn owned_scope_prepared_retention_needs_no_graph_or_control_after_commit() {
    let raw = recorded();
    let mut ids = Identities::default();
    let domain = ids.domain(&CapturedDomain::Type).unwrap().unwrap();
    let activation = ids.activation().unwrap();
    let producer = ids.producer().unwrap();
    let prepared = raw
        .try_map_references::<InternalError, _, _, _>(
            |_| Ok(domain.clone()),
            |_| Ok(activation.clone()),
            |_| Ok((producer.clone(), 0)),
        )
        .unwrap();
    drop(raw);
    drop(ids);
    drop(domain);
    let control = Control::new(|_| Some(Signal::Int));
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(Signal::Int));
    let mut retained = BodyScopeRetention::default();
    retained.retain(prepared);
    assert_eq!(retained.scope().quantifiers.len(), 1);
    assert!(retained.scope().readings.contains("reading"));
}

#[test]
fn owned_scope_recorded_domain_reuse_and_equal_fresh_domains_preserve_merge_identity() {
    use std::collections::BTreeMap;
    let mut raw = recorded();
    raw.quantifiers[0].assembly_instance = None;
    let mut fresh = raw.clone();
    fresh.quantifiers[0].domain = Some(NodeRef(4));
    let mut other_descriptor = raw.clone();
    other_descriptor.quantifiers[0].name = "y".into();
    other_descriptor.quantifiers[0].occurrence = (30, 40);
    let captured = CapturedDomain::Finite(Arc::from([Scalar::Bool(true)]));
    let mut ids = Identities::default();
    let activation = ids.activation().unwrap();
    // This fixture is the recording adapter's scoped correspondence table,
    // not the runtime Domain identity or a cache of mathematical evaluation.
    let mut origins = BTreeMap::<NodeRef, OwnedDomain>::new();
    let mut capture = |scope: &Scope| {
        scope
            .try_map_references::<InternalError, _, _, _>(
                |reference| {
                    if let Some(domain) = origins.get(reference) {
                        return Ok(domain.clone());
                    }
                    let domain = ids.domain(&captured)?.unwrap();
                    origins.insert(*reference, domain.clone());
                    Ok(domain)
                },
                |_| Ok(activation.clone()),
                |_| unreachable!(),
            )
            .unwrap()
    };
    let original = capture(&raw);
    let reused = capture(&raw);
    let distinct = capture(&fresh);
    let other = capture(&other_descriptor);
    assert_eq!(original, reused);
    assert_ne!(original, distinct);
    assert!(original.source_compatible(&distinct));
    assert_eq!(original.quantifiers[0].domain, other.quantifiers[0].domain);
    let mut retained = BodyScopeRetention::default();
    retained.retain(original);
    retained.retain(reused);
    assert_eq!(retained.scope().quantifiers.len(), 1);
    retained.retain(distinct);
    assert_eq!(retained.scope().quantifiers.len(), 2);
    retained.retain(other);
    assert_eq!(retained.scope().quantifiers.len(), 3);
    let mut recorded_merge = raw.clone();
    recorded_merge.merge(&raw);
    recorded_merge.merge(&fresh);
    recorded_merge.merge(&other_descriptor);
    assert_eq!(
        retained.scope().quantifiers.len(),
        recorded_merge.quantifiers.len()
    );
    assert_eq!(origins.len(), 2);
}
