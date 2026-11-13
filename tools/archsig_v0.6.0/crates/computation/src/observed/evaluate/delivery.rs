//! Root quantifier delivery consumes the ordinary evaluator's completed body.
//! Normal delivery retains canonical reasons, Scope and selected counterexamples.
//! Raw source/evaluation/evidence Nodes never serve as successful receipts; their
//! native/$answer/needed consumers keep the full observation route.
use super::*;
use crate::observed::owned_scope::{
    ActivationId, BodyScopeRetention, Identities, OwnedDomain, OwnedScope, ProducerId,
};
use std::sync::Arc;

pub(in crate::observed) type OwnedReason = ReasonOf<ProducerId>;

#[derive(Clone, Debug)]
pub(in crate::observed) struct OwnedValue {
    pub producer: ProducerId,
    pub scalar: Arc<Scalar>,
}
/// Sealed by the evaluator only after the root loop and original bindings have
/// completed. This contains values for projection, never a raw proof receipt.
#[derive(Clone, Debug)]
pub(in crate::observed) struct ClosedAnswer {
    pub id: String,
    pub status: Decision,
    pub value: Option<OwnedValue>,
    pub applicability: &'static str,
    pub scope: OwnedScope,
    pub reasons: Vec<OwnedReason>,
    pub counterexamples: Vec<Counterexample>,
}

#[derive(Clone, Debug)]
pub(in crate::observed) struct OwnedBinding {
    pub name: String,
    pub value: OwnedValue,
}
#[derive(Clone, Debug)]
pub(in crate::observed) struct Counterexample {
    pub bindings: Vec<OwnedBinding>,
    pub left: OwnedValue,
    pub right: OwnedValue,
    pub facts: Vec<Fact>,
    pub operator: Option<BinOp>,
}

/// Actual completed body data, rather than a Graph certification tag.
#[derive(Clone, Debug)]
pub(super) struct ClosedBody {
    pub truth: Option<bool>,
    pub failed: bool,
    pub pending: bool,
    pub scope: OwnedScope,
    pub support: Support,
    pub reasons: Vec<OwnedReason>,
    pub counterexamples: Vec<Counterexample>,
}

/// A conservative first route: the decision is made for the whole batch before
/// evaluating any body. Other request consumers keep the existing full API.
pub(in crate::observed) fn closed_roots_eligible(prepared: &PreparedObserved) -> bool {
    use archsig_input::law::ast::{QuantDomain, QuantSplit};
    if prepared.object.is_some()
        || prepared.requests().requests().is_empty()
        || prepared
            .inputs()
            .archmap()
            .snapshots()
            .iter()
            .flat_map(|s| &s.subjects)
            .flat_map(|s| &s.fields)
            .any(|field| !matches!(field.slot, Slot::Known { .. }))
    {
        return false;
    }
    let law = prepared.inputs().law();
    for request in prepared.requests().requests() {
        if !matches!(request.kind, QuestionKind::Check | QuestionKind::Evaluate)
            || !request.dependencies.is_empty()
            || request
                .constraints
                .iter()
                .any(|constraint| constraint.dynamic)
            || request.arguments.iter().any(|argument| {
                !argument.name.starts_with("bind.")
                    || !matches!(argument.value, Selector::Subject { .. })
            })
        {
            return false;
        }
        let Some(name) = request.declaration() else {
            return false;
        };
        let declaration = &law.declarations()[name];
        let (params, body) = match &declaration.signature {
            Signature::View { params, body, .. }
            | Signature::Law {
                params,
                guard: None,
                body,
                ..
            } => (params, *body),
            _ => return false,
        };
        if params.len() != request.arguments.len() {
            return false;
        }
        let ExprKind::Quant {
            split:
                QuantSplit::Fixed {
                    domain: QuantDomain::In(domain),
                    body,
                },
            ..
        } = &law.exprs()[body].kind
        else {
            return false;
        };
        let Some(Type::List(element) | Type::Set(element)) = law.expr_type(*domain) else {
            return false;
        };
        if !matches!(
            element.as_ref(),
            Type::Unit
                | Type::Text
                | Type::Bool
                | Type::Z
                | Type::Q
                | Type::Fp(_)
                | Type::Ref(_)
                | Type::Data(_)
        ) {
            return false;
        }
        let mut pending = vec![*domain, *body];
        while let Some(id) = pending.pop() {
            // Path/Term wire projection needs native owners. Plain data and
            // typed Map application have self-owned Scalar payloads.
            let mut types = vec![law.expr_type(id).expect("checked expression type")];
            while let Some(ty) = types.pop() {
                match ty {
                    Type::Path(..) | Type::Term(..) => return false,
                    Type::Tuple(items) => types.extend(items),
                    Type::List(item) | Type::Set(item) | Type::Option(item) => types.push(item),
                    Type::Map(domain, codomain) => {
                        types.push(domain);
                        types.push(codomain);
                    }
                    _ => {}
                }
            }
            match &law.exprs()[id].kind {
                ExprKind::Int(_)
                | ExprKind::Bool(_)
                | ExprKind::Str(_)
                | ExprKind::Unit
                | ExprKind::Dotted(_)
                | ExprKind::None(_) => {}
                ExprKind::Group(child) | ExprKind::Some(child) => pending.push(*child),
                ExprKind::Unary { operand, .. } => pending.push(*operand),
                ExprKind::Binary { lhs, rhs, .. } => pending.extend([*lhs, *rhs]),
                ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => pending.push(*base),
                ExprKind::Family { owner, .. } => pending.push(*owner),
                ExprKind::Let { value, body, .. } => pending.extend([*value, *body]),
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => pending.extend([*cond, *then_branch, *else_branch]),
                ExprKind::ListLit { items, .. }
                | ExprKind::SetLit { items, .. }
                | ExprKind::Tuple(items) => pending.extend(items),
                ExprKind::Call { callee, args }
                    if args.len() == 1 && matches!(law.expr_type(*callee), Some(Type::Map(..))) =>
                {
                    pending.extend([*callee, args[0]]);
                }
                // Named/native calls, free axes and nested quantifiers retain
                // their full route until their own consumers are connected.
                _ => return false,
            }
        }
    }
    true
}

/// Execute the admitted requests with the same Evaluator and body reducer.
/// Each completed root owns its delivery data; the next root gets a fresh
/// recording Graph. Only an unfinished current root can escape as a raw tail.
pub(in crate::observed) fn evaluate_closed_roots(
    prepared: PreparedObserved,
    control: &Control,
) -> ClosedRun {
    evaluate_closed_roots_with_check(prepared, control, |_| Ok(()))
}
// Like the raw runner's rejecting validator callback, this can reject a
// completed root before commit; it cannot supply or change a successful result.
pub(super) fn evaluate_closed_roots_with_check(
    prepared: PreparedObserved,
    control: &Control,
    mut after_root: impl FnMut(&Request) -> Result<(), InternalError>,
) -> ClosedRun {
    let mut answers: Vec<Option<DeliveryAnswer>> = std::iter::repeat_with(|| None)
        .take(prepared.requests().requests().len())
        .collect();
    let mut issues = Vec::new();
    let mut tail = None;
    let mut internal = false;
    let mut has_nodes = false;
    let mut not_implemented = None;
    {
        let environment = Environment::with_prepared(&prepared, control).ok();
        for &index in prepared.requests().evaluation_order() {
            let request = &prepared.requests().requests()[index];
            let declaration = &prepared.inputs().law().declarations()
                [request.declaration().expect("admitted declaration")];
            let mut base = Scope::default();
            base.readings.insert(declaration.reading.clone());
            if let Some(signal) = control.stop_reason() {
                let reason = Reason::stopped(&request.id, signal);
                issues.push(DeliveryReason::Recorded(reason.clone()));
                answers[index] = Some(DeliveryAnswer::Recorded(Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons: vec![reason],
                    scope: base,
                }));
                continue;
            }
            if internal {
                let reason =
                    Reason::internal(&request.id, "previous derivation verification".into());
                issues.push(DeliveryReason::Recorded(reason.clone()));
                answers[index] = Some(DeliveryAnswer::Recorded(Answer {
                    id: request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons: vec![reason],
                    scope: Scope::default(),
                }));
                continue;
            }
            let environment = environment
                .as_ref()
                .expect("unstopped environment construction");
            let mut graph = Graph::new(control);
            graph.requests = prepared.requests().requests().to_vec();
            graph.active.request = index;
            let (_architecture, architecture_failure) = match environment.enter_architecture(&graph)
            {
                Ok(guard) => (Some(guard), None),
                Err(failure) => (None, Some(failure)),
            };
            environment.state.merge_architecture_scope(&mut base);
            let (params, guard, body) = match &declaration.signature {
                Signature::View { params, body, .. } => (params, None, *body),
                Signature::Law {
                    params,
                    guard,
                    body,
                    ..
                } => (params, *guard, *body),
                _ => unreachable!("admitted declaration signature"),
            };
            let mut evaluator = Evaluator {
                environment,
                graph: &mut graph,
                control,
                request,
                declaration,
                bindings: vec![],
                lexical: BTreeMap::new(),
                formal: BTreeMap::new(),
                base,
                retained_scope: Scope::default(),
                reasons: vec![],
                completed: BTreeMap::new(),
                answer_evaluation: None,
                verified_observed: None,
                completing: false,
                finite_universal: None,
                sources: BTreeMap::new(),
            };
            let mut progress = RootProgress::default();
            let result = (|| {
                if let Some(failure) = architecture_failure {
                    return Err(failure.into());
                }
                evaluator.tick(Checkpoint::FiniteIteration)?;
                evaluator.projection_conditions()?;
                evaluator.bind(params)?;
                if !evaluator.closed_root_eligible(body, guard)? || evaluator.is_family(params) {
                    return Err(internal!("静的閉包admissionと実root contextが一致しない").into());
                }
                evaluator.closed_root_answer(params, body, &mut progress)
            })();
            let result = result.and_then(|answer| {
                after_root(request).map_err(Failure::Internal)?;
                Ok(answer)
            });
            match result {
                Ok(answer) => {
                    has_nodes |= !evaluator.graph.nodes.is_empty();
                    issues.extend(answer.reasons.iter().cloned().map(DeliveryReason::Closed));
                    answers[index] = Some(DeliveryAnswer::Closed(answer));
                    #[cfg(test)]
                    data::observe_actual(
                        declaration.span,
                        evaluator.graph.active,
                        "delivery_answer_committed",
                        index,
                    );
                    if let Err(Failure::Stop(signal)) = evaluator.tick(Checkpoint::FiniteIteration)
                    {
                        issues.push(DeliveryReason::Recorded(Reason::stopped(
                            &request.id,
                            signal,
                        )));
                    }
                }
                Err(failure) => {
                    let stopped = matches!(failure, Failure::Stop(_));
                    let reason = match failure {
                        Failure::Stop(signal) => Reason::stopped(&request.id, signal),
                        Failure::NotImplemented { location, feature } => {
                            not_implemented = Some((declaration.name.clone(), location, feature));
                            internal = true;
                            Reason::internal(
                                &request.id,
                                format!("{} evaluation", request.kind.wire()),
                            )
                        }
                        Failure::Internal(_) => {
                            internal = true;
                            Reason::internal(
                                &request.id,
                                format!("{} evaluation", request.kind.wire()),
                            )
                        }
                    };
                    if stopped {
                        has_nodes |= !evaluator.graph.nodes.is_empty();
                        let mut reasons = evaluator.reasons.clone();
                        reasons.push(reason);
                        sort_reasons(&mut reasons);
                        let mut scope = evaluator.base.clone();
                        scope.merge(&evaluator.retained_scope);
                        let retained = progress.into_retained();
                        issues.extend(retained.reasons.iter().cloned().map(DeliveryReason::Closed));
                        issues.extend(reasons.iter().cloned().map(DeliveryReason::Recorded));
                        answers[index] = Some(DeliveryAnswer::Recorded(Answer {
                            id: request.id.clone(),
                            status: Decision::Undetermined,
                            outputs: BTreeMap::new(),
                            claim: None,
                            evidence: vec![],
                            reasons,
                            scope,
                        }));
                        drop(evaluator);
                        tail = Some(RecordedTail {
                            graph,
                            request_index: index,
                            retained,
                        });
                    } else {
                        // Match the raw failure contract: unverified current
                        // outputs/metadata cannot qualify the saved prefix.
                        issues.push(DeliveryReason::Recorded(reason.clone()));
                        answers[index] = Some(DeliveryAnswer::Recorded(Answer {
                            id: request.id.clone(),
                            status: Decision::Undetermined,
                            outputs: BTreeMap::new(),
                            claim: None,
                            evidence: vec![],
                            reasons: vec![reason],
                            scope: Scope::default(),
                        }));
                    }
                }
            }
        }
    }
    let answers: Vec<_> = answers
        .into_iter()
        .map(|answer| answer.expect("complete request order"))
        .collect();
    let partial = answers.iter().any(|answer| match answer {
        DeliveryAnswer::Closed(answer) => answer.status == Decision::Undetermined,
        DeliveryAnswer::Recorded(answer) => answer.status == Decision::Undetermined,
    });
    let status = if control.stop_reason().is_some() {
        "interrupted"
    } else if internal || not_implemented.is_some() {
        "error"
    } else if partial {
        "partial"
    } else {
        "complete"
    };
    ClosedRun {
        prepared,
        answers,
        issues,
        status,
        tail,
        internal,
        has_nodes,
        not_implemented,
    }
}

#[derive(Debug)]
pub(in crate::observed) struct ClosedRun {
    pub prepared: PreparedObserved,
    pub answers: Vec<DeliveryAnswer>,
    pub issues: Vec<DeliveryReason>,
    pub status: &'static str,
    pub tail: Option<RecordedTail>,
    pub internal: bool,
    pub has_nodes: bool,
    pub not_implemented: Option<(String, Location, String)>,
}
#[derive(Debug)]
pub(in crate::observed) enum DeliveryAnswer {
    Closed(ClosedAnswer),
    Recorded(Answer),
}
#[derive(Clone, Debug)]
pub(in crate::observed) enum DeliveryReason {
    Closed(OwnedReason),
    Recorded(Reason),
}
#[derive(Debug)]
pub(in crate::observed) struct RecordedTail {
    pub graph: Graph,
    pub request_index: usize,
    pub retained: RetainedRoot,
}
#[derive(Debug, Default)]
pub(in crate::observed) struct RetainedRoot {
    pub scope: OwnedScope,
    pub reasons: Vec<OwnedReason>,
    pub value: Option<OwnedValue>,
    pub root_complete: bool,
    pub references: RegionReferences,
}

/// The caller keeps this across errors: sealed prior bodies and the stable
/// identities used by the current recorded tail survive a stopped root.
#[derive(Default, Debug)]
pub(super) struct RootProgress {
    pub fold: QuantifierFold,
    pub ownership: Option<RegionOwnership>,
    pub closed_body: Option<ClosedBody>,
    pub root_value: Option<OwnedValue>,
}
impl RootProgress {
    /// Transfer already owned observations only. This is safe after Control
    /// freezes and deliberately performs no Graph read or semantic analysis.
    pub fn into_retained(self) -> RetainedRoot {
        let mut scope = self.fold.retained.into_scope();
        let mut reasons = self.fold.committed_reasons;
        reasons.extend(self.fold.reasons);
        let root_complete = self.closed_body.is_some();
        if let Some(body) = self.closed_body {
            scope.merge(&body.scope);
            reasons.extend(body.reasons);
        }
        RetainedRoot {
            scope,
            reasons,
            value: self.root_value,
            root_complete,
            references: self
                .ownership
                .map(RegionOwnership::into_references)
                .unwrap_or_default(),
        }
    }
    #[cfg(test)]
    pub fn completed_len(&self) -> usize {
        self.fold.completed_len()
    }
}

/// The existing loop supplies every result, including bodies after a decisive
/// Forall false / Exists true. Truth reduction remains quantifier::reduce.
#[derive(Default, Debug)]
pub(super) struct QuantifierFold {
    results: Vec<Option<bool>>,
    failed: bool,
    pending: bool,
    retained: BodyScopeRetention,
    factors: Vec<Support>,
    committed_reasons: Vec<OwnedReason>,
    reasons: Vec<OwnedReason>,
    counterexamples: Vec<Counterexample>,
}
impl QuantifierFold {
    #[cfg(test)]
    pub fn completed_len(&self) -> usize {
        self.results.len()
    }
    pub fn observe_condition(&mut self, failed: bool, pending: bool) {
        self.failed |= failed;
        self.pending |= pending;
    }
    pub fn retain_committed(&mut self, scope: OwnedScope, reasons: Vec<OwnedReason>) {
        self.retained.retain(scope);
        self.committed_reasons.extend(reasons);
    }
    pub fn retain_root(&mut self, scope: OwnedScope, support: Support, reasons: Vec<OwnedReason>) {
        self.retained.retain(scope);
        self.factors.push(support);
        self.reasons.extend(reasons);
    }
    pub fn consume(&mut self, body: ClosedBody) {
        self.results.push(body.truth);
        self.failed |= body.failed;
        self.pending |= body.pending;
        self.retained.retain(body.scope);
        self.factors.push(body.support);
        self.reasons.extend(body.reasons);
        self.counterexamples.extend(body.counterexamples);
    }
    pub fn finish(
        self,
        kind: archsig_input::law::ast::QuantKind,
        finite: bool,
        control: &Control,
    ) -> Result<ClosedBody, ValidationFailure> {
        let truth = self.truth(kind, finite, control)?;
        Ok(self.seal(truth))
    }
    pub fn truth(
        &self,
        kind: archsig_input::law::ast::QuantKind,
        finite: bool,
        control: &Control,
    ) -> Result<Option<bool>, ValidationFailure> {
        if finite && !self.failed && !self.pending {
            crate::observed::quantifier::reduce(kind, &self.results, control)
        } else {
            Ok(None)
        }
    }
    pub fn seal(self, truth: Option<bool>) -> ClosedBody {
        ClosedBody {
            truth,
            failed: self.failed,
            pending: self.pending,
            scope: self.retained.into_scope(),
            support: Support::sum(vec![], self.factors),
            reasons: self.reasons,
            counterexamples: self.counterexamples,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_input::law::ast::QuantKind;
    use std::{cell::Cell, rc::Rc};

    fn value(value: Arc<Scalar>) -> Node {
        Node {
            ty: NodeType::Value(value.ty()),
            payload: Some(Payload::scalar(value)),
            rule: Rule::Construction("evaluation"),
            arguments: vec![],
            support: Support::default(),
            scope: Scope::default(),
            evidence: vec![],
            judgment: None,
            reasons: vec![],
        }
    }
    fn body(truth: Option<bool>, pending: bool, failed: bool) -> ClosedBody {
        ClosedBody {
            truth,
            pending,
            failed,
            scope: OwnedScope::default(),
            support: Support::default(),
            reasons: vec![],
            counterexamples: vec![],
        }
    }
    #[test]
    fn delivery_body_fold_consumes_every_result_and_preserves_pending_failed_and_empty() {
        let control = Control::unlimited();
        let mut fold = QuantifierFold::default();
        fold.consume(body(Some(false), false, false));
        fold.consume(body(Some(true), true, false));
        assert_eq!(fold.results.len(), 2);
        let result = fold.finish(QuantKind::Forall, true, &control).unwrap();
        assert_eq!(result.truth, None);
        assert!(result.pending);
        let mut fold = QuantifierFold::default();
        fold.consume(body(Some(true), false, false));
        fold.consume(body(Some(false), false, true));
        assert_eq!(fold.results.len(), 2);
        let result = fold.finish(QuantKind::Exists, true, &control).unwrap();
        assert_eq!(result.truth, None);
        assert!(result.failed);
        assert_eq!(
            QuantifierFold::default()
                .finish(QuantKind::Forall, true, &control)
                .unwrap()
                .truth,
            Some(true)
        );
        assert_eq!(
            QuantifierFold::default()
                .finish(QuantKind::Exists, true, &control)
                .unwrap()
                .truth,
            Some(false)
        );
        assert_eq!(
            QuantifierFold::default()
                .finish(QuantKind::Forall, false, &control)
                .unwrap()
                .truth,
            None
        );
    }
    #[test]
    fn delivery_discarded_body_releases_graph_values_and_reuses_only_scratch_indices() {
        let mut graph = Graph::new(&Control::unlimited());
        let root = graph.push(value(Arc::new(Scalar::Bool(false)))).unwrap();
        let prefix = graph.suffix_checkpoint();
        let identity = graph.nodes.prefix_identity();
        let mut fold = QuantifierFold::default();
        for _ in 0..3 {
            let scalar = Arc::new(Scalar::Bool(true));
            let weak = Arc::downgrade(&scalar);
            let reference = graph.push(value(scalar)).unwrap();
            assert_eq!(reference.0, prefix.node_len());
            let truth = graph.boolean(Some(reference)).unwrap();
            fold.consume(body(truth, false, false));
            graph.discard_suffix(&prefix).unwrap();
            assert!(
                weak.upgrade().is_none(),
                "closed truth must not own its body Graph"
            );
            assert!(Rc::ptr_eq(&identity, &graph.nodes.prefix_identity()));
            assert_eq!(graph.boolean(Some(root)).unwrap(), Some(false));
        }
        assert_eq!(fold.results.len(), 3);
        assert_eq!(
            fold.finish(QuantKind::Forall, true, &Control::unlimited())
                .unwrap()
                .truth,
            Some(true)
        );
    }
    #[test]
    fn delivery_shared_domain_keeps_only_required_members_after_body_graph_release() {
        let mut graph = Graph::new(&Control::unlimited());
        let prefix = graph.suffix_checkpoint();
        let member = Arc::new(Scalar::Bool(true));
        let required = Arc::downgrade(&member);
        let temporary = Arc::new(Scalar::Bool(false));
        let discarded = Arc::downgrade(&temporary);
        let reference = graph.push(value(member.clone())).unwrap();
        graph.push(value(temporary)).unwrap();
        let mut identities = Identities::default();
        let domain = identities.shared_domain(vec![member]).unwrap();
        let owned = domain.member(0).unwrap();
        graph.discard_suffix(&prefix).unwrap();
        assert!(discarded.upgrade().is_none());
        assert!(required.upgrade().is_some());
        assert_eq!(owned.value(), &Scalar::Bool(true));
        assert!(graph.get(reference).is_err());
        drop(owned);
        drop(domain);
        assert!(required.upgrade().is_none());
    }
    #[test]
    fn delivery_suffix_rejects_changed_prefix_without_dropping_the_body() {
        let mut graph = Graph::new(&Control::unlimited());
        graph.push(value(Arc::new(Scalar::Bool(false)))).unwrap();
        let prefix = graph.suffix_checkpoint();
        graph.push(value(Arc::new(Scalar::Bool(true)))).unwrap();
        graph.nodes[0].scope.modes.insert("changed".into());
        assert!(graph.discard_suffix(&prefix).is_err());
        assert_eq!(graph.nodes.len(), 2);
    }
    #[test]
    fn delivery_suffix_cleanup_after_stop_never_reenters_control() {
        let stopped = Rc::new(Cell::new(false));
        let calls = Rc::new(Cell::new(0));
        let seen = calls.clone();
        let armed = stopped.clone();
        let control = Control::new(move |_| {
            seen.set(seen.get() + 1);
            armed.get().then_some(Signal::Int)
        });
        let mut graph = Graph::new(&control);
        let prefix = graph.suffix_checkpoint();
        graph.push(value(Arc::new(Scalar::Bool(true)))).unwrap();
        stopped.set(true);
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(Signal::Int));
        let before = calls.get();
        graph.discard_suffix(&prefix).unwrap();
        assert_eq!(calls.get(), before);
        assert!(graph.nodes.is_empty());
    }
}

/// Pure reference conversion for the current recorded tail after Stop.
#[derive(Debug, Default)]
pub(in crate::observed) struct RegionReferences {
    domains: BTreeMap<NodeRef, OwnedDomain>,
    contexts: BTreeMap<crate::observed::call::Context, ActivationId>,
    producers: BTreeMap<NodeRef, ProducerId>,
}
impl RegionReferences {
    pub fn map_scope(&self, scope: &Scope) -> Result<OwnedScope, InternalError> {
        scope.try_map_references(
            |domain| {
                self.domains
                    .get(domain)
                    .cloned()
                    .ok_or_else(|| internal!("保持ScopeのDomain対応がない"))
            },
            |context| {
                self.contexts
                    .get(context)
                    .cloned()
                    .ok_or_else(|| internal!("保持ScopeのContext対応がない"))
            },
            |(source, index)| {
                self.producers
                    .get(source)
                    .cloned()
                    .map(|source| (source, *index))
                    .ok_or_else(|| internal!("保持Scopeのproducer対応がない"))
            },
        )
    }
}

/// Root-fixed references are shared across bodies. Scratch correspondences are
/// discarded after a successful closure, so reused raw indices never become
/// runtime identities and this is not a cache of evaluated expressions.
#[derive(Debug)]
pub(super) struct RegionOwnership {
    identities: Identities,
    node_cutoff: usize,
    context_limits: [usize; 4],
    prefix_domains: BTreeMap<NodeRef, OwnedDomain>,
    body_domains: BTreeMap<NodeRef, OwnedDomain>,
    prefix_contexts: BTreeMap<crate::observed::call::Context, ActivationId>,
    body_contexts: BTreeMap<crate::observed::call::Context, ActivationId>,
    prefix_producers: BTreeMap<NodeRef, ProducerId>,
    body_producers: BTreeMap<NodeRef, ProducerId>,
}
impl RegionOwnership {
    fn into_references(mut self) -> RegionReferences {
        self.prefix_domains.extend(self.body_domains);
        self.prefix_contexts.extend(self.body_contexts);
        self.prefix_producers.extend(self.body_producers);
        RegionReferences {
            domains: self.prefix_domains,
            contexts: self.prefix_contexts,
            producers: self.prefix_producers,
        }
    }
    pub(super) fn new(prefix: &GraphSuffixCheckpoint) -> Self {
        Self {
            identities: Identities::default(),
            node_cutoff: prefix.node_len(),
            context_limits: prefix.context_limits(),
            prefix_domains: BTreeMap::new(),
            body_domains: BTreeMap::new(),
            prefix_contexts: BTreeMap::new(),
            body_contexts: BTreeMap::new(),
            prefix_producers: BTreeMap::new(),
            body_producers: BTreeMap::new(),
        }
    }
    pub(super) fn begin_body(&mut self) {
        self.body_domains.clear();
        self.body_contexts.clear();
        self.body_producers.clear();
    }
    fn prefix_context(&self, context: crate::observed::call::Context) -> bool {
        [
            context.frame,
            context.iteration,
            context.instance,
            context.case,
        ]
        .into_iter()
        .zip(self.context_limits)
        .all(|(index, limit)| index.is_none_or(|i| i < limit))
    }
    fn producer(&mut self, reference: NodeRef) -> Result<ProducerId, InternalError> {
        let table = if reference.0 < self.node_cutoff {
            &mut self.prefix_producers
        } else {
            &mut self.body_producers
        };
        if let Some(identity) = table.get(&reference) {
            return Ok(identity.clone());
        }
        let identity = self.identities.producer()?;
        table.insert(reference, identity.clone());
        Ok(identity)
    }
    fn context(
        &mut self,
        context: crate::observed::call::Context,
    ) -> Result<ActivationId, InternalError> {
        let table = if self.prefix_context(context) {
            &mut self.prefix_contexts
        } else {
            &mut self.body_contexts
        };
        if let Some(identity) = table.get(&context) {
            return Ok(identity.clone());
        }
        let identity = self.identities.activation()?;
        table.insert(context, identity.clone());
        Ok(identity)
    }
    pub(super) fn fresh_value(&mut self, scalar: Scalar) -> Result<OwnedValue, InternalError> {
        Ok(OwnedValue {
            producer: self.identities.producer()?,
            scalar: Arc::new(scalar),
        })
    }
    fn value(&mut self, graph: &Graph, reference: NodeRef) -> Result<OwnedValue, InternalError> {
        let scalar = match &graph.get(reference)?.payload {
            Some(Payload::Scalar(scalar)) => scalar.clone(),
            // Native projections own Scalar data too. Only a selected value is
            // copied here; a Scalar never owns an entire native/body Graph.
            _ => Arc::new(graph.scalar(reference)?.clone()),
        };
        Ok(OwnedValue {
            producer: self.producer(reference)?,
            scalar,
        })
    }
    pub(super) fn domain(
        &mut self,
        graph: &Graph,
        reference: NodeRef,
    ) -> Result<OwnedDomain, InternalError> {
        let previous = if reference.0 < self.node_cutoff {
            self.prefix_domains.get(&reference)
        } else {
            self.body_domains.get(&reference)
        };
        if let Some(domain) = previous {
            return Ok(domain.clone());
        }
        let domain = match &graph.get(reference)?.payload {
            Some(Payload::TypeDomain { .. }) => self
                .identities
                .domain(&crate::observed::environment::CapturedDomain::Type)?
                .ok_or(internal!("型Domainの所有結果がない"))?,
            Some(Payload::Domain { elements, .. }) => {
                let mut members = Vec::with_capacity(elements.len());
                for element in elements {
                    let value = self.value(graph, *element)?;
                    members.push((value.producer, value.scalar));
                }
                self.identities.recorded_domain(members)?
            }
            _ => return Err(internal!("native Domainにはfull consumerが必要")),
        };
        if reference.0 < self.node_cutoff {
            self.prefix_domains.insert(reference, domain.clone());
        } else {
            self.body_domains.insert(reference, domain.clone());
        }
        Ok(domain)
    }
    pub(super) fn scope(
        &mut self,
        graph: &Graph,
        scope: &Scope,
    ) -> Result<OwnedScope, InternalError> {
        for quantifier in &scope.quantifiers {
            if let Some(domain) = quantifier.domain {
                self.domain(graph, domain)?;
            }
            if let Some(context) = quantifier.context {
                self.context(context)?;
            }
            if let Some((source, _)) = quantifier.assembly_instance {
                self.producer(source)?;
            }
        }
        scope.try_map_references(
            |domain| {
                (if domain.0 < self.node_cutoff {
                    self.prefix_domains.get(domain)
                } else {
                    self.body_domains.get(domain)
                })
                .cloned()
                .ok_or_else(|| internal!("所有Domain対応がない"))
            },
            |context| {
                (if self.prefix_context(*context) {
                    self.prefix_contexts.get(context)
                } else {
                    self.body_contexts.get(context)
                })
                .cloned()
                .ok_or_else(|| internal!("所有Context対応がない"))
            },
            |(source, index)| {
                (if source.0 < self.node_cutoff {
                    self.prefix_producers.get(source)
                } else {
                    self.body_producers.get(source)
                })
                .cloned()
                .map(|producer| (producer, *index))
                .ok_or_else(|| internal!("所有Scope producer対応がない"))
            },
        )
    }
    pub(super) fn reason(&mut self, reason: &Reason) -> Result<OwnedReason, InternalError> {
        let kind = match &reason.kind {
            ReasonKind::Missing => ReasonKindOf::Missing,
            ReasonKind::VisibilityInsufficient {
                locals,
                coordinates,
            } => ReasonKindOf::VisibilityInsufficient {
                locals: locals.clone(),
                coordinates: coordinates
                    .iter()
                    .map(|r| self.producer(*r))
                    .collect::<Result<_, _>>()?,
            },
            ReasonKind::DependencyBlocked { request } => ReasonKindOf::DependencyBlocked {
                request: request.clone(),
            },
            ReasonKind::ConditionFailed {
                condition,
                construction,
            } => ReasonKindOf::ConditionFailed {
                condition: self.producer(*condition)?,
                construction,
            },
            ReasonKind::UnsupportedAlgorithm {
                question,
                operand_types,
                method,
            } => ReasonKindOf::UnsupportedAlgorithm {
                question: *question,
                operand_types: operand_types.clone(),
                method: method.clone(),
            },
            ReasonKind::Stop(signal) => ReasonKindOf::Stop(signal.clone()),
            ReasonKind::Internal(message) => ReasonKindOf::Internal(message.clone()),
        };
        Ok(ReasonOf {
            kind,
            request: reason.request.clone(),
            dependencies: reason
                .dependencies
                .iter()
                .map(|r| self.producer(*r))
                .collect::<Result<_, _>>()?,
            missing: reason.missing.clone(),
            location: reason.location.clone(),
        })
    }
    fn counterexample(
        &mut self,
        graph: &Graph,
        reference: NodeRef,
    ) -> Result<Counterexample, InternalError> {
        let Some(Payload::Counterexample {
            bindings,
            left,
            right,
            facts,
        }) = &graph.get(reference)?.payload
        else {
            return Err(internal!("閉包対象がCounterexampleでない"));
        };
        Ok(Counterexample {
            bindings: bindings
                .iter()
                .map(|b| self.binding(graph, b))
                .collect::<Result<_, _>>()?,
            left: self.value(graph, *left)?,
            right: self.value(graph, *right)?,
            facts: facts.clone(),
            // This closure is used for the root quantifier's own evidence. Its
            // source is Quant, never the guardless binary Law summary operator.
            operator: None,
        })
    }
    pub(super) fn close_body(
        &mut self,
        environment: &Environment<'_>,
        graph: &Graph,
        body: &Evaluated,
        evidence: &[NodeRef],
    ) -> Result<ClosedBody, ValidationFailure> {
        let pending = environment.evaluation_condition_pending(graph, body.evaluation)?;
        // Support owns only Facts and shared Fact factors, never Graph values.
        // Keep the fixed roster factor shared; consumers materialize the Fact
        // sequence only when producing a body or root counterexample.
        let support = body.support.clone();
        Ok(ClosedBody {
            truth: graph.boolean(body.value())?,
            pending,
            failed: body
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. })),
            scope: self.scope(graph, &body.scope)?,
            support,
            reasons: body
                .reasons
                .iter()
                .map(|r| self.reason(r))
                .collect::<Result<_, _>>()?,
            counterexamples: evidence
                .iter()
                .map(|r| self.counterexample(graph, *r))
                .collect::<Result<_, _>>()?,
        })
    }
    pub(super) fn binding(
        &mut self,
        graph: &Graph,
        binding: &Binding,
    ) -> Result<OwnedBinding, InternalError> {
        Ok(OwnedBinding {
            name: binding.name.clone(),
            value: self.value(graph, binding.value)?,
        })
    }
}
