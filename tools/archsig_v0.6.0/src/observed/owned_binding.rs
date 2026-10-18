//! 固定された原始Owned束縛を、元selectorと原始owner事実から検査する。
use super::*;
use crate::law::model::{Param, Signature};

pub(in crate::observed) struct OwnedBindingPlan {
    pub scalar: Scalar,
    pub checks: owned_call::Checks,
    pub dependencies: Vec<NodeRef>,
    pub producer: String,
}
struct Selected {
    scalar: Scalar,
    scope: Scope,
    support: Vec<Fact>,
    root: Option<NodeRef>,
    producer: Option<String>,
}

impl Environment<'_> {
    pub(in crate::observed) fn fixed_owned_binding(request: &Request, p: &Param) -> bool {
        let Type::Owned(_, owner) = &p.ty else {
            return false;
        };
        let selected = |name: &str| {
            request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{name}"))
        };
        let (Some(value), Some(owner)) = (selected(&p.name), selected(owner)) else {
            return false;
        };
        request
            .constraints
            .iter()
            .any(|c| c.parameter == p.name && c.dynamic)
            && (matches!(value.value, Selector::Answer { .. })
                || matches!(owner.value, Selector::Answer { .. }))
    }

    fn owned_selected(
        &self,
        graph: &Graph,
        selector: &Selector,
        reading: &str,
        span: (usize, usize),
    ) -> Result<Selected, ValidationFailure> {
        self.tick()?;
        match selector {
            Selector::Subject { snapshot, subject } => {
                let s = self.subject(snapshot, subject)?;
                Ok(Selected {
                    scalar: Scalar::Subject {
                        snapshot: snapshot.clone(),
                        subject: subject.clone(),
                        entity: s.ty.clone(),
                    },
                    scope: self.scope(s, reading, None)?,
                    support: vec![Fact {
                        snapshot: snapshot.clone(),
                        subject: subject.clone(),
                        field: None,
                        atom: None,
                    }],
                    root: None,
                    producer: None,
                })
            }
            Selector::Answer { id, .. } => {
                let plan = self.answer_binding(graph, selector, span)?;
                let (node, root) = match plan {
                    AnswerBinding::Reference(r) => (graph.get(r)?.clone(), r),
                    AnswerBinding::Projection(n) => {
                        let root = *n.arguments.first().ok_or("所属射影の元rootがない")?;
                        (n, root)
                    }
                    AnswerBinding::Inapplicable(_) => {
                        return Err(self.answer_projection_unprovided(span));
                    }
                };
                let Some(Payload::Scalar(scalar)) = node.payload else {
                    return Err("所属束縛の元Answerが通常値でない".into());
                };
                Ok(Selected {
                    scalar,
                    scope: node.scope,
                    support: node.support,
                    root: Some(root),
                    producer: Some(id.clone()),
                })
            }
            _ => Err("所属束縛が元subject/Answerでない".into()),
        }
    }

    pub(in crate::observed) fn owned_binding_plan(
        &self,
        graph: &Graph,
        request: &Request,
        p: &Param,
    ) -> Result<Option<OwnedBindingPlan>, ValidationFailure> {
        if !Self::fixed_owned_binding(request, p) {
            return Ok(None);
        }
        self.tick()?;
        let originals = self.original_requests.ok_or("所属束縛の元Requestがない")?;
        let context = self.current_context(graph);
        if originals.get(context.request) != Some(request)
            || graph.requests.get(context.request) != Some(request)
        {
            return Err("所属束縛のRequestが元入力と違う".into());
        }
        let d = &self.inputs.law().declarations[request.declaration()];
        let params = match &d.signature {
            Signature::View { params, .. } | Signature::Law { params, .. } => params,
            _ => return Err("所属束縛の元宣言がview/Lawでない".into()),
        };
        if !params.contains(p) {
            return Err("所属束縛の元parameterが違う".into());
        }
        let Type::Owned(_, owner_name) = &p.ty else {
            unreachable!()
        };
        let owner_parameter = params
            .iter()
            .find(|a| &a.name == owner_name)
            .ok_or("所属束縛の元owner parameterがない")?;
        let selector = |name: &str| {
            request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{name}"))
                .map(|a| &a.value)
                .ok_or_else(|| ValidationFailure::Internal("所属束縛の元selectorがない".into()))
        };
        let value = self.owned_selected(graph, selector(&p.name)?, &d.reading, p.span)?;
        let owner = self.owned_selected(
            graph,
            selector(owner_name)?,
            &d.reading,
            owner_parameter.span,
        )?;
        if value.scalar.ty() != p.ty.erase() || owner.scalar.ty() != owner_parameter.ty.erase() {
            return Err(self.answer_projection_unprovided(p.span));
        }
        let values = BTreeMap::from([(owner_name.as_str(), Some(&owner.scalar))]);
        let mut checks = owned_call::Checks::default();
        self.owned_reference_check(
            &p.ty,
            Some(&value.scalar),
            &values,
            &d.reading,
            p.span,
            &mut checks,
        )?;
        checks.scope.merge(&value.scope);
        checks.scope.merge(&owner.scope);
        checks.support.extend(value.support);
        checks.support.extend(owner.support);
        checks.support.sort();
        checks.support.dedup();
        let mut dependencies = Vec::new();
        for r in value.root.into_iter().chain(owner.root) {
            self.tick()?;
            if !dependencies.contains(&r) {
                dependencies.push(r);
            }
        }
        let producer = value
            .producer
            .or(owner.producer)
            .ok_or("所属束縛に元Answerがない")?;
        #[cfg(test)]
        data::observe_actual(p.span, context, "owned_binding_checked", 0);
        self.tick()?;
        Ok(Some(OwnedBindingPlan {
            scalar: value.scalar,
            checks,
            dependencies,
            producer,
        }))
    }

    pub(in crate::observed) fn owned_binding_node(
        &self,
        graph: &Graph,
        request: &Request,
        p: &Param,
        original: NodeRef,
    ) -> Result<Option<Node>, ValidationFailure> {
        let Some(plan) = self.owned_binding_plan(graph, request, p)? else {
            return Ok(None);
        };
        if plan.checks.failure.is_some() || plan.checks.blocked {
            return Err("未確認・不適合Owned束縛を通常値へ消費した".into());
        }
        let input = graph.get(original)?;
        let argument = request
            .arguments
            .iter()
            .find(|a| a.name == format!("bind.{}", p.name))
            .ok_or("所属束縛の元引数がない")?;
        match &argument.value {
            selector @ Selector::Answer { .. } => {
                self.answer_binding_matches(graph, selector, original, p.span)?
            }
            Selector::Subject { snapshot, subject } => {
                let s = self.subject(snapshot, subject)?;
                if input.rule
                    != (Rule::Input {
                        kind: "subject",
                        location: Location::ArchMap {
                            pointer: s.pointer.clone(),
                            span: None,
                        },
                    })
                    || graph.context_at(original.0) != self.current_context(graph)
                {
                    return Err("所属束縛の元subject producerが違う".into());
                }
            }
            _ => return Err("所属束縛の元selectorが違う".into()),
        }
        self.validate_at(graph, input, original.0)?;
        if graph.scalar(original)? != &plan.scalar {
            return Err("所属束縛の元値が違う".into());
        }
        let mut arguments = vec![original];
        for r in plan.dependencies {
            if !arguments.contains(&r) {
                arguments.push(r);
            }
        }
        self.tick()?;
        Ok(Some(Node {
            ty: NodeType::Value(Type::Bool),
            payload: Some(Payload::Scalar(Scalar::Bool(true))),
            rule: Rule::OwnedBinding(p.name.clone()),
            arguments,
            support: plan.checks.support,
            scope: plan.checks.scope,
            evidence: vec![],
            judgment: None,
            reasons: vec![],
        }))
    }

    pub(super) fn validate_owned_binding(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let Rule::OwnedBinding(parameter) = &node.rule else {
            return Ok(false);
        };
        self.tick()?;
        let context = self.current_context(graph);
        if context.frame.is_some()
            || context.iteration.is_some()
            || context.instance.is_some()
            || context.case.is_some()
        {
            return Err("所属束縛が元Requestのrootにない".into());
        }
        let request = self
            .original_requests
            .and_then(|r| r.get(context.request))
            .ok_or("所属束縛の元Requestがない")?;
        let d = &self.inputs.law().declarations[request.declaration()];
        let params = match &d.signature {
            Signature::View { params, .. } | Signature::Law { params, .. } => params,
            _ => return Err("所属束縛の元署名がない".into()),
        };
        let p = params
            .iter()
            .find(|p| &p.name == parameter)
            .ok_or("所属束縛の元parameterがない")?;
        let original = *node.arguments.first().ok_or("所属束縛の元値辺がない")?;
        for r in &node.arguments {
            if r.0 >= limit {
                return Err("所属束縛の引数が未出".into());
            }
        }
        let expected = self
            .owned_binding_node(graph, request, p, original)?
            .ok_or("元入力に動的固定Owned制約がない")?;
        if node != &expected {
            return Err("所属束縛の型・値・元Ref・辺・支持・Scopeが元入力と違う".into());
        }
        self.tick()?;
        Ok(true)
    }

    pub(in crate::observed) fn require_owned_binding(
        &self,
        graph: &Graph,
        request: &Request,
        p: &Param,
        value: NodeRef,
    ) -> Result<Option<NodeRef>, ValidationFailure> {
        if !Self::fixed_owned_binding(request, p) {
            return Ok(None);
        }
        let context = self.current_context(graph);
        let mut selected = None;
        for (i, node) in graph
            .nodes
            .iter()
            .enumerate()
            .take(self.cutoff.get().min(graph.nodes.len()))
        {
            self.tick()?;
            let at = graph.context_at(i);
            if at.request == context.request
                && at.frame.is_none()
                && at.iteration.is_none()
                && at.instance.is_none()
                && at.case.is_none()
                && node.rule == Rule::OwnedBinding(p.name.clone())
            {
                if selected.replace(NodeRef(i)).is_some() {
                    return Err("元Owned制約の所属確認が重複".into());
                }
                if node.arguments.first() != Some(&value) {
                    return Err("所属確認が元束縛値を指していない".into());
                }
                self.validate_at(graph, node, i)?;
            }
        }
        selected
            .map(Some)
            .ok_or_else(|| "元Owned制約の所属確認がない".into())
    }
}
