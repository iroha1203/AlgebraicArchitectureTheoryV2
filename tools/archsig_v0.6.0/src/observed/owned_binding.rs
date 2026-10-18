//! 全ownerが固定されたOwned束縛を、元selector・各member・原始owner事実から検査する。
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
    fn binding_owner_names<'t>(
        &self,
        ty: &'t Type,
        _span: (usize, usize),
    ) -> Result<BTreeSet<&'t str>, ValidationFailure> {
        let mut owners = BTreeSet::new();
        let mut pending = vec![ty];
        #[cfg(test)]
        let mut index = 0;
        while let Some(ty) = pending.pop() {
            self.tick()?;
            #[cfg(test)]
            {
                data::observe_actual(
                    _span,
                    self.context.get().unwrap_or_default(),
                    "owned_binding_type",
                    index,
                );
                index += 1;
            }
            match ty {
                Type::Owned(_, owner) => {
                    owners.insert(owner.as_str());
                }
                Type::Tuple(items) => pending.extend(items),
                Type::List(item) | Type::Set(item) | Type::Option(item) => pending.push(item),
                Type::Map(from, to) => {
                    pending.push(from);
                    pending.push(to);
                }
                _ => {}
            }
            self.tick()?;
        }
        Ok(owners)
    }

    pub(in crate::observed) fn fixed_owned_binding(
        &self,
        request: &Request,
        p: &Param,
    ) -> Result<bool, ValidationFailure> {
        self.tick()?;
        let owners = self.binding_owner_names(&p.ty, p.span)?;
        if owners.is_empty() {
            return Ok(false);
        }
        let selected = |name: &str| {
            request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{name}"))
        };
        let Some(value) = selected(&p.name) else {
            return Ok(false);
        };
        let mut answer = matches!(value.value, Selector::Answer { .. });
        for (_index, owner) in owners.into_iter().enumerate() {
            self.tick()?;
            #[cfg(test)]
            data::observe_actual(
                p.span,
                self.context.get().unwrap_or_default(),
                "owned_binding_owner",
                _index,
            );
            let Some(owner) = selected(owner) else {
                self.tick()?;
                return Ok(false);
            };
            answer |= matches!(owner.value, Selector::Answer { .. });
            self.tick()?;
        }
        self.tick()?;
        Ok(answer
            && request
                .constraints
                .iter()
                .any(|c| c.parameter == p.name && c.dynamic))
    }

    // 自由ownerの実prefixごとの所属へ送る原始Answer参照。
    pub(in crate::observed) fn deferred_owned_binding(
        &self,
        request: &Request,
        p: &Param,
    ) -> Result<bool, ValidationFailure> {
        self.tick()?;
        let Type::Owned(_, owner) = &p.ty else {
            return Ok(false);
        };
        if request.kind != QuestionKind::Check {
            return Ok(false);
        }
        let mut answer = false;
        let mut fixed_owner = false;
        for (_index, argument) in request.arguments.iter().enumerate() {
            self.tick()?;
            #[cfg(test)]
            data::observe_actual(
                p.span,
                self.context.get().unwrap_or_default(),
                "deferred_owned_binding",
                _index,
            );
            if argument.name == format!("bind.{}", p.name) {
                answer = matches!(argument.value, Selector::Answer { .. });
            }
            fixed_owner |= argument.name == format!("bind.{owner}");
            self.tick()?;
        }
        let mut dynamic = false;
        for constraint in &request.constraints {
            self.tick()?;
            dynamic |= constraint.parameter == p.name && constraint.dynamic;
            self.tick()?;
        }
        self.tick()?;
        Ok(answer && !fixed_owner && dynamic)
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
        if !self.fixed_owned_binding(request, p)? {
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
        let owner_names = self.binding_owner_names(&p.ty, p.span)?;
        let selector = |name: &str| {
            request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{name}"))
                .map(|a| &a.value)
                .ok_or_else(|| ValidationFailure::Internal("所属束縛の元selectorがない".into()))
        };
        let value = self.owned_selected(graph, selector(&p.name)?, &d.reading, p.span)?;
        if value.scalar.ty() != p.ty.erase() {
            return Err(self.answer_projection_unprovided(p.span));
        }
        // ownerは元署名の順。集合の列挙順から依存辺の意味を決めない。
        let mut owners = Vec::new();
        for parameter in params {
            self.tick()?;
            if owner_names.contains(parameter.name.as_str()) {
                let selected = self.owned_selected(
                    graph,
                    selector(&parameter.name)?,
                    &d.reading,
                    parameter.span,
                )?;
                if selected.scalar.ty() != parameter.ty.erase() {
                    return Err(self.answer_projection_unprovided(parameter.span));
                }
                owners.push((parameter.name.as_str(), selected));
            }
        }
        if owners.len() != owner_names.len() {
            return Err("所属束縛の元owner parameterがない".into());
        }
        let values = owners
            .iter()
            .map(|(name, owner)| (*name, Some(&owner.scalar)))
            .collect();
        let mut checks = owned_call::Checks::default();
        self.owned_call_value_check(
            &p.ty,
            &super::super::term::affine::Value::Known(value.scalar.clone()),
            &values,
            &d.reading,
            p.span,
            &mut checks,
        )?;
        checks.scope.merge(&value.scope);
        checks.support.extend(value.support);
        let mut dependencies = Vec::new();
        if let Some(root) = value.root {
            dependencies.push(root);
        }
        let mut producer = value.producer;
        for (_, owner) in owners {
            self.tick()?;
            checks.scope.merge(&owner.scope);
            checks.support.extend(owner.support);
            if let Some(root) = owner.root
                && !dependencies.contains(&root)
            {
                dependencies.push(root);
            }
            producer = producer.or(owner.producer);
        }
        checks.support.sort();
        checks.support.dedup();
        let producer = producer.ok_or("所属束縛に元Answerがない")?;
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
        if !self.fixed_owned_binding(request, p)? {
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
