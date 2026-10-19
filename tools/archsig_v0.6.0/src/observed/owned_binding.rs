//! 固定ownerのOwned束縛を、元selector・各member・原始owner事実から検査する。
use super::*;
use crate::law::model::{Param, Signature};

pub(in crate::observed) struct OwnedBindingPlan {
    pub scalar: Scalar,
    pub checks: owned_call::Checks,
    pub dependencies: Vec<NodeRef>,
    pub condition_inputs: Vec<ConditionInput>,
    pub producer: String,
}
#[derive(Clone, Debug)]
pub(in crate::observed) enum ConditionInput {
    Reference(NodeRef),
    Subject(Box<Node>),
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
        let mut fixed = 0;
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
                continue;
            };
            fixed += 1;
            answer |= matches!(owner.value, Selector::Answer { .. });
            self.tick()?;
        }
        self.tick()?;
        Ok(fixed > 0
            && answer
            && request
                .constraints
                .iter()
                .any(|c| c.parameter == p.name && c.dynamic))
    }

    // 自由ownerを含む固定Answerを、実prefixごとの所属へ送る。
    pub(in crate::observed) fn deferred_owned_binding(
        &self,
        request: &Request,
        p: &Param,
    ) -> Result<bool, ValidationFailure> {
        self.tick()?;
        if request.kind != QuestionKind::Check {
            return Ok(false);
        }
        let owners = self.binding_owner_names(&p.ty, p.span)?;
        if owners.is_empty() {
            return Ok(false);
        }
        let mut answer = false;
        let mut fixed_owners = BTreeSet::new();
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
            for owner in &owners {
                self.tick()?;
                if argument.name == format!("bind.{owner}") {
                    fixed_owners.insert(*owner);
                }
                self.tick()?;
            }
            self.tick()?;
        }
        let mut dynamic = false;
        for constraint in &request.constraints {
            self.tick()?;
            dynamic |= constraint.parameter == p.name && constraint.dynamic;
            self.tick()?;
        }
        self.tick()?;
        Ok(answer && fixed_owners.len() < owners.len() && dynamic)
    }

    // root条件では固定されたownerだけを検査し、自由ownerは実fiberへ残す。
    // 値・元署名・公開型は変更せず、検査する所属制約だけを選ぶ。
    fn binding_fixed_type(
        &self,
        ty: &Type,
        fixed: &BTreeSet<&str>,
    ) -> Result<Type, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let ty = match ty {
                Type::Owned(entity, owner) if !fixed.contains(owner.as_str()) => {
                    Type::Ref(entity.clone())
                }
                Type::Tuple(items) => {
                    let mut types = Vec::new();
                    for item in items {
                        self.tick()?;
                        types.push(self.binding_fixed_type(item, fixed)?);
                        self.tick()?;
                    }
                    Type::Tuple(types)
                }
                Type::Option(item) => Type::Option(Box::new(self.binding_fixed_type(item, fixed)?)),
                Type::List(item) => Type::List(Box::new(self.binding_fixed_type(item, fixed)?)),
                Type::Set(item) => Type::Set(Box::new(self.binding_fixed_type(item, fixed)?)),
                Type::Map(from, to) => Type::Map(
                    Box::new(self.binding_fixed_type(from, fixed)?),
                    Box::new(self.binding_fixed_type(to, fixed)?),
                ),
                ty => ty.clone(),
            };
            self.tick()?;
            Ok(ty)
        })
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

    fn owned_condition_input(
        &self,
        selected: &Selected,
    ) -> Result<ConditionInput, ValidationFailure> {
        self.tick()?;
        if let Some(root) = selected.root {
            return Ok(ConditionInput::Reference(root));
        }
        let Scalar::Subject {
            snapshot, subject, ..
        } = &selected.scalar
        else {
            return Err("所属条件の直接入力がsubjectでない".into());
        };
        let original = self.subject(snapshot, subject)?;
        Ok(ConditionInput::Subject(Box::new(Node {
            ty: NodeType::Value(selected.scalar.ty()),
            payload: Some(Payload::Scalar(selected.scalar.clone())),
            rule: Rule::Input {
                kind: "subject",
                location: Location::ArchMap {
                    pointer: original.pointer.clone(),
                    span: None,
                },
            },
            arguments: vec![],
            support: selected.support.clone(),
            scope: selected.scope.clone(),
            evidence: vec![],
            judgment: None,
            reasons: vec![],
        })))
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
        let mut selected_owners = BTreeSet::new();
        for argument in &request.arguments {
            self.tick()?;
            if let Some(name) = argument.name.strip_prefix("bind.")
                && owner_names.contains(name)
            {
                selected_owners.insert(name);
            }
            self.tick()?;
        }
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
            if owner_names.contains(parameter.name.as_str())
                && selected_owners.contains(parameter.name.as_str())
            {
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
        if owners.is_empty() || owners.len() != selected_owners.len() {
            return Err("所属束縛の固定owner parameterがない".into());
        }
        let fixed = owners.iter().map(|(name, _)| *name).collect();
        let checked_type = self.binding_fixed_type(&p.ty, &fixed)?;
        let values = owners
            .iter()
            .map(|(name, owner)| (*name, Some(&owner.scalar)))
            .collect();
        let mut checks = owned_call::Checks::default();
        self.owned_call_value_check(
            &checked_type,
            &super::super::term::affine::Value::Known(value.scalar.clone()),
            &values,
            &d.reading,
            p.span,
            &mut checks,
        )?;
        if checks.blocked && checks.failure.is_none() && !checks.missing.is_empty() {
            // 固定値の所属も、元ArchMapへ拡張できる共有assignmentで判断する。
            // 候補値は一時的な引数として渡し、観測表・DAGの原始値へ書き込まない。
            let mut fields = checks.missing.clone();
            fields.sort();
            fields.dedup();
            let assignments = self.completion_assignments(&fields, &mut |_phase, _index| {
                #[cfg(test)]
                data::observe_actual(p.span, context, "owned_binding_completion_enum", _index);
            })?;
            checks.scope.merge(&assignments.scope);
            checks.support.extend(assignments.support);
            let mut succeeded = false;
            let mut failure = None;
            let mut unresolved = false;
            for (_index, assignment) in assignments.values.into_iter().enumerate() {
                self.tick()?;
                #[cfg(test)]
                data::observe_actual(p.span, context, "owned_binding_completion_case", _index);
                let members = if fields.len() == 1 {
                    vec![assignment]
                } else {
                    let Scalar::Tuple(members) = &assignment else {
                        return Err("所属補完の共有assignmentがTupleでない".into());
                    };
                    members.clone()
                };
                if members.len() != fields.len() {
                    return Err("所属補完の元slot数が違う".into());
                }
                let assignment = fields.iter().cloned().zip(members).collect();
                let mut case = owned_call::Checks::default();
                self.owned_call_value_check_assigned(
                    &checked_type,
                    &super::super::term::affine::Value::Known(value.scalar.clone()),
                    &values,
                    &d.reading,
                    p.span,
                    &mut case,
                    Some(&assignment),
                )?;
                checks.scope.merge(&case.scope);
                checks.support.extend(case.support);
                if let Some(pair) = case.failure {
                    failure = failure.or(Some(pair));
                } else if case.blocked {
                    unresolved = true;
                    checks.missing.extend(case.missing);
                } else {
                    succeeded = true;
                }
                self.tick()?;
            }
            checks.blocked = unresolved || (succeeded && failure.is_some());
            checks.failure = if !succeeded && !unresolved {
                failure
            } else {
                None
            };
        }
        let mut condition_inputs = vec![self.owned_condition_input(&value)?];
        checks.scope.merge(&value.scope);
        checks.support.extend(value.support);
        let mut dependencies = Vec::new();
        if let Some(root) = value.root {
            dependencies.push(root);
        }
        let mut producer = value.producer;
        for (_, owner) in owners {
            self.tick()?;
            condition_inputs.push(self.owned_condition_input(&owner)?);
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
            condition_inputs,
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
