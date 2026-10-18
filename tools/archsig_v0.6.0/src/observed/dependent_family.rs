//! 元署名を左から束縛した実fiber。検査は提示された行でなく元観測から域を再構成する。
use super::family::{Plan, family_items, family_type};
use super::*;
use crate::law::ast::QuantKind;

pub(in crate::observed) struct DependentStep {
    pub enumeration: super::super::finite::Enumeration,
    pub missing: Vec<Fact>,
}

struct Layout {
    // 検査中の既出Refだけを保持する。値のshadow表や照合成功を入力として再利用しない。
    domains: Vec<(usize, NodeRef)>,
    paths: Vec<Vec<NodeRef>>,
    scope: Scope,
    support: Vec<Fact>,
    next: Option<(usize, Vec<NodeRef>)>,
}

impl Environment<'_> {
    fn dependent_fixed_value(
        &self,
        graph: &Graph,
        request: &Request,
        name: &str,
    ) -> Result<Option<super::super::finite::Enumeration>, ValidationFailure> {
        let Some(argument) = request
            .arguments
            .iter()
            .find(|a| a.name == format!("bind.{name}"))
        else {
            return Ok(None);
        };
        let declaration = &self.inputs.law().declarations[request.declaration()];
        let mut enumeration = super::super::finite::Enumeration::default();
        match &argument.value {
            Selector::Subject { snapshot, subject } => {
                let s = self.subject(snapshot, subject)?;
                enumeration.values.push(Scalar::Subject {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    entity: s.ty.clone(),
                });
                enumeration.scope = self.scope(s, &declaration.reading, None)?;
                enumeration.support.push(Fact {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    field: None,
                    atom: None,
                });
            }
            selector @ Selector::Answer { .. } => {
                let crate::law::model::Signature::Law { params, .. } = &declaration.signature
                else {
                    return Err("固定fiberの元Law署名がない".into());
                };
                let parameter = params
                    .iter()
                    .find(|p| p.name == name)
                    .ok_or("固定fiberの元parameterがない")?;
                let node = match self.answer_binding(graph, selector, parameter.span)? {
                    AnswerBinding::Reference(r) => graph.get(r)?.clone(),
                    AnswerBinding::Projection(node) => node,
                    AnswerBinding::Inapplicable(_) => {
                        return Err("不適合Answerが固定fiberに到達した".into());
                    }
                };
                let Some(Payload::Scalar(value)) = node.payload else {
                    return Err("固定fiberの元Answerが値でない".into());
                };
                enumeration.values.push(value);
                enumeration.scope = node.scope;
                enumeration.support = node.support;
            }
            _ => return Err("固定fiberが元subject/Answer selectorでない".into()),
        }
        Ok(Some(enumeration))
    }

    pub(in crate::observed) fn dependent_family_step(
        &self,
        graph: &Graph,
        request: &Request,
        parameter: usize,
        prefix: &[(String, Scalar)],
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<DependentStep, ValidationFailure> {
        self.tick()?;
        let plan = self.family_plan(request)?.ok_or("依存族の元署名がない")?;
        if !plan.dependent {
            return Err("非依存族をfiberとして列挙した".into());
        }
        let p = plan
            .parameters
            .get(parameter)
            .ok_or("fiberの元parameterがない")?;
        let prior: Vec<_> = plan.parameters[..parameter]
            .iter()
            .filter(|p| plan.unbound.iter().any(|free| free.name == p.name))
            .collect();
        if prefix.len() != prior.len() {
            return Err("fiberの先行自由束縛数が違う".into());
        }
        for (p, (name, value)) in prior.iter().zip(prefix) {
            self.tick()?;
            if p.name != *name || p.ty.erase() != value.ty() {
                return Err("fiberの先行自由束縛型・順が違う".into());
            }
            data::check(value, self.inputs.law(), &self.control)?;
        }
        let fixed = self.dependent_fixed_value(graph, request, &p.name)?;
        let reading = &self.inputs.law().declarations[request.declaration()].reading;
        let mut result = DependentStep {
            enumeration: super::super::finite::Enumeration::default(),
            missing: vec![],
        };
        if let Type::Owned(entity, owner_name) = &p.ty {
            let owner = prefix
                .iter()
                .find(|(name, _)| name == owner_name)
                .map(|(_, value)| value.clone())
                .or(self
                    .dependent_fixed_value(graph, request, owner_name)?
                    .and_then(|mut e| e.values.pop()))
                .ok_or("依存parameterの先行ownerがない")?;
            let roster = self.owned_members(
                entity,
                &owner,
                fixed.as_ref().and_then(|e| e.values.first()),
                reading,
                observer,
            )?;
            result.enumeration = roster.enumeration;
            result.missing = roster.missing;
        } else if let Some(enumeration) = fixed {
            if enumeration.values.len() != 1 || enumeration.values[0].ty() != p.ty.erase() {
                return Err("固定fiber型が元署名と違う".into());
            }
            result.enumeration = enumeration;
            if p.ty != p.ty.erase() {
                // 固定複合値のleafも、元署名の現在の実prefixで検査する。
                // 全固定ownerは従来のroot条件で放電し、混在は計画段階で拒否する。
                let mut owners = BTreeMap::new();
                for prior in &plan.parameters[..parameter] {
                    self.tick()?;
                    if matches!(prior.ty, Type::Ref(_)) {
                        let value = prefix
                            .iter()
                            .find(|(name, _)| *name == prior.name)
                            .map(|(_, value)| value.clone())
                            .or(self
                                .dependent_fixed_value(graph, request, &prior.name)?
                                .and_then(|mut e| e.values.pop()))
                            .ok_or("固定複合fiberの先行ownerがない")?;
                        owners.insert(prior.name.as_str(), value);
                    }
                    self.tick()?;
                }
                let mut values = BTreeMap::new();
                for (name, value) in &owners {
                    self.tick()?;
                    values.insert(*name, Some(value));
                    self.tick()?;
                }
                let mut checks = owned_call::Checks::default();
                let checked = self.owned_call_value_check(
                    &p.ty,
                    &super::super::term::affine::Value::Known(result.enumeration.values[0].clone()),
                    &values,
                    reading,
                    p.span,
                    &mut checks,
                );
                match checked {
                    Ok(()) => {}
                    Err(ValidationFailure::UnsupportedExpression { .. })
                        if !checks.missing.is_empty() => {}
                    Err(error) => return Err(error),
                }
                result.enumeration.scope.merge(&checks.scope);
                result.enumeration.support.extend(checks.support);
                result.missing = checks.missing;
                if checks.failure.is_some() || checks.blocked || !result.missing.is_empty() {
                    result.enumeration.values.clear();
                }
            }
        } else {
            // 元署名の複合型に含まれる各Owned leafも、現在の実prefixから
            // ownerを読む。消去型の全登録族へ置き換えない。
            let observer = RefCell::new(observer);
            let missing = RefCell::new(Vec::new());
            result.enumeration = super::super::finite::values_with_owned(
                &p.ty,
                self.inputs.law(),
                &self.control,
                &mut |entity| {
                    self.reference_roster(entity, &mut |i| observer.borrow_mut()("ref_roster", i))
                },
                &mut |entity, owner_name| {
                    self.tick()?;
                    let owner = prefix
                        .iter()
                        .find(|(name, _)| name == owner_name)
                        .map(|(_, value)| value.clone())
                        .or(self
                            .dependent_fixed_value(graph, request, owner_name)?
                            .and_then(|mut e| e.values.pop()))
                        .ok_or("複合依存parameterの先行ownerがない")?;
                    let roster =
                        self.owned_members(entity, &owner, None, reading, &mut |phase, i| {
                            observer.borrow_mut()(phase, i)
                        })?;
                    missing.borrow_mut().extend(roster.missing);
                    Ok(roster.enumeration)
                },
                &mut |i| observer.borrow_mut()("family_enum", i),
            )?;
            result.missing = missing.into_inner();
        }
        result.enumeration.support.sort();
        result.enumeration.support.dedup();
        result.missing.sort();
        result.missing.dedup();
        self.tick()?;
        Ok(result)
    }

    pub(in crate::observed) fn dependent_merge_scope(
        &self,
        plan: &Plan,
        scope: &mut Scope,
        domains: &[(usize, NodeRef)],
        context: super::super::call::Context,
    ) -> Result<(), ValidationFailure> {
        scope.merge_quantifiers(&Scope {
            quantifiers: self.dependent_family_descriptors(plan, domains, context),
            ..Scope::default()
        });
        self.family_order_scope(plan, scope)
    }

    pub(in crate::observed) fn dependent_family_descriptors(
        &self,
        plan: &Plan,
        domains: &[(usize, NodeRef)],
        context: super::super::call::Context,
    ) -> Vec<Quantifier> {
        let mut quantifiers = Vec::new();
        for p in &plan.free {
            let parameter = plan
                .parameters
                .iter()
                .position(|original| original.name == p.name)
                .expect("元parameter");
            let actual: Vec<_> = domains
                .iter()
                .filter(|(i, _)| *i == parameter)
                .map(|(_, r)| *r)
                .collect();
            let descriptor = |domain| Quantifier {
                kind: QuantKind::Forall,
                name: p.name.clone(),
                ty: p.ty.erase(),
                domain,
                occurrence: p.span,
                context: (!matches!(p.ty, Type::Z | Type::Q)).then_some(context),
            };
            if actual.is_empty() {
                quantifiers.push(descriptor(None));
            } else {
                quantifiers.extend(actual.into_iter().map(|r| descriptor(Some(r))));
            }
        }
        quantifiers
    }

    fn dependent_indices(&self, plan: &Plan) -> Vec<usize> {
        plan.parameters
            .iter()
            .enumerate()
            .filter(|(_, p)| !plan.numeric.iter().any(|n| n.name == p.name))
            .map(|(i, _)| i)
            .collect()
    }

    fn dependent_path(
        &self,
        graph: &Graph,
        source: NodeRef,
        plan: &Plan,
        path: &[NodeRef],
        count: usize,
        limit: usize,
    ) -> Result<Vec<(String, Scalar)>, ValidationFailure> {
        if path.len() != count * 2 {
            return Err("fiberの実先行path件数が違う".into());
        }
        let indices = self.dependent_indices(plan);
        let context = graph.context_at(source.0);
        let mut prefix = Vec::new();
        for (position, pair) in path.chunks_exact(2).enumerate() {
            self.tick()?;
            let (domain, selected) = (pair[0], pair[1]);
            if domain.0 >= limit
                || selected.0 >= domain.0
                || graph.context_at(domain.0) != context
                || graph.context_at(selected.0) != context
            {
                return Err("fiberの先行Domain・選択が既出の同Contextでない".into());
            }
            let p = &plan.parameters[indices[position]];
            let node = graph.get(domain)?;
            let Some(Payload::Domain { ty, elements }) = &node.payload else {
                return Err("fiberの先行Domainがない".into());
            };
            let expected: Vec<_> = std::iter::once(source)
                .chain(path[..position * 2].iter().copied())
                .collect();
            if !matches!(&node.rule,Rule::Input {kind:"law",location:Location::Law {span}} if *span == p.span)
                || ty != &p.ty.erase()
                || node.arguments.get(..expected.len()) != Some(expected.as_slice())
                || !elements.contains(&selected)
                || graph.get(selected)?.arguments != expected
            {
                return Err("fiberの先行Domain・選択producerが元prefixと違う".into());
            }
            self.validate_at(graph, node, domain.0)?;
            if plan.unbound.iter().any(|u| u.name == p.name) {
                prefix.push((p.name.clone(), graph.scalar(selected)?.clone()));
            }
        }
        Ok(prefix)
    }

    fn dependent_step_context(
        &self,
        graph: &Graph,
        source: NodeRef,
        plan: &Plan,
        parameter: usize,
        path: &[NodeRef],
        limit: usize,
    ) -> Result<DependentStep, ValidationFailure> {
        let indices = self.dependent_indices(plan);
        let count = indices
            .iter()
            .position(|i| *i == parameter)
            .ok_or("fiberの実parameter位置がない")?;
        let prefix = self.dependent_path(graph, source, plan, path, count, limit)?;
        let request = &graph.requests[graph.context_at(source.0).request];
        let mut step =
            self.dependent_family_step(graph, request, parameter, &prefix, &mut |_, _| {})?;
        step.enumeration.scope.merge(&graph.get(source)?.scope);
        let mut domains = Vec::new();
        for (position, pair) in path.chunks_exact(2).enumerate() {
            self.tick()?;
            step.enumeration.scope.merge(&graph.get(pair[1])?.scope);
            step.enumeration
                .support
                .extend(graph.get(pair[1])?.support.iter().cloned());
            domains.push((indices[position], pair[0]));
        }
        self.dependent_merge_scope(
            plan,
            &mut step.enumeration.scope,
            &domains,
            graph.context_at(source.0),
        )?;
        step.enumeration.support.sort();
        step.enumeration.support.dedup();
        Ok(step)
    }

    fn dependent_layout(
        &self,
        graph: &Graph,
        source: NodeRef,
        plan: &Plan,
        limit: usize,
        complete: bool,
    ) -> Result<Layout, ValidationFailure> {
        let context = graph.context_at(source.0);
        let indices = self.dependent_indices(plan);
        let mut candidates = Vec::new();
        for (id, node) in graph
            .nodes
            .iter()
            .enumerate()
            .take(limit.min(graph.nodes.len()))
        {
            self.tick()?;
            if node.ty == NodeType::Domain
                && node.arguments.first() == Some(&source)
                && let Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                } = &node.rule
                && let Some(parameter) = indices.iter().find(|&&i| plan.parameters[i].span == *span)
            {
                if graph.context_at(id) != context {
                    return Err("実prefixDomainが別Contextに属す".into());
                }
                candidates.push((*parameter, NodeRef(id)));
            }
        }
        let mut layout = Layout {
            domains: vec![],
            paths: vec![],
            scope: graph.get(source)?.scope.clone(),
            support: vec![],
            next: None,
        };
        // 各候補Domain自体を元観測から照合した後、その実elementsを辿る。
        // 要素の除去はDomain照合、prefixの除去・追加はこのcoverage照合で拒否する。
        let mut pending = vec![(0usize, Vec::<NodeRef>::new())];
        while let Some((position, path)) = pending.pop() {
            self.tick()?;
            if position == indices.len() {
                layout.paths.push(path);
                continue;
            }
            let parameter = indices[position];
            let expected: Vec<_> = std::iter::once(source)
                .chain(path.iter().copied())
                .collect();
            let found: Vec<_> = candidates
                .iter()
                .filter(|(i, r)| {
                    *i == parameter
                        && graph.get(*r).is_ok_and(|n| {
                            n.arguments.get(..expected.len()) == Some(expected.as_slice())
                        })
                })
                .map(|(_, r)| *r)
                .collect();
            if found.is_empty() && !complete {
                layout.next = Some((parameter, path));
                break;
            }
            let [domain] = found.as_slice() else {
                return Err("実prefixDomainの欠落・重複がある".into());
            };
            let domain = *domain;
            self.validate_at(graph, graph.get(domain)?, domain.0)?;
            layout.domains.push((parameter, domain));
            layout.scope.merge(&graph.get(domain)?.scope);
            layout
                .support
                .extend(graph.get(domain)?.support.iter().cloned());
            let Some(Payload::Domain { elements, .. }) = &graph.get(domain)?.payload else {
                return Err("実fiberがDomainでない".into());
            };
            for &selected in elements.iter().rev() {
                self.tick()?;
                let mut next = path.clone();
                next.extend([domain, selected]);
                pending.push((position + 1, next));
            }
        }
        if layout.domains != candidates {
            return Err("実prefixDomainの元順・coverageが違う".into());
        }
        self.dependent_merge_scope(plan, &mut layout.scope, &layout.domains, context)?;
        layout.support.sort();
        layout.support.dedup();
        Ok(layout)
    }

    fn dependent_row_value(
        &self,
        graph: &Graph,
        plan: &Plan,
        path: &[NodeRef],
    ) -> Result<Scalar, ValidationFailure> {
        let indices = self.dependent_indices(plan);
        let mut values = Vec::new();
        for (position, pair) in path.chunks_exact(2).enumerate() {
            self.tick()?;
            if plan
                .unbound
                .iter()
                .any(|u| u.name == plan.parameters[indices[position]].name)
            {
                values.push(graph.scalar(pair[1])?.clone());
            }
        }
        if values.len() == 1 {
            Ok(values.remove(0))
        } else {
            Ok(Scalar::Tuple(values))
        }
    }

    pub(super) fn dependent_family_domains(
        &self,
        graph: &Graph,
        source: NodeRef,
        domains: &[NodeRef],
        plan: &Plan,
    ) -> Result<Scope, ValidationFailure> {
        let layout = self.dependent_layout(graph, source, plan, self.cutoff.get(), true)?;
        if layout.domains.iter().map(|(_, r)| *r).collect::<Vec<_>>() != domains {
            return Err("依存族の実prefix域一覧が違う".into());
        }
        Ok(layout.scope)
    }

    pub(super) fn dependent_family_domain_parts(
        &self,
        graph: &Graph,
        domain: NodeRef,
        source: NodeRef,
        plan: Plan,
    ) -> Result<(NodeRef, Vec<NodeRef>, Plan), ValidationFailure> {
        let node = graph.get(domain)?;
        let Some(Payload::Domain { elements, .. }) = &node.payload else {
            return Err("依存族の総Domainがない".into());
        };
        let end = node
            .arguments
            .len()
            .checked_sub(elements.len())
            .ok_or("依存族総Domain辺数が違う")?;
        let domains = node
            .arguments
            .get(1..end)
            .ok_or("依存族総Domainの実prefix域がない")?
            .to_vec();
        self.validate_at(graph, node, domain.0)?;
        Ok((source, domains, plan))
    }

    pub(super) fn validate_dependent_family_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let Some(&source) = node.arguments.first() else {
            return Ok(false);
        };
        if !matches!(&graph.get(source)?.payload,Some(Payload::Expression {parameters,..}) if !parameters.is_empty())
        {
            return Ok(false);
        }
        let (_, plan) = self.family_request(graph, source)?;
        if !plan.dependent {
            return Ok(false);
        }
        let Rule::Input {
            kind: "law",
            location: Location::Law { span },
        } = &node.rule
        else {
            return Ok(false);
        };
        self.validate_at(graph, graph.get(source)?, source.0)?;
        let d = &self.inputs.law().declarations
            [graph.requests[graph.context_at(source.0).request].declaration()];
        let context = self.current_context(graph);
        if let Some(index) = context.instance {
            let record = graph
                .instances
                .get(index)
                .ok_or("依存rowの元instanceがない")?;
            let parameter = plan
                .unbound
                .iter()
                .position(|p| p.span == *span)
                .ok_or("依存row値の元自由parameterがない")?;
            if record.source != source
                || node.arguments != [source, record.domain, record.member]
                || context
                    != (super::super::call::Context {
                        instance: Some(index),
                        ..record.caller
                    })
                || graph.context_at(source.0) != record.caller
                || graph.context_at(record.domain.0) != record.caller
                || graph.context_at(record.member.0) != record.caller
            {
                return Err("依存row値の元instance辺・Contextが違う".into());
            }
            self.validate_at(graph, graph.get(record.domain)?, record.domain.0)?;
            let Some(Payload::Domain { elements, .. }) = &graph.get(record.domain)?.payload else {
                return Err("依存row総Domainがない".into());
            };
            if !elements.contains(&record.member) {
                return Err("依存rowが総Domainにない".into());
            }
            let items = family_items(graph.scalar(record.member)?, plan.unbound.len())?;
            self.dependent_clean_scalar(
                node,
                &items[parameter],
                &graph.get(record.domain)?.scope,
                &graph.get(record.domain)?.support,
            )?;
            return Ok(true);
        }
        if context != graph.context_at(source.0) {
            return Err("依存族値・Domainが別Contextに属す".into());
        }
        if let Some(parameter) = plan.parameters.iter().position(|p| p.span == *span) {
            let count = self
                .dependent_indices(&plan)
                .iter()
                .position(|i| *i == parameter)
                .ok_or("依存fiberのparameter位置がない")?;
            let end = 1 + 2 * count;
            let path = node
                .arguments
                .get(1..end)
                .ok_or("依存fiberの元先行pathがない")?;
            let step = self.dependent_step_context(graph, source, &plan, parameter, path, limit)?;
            if !step.missing.is_empty() {
                return Err("未観測ownerから確定fiberを生成した".into());
            }
            if let Some(Payload::Scalar(value)) = &node.payload {
                if node.arguments.len() != end
                    || !data::contains(&step.enumeration.values, value, &self.control)?
                {
                    return Err("fiber値が元実域にない".into());
                }
                self.dependent_clean_scalar(
                    node,
                    value,
                    &step.enumeration.scope,
                    &step.enumeration.support,
                )?;
            } else if let Some(Payload::Domain { ty, elements }) = &node.payload {
                if node.ty != NodeType::Domain
                    || *ty != plan.parameters[parameter].ty.erase()
                    || node.arguments.get(end..) != Some(elements.as_slice())
                    || elements.len() != step.enumeration.values.len()
                    || node.scope != step.enumeration.scope
                    || node.support != step.enumeration.support
                    || !node.evidence.is_empty()
                    || !node.reasons.is_empty()
                    || node.judgment.is_some()
                {
                    return Err("fiberの元型・全域・Scope・支持が違う".into());
                }
                for (r, expected) in elements.iter().zip(&step.enumeration.values) {
                    self.tick()?;
                    if r.0 >= limit
                        || graph.context_at(r.0) != context
                        || graph.get(*r)?.arguments != node.arguments[..end]
                        || !matches!(&graph.get(*r)?.rule, Rule::Input {kind:"law",location:Location::Law {span:member_span}} if member_span == span)
                        || graph.scalar(*r)? != expected
                    {
                        return Err("fiberの元選択producer・順・値が違う".into());
                    }
                    self.validate_at(graph, graph.get(*r)?, r.0)?;
                }
            } else {
                return Err("fiberのpayloadが値・Domainでない".into());
            }
            return Ok(true);
        }
        if *span != d.span {
            return Err("依存族の元parameter・宣言出現が違う".into());
        }
        let layout = self.dependent_layout(graph, source, &plan, limit, true)?;
        if let Some(Payload::Scalar(value)) = &node.payload {
            let path = node.arguments.get(1..).ok_or("依存rowの実pathがない")?;
            if !layout.paths.iter().any(|expected| expected == path) {
                return Err("依存rowの元実pathが違う".into());
            }
            let expected = self.dependent_row_value(graph, &plan, path)?;
            self.dependent_clean_scalar(node, &expected, &layout.scope, &layout.support)?;
            if value != &expected {
                return Err("依存row値が元宣言順と違う".into());
            }
        } else if let Some(Payload::Domain { ty, elements }) = &node.payload {
            let types: Vec<_> = plan.unbound.iter().map(|p| p.ty.erase()).collect();
            let end = 1 + layout.domains.len();
            if node.ty != NodeType::Domain
                || *ty != family_type(&types)
                || node.arguments.get(1..end)
                    != Some(
                        layout
                            .domains
                            .iter()
                            .map(|(_, r)| *r)
                            .collect::<Vec<_>>()
                            .as_slice(),
                    )
                || node.arguments.get(end..) != Some(elements.as_slice())
                || elements.len() != layout.paths.len()
                || node.scope != layout.scope
                || node.support != layout.support
                || !node.evidence.is_empty()
                || !node.reasons.is_empty()
                || node.judgment.is_some()
            {
                return Err("依存総Domainのcoverage・型・Scope・支持が違う".into());
            }
            for (&r, path) in elements.iter().zip(&layout.paths) {
                self.tick()?;
                let expected: Vec<_> = std::iter::once(source)
                    .chain(path.iter().copied())
                    .collect();
                if r.0 >= limit
                    || graph.context_at(r.0) != context
                    || graph.get(r)?.arguments != expected
                    || !matches!(&graph.get(r)?.rule, Rule::Input {kind:"law",location:Location::Law {span:member_span}} if member_span == span)
                    || graph.scalar(r)? != &self.dependent_row_value(graph, &plan, path)?
                {
                    return Err("依存総Domainの実row順・producerが違う".into());
                }
                self.validate_at(graph, graph.get(r)?, r.0)?;
            }
        } else {
            return Err("依存総域のpayloadが違う".into());
        }
        Ok(true)
    }

    fn dependent_clean_scalar(
        &self,
        node: &Node,
        expected: &Scalar,
        scope: &Scope,
        support: &[Fact],
    ) -> Result<(), ValidationFailure> {
        data::check(expected, self.inputs.law(), &self.control)?;
        if node.ty != NodeType::Value(expected.ty())
            || !matches!(&node.payload,Some(Payload::Scalar(value)) if value == expected)
            || node.scope != *scope
            || node.support != support
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
            || node.judgment.is_some()
        {
            return Err("依存族値の型・元値・Scope・支持が違う".into());
        }
        Ok(())
    }

    pub(super) fn validate_dependent_family_unknown(
        &self,
        graph: &Graph,
        request: &Request,
        answer: &Answer,
        plan: &Plan,
    ) -> Result<bool, ValidationFailure> {
        if !answer.outputs.is_empty() {
            return Ok(false);
        }
        graph.validate_answer(answer, true)?;
        let request_index = graph
            .requests
            .iter()
            .position(|actual| actual == request)
            .ok_or("未決依存族の元Requestがない")?;
        if answer.id != request.id
            || answer.status != Decision::Undetermined
            || answer.claim.is_some()
            || !answer.evidence.is_empty()
            || answer.reasons.len() != 2
        {
            return Err("未決依存族が結論・証拠を持つか元Requestと違う".into());
        }
        let first = &answer.reasons[0];
        let [source] = first.dependencies.as_slice() else {
            return Err("未決依存族の理由が元Source一件への依存でない".into());
        };
        let source = *source;
        let context = graph.context_at(source.0);
        if context.request != request_index
            || context.frame.is_some()
            || context.iteration.is_some()
            || context.instance.is_some()
        {
            return Err("未決依存族Sourceが別実Contextに属す".into());
        }
        let (_, actual_plan) = self.family_request(graph, source)?;
        if !actual_plan.dependent {
            return Err("未決依存族が元依存署名でない".into());
        }
        let Some(Location::Law { span }) = &first.location else {
            return Err("未決依存族の元parameter位置がない".into());
        };
        let parameter = plan
            .parameters
            .iter()
            .position(|p| p.span == *span)
            .ok_or("未決ownerの元出現が違う")?;
        let previous = self.context.replace(Some(context));
        let old_cutoff = self.cutoff.replace(graph.nodes.len());
        let result = (|| -> Result<(), ValidationFailure> {
            self.validate_at(graph, graph.get(source)?, source.0)?;
            let layout = self.dependent_layout(graph, source, plan, graph.nodes.len(), false)?;
            let (expected_parameter, path) = layout
                .next
                .as_ref()
                .ok_or("未決ownerに元列挙の未完了prefixがない")?;
            if *expected_parameter != parameter {
                return Err("未決ownerが元列挙の未完了parameterと違う".into());
            }
            let step = self.dependent_step_context(
                graph,
                source,
                plan,
                parameter,
                path,
                graph.nodes.len(),
            )?;
            if step.missing.is_empty() {
                return Err("未決ownerに元欠測がない".into());
            }
            let mut scope = layout.scope;
            scope.merge(&step.enumeration.scope);
            self.dependent_merge_scope(plan, &mut scope, &layout.domains, context)?;
            let missing = Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: vec![source],
                missing: step.missing,
                location: Some(Location::Law { span: *span }),
            };
            let unsupported = Reason {
                kind: ReasonKind::UnsupportedAlgorithm {
                    question: QuestionKind::Check,
                    operand_types: vec![plan.parameters[parameter].ty.erase()],
                    method: "unresolved_dependent_owner".into(),
                },
                request: request.id.clone(),
                dependencies: vec![source],
                missing: vec![],
                location: Some(Location::Law { span: *span }),
            };
            let mut reasons = vec![missing, unsupported];
            sort_reasons(&mut reasons);
            if answer.scope != scope
                || answer.reasons.iter().map(Reason::wire).collect::<Vec<_>>()
                    != reasons.iter().map(Reason::wire).collect::<Vec<_>>()
            {
                return Err("未決依存族の元欠測・未実装理由・Scopeが違う".into());
            }
            Ok(())
        })();
        self.cutoff.set(old_cutoff);
        self.context.set(previous);
        result.map(|()| true)
    }
}
