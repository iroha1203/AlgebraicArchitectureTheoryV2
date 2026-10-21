//! 元TypeAstの添字出現を、現在の実束縛producerと原始所属族へ結ぶ。
use super::*;

pub(in crate::observed) struct TypeDomain {
    pub values: Option<Vec<Scalar>>,
    pub scope: Scope,
    pub support: Vec<Fact>,
    pub missing: Vec<Fact>,
    pub owners: Vec<NodeRef>,
    pub type_span: (usize, usize),
}
type OwnerInputs = (Vec<NodeRef>, BTreeMap<String, SourceValue>, Vec<Fact>);

impl Environment<'_> {
    pub(super) fn owned_type_values(
        &self,
        spec: &quantifier::Spec<'_>,
        variables: &BTreeMap<String, SourceValue>,
        reading: &str,
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<TypeDomain, ValidationFailure> {
        if spec.owners.is_empty() {
            let e = self.finite_values(&spec.element, observer)?;
            let mut domain = TypeDomain {
                values: Some(e.values),
                scope: e.scope,
                support: e.support,
                missing: vec![],
                owners: vec![],
                type_span: spec.type_span.unwrap_or(spec.span),
            };
            self.restrict_object_domain(&spec.domain_type, &mut domain)?;
            return Ok(domain);
        }
        let mut scope = Scope::default();
        let mut support = Vec::new();
        let unresolved = Cell::new(false);
        for leaf in &spec.owners {
            self.tick()?;
            let value = variables
                .get(&leaf.name)
                .ok_or("元Owned添字の現在束縛がない")?;
            if value
                .known_value
                .as_ref()
                .is_some_and(|v| v.ty() != Type::Ref(leaf.root.clone()))
            {
                return Err("元Owned添字の現在owner型が違う".into());
            }
            if value.known_value.is_none() {
                unresolved.set(true);
                scope.completions = true;
            }
            scope.merge(&value.scope);
            support.extend(value.support.iter().cloned());
        }
        let observer = RefCell::new(observer);
        let missing = RefCell::new(Vec::new());
        let enumeration = super::super::finite::values_with_owned(
            &spec.domain_type,
            self.inputs.law(),
            &self.control,
            &mut |entity| {
                self.reference_roster(entity, &mut |i| observer.borrow_mut()("ref_roster", i))
            },
            &mut |entity, name| {
                let leaf = spec
                    .owners
                    .iter()
                    .find(|leaf| leaf.entity == entity && leaf.name == name)
                    .ok_or("元Owned型leafと列挙が違う")?;
                let value = variables.get(name).ok_or("元Owned添字値がない")?;
                if let Some(owner) = &value.known_value {
                    if owner.ty() != Type::Ref(leaf.root.clone()) {
                        return Err("元Ownedの根owner型が違う".into());
                    }
                    let roster =
                        self.owned_members(entity, owner, None, reading, &mut |phase, i| {
                            observer.borrow_mut()(phase, i)
                        })?;
                    missing.borrow_mut().extend(roster.missing);
                    Ok(roster.enumeration)
                } else {
                    unresolved.set(true);
                    let mut e = super::super::finite::Enumeration::default();
                    e.scope.completions = true;
                    Ok(e)
                }
            },
            &mut |i| observer.borrow_mut()("type_enum", i),
        )?;
        scope.merge(&enumeration.scope);
        support.extend(enumeration.support);
        support.sort();
        support.dedup();
        let mut missing = missing.into_inner();
        missing.sort();
        missing.dedup();
        let values = if unresolved.get() {
            None
        } else {
            Some(enumeration.values)
        };
        let mut domain = TypeDomain {
            values,
            scope,
            support,
            missing,
            owners: vec![],
            type_span: spec.type_span.ok_or("元Owned型位置がない")?,
        };
        // 明示されたownerは固定参照。公開環境の別rootの族へ交差しない。
        if self.architecture_ref().is_none() {
            self.restrict_object_domain(&spec.domain_type, &mut domain)?;
        }
        if !domain.missing.is_empty() {
            domain.values = None;
        }
        Ok(domain)
    }

    pub(super) fn restrict_object_domain(
        &self,
        ty: &Type,
        domain: &mut TypeDomain,
    ) -> Result<(), ValidationFailure> {
        if let Some(object) = self.object_domain()
            && object.is_local(ty)
        {
            object.restrict(
                ty,
                &mut domain.values,
                &mut domain.missing,
                &mut domain.support,
                &mut domain.scope,
                &self.control,
                &self.completion_values.borrow(),
            )?;
            // 同じ対象域の所属を決める既知ownerを、除外された候補も含めて保持する。
            // 部分対象ではそのsubjectを選んだownerだけが根拠となる。
            for subject in self.subjects.values() {
                self.control
                    .clone()
                    .checkpoint(Checkpoint::ObjectEvaluation)?;
                if !object.membership_subject(subject) {
                    continue;
                }
                use crate::definition::PrimitiveSignature;
                if !matches!(
                    self.inputs
                        .definitions()
                        .declarations
                        .get(&subject.ty)
                        .map(|d| &d.signature),
                    Some(
                        PrimitiveSignature::Entity { owner: Some(_), .. }
                            | PrimitiveSignature::Arrow { .. }
                    )
                ) {
                    continue;
                }
                for field in &subject.fields {
                    self.control
                        .clone()
                        .checkpoint(Checkpoint::ObjectEvaluation)?;
                    if field.name.rsplit('.').next() != Some("owner") {
                        continue;
                    }
                    if let Slot::Known { atom, origin, .. } = &field.slot {
                        domain.scope.merge(&self.scope(
                            subject,
                            object.identity.reading(),
                            Some(origin),
                        )?);
                        domain.support.push(Fact {
                            snapshot: subject.snapshot.clone(),
                            subject: subject.id.clone(),
                            field: Some(field.name.clone()),
                            atom: Some(atom.clone()),
                        });
                    }
                }
            }
            domain.support.sort();
            domain.support.dedup();
        }
        Ok(())
    }

    fn owned_type_producers(
        &self,
        graph: &Graph,
        spec: &quantifier::Spec<'_>,
        bindings: &[Binding],
    ) -> Result<OwnerInputs, ValidationFailure> {
        let mut owners = Vec::new();
        let mut variables = BTreeMap::new();
        let mut missing = Vec::new();
        for leaf in &spec.owners {
            self.tick()?;
            let bytes = self.inputs.sources().law().bytes();
            if !(leaf.type_span.0 <= leaf.span.0 && leaf.span.1 <= leaf.type_span.1)
                || bytes.get(leaf.span.0..leaf.span.1) != Some(leaf.name.as_bytes())
            {
                return Err("元Owned添字のname・byte spanが違う".into());
            }
            let mut lexical = None;
            for (name, origin) in self.lexical_context(leaf.span)? {
                self.tick()?;
                if name == leaf.name && lexical.replace(origin).is_some() {
                    return Err("元Owned添字のlexical束縛が一意でない".into());
                }
            }
            let (producer, known, scope, support) = if let Some(origin) = lexical {
                match origin {
                    LexicalOrigin::Let(rhs) => {
                        let producer = self.actual_evaluation(graph, rhs, bindings)?;
                        let value = self
                            .evaluation(graph, producer)?
                            .2
                            .map(|r| graph.scalar(r).cloned())
                            .transpose()?;
                        let node = graph.get(producer)?;
                        (producer, value, node.scope.clone(), node.support.clone())
                    }
                    LexicalOrigin::Pattern {
                        matching,
                        arm,
                        binder,
                    } => {
                        let ExprKind::Match { scrutinee, .. } =
                            self.inputs.law().exprs[matching].kind
                        else {
                            return Err("元pattern添字のASTが違う".into());
                        };
                        let producer = self.actual_evaluation(graph, scrutinee, bindings)?;
                        let value = self
                            .evaluation(graph, producer)?
                            .2
                            .ok_or("未知patternからownerを束縛した")?;
                        if data::select(
                            self.inputs.law(),
                            matching,
                            Some(graph.scalar(value)?),
                            &self.control,
                        )? != Some(arm)
                        {
                            return Err("元Owned添字のpattern armが違う".into());
                        }
                        let known =
                            data::project(graph.scalar(value)?, &binder.path, &self.control)?;
                        if known.ty() != binder.ty {
                            return Err("元Owned添字のpattern path型が違う".into());
                        }
                        let node = graph.get(producer)?;
                        (
                            producer,
                            Some(known),
                            node.scope.clone(),
                            node.support.clone(),
                        )
                    }
                    LexicalOrigin::Iteration(comp) => {
                        let index = self
                            .iteration_for(graph, comp)?
                            .ok_or("元Owned添字の実反復がない")?;
                        let record = &graph.iterations[index];
                        if self.expression_bindings(graph, record.source)? != bindings {
                            return Err("元Owned添字の反復元束縛が違う".into());
                        }
                        let (input, known, analysis) = self.iteration_input(graph, index)?;
                        let producer = if let Some(finite) = record.finite {
                            let Some(Payload::Domain { elements, .. }) =
                                &graph.get(finite)?.payload
                            else {
                                return Err("元Owned添字の反復Domainがない".into());
                            };
                            *elements
                                .iter()
                                .find(|r| graph.scalar(**r).is_ok_and(|v| v == &known))
                                .ok_or("元Owned添字の実Domain memberがない")?
                        } else {
                            input
                        };
                        (producer, Some(known), analysis.scope, analysis.support)
                    }
                    LexicalOrigin::Universal(_) => {
                        return Err("数値全域binderをOwned根ownerへ使った".into());
                    }
                }
            } else if let Some(producer) = self.call_parameter(graph, &leaf.name)? {
                self.recheck_evaluation(graph, producer)?;
                let value = self
                    .evaluation(graph, producer)?
                    .2
                    .map(|r| graph.scalar(r).cloned())
                    .transpose()?;
                let node = graph.get(producer)?;
                (producer, value, node.scope.clone(), node.support.clone())
            } else {
                let binding = bindings
                    .iter()
                    .find(|b| b.name == leaf.name)
                    .ok_or("元Owned添字の宣言parameter束縛がない")?;
                if binding.ty != Type::Ref(leaf.root.clone()) {
                    return Err("元Owned添字のparameter型が違う".into());
                }
                if graph.context_at(binding.value.0).request != self.current_context(graph).request
                {
                    return Err("元Owned添字parameterが別Requestのproducerである".into());
                }
                self.validate_at(graph, graph.get(binding.value)?, binding.value.0)?;
                let node = graph.get(binding.value)?;
                (
                    binding.value,
                    Some(graph.scalar(binding.value)?.clone()),
                    node.scope.clone(),
                    node.support.clone(),
                )
            };
            if producer.0 >= self.cutoff.get().min(graph.nodes.len()) {
                return Err("元Owned添字producerが既出でない".into());
            }
            if known
                .as_ref()
                .is_some_and(|v| v.ty() != Type::Ref(leaf.root.clone()))
            {
                return Err("元Owned添字の根owner値型が違う".into());
            }
            for reason in &graph.get(producer)?.reasons {
                self.tick()?;
                missing.extend(reason.missing.iter().cloned());
            }
            owners.push(producer);
            variables.insert(
                leaf.name.clone(),
                SourceValue {
                    condition_failed: false,
                    condition_pending: false,
                    symbolic: None,
                    comparison: None,
                    affine: None,
                    scope,
                    known_value: known,
                    support,
                    scalar_scope: None,
                },
            );
        }
        missing.sort();
        missing.dedup();
        Ok((owners, variables, missing))
    }

    pub(in crate::observed) fn owned_type_domain(
        &self,
        graph: &Graph,
        id: usize,
        bindings: &[Binding],
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<TypeDomain, ValidationFailure> {
        let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
        if spec.domain.is_some() {
            return Err("In量化をOwned型域として列挙した".into());
        }
        let (owners, variables, missing) = self.owned_type_producers(graph, &spec, bindings)?;
        let declaration = self
            .inputs
            .law()
            .declarations
            .values()
            .find(|d| d.span.0 <= spec.span.0 && spec.span.1 <= d.span.1)
            .ok_or("元Owned型量化の宣言がない")?;
        let mut domain =
            self.owned_type_values(&spec, &variables, &declaration.reading, observer)?;
        domain.owners = owners;
        domain.missing.extend(missing);
        domain.missing.sort();
        domain.missing.dedup();
        Ok(domain)
    }

    /// 実量化も現在caseの共有代入から元Owned型域を構成する。
    pub(in crate::observed) fn owned_type_domain_at(
        &self,
        graph: &Graph,
        id: usize,
        bindings: &[Binding],
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<TypeDomain, ValidationFailure> {
        if graph.active.case.is_none() {
            return self.owned_type_domain(graph, id, bindings, observer);
        }
        self.validation_graph_session(graph, || {
            let previous_context = self.context.replace(Some(graph.active));
            let previous_cutoff = self.cutoff.replace(graph.nodes.len());
            let previous_completion = self.completion_values.replace(Vec::new());
            let result = (|| {
                if let Some(case) = graph.active.case {
                    *self.completion_values.borrow_mut() = self.completion_values(graph, case)?;
                }
                #[cfg(test)]
                data::observe_actual(
                    self.inputs.law().exprs[id].span,
                    graph.active,
                    "owned_type_case",
                    0,
                );
                self.tick()?;
                self.owned_type_domain(graph, id, bindings, observer)
            })();
            self.completion_values.replace(previous_completion);
            self.cutoff.set(previous_cutoff);
            self.context.set(previous_context);
            result
        })
    }

    /// 元の型量化と実owner producerから、補完前の所属欠測を読む。
    pub(in crate::observed) fn owned_type_missing_slots(
        &self,
        graph: &Graph,
        source: NodeRef,
    ) -> Result<Option<(Vec<Fact>, (usize, usize))>, ValidationFailure> {
        let span = self.expression_span(graph, source)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        let ExprKind::Quant {
            split:
                crate::law::ast::QuantSplit::Fixed {
                    domain: crate::law::ast::QuantDomain::Type(original),
                    ..
                },
            ..
        } = &self.inputs.law().exprs[id].kind
        else {
            return Ok(None);
        };
        if !quantifier::has_owner(original, &self.control)? && self.object_domain().is_none() {
            return Ok(None);
        }
        let bindings = self.expression_bindings(graph, source)?;
        let previous = self.completion_values.replace(Vec::new());
        let result = (|| {
            let domain = self.owned_type_domain(graph, id, bindings, &mut |_, _| {})?;
            #[cfg(test)]
            data::observe_actual(
                span,
                self.current_context(graph),
                "owned_type_missing_source",
                0,
            );
            self.tick()?;
            Ok::<_, ValidationFailure>(domain)
        })();
        self.completion_values.replace(previous);
        result.map(|domain| {
            (!domain.missing.is_empty()).then_some((domain.missing, domain.type_span))
        })
    }

    pub(super) fn owned_type_arguments(
        &self,
        graph: &Graph,
        id: usize,
        bindings: &[Binding],
    ) -> Result<Vec<NodeRef>, ValidationFailure> {
        let ExprKind::Quant {
            split:
                crate::law::ast::QuantSplit::Fixed {
                    domain: crate::law::ast::QuantDomain::Type(original),
                    ..
                },
            ..
        } = &self.inputs.law().exprs[id].kind
        else {
            return Ok(vec![]);
        };
        if !quantifier::has_owner(original, &self.control)? {
            return Ok(vec![]);
        }
        let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
        Ok(self.owned_type_producers(graph, &spec, bindings)?.0)
    }

    pub(super) fn validate_owned_type_unknown(
        &self,
        graph: &Graph,
        node: &Node,
        id: usize,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::Evaluation {
            expression,
            bindings,
            parts,
            value,
            applicability,
            ..
        }) = &node.payload
        else {
            return Ok(false);
        };
        let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
        let domain = self.owned_type_domain(graph, id, bindings, &mut |_, _| {})?;
        if domain.values.is_some() {
            return Ok(false);
        }
        if expression.0 >= limit
            || graph.context_at(expression.0) != self.current_context(graph)
            || self.expression_span(graph, *expression)? != spec.span
            || self.expression_bindings(graph, *expression)? != bindings
        {
            return Err("未知Owned型量化の元Source・束縛・Contextが違う".into());
        }
        self.validate_at(graph, graph.get(*expression)?, expression.0)?;
        let mut scope = graph.get(*expression)?.scope.clone();
        scope.merge(&domain.scope);
        scope.add_quantifier(spec.descriptor(None, Some(self.current_context(graph))));
        scope.order_quantifiers_like(&graph.get(*expression)?.scope);
        let original = self.analyze_source(graph, spec.span, bindings)?;
        if node.ty != NodeType::Evaluation(Type::Bool)
            || !matches!(node.rule, Rule::Construction("evaluation"))
            || node.arguments != [*expression]
            || parts.len() != 1
            || parts[0].location != (Location::Law { span: spec.span })
            || !parts[0].children.is_empty()
            || parts[0].value.is_some()
            || parts[0].residual.is_some()
            || value.is_some()
            || *applicability != "applicable"
            || node.scope != scope
            || !scope.completions
            || node.support != domain.support
            || original.support != domain.support
            || original.known_value.is_some()
            || !node.evidence.is_empty()
            || node.judgment.is_some()
        {
            return Err("未知Owned域を完全Domain・body・通常値・証拠へ昇格した".into());
        }
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("未知Owned量化の元Requestがない")?;
        let mut reasons = Vec::new();
        if !domain.missing.is_empty() {
            reasons.push(Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: vec![*expression],
                missing: domain.missing,
                location: Some(Location::Law {
                    span: domain.type_span,
                }),
            });
        }
        if reasons.is_empty() {
            reasons.push(Reason {
                kind: ReasonKind::UnsupportedAlgorithm {
                    question: request.kind,
                    operand_types: vec![spec.element],
                    method: "unresolved_owned_type_quantification".into(),
                },
                request: request.id.clone(),
                dependencies: vec![*expression],
                missing: vec![],
                location: Some(Location::Law {
                    span: domain.type_span,
                }),
            });
        }
        sort_reasons(&mut reasons);
        if !reasons_equal(&node.reasons, &reasons) {
            return Err("未知Owned型量化の元欠測・型付き未実装理由が違う".into());
        }
        Ok(true)
    }
}
