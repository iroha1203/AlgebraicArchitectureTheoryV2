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
            return Ok(TypeDomain {
                values: Some(e.values),
                scope: e.scope,
                support: e.support,
                missing: vec![],
                owners: vec![],
                type_span: spec.type_span.unwrap_or(spec.span),
            });
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
        let values = if unresolved.get() || !missing.is_empty() {
            None
        } else {
            Some(enumeration.values)
        };
        Ok(TypeDomain {
            values,
            scope,
            support,
            missing,
            owners: vec![],
            type_span: spec.type_span.ok_or("元Owned型位置がない")?,
        })
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
        sort_reasons(&mut reasons);
        if node.reasons.iter().map(Reason::wire).collect::<Vec<_>>()
            != reasons.iter().map(Reason::wire).collect::<Vec<_>>()
        {
            return Err("未知Owned型量化の元欠測・型付き未実装理由が違う".into());
        }
        Ok(true)
    }
}
