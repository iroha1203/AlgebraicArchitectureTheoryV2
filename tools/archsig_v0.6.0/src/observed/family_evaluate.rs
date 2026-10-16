//! 元Law parameterの有限直積を実instanceへ適用し、全称要求を集約する。
use super::*;
use crate::observed::environment::family::{family_decision, family_items, family_type};

impl Evaluator<'_, '_> {
    pub(super) fn is_family(&self, params: &[Param]) -> bool {
        self.request.kind == QuestionKind::Check
            && params.iter().any(|p| {
                !self
                    .request
                    .arguments
                    .iter()
                    .any(|a| a.name == format!("bind.{}", p.name))
            })
    }
    fn family_observe(&self, _phase: &'static str, _index: usize) {
        #[cfg(test)]
        data::observe_actual(self.declaration.span, self.graph.active, _phase, _index);
    }
    fn family_source(
        &mut self,
        id: usize,
        parameters: &[Param],
        scope: &Scope,
    ) -> Result<NodeRef, Failure> {
        let span = self.environment.inputs.law().exprs[id].span;
        self.push(Node {
            ty: NodeType::Expression(Type::Bool),
            payload: Some(Payload::Expression {
                location: Location::Law { span },
                parameters: parameters
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.clone()))
                    .collect(),
                bindings: self.bindings.clone(),
            }),
            rule: Rule::Input {
                kind: "law",
                location: Location::Law { span },
            },
            arguments: self
                .environment
                .source_arguments(self.graph, span, &self.bindings)?,
            support: vec![],
            evidence: vec![],
            judgment: None,
            scope: scope.clone(),
            reasons: vec![],
        })
    }
    pub(super) fn family_answer(
        &mut self,
        _params: &[Param],
        guard: Option<usize>,
        body: usize,
        role: Option<Role>,
    ) -> Result<Answer, Failure> {
        let numeric = _params
            .iter()
            .filter(|parameter| {
                !self
                    .request
                    .arguments
                    .iter()
                    .any(|argument| argument.name == format!("bind.{}", parameter.name))
            })
            .collect::<Vec<_>>();
        if !numeric.is_empty()
            && numeric
                .iter()
                .all(|parameter| matches!(parameter.ty, Type::Z | Type::Q))
        {
            return self.universal_family_answer(_params, role);
        }
        self.finite_family_answer(guard, body, role)
    }

    #[inline(never)]
    fn finite_family_answer(
        &mut self,
        guard: Option<usize>,
        body: usize,
        role: Option<Role>,
    ) -> Result<Answer, Failure> {
        let plan = self
            .environment
            .family_plan(self.request)?
            .ok_or_else(|| Failure::Internal("有限Law族の計画がない".into()))?;
        let fixed: Vec<_> = plan
            .parameters
            .iter()
            .filter(|p| {
                self.request
                    .arguments
                    .iter()
                    .any(|argument| argument.name == format!("bind.{}", p.name))
            })
            .cloned()
            .collect();
        self.bind(&fixed)?;
        let root = self.graph.active;
        let fixed_bindings = self.bindings.clone();
        let mut raw_scope = self.base.clone();
        raw_scope.quantifiers = self.environment.family_descriptors(&plan, &[], root);
        raw_scope.assignments = !plan.numeric.is_empty();
        let source = self.family_source(body, &plan.free, &raw_scope)?;
        let guard_source = guard
            .map(|g| self.family_source(g, &plan.free, &raw_scope))
            .transpose()?;
        let mut domains = Vec::new();
        let mut all_scope = raw_scope.clone();
        let mut all_support = Vec::new();
        for (parameter_index, p) in plan.unbound.iter().enumerate() {
            self.family_observe("family_domain", parameter_index);
            self.tick(Checkpoint::FiniteIteration)?;
            #[cfg(test)]
            let (span, context) = (self.declaration.span, root);
            let enumeration = self
                .environment
                .finite_values(&p.ty, &mut |_phase, _index| {
                    #[cfg(test)]
                    data::observe_actual(span, context, "family_enum", _index);
                })?;
            let mut scope = raw_scope.clone();
            scope.merge(&enumeration.scope);
            let mut elements = Vec::new();
            for value in enumeration.values {
                self.tick(Checkpoint::FiniteIteration)?;
                elements.push(self.value(
                    value,
                    Rule::Input {
                        kind: "law",
                        location: Location::Law { span: p.span },
                    },
                    vec![source],
                    enumeration.support.clone(),
                    scope.clone(),
                )?);
            }
            let arguments = std::iter::once(source)
                .chain(elements.iter().copied())
                .collect();
            let domain = self.push(Node {
                ty: NodeType::Domain,
                payload: Some(Payload::Domain {
                    ty: p.ty.clone(),
                    elements,
                }),
                rule: Rule::Input {
                    kind: "law",
                    location: Location::Law { span: p.span },
                },
                arguments,
                support: enumeration.support.clone(),
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: vec![],
            })?;
            domains.push(domain);
            all_scope.merge(&scope);
            all_support.extend(enumeration.support);
        }
        all_scope.quantifiers = self.environment.family_descriptors(&plan, &domains, root);
        all_support.sort();
        all_support.dedup();
        self.retained_scope.merge(&all_scope);
        let types: Vec<_> = plan.unbound.iter().map(|p| p.ty.clone()).collect();
        let product = if domains.len() == 1 {
            domains[0]
        } else {
            #[cfg(test)]
            let (span, context) = (self.declaration.span, root);
            let enumeration = self
                .environment
                .family_product(&types, &mut |_phase, _index| {
                    #[cfg(test)]
                    data::observe_actual(span, context, "family_product", _index);
                })?;
            let mut elements = Vec::new();
            for value in enumeration.values {
                self.family_observe("family_product_member", elements.len());
                self.tick(Checkpoint::FiniteIteration)?;
                elements.push(
                    self.value(
                        value,
                        Rule::Input {
                            kind: "law",
                            location: Location::Law {
                                span: self.declaration.span,
                            },
                        },
                        std::iter::once(source)
                            .chain(domains.iter().copied())
                            .collect(),
                        all_support.clone(),
                        all_scope.clone(),
                    )?,
                );
            }
            self.push(Node {
                ty: NodeType::Domain,
                payload: Some(Payload::Domain {
                    ty: family_type(&types),
                    elements: elements.clone(),
                }),
                rule: Rule::Input {
                    kind: "law",
                    location: Location::Law {
                        span: self.declaration.span,
                    },
                },
                arguments: std::iter::once(source)
                    .chain(domains.iter().copied())
                    .chain(elements)
                    .collect(),
                support: all_support.clone(),
                evidence: vec![],
                judgment: None,
                scope: all_scope.clone(),
                reasons: vec![],
            })?
        };
        let Some(Payload::Domain { elements, .. }) = &self.graph.get(product)?.payload else {
            return Err(Failure::Internal("実直積Domainがない".into()));
        };
        let members = elements.clone();
        let domain_scope = all_scope.clone();
        let domain_support = all_support.clone();
        let mut rows = Vec::new();
        let mut row_instances = Vec::new();
        let mut row_evidence = Vec::new();
        let mut value = Some(true);
        let mut reasons = Vec::new();
        for member in members {
            self.family_observe("family_row", rows.len());
            self.tick(Checkpoint::FiniteIteration)?;
            let items = family_items(self.graph.scalar(member)?, types.len())?;
            let index = self.graph.instances.len();
            self.graph.instances.push(super::super::call::Instance {
                caller: root,
                source,
                domain: product,
                member,
            });
            self.graph.active = super::super::call::Context {
                instance: Some(index),
                ..root
            };
            self.bindings.clear();
            self.base = domain_scope.clone();
            self.lexical.clear();
            self.formal.clear();
            self.sources.clear();
            self.completed.clear();
            self.answer_evaluation = None;
            let row_result = (|| -> Result<Answer, Failure> {
                for p in &plan.parameters {
                    self.tick(Checkpoint::FiniteIteration)?;
                    if plan.numeric.iter().any(|numeric| numeric.name == p.name) {
                        continue;
                    }
                    let value = if let Some(i) = plan.unbound.iter().position(|u| u.name == p.name)
                    {
                        self.value(
                            items[i].clone(),
                            Rule::Input {
                                kind: "law",
                                location: Location::Law { span: p.span },
                            },
                            vec![source, product, member],
                            domain_support.clone(),
                            domain_scope.clone(),
                        )?
                    } else {
                        fixed_bindings
                            .iter()
                            .find(|b| b.name == p.name)
                            .ok_or_else(|| Failure::Internal("固定bindingがない".into()))?
                            .value
                    };
                    self.bindings.push(Binding {
                        name: p.name.clone(),
                        ty: p.ty.erase(),
                        value,
                    });
                }
                self.answer(&plan.parameters, guard, body, role)
            })();
            // 未完成wholeのAnswerへ最終rowを昇格させない。停止も元Contextへ戻してから伝播。
            self.graph.active = root;
            self.bindings = fixed_bindings.clone();
            self.base = raw_scope.clone();
            self.sources.clear();
            self.completed.clear();
            self.answer_evaluation = None;
            self.lexical.clear();
            self.formal.clear();
            let row = row_result?;
            let evaluation = row.outputs["evaluation"];
            let proposition = row.outputs["proposition"];
            let Some(Payload::Proposition { instance }) = &self.graph.get(proposition)?.payload
            else {
                return Err(Failure::Internal("実rowのLawInstanceがない".into()));
            };
            row_instances.push(*instance);

            let Some(Payload::Evaluation { value: v, .. }) = &self.graph.get(evaluation)?.payload
            else {
                return Err(Failure::Internal("実row適用評価がない".into()));
            };
            let b = self.graph.boolean(*v)?;
            if b == Some(false) {
                value = Some(false);
            } else if b.is_none() && value != Some(false) {
                value = None;
            }
            all_scope.merge(&row.scope);
            all_support.extend(self.graph.get(evaluation)?.support.iter().cloned());
            reasons.extend(row.reasons);
            for e in row.evidence {
                if matches!(
                    self.graph.get(e)?.payload,
                    Some(Payload::Counterexample { .. })
                ) {
                    row_evidence.push(e);
                }
            }
            rows.push(evaluation);
            self.tick(Checkpoint::FiniteIteration)?;
        }
        all_support.sort();
        all_support.dedup();
        sort_reasons(&mut reasons);
        self.environment.family_order_scope(&plan, &mut all_scope)?;
        let template = self.push(Node {
            ty: NodeType::LawInstance,
            payload: Some(Payload::LawInstance {
                name: self.declaration.name.clone(),
                role: match role.ok_or_else(|| Failure::Internal("族Lawのroleがない".into()))?
                {
                    Role::Required => "required",
                    Role::Optional => "optional",
                },
                bindings: fixed_bindings.clone(),
                guard: guard_source,
                body: source,
                occurrence: Location::Law {
                    span: self.declaration.span,
                },
            }),
            rule: Rule::Construction("law_instance"),
            arguments: std::iter::once(source)
                .chain(guard_source)
                .chain(std::iter::once(product))
                .chain(row_instances.iter().copied())
                .chain(rows.iter().copied())
                .collect(),
            support: all_support.clone(),
            evidence: vec![],
            judgment: None,
            scope: all_scope.clone(),
            reasons: vec![],
        })?;
        self.family_observe("family_aggregate", 0);
        self.tick(Checkpoint::FiniteIteration)?;
        let scalar = value
            .map(|b| {
                self.value(
                    Scalar::Bool(b),
                    Rule::Construction("evaluation"),
                    std::iter::once(template)
                        .chain(rows.iter().copied())
                        .collect(),
                    all_support.clone(),
                    all_scope.clone(),
                )
            })
            .transpose()?;
        let evaluation = self.push_law_evaluation(Node {
            ty: NodeType::Evaluation(Type::Bool),
            payload: Some(Payload::Evaluation {
                expression: source,
                bindings: fixed_bindings,
                parts: vec![Part {
                    location: Location::Law {
                        span: self.environment.inputs.law().exprs[body].span,
                    },
                    value: scalar,
                    residual: None,
                    children: rows.clone(),
                }],
                value: scalar,
                applicability: "applicable",
            }),
            rule: Rule::Construction("evaluation"),
            arguments: std::iter::once(template)
                .chain(std::iter::once(product))
                .chain(rows.iter().copied())
                .collect(),
            support: all_support.clone(),
            evidence: vec![],
            judgment: None,
            scope: all_scope.clone(),
            reasons: reasons.clone(),
        })?;
        let mut evidence = row_evidence;
        if value == Some(true) {
            self.family_observe("family_exhaustion", 0);
            self.tick(Checkpoint::FiniteIteration)?;
            let proof = self.push(Node {
                ty: NodeType::Evidence,
                payload: Some(Payload::FiniteExhaustion {
                    domain: product,
                    checked: rows.len(),
                    instances: rows,
                }),
                rule: Rule::Construction("evidence"),
                arguments: vec![template, evaluation],
                support: all_support.clone(),
                evidence: vec![],
                judgment: None,
                scope: all_scope.clone(),
                reasons: vec![],
            })?;
            evidence.push(proof);
        }
        let status = family_decision(value);
        let proposition = self.push(Node {
            ty: NodeType::Proposition,
            payload: Some(Payload::Proposition { instance: template }),
            rule: Rule::Construction("proposition"),
            arguments: vec![template, evaluation],
            support: all_support,
            evidence: evidence.clone(),
            judgment: Some(Judgment {
                status,
                evidence: evidence.clone(),
                reasons: reasons.clone(),
            }),
            scope: all_scope.clone(),
            reasons: reasons.clone(),
        })?;
        Ok(Answer {
            id: self.request.id.clone(),
            status,
            outputs: BTreeMap::from([
                ("evaluation".into(), evaluation),
                ("proposition".into(), proposition),
            ]),
            claim: Some(proposition),
            evidence,
            reasons,
            scope: all_scope,
        })
    }
    pub(super) fn inapplicable_family_row(
        &mut self,
        _params: &[Param],
        guard_id: usize,
        body_id: usize,
        role: Option<Role>,
        guard: &Evaluated,
    ) -> Result<Answer, Failure> {
        let body = self.source(
            self.environment.inputs.law().exprs[body_id].span,
            Type::Bool,
        )?;
        let instance = self.push(Node {
            ty: NodeType::LawInstance,
            payload: Some(Payload::LawInstance {
                name: self.declaration.name.clone(),
                role: match role.ok_or_else(|| Failure::Internal("row roleがない".into()))? {
                    Role::Required => "required",
                    Role::Optional => "optional",
                },
                bindings: self.bindings.clone(),
                guard: Some(guard.expression),
                body: body.expression,
                occurrence: Location::Law {
                    span: self.declaration.span,
                },
            }),
            rule: Rule::Construction("law_instance"),
            arguments: std::iter::once(body.expression)
                .chain(std::iter::once(guard.evaluation))
                .chain(self.bindings.iter().map(|b| b.value))
                .collect(),
            support: guard.support.clone(),
            evidence: vec![],
            judgment: None,
            scope: guard.scope.clone(),
            reasons: vec![],
        })?;
        let value = self.value(
            Scalar::Bool(true),
            Rule::Construction("evaluation"),
            vec![instance, guard.evaluation],
            guard.support.clone(),
            guard.scope.clone(),
        )?;
        let evaluation = self.push_law_evaluation(Node {
            ty: NodeType::Evaluation(Type::Bool),
            payload: Some(Payload::Evaluation {
                expression: body.expression,
                bindings: self.bindings.clone(),
                parts: vec![
                    Part {
                        location: Location::Law {
                            span: self.environment.inputs.law().exprs[guard_id].span,
                        },
                        value: guard.value,
                        residual: guard.residual,
                        children: vec![guard.evaluation],
                    },
                    Part {
                        location: Location::Law {
                            span: self.environment.inputs.law().exprs[body_id].span,
                        },
                        value: None,
                        residual: None,
                        children: vec![],
                    },
                ],
                value: Some(value),
                applicability: "not_applicable",
            }),
            rule: Rule::Construction("evaluation"),
            arguments: vec![instance, guard.evaluation],
            support: guard.support.clone(),
            evidence: vec![],
            judgment: None,
            scope: guard.scope.clone(),
            reasons: guard.reasons.clone(),
        })?;
        let proposition = self.push(Node {
            ty: NodeType::Proposition,
            payload: Some(Payload::Proposition { instance }),
            rule: Rule::Construction("proposition"),
            arguments: vec![instance, evaluation],
            support: guard.support.clone(),
            evidence: vec![],
            judgment: Some(Judgment {
                status: Decision::Established,
                evidence: vec![],
                reasons: guard.reasons.clone(),
            }),
            scope: guard.scope.clone(),
            reasons: guard.reasons.clone(),
        })?;
        Ok(Answer {
            id: self.request.id.clone(),
            status: Decision::Established,
            outputs: BTreeMap::from([
                ("evaluation".into(), evaluation),
                ("proposition".into(), proposition),
            ]),
            claim: Some(proposition),
            evidence: vec![],
            reasons: guard.reasons.clone(),
            scope: guard.scope.clone(),
        })
    }
}
