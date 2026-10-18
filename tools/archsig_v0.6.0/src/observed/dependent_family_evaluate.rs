//! 元署名の宣言順に、実prefix域を選択して依存Law族のrowを構成する。
use super::*;
use crate::observed::environment::family::{Plan, family_decision, family_items, family_type};

#[derive(Clone, Default)]
struct Prefix {
    path: Vec<(NodeRef, NodeRef)>,
    free: Vec<(String, Scalar)>,
}
fn path_arguments(source: NodeRef, path: &[(NodeRef, NodeRef)]) -> Vec<NodeRef> {
    std::iter::once(source)
        .chain(path.iter().flat_map(|&(domain, member)| [domain, member]))
        .collect()
}

impl Evaluator<'_, '_> {
    pub(super) fn dependent_family_answer(
        &mut self,
        plan: Plan,
        guard: Option<usize>,
        body: usize,
        role: Option<Role>,
    ) -> Result<Answer, Failure> {
        let fixed: Vec<_> = plan
            .parameters
            .iter()
            .filter(|p| {
                self.request
                    .arguments
                    .iter()
                    .any(|a| a.name == format!("bind.{}", p.name))
            })
            .cloned()
            .collect();
        // 元selectorの固定値を保持する。動的Owned制約の放電は各実prefixで行う。
        self.bind_parameters(&fixed, true)?;
        let root = self.graph.active;
        let fixed_bindings = self.bindings.clone();
        let finite_parameters: Vec<_> = plan
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, p)| !plan.numeric.iter().any(|n| n.name == p.name))
            .collect();
        let mut raw_scope = self.base.clone();
        self.environment
            .dependent_merge_scope(&plan, &mut raw_scope, &[], root)?;
        raw_scope.assignments |= !plan.numeric.is_empty();
        let source = self.family_source(body, &plan.free, &raw_scope)?;
        let guard_source = guard
            .map(|g| self.family_source(g, &plan.free, &raw_scope))
            .transpose()?;
        let mut domains = Vec::new();
        let mut paths = Vec::new();
        let mut all_scope = raw_scope.clone();
        let mut all_support = Vec::new();
        // DFS preorder。子の逆順pushにより、元Domainの要素順でprefixを辿る。
        let mut pending = vec![(0, Prefix::default())];
        while let Some((parameter_index, prefix)) = pending.pop() {
            self.tick(Checkpoint::FiniteIteration)?;
            if parameter_index == plan.parameters.len() {
                paths.push(prefix.path);
                continue;
            }
            let parameter = &plan.parameters[parameter_index];
            // 無限数値parameterは各実rowの全域評価へ渡す。有限fiberにはしない。
            if plan.numeric.iter().any(|p| p.name == parameter.name) {
                pending.push((parameter_index + 1, prefix));
                continue;
            }
            self.family_observe("dependent_domain", domains.len());
            self.tick(Checkpoint::FiniteIteration)?;
            #[cfg(test)]
            let (span, context) = (self.declaration.span, root);
            let step = self.environment.dependent_family_step(
                self.graph,
                self.request,
                parameter_index,
                &prefix.free,
                &mut |_phase, _index| {
                    #[cfg(test)]
                    {
                        data::observe_actual(span, context, "dependent_enum", _index);
                        data::observe_actual(parameter.span, context, _phase, _index);
                    }
                },
            )?;
            let mut scope = raw_scope.clone();
            scope.merge(&step.enumeration.scope);
            let mut support = step.enumeration.support;
            for &(_, selected) in &prefix.path {
                self.tick(Checkpoint::FiniteIteration)?;
                scope.merge(&self.graph.get(selected)?.scope);
                support.extend(self.graph.get(selected)?.support.iter().cloned());
                self.tick(Checkpoint::FiniteIteration)?;
            }
            self.environment.dependent_merge_scope(
                &plan,
                &mut scope,
                &prefix
                    .path
                    .iter()
                    .enumerate()
                    .map(|(i, &(domain, _))| {
                        let parameter = finite_parameters[i].0;
                        (parameter, domain)
                    })
                    .collect::<Vec<_>>(),
                root,
            )?;
            support.sort();
            support.dedup();
            if !step.missing.is_empty() {
                all_scope.merge(&scope);
                self.environment
                    .dependent_merge_scope(&plan, &mut all_scope, &domains, root)?;
                let dependencies = vec![source];
                let location = Some(Location::Law {
                    span: parameter.span,
                });
                let reasons = vec![
                    Reason {
                        kind: ReasonKind::Missing,
                        request: self.request.id.clone(),
                        dependencies: dependencies.clone(),
                        missing: step.missing,
                        location: location.clone(),
                    },
                    Reason {
                        kind: ReasonKind::UnsupportedAlgorithm {
                            question: QuestionKind::Check,
                            operand_types: vec![parameter.ty.erase()],
                            method: "unresolved_dependent_owner".into(),
                        },
                        request: self.request.id.clone(),
                        dependencies,
                        missing: vec![],
                        location,
                    },
                ];
                self.reasons.extend(reasons.iter().cloned());
                self.retained_scope.merge(&all_scope);
                return Ok(Answer {
                    id: self.request.id.clone(),
                    status: Decision::Undetermined,
                    outputs: BTreeMap::new(),
                    claim: None,
                    evidence: vec![],
                    reasons,
                    scope: all_scope,
                });
            }
            let arguments = path_arguments(source, &prefix.path);
            let mut elements = Vec::new();
            let mut children = Vec::new();
            for value in step.enumeration.values {
                self.tick(Checkpoint::FiniteIteration)?;
                let scalar = self.value(
                    value.clone(),
                    Rule::Input {
                        kind: "law",
                        location: Location::Law {
                            span: parameter.span,
                        },
                    },
                    arguments.clone(),
                    support.clone(),
                    scope.clone(),
                )?;
                elements.push(scalar);
                let mut child = prefix.clone();
                if plan.unbound.iter().any(|p| p.name == parameter.name) {
                    child.free.push((parameter.name.clone(), value));
                }
                children.push((scalar, child));
            }
            let domain = self.push(Node {
                ty: NodeType::Domain,
                payload: Some(Payload::Domain {
                    ty: parameter.ty.erase(),
                    elements: elements.clone(),
                }),
                rule: Rule::Input {
                    kind: "law",
                    location: Location::Law {
                        span: parameter.span,
                    },
                },
                arguments: arguments.into_iter().chain(elements).collect(),
                support: support.clone(),
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: vec![],
            })?;
            domains.push((parameter_index, domain));
            all_scope.merge(&scope);
            all_support.extend(support);
            self.family_observe("dependent_domain_done", domains.len() - 1);
            self.tick(Checkpoint::FiniteIteration)?;
            for (scalar, mut child) in children.into_iter().rev() {
                self.tick(Checkpoint::FiniteIteration)?;
                child.path.push((domain, scalar));
                pending.push((parameter_index + 1, child));
                self.tick(Checkpoint::FiniteIteration)?;
            }
        }
        self.environment
            .dependent_merge_scope(&plan, &mut all_scope, &domains, root)?;
        all_support.sort();
        all_support.dedup();
        self.retained_scope.merge(&all_scope);
        let types: Vec<_> = plan.unbound.iter().map(|p| p.ty.erase()).collect();
        let mut members = Vec::new();
        for path in paths {
            self.family_observe("dependent_member", members.len());
            self.tick(Checkpoint::FiniteIteration)?;
            let mut values = Vec::new();
            for ((_, parameter), &(_, selected)) in finite_parameters.iter().zip(&path) {
                self.tick(Checkpoint::FiniteIteration)?;
                if plan.unbound.iter().any(|p| p.name == parameter.name) {
                    values.push(self.graph.scalar(selected)?.clone());
                }
                self.tick(Checkpoint::FiniteIteration)?;
            }
            let value = if values.len() == 1 {
                values.remove(0)
            } else {
                Scalar::Tuple(values)
            };
            members.push(self.value(
                value,
                Rule::Input {
                    kind: "law",
                    location: Location::Law {
                        span: self.declaration.span,
                    },
                },
                path_arguments(source, &path),
                all_support.clone(),
                all_scope.clone(),
            )?);
        }
        let product = self.push(Node {
            ty: NodeType::Domain,
            payload: Some(Payload::Domain {
                ty: family_type(&types),
                elements: members.clone(),
            }),
            rule: Rule::Input {
                kind: "law",
                location: Location::Law {
                    span: self.declaration.span,
                },
            },
            arguments: std::iter::once(source)
                .chain(domains.iter().map(|&(_, domain)| domain))
                .chain(members.iter().copied())
                .collect(),
            support: all_support.clone(),
            evidence: vec![],
            judgment: None,
            scope: all_scope.clone(),
            reasons: vec![],
        })?;
        let domain_scope = all_scope.clone();
        let domain_support = all_support.clone();
        let mut rows = Vec::new();
        let mut row_instances = Vec::new();
        let mut row_evidence = Vec::new();
        let mut value = Some(true);
        let mut reasons = Vec::new();
        for member in members {
            self.family_observe("dependent_row", rows.len());
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
                for parameter in &plan.parameters {
                    self.tick(Checkpoint::FiniteIteration)?;
                    if plan.numeric.iter().any(|p| p.name == parameter.name) {
                        continue;
                    }
                    let value = if let Some(i) =
                        plan.unbound.iter().position(|p| p.name == parameter.name)
                    {
                        self.value(
                            items[i].clone(),
                            Rule::Input {
                                kind: "law",
                                location: Location::Law {
                                    span: parameter.span,
                                },
                            },
                            vec![source, product, member],
                            domain_support.clone(),
                            domain_scope.clone(),
                        )?
                    } else {
                        fixed_bindings
                            .iter()
                            .find(|b| b.name == parameter.name)
                            .ok_or_else(|| Failure::Internal("依存rowの固定bindingがない".into()))?
                            .value
                    };
                    self.bindings.push(Binding {
                        name: parameter.name.clone(),
                        ty: parameter.ty.erase(),
                        value,
                    });
                }
                self.answer(&plan.parameters, guard, body, role)
            })();
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
                return Err(Failure::Internal("依存rowのLawInstanceがない".into()));
            };
            row_instances.push(*instance);
            let Some(Payload::Evaluation { value: actual, .. }) =
                &self.graph.get(evaluation)?.payload
            else {
                return Err(Failure::Internal("依存rowの適用評価がない".into()));
            };
            let actual = self.graph.boolean(*actual)?;
            if actual == Some(false) {
                value = Some(false);
            } else if actual.is_none() && value != Some(false) {
                value = None;
            }
            all_scope.merge(&row.scope);
            all_support.extend(self.graph.get(evaluation)?.support.iter().cloned());
            reasons.extend(row.reasons);
            for evidence in row.evidence {
                if matches!(
                    self.graph.get(evidence)?.payload,
                    Some(Payload::Counterexample { .. })
                ) {
                    row_evidence.push(evidence);
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
                role: match role.ok_or_else(|| Failure::Internal("依存Lawのroleがない".into()))?
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
        self.family_observe("dependent_aggregate", 0);
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
            self.family_observe("dependent_exhaustion", 0);
            self.tick(Checkpoint::FiniteIteration)?;
            evidence.push(self.push(Node {
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
            })?);
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
}
