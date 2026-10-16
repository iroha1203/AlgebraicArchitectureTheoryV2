//! 元Bool slotの共有assignmentごとに選択した問い全体を評価する。
use super::*;
impl Evaluator<'_, '_> {
    fn completion_observe(&self, _phase: &'static str, _index: usize) {
        #[cfg(test)]
        data::observe_actual(self.declaration.span, self.graph.active, _phase, _index);
    }
    fn completion_reset(&mut self, context: super::super::call::Context) {
        self.graph.active = context;
        self.bindings.clear();
        self.lexical.clear();
        self.formal.clear();
        self.sources.clear();
        self.completed.clear();
        self.answer_evaluation = None;
        self.base = Scope::default();
        self.base.readings.insert(self.declaration.reading.clone());
        self.base.completions = context.case.is_some();
    }
    pub(super) fn complete_answer(
        &mut self,
        observed: Result<Answer, Failure>,
        params: &[Param],
        guard: Option<usize>,
        body: usize,
        role: Option<Role>,
    ) -> Result<Answer, Failure> {
        let root = self.graph.active;
        if root.case.is_some() {
            return observed;
        }
        if let Ok(answer) = &observed
            && answer.status != Decision::Undetermined
            && !answer.reasons.is_empty()
        {
            // 原式だけで既知となった回答を、追加の補完導出に先立ち独立に検査する。
            // 外側のvalidator callbackは呼ばず、Stop/失敗なら保存もしない。
            self.environment
                .validate_answer(self.graph, self.request, answer)?;
            self.verified_observed = Some(answer.clone());
        }
        let mut roots = Vec::new();
        match &observed {
            Ok(answer) => {
                roots.extend(answer.outputs.get("evaluation").copied());
                roots.extend(answer.claim);
            }
            Err(Failure::NotImplemented { .. }) => {
                roots.extend(
                    self.reasons
                        .iter()
                        .flat_map(|r| r.dependencies.iter().copied()),
                );
                roots.extend(self.completed.values().map(|v| v.evaluation));
            }
            Err(_) => return observed,
        }
        roots.sort_by_key(|r| r.0);
        roots.dedup();
        let (fields, _, _) = self.environment.completion_slots(self.graph, &roots)?;
        if fields.is_empty() {
            return observed;
        }
        self.completing = true;
        let fixed = self.bindings.clone();
        // 未完成のbaseではcall/反復を出た後の元root固定束縛のみを保持する。
        let fixed: Vec<_> = params
            .iter()
            .filter_map(|p| {
                fixed
                    .iter()
                    .find(|b| {
                        b.name == p.name
                            && self
                                .request
                                .arguments
                                .iter()
                                .any(|a| a.name == format!("bind.{}", p.name))
                    })
                    .cloned()
            })
            .collect();
        loop {
            self.completion_reset(root);
            self.bindings = fixed.clone();
            let (fields, sources, reasons) =
                self.environment.completion_slots(self.graph, &roots)?;
            if fields.is_empty() {
                return Err(Failure::Internal("既読Bool補完域が消えた".into()));
            }
            let mut scope = self.base.clone();
            scope.completions = true;
            let mut support = Vec::new();
            for &r in &roots {
                scope.merge(&self.graph.get(r)?.scope);
                support.extend(self.graph.get(r)?.support.iter().cloned());
            }
            support.sort();
            support.dedup();
            let unbound: Vec<_> = params
                .iter()
                .filter(|p| !fixed.iter().any(|b| b.name == p.name))
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect();
            let location = Location::Law {
                span: self.environment.inputs.law().exprs[body].span,
            };
            let seed = self.push(Node {
                ty: NodeType::Expression(
                    self.environment
                        .inputs
                        .law()
                        .expr_type(body)
                        .ok_or_else(|| Failure::Internal("補完元型がない".into()))?
                        .clone(),
                ),
                payload: Some(Payload::CompletionSeed {
                    location: location.clone(),
                    parameters: unbound.clone(),
                    bindings: fixed.clone(),
                    roots: roots.clone(),
                    fields: fields.clone(),
                    sources: sources.clone(),
                }),
                rule: Rule::Input {
                    kind: "law",
                    location: location.clone(),
                },
                arguments: fixed
                    .iter()
                    .map(|b| b.value)
                    .chain(roots.iter().copied())
                    .chain(sources.iter().copied())
                    .collect(),
                support: vec![],
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: reasons.clone(),
            })?;
            let ty = if fields.len() == 1 {
                Type::Bool
            } else {
                Type::Tuple(vec![Type::Bool; fields.len()])
            };
            #[cfg(test)]
            let (span, context) = (self.declaration.span, root);
            let assignments = self.environment.finite_values(&ty, &mut |_phase, _index| {
                #[cfg(test)]
                data::observe_actual(span, context, "completion_enum", _index);
            })?;
            let mut members = Vec::new();
            for value in assignments.values {
                self.tick(Checkpoint::FiniteIteration)?;
                members.push(self.value(
                    value,
                    Rule::Construction("domain"),
                    vec![seed],
                    support.clone(),
                    scope.clone(),
                )?);
            }
            let domain = self.push(Node {
                ty: NodeType::Domain,
                payload: Some(Payload::Domain {
                    ty: ty.clone(),
                    elements: members.clone(),
                }),
                rule: Rule::Construction("domain"),
                arguments: std::iter::once(seed)
                    .chain(members.iter().copied())
                    .collect(),
                support: support.clone(),
                evidence: vec![],
                judgment: None,
                scope: scope.clone(),
                reasons: vec![],
            })?;
            let mut cases = Vec::new();
            let mut propositions = Vec::new();
            let mut case_values = Vec::new();
            let mut added = false;
            let mut all_scope = scope.clone();
            let mut all_support = support.clone();
            let mut all_reasons = reasons.clone();
            for member in members {
                self.completion_observe("completion_case", cases.len());
                self.tick(Checkpoint::FiniteIteration)?;
                let values = if fields.len() == 1 {
                    vec![self.graph.scalar(member)?.clone()]
                } else {
                    let Scalar::Tuple(values) = self.graph.scalar(member)? else {
                        return Err(Failure::Internal("補完tupleがない".into()));
                    };
                    values.clone()
                };
                let mut refs = Vec::new();
                for (value, &source) in values.into_iter().zip(&sources) {
                    refs.push(self.value(
                        value,
                        Rule::Construction("domain"),
                        vec![seed, domain, member, source],
                        support.clone(),
                        scope.clone(),
                    )?);
                }
                let index = self.graph.cases.len();
                self.graph.cases.push(super::super::call::CompletionCase {
                    caller: root,
                    seed,
                    domain,
                    member,
                    values: refs.clone(),
                });
                self.completion_reset(super::super::call::Context {
                    case: Some(index),
                    ..root
                });
                let evaluated = if self.is_family(params) {
                    self.family_answer(params, guard, body, role)
                } else {
                    self.answer(params, guard, body, role)
                };
                let mut discovered_roots = Vec::new();
                match &evaluated {
                    Ok(answer) => {
                        discovered_roots.extend(answer.outputs.get("evaluation").copied());
                        discovered_roots.extend(answer.claim);
                    }
                    Err(Failure::NotImplemented { .. }) => {
                        discovered_roots.extend(
                            self.reasons
                                .iter()
                                .flat_map(|r| r.dependencies.iter().copied()),
                        );
                        discovered_roots.extend(self.completed.values().map(|v| v.evaluation));
                    }
                    Err(_) => {}
                }
                self.completion_reset(root);
                self.bindings = fixed.clone();
                let (new_fields, _, _) = self
                    .environment
                    .completion_slots(self.graph, &discovered_roots)?;
                if new_fields.iter().any(|f| !fields.contains(f)) {
                    roots.extend(discovered_roots);
                    roots.sort_by_key(|r| r.0);
                    roots.dedup();
                    added = true;
                    break;
                }
                let answer = evaluated?;
                let evaluation = answer.outputs["evaluation"];
                all_scope.merge(&answer.scope);
                all_support.extend(self.graph.get(evaluation)?.support.iter().cloned());
                all_reasons.extend(self.graph.get(evaluation)?.reasons.iter().cloned());
                all_reasons.extend(answer.reasons);
                if let Some(proposition) = answer.claim {
                    let node = self.graph.get(proposition)?;
                    all_scope.merge(&node.scope);
                    all_support.extend(node.support.iter().cloned());
                    all_reasons.extend(node.reasons.iter().cloned());
                }
                cases.push(evaluation);
                propositions.extend(answer.claim);
                case_values.push(refs);
                self.tick(Checkpoint::FiniteIteration)?;
            }
            if added {
                continue;
            }
            if cases.is_empty() {
                return Err(Failure::Internal("補完case集合が空".into()));
            }
            all_support.sort();
            all_support.dedup();
            crate::observed::environment::completion::canonical_reasons(
                &mut all_reasons,
                self.control,
            )?;
            let result_values: Vec<_> = cases
                .iter()
                .map(|r| match &self.graph.get(*r)?.payload {
                    Some(Payload::Evaluation { value, .. }) => Ok(*value),
                    _ => Err(Failure::Internal("補完caseが評価でない".into())),
                })
                .collect::<Result<_, _>>()?;
            let known = if let Some(first) = result_values[0] {
                let first = self.graph.scalar(first)?.clone();
                let mut same = true;
                for value in &result_values {
                    self.tick(Checkpoint::FiniteIteration)?;
                    same &= match value {
                        Some(value) => {
                            data::equal(self.graph.scalar(*value)?, &first, self.control)?
                        }
                        None => false,
                    };
                }
                same.then_some(first)
            } else {
                None
            };
            let mut evidence = Vec::new();
            if known.is_some() {
                self.completion_observe("completion_coverage", 0);
                self.tick(Checkpoint::FiniteIteration)?;
                evidence.push(
                    self.push(Node {
                        ty: NodeType::Evidence,
                        payload: Some(Payload::FiniteExhaustion {
                            domain,
                            checked: cases.len(),
                            instances: cases.clone(),
                        }),
                        rule: Rule::Construction("evidence"),
                        arguments: std::iter::once(seed)
                            .chain([domain])
                            .chain(cases.iter().copied())
                            .collect(),
                        support: all_support.clone(),
                        evidence: vec![],
                        judgment: None,
                        scope: all_scope.clone(),
                        reasons: vec![],
                    })?,
                );
            } else {
                let mut pair = None;
                for i in 0..cases.len() {
                    for j in i + 1..cases.len() {
                        self.tick(Checkpoint::FiniteIteration)?;
                        if let (Some(a), Some(b)) = (result_values[i], result_values[j])
                            && !data::equal(
                                self.graph.scalar(a)?,
                                self.graph.scalar(b)?,
                                self.control,
                            )?
                        {
                            pair = Some((i, j));
                            break;
                        }
                    }
                    if pair.is_some() {
                        break;
                    }
                }
                if let Some((i, j)) = pair {
                    self.completion_observe("completion_pair", 0);
                    self.tick(Checkpoint::FiniteIteration)?;
                    evidence.push(
                        self.push(Node {
                            ty: NodeType::Evidence,
                            payload: Some(Payload::CompletionPair {
                                fields: fields.clone(),
                                first: case_values[i].clone(),
                                second: case_values[j].clone(),
                                first_result: cases[i],
                                second_result: cases[j],
                            }),
                            rule: Rule::Construction("evidence"),
                            arguments: std::iter::once(seed)
                                .chain([domain, cases[i], cases[j]])
                                .chain(case_values[i].iter().copied())
                                .chain(case_values[j].iter().copied())
                                .collect(),
                            support: all_support.clone(),
                            evidence: vec![],
                            judgment: None,
                            scope: all_scope.clone(),
                            reasons: vec![],
                        })?,
                    );
                }
            }
            self.completion_observe("completion_aggregate", 0);
            self.tick(Checkpoint::FiniteIteration)?;
            let value = known
                .map(|value| {
                    self.push(Node {
                        ty: NodeType::Value(value.ty()),
                        payload: Some(Payload::Scalar(value)),
                        rule: Rule::Construction("evaluation"),
                        arguments: std::iter::once(seed)
                            .chain([domain])
                            .chain(cases.iter().copied())
                            .collect(),
                        support: all_support.clone(),
                        evidence: evidence.clone(),
                        judgment: None,
                        scope: all_scope.clone(),
                        reasons: vec![],
                    })
                })
                .transpose()?;
            let evaluation = self.push_law_evaluation(Node {
                ty: NodeType::Evaluation(
                    self.environment
                        .inputs
                        .law()
                        .expr_type(body)
                        .unwrap()
                        .clone(),
                ),
                payload: Some(Payload::Evaluation {
                    expression: seed,
                    bindings: fixed.clone(),
                    parts: vec![Part {
                        location: location.clone(),
                        value,
                        residual: None,
                        children: cases.clone(),
                    }],
                    value,
                    applicability: "applicable",
                }),
                rule: Rule::Construction("evaluation"),
                arguments: std::iter::once(seed)
                    .chain([domain])
                    .chain(cases.iter().copied())
                    .chain(propositions.iter().copied())
                    .collect(),
                support: all_support.clone(),
                evidence: evidence.clone(),
                judgment: None,
                scope: all_scope.clone(),
                reasons: all_reasons.clone(),
            })?;
            let status = if self.request.kind == QuestionKind::Evaluate {
                if value.is_some() {
                    Decision::Established
                } else {
                    Decision::Undetermined
                }
            } else {
                match self.graph.boolean(value)? {
                    Some(true) => Decision::Established,
                    Some(false) => Decision::Refuted,
                    None => Decision::Undetermined,
                }
            };
            let mut outputs = BTreeMap::from([("evaluation".into(), evaluation)]);
            let claim = if self.request.kind == QuestionKind::Evaluate {
                if let Some(value) = value {
                    outputs.insert("value".into(), value);
                }
                None
            } else {
                let guard = guard
                    .map(|id| {
                        self.push(Node {
                            ty: NodeType::Expression(Type::Bool),
                            payload: Some(Payload::CompletionSeed {
                                location: Location::Law {
                                    span: self.environment.inputs.law().exprs[id].span,
                                },
                                parameters: unbound.clone(),
                                bindings: fixed.clone(),
                                roots: roots.clone(),
                                fields: fields.clone(),
                                sources: sources.clone(),
                            }),
                            rule: Rule::Input {
                                kind: "law",
                                location: Location::Law {
                                    span: self.environment.inputs.law().exprs[id].span,
                                },
                            },
                            arguments: fixed
                                .iter()
                                .map(|b| b.value)
                                .chain(roots.iter().copied())
                                .chain(sources.iter().copied())
                                .collect(),
                            support: vec![],
                            evidence: vec![],
                            judgment: None,
                            scope: scope.clone(),
                            reasons: reasons.clone(),
                        })
                    })
                    .transpose()?;
                let instance = self.push(Node {
                    ty: NodeType::LawInstance,
                    payload: Some(Payload::CompletionInstance {
                        name: self.declaration.name.clone(),
                        role: match role.unwrap() {
                            Role::Required => "required",
                            Role::Optional => "optional",
                        },
                        bindings: fixed.clone(),
                        guard,
                        body: seed,
                        occurrence: Location::Law {
                            span: self.declaration.span,
                        },
                    }),
                    rule: Rule::Construction("law_instance"),
                    arguments: std::iter::once(seed)
                        .chain(guard)
                        .chain(propositions)
                        .collect(),
                    support: all_support.clone(),
                    evidence: vec![],
                    judgment: None,
                    scope: all_scope.clone(),
                    reasons: vec![],
                })?;
                let proposition = self.push(Node {
                    ty: NodeType::Proposition,
                    payload: Some(Payload::Proposition { instance }),
                    rule: Rule::Construction("proposition"),
                    arguments: vec![instance, evaluation],
                    support: all_support,
                    evidence: evidence.clone(),
                    judgment: Some(Judgment {
                        status,
                        evidence: evidence.clone(),
                        reasons: all_reasons.clone(),
                    }),
                    scope: all_scope.clone(),
                    reasons: all_reasons.clone(),
                })?;
                outputs.insert("proposition".into(), proposition);
                Some(proposition)
            };
            return Ok(Answer {
                id: self.request.id.clone(),
                status,
                outputs,
                claim,
                evidence,
                reasons: all_reasons,
                scope: all_scope,
            });
        }
    }
}
