//! 元の公開selectorが実値に適合しない場合の構成条件。
use super::owned_binding::ConditionInput;
use super::*;

#[derive(Clone, Debug)]
pub(in crate::observed) struct ProjectionFailurePlan {
    pub context: super::super::call::Context,
    pub parameter: String,
    pub root: NodeRef,
    pub producer: String,
    pub location: Option<Location>,
    pub inputs: Vec<ConditionInput>,
    pub scope: Scope,
    pub support: Vec<Fact>,
}
impl Environment<'_> {
    pub(in crate::observed) fn projection_failure_plans(
        &self,
        graph: &Graph,
        request: &Request,
    ) -> Result<Vec<ProjectionFailurePlan>, ValidationFailure> {
        if !request
            .arguments
            .iter()
            .any(|a| matches!(a.value, Selector::Answer { .. }))
        {
            return Ok(vec![]);
        }
        let index = self
            .original_requests
            .and_then(|rs| rs.iter().position(|r| r == request))
            .ok_or("射影条件のRequestが元入力にない")?;
        let previous = self.context.replace(Some(super::super::call::Context {
            request: index,
            frame: None,
            iteration: None,
            instance: None,
            case: None,
        }));
        let result = self.projection_failure_plans_current(graph, request);
        self.context.set(previous);
        result
    }
    fn projection_failure_plans_current(
        &self,
        graph: &Graph,
        request: &Request,
    ) -> Result<Vec<ProjectionFailurePlan>, ValidationFailure> {
        self.tick()?;
        if request.kind == QuestionKind::Map {
            let mut plans = vec![];
            for constraint in &request.constraints {
                let Selector::Answer { id, .. } = &constraint.selector else {
                    continue;
                };
                let root = match self.answer_binding(graph, &constraint.selector, (0, 0)) {
                    Ok(AnswerBinding::Inapplicable(root)) => Some(root),
                    Ok(AnswerBinding::Reference(r))
                        if graph.get(r)?.ty != NodeType::Value(constraint.expected.clone()) =>
                    {
                        Some(r)
                    }
                    Ok(AnswerBinding::Projection(node))
                        if node.ty != NodeType::Value(constraint.expected.clone()) =>
                    {
                        node.arguments.first().copied()
                    }
                    Err(ValidationFailure::UnsupportedExpression { .. }) => None,
                    Err(error) => return Err(error),
                    _ => None,
                };
                if let Some(root) = root {
                    let original = graph.get(root)?;
                    plans.push(ProjectionFailurePlan {
                        context: self.current_context(graph),
                        parameter: constraint.parameter.clone(),
                        root,
                        producer: id.clone(),
                        location: None,
                        inputs: vec![ConditionInput::Reference(root)],
                        scope: original.scope.clone(),
                        support: original.support.clone(),
                    });
                }
            }
            return Ok(plans);
        }
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration().ok_or("元要求に宣言がない")?)
            .ok_or("射影条件の元宣言がない")?;
        let params = match &declaration.signature {
            crate::law::model::Signature::View { params, .. }
            | crate::law::model::Signature::Law { params, .. } => params,
            _ => return Err("射影条件の元宣言がview/Lawでない".into()),
        };
        let mut plans = vec![];
        for parameter in params {
            self.tick()?;
            if parameter.ty != parameter.ty.erase()
                && !self.fixed_owned_binding(request, parameter)?
                && !self.deferred_owned_binding(request, parameter)?
                && request
                    .constraints
                    .iter()
                    .any(|c| c.parameter == parameter.name && c.dynamic)
            {
                continue;
            }
            let Some(argument) = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", parameter.name))
            else {
                // Lawの自由parameterを構成条件の値入力へ補わない。
                if request.kind != QuestionKind::Check {
                    return Err("射影条件の元view束縛がない".into());
                }
                continue;
            };
            let Selector::Answer { id, .. } = &argument.value else {
                continue;
            };
            let plan = match self.answer_binding(graph, &argument.value, parameter.span) {
                Ok(plan) => plan,
                Err(ValidationFailure::UnsupportedExpression { .. }) => continue,
                Err(error) => return Err(error),
            };
            let root = match plan {
                AnswerBinding::Inapplicable(root) => Some(root),
                AnswerBinding::Reference(reference)
                    if graph.get(reference)?.ty != NodeType::Value(parameter.ty.erase()) =>
                {
                    Some(reference)
                }
                AnswerBinding::Projection(node)
                    if node.ty != NodeType::Value(parameter.ty.erase()) =>
                {
                    node.arguments.first().copied()
                }
                _ => None,
            };
            if let Some(root) = root {
                let original = graph.get(root)?;
                plans.push(ProjectionFailurePlan {
                    context: self.current_context(graph),
                    parameter: parameter.name.clone(),
                    root,
                    producer: id.clone(),
                    location: Some(Location::Law {
                        span: parameter.span,
                    }),
                    inputs: vec![ConditionInput::Reference(root)],
                    scope: original.scope.clone(),
                    support: original.support.clone(),
                });
            }
            self.tick()?;
        }
        for parameter in params {
            self.tick()?;
            if plans.iter().any(|p| p.parameter == parameter.name) {
                continue;
            }
            let plan = match self.owned_binding_plan(graph, request, parameter) {
                Ok(plan) => plan,
                Err(ValidationFailure::UnsupportedExpression { .. }) => continue,
                Err(error) => return Err(error),
            };
            if let Some(plan) = plan
                && plan.checks.failure.is_some()
            {
                let root = *plan
                    .dependencies
                    .first()
                    .ok_or("所属条件の元Answerがない")?;
                plans.push(ProjectionFailurePlan {
                    context: self.current_context(graph),
                    parameter: parameter.name.clone(),
                    root,
                    producer: plan.producer,
                    location: Some(Location::Law {
                        span: parameter.span,
                    }),
                    inputs: plan.condition_inputs,
                    scope: plan.checks.scope,
                    support: plan.checks.support,
                });
            }
        }
        Ok(plans)
    }

    pub(in crate::observed) fn projection_failure_reasons(
        &self,
        graph: &Graph,
        request: &Request,
    ) -> Result<(Vec<Reason>, Scope), ValidationFailure> {
        let current = self
            .original_requests
            .and_then(|rs| rs.iter().position(|r| r == request))
            .ok_or("射影条件の元Requestがない")?;
        let mut reasons = vec![];
        let mut scope = Scope::default();
        for plan in self.projection_failure_plans(graph, request)? {
            self.tick()?;
            let plan_dependencies = self.projection_failure_dependencies(graph, &plan)?;
            let mut selected = None;
            for (index, node) in graph
                .nodes
                .iter()
                .enumerate()
                .take(self.cutoff.get().min(graph.nodes.len()))
            {
                self.tick()?;
                if graph.context_at(index).request == current
                    && matches!(&node.rule, Rule::ProjectionCheck { parameter, part: ProjectionCheckPart::Condition } if parameter == &plan.parameter)
                {
                    if selected.is_some() {
                        return Err("同じ元射影条件が重複している".into());
                    }
                    self.validate_at(graph, node, index)?;
                    selected = Some(NodeRef(index));
                }
            }
            let condition = selected.ok_or("不適合な元射影の条件反証がない")?;
            scope.merge(&plan.scope);
            reasons.push(Reason {
                kind: ReasonKind::ConditionFailed {
                    condition,
                    construction: "projection",
                },
                request: request.id.clone(),
                dependencies: plan_dependencies.clone(),
                missing: vec![],
                location: plan.location.clone(),
            });
            let mut dependencies = plan_dependencies;
            dependencies.push(condition);
            dependencies.extend(graph.get(condition)?.evidence.iter().copied());
            dependencies.sort_by_key(|r| r.0);
            dependencies.dedup();
            reasons.push(Reason {
                kind: ReasonKind::DependencyBlocked {
                    request: plan.producer,
                },
                request: request.id.clone(),
                dependencies,
                missing: vec![],
                location: plan.location.clone(),
            });
        }
        Ok((reasons, scope))
    }
    pub(in crate::observed) fn commit_projection_conditions(
        &self,
        graph: &mut Graph,
        request: &Request,
    ) -> Result<(), ValidationFailure> {
        for plan in self.projection_failure_plans(graph, request)? {
            use ProjectionCheckPart::*;
            let mut values = vec![];
            for part in [Name, Actual, Required, Evidence, Condition] {
                self.control.clone().checkpoint(Checkpoint::Projection)?;
                let prior = match part {
                    Name | Actual | Required => vec![],
                    Evidence => values.clone(),
                    Condition => vec![values[0], values[3]],
                };
                let node = self.projection_failure_node(graph, &plan, part, &prior)?;
                self.validate(graph, &node)?;
                values.push(graph.push(node)?);
                self.control.clone().checkpoint(Checkpoint::Projection)?;
            }
        }
        Ok(())
    }

    // 同Requestの既出leafだけを元subject selectorの型・値・支持・Scopeから復元する。
    pub(in crate::observed) fn projection_subject_input(
        &self,
        graph: &Graph,
        expected: &Node,
        context: super::super::call::Context,
    ) -> Result<Option<NodeRef>, ValidationFailure> {
        for (index, node) in graph
            .nodes
            .iter()
            .enumerate()
            .take(self.cutoff.get().min(graph.nodes.len()))
        {
            self.tick()?;
            if graph.context_at(index) == context && node == expected {
                self.validate_at(graph, node, index)?;
                self.tick()?;
                return Ok(Some(NodeRef(index)));
            }
            self.tick()?;
        }
        Ok(None)
    }

    pub(in crate::observed) fn projection_failure_dependencies(
        &self,
        graph: &Graph,
        plan: &ProjectionFailurePlan,
    ) -> Result<Vec<NodeRef>, ValidationFailure> {
        let mut dependencies = vec![];
        for input in &plan.inputs {
            self.tick()?;
            let root = match input {
                ConditionInput::Reference(root) => {
                    graph.get(*root)?;
                    *root
                }
                ConditionInput::Subject(node) => self
                    .projection_subject_input(graph, node, plan.context)?
                    .ok_or("所属条件の元subject入力がない")?,
            };
            if !dependencies.contains(&root) {
                dependencies.push(root);
            }
            self.tick()?;
        }
        Ok(dependencies)
    }

    pub(in crate::observed) fn projection_failure_node(
        &self,
        graph: &Graph,
        plan: &ProjectionFailurePlan,
        part: ProjectionCheckPart,
        prior: &[NodeRef],
    ) -> Result<Node, ValidationFailure> {
        self.tick()?;
        let dependencies = self.projection_failure_dependencies(graph, plan)?;
        let mut node = Node {
            ty: NodeType::Value(Type::Text),
            payload: None,
            rule: Rule::ProjectionCheck {
                parameter: plan.parameter.clone(),
                part,
            },
            arguments: dependencies.clone(),
            support: plan.support.clone(),
            scope: plan.scope.clone(),
            evidence: vec![],
            judgment: None,
            reasons: vec![],
        };
        use ProjectionCheckPart::*;
        match (part, prior) {
            (Name, []) => node.payload = Some(Payload::Scalar(Scalar::Text("projection".into()))),
            (Actual, []) | (Required, []) => {
                node.ty = NodeType::Value(Type::Bool);
                node.payload = Some(Payload::Scalar(Scalar::Bool(part == Required)));
            }
            (Evidence, [name, actual, required]) => {
                node.ty = NodeType::Evidence;
                node.arguments.extend([*name, *actual, *required]);
                node.payload = Some(Payload::ProjectionCounterexample {
                    left: *actual,
                    right: *required,
                    facts: plan.support.clone(),
                });
            }
            (Condition, [name, evidence]) => {
                node.ty = NodeType::Proposition;
                node.arguments.extend([*name, *evidence]);
                node.payload = Some(Payload::ProjectionCondition {
                    name: *name,
                    inputs: dependencies.clone(),
                });
                node.evidence = vec![*evidence];
                node.judgment = Some(Judgment {
                    status: Decision::Refuted,
                    evidence: vec![*evidence],
                    reasons: vec![],
                });
            }
            _ => return Err("射影条件の構成part・引数数が違う".into()),
        }
        self.tick()?;
        Ok(node)
    }

    pub(super) fn validate_projection_check(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let Rule::ProjectionCheck { parameter, part } = &node.rule else {
            return Ok(false);
        };
        self.tick()?;
        let context = self.current_context(graph);
        if context.frame.is_some()
            || context.iteration.is_some()
            || context.instance.is_some()
            || context.case.is_some()
        {
            return Err("射影条件が元Requestの束縛前contextでない".into());
        }
        let request = self
            .original_requests
            .and_then(|rs| rs.get(context.request))
            .ok_or("射影条件の元Requestがない")?;
        let plan = self
            .projection_failure_plans(graph, request)?
            .into_iter()
            .find(|p| &p.parameter == parameter)
            .ok_or("元selectorに実値射影の不適合がない")?;
        if plan.root.0 >= limit {
            return Err("射影条件のrootが未出".into());
        }
        let dependencies = self.projection_failure_dependencies(graph, &plan)?;
        let prior = node
            .arguments
            .strip_prefix(dependencies.as_slice())
            .ok_or("射影条件の元root・実依存辺が違う")?;
        if dependencies.iter().any(|r| r.0 >= limit) {
            return Err("射影条件の依存辺が未出".into());
        }
        for &reference in prior {
            self.tick()?;
            if reference.0 >= limit || graph.context_at(reference.0) != context {
                return Err("射影条件の証拠が既出同Requestでない".into());
            }
            let original = graph.get(reference)?;
            let Rule::ProjectionCheck {
                parameter: original_parameter,
                ..
            } = &original.rule
            else {
                return Err("射影条件の実証拠が元selectorに属さない".into());
            };
            if original_parameter != parameter {
                return Err("射影条件の証拠parameterが違う".into());
            }
            self.validate_at(graph, original, reference.0)?;
        }
        let expected = self.projection_failure_node(graph, &plan, *part, prior)?;
        if &expected != node {
            return Err("射影条件の型・値・実辺・支持・Scope・反証が元入力と違う".into());
        }
        graph.projection_check_shape(node)?;
        Ok(true)
    }
}

impl Graph {
    pub(in crate::observed) fn projection_check_shape(
        &self,
        node: &Node,
    ) -> Result<(), ValidationFailure> {
        use ProjectionCheckPart::*;
        let Rule::ProjectionCheck { parameter, part } = &node.rule else {
            return Err("射影条件の構成規則がない".into());
        };
        let expect_part = |reference: NodeRef, required| -> Result<(), ValidationFailure> {
            if self.get(reference)?.rule
                != (Rule::ProjectionCheck {
                    parameter: parameter.clone(),
                    part: required,
                })
            {
                return Err("射影条件の証拠partが違う".into());
            }
            Ok(())
        };
        let extra = match part {
            Name | Actual | Required => 0,
            Evidence => 3,
            Condition => 2,
        };
        let count = node
            .arguments
            .len()
            .checked_sub(extra)
            .filter(|n| *n > 0)
            .ok_or("射影条件に元rootがない")?;
        let (roots, prior) = node.arguments.split_at(count);
        match (part, &node.payload, prior) {
            (Name, Some(Payload::Scalar(Scalar::Text(name))), []) if name == "projection" => {}
            (Actual | Required, Some(Payload::Scalar(Scalar::Bool(value))), [])
                if *value == (*part == Required) => {}
            (
                Evidence,
                Some(Payload::ProjectionCounterexample { left, right, facts }),
                [name, actual, required],
            ) => {
                expect_part(*name, Name)?;
                expect_part(*actual, Actual)?;
                expect_part(*required, Required)?;
                if left != actual
                    || right != required
                    || facts != &node.support
                    || node.ty != NodeType::Evidence
                    || self.get(*name)?.arguments != roots
                    || self.get(*actual)?.arguments != roots
                    || self.get(*required)?.arguments != roots
                    || self.scalar(*actual)? != &Scalar::Bool(false)
                    || self.scalar(*required)? != &Scalar::Bool(true)
                {
                    return Err("射影反例の実成否・要求・元rootが違う".into());
                }
            }
            (
                Condition,
                Some(Payload::ProjectionCondition { name, inputs }),
                [construction, evidence],
            ) => {
                expect_part(*construction, Name)?;
                expect_part(*evidence, Evidence)?;
                let proof = self.get(*evidence)?;
                if name != construction
                    || inputs.as_slice() != roots
                    || node.ty != NodeType::Proposition
                    || proof.arguments.len() != roots.len() + 3
                    || proof.arguments[..roots.len()] != *roots
                    || proof.arguments[roots.len()] != *name
                    || node.evidence != [*evidence]
                    || node.judgment
                        != Some(Judgment {
                            status: Decision::Refuted,
                            evidence: vec![*evidence],
                            reasons: vec![],
                        })
                    || proof.scope != node.scope
                    || proof.support != node.support
                {
                    return Err("射影条件のconstructible・元root・反証が違う".into());
                }
            }
            _ => return Err("射影条件のpayload・型・引数数が違う".into()),
        }
        Ok(())
    }
}
