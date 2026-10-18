//! 元の公開selectorが実値に適合しない場合の構成条件。
use super::*;

#[derive(Clone, Debug)]
pub(in crate::observed) struct ProjectionFailurePlan {
    pub parameter: String,
    pub root: NodeRef,
    pub producer: String,
    pub span: (usize, usize),
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
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
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
                plans.push(ProjectionFailurePlan {
                    parameter: parameter.name.clone(),
                    root,
                    producer: id.clone(),
                    span: parameter.span,
                });
            }
            self.tick()?;
        }
        Ok(plans)
    }

    pub(in crate::observed) fn projection_failure_node(
        &self,
        graph: &Graph,
        plan: &ProjectionFailurePlan,
        part: ProjectionCheckPart,
        prior: &[NodeRef],
    ) -> Result<Node, ValidationFailure> {
        self.tick()?;
        let root = graph.get(plan.root)?;
        let mut node = Node {
            ty: NodeType::Value(Type::Text),
            payload: None,
            rule: Rule::ProjectionCheck {
                parameter: plan.parameter.clone(),
                part,
            },
            arguments: vec![plan.root],
            support: root.support.clone(),
            scope: root.scope.clone(),
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
                    facts: root.support.clone(),
                });
            }
            (Condition, [name, evidence]) => {
                node.ty = NodeType::Proposition;
                node.arguments.extend([*name, *evidence]);
                node.payload = Some(Payload::ProjectionCondition {
                    name: *name,
                    root: plan.root,
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
        let [root, prior @ ..] = node.arguments.as_slice() else {
            return Err("射影条件のroot引数がない".into());
        };
        if *root != plan.root {
            return Err("射影条件の元rootが違う".into());
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
        match (part, &node.payload, node.arguments.as_slice()) {
            (Name, Some(Payload::Scalar(Scalar::Text(name))), [_]) if name == "projection" => {}
            (Actual | Required, Some(Payload::Scalar(Scalar::Bool(value))), [_])
                if *value == (*part == Required) => {}
            (
                Evidence,
                Some(Payload::ProjectionCounterexample { left, right, facts }),
                [root, name, actual, required],
            ) => {
                expect_part(*name, Name)?;
                expect_part(*actual, Actual)?;
                expect_part(*required, Required)?;
                if left != actual
                    || right != required
                    || facts != &node.support
                    || node.ty != NodeType::Evidence
                    || self.get(*name)?.arguments != [*root]
                    || self.get(*actual)?.arguments != [*root]
                    || self.get(*required)?.arguments != [*root]
                    || self.scalar(*actual)? != &Scalar::Bool(false)
                    || self.scalar(*required)? != &Scalar::Bool(true)
                {
                    return Err("射影反例の実成否・要求・元rootが違う".into());
                }
            }
            (
                Condition,
                Some(Payload::ProjectionCondition { name, root }),
                [original, construction, evidence],
            ) => {
                expect_part(*construction, Name)?;
                expect_part(*evidence, Evidence)?;
                let proof = self.get(*evidence)?;
                if name != construction
                    || root != original
                    || node.ty != NodeType::Proposition
                    || proof.arguments.len() != 4
                    || proof.arguments[..2] != [*root, *name]
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
