//! 元の型付き出力から公開された構造成分を取り出す。
use super::*;
use crate::observed::projection::{
    ProjectionFailure, ProjectionStep, ProjectionType, resolve_projection_controlled,
};

impl Environment<'_> {
    pub(super) fn answer_projection_unprovided(&self, span: (usize, usize)) -> ValidationFailure {
        ValidationFailure::UnsupportedExpression {
            location: Location::Law { span },
            feature: "未生成出力・動的な構造成分不適合を含むAnswer射影".into(),
        }
    }
    pub(super) fn answer_projection(
        &self,
        graph: &Graph,
        root: NodeRef,
        path: &[ProjectionStep],
        span: (usize, usize),
    ) -> Result<AnswerBinding, ValidationFailure> {
        self.tick()?;
        if root.0 >= self.cutoff.get() {
            return Err("射影の元出力が既出prefixにない".into());
        }
        let original = graph.get(root)?;
        if matches!(&original.payload,Some(Payload::Construction(v)) if v.is_blocked()) {
            return Err(self.answer_projection_unprovided(span));
        }
        let native_type = match &original.payload {
            Some(Payload::Construction(v)) => v.projection_type(),
            _ => None,
        };
        let initial = match (&original.ty, native_type) {
            (_, Some(ty)) => ty,
            (NodeType::Value(t), None) => ProjectionType::Law(t.clone()),
            (NodeType::Evaluation(t), None) => ProjectionType::Evaluation(t.clone()),
            _ => return Err(self.answer_projection_unprovided(span)),
        };
        match resolve_projection_controlled(
            self.inputs.law(),
            initial,
            path,
            &mut self.control.clone(),
        ) {
            Ok(_) => {}
            Err(ProjectionFailure::Interrupted(stop)) => return Err(stop.into()),
            Err(ProjectionFailure::Invalid(_)) => {
                return Ok(AnswerBinding::Inapplicable(root));
            }
        }
        if path.is_empty() {
            return Ok(AnswerBinding::Reference(root));
        }
        if let Some(Payload::Construction(v)) = &original.payload
            && v.projection_type().is_some()
        {
            let Some((selected, used)) = v.project(path) else {
                return Ok(AnswerBinding::Inapplicable(root));
            };
            return self.answer_projection(graph, selected, &path[used..], span);
        }
        let (value, steps) = if matches!(original.ty, NodeType::Evaluation(_)) {
            let Some((ProjectionStep::Field(field), rest)) = path.split_first() else {
                return Err(self.answer_projection_unprovided(span));
            };
            if field != "value" {
                return Ok(AnswerBinding::Inapplicable(root));
            }
            let value = self
                .evaluation(graph, root)?
                .2
                .ok_or_else(|| self.answer_projection_unprovided(span))?;
            (value, rest)
        } else {
            (root, path)
        };
        if value.0 >= self.cutoff.get() {
            return Err("射影の元値が既出prefixにない".into());
        }
        let mut scalar = graph.scalar(value)?;
        let mut represented = Some(value);
        if steps.is_empty() {
            return Ok(AnswerBinding::Reference(value));
        }
        for (index, step) in steps.iter().enumerate() {
            self.tick()?;
            #[cfg(test)]
            data::observe_actual(
                span,
                self.current_context(graph),
                "answer_projection_check_step",
                index,
            );
            if let Scalar::Path(path_value) = scalar {
                let component = match (step, &steps[index + 1..]) {
                    (ProjectionStep::Field(field), []) if field == "source" => {
                        Some(path_value.object())
                    }
                    (ProjectionStep::Field(field), []) if field == "target" => {
                        Some(path_value.target())
                    }
                    (ProjectionStep::Field(field), [ProjectionStep::Index(position)])
                        if field == "generators" =>
                    {
                        path_value.step.as_ref().and_then(|step| {
                            match usize::try_from(*position) {
                                Ok(0) => Some(&step.generator),
                                Ok(index) => step.word_tail.get(index - 1),
                                Err(_) => None,
                            }
                            .cloned()
                        })
                    }
                    _ => None,
                };
                let Some(component) = component else {
                    return Ok(AnswerBinding::Inapplicable(root));
                };
                // 成分表示の各段階で選ばれたPathの元Refから辿る。
                let prior = &graph.nodes[..self.cutoff.get().min(graph.nodes.len())];
                let path_reference = represented.ok_or("Pathの表示元Refがない")?;
                let selected = super::super::path_value::reference(
                    &component,
                    prior,
                    &graph.get(path_reference)?.arguments,
                    &self.control,
                )?;
                #[cfg(test)]
                data::observe_actual(
                    span,
                    self.current_context(graph),
                    "answer_projection_step",
                    index,
                );
                self.tick()?;
                return Ok(AnswerBinding::Reference(selected));
            }
            let has_path = super::super::path_value::contains_path(&scalar.ty(), &self.control)?;
            scalar = match (scalar, step) {
                (
                    Scalar::Tuple(items)
                    | Scalar::List { items, .. }
                    | Scalar::Data { args: items, .. },
                    ProjectionStep::Index(index),
                ) => match usize::try_from(*index)
                    .ok()
                    .and_then(|index| items.get(index))
                {
                    Some(value) => value,
                    None => return Ok(AnswerBinding::Inapplicable(root)),
                },
                (
                    Scalar::Option {
                        value: Some(value), ..
                    },
                    ProjectionStep::Field(field),
                ) if field == "some" => value,
                _ => return Ok(AnswerBinding::Inapplicable(root)),
            };
            represented = if has_path {
                // Pathを含むTは成分をRefで表示する。各親と同じ選択を順に
                // 復元し、同値なPathが複数あっても表示されたRefを保つ。
                let parent = represented.ok_or("非原始成分の表示元Refがない")?;
                Some(super::super::path_value::reference(
                    scalar,
                    &graph.nodes[..self.cutoff.get().min(graph.nodes.len())],
                    &graph.get(parent)?.arguments,
                    &self.control,
                )?)
            } else {
                None
            };
            #[cfg(test)]
            data::observe_actual(
                span,
                self.current_context(graph),
                "answer_projection_step",
                index,
            );
            #[cfg(not(test))]
            let _ = index;
            self.tick()?;
        }
        if let Some(reference) = represented {
            return Ok(AnswerBinding::Reference(reference));
        }
        data::check(scalar, self.inputs.law(), &self.control)?;
        let node = Node {
            ty: NodeType::Value(scalar.ty()),
            payload: Some(Payload::Scalar(scalar.clone())),
            rule: Rule::Projection(path.to_vec()),
            arguments: vec![root],
            support: original.support.clone(),
            evidence: vec![],
            judgment: None,
            scope: original.scope.clone(),
            reasons: vec![],
        };
        self.tick()?;
        Ok(AnswerBinding::Projection(node))
    }

    pub(super) fn validate_answer_projection_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        let Rule::Projection(path) = &node.rule else {
            return Err("射影nodeの規則が違う".into());
        };
        let [root] = node.arguments.as_slice() else {
            return Err("射影の元出力引数数が違う".into());
        };
        if path.is_empty() || root.0 >= limit {
            return Err("射影の全path・既出元出力がない".into());
        }
        let context = self.current_context(graph);
        if context.frame.is_some()
            || context.iteration.is_some()
            || context.instance.is_some()
            || context.case.is_some()
        {
            return Err("射影nodeが元Requestの束縛前contextでない".into());
        }
        let request = self
            .original_requests
            .and_then(|requests| requests.get(context.request))
            .ok_or("射影の元Requestがない")?;
        if matches!(request.kind, QuestionKind::Map | QuestionKind::Compose | QuestionKind::Compare) {
            for constraint in &request.constraints {
                if !matches!(constraint.selector, Selector::Answer { .. }) {
                    continue;
                }
                if let AnswerBinding::Projection(expected) =
                    self.answer_binding(graph, &constraint.selector, (0, 0))?
                    && expected == *node
                    && node.ty == NodeType::Value(constraint.expected.clone())
                {
                    return Ok(());
                }
            }
            return Err("map射影nodeが元on・型・値・支持・Scopeと違う".into());
        }
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration().ok_or("元要求に宣言がない")?)
            .ok_or("射影の元宣言がない")?;
        let params = match &declaration.signature {
            crate::law::model::Signature::View { params, .. }
            | crate::law::model::Signature::Law { params, .. } => params,
            _ => return Err("射影の元宣言がview/Lawでない".into()),
        };
        for argument in &request.arguments {
            self.tick()?;
            if !matches!(argument.value, Selector::Answer { .. }) {
                continue;
            }
            let parameter = params
                .iter()
                .find(|parameter| argument.name == format!("bind.{}", parameter.name))
                .ok_or("射影の元parameterがない")?;
            let expected = match self.answer_binding(graph, &argument.value, parameter.span) {
                Ok(AnswerBinding::Projection(expected)) => expected,
                Ok(AnswerBinding::Reference(_))
                | Ok(AnswerBinding::Inapplicable(_))
                | Err(ValidationFailure::UnsupportedExpression { .. }) => continue,
                Err(failure) => return Err(failure),
            };
            if expected.arguments == node.arguments && expected.rule == node.rule {
                if expected != *node || expected.ty != NodeType::Value(parameter.ty.erase()) {
                    return Err("射影の値・型・支持・Scopeが元出力と違う".into());
                }
                self.tick()?;
                return Ok(());
            }
        }
        Err("射影nodeの元出力/pathが元Requestにない".into())
    }
}
