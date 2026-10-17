//! 元Family式と原始owner slotからの所属Set。提示された集合・owner値だけで認定しない。
use super::*;
use crate::definition::PrimitiveSignature;

pub(in crate::observed) struct OwnedMembers {
    pub enumeration: super::super::finite::Enumeration,
    pub missing: Vec<Fact>,
}

impl Environment<'_> {
    /// 宣言族と式族で同じ原始rosterを読む。既存依存族のobserver名と列挙順を保つ。
    pub(super) fn owned_members(
        &self,
        entity: &str,
        owner: &Scalar,
        fixed: Option<&Scalar>,
        reading: &str,
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<OwnedMembers, ValidationFailure> {
        let mut result = OwnedMembers {
            enumeration: super::super::finite::Enumeration::default(),
            missing: vec![],
        };
        let Scalar::Subject {
            snapshot: owner_snapshot,
            subject: owner_subject,
            ..
        } = owner
        else {
            return Err("依存parameterのownerがRefでない".into());
        };
        let owner_subject_input = self.subject(owner_snapshot, owner_subject)?;
        result
            .enumeration
            .scope
            .merge(&self.scope(owner_subject_input, reading, None)?);
        result.enumeration.support.push(Fact {
            snapshot: owner_snapshot.clone(),
            subject: owner_subject.clone(),
            field: None,
            atom: None,
        });
        let field_name = format!("{entity}.owner");
        for (snapshot_index, snapshot) in self.inputs.archmap().snapshots.iter().enumerate() {
            observer("dependent_snapshot", snapshot_index);
            self.tick()?;
            if snapshot.id != *owner_snapshot {
                continue;
            }
            result
                .enumeration
                .scope
                .snapshots
                .insert(snapshot.id.clone());
            result
                .enumeration
                .scope
                .modes
                .insert(self.origin_mode(&snapshot.origin)?.into());
            for (index, subject) in snapshot.subjects.iter().enumerate() {
                observer("dependent_subject", index);
                self.tick()?;
                let value = Scalar::Subject {
                    snapshot: snapshot.id.clone(),
                    subject: subject.id.clone(),
                    entity: subject.ty.clone(),
                };
                if subject.ty != entity || fixed.is_some_and(|fixed| fixed != &value) {
                    continue;
                }
                result
                    .enumeration
                    .scope
                    .merge(&self.scope(subject, reading, None)?);
                result.enumeration.support.push(Fact {
                    snapshot: snapshot.id.clone(),
                    subject: subject.id.clone(),
                    field: None,
                    atom: None,
                });
                let field = self.field(&snapshot.id, &subject.id, &field_name)?;
                match &field.slot {
                    Slot::Known {
                        value:
                            Value::Ref {
                                snapshot: target_snapshot,
                                subject: target_subject,
                            },
                        atom,
                        origin,
                        ..
                    } => {
                        result.enumeration.scope.merge(&self.scope(
                            subject,
                            reading,
                            Some(origin),
                        )?);
                        result.enumeration.support.push(Fact {
                            snapshot: snapshot.id.clone(),
                            subject: subject.id.clone(),
                            field: Some(field_name.clone()),
                            atom: Some(atom.clone()),
                        });
                        if target_snapshot == owner_snapshot && target_subject == owner_subject {
                            result.enumeration.values.push(value);
                        }
                    }
                    Slot::Missing => {
                        result.enumeration.scope.completions = true;
                        result.missing.push(Fact {
                            snapshot: snapshot.id.clone(),
                            subject: subject.id.clone(),
                            field: Some(field_name.clone()),
                            atom: None,
                        });
                    }
                    _ => return Err("元owner slotがRef型でない".into()),
                }
                self.tick()?;
            }
            self.tick()?;
        }
        // 別snapshotの固定childも明示存在を保持し、空fiberの支持から落とさない。
        if let Some(Scalar::Subject {
            snapshot, subject, ..
        }) = fixed
        {
            let s = self.subject(snapshot, subject)?;
            result
                .enumeration
                .scope
                .merge(&self.scope(s, reading, None)?);
            result.enumeration.support.push(Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: None,
                atom: None,
            });
        }
        Ok(result)
    }

    pub(in crate::observed) fn owned_expression_spec(
        &self,
        id: usize,
    ) -> Result<(String, usize), ValidationFailure> {
        self.tick()?;
        let law = self.inputs.law();
        let expression = law.exprs.get(id).ok_or("元Family ASTがない")?;
        let ExprKind::Family { name, owner } = &expression.kind else {
            return Err("元式がFamilyでない".into());
        };
        let mut resolved = None;
        for info in &law.infos {
            self.tick()?;
            for (span, target) in &info.references {
                self.tick()?;
                if *span == name.span()
                    && resolved
                        .replace(target.clone())
                        .is_some_and(|old| old != *target)
                {
                    return Err("元Familyの静的解決名が一意でない".into());
                }
            }
        }
        let target = resolved.ok_or("元Family名の静的解決がない")?;
        let root = match law
            .definitions
            .declarations
            .get(&target)
            .map(|d| &d.signature)
        {
            Some(
                PrimitiveSignature::Entity {
                    owner: Some(root), ..
                }
                | PrimitiveSignature::Arrow { owner: root, .. },
            ) => root,
            _ => return Err("元Familyがownerを持つentity・arrowでない".into()),
        };
        if law.expr_type(id) != Some(&Type::Set(Box::new(Type::Ref(target.clone()))))
            || law.expr_type(*owner).map(Type::erase) != Some(Type::Ref(root.clone()))
        {
            return Err("元Family・ownerの検査済み型が解決名と違う".into());
        }
        Ok((target, *owner))
    }

    pub(in crate::observed) fn owned_expression_members(
        &self,
        id: usize,
        owner: Option<&Scalar>,
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<OwnedMembers, ValidationFailure> {
        let (entity, owner_id) = self.owned_expression_spec(id)?;
        let declaration = self
            .inputs
            .law()
            .declarations
            .values()
            .find(|d| {
                d.span.0 <= self.inputs.law().exprs[id].span.0
                    && self.inputs.law().exprs[id].span.1 <= d.span.1
            })
            .ok_or("元Familyの宣言がない")?;
        let mut result = if let Some(owner) = owner {
            if Some(owner.ty()) != self.inputs.law().expr_type(owner_id).map(Type::erase) {
                return Err("元Family owner値型が違う".into());
            }
            self.owned_members(&entity, owner, None, &declaration.reading, observer)?
        } else {
            let mut enumeration = super::super::finite::Enumeration::default();
            enumeration.scope.completions = true;
            OwnedMembers {
                enumeration,
                missing: vec![],
            }
        };
        result.enumeration.support.sort();
        result.enumeration.support.dedup();
        result.missing.sort();
        result.missing.dedup();
        self.tick()?;
        Ok(result)
    }

    pub(super) fn scoped_owned_family(
        &self,
        id: usize,
        owner: SourceValue,
        reading: &str,
    ) -> Result<SourceValue, ValidationFailure> {
        let (entity, _) = self.owned_expression_spec(id)?;
        let roster =
            self.owned_expression_members(id, owner.known_value.as_ref(), &mut |_, _| {})?;
        let mut scope = owner.scope;
        scope.readings.insert(reading.into());
        scope.merge(&roster.enumeration.scope);
        let mut support = owner.support;
        support.extend(roster.enumeration.support);
        support.sort();
        support.dedup();
        let known_value = if owner.known_value.is_some() && roster.missing.is_empty() {
            Some(data::set(
                Type::Ref(entity),
                &roster.enumeration.values,
                &self.control,
            )?)
        } else {
            None
        };
        let scalar_scope = known_value.as_ref().map(|_| scope.clone());
        Ok(SourceValue {
            symbolic: None,
            comparison: None,
            affine: None,
            scope,
            known_value,
            support,
            scalar_scope,
        })
    }

    fn owned_family_inputs(
        &self,
        graph: &Graph,
        source: NodeRef,
        owner_evaluation: NodeRef,
        id: usize,
        limit: usize,
    ) -> Result<SourceAnalysis, ValidationFailure> {
        let (_, owner_id) = self.owned_expression_spec(id)?;
        let span = self.inputs.law().exprs[id].span;
        let context = self.current_context(graph);
        if source.0 >= limit
            || owner_evaluation.0 >= limit
            || graph.context_at(source.0) != context
            || graph.context_at(owner_evaluation.0) != context
        {
            return Err("Familyの元Source・owner評価が既出同Contextでない".into());
        }
        let own = graph.get(source)?;
        let Some(Payload::Expression {
            location: Location::Law { span: own_span },
            parameters,
            bindings,
        }) = &own.payload
        else {
            return Err("Familyに元Sourceがない".into());
        };
        if *own_span != span
            || !parameters.is_empty()
            || own.arguments != self.source_arguments(graph, span, bindings)?
            || own.ty
                != NodeType::Expression(
                    self.inputs
                        .law()
                        .expr_type(id)
                        .ok_or("元Family型がない")?
                        .clone(),
                )
        {
            return Err("Familyのown Source・元束縛・型が違う".into());
        }
        self.validate_at(graph, own, source.0)?;
        let (owner_source, owner_bindings, value) = self.evaluation(graph, owner_evaluation)?;
        if self.expression_span(graph, owner_source)? != self.inputs.law().exprs[owner_id].span
            || owner_bindings != bindings
            || graph.get(owner_evaluation)?.ty
                != NodeType::Evaluation(
                    self.inputs
                        .law()
                        .expr_type(owner_id)
                        .ok_or("元owner型がない")?
                        .clone(),
                )
            || self.actual_evaluation(graph, owner_id, bindings)? != owner_evaluation
        {
            return Err("Familyの実owner子評価が元AST・producer・束縛と違う".into());
        }
        let original_owner =
            self.analyze_source(graph, self.inputs.law().exprs[owner_id].span, bindings)?;
        let actual_owner = value.map(|r| graph.scalar(r)).transpose()?;
        if original_owner.known_value.as_ref() != actual_owner {
            return Err("Familyの実owner値が元入力と違う".into());
        }
        self.resolve_analysis(
            graph,
            self.analyze_source(graph, span, bindings)?,
            &[owner_evaluation],
        )
    }

    pub(super) fn owned_family_scalar_analysis(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<SourceAnalysis, ValidationFailure> {
        let Rule::Input {
            kind: "law",
            location: Location::Law { span },
        } = &node.rule
        else {
            return Err("Family Scalarに元Law出現がない".into());
        };
        let id = *self
            .expressions
            .get(span)
            .ok_or("Family Scalarの元ASTがない")?;
        let [source, owner_evaluation] = node.arguments.as_slice() else {
            return Err("Family Scalarの元Source・実owner評価辺がない".into());
        };
        let analysis = self.owned_family_inputs(graph, *source, *owner_evaluation, id, limit)?;
        let bindings = self.expression_bindings(graph, *source)?;
        if !self.field_source_producer_matches(graph, node, limit, *source, bindings)?
            || !matches!(&node.payload,Some(Payload::Scalar(value)) if analysis.known_value.as_ref()==Some(value))
            || node.ty
                != NodeType::Value(
                    self.inputs
                        .law()
                        .expr_type(id)
                        .ok_or("元Family型がない")?
                        .clone(),
                )
            || node.support != analysis.support
            || analysis.scalar_scope.as_ref() != Some(&node.scope)
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
            || node.judgment.is_some()
        {
            return Err("Family Scalarの元集合・支持・Scope・実producerが違う".into());
        }
        Ok(analysis)
    }

    pub(super) fn validate_owned_family_evaluation(
        &self,
        graph: &Graph,
        node: &Node,
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
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &graph.get(*expression)?.payload
        else {
            return Ok(false);
        };
        let span = *span;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(false);
        };
        if !matches!(&self.inputs.law().exprs[id].kind, ExprKind::Family { .. }) {
            return Ok(false);
        }
        if parts.len() != 1
            || parts[0].children.len() != 1
            || parts[0].location != (Location::Law { span })
            || parts[0].value != *value
            || parts[0].residual.is_some()
            || *applicability != "applicable"
            || bindings != self.expression_bindings(graph, *expression)?
        {
            return Err("Family評価の元part・束縛・owner子が違う".into());
        }
        let owner_evaluation = parts[0].children[0];
        let analysis = self.owned_family_inputs(graph, *expression, owner_evaluation, id, limit)?;
        let expected_arguments: Vec<_> = std::iter::once(*expression)
            .chain(std::iter::once(owner_evaluation))
            .chain(*value)
            .collect();
        if node.arguments != expected_arguments
            || !matches!(node.rule, Rule::Construction("evaluation"))
            || node.ty
                != NodeType::Evaluation(
                    self.inputs
                        .law()
                        .expr_type(id)
                        .ok_or("元Family型がない")?
                        .clone(),
                )
            || node.scope != analysis.scope
            || !graph
                .get(*expression)?
                .scope
                .source_compatible(&analysis.scope)
            || node.support != analysis.support
            || !node.evidence.is_empty()
            || node.judgment.is_some()
        {
            return Err("Family評価の元規則・型・Scope・支持・辺が違う".into());
        }
        match (value, analysis.known_value.as_ref()) {
            (Some(reference), Some(expected)) => {
                if reference.0 >= limit
                    || graph.get(*reference)?.arguments != [*expression, owner_evaluation]
                    || graph.context_at(reference.0) != self.current_context(graph)
                    || graph.scalar(*reference)? != expected
                    || !matches!(&graph.get(*reference)?.rule,Rule::Input {kind:"law",location:Location::Law {span:actual}} if *actual==span)
                {
                    return Err("Family評価の集合値が元出現・owner評価に接続しない".into());
                }
                self.validate_at(graph, graph.get(*reference)?, reference.0)?;
            }
            (None, None) => {}
            _ => return Err("Family評価の確定・欠測が元入力と違う".into()),
        }
        let (_, _, owner_value) = self.evaluation(graph, owner_evaluation)?;
        let members = self.owned_expression_members(
            id,
            owner_value.map(|r| graph.scalar(r)).transpose()?,
            &mut |_, _| {},
        )?;
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("Family評価の元Requestがない")?;
        let mut reasons = graph.get(owner_evaluation)?.reasons.clone();
        if !members.missing.is_empty() {
            reasons.push(Reason {
                kind: ReasonKind::Missing,
                request: request.id.clone(),
                dependencies: vec![*expression],
                missing: members.missing.clone(),
                location: Some(Location::Law { span }),
            });
        }
        if owner_value.is_none() || !members.missing.is_empty() {
            reasons.push(Reason {
                kind: ReasonKind::UnsupportedAlgorithm {
                    question: request.kind,
                    operand_types: vec![
                        self.inputs
                            .law()
                            .expr_type(id)
                            .ok_or("元Family型がない")?
                            .clone(),
                    ],
                    method: "unresolved_owned_expression_family".into(),
                },
                request: request.id.clone(),
                dependencies: vec![*expression],
                missing: vec![],
                location: Some(Location::Law { span }),
            });
        }
        sort_reasons(&mut reasons);
        if node.reasons.iter().map(Reason::wire).collect::<Vec<_>>()
            != reasons.iter().map(Reason::wire).collect::<Vec<_>>()
        {
            return Err("Family評価が元owner欠測・未実装理由を保持しない".into());
        }
        Ok(true)
    }
}
