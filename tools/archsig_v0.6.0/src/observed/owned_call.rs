//! Owned参照とcontainerのcall境界を元署名・実引数・原始owner事実から検査する。
use super::super::term::affine::Value as PartialValue;
use super::*;
use crate::law::model::{Declaration, Signature};

#[derive(Default)]
pub(in crate::observed) struct Checks {
    pub scope: Scope,
    pub support: Vec<Fact>,
    pub failure: Option<(Scalar, Scalar)>,
    pub blocked: bool,
    // 所属が未確定の実owner slot。値へ補わず、呼出しと補完の元Sourceへ残す。
    pub missing: Vec<Fact>,
}

impl Environment<'_> {
    fn call_type_has_owned(&self, ty: &Type) -> Result<bool, ValidationFailure> {
        let mut pending = vec![ty];
        while let Some(ty) = pending.pop() {
            self.tick()?;
            match ty {
                Type::Owned(..) => return Ok(true),
                Type::Tuple(items) => pending.extend(items),
                Type::List(item) | Type::Set(item) | Type::Option(item) => pending.push(item),
                Type::Map(from, to) => {
                    pending.push(from);
                    pending.push(to);
                }
                _ => {}
            }
        }
        Ok(false)
    }

    pub(in crate::observed) fn owned_call_value_check(
        &self,
        ty: &Type,
        value: &PartialValue,
        values: &BTreeMap<&str, Option<&Scalar>>,
        reading: &str,
        span: (usize, usize),
        checks: &mut Checks,
    ) -> Result<(), ValidationFailure> {
        enum Member<'a> {
            Known(&'a Scalar),
            Partial(&'a PartialValue),
            // 各既知leafの検査後、空表も含め完全な期待始域へ照合する。
            MapDomain(&'a [(Scalar, Scalar)]),
        }
        let mut pending = vec![(ty, Member::Partial(value))];
        while let Some((ty, member)) = pending.pop() {
            self.tick()?;
            if !self.call_type_has_owned(ty)? {
                continue;
            }
            let member = match member {
                Member::Partial(PartialValue::Known(v)) => Member::Known(v),
                other => other,
            };
            match (ty, member) {
                (Type::Owned(..), Member::Known(value)) => {
                    self.owned_reference_check(ty, Some(value), values, reading, span, checks)?;
                }
                (Type::Owned(..), Member::MapDomain(pairs)) => {
                    self.owned_call_map_domain(ty, pairs, values, reading, span, checks)?;
                }
                (
                    Type::Map(from, to),
                    Member::Known(Scalar::Map {
                        domain,
                        codomain,
                        pairs,
                    }),
                ) if *domain == from.erase() && *codomain == to.erase() => {
                    if matches!(from.as_ref(), Type::Owned(..)) {
                        pending.push((from, Member::MapDomain(pairs)));
                    }
                    for (key, image) in pairs.iter().rev() {
                        self.tick()?;
                        pending.push((to, Member::Known(image)));
                        pending.push((from, Member::Known(key)));
                    }
                }
                // 未生成memberを補わず、後続の既知不適合は引き続き探す。
                (_, Member::Partial(PartialValue::Unsupported(_))) => checks.blocked = true,
                (Type::Tuple(types), Member::Known(Scalar::Tuple(items)))
                    if types.len() == items.len() =>
                {
                    for (ty, value) in types.iter().zip(items).rev() {
                        self.tick()?;
                        pending.push((ty, Member::Known(value)));
                    }
                }
                (Type::Tuple(types), Member::Partial(PartialValue::Tuple(items)))
                    if types.len() == items.len() =>
                {
                    for (ty, value) in types.iter().zip(items).rev() {
                        self.tick()?;
                        pending.push((ty, Member::Partial(value)));
                    }
                }
                (Type::List(ty), Member::Known(Scalar::List { element, items }))
                | (Type::Set(ty), Member::Known(Scalar::Set { element, items }))
                    if *element == ty.erase() =>
                {
                    for value in items.iter().rev() {
                        self.tick()?;
                        pending.push((ty, Member::Known(value)));
                    }
                }
                (Type::List(ty), Member::Partial(PartialValue::List { element, items }))
                | (Type::Set(ty), Member::Partial(PartialValue::SetLiteral { element, items }))
                    if *element == ty.erase() =>
                {
                    for value in items.iter().rev() {
                        self.tick()?;
                        pending.push((ty, Member::Partial(value)));
                    }
                }
                (Type::Option(ty), Member::Known(Scalar::Option { element, value }))
                    if *element == ty.erase() =>
                {
                    if let Some(value) = value {
                        pending.push((ty, Member::Known(value)));
                    }
                }
                (Type::Option(ty), Member::Partial(PartialValue::Option { element, value }))
                    if *element == ty.erase() =>
                {
                    if let Some(value) = value {
                        pending.push((ty, Member::Partial(value)));
                    }
                }
                _ => return Err("Owned callの複合memberが元署名型と違う".into()),
            }
            if checks.failure.is_some() {
                break;
            }
            self.tick()?;
        }
        Ok(())
    }

    fn owned_call_map_domain(
        &self,
        ty: &Type,
        pairs: &[(Scalar, Scalar)],
        values: &BTreeMap<&str, Option<&Scalar>>,
        reading: &str,
        span: (usize, usize),
        checks: &mut Checks,
    ) -> Result<(), ValidationFailure> {
        let Type::Owned(entity, owner_name) = ty else {
            return Err("Map所属域の元型がOwnedでない".into());
        };
        self.tick()?;
        let unsupported = || ValidationFailure::UnsupportedExpression {
            location: Location::Law { span },
            feature: "未確定owner族を持つMap呼出しの全域条件".into(),
        };
        let owner = values
            .get(owner_name.as_str())
            .and_then(|v| *v)
            .ok_or_else(|| unsupported())?;
        let members =
            self.owned_members(entity, owner, None, reading, &mut |operation, index| {
                #[cfg(test)]
                if operation == "dependent_subject" {
                    data::observe_actual(
                        span,
                        self.context.get().unwrap_or_default(),
                        "owned_call_map_domain_roster",
                        index,
                    );
                }
                #[cfg(not(test))]
                let _ = (operation, index);
            })?;
        checks.scope.merge(&members.enumeration.scope);
        checks.support.extend(members.enumeration.support);
        if !members.missing.is_empty() {
            checks.missing.extend(members.missing);
            return Err(unsupported());
        }
        let mut keys = Vec::new();
        for (key, _) in pairs {
            self.tick()?;
            keys.push(key.clone());
            self.tick()?;
        }
        let actual = data::set(ty.erase(), &keys, &self.control)?;
        let required = data::set(ty.erase(), &members.enumeration.values, &self.control)?;
        #[cfg(test)]
        data::observe_actual(
            span,
            self.context.get().unwrap_or_default(),
            "owned_call_map_domain",
            0,
        );
        self.tick()?;
        if !data::equal(&actual, &required, &self.control)? {
            checks.failure = Some((actual, required));
        }
        self.tick()?;
        Ok(())
    }

    // 通常値がない場合も、元Sourceが保持する部分成分だけを所属検査に使う。
    // この内部値をScalar nodeや引数Bindingへ変換しない。
    pub(in crate::observed) fn owned_call_argument(
        &self,
        graph: &Graph,
        evaluation: NodeRef,
    ) -> Result<PartialValue, ValidationFailure> {
        let (source, bindings, known) = self.evaluation(graph, evaluation)?;
        if let Some(known) = known {
            return Ok(PartialValue::Known(graph.scalar(known)?.clone()));
        }
        let analysis = self.original_evaluation_source(graph, evaluation, source, bindings)?;
        Ok(Self::owned_source_argument(
            &analysis.known_value,
            analysis.symbolic.as_deref(),
            self.inputs
                .law()
                .expr_type(
                    *self
                        .expressions
                        .get(&self.expression_span(graph, source)?)
                        .ok_or("部分引数の元式がない")?,
                )
                .ok_or("部分引数の元型がない")?,
        ))
    }

    /// 未選択if枝と、左値で短絡した右辺の条件を外側の必要条件へ混ぜない。
    /// 子の導出・支持・欠測は保持し、必要な子は実評価のBoolから選ぶ。
    pub(in crate::observed) fn evaluation_child_reasons(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
    ) -> Result<Vec<super::super::result::Reason>, ValidationFailure> {
        let span = self.expression_span(graph, source)?;
        let kind = self
            .expressions
            .get(&span)
            .map(|id| &self.inputs.law().exprs[*id].kind);
        let mut required = vec![true; children.len()];
        match kind {
            Some(ExprKind::If { .. }) if children.len() == 3 => {
                match graph.boolean(self.evaluation(graph, children[0])?.2)? {
                    Some(true) => required[2] = false,
                    Some(false) => required[1] = false,
                    None => {}
                }
            }
            Some(ExprKind::Binary { op, .. }) if children.len() == 2 => {
                use crate::law::ast::BinOp;
                if matches!(op, BinOp::And | BinOp::Or | BinOp::Implies) {
                    let left = graph.boolean(self.evaluation(graph, children[0])?.2)?;
                    if matches!(
                        (op, left),
                        (BinOp::And | BinOp::Implies, Some(false)) | (BinOp::Or, Some(true))
                    ) {
                        required[1] = false;
                    }
                }
            }
            _ => {}
        }
        let mut reasons = Vec::new();
        for (child, required) in children.iter().zip(required) {
            self.tick()?;
            reasons.extend(
                graph
                    .get(*child)?
                    .reasons
                    .iter()
                    .filter(|r| {
                        required
                            || !matches!(
                                r.kind,
                                super::super::result::ReasonKind::ConditionFailed { .. }
                            )
                    })
                    .cloned(),
            );
        }
        Ok(reasons)
    }

    pub(in crate::observed) fn evaluation_condition_pending(
        &self,
        graph: &Graph,
        evaluation: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        let (source, bindings, value) = self.evaluation(graph, evaluation)?;
        if value.is_some() {
            return Ok(false);
        }
        Ok(self
            .original_evaluation_source(graph, evaluation, source, bindings)?
            .condition_pending)
    }

    pub(super) fn owned_source_argument(
        known: &Option<Scalar>,
        symbolic: Option<&PartialValue>,
        ty: &Type,
    ) -> PartialValue {
        if let Some(v) = known {
            PartialValue::Known(v.clone())
        } else if let Some(v) = symbolic {
            v.clone()
        } else {
            PartialValue::Unsupported(ty.erase())
        }
    }

    pub(in crate::observed) fn owned_reference_check(
        &self,
        ty: &Type,
        value: Option<&Scalar>,
        values: &BTreeMap<&str, Option<&Scalar>>,
        reading: &str,
        _span: (usize, usize),
        checks: &mut Checks,
    ) -> Result<(), ValidationFailure> {
        let Type::Owned(entity, owner_name) = ty else {
            return Ok(());
        };
        self.tick()?;
        let expected = values.get(owner_name.as_str()).copied().flatten();
        let (Some(value), Some(expected)) = (value, expected) else {
            checks.blocked = true;
            return Ok(());
        };
        let Scalar::Subject {
            snapshot,
            subject,
            entity: actual_entity,
        } = value
        else {
            return Err("Owned callの実値が参照でない".into());
        };
        if actual_entity != entity {
            return Err("Owned callの参照型が元署名と違う".into());
        }
        let root = match &self
            .inputs
            .law()
            .definitions
            .declarations
            .get(entity)
            .ok_or("Owned callの原始型がない")?
            .signature
        {
            crate::definition::PrimitiveSignature::Entity {
                owner: Some(root), ..
            }
            | crate::definition::PrimitiveSignature::Arrow { owner: root, .. } => root,
            _ => return Err("Owned callの型がowned entity/arrowでない".into()),
        };
        if expected.ty() != Type::Ref(root.clone()) {
            return Err("Owned callの実owner型が元署名と違う".into());
        }
        let Scalar::Subject {
            snapshot: os,
            subject: oi,
            ..
        } = expected
        else {
            return Err("Owned callのownerが参照でない".into());
        };
        let subject_input = self.subject(snapshot, subject)?;
        checks
            .scope
            .merge(&self.scope(subject_input, reading, None)?);
        checks
            .scope
            .merge(&self.scope(self.subject(os, oi)?, reading, None)?);
        checks.support.extend([
            Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: None,
                atom: None,
            },
            Fact {
                snapshot: os.clone(),
                subject: oi.clone(),
                field: None,
                atom: None,
            },
        ]);
        let field = format!("{entity}.owner");
        let Slot::Known {
            value:
                Value::Ref {
                    snapshot: actual_snapshot,
                    subject: actual_subject,
                },
            atom,
            origin,
            ..
        } = &self.field(snapshot, subject, &field)?.slot
        else {
            checks.scope.completions = true;
            let fact = Fact {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                field: Some(field),
                atom: None,
            };
            if let Some((_, _, actual)) = self
                .completion_values
                .borrow()
                .iter()
                .find(|(f, _, _)| f == &fact)
            {
                let Scalar::Subject {
                    snapshot: actual_snapshot,
                    subject: actual_subject,
                    entity,
                } = actual
                else {
                    return Err("補完ownerがRefでない".into());
                };
                if entity != root || self.subject(actual_snapshot, actual_subject)?.ty != *root {
                    return Err("補完owner型が元署名と違う".into());
                }
                checks.scope.merge(&self.scope(
                    self.subject(actual_snapshot, actual_subject)?,
                    reading,
                    None,
                )?);
                checks.support.push(Fact {
                    snapshot: actual_snapshot.clone(),
                    subject: actual_subject.clone(),
                    field: None,
                    atom: None,
                });
                if snapshot != os {
                    checks.failure =
                        Some((Scalar::Text(snapshot.clone()), Scalar::Text(os.clone())));
                } else if actual != expected {
                    checks.failure = Some((actual.clone(), expected.clone()));
                }
                self.tick()?;
                return Ok(());
            }
            checks.missing.push(fact);
            checks.blocked = true;
            #[cfg(test)]
            data::observe_actual(
                _span,
                self.context
                    .get()
                    .or(self.scoped_context.get())
                    .unwrap_or_default(),
                "owned_call_missing",
                0,
            );
            self.tick()?;
            return Ok(());
        };
        checks
            .scope
            .merge(&self.scope(subject_input, reading, Some(origin))?);
        checks.support.push(Fact {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: Some(field),
            atom: Some(atom.clone()),
        });
        let actual = Scalar::Subject {
            snapshot: actual_snapshot.clone(),
            subject: actual_subject.clone(),
            entity: root.clone(),
        };
        checks.scope.merge(&self.scope(
            self.subject(actual_snapshot, actual_subject)?,
            reading,
            None,
        )?);
        checks.support.push(Fact {
            snapshot: actual_snapshot.clone(),
            subject: actual_subject.clone(),
            field: None,
            atom: None,
        });
        if snapshot != os {
            checks.failure = Some((Scalar::Text(snapshot.clone()), Scalar::Text(os.clone())));
        } else if actual != *expected {
            checks.failure = Some((actual, expected.clone()));
        }
        #[cfg(test)]
        data::observe_actual(
            _span,
            self.context.get().unwrap_or_default(),
            "owned_call_constraint",
            0,
        );
        self.tick()?;
        Ok(())
    }

    pub(in crate::observed) fn owned_call_checks(
        &self,
        declaration: &Declaration,
        arguments: &[PartialValue],
        returned: Option<&PartialValue>,
        span: (usize, usize),
    ) -> Result<Checks, ValidationFailure> {
        let Signature::View {
            params, returns, ..
        } = &declaration.signature
        else {
            return Err("Owned callの元宣言がviewでない".into());
        };
        let mut owned = self.call_type_has_owned(returns)?;
        for parameter in params {
            owned |= self.call_type_has_owned(&parameter.ty)?;
        }
        if !owned {
            return Ok(Checks::default());
        }
        if params.len() != arguments.len() {
            return Err("Owned callの引数数が元署名と違う".into());
        }
        let mut values = BTreeMap::new();
        let mut checks = Checks::default();
        for (p, value) in params.iter().zip(arguments) {
            self.tick()?;
            self.owned_call_value_check(
                &p.ty,
                value,
                &values,
                &declaration.reading,
                span,
                &mut checks,
            )?;
            if checks.failure.is_some() {
                break;
            }
            if values
                .insert(
                    p.name.as_str(),
                    match value {
                        PartialValue::Known(v) => Some(v),
                        _ => None,
                    },
                )
                .is_some()
            {
                return Err("Owned callの元parameter名が重複する".into());
            }
        }
        if checks.failure.is_none()
            && !checks.blocked
            && let Some(value) = returned
        {
            self.owned_call_value_check(
                returns,
                value,
                &values,
                &declaration.reading,
                span,
                &mut checks,
            )?;
        }
        checks.support.sort();
        checks.support.dedup();
        checks.missing.sort();
        checks.missing.dedup();
        Ok(checks)
    }

    /// 実評価の呼出し境界も、再検査と同じ共有case代入で所属を判定する。
    pub(in crate::observed) fn owned_call_checks_at(
        &self,
        graph: &Graph,
        declaration: &Declaration,
        arguments: &[PartialValue],
        returned: Option<&PartialValue>,
        span: (usize, usize),
    ) -> Result<Checks, ValidationFailure> {
        if graph.active.case.is_none() {
            return self.owned_call_checks(declaration, arguments, returned, span);
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
                data::observe_actual(span, graph.active, "owned_call_case", 0);
                self.tick()?;
                self.owned_call_checks(declaration, arguments, returned, span)
            })();
            self.completion_values.replace(previous_completion);
            self.cutoff.set(previous_cutoff);
            self.context.set(previous_context);
            result
        })
    }

    /// 呼出しの実引数producerから、観測時点で欠けていた所属slotを再構成する。
    /// caseの代入値を元観測へ上書きせず、元Missingを補完の共有軸にする。
    pub(in crate::observed) fn owned_call_missing_slots(
        &self,
        graph: &Graph,
        source: NodeRef,
    ) -> Result<Option<Vec<Fact>>, ValidationFailure> {
        // wholeの集約Sourceを、そのspanと同じ元callの実引数へ読み替えない。
        if self.family_source_root(graph, source)?
            || self.universal_source_root(graph, source)? == Some(source)
        {
            return Ok(None);
        }
        let span = self.expression_span(graph, source)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        if !self.owns_call(id)? {
            return Ok(None);
        }
        let ExprKind::Call { args, .. } = &self.inputs.law().exprs[id].kind else {
            return Err("所属slotの元式がcallでない".into());
        };
        let bindings = self.expression_bindings(graph, source)?;
        let limit = self.cutoff.get().min(graph.nodes.len());
        let mut children = None;
        for (index, node) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if graph.context_at(index) != self.current_context(graph) {
                continue;
            }
            let Some(Payload::Evaluation {
                expression,
                bindings: actual,
                parts,
                ..
            }) = &node.payload
            else {
                continue;
            };
            if *expression == source && actual == bindings {
                if parts.len() != 1
                    || parts[0].location != (Location::Law { span })
                    || children.replace(parts[0].children.clone()).is_some()
                {
                    return Err("所属slotの元call実評価が一意でない".into());
                }
            }
        }
        let children = children.ok_or("所属slotの元call実評価がない")?;
        // 現caseの実frame/bodyと引数を先に照合し、その後だけ元Missingへ戻る。
        self.owned_call_inputs(graph, source, &children, limit)?
            .ok_or("所属slotの元call検査がない")?;
        let declaration = self.named_view(id)?.ok_or("所属slotの元viewがない")?;
        let arguments = children[..args.len()]
            .iter()
            .map(|child| self.owned_call_argument(graph, *child))
            .collect::<Result<Vec<_>, _>>()?;
        let returned = children
            .get(args.len())
            .map(|body| self.owned_call_argument(graph, *body))
            .transpose()?;
        #[cfg(test)]
        data::observe_actual(
            span,
            self.current_context(graph),
            "owned_call_missing_source",
            0,
        );
        self.tick()?;
        let previous = self.completion_values.replace(Vec::new());
        let result = self
            .owned_call_checks(declaration, &arguments, returned.as_ref(), span)
            .map(|checks| {
                if checks.missing.is_empty() {
                    None
                } else {
                    Some(checks.missing)
                }
            });
        self.completion_values.replace(previous);
        result
    }

    pub(in crate::observed) fn owns_call(&self, id: usize) -> Result<bool, ValidationFailure> {
        let Some(d) = self.named_view(id)? else {
            return Ok(false);
        };
        let Signature::View {
            params, returns, ..
        } = &d.signature
        else {
            unreachable!()
        };
        let mut owned = self.call_type_has_owned(returns)?;
        for parameter in params {
            owned |= self.call_type_has_owned(&parameter.ty)?;
        }
        Ok(owned)
    }

    pub(in crate::observed) fn owned_call_inputs(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<Option<Checks>, ValidationFailure> {
        if !matches!(
            graph.get(source)?.payload,
            Some(Payload::Expression {
                location: Location::Law { .. },
                ..
            })
        ) {
            return Ok(None);
        }
        let span = self.expression_span(graph, source)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        let Some(declaration) = self.named_view(id)? else {
            return Ok(None);
        };
        let Signature::View { params, body, .. } = &declaration.signature else {
            unreachable!()
        };
        let ExprKind::Call { args, .. } = &self.inputs.law().exprs[id].kind else {
            unreachable!()
        };
        if args.len() != params.len()
            || !(children.len() == args.len() || children.len() == args.len() + 1)
            || source.0 >= limit
            || graph.context_at(source.0) != self.current_context(graph)
        {
            return Err("Owned callの元引数数・Source Contextが違う".into());
        }
        let mut inherited_failure = false;
        let mut inherited_pending = false;
        for child in &children[..args.len()] {
            self.tick()?;
            inherited_pending |= self.evaluation_condition_pending(graph, *child)?;
            inherited_failure |= graph
                .get(*child)?
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }));
        }
        if !self.owns_call(id)? && !inherited_failure && !inherited_pending {
            return Ok(None);
        }
        self.validate_at(graph, graph.get(source)?, source.0)?;
        let bindings = self.expression_bindings(graph, source)?;
        let mut values = Vec::new();
        let mut scope = graph.get(source)?.scope.clone();
        let mut support = Vec::new();
        for (&id, &child) in args.iter().zip(children) {
            self.tick()?;
            if child.0 >= limit || graph.context_at(child.0) != self.current_context(graph) {
                return Err("Owned callの実引数が既出同callerでない".into());
            }
            self.recheck_evaluation(graph, child)?;
            let (expression, actual_bindings, _) = self.evaluation(graph, child)?;
            self.source_matches(graph, expression, id)?;
            if actual_bindings != bindings || self.actual_evaluation(graph, id, bindings)? != child
            {
                return Err("Owned callの引数producer・束縛が元出現と違う".into());
            }
            values.push(self.owned_call_argument(graph, child)?);
            scope.merge(&graph.get(child)?.scope);
            support.extend(graph.get(child)?.support.iter().cloned());
        }
        let mut checks = if inherited_failure {
            Checks {
                blocked: true,
                ..Checks::default()
            }
        } else {
            self.owned_call_checks(declaration, &values, None, span)?
        };
        checks.blocked |= inherited_pending;
        if children.len() == args.len() + 1 {
            if checks.failure.is_some() || checks.blocked {
                return Err("所属不適合・未確定のcallee bodyを評価した".into());
            }
            let child = children[args.len()];
            if child.0 >= limit {
                return Err("Owned call bodyが未出".into());
            }
            let context = graph.context_at(child.0);
            let index = context.frame.ok_or("Owned call bodyにframeがない")?;
            let frame = graph.frames.get(index).ok_or("Owned call frameがない")?;
            if frame.source != source
                || frame.caller != self.current_context(graph)
                || frame.arguments != children[..args.len()]
                || context
                    != (super::super::call::Context {
                        frame: Some(index),
                        iteration: None,
                        ..frame.caller
                    })
            {
                return Err("Owned call bodyと元frameが違う".into());
            }
            if self.universal_source_root(graph, source)?.is_none() {
                self.frame_arguments(graph, index)?;
            }
            // 全域Sourceでは上のcaller/実引数対応と、以下の元Planからの
            // body再検査でframeを照合する。数値binderを通常の既知束縛へ落とさない。
            self.recheck_evaluation(graph, child)?;
            let (expression, _, _) = self.evaluation(graph, child)?;
            self.source_matches(graph, expression, *body)?;
            if graph.context_at(expression.0) != context {
                return Err("Owned body SourceのContextが違う".into());
            }
            let partial = self.owned_call_argument(graph, child)?;
            checks = self.owned_call_checks(declaration, &values, Some(&partial), span)?;
            scope.merge(&graph.get(child)?.scope);
            support.extend(graph.get(child)?.support.iter().cloned());
        } else if checks.failure.is_none() && !checks.blocked {
            return Err("所属適合callに元body評価がない".into());
        }
        scope.merge(&checks.scope);
        support.extend(checks.support);
        support.sort();
        support.dedup();
        checks.scope = scope;
        checks.support = support;
        Ok(Some(checks))
    }

    pub(super) fn validate_owned_call_condition_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let extra = match (&node.payload, &node.rule) {
            (Some(Payload::OwnedCallCondition { .. }), _) => 3,
            (Some(Payload::OwnedCallCounterexample { .. }), _) => 2,
            (Some(Payload::Scalar(value)), Rule::Construction("evaluation" | "domain"))
                if matches!(value, Scalar::Subject { .. } | Scalar::Text(_))
                    || matches!(
                        value,
                        Scalar::Set {
                            element: Type::Ref(_),
                            ..
                        }
                    ) =>
            {
                0
            }
            _ => return Ok(false),
        };
        let Some(n) = node.arguments.len().checked_sub(extra) else {
            return Err("Owned条件の元辺が不足".into());
        };
        if n == 0 {
            return Err("Owned条件に元Sourceがない".into());
        }
        let source = node.arguments[0];
        if !matches!(
            graph.get(source)?.payload,
            Some(Payload::Expression {
                location: Location::Law { .. },
                ..
            })
        ) {
            if extra == 0 {
                return Ok(false);
            }
            return Err("Owned条件に元call Sourceがない".into());
        }
        if self.family_source_root(graph, source)? {
            if extra == 0 {
                return Ok(false);
            }
            return Err("whole族Sourceをcall所属条件に転用した".into());
        }
        let Some(checks) = self.owned_call_inputs(graph, source, &node.arguments[1..n], limit)?
        else {
            if extra == 0 {
                return Ok(false);
            }
            return Err("Owned条件の元署名が違う".into());
        };
        let Some((actual, required)) = checks.failure else {
            if extra == 0 {
                return Ok(false);
            }
            return Err("Owned条件に元所属不適合がない".into());
        };
        if node.scope != checks.scope || node.support != checks.support || !node.reasons.is_empty()
        {
            return Err("Owned条件の元Scope・支持・理由が違う".into());
        }
        match &node.payload {
            Some(Payload::Scalar(value)) => {
                let expected = match node.rule {
                    Rule::Construction("evaluation") => &actual,
                    Rule::Construction("domain") => &required,
                    _ => return Err("Owned条件owner値の規則が違う".into()),
                };
                if value != expected
                    || node.ty != NodeType::Value(expected.ty())
                    || !node.evidence.is_empty()
                    || node.judgment.is_some()
                {
                    return Err("Owned条件owner値が原始所属・実引数と違う".into());
                }
            }
            Some(Payload::OwnedCallCounterexample {
                bindings,
                left,
                right,
                ..
            }) => {
                graph.owned_call_counterexample_shape(node)?;
                if bindings != self.expression_bindings(graph, source)?
                    || node.arguments[n..] != [*left, *right]
                {
                    return Err("Owned反例の元束縛・辺が違う".into());
                }
                for r in [*left, *right] {
                    self.validate_at(graph, graph.get(r)?, r.0)?;
                }
                if graph.scalar(*left)? != &actual || graph.scalar(*right)? != &required {
                    return Err("Owned反例が元owner不等でない".into());
                }
            }
            Some(Payload::OwnedCallCondition { left, right }) => {
                if node.ty != NodeType::Proposition || node.arguments[n..n + 2] != [*left, *right] {
                    return Err("Owned条件命題の型・辺が違う".into());
                }
                graph.validate_proposition_evidence(node)?;
                for r in [*left, *right, node.arguments[n + 2]] {
                    self.validate_at(graph, graph.get(r)?, r.0)?;
                }
                if graph.scalar(*left)? != &actual || graph.scalar(*right)? != &required {
                    return Err("Owned条件命題の実ownerが違う".into());
                }
            }
            _ => return Err("Owned条件payloadが違う".into()),
        }
        Ok(true)
    }

    pub(super) fn owned_call_condition_reason(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<Option<Reason>, ValidationFailure> {
        let Some(checks) = self.owned_call_inputs(graph, source, children, limit)? else {
            return Ok(None);
        };
        if checks.failure.is_none() {
            return Ok(None);
        }
        let edges: Vec<_> = std::iter::once(source)
            .chain(children.iter().copied())
            .collect();
        let mut found = None;
        for (i, node) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if graph.context_at(i) == self.current_context(graph)
                && matches!(node.payload, Some(Payload::OwnedCallCondition { .. }))
                && node.arguments.get(..edges.len()) == Some(edges.as_slice())
            {
                self.validate_at(graph, node, i)?;
                if found.replace(NodeRef(i)).is_some() {
                    return Err("元callの所属条件命題が重複".into());
                }
            }
        }
        let condition = found.ok_or("元callの反証済み所属条件がない")?;
        let request = graph
            .requests
            .get(self.current_context(graph).request)
            .ok_or("Owned条件の元requestがない")?;
        Ok(Some(Reason {
            kind: ReasonKind::ConditionFailed {
                condition,
                construction: "evaluation",
            },
            request: request.id.clone(),
            dependencies: vec![source],
            missing: vec![],
            location: Some(Location::Law {
                span: self.expression_span(graph, source)?,
            }),
        }))
    }

    pub(super) fn validate_failed_owned_call(
        &self,
        graph: &Graph,
        node: &Node,
        source: NodeRef,
        children: &[NodeRef],
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if !matches!(
            graph.get(source)?.payload,
            Some(Payload::Expression {
                location: Location::Law { .. },
                ..
            })
        ) {
            return Ok(false);
        }
        // wholeのrow/body子を、元callの実引数と取り違えない。
        // 各出現のcall Sourceはtemplateを別の既出nodeとして指す。
        if self.family_source_root(graph, source)?
            || self.universal_source_root(graph, source)? == Some(source)
        {
            return Ok(false);
        }
        let span = self.expression_span(graph, source)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(false);
        };
        let Some(declaration) = self.named_view(id)? else {
            return Ok(false);
        };
        let Signature::View { params, .. } = &declaration.signature else {
            unreachable!()
        };
        if children.len() != params.len() && children.len() != params.len() + 1 {
            return Ok(false);
        }
        let Some(checks) = self.owned_call_inputs(graph, source, children, limit)? else {
            return Ok(false);
        };
        if checks.failure.is_none() && !checks.blocked {
            return Ok(false);
        }
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
        let expected: Vec<_> = std::iter::once(source)
            .chain(children.iter().copied())
            .collect();
        if *expression != source
            || bindings != self.expression_bindings(graph, source)?
            || value.is_some()
            || *applicability != "applicable"
            || parts.len() != 1
            || parts[0].location != (Location::Law { span })
            || parts[0].value.is_some()
            || parts[0].residual.is_some()
            || node.arguments != expected
            || node.ty
                != NodeType::Evaluation(
                    self.inputs
                        .law()
                        .expr_type(id)
                        .ok_or("Owned callの元型がない")?
                        .clone(),
                )
            || node.support != checks.support
            || node.scope != checks.scope
            || !node.evidence.is_empty()
            || node.judgment.is_some()
            || !matches!(node.rule, Rule::Construction("evaluation"))
        {
            return Err("所属不適合call評価の元辺・値・型・Scopeが違う".into());
        }
        self.evaluation_missing_reasons(graph, node, source, children, None)?;
        Ok(true)
    }
}
