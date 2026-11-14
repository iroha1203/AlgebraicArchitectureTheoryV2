//! 全域Domainを要求しない、元入力へ拡張可能な二つのwhole補完。
use super::*;
use crate::observed::call::CompletionOrigin;
impl Environment<'_> {
    pub(in crate::observed) fn completion_probe_assignment_valid(
        &self,
        fields: &[Fact],
        value: &Scalar,
    ) -> Result<bool, ValidationFailure> {
        let types = self.completion_slot_types_for(fields, CompletionMode::Assignment)?;
        self.completion_assignment_consistent(fields, &types, value)
    }
    pub(in crate::observed) fn local_completion_pair_matches_answer(
        &self,
        graph: &Graph,
        seed_ref: NodeRef,
        answer: &Answer,
    ) -> Result<(), ValidationFailure> {
        let seed = self.completion_seed(graph, seed_ref)?;
        let root = *answer
            .outputs
            .get("evaluation")
            .ok_or(internal!("補助対の元回答に評価がない"))?;
        let Some(Payload::CompletionSeed { roots, .. }) = &graph.get(seed_ref)?.payload else {
            unreachable!();
        };
        if graph
            .requests
            .get(seed.context.request)
            .map(|r| r.id.as_str())
            != Some(answer.id.as_str())
            || !roots.contains(&root)
            || answer.claim.is_some_and(|claim| !roots.contains(&claim))
        {
            return Err(internal!("補助補完対が別の元Request・whole回答を指す").into());
        }
        Ok(())
    }
    pub(in crate::observed) fn validate_local_completion_pair(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        let Some(Payload::CompletionPair {
            fields,
            first,
            second,
            first_result,
            second_result,
        }) = &node.payload
        else {
            return Ok(false);
        };
        let first_context = graph.context_at(first_result.0);
        let Some(first_case) = first_context.case.and_then(|index| graph.cases.get(index)) else {
            return Ok(false);
        };
        if first_case.origin != CompletionOrigin::Assignment {
            return Ok(false);
        }
        let seed = self.completion_seed(graph, first_case.seed)?;
        let mut scope = seed.scope.clone();
        let mut support = seed.support.clone();
        let mut reasons = seed.reasons.clone();
        let mut members = Vec::new();
        let mut values = Vec::new();
        for (result, assignment) in [(*first_result, first), (*second_result, second)] {
            self.tick()?;
            if result.0 >= limit {
                return Err(internal!("補助補完対が未来のwholeを指す").into());
            }
            let context = graph.context_at(result.0);
            let index = context.case.ok_or(internal!("補助補完wholeのcaseがない"))?;
            let case = graph
                .cases
                .get(index)
                .ok_or(internal!("補助補完caseがない"))?;
            if case.origin != CompletionOrigin::Assignment
                || case.seed != seed.reference
                || case.caller != seed.context
                || context.request != seed.context.request
                || context.frame.is_some()
                || context.iteration.is_some()
                || context.instance.is_some()
            {
                return Err(internal!("補助補完対のwholeが別Context・Seed・域に属する").into());
            }
            let actual = self.completion_values(graph, index)?;
            if actual
                .iter()
                .map(|(_, reference, _)| *reference)
                .collect::<Vec<_>>()
                != *assignment
            {
                return Err(internal!("補助補完対のslot値が別assignment").into());
            }
            self.recheck_evaluation(graph, result)?;
            let (expression, bindings, value) = self.evaluation(graph, result)?;
            let request = &graph.requests[seed.context.request];
            let declaration = &self.indexes.inputs.law().declarations()[request
                .declaration()
                .ok_or(internal!("補助補完の元宣言がない"))?];
            let body = match &declaration.signature {
                Signature::View { body, .. } | Signature::Law { body, .. } => *body,
                _ => return Err(internal!("補助補完の元宣言がview/Lawでない").into()),
            };
            let raw_source = if request.kind == QuestionKind::Check {
                match graph
                    .get(result)?
                    .arguments
                    .first()
                    .map(|r| graph.get(*r))
                    .transpose()?
                    .and_then(|n| n.payload.as_ref())
                {
                    Some(Payload::LawInstance { body, .. }) => *body,
                    _ => expression,
                }
            } else {
                expression
            };
            self.source_matches(graph, raw_source, body)?;
            self.completion_case_bindings(graph, &seed, raw_source, bindings, context)?;
            let value = value.ok_or(internal!("補助補完対に未知whole結果がある"))?;
            values.push(value);
            members.push(case.member);
            let whole = graph.get(result)?;
            scope.merge(&whole.scope);
            support = Support::sum(vec![], [support, whole.support.clone()]);
            reasons.extend(whole.reasons.iter().cloned());
        }
        canonical_reasons(&mut reasons, &self.control)?;
        let expected_arguments: Vec<_> = [
            seed.reference,
            members[0],
            members[1],
            *first_result,
            *second_result,
        ]
        .into_iter()
        .chain(first.iter().copied())
        .chain(second.iter().copied())
        .collect();
        if fields != &seed.fields
            || first_result == second_result
            || first.len() != fields.len()
            || second.len() != fields.len()
            || value_equality::equal(
                graph.scalar(values[0])?,
                graph.scalar(values[1])?,
                self.indexes.inputs.law(),
                &self.control,
            )? != Some(false)
            || node.ty != NodeType::Evidence
            || !clean(node, "evidence")
            || !reasons_equal(&node.reasons, &reasons)
            || node.arguments != expected_arguments
            || node.scope != scope
            || !node.support.same_facts(&support, &self.control)?
            || graph.context_at(limit) != seed.context
        {
            return Err(internal!("補助補完対の相違・型・元whole・Scope・理由が違う").into());
        }
        Ok(true)
    }
}

impl Environment<'_> {
    /// 全候補域とは別の有限提案。提案自体は何も証明せず、採用前に全slotを同時にpinする。
    pub(in crate::observed) fn completion_probe_assignments(
        &self,
        graph: &Graph,
        fields: &[Fact],
        roots: &[NodeRef],
        carried: &BTreeMap<Fact, Scalar>,
    ) -> Result<Vec<Scalar>, ValidationFailure> {
        let types = self.completion_slot_types_for(fields, CompletionMode::Assignment)?;
        let has_sets = types.iter().any(|ty| matches!(ty, Type::Set(_)));
        let mut selector = false;
        let mut baseline = Vec::new();
        for (fact, ty) in fields.iter().zip(&types) {
            let value = match carried.get(fact) {
                Some(value) if value.ty() == *ty => Some(value.clone()),
                Some(_) => return Err(internal!("probe継続代入の元slot型が違う").into()),
                None => self.completion_probe_default(ty)?,
            };
            let Some(value) = value else {
                return Ok(Vec::new());
            };
            baseline.push(value);
        }
        let pack = |values: Vec<Scalar>| {
            if values.len() == 1 {
                values.into_iter().next().unwrap()
            } else {
                Scalar::Tuple(values)
            }
        };
        let mut proposals = vec![pack(baseline.clone())];
        // 一つの実binder・未知ifの枝に属する要求だけを同時に提案する。
        type Branch = Vec<(usize, bool)>;
        let mut groups: BTreeMap<
            (bool, super::super::super::call::Context, Branch),
            BTreeMap<usize, Scalar>,
        > = BTreeMap::new();
        let mut pending: Vec<_> = roots.iter().map(|root| (*root, Vec::new())).collect();
        let mut seen = BTreeSet::new();
        while let Some((reference, branch)) = pending.pop() {
            self.tick()?;
            if !seen.insert((reference, branch.clone())) {
                continue;
            }
            let node = graph.get(reference)?;
            let Some(Payload::Evaluation {
                expression,
                parts,
                value,
                ..
            }) = &node.payload
            else {
                continue;
            };
            if value.is_some() {
                continue;
            }
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &graph.get(*expression)?.payload
            else {
                for child in parts.iter().flat_map(|p| &p.children) {
                    pending.push((*child, branch.clone()));
                }
                continue;
            };
            let Some(&id) = self.indexes.inputs.law().program().expressions.get(span) else {
                continue;
            };
            let children: Vec<_> = parts
                .iter()
                .flat_map(|p| p.children.iter().copied())
                .collect();
            let child = |id: usize| -> Option<NodeRef> {
                let span = self.indexes.inputs.law().exprs()[id].span;
                children.iter().copied().find(|r| {
                    let Ok(node) = graph.get(*r) else { return false; };
                    let Some(Payload::Evaluation { expression, .. }) = &node.payload else { return false; };
                    matches!(graph.get(*expression).map(|n| &n.payload), Ok(Some(Payload::Expression{location:Location::Law{span:actual},..})) if *actual==span)
                })
            };
            let scalar = |reference: NodeRef| -> Option<Scalar> {
                match &graph.get(reference).ok()?.payload {
                    Some(Payload::Evaluation {
                        value: Some(value), ..
                    }) => graph.scalar(*value).ok().cloned(),
                    _ => None,
                }
            };
            let field = |reference: NodeRef| -> Option<usize> {
                let node = graph.get(reference).ok()?;
                let Some(Payload::Evaluation { expression, .. }) = &node.payload else {
                    return None;
                };
                let Some(Payload::Expression {
                    location: Location::Law { span },
                    ..
                }) = &graph.get(*expression).ok()?.payload
                else {
                    return None;
                };
                let id = *self.indexes.inputs.law().program().expressions.get(span)?;
                if !matches!(
                    self.indexes.inputs.law().exprs()[id].kind,
                    ExprKind::Dotted(_) | ExprKind::Field { .. }
                ) {
                    return None;
                }
                let mut actual = node
                    .reasons
                    .iter()
                    .filter(|r| matches!(r.kind, ReasonKind::Missing))
                    .flat_map(|r| &r.missing)
                    .filter_map(|f| fields.iter().position(|candidate| candidate == f));
                let first = actual.next()?;
                actual.all(|other| other == first).then_some(first)
            };
            let group = groups
                .entry((
                    graph.context_at(reference.0).case.is_none(),
                    graph.context_at(reference.0),
                    branch.clone(),
                ))
                .or_default();
            match &self.indexes.inputs.law().exprs()[id].kind {
                ExprKind::Binary {
                    op: BinOp::In,
                    lhs,
                    rhs,
                } => {
                    if let Some((item, index)) = child(*lhs)
                        .and_then(&scalar)
                        .zip(child(*rhs).and_then(&field))
                    {
                        if let Type::Set(element) = &types[index]
                            && item.ty() == **element
                        {
                            group.insert(
                                index,
                                Scalar::Set {
                                    element: (**element).clone(),
                                    items: vec![item],
                                },
                            );
                        }
                    }
                }
                ExprKind::Binary {
                    op: BinOp::Eq,
                    lhs,
                    rhs,
                } => {
                    for (unknown, known) in [(*lhs, *rhs), (*rhs, *lhs)] {
                        if let Some((index, value)) = child(unknown)
                            .and_then(&field)
                            .zip(child(known).and_then(&scalar))
                            && value.ty() == types[index]
                        {
                            selector |= graph.context_at(reference.0).iteration.is_some()
                                && matches!(&value, Scalar::Option { value: Some(item), .. } if matches!(item.as_ref(), Scalar::Subject { .. }));
                            group.insert(index, value);
                        }
                        if let ExprKind::Call { callee, args } =
                            &self.indexes.inputs.law().exprs()[unknown].kind
                            && self
                                .indexes
                                .inputs
                                .law()
                                .program()
                                .callees
                                .get(callee)
                                .is_some_and(|c| {
                                    matches!(c, archsig_input::law::ir::Callee::Builtin("count"))
                                })
                            && args.len() == 1
                            && let Some(count) = child(known).and_then(&scalar)
                            && let Scalar::Z(ref count) = count
                            && let Some(count_call) = child(unknown)
                        {
                            let Some(Payload::Evaluation { parts, .. }) =
                                &graph.get(count_call)?.payload
                            else {
                                continue;
                            };
                            for argument in parts.iter().flat_map(|p| &p.children) {
                                if let Some(index) = field(*argument)
                                    && let Type::Set(element) = &types[index]
                                {
                                    if count == &0.into() {
                                        group.entry(index).or_insert_with(|| Scalar::Set {
                                            element: (**element).clone(),
                                            items: vec![],
                                        });
                                    } else if count == &1.into()
                                        && let Some(item) =
                                            self.completion_probe_set_item(&fields[index])?
                                    {
                                        group.entry(index).or_insert_with(|| Scalar::Set {
                                            element: (**element).clone(),
                                            items: vec![item],
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } if child(*cond).and_then(&scalar).is_none() => {
                    if let Some(cond) = child(*cond) {
                        pending.push((cond, branch.clone()));
                    }
                    for (id, flag) in [(*then_branch, true), (*else_branch, false)] {
                        if let Some(child) = child(id) {
                            let mut path = branch.clone();
                            path.push((id, flag));
                            pending.push((child, path));
                        }
                    }
                    continue;
                }
                _ => {}
            }
            for child in children {
                pending.push((child, branch.clone()));
            }
        }
        if (!has_sets && !selector) || groups.values().all(BTreeMap::is_empty) {
            return Ok(Vec::new());
        }
        for goal in groups.into_values() {
            if goal.is_empty() {
                continue;
            }
            let mut values = baseline.clone();
            for (index, value) in goal {
                values[index] = value;
            }
            let value = pack(values);
            if !data::contains(&proposals, &value, &self.control)? {
                proposals.push(value);
            }
        }
        // 型の最小の異なる値も提案する。件数上限や候補域の切捨てではない。
        for (index, ty) in types.iter().enumerate() {
            self.tick()?;
            let alternate = match ty {
                Type::Bool => Some(Scalar::Bool(true)),
                Type::Option(element) => {
                    self.completion_probe_default(element)?
                        .map(|v| Scalar::Option {
                            element: (**element).clone(),
                            value: Some(Box::new(v)),
                        })
                }
                Type::Set(element) => {
                    self.completion_probe_set_item(&fields[index])?
                        .map(|v| Scalar::Set {
                            element: (**element).clone(),
                            items: vec![v],
                        })
                }
                _ => None,
            };
            if let Some(value) = alternate {
                let mut values = baseline.clone();
                values[index] = value;
                let value = pack(values);
                if !data::contains(&proposals, &value, &self.control)? {
                    proposals.push(value);
                }
            }
        }
        Ok(proposals)
    }
    fn completion_probe_set_item(&self, fact: &Fact) -> Result<Option<Scalar>, ValidationFailure> {
        let field = self.indexes.field(
            &self.state,
            &fact.snapshot,
            &fact.subject,
            fact.field
                .as_deref()
                .ok_or(internal!("集合提案に元fieldがない"))?,
        )?;
        let Type::Set(element) = &field.ty else {
            return Ok(None);
        };
        if let Type::Owned(entity, name) = element.as_ref() {
            let holder = self.indexes.subject(&fact.snapshot, &fact.subject)?;
            let owner = self.indexes.field(
                &self.state,
                &fact.snapshot,
                &fact.subject,
                &format!("{}.{name}", holder.ty),
            )?;
            // 観測済みownerだけを提案に使う。補完値を既知所属として扱わない。
            if matches!(owner.slot, Slot::Known { .. })
                && let Some(owner) = self.indexes.observed_scalar(owner, &self.control)?
            {
                return Ok(self
                    .owned_members(entity, &owner, None, "", &mut |_, _| {})?
                    .enumeration
                    .values
                    .into_iter()
                    .next());
            }
        }
        self.completion_probe_default(&element.erase())
    }
    fn completion_probe_default(&self, ty: &Type) -> Result<Option<Scalar>, ValidationFailure> {
        self.tick()?;
        Ok(match ty {
            Type::Unit => Some(Scalar::Unit),
            Type::Text => Some(Scalar::Text(String::new())),
            Type::Bool => Some(Scalar::Bool(false)),
            Type::Fp(modulus) => Some(Scalar::Fp {
                modulus: modulus.clone(),
                value: 0.into(),
            }),
            Type::Set(element) => Some(Scalar::Set {
                element: (**element).clone(),
                items: vec![],
            }),
            Type::Option(element) => Some(Scalar::Option {
                element: (**element).clone(),
                value: None,
            }),
            Type::Ref(entity) => self
                .indexes
                .reference_roster(&self.control, entity, &mut |_| {})?
                .values
                .into_iter()
                .next(),
            Type::Tuple(items) => {
                let mut values = Vec::new();
                for ty in items {
                    let Some(value) = self.completion_probe_default(ty)? else {
                        return Ok(None);
                    };
                    values.push(value);
                }
                Some(Scalar::Tuple(values))
            }
            // 非対応の提案は従来の全域列挙へ残す。
            _ => None,
        })
    }
}
