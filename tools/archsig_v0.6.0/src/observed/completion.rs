//! 元の欠測 slot、補完代入、補完内の whole 評価を照合する。
use super::*;
use crate::law::{ast::Role, model::Signature};
use crate::observed::{control::CheckFailure, value_equality};

#[derive(Clone)]
pub(super) struct Seed {
    reference: NodeRef,
    context: super::super::call::Context,
    location: Location,
    bindings: Vec<Binding>,
    fields: Vec<Fact>,
    types: Vec<Type>,
    sources: Vec<NodeRef>,
    scope: Scope,
    support: Vec<Fact>,
    reasons: Vec<Reason>,
    ty: Type,
}
pub(super) type MemoKey = (usize, super::super::call::Context, usize, usize);
pub(super) type DomainKey = (usize, super::super::call::Context, usize, usize, usize);
pub(super) type SlotsKey = (usize, super::super::call::Context, usize, Vec<usize>);
pub(super) type SlotCollection = (Vec<Fact>, Vec<NodeRef>, Vec<Reason>);
type EvaluationParts = (NodeRef, NodeRef, Vec<NodeRef>, Vec<NodeRef>);
struct Aggregate {
    seed: Seed,
    evaluations: Vec<NodeRef>,
    scope: Scope,
    support: Vec<Fact>,
    reasons: Vec<Reason>,
    value: Option<Scalar>,
    pair: Option<(usize, usize)>,
}
pub(in crate::observed) fn value_comparison_reason(
    request: &crate::observed::request::Request,
    ty: &Type,
    location: &Location,
    source: NodeRef,
) -> Reason {
    Reason {
        kind: ReasonKind::UnsupportedAlgorithm {
            question: request.kind,
            operand_types: vec![ty.clone()],
            method: "extensional value equality in completions".into(),
        },
        request: request.id.clone(),
        dependencies: vec![source],
        missing: vec![],
        location: Some(location.clone()),
    }
}
fn reasons_equal(a: &[Reason], b: &[Reason]) -> bool {
    a.iter().map(Reason::wire).collect::<Vec<_>>() == b.iter().map(Reason::wire).collect::<Vec<_>>()
}
/// 原理由の依存Ref・slot・位置をすべて保つ集合和。既存の表示主順を維持し、
/// 同じ位置に複数caseの理由がある場合も完全に同一な理由だけを一度にする。
pub(in crate::observed) fn canonical_reasons(
    reasons: &mut Vec<Reason>,
    control: &Control,
) -> Result<(), ValidationFailure> {
    let mut controlled = control.clone();
    let mut keys = Vec::new();
    for (index, reason) in reasons.iter().enumerate() {
        controlled.checkpoint(Checkpoint::FiniteIteration)?;
        let key = reason
            .wire()
            .canonical_controlled::<Box<crate::issue::Issue>>(
                &mut controlled,
                Checkpoint::FiniteIteration,
            )
            .map_err(|_| {
                controlled
                    .stop_reason()
                    .map(ValidationFailure::Stop)
                    .unwrap_or_else(|| {
                        ValidationFailure::Internal("補完理由のcanonical keyを構成できない".into())
                    })
            })?;
        keys.push((key, index));
    }
    keys.sort_by(|a, b| a.0.cmp(&b.0));
    keys.dedup_by(|a, b| a.0 == b.0);
    let mut canonical: Vec<_> = keys
        .into_iter()
        .map(|(_, index)| reasons[index].clone())
        .collect();
    sort_reasons(&mut canonical);
    controlled.checkpoint(Checkpoint::FiniteIteration)?;
    *reasons = canonical;
    Ok(())
}

fn clean(node: &Node, name: &str) -> bool {
    matches!(&node.rule, Rule::Construction(actual) if *actual == name)
        && node.evidence.is_empty()
        && node.judgment.is_none()
}
fn assignment_type(types: &[Type]) -> Type {
    if types.len() == 1 {
        types[0].clone()
    } else {
        Type::Tuple(types.to_vec())
    }
}
fn components(
    value: &Scalar,
    types: &[Type],
    law: &crate::law::CheckedLaw,
    control: &Control,
) -> Result<Vec<Scalar>, ValidationFailure> {
    control.clone().checkpoint(Checkpoint::FiniteIteration)?;
    data::check(value, law, control)?;
    let values = match value {
        value if types.len() == 1 => vec![value.clone()],
        Scalar::Tuple(values) if types.len() > 1 && values.len() == types.len() => values.clone(),
        _ => return Err("補完代入の元slot数・型が違う".into()),
    };
    for (value, ty) in values.iter().zip(types) {
        control.clone().checkpoint(Checkpoint::FiniteIteration)?;
        if !super::super::finite::field_completion_supported(ty, law, control)?
            || value.ty() != ty.erase()
        {
            return Err("補完代入の成分型が元の有限slotと違う".into());
        }
    }
    control.clone().checkpoint(Checkpoint::FiniteIteration)?;
    Ok(values)
}

impl Environment<'_> {
    pub(in crate::observed) fn completion_type_supported(
        &self,
        ty: &Type,
    ) -> Result<bool, ValidationFailure> {
        super::super::finite::field_completion_supported(ty, self.inputs.law(), &self.control)
    }

    fn completion_has_references(&self, types: &[Type]) -> Result<bool, ValidationFailure> {
        let mut pending: Vec<_> = types.iter().collect();
        let mut seen = BTreeSet::new();
        while let Some(ty) = pending.pop() {
            self.tick()?;
            match ty {
                Type::Ref(_) | Type::Owned(..) | Type::Map(..) => return Ok(true),
                Type::Tuple(items) => pending.extend(items),
                Type::Option(item) | Type::Set(item) | Type::List(item) => pending.push(item),
                Type::Data(family) if seen.insert(family.as_str()) => {
                    for ctor in data::constructors(self.inputs.law(), family)? {
                        self.tick()?;
                        pending.extend(&ctor.arguments);
                    }
                }
                _ => {}
            }
        }
        Ok(false)
    }

    /// 候補の列挙前に、元入力だけから補完の支持とScopeを構成する。
    /// Sourceを先に残し、実列挙のobserverと検査用の静的読取りを分離する。
    pub(in crate::observed) fn completion_assignment_context(
        &self,
        fields: &[Fact],
    ) -> Result<super::super::finite::Enumeration, ValidationFailure> {
        let types = self.completion_slot_types(fields)?;
        let mut all = super::super::finite::Enumeration::default();
        if !self.completion_has_references(&types)? {
            return Ok(all);
        }
        // 参照候補の可否は選択したfield以外の既知Map/ownerにも依存する。
        // その元登録族・原始事実と現在の由来を支持へ保持する。
        for snapshot in &self.inputs.archmap().snapshots {
            self.tick()?;
            all.scope.snapshots.insert(snapshot.id.clone());
            all.scope
                .modes
                .insert(self.origin_mode(&snapshot.origin)?.into());
            for subject in &snapshot.subjects {
                self.tick()?;
                all.scope.merge(&self.scope(subject, "", None)?);
                all.scope.readings.remove("");
                all.support.push(Fact {
                    snapshot: snapshot.id.clone(),
                    subject: subject.id.clone(),
                    field: None,
                    atom: None,
                });
                for field in &subject.fields {
                    self.tick()?;
                    if let Slot::Known { atom, origin, .. } = &field.slot {
                        all.scope.modes.insert(self.origin_mode(origin)?.into());
                        all.support.push(Fact {
                            snapshot: snapshot.id.clone(),
                            subject: subject.id.clone(),
                            field: Some(field.name.clone()),
                            atom: Some(atom.clone()),
                        });
                    }
                }
            }
        }
        all.support.sort();
        all.support.dedup();
        self.tick()?;
        Ok(all)
    }

    /// 元slot順の全候補を作り、元ArchMap制約へ拡張できる代入だけを残す。
    pub(in crate::observed) fn completion_assignments(
        &self,
        fields: &[Fact],
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<super::super::finite::Enumeration, ValidationFailure> {
        let types = self.completion_slot_types(fields)?;
        let ty = assignment_type(&types);
        let observer = RefCell::new(observer);
        let mut all = super::super::finite::field_candidates(
            &ty,
            self.inputs.law(),
            &self.control,
            &mut |entity| {
                self.reference_roster(entity, &mut |index| {
                    observer.borrow_mut()("ref_roster", index)
                })
            },
            &mut |index| observer.borrow_mut()("type_enum", index),
        )?;
        if !self.completion_has_references(&types)? {
            return Ok(all);
        }
        let context = self.completion_assignment_context(fields)?;
        all.scope.merge(&context.scope);
        all.support.extend(context.support);
        let mut kept = Vec::new();
        for (index, value) in all.values.into_iter().enumerate() {
            self.tick()?;
            let values = components(&value, &types, self.inputs.law(), &self.control)?;
            let mut pinned = Vec::new();
            for (fact, value) in fields.iter().zip(values) {
                self.tick()?;
                pinned.push(crate::archmap::FieldAssignment {
                    snapshot: fact.snapshot.clone(),
                    subject: fact.subject.clone(),
                    field: fact.field.clone().ok_or("補完に元fieldがない")?,
                    value: data::input_json(&value, &self.control)?,
                });
            }
            observer.borrow_mut()("reference_constraints", index);
            self.tick()?;
            match crate::archmap::check_completion_with_values::<
                CheckFailure<Box<crate::issue::Issue>>,
            >(
                &self.inputs.archmap().snapshots,
                &self.inputs.law().definitions,
                &pinned,
                &mut self.control.clone(),
            ) {
                Ok(()) => kept.push(value),
                Err(CheckFailure::Input(issue))
                    if issue.code == crate::issue::Code::InconsistentObservation => {}
                Err(CheckFailure::Stopped(reason)) => return Err(ValidationFailure::Stop(reason)),
                Err(CheckFailure::Input(issue)) => {
                    return Err(ValidationFailure::Internal(format!(
                        "参照補完候補の元入力検査: {}",
                        issue.message
                    )));
                }
            }
            self.tick()?;
        }
        all.values = kept;
        all.support.sort();
        all.support.dedup();
        if all.values.is_empty() {
            return Err("検査済み入力の参照補完全域が空になった".into());
        }
        self.tick()?;
        Ok(all)
    }

    fn completion_slot_types(&self, fields: &[Fact]) -> Result<Vec<Type>, ValidationFailure> {
        self.tick()?;
        if fields.is_empty() {
            return Err("補完slotの型族が空である".into());
        }
        let mut types = Vec::new();
        for fact in fields {
            self.tick()?;
            let field = self.field(
                &fact.snapshot,
                &fact.subject,
                fact.field.as_deref().ok_or("補完slotに元field名がない")?,
            )?;
            if fact.atom.is_some()
                || field.slot != Slot::Missing
                || !self.completion_type_supported(&field.ty)?
            {
                return Err("補完slotが元の有限型の欠測fieldでない".into());
            }
            types.push(field.ty.erase());
            self.tick()?;
        }
        Ok(types)
    }

    /// 型の供給元は検査済みfieldだけとし、元slot順を保った実代入型を返す。
    pub(in crate::observed) fn completion_assignment_type(
        &self,
        fields: &[Fact],
    ) -> Result<Type, ValidationFailure> {
        let types = self.completion_slot_types(fields)?;
        let ty = assignment_type(&types);
        self.tick()?;
        Ok(ty)
    }

    fn completion_memo_key(&self, graph: &Graph, index: usize) -> MemoKey {
        (
            graph as *const Graph as usize,
            self.current_context(graph),
            self.cutoff.get().min(graph.nodes.len()),
            index,
        )
    }
    /// 選択済みの実DAGにある理由と、まだEvaluationを持たないfield Sourceを読む。
    pub(in crate::observed) fn completion_slots(
        &self,
        graph: &Graph,
        roots: &[NodeRef],
    ) -> Result<SlotCollection, ValidationFailure> {
        self.validation_graph_session(graph, || {
            self.tick()?;
            let key = (
                graph as *const Graph as usize,
                self.current_context(graph),
                self.cutoff.get().min(graph.nodes.len()),
                roots.iter().map(|r| r.0).collect(),
            );
            let cached = self.cache.borrow().completion_slots.get(&key).cloned();
            if let Some(value) = cached {
                self.tick()?;
                return Ok(value);
            }
            let value = self.completion_slots_uncached(graph, roots)?;
            self.tick()?;
            self.cache
                .borrow_mut()
                .completion_slots
                .insert(key, value.clone());
            Ok(value)
        })
    }
    fn completion_slots_uncached(
        &self,
        graph: &Graph,
        roots: &[NodeRef],
    ) -> Result<SlotCollection, ValidationFailure> {
        let mut pending = roots.to_vec();
        let mut seen = BTreeSet::new();
        // Sourceの存在とslotの実読取りを区別する。直接rootはNotImplemented時に
        // 評価器がcommit済Missingを明示したもの。通常は実理由の依存辺だけを読む。
        let direct_sources: BTreeSet<_> = roots
            .iter()
            .filter(|r| {
                matches!(
                    graph.get(**r).map(|n| &n.payload),
                    Ok(Some(Payload::Expression { .. }))
                )
            })
            .map(|r| r.0)
            .collect();
        let mut read_sources: BTreeMap<usize, Vec<Fact>> = BTreeMap::new();
        let mut slots: BTreeMap<Fact, NodeRef> = BTreeMap::new();
        let mut reasons = Vec::new();
        while let Some(reference) = pending.pop() {
            self.tick()?;
            if !seen.insert(reference.0) {
                continue;
            }
            let node = graph.get(reference)?;
            pending.extend(node.arguments.iter().copied());
            pending.extend(node.evidence.iter().copied());
            for reason in &node.reasons {
                self.tick()?;
                reasons.push(reason.clone());
                pending.extend(reason.dependencies.iter().copied());
                if matches!(reason.kind, ReasonKind::Missing) {
                    for dependency in &reason.dependencies {
                        read_sources
                            .entry(dependency.0)
                            .or_default()
                            .extend(reason.missing.iter().cloned());
                    }
                }
            }
            if let Some(judgment) = &node.judgment {
                reasons.extend(judgment.reasons.iter().cloned());
                pending.extend(judgment.evidence.iter().copied());
                for reason in &judgment.reasons {
                    pending.extend(reason.dependencies.iter().copied());
                    if matches!(reason.kind, ReasonKind::Missing) {
                        for dependency in &reason.dependencies {
                            read_sources
                                .entry(dependency.0)
                                .or_default()
                                .extend(reason.missing.iter().cloned());
                        }
                    }
                }
            }
            if let Some(Payload::Evaluation {
                expression,
                parts,
                value,
                ..
            }) = &node.payload
            {
                pending.push(*expression);
                pending.extend(*value);
                for part in parts {
                    pending.extend(part.children.iter().copied());
                }
            }
        }
        let candidates: BTreeSet<_> = direct_sources
            .iter()
            .copied()
            .chain(read_sources.keys().copied())
            .collect();
        for index in candidates {
            self.tick()?;
            let reference = NodeRef(index);
            let node = graph.get(reference)?;
            let Some(Payload::Expression {
                location: Location::Law { span },
                bindings,
                parameters,
            }) = &node.payload
            else {
                continue;
            };
            let context = graph.context_at(reference.0);
            let previous = self.context.replace(Some(context));
            let mut missing_span = *span;
            let analysis = (|| -> Result<Vec<Fact>, ValidationFailure> {
                if let Some(fields) = self.owned_call_missing_slots(graph, reference)? {
                    return Ok(fields);
                }
                if parameters.is_empty() {
                    if let Some(fields) =
                        self.owned_expression_missing_slots(graph, *span, bindings)?
                    {
                        return Ok(fields);
                    }
                    Ok(self
                        .analyze_source(graph, *span, bindings)?
                        .missing
                        .map(|missing| missing.fact)
                        .into_iter()
                        .collect())
                } else if let Some((fields, location)) =
                    self.dependent_source_missing_slots(graph, reference)?
                {
                    missing_span = location;
                    Ok(fields)
                } else {
                    // 数値全称軸を持つ実field Sourceは元template/Domainへ戻る。
                    // 依存族の所属以外は、元数値Planのfield読取りへ戻る。
                    Ok(self
                        .universal_missing_source_analysis(graph, reference)?
                        .and_then(|analysis| analysis.missing)
                        .map(|missing| missing.fact)
                        .into_iter()
                        .collect())
                }
            })();
            self.context.set(previous);
            let fields = analysis?;
            if fields.is_empty() {
                continue;
            }
            if !direct_sources.contains(&index)
                && read_sources.get(&index).is_none_or(|facts| {
                    facts.is_empty() || facts.iter().any(|fact| !fields.contains(fact))
                })
            {
                return Err("欠測理由のslotが元実読取りSourceと違う".into());
            }
            for fact in fields {
                self.tick()?;
                if !direct_sources.contains(&index)
                    && !read_sources
                        .get(&index)
                        .is_some_and(|facts| facts.contains(&fact))
                {
                    continue;
                }
                let field = self.field(
                    &fact.snapshot,
                    &fact.subject,
                    fact.field.as_deref().ok_or("欠測slotにfieldがない")?,
                )?;
                if field.slot != Slot::Missing || fact.atom.is_some() {
                    return Err("補完の元slotが現在の欠測でない".into());
                }
                let request = graph
                    .requests
                    .get(context.request)
                    .ok_or("欠測Sourceの元Requestがない")?;
                reasons.push(Reason {
                    kind: ReasonKind::Missing,
                    request: request.id.clone(),
                    dependencies: vec![reference],
                    missing: vec![fact.clone()],
                    location: Some(Location::Law { span: missing_span }),
                });
                if self.completion_type_supported(&field.ty)? {
                    slots
                        .entry(fact)
                        .and_modify(|old| {
                            if reference.0 < old.0 {
                                *old = reference;
                            }
                        })
                        .or_insert(reference);
                }
            }
        }
        if !slots.is_empty() {
            // 探索前のowner未解決は各caseの元wholeで判定し直す。
            // caseでも未解決なら、その実評価/再検査が同じ理由を再生成する。
            // 元Missing/Sourceと他の算法理由はseedにも保持する。
            let mut retained = Vec::new();
            for reason in reasons {
                self.tick()?;
                if !matches!(&reason.kind,
                    ReasonKind::UnsupportedAlgorithm { method, .. }
                        if method == "unresolved_owned_expression_family")
                {
                    retained.push(reason);
                }
            }
            reasons = retained;
        }
        canonical_reasons(&mut reasons, &self.control)?;
        let (fields, sources) = slots.into_iter().unzip();
        Ok((fields, sources, reasons))
    }

    fn completion_seed(
        &self,
        graph: &Graph,
        reference: NodeRef,
    ) -> Result<Seed, ValidationFailure> {
        self.validation_graph_session(graph, || {
            self.tick()?;
            let key = self.completion_memo_key(graph, reference.0);
            let cached = self.cache.borrow().completion_seeds.get(&key).cloned();
            if let Some(value) = cached {
                self.tick()?;
                return Ok(value);
            }
            let value = self.completion_seed_uncached(graph, reference)?;
            self.tick()?;
            self.cache
                .borrow_mut()
                .completion_seeds
                .insert(key, value.clone());
            Ok(value)
        })
    }
    fn completion_seed_uncached(
        &self,
        graph: &Graph,
        reference: NodeRef,
    ) -> Result<Seed, ValidationFailure> {
        let node = graph.get(reference)?;
        let Some(Payload::CompletionSeed {
            location,
            parameters,
            bindings,
            roots,
            fields,
            sources,
        }) = &node.payload
        else {
            return Err("補完の元Sourceがない".into());
        };
        let context = graph.context_at(reference.0);
        if context.case.is_some()
            || context.frame.is_some()
            || context.iteration.is_some()
            || context.instance.is_some()
        {
            return Err("補完Seedが元Request rootでない".into());
        }
        let request = graph
            .requests
            .get(context.request)
            .ok_or("補完Seedの元Requestがない")?;
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
            .ok_or("補完Seedの元宣言がない")?;
        let (params, body, guard, ty) = match &declaration.signature {
            Signature::View {
                params,
                body,
                returns,
            } if request.kind == QuestionKind::Evaluate => (params, *body, None, returns.erase()),
            Signature::Law {
                params,
                body,
                guard,
                ..
            } if request.kind == QuestionKind::Check => (params, *body, *guard, Type::Bool),
            _ => return Err("補完Seedの問いと宣言が違う".into()),
        };
        let body_location = Location::Law {
            span: self.inputs.law().exprs[body].span,
        };
        let guard_location = guard.map(|id| Location::Law {
            span: self.inputs.law().exprs[id].span,
        });
        if location != &body_location && Some(location) != guard_location.as_ref() {
            return Err("補完Seedが元body/guard出現でない".into());
        }
        let expected_free: Vec<_> = params
            .iter()
            .filter(|p| {
                !request
                    .arguments
                    .iter()
                    .any(|a| a.name == format!("bind.{}", p.name))
            })
            .map(|p| (p.name.clone(), p.ty.erase()))
            .collect();
        let fixed: Vec<_> = params
            .iter()
            .filter(|p| {
                request
                    .arguments
                    .iter()
                    .any(|a| a.name == format!("bind.{}", p.name))
            })
            .collect();
        if parameters != &expected_free
            || bindings.len() != fixed.len()
            || roots.is_empty()
            || fields.is_empty()
            || fields.len() != sources.len()
        {
            return Err("補完Seedの自由parameter/固定束縛/欠測族が違う".into());
        }
        let mut scope = Scope::default();
        scope.readings.insert(declaration.reading.clone());
        let mut support = Vec::new();
        for (p, b) in fixed.iter().zip(bindings) {
            self.completion_seed_binding(graph, request, p, b, context, reference.0)?;
            scope.merge(&graph.get(b.value)?.scope);
        }
        for root in roots {
            self.tick()?;
            if root.0 >= reference.0 || graph.context_at(root.0).request != context.request {
                return Err("補完Seedに未来/別Requestのrootがある".into());
            }
            self.validate_at(graph, graph.get(*root)?, root.0)?;
            scope.merge(&graph.get(*root)?.scope);
            support.extend(graph.get(*root)?.support.iter().cloned());
        }
        let (expected_fields, expected_sources, reasons) = self.completion_slots(graph, roots)?;
        if *fields != expected_fields || *sources != expected_sources {
            return Err("補完Seedのslot identity/元field出現が違う".into());
        }
        let types = self.completion_slot_types(fields)?;
        let assignments = self.completion_assignment_context(fields)?;
        scope.merge(&assignments.scope);
        support.extend(assignments.support);
        for source in sources {
            self.tick()?;
            if source.0 >= reference.0 {
                return Err("補完SeedのfieldSourceが既出でない".into());
            }
        }
        scope.completions = true;
        support.sort();
        support.dedup();
        let expected_arguments: Vec<_> = bindings
            .iter()
            .map(|b| b.value)
            .chain(roots.iter().copied())
            .chain(sources.iter().copied())
            .collect();
        let source_ty = if Some(location) == guard_location.as_ref() {
            Type::Bool
        } else {
            ty.clone()
        };
        if node.ty != NodeType::Expression(source_ty.clone())
            || !matches!(&node.rule, Rule::Input {kind:"law",location:actual} if actual == location)
            || node.arguments != expected_arguments
            || !node.support.is_empty()
            || !node.evidence.is_empty()
            || node.judgment.is_some()
            || node.scope != scope
            || !reasons_equal(&node.reasons, &reasons)
        {
            return Err("補完Seedの型/元辺/Scope/理由が違う".into());
        }
        Ok(Seed {
            reference,
            context,
            location: location.clone(),
            bindings: bindings.clone(),
            fields: fields.clone(),
            types,
            sources: sources.clone(),
            scope,
            support,
            reasons,
            ty: source_ty,
        })
    }

    fn completion_domain(
        &self,
        graph: &Graph,
        seed: &Seed,
        domain: NodeRef,
    ) -> Result<Vec<NodeRef>, ValidationFailure> {
        self.validation_graph_session(graph, || {
            self.tick()?;
            let key = (
                graph as *const Graph as usize,
                self.current_context(graph),
                self.cutoff.get().min(graph.nodes.len()),
                seed.reference.0,
                domain.0,
            );
            let cached = self.cache.borrow().completion_domains.get(&key).cloned();
            if let Some(value) = cached {
                self.tick()?;
                return Ok(value);
            }
            let value = self.completion_domain_uncached(graph, seed, domain)?;
            self.tick()?;
            self.cache
                .borrow_mut()
                .completion_domains
                .insert(key, value.clone());
            Ok(value)
        })
    }
    fn completion_domain_uncached(
        &self,
        graph: &Graph,
        seed: &Seed,
        domain: NodeRef,
    ) -> Result<Vec<NodeRef>, ValidationFailure> {
        let node = graph.get(domain)?;
        let Some(Payload::Domain { ty, elements }) = &node.payload else {
            return Err("補完の有限代入域がない".into());
        };
        if domain.0 <= seed.reference.0
            || graph.context_at(domain.0) != seed.context
            || *ty != assignment_type(&seed.types)
            || node.ty != NodeType::Domain
            || !clean(node, "domain")
            || !node.reasons.is_empty()
            || node.scope != seed.scope
            || node.support != seed.support
            || node.arguments
                != std::iter::once(seed.reference)
                    .chain(elements.iter().copied())
                    .collect::<Vec<_>>()
        {
            return Err("補完Domainの型/元Seed/Scope/支持が違う".into());
        }
        let enumeration = self.completion_assignments(&seed.fields, &mut |_, _| {})?;
        if elements.is_empty() || elements.len() != enumeration.values.len() {
            return Err("補完Domainが空/全域件数と違う".into());
        }
        let mut seen = Vec::new();
        for element in elements {
            self.tick()?;
            if element.0 >= domain.0 || graph.context_at(element.0) != seed.context {
                return Err("補完memberが既出の元Contextでない".into());
            }
            let member = graph.get(*element)?;
            let value = graph.scalar(*element)?;
            components(value, &seed.types, self.inputs.law(), &self.control)?;
            if member.ty != NodeType::Value(ty.clone())
                || !clean(member, "domain")
                || !member.reasons.is_empty()
                || member.arguments != [seed.reference]
                || member.scope != seed.scope
                || member.support != seed.support
                || !data::contains(&enumeration.values, value, &self.control)?
                || data::contains(&seen, value, &self.control)?
            {
                return Err("補完memberの元型/代入/重複/producerが違う".into());
            }
            seen.push(value.clone());
        }
        Ok(elements.clone())
    }

    pub(in crate::observed) fn completion_values(
        &self,
        graph: &Graph,
        case: usize,
    ) -> Result<Vec<(Fact, NodeRef, Scalar)>, ValidationFailure> {
        self.validation_graph_session(graph, || {
            self.tick()?;
            let record = graph.cases.get(case).ok_or("補完case索引がない")?;
            let limit = self.cutoff.get().min(graph.nodes.len());
            let prefix = std::iter::once(record.seed)
                .chain([record.domain, record.member])
                .chain(record.values.iter().copied())
                .map(|r| r.0)
                .max()
                .ok_or("補完caseの元producerがない")?;
            if prefix >= limit {
                return Err("補完caseに未出producerがある".into());
            }
            // assignmentの証拠はcase本体より前のcaller prefixだけに属する。
            // 深いcalleeのContext/全称Planを元の欠測slotへ逆流させない。
            let old_context = self.context.replace(Some(record.caller));
            let old_limit = self.cutoff.replace(prefix + 1);
            let old_universal = self.universal_context.replace(None);
            let result = (|| {
                let key = self.completion_memo_key(graph, case);
                let cached = self.cache.borrow().completion_cases.get(&key).cloned();
                if let Some(value) = cached {
                    self.tick()?;
                    return Ok(value);
                }
                let value = self.completion_values_uncached(graph, case)?;
                self.tick()?;
                self.cache
                    .borrow_mut()
                    .completion_cases
                    .insert(key, value.clone());
                Ok(value)
            })();
            self.universal_context.replace(old_universal);
            self.cutoff.set(old_limit);
            self.context.set(old_context);
            result
        })
    }
    fn completion_values_uncached(
        &self,
        graph: &Graph,
        case: usize,
    ) -> Result<Vec<(Fact, NodeRef, Scalar)>, ValidationFailure> {
        let record = graph.cases.get(case).ok_or("補完case索引がない")?;
        let seed = self.completion_seed(graph, record.seed)?;
        if record.caller != seed.context || record.caller.case.is_some() {
            return Err("補完caseの元callerが違う".into());
        }
        let elements = self.completion_domain(graph, &seed, record.domain)?;
        if !elements.contains(&record.member) || record.values.len() != seed.fields.len() {
            return Err("補完caseのmember/slot数が違う".into());
        }
        let values = components(
            graph.scalar(record.member)?,
            &seed.types,
            self.inputs.law(),
            &self.control,
        )?;
        let mut result = Vec::new();
        for (i, (&reference, value)) in record.values.iter().zip(values).enumerate() {
            self.tick()?;
            let node = graph.get(reference)?;
            data::check(graph.scalar(reference)?, self.inputs.law(), &self.control)?;
            if reference.0 <= record.domain.0
                || graph.context_at(reference.0) != seed.context
                || node.ty != NodeType::Value(seed.types[i].clone())
                || !data::equal(graph.scalar(reference)?, &value, &self.control)?
                || !clean(node, "domain")
                || node.arguments != [record.seed, record.domain, record.member, seed.sources[i]]
                || node.scope != seed.scope
                || node.support != seed.support
                || !node.reasons.is_empty()
            {
                return Err("補完slot projectionが元member/field/producerと違う".into());
            }
            result.push((seed.fields[i].clone(), reference, value));
        }
        Ok(result)
    }

    pub(in crate::observed) fn completion_slot(
        &self,
        graph: &Graph,
        fact: &Fact,
    ) -> Result<Option<NodeRef>, ValidationFailure> {
        let Some(case) = self.current_context(graph).case else {
            return Ok(None);
        };
        Ok(self
            .completion_values(graph, case)?
            .into_iter()
            .find(|(field, _, _)| field == fact)
            .map(|(_, reference, _)| reference))
    }

    /// Seedは観測rootの固定Refを持つ。各caseのbindが再生成したRefは、そのcaseの
    /// 元body Sourceへliteralに結び、元selector・署名・Input subject producerを照合する。
    fn completion_case_bindings(
        &self,
        graph: &Graph,
        seed: &Seed,
        source: NodeRef,
        bindings: &[Binding],
        context: super::super::call::Context,
    ) -> Result<(), ValidationFailure> {
        if graph.context_at(source.0) != context
            || context.case.is_none()
            || context.frame.is_some()
            || context.iteration.is_some()
            || context.instance.is_some()
        {
            return Err("補完固定束縛の元Sourceが別case producer".into());
        }
        let source_bindings = self.expression_bindings(graph, source)?;
        if bindings != source_bindings {
            return Err("補完whole固定束縛が元case Sourceと違う".into());
        }
        let request = graph
            .requests
            .get(context.request)
            .ok_or("補完caseの元Requestがない")?;
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
            .ok_or("補完caseの元宣言がない")?;
        let params = match &declaration.signature {
            Signature::View { params, .. } | Signature::Law { params, .. } => params,
            _ => return Err("補完case対象署名が違う".into()),
        };
        let fixed: Vec<_> = params
            .iter()
            .filter(|p| {
                request
                    .arguments
                    .iter()
                    .any(|a| a.name == format!("bind.{}", p.name))
            })
            .collect();
        if bindings.len() != fixed.len() || seed.bindings.len() != fixed.len() {
            return Err("補完case固定parameter件数が違う".into());
        }
        for ((parameter, binding), observed) in fixed.iter().zip(bindings).zip(&seed.bindings) {
            self.tick()?;
            if binding.name != parameter.name
                || binding.ty != parameter.ty.erase()
                || observed.name != binding.name
                || observed.ty != binding.ty
                || binding.value.0 >= source.0
            {
                return Err("補完case固定bindings署名/producerが違う".into());
            }
            let selected = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", parameter.name))
                .ok_or("補完case固定selectorがない")?;
            if matches!(&selected.value, Selector::Answer { .. }) {
                if binding.value != observed.value {
                    return Err("補完case固定Answerが元Seedのproducerでない".into());
                }
                self.validate_at(graph, graph.get(binding.value)?, binding.value.0)?;
                continue;
            }
            if graph.context_at(binding.value.0) != context {
                return Err("補完case固定subjectが別producer".into());
            }
            let Selector::Subject { snapshot, subject } = &selected.value else {
                return Err("補完case固定selectorがsubjectでない".into());
            };
            let subject = self.subject(snapshot, subject)?;
            let expected = Scalar::Subject {
                snapshot: subject.snapshot.clone(),
                subject: subject.id.clone(),
                entity: subject.ty.clone(),
            };
            let producer = graph.get(binding.value)?;
            if graph.scalar(binding.value)? != &expected
                || graph.scalar(observed.value)? != &expected
                || producer.ty != NodeType::Value(parameter.ty.erase())
                || !matches!(&producer.rule,Rule::Input{kind:"subject",location:Location::ArchMap{pointer,span:None}} if pointer==&subject.pointer)
                || !producer.arguments.is_empty()
            {
                return Err("補完case固定bindingが元selectorのInput subjectでない".into());
            }
            self.validate_at(graph, producer, binding.value.0)?;
        }
        Ok(())
    }

    fn completion_aggregate(
        &self,
        graph: &Graph,
        seed_ref: NodeRef,
        domain: NodeRef,
        evaluations: &[NodeRef],
        propositions: &[NodeRef],
    ) -> Result<Aggregate, ValidationFailure> {
        let seed = self.completion_seed(graph, seed_ref)?;
        let elements = self.completion_domain(graph, &seed, domain)?;
        if evaluations.len() != elements.len()
            || (!propositions.is_empty() && propositions.len() != elements.len())
        {
            return Err("補完全検査のcoverage件数が違う".into());
        }
        let request = &graph.requests[seed.context.request];
        let mut scope = seed.scope.clone();
        let mut support = seed.support.clone();
        let mut reasons = seed.reasons.clone();
        let mut seen = Vec::new();
        let mut case_values = Vec::new();
        for &evaluation in evaluations {
            self.tick()?;
            let context = graph.context_at(evaluation.0);
            let index = context.case.ok_or("補完内whole評価にcaseがない")?;
            let case = graph.cases.get(index).ok_or("whole評価のcase索引がない")?;
            if context.request != seed.context.request
                || context.frame.is_some()
                || context.iteration.is_some()
                || context.instance.is_some()
                || case.seed != seed_ref
                || case.domain != domain
                || case.caller != seed.context
                || !elements.contains(&case.member)
                || seen.contains(&case.member)
            {
                return Err("補完全検査に別case/重複memberがある".into());
            }
            self.completion_values(graph, index)?;
            seen.push(case.member);
            self.recheck_evaluation(graph, evaluation)?;
            let (expression, bindings, v) = self.evaluation(graph, evaluation)?;
            let declaration = &self.inputs.law().declarations[request.declaration()];
            let body = match &declaration.signature {
                Signature::View { body, .. } | Signature::Law { body, .. } => *body,
                _ => return Err("補完の対象宣言が違う".into()),
            };
            let raw_source = if request.kind == QuestionKind::Check {
                let proposition = propositions
                    .iter()
                    .copied()
                    .find(|r| graph.context_at(r.0) == context);
                if let Some(proposition) = proposition {
                    let p = graph.get(proposition)?;
                    if p.arguments.get(1) != Some(&evaluation) {
                        return Err("補完case命題が別whole評価を指す".into());
                    }
                    self.validate_at(graph, p, proposition.0)?;
                }
                // guard/familyの集約式は元body Sourceを保持する。実際の適用は既存再検査が照合する。
                if let Some(&instance) = graph.get(evaluation)?.arguments.first() {
                    match &graph.get(instance)?.payload {
                        Some(Payload::LawInstance { body, .. }) => *body,
                        Some(Payload::ParameterizedTransform {
                            operation: TransformOp::Not,
                            ..
                        }) if instance == expression
                            && self.universal_owned_evaluation(graph, evaluation)? =>
                        {
                            // 上でwhole自体を再検査済み。全域guardの固定含意式は、
                            // 元Law body Sourceへの既定not/and/not辺を明示的に辿る。
                            self.universal_raw_body(graph, expression)?
                        }
                        _ => expression,
                    }
                } else {
                    expression
                }
            } else {
                expression
            };
            self.source_matches(graph, raw_source, body)?;
            self.completion_case_bindings(graph, &seed, raw_source, bindings, context)?;
            case_values.push(v.map(|v| graph.scalar(v)).transpose()?);
            scope.merge(&graph.get(evaluation)?.scope);
            support.extend(graph.get(evaluation)?.support.iter().cloned());
            reasons.extend(graph.get(evaluation)?.reasons.iter().cloned());
        }
        if !propositions.is_empty() {
            for &proposition in propositions {
                self.tick()?;
                let node = graph.get(proposition)?;
                if node.ty != NodeType::Proposition
                    || !evaluations.iter().any(|e| {
                        node.arguments.get(1) == Some(e)
                            && graph.context_at(e.0) == graph.context_at(proposition.0)
                    })
                {
                    return Err("補完case命題とwhole評価が一対一でない".into());
                }
                if propositions.iter().filter(|r| **r == proposition).count() != 1 {
                    return Err("補完case命題を重複した".into());
                }
                self.validate_at(graph, node, proposition.0)?;
                scope.merge(&node.scope);
                support.extend(node.support.iter().cloned());
                reasons.extend(node.reasons.iter().cloned());
            }
        }
        support.sort();
        support.dedup();
        let outcome = value_equality::all_cases(&case_values, self.inputs.law(), &self.control)?;
        if outcome.unsupported {
            reasons.push(value_comparison_reason(
                request,
                &seed.ty,
                &seed.location,
                seed.reference,
            ));
        }
        canonical_reasons(&mut reasons, &self.control)?;
        Ok(Aggregate {
            seed,
            evaluations: evaluations.to_vec(),
            scope,
            support,
            reasons,
            value: outcome.value,
            pair: outcome.pair,
        })
    }

    fn completion_evaluation_parts(
        &self,
        graph: &Graph,
        node: &Node,
    ) -> Result<Option<EvaluationParts>, ValidationFailure> {
        let Some(Payload::Evaluation {
            expression, parts, ..
        }) = &node.payload
        else {
            return Ok(None);
        };
        if !matches!(
            &graph.get(*expression)?.payload,
            Some(Payload::CompletionSeed { .. })
        ) {
            return Ok(None);
        }
        let domain = *node.arguments.get(1).ok_or("補完集約の代入Domainがない")?;
        let evaluations = parts
            .first()
            .ok_or("補完集約のpartがない")?
            .children
            .clone();
        let count = evaluations.len();
        if node.arguments.first() != Some(expression)
            || node.arguments.get(2..2 + count) != Some(evaluations.as_slice())
        {
            return Err("補完集約の実case辺が違う".into());
        }
        let propositions = node
            .arguments
            .get(2 + count..)
            .ok_or("補完集約辺がない")?
            .to_vec();
        Ok(Some((*expression, domain, evaluations, propositions)))
    }

    /// 証拠は集約値より先に置かれる。元caseのroot出現/命題からwholeだけを復元する。
    fn completion_producers(
        &self,
        graph: &Graph,
        seed: &Seed,
        domain: NodeRef,
        limit: usize,
    ) -> Result<(Vec<NodeRef>, Vec<NodeRef>), ValidationFailure> {
        let request = &graph.requests[seed.context.request];
        let declaration = &self.inputs.law().declarations[request.declaration()];
        let body = match &declaration.signature {
            Signature::View { body, .. } | Signature::Law { body, .. } => *body,
            _ => return Err("補完producer宣言がない".into()),
        };
        let mut evaluations = Vec::new();
        let mut propositions = Vec::new();
        for (i, node) in graph.nodes[..limit.min(graph.nodes.len())]
            .iter()
            .enumerate()
        {
            self.tick()?;
            let context = graph.context_at(i);
            let Some(case) = context.case.and_then(|c| graph.cases.get(c)) else {
                continue;
            };
            if context.request != seed.context.request
                || context.frame.is_some()
                || context.iteration.is_some()
                || context.instance.is_some()
                || case.seed != seed.reference
                || case.domain != domain
            {
                continue;
            }
            if request.kind == QuestionKind::Check {
                if !matches!(&node.payload, Some(Payload::Proposition { .. })) {
                    continue;
                }
                let evaluation = *node.arguments.get(1).ok_or("補完case命題の評価がない")?;
                evaluations.push(evaluation);
                propositions.push(NodeRef(i));
            } else if let Some(Payload::Evaluation { expression, .. }) = &node.payload {
                let Some(
                    Payload::Expression {
                        location: Location::Law { span },
                        ..
                    }
                    | Payload::CompletionSeed {
                        location: Location::Law { span },
                        ..
                    },
                ) = &graph.get(*expression)?.payload
                else {
                    // 数値差などの合成式は、元bodyを返す実Sourceではない。
                    continue;
                };
                if *span == self.inputs.law().exprs[body].span {
                    evaluations.push(NodeRef(i));
                }
            }
        }
        Ok((evaluations, propositions))
    }

    fn completion_evidence(
        &self,
        graph: &Graph,
        node: &Node,
        a: &Aggregate,
        domain: NodeRef,
    ) -> Result<(), ValidationFailure> {
        let mut full = 0;
        let mut pair = 0;
        for &reference in &node.evidence {
            self.tick()?;
            let proof = graph.get(reference)?;
            if proof.arguments.get(..2) != Some([a.seed.reference, domain].as_slice()) {
                return Err("補完集約の証拠が別Seed/Domain".into());
            }
            self.validate_at(graph, proof, reference.0)?;
            match &proof.payload {
                Some(Payload::FiniteExhaustion { instances, .. })
                    if instances.len() == a.evaluations.len()
                        && instances.iter().all(|r| a.evaluations.contains(r)) =>
                {
                    full += 1
                }
                Some(Payload::CompletionPair {
                    first_result,
                    second_result,
                    ..
                }) if a.evaluations.contains(first_result)
                    && a.evaluations.contains(second_result) =>
                {
                    pair += 1
                }
                _ => return Err("補完集約に別wholeの証拠がある".into()),
            }
        }
        if full != usize::from(a.value.is_some()) || pair != usize::from(a.pair.is_some()) {
            return Err("補完集約の全検査/補完対が不足/余分".into());
        }
        Ok(())
    }

    pub(in crate::observed) fn validate_completion_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<bool, ValidationFailure> {
        if node.arguments.iter().any(|r| r.0 >= limit) {
            return Err("補完nodeが未来を参照する".into());
        }
        if matches!(&node.payload, Some(Payload::CompletionSeed { .. })) {
            // 未挿入nodeも元入力へ照合するため、一時Graphを作らず同じ構造検査を行う。
            self.completion_seed_node(graph, node, limit)?;
            return Ok(true);
        }
        if let Some(Payload::CompletionInstance {
            name,
            role,
            bindings,
            guard,
            body,
            occurrence,
        }) = &node.payload
        {
            let seed = self.completion_seed(graph, *body)?;
            let request = &graph.requests[seed.context.request];
            let d = &self.inputs.law().declarations[request.declaration()];
            let Signature::Law {
                role: r, guard: g, ..
            } = &d.signature
            else {
                return Err("補完命題の対象がLawでない".into());
            };
            let offset = 1 + usize::from(guard.is_some());
            if name != &d.name
                || *role
                    != if *r == Role::Required {
                        "required"
                    } else {
                        "optional"
                    }
                || bindings != &seed.bindings
                || occurrence != &(Location::Law { span: d.span })
                || node.arguments.first() != Some(body)
                || graph.context_at(limit) != seed.context
                || !clean(node, "law_instance")
                || !node.reasons.is_empty()
            {
                return Err("補完LawInstanceの元宣言/Context/bindingsが違う".into());
            }
            match (guard, g) {
                (Some(actual), Some(id)) => {
                    let s = self.completion_seed(graph, *actual)?;
                    if s.location
                        != (Location::Law {
                            span: self.inputs.law().exprs[*id].span,
                        })
                        || s.fields != seed.fields
                        || s.sources != seed.sources
                        || s.context != seed.context
                        || node.arguments.get(1) != Some(actual)
                    {
                        return Err("補完guardSeedが元Lawと違う".into());
                    }
                }
                (None, None) => {}
                _ => return Err("補完LawInstanceのguardが違う".into()),
            }
            let props = node
                .arguments
                .get(offset..)
                .ok_or("補完LawInstanceにcase命題がない")?;
            let mut evals = Vec::new();
            for p in props {
                evals.push(
                    *graph
                        .get(*p)?
                        .arguments
                        .get(1)
                        .ok_or("case命題にwhole評価がない")?,
                );
            }
            let first = *evals.first().ok_or("補完LawInstanceのcaseが空")?;
            let c = graph
                .cases
                .get(
                    graph
                        .context_at(first.0)
                        .case
                        .ok_or("case命題の補完がない")?,
                )
                .ok_or("case索引がない")?;
            let a = self.completion_aggregate(graph, *body, c.domain, &evals, props)?;
            if node.ty != NodeType::LawInstance
                || node.scope != a.scope
                || node.support != a.support
            {
                return Err("補完LawInstanceの全case支持/Scopeが違う".into());
            }
            return Ok(true);
        }
        let first = node.arguments.first().copied();
        let seed_ref = first.filter(|r| {
            matches!(
                graph.get(*r).map(|n| &n.payload),
                Ok(Some(Payload::CompletionSeed { .. }))
            )
        });
        if let Some(seed_ref) = seed_ref {
            let seed = self.completion_seed(graph, seed_ref)?;
            if let Some(Payload::Domain { ty, elements }) = &node.payload {
                self.completion_domain_node(graph, node, limit, &seed, ty, elements)?;
                return Ok(true);
            }
            if let Some(Payload::Scalar(value)) = &node.payload {
                if matches!(&node.rule, Rule::Construction("domain")) {
                    self.completion_assignment_node(graph, node, &seed, value)?;
                    return Ok(true);
                }
                if matches!(&node.rule, Rule::Construction("evaluation")) {
                    let domain = *node.arguments.get(1).ok_or("補完値のDomainがない")?;
                    let a = self.completion_aggregate(
                        graph,
                        seed_ref,
                        domain,
                        &node.arguments[2..],
                        &[],
                    )?;
                    if node.ty != NodeType::Value(seed.ty.clone())
                        || match &a.value {
                            Some(expected) => !data::equal(expected, value, &self.control)?,
                            None => true,
                        }
                        || node.scope != a.scope
                        || node.support != a.support
                        || !matches!(&node.rule, Rule::Construction("evaluation"))
                        || node.judgment.is_some()
                        || !node.reasons.is_empty()
                        || graph.context_at(limit) != seed.context
                    {
                        return Err("全補完値が元whole全検査と違う".into());
                    }
                    self.completion_evidence(graph, node, &a, domain)?;
                    return Ok(true);
                }
            }
            if let Some(Payload::FiniteExhaustion {
                domain,
                checked,
                instances,
            }) = &node.payload
            {
                let a = self.completion_aggregate(graph, seed_ref, *domain, instances, &[])?;
                if node.ty != NodeType::Evidence
                    || !clean(node, "evidence")
                    || !node.reasons.is_empty()
                    || a.value.is_none()
                    || *checked != instances.len()
                    || node.arguments
                        != std::iter::once(seed_ref)
                            .chain([*domain])
                            .chain(instances.iter().copied())
                            .collect::<Vec<_>>()
                    || node.scope != a.scope
                    || node.support != a.support
                    || graph.context_at(limit) != seed.context
                {
                    return Err("補完全検査の全coverage/同一結果が違う".into());
                }
                return Ok(true);
            }
            if let Some(Payload::CompletionPair {
                fields,
                first,
                second,
                first_result,
                second_result,
            }) = &node.payload
            {
                self.completion_pair_node(
                    graph,
                    node,
                    limit,
                    &seed,
                    fields,
                    first,
                    second,
                    *first_result,
                    *second_result,
                )?;
                return Ok(true);
            }
        }
        if let Some((seed, domain, evals, props)) = self.completion_evaluation_parts(graph, node)? {
            let a = self.completion_aggregate(graph, seed, domain, &evals, &props)?;
            let Some(Payload::Evaluation {
                expression: _,
                bindings,
                parts,
                value,
                applicability,
            }) = &node.payload
            else {
                unreachable!()
            };
            if node.ty != NodeType::Evaluation(a.seed.ty.clone())
                || !matches!(&node.rule, Rule::Construction("evaluation"))
                || node.judgment.is_some()
                || bindings != &a.seed.bindings
                || parts.len() != 1
                || parts[0].location != a.seed.location
                || parts[0].residual.is_some()
                || parts[0].value != *value
                || *applicability != "applicable"
                || node.scope != a.scope
                || node.support != a.support
                || !reasons_equal(&node.reasons, &a.reasons)
                || graph.context_at(limit) != a.seed.context
                || (graph.requests[a.seed.context.request].kind == QuestionKind::Check
                    && props.len() != evals.len())
            {
                return Err("補完集約Evaluationの元case/型/支持/Scopeが違う".into());
            }
            self.completion_evidence(graph, node, &a, domain)?;
            match (value, &a.value) {
                (Some(reference), Some(expected)) => {
                    let producer = graph.get(*reference)?;
                    if !data::equal(graph.scalar(*reference)?, expected, &self.control)?
                        || producer.arguments
                            != std::iter::once(seed)
                                .chain([domain])
                                .chain(evals.iter().copied())
                                .collect::<Vec<_>>()
                        || graph.context_at(reference.0) != a.seed.context
                    {
                        return Err("補完集約値が別producer".into());
                    }
                    self.validate_at(graph, producer, reference.0)?;
                }
                (None, None) => {}
                _ => return Err("補完集約値の有無が違う".into()),
            }
            return Ok(true);
        }
        if let Some(Payload::Proposition { instance }) = &node.payload
            && matches!(
                &graph.get(*instance)?.payload,
                Some(Payload::CompletionInstance { .. })
            )
        {
            self.validate_at(graph, graph.get(*instance)?, instance.0)?;
            let evaluation = *node.arguments.get(1).ok_or("補完命題の集約評価がない")?;
            let e = graph.get(evaluation)?;
            let (seed, domain, evals, props) = self
                .completion_evaluation_parts(graph, e)?
                .ok_or("補完命題が元集約評価を指さない")?;
            let Some(Payload::CompletionInstance {
                body: instance_seed,
                guard: instance_guard,
                ..
            }) = &graph.get(*instance)?.payload
            else {
                unreachable!()
            };
            let instance_props = graph
                .get(*instance)?
                .arguments
                .get(1 + usize::from(instance_guard.is_some())..)
                .ok_or("補完LawInstanceのcase命題群がない")?;
            if *instance_seed != seed
                || instance_props.len() != props.len()
                || instance_props.iter().any(|r| !props.contains(r))
            {
                return Err("補完命題のLawInstanceと集約Evaluationが別Seed/case群".into());
            }
            self.validate_at(graph, e, evaluation.0)?;
            let a = self.completion_aggregate(graph, seed, domain, &evals, &props)?;
            let status = match &a.value {
                Some(Scalar::Bool(true)) => Decision::Established,
                Some(Scalar::Bool(false)) => Decision::Refuted,
                None => Decision::Undetermined,
                _ => return Err("補完Lawの値がBoolでない".into()),
            };
            if node.ty != NodeType::Proposition
                || !matches!(&node.rule, Rule::Construction("proposition"))
                || node.arguments != [*instance, evaluation]
                || node.scope != a.scope
                || node.support != a.support
                || !reasons_equal(&node.reasons, &a.reasons)
                || !node.judgment.as_ref().is_some_and(|j| {
                    j.status == status
                        && j.evidence == node.evidence
                        && reasons_equal(&j.reasons, &a.reasons)
                })
                || graph.context_at(limit) != a.seed.context
            {
                return Err("補完命題の判断/支持/元wholeが違う".into());
            }
            self.completion_evidence(graph, node, &a, domain)?;
            if node.evidence != e.evidence {
                return Err("補完命題と集約評価の証拠が違う".into());
            }
            return Ok(true);
        }
        if self.current_context(graph).case.is_some()
            && matches!(&node.payload, Some(Payload::Scalar(_)))
            && node.arguments.len() == 3
            && matches!((&node.rule,&graph.get(node.arguments[0])?.payload),
            (Rule::Input {kind:"law",location:Location::Law {span}},
             Some(Payload::Expression {location:Location::Law {span:source_span},parameters,..}))
            if span==source_span && parameters.is_empty()
                && self.completion_field_owner_span(*source_span)?.is_some())
        {
            self.completion_field_node(graph, node, limit)?;
            return Ok(true);
        }
        Ok(false)
    }

    // Seedでも固定Answerは元の出力/射影へ戻り、値の一致だけでproducerを代用しない。
    fn completion_seed_binding(
        &self,
        graph: &Graph,
        request: &Request,
        parameter: &crate::law::model::Param,
        binding: &Binding,
        context: super::super::call::Context,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        if parameter.name != binding.name
            || parameter.ty.erase() != binding.ty
            || binding.value.0 >= limit
            || graph.scalar(binding.value)?.ty() != binding.ty
        {
            return Err("補完Seedの固定binding署名・型・prefixが違う".into());
        }
        let selected = request
            .arguments
            .iter()
            .find(|a| a.name == format!("bind.{}", parameter.name))
            .ok_or("Seed固定引数がない")?;
        match &selected.value {
            selector @ Selector::Answer { .. } => {
                self.answer_binding_matches(graph, selector, binding.value, parameter.span)?;
            }
            Selector::Subject { snapshot, subject } => {
                let actual = self.subject(snapshot, subject)?;
                if graph.context_at(binding.value.0) != context
                    || graph.scalar(binding.value)?
                        != &(Scalar::Subject {
                            snapshot: snapshot.clone(),
                            subject: subject.clone(),
                            entity: actual.ty.clone(),
                        })
                {
                    return Err("補完Seed固定subjectが元Requestと違う".into());
                }
            }
            _ => return Err("Seed固定引数が元subject/Answerでない".into()),
        }
        self.validate_at(graph, graph.get(binding.value)?, binding.value.0)?;
        Ok(())
    }

    // 未挿入のSeedはpayloadを直接読む。参照先nodeの検査は同じ元入力照合を使う。
    fn completion_seed_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let Some(Payload::CompletionSeed {
            location,
            parameters,
            bindings,
            roots,
            fields,
            sources,
        }) = &node.payload
        else {
            return Err("Seed payloadがない".into());
        };
        let context = graph.context_at(limit);
        if context.case.is_some()
            || context.frame.is_some()
            || context.iteration.is_some()
            || context.instance.is_some()
            || roots.is_empty()
            || fields.is_empty()
        {
            return Err("補完Seedの元Context/族が不正".into());
        }
        let request = graph
            .requests
            .get(context.request)
            .ok_or("Seed Requestがない")?;
        let d = self
            .inputs
            .law()
            .declarations
            .get(request.declaration())
            .ok_or("Seed宣言がない")?;
        let (params, body, guard, ty) = match &d.signature {
            Signature::View {
                params,
                body,
                returns,
            } if request.kind == QuestionKind::Evaluate => (params, *body, None, returns.erase()),
            Signature::Law {
                params,
                body,
                guard,
                ..
            } if request.kind == QuestionKind::Check => (params, *body, *guard, Type::Bool),
            _ => return Err("Seed署名が違う".into()),
        };
        let is_guard = guard.is_some_and(|g| {
            *location
                == (Location::Law {
                    span: self.inputs.law().exprs[g].span,
                })
        });
        if *location
            != (Location::Law {
                span: self.inputs.law().exprs[body].span,
            })
            && !is_guard
        {
            return Err("Seed位置が元body/guardでない".into());
        }
        let free: Vec<_> = params
            .iter()
            .filter(|p| {
                !request
                    .arguments
                    .iter()
                    .any(|a| a.name == format!("bind.{}", p.name))
            })
            .map(|p| (p.name.clone(), p.ty.erase()))
            .collect();
        let fixed: Vec<_> = params
            .iter()
            .filter(|p| {
                request
                    .arguments
                    .iter()
                    .any(|a| a.name == format!("bind.{}", p.name))
            })
            .collect();
        if parameters != &free || fixed.len() != bindings.len() {
            return Err("Seed元parameterが違う".into());
        }
        let mut scope = Scope::default();
        scope.readings.insert(d.reading.clone());
        for (p, b) in fixed.iter().zip(bindings) {
            self.completion_seed_binding(graph, request, p, b, context, limit)?;
            scope.merge(&graph.get(b.value)?.scope);
        }
        for root in roots {
            self.tick()?;
            if root.0 >= limit || graph.context_at(root.0).request != context.request {
                return Err("Seed rootが未来/別Request".into());
            }
            self.validate_at(graph, graph.get(*root)?, root.0)?;
            scope.merge(&graph.get(*root)?.scope);
        }
        let (fs, ss, rs) = self.completion_slots(graph, roots)?;
        self.completion_slot_types(fields)?;
        let assignments = self.completion_assignment_context(fields)?;
        scope.merge(&assignments.scope);
        scope.completions = true;
        if *fields != fs
            || *sources != ss
            || node.ty != NodeType::Expression(if is_guard { Type::Bool } else { ty })
            || !matches!(&node.rule,Rule::Input{kind:"law",location:l}if l==location)
            || node.arguments
                != bindings
                    .iter()
                    .map(|b| b.value)
                    .chain(roots.iter().copied())
                    .chain(sources.iter().copied())
                    .collect::<Vec<_>>()
            || !node.support.is_empty()
            || !node.evidence.is_empty()
            || node.judgment.is_some()
            || node.scope != scope
            || !reasons_equal(&node.reasons, &rs)
        {
            return Err("Seed元slot/Scope/辺/理由が違う".into());
        }
        Ok(())
    }
    fn completion_domain_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
        seed: &Seed,
        ty: &Type,
        elements: &[NodeRef],
    ) -> Result<(), ValidationFailure> {
        if *ty != assignment_type(&seed.types)
            || node.ty != NodeType::Domain
            || !clean(node, "domain")
            || !node.reasons.is_empty()
            || node.scope != seed.scope
            || node.support != seed.support
            || graph.context_at(limit) != seed.context
            || node.arguments
                != std::iter::once(seed.reference)
                    .chain(elements.iter().copied())
                    .collect::<Vec<_>>()
        {
            return Err("補完Domain元型/Context/支持が違う".into());
        }
        let all = self.completion_assignments(&seed.fields, &mut |_, _| {})?;
        if elements.is_empty() || elements.len() != all.values.len() {
            return Err("補完Domain全件数が違う".into());
        }
        let mut seen = Vec::new();
        for r in elements {
            self.tick()?;
            let n = graph.get(*r)?;
            let v = graph.scalar(*r)?;
            self.completion_assignment_node(graph, n, seed, v)?;
            if r.0 >= limit
                || graph.context_at(r.0) != seed.context
                || !data::contains(&all.values, v, &self.control)?
                || data::contains(&seen, v, &self.control)?
            {
                return Err("補完Domainの漏れ/重複/別producer".into());
            }
            seen.push(v.clone());
        }
        Ok(())
    }
    fn completion_assignment_node(
        &self,
        graph: &Graph,
        node: &Node,
        seed: &Seed,
        value: &Scalar,
    ) -> Result<(), ValidationFailure> {
        if !clean(node, "domain")
            || !node.reasons.is_empty()
            || node.scope != seed.scope
            || node.support != seed.support
        {
            return Err("補完代入のScope/支持が違う".into());
        }
        if node.arguments == [seed.reference] {
            components(value, &seed.types, self.inputs.law(), &self.control)?;
            if self.completion_has_references(&seed.types)? {
                let all = self.completion_assignments(&seed.fields, &mut |_, _| {})?;
                if !data::contains(&all.values, value, &self.control)? {
                    return Err("参照補完memberが元入力に整合する全域にない".into());
                }
            }
            if node.ty != NodeType::Value(assignment_type(&seed.types)) {
                return Err("補完member型が違う".into());
            }
            return Ok(());
        }
        data::check(value, self.inputs.law(), &self.control)?;
        let [actual, domain, member, source] = node.arguments.as_slice() else {
            return Err("補完projectionの元辺が違う".into());
        };
        if *actual != seed.reference {
            return Err("補完projectionが別Seed".into());
        }
        let elements = self.completion_domain(graph, seed, *domain)?;
        if !elements.contains(member) {
            return Err("補完projectionのmemberがDomainにない".into());
        }
        let i = seed
            .sources
            .iter()
            .position(|r| r == source)
            .ok_or("補完projectionのfieldSourceがない")?;
        let values = components(
            graph.scalar(*member)?,
            &seed.types,
            self.inputs.law(),
            &self.control,
        )?;
        let mut matches = data::equal(value, &values[i], &self.control)?
            && node.ty == NodeType::Value(seed.types[i].clone());
        // 一つのFamily Sourceは複数subjectのowner slotを読む。単独の値nodeは
        // このSourceが読むmember成分であることを示し、slotごとの対応は
        // completion_values_uncachedがCase.valuesの元順で厳密に照合する。
        if !matches {
            for j in i + 1..seed.sources.len() {
                self.tick()?;
                if seed.sources[j] == *source
                    && node.ty == NodeType::Value(seed.types[j].clone())
                    && data::equal(value, &values[j], &self.control)?
                {
                    matches = true;
                    break;
                }
            }
        }
        if !matches {
            return Err("補完projectionのslot値/型が違う".into());
        }
        Ok(())
    }
    fn completion_field_owner_span(
        &self,
        span: (usize, usize),
    ) -> Result<Option<(usize, usize)>, ValidationFailure> {
        if let Some((id, count)) = self.chain_field_occurrence(span)? {
            let prefixes = self.dotted_prefixes(id)?;
            let previous = count.checked_sub(2).ok_or("補完fieldの元prefix数が違う")?;
            return Ok(Some(
                prefixes
                    .get(previous)
                    .ok_or("補完fieldの元owner prefixがない")?
                    .0,
            ));
        }
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        Ok(match &self.inputs.law().exprs[id].kind {
            ExprKind::Dotted(parts) if parts.len() > 1 => {
                Some((parts[0].span.0, parts[parts.len() - 2].span.1))
            }
            ExprKind::Field { base, .. } => Some(self.inputs.law().exprs[*base].span),
            _ => None,
        })
    }

    fn completion_field_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let [source, owner, assignment] = node.arguments.as_slice() else {
            return Err("補完fieldの元辺が違う".into());
        };
        let Some(Payload::Expression {
            location: Location::Law { span },
            bindings,
            ..
        }) = &graph.get(*source)?.payload
        else {
            return Err("補完fieldの元Sourceがない".into());
        };
        let a = self.analyze_source(graph, *span, bindings)?;
        let owner_span = self
            .completion_field_owner_span(*span)?
            .ok_or("補完field Sourceが元field構文でない")?;
        let mut owner_evaluation = None;
        for (index, candidate) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if graph.context_at(index) != self.current_context(graph) {
                continue;
            }
            let Some(Payload::Evaluation {
                expression,
                bindings: actual,
                ..
            }) = &candidate.payload
            else {
                continue;
            };
            if actual != bindings {
                continue;
            }
            let Some(
                Payload::Expression {
                    location: Location::Law { span },
                    ..
                }
                | Payload::CompletionSeed {
                    location: Location::Law { span },
                    ..
                },
            ) = &graph.get(*expression)?.payload
            else {
                continue;
            };
            if *span != owner_span {
                continue;
            }
            if candidate
                .arguments
                .first()
                .is_some_and(|r| graph.get(*r).is_ok_and(|n| n.ty == NodeType::LawInstance))
            {
                continue;
            }
            if owner_evaluation.replace(NodeRef(index)).is_some() {
                return Err("補完fieldの元owner評価が一意でない".into());
            }
        }
        let owner_evaluation = owner_evaluation.ok_or("補完fieldの既出実owner評価がない")?;
        self.recheck_evaluation(graph, owner_evaluation)?;
        if self.evaluation(graph, owner_evaluation)?.2 != Some(*owner) {
            return Err("補完field ownerが元AST実評価のproducerでない".into());
        }
        let fact = a.missing.ok_or("補完fieldが元欠測でない")?.fact;
        let expected = self
            .completion_slot(graph, &fact)?
            .ok_or("補完fieldの代入がない")?;
        let Scalar::Subject {
            snapshot, subject, ..
        } = graph.scalar(*owner)?
        else {
            return Err("補完field ownerがRefでない".into());
        };
        let types = self.completion_slot_types(std::slice::from_ref(&fact))?;
        let Some(Payload::Scalar(value)) = &node.payload else {
            return Err("補完field値がない".into());
        };
        data::check(value, self.inputs.law(), &self.control)?;
        if *assignment != expected
            || fact.snapshot != *snapshot
            || fact.subject != *subject
            || node.ty != NodeType::Value(types[0].clone())
            || graph.scalar(*assignment)?.ty() != types[0]
            || !data::equal(graph.scalar(*assignment)?, value, &self.control)?
            || !matches!(&node.rule,Rule::Input{kind:"law",location:Location::Law{span:s}}if s==span)
            || node.scope != a.scalar_scope.unwrap_or(a.scope)
            || !node.support.is_empty()
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
            || node.judgment.is_some()
            || graph.context_at(source.0) != graph.context_at(limit)
        {
            return Err("補完fieldの元slot/共有代入/producerが違う".into());
        }
        Ok(())
    }
    #[allow(clippy::too_many_arguments)]
    fn completion_pair_node(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
        seed: &Seed,
        fields: &[Fact],
        first: &[NodeRef],
        second: &[NodeRef],
        first_result: NodeRef,
        second_result: NodeRef,
    ) -> Result<(), ValidationFailure> {
        let domain = *node.arguments.get(1).ok_or("補完対Domainがない")?;
        let (evals, props) = self.completion_producers(graph, seed, domain, limit)?;
        let a = self.completion_aggregate(graph, seed.reference, domain, &evals, &props)?;
        if fields != seed.fields
            || first.len() != fields.len()
            || second.len() != fields.len()
            || !a.evaluations.contains(&first_result)
            || !a.evaluations.contains(&second_result)
            || first_result == second_result
        {
            return Err("補完対のslot/whole結果が違う".into());
        }
        for (result, values) in [(first_result, first), (second_result, second)] {
            let case = graph
                .context_at(result.0)
                .case
                .ok_or("補完対結果にcaseなし")?;
            let expected = self.completion_values(graph, case)?;
            if expected.iter().map(|(_, r, _)| *r).collect::<Vec<_>>() != values {
                return Err("補完対の型付き代入が別case".into());
            }
        }
        let left = self
            .evaluation(graph, first_result)?
            .2
            .ok_or("補完対の第一結果が未知")?;
        let right = self
            .evaluation(graph, second_result)?
            .2
            .ok_or("補完対の第二結果が未知")?;
        if value_equality::equal(
            graph.scalar(left)?,
            graph.scalar(right)?,
            self.inputs.law(),
            &self.control,
        )? != Some(false)
            || node.ty != NodeType::Evidence
            || !clean(node, "evidence")
            || !node.reasons.is_empty()
            || node.scope != a.scope
            || node.support != a.support
            || graph.context_at(limit) != seed.context
            || node.arguments
                != [seed.reference, domain, first_result, second_result]
                    .into_iter()
                    .chain(first.iter().copied())
                    .chain(second.iter().copied())
                    .collect::<Vec<_>>()
        {
            return Err("補完対の結果差/元代入/支持/Scopeが違う".into());
        }
        Ok(())
    }

    pub(in crate::observed) fn validate_completion_answer(
        &self,
        graph: &Graph,
        request: &Request,
        answer: &Answer,
    ) -> Result<bool, ValidationFailure> {
        let Some(&evaluation) = answer.outputs.get("evaluation") else {
            return Ok(false);
        };
        let node = graph.get(evaluation)?;
        let Some((seed, domain, evals, props)) = self.completion_evaluation_parts(graph, node)?
        else {
            return Ok(false);
        };
        let a = self.completion_aggregate(graph, seed, domain, &evals, &props)?;
        if graph.requests.get(a.seed.context.request) != Some(request)
            || answer.id != request.id
            || answer.scope != a.scope
            || !reasons_equal(&answer.reasons, &a.reasons)
        {
            return Err("補完Answerが元Request/Scope/理由と違う".into());
        }
        self.validate_at(graph, node, evaluation.0)?;
        if request.kind == QuestionKind::Check {
            let claim = answer.claim.ok_or("補完check claimがない")?;
            self.validate_at(graph, graph.get(claim)?, claim.0)?;
            let c = graph.get(claim)?;
            if c.arguments.get(1) != Some(&evaluation)
                || answer.outputs.get("proposition") != Some(&claim)
                || c.judgment.as_ref().map(|j| j.status) != Some(answer.status)
                || answer.evidence != c.evidence
            {
                return Err("補完Answer claim/証拠/判断が違う".into());
            }
        } else {
            let Some(Payload::Evaluation { value, .. }) = &node.payload else {
                unreachable!()
            };
            if answer.claim.is_some()
                || answer.evidence != node.evidence
                || answer.outputs.get("value").copied() != *value
                || answer.status
                    != if value.is_some() {
                        Decision::Established
                    } else {
                        Decision::Undetermined
                    }
            {
                return Err("補完view Answerの値/判断が違う".into());
            }
        }
        Ok(true)
    }
}
