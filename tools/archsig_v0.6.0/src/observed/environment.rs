//! 不変の原始観測表からの参照・slot 読取りと、生成 leaf の元入力照合。
use super::{
    control::{Checkpoint, Control, StopReason},
    data,
    input::CheckedInputs,
    numeric, quantifier,
    request::{QuestionKind, Request, Selector},
    result::*,
};
use crate::{
    archmap::{Slot, Subject, Value},
    issue::Location,
    law::ast::{BinOp, ExprKind, UnOp},
    types::Type,
};
#[path = "family.rs"]
pub(super) mod family;

use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet},
};

/// 入力照合中の metadata。Source の commit までは結果の理由へ昇格しない。
#[derive(Clone, Debug)]
pub(crate) struct PendingMissing {
    pub fact: Fact,
}
#[derive(Clone, Debug)]
pub(crate) struct SourceAnalysis {
    pub scope: Scope,
    pub known_value: Option<Scalar>,
    pub missing: Option<PendingMissing>,
    pub support: Vec<Fact>,
    pub scalar_scope: Option<Scope>,
}

#[derive(Clone)]
struct SourceValue {
    scope: Scope,
    known_value: Option<Scalar>,
    support: Vec<Fact>,
    scalar_scope: Option<Scope>,
}

#[derive(Clone)]
enum LexicalOrigin {
    Let(usize),
    Iteration(usize),
    Pattern {
        matching: usize,
        arm: usize,
        binder: data::Binder,
    },
}

type SourceCacheEntry = (
    super::call::Context,
    usize,
    (usize, usize),
    Vec<Binding>,
    SourceAnalysis,
);
type FrameInputs = (Vec<Binding>, BTreeMap<String, SourceValue>, Scope);
type NodeRefKey = (super::call::Context, usize);
type IterationInputs = (NodeRef, Scalar, SourceAnalysis);

// 一回の不変Graph借用に閉じた成功照合だけを共有する。呼出し終了時に破棄する。
#[derive(Default)]
struct ValidationCache {
    checked: BTreeSet<NodeRefKey>,
    rechecked: BTreeSet<NodeRefKey>,
    sources: Vec<SourceCacheEntry>,
    frames: BTreeMap<(usize, usize), FrameInputs>,
    iterations: BTreeMap<(usize, usize), IterationInputs>,
}

#[cfg(test)]
type NameTokenObserver = Box<dyn FnMut((usize, usize), super::call::Context)>;

pub(crate) struct Environment<'a> {
    pub inputs: &'a CheckedInputs,
    subjects: BTreeMap<(String, String), &'a Subject>,
    fields: BTreeMap<(String, String, String), &'a crate::archmap::Field>,
    atoms: BTreeMap<String, Fact>,
    modes: BTreeMap<String, &'static str>,
    snapshot_origins: BTreeMap<String, String>,
    expressions: BTreeMap<(usize, usize), usize>,
    control: Control,
    context: Cell<Option<super::call::Context>>,
    scoped_context: Cell<Option<super::call::Context>>,
    validation_depth: Cell<usize>,
    cutoff: Cell<usize>,
    cache: RefCell<ValidationCache>,
    #[cfg(test)]
    optional_name_context: Cell<Option<super::call::Context>>,
    #[cfg(test)]
    name_token_observer: RefCell<Option<NameTokenObserver>>,
}
impl<'a> Environment<'a> {
    pub fn new(inputs: &'a CheckedInputs, control: &mut Control) -> Result<Self, StopReason> {
        let mut subjects = BTreeMap::new();
        let mut fields = BTreeMap::new();
        let mut atoms = BTreeMap::new();
        let mut modes = BTreeMap::new();
        let mut snapshot_origins = BTreeMap::new();
        let mut expressions = BTreeMap::new();
        for origin in &inputs.archmap().origins {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            modes.insert(origin.id.clone(), origin.mode.wire());
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        for (id, e) in inputs.law().exprs.iter().enumerate() {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            if inputs.law().expr_type(id).is_some() {
                expressions.insert(e.span, id);
            }
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        control.checkpoint(Checkpoint::FiniteIteration)?;
        for snapshot in &inputs.archmap().snapshots {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            snapshot_origins.insert(snapshot.id.clone(), snapshot.origin.clone());
            for s in &snapshot.subjects {
                control.checkpoint(Checkpoint::FiniteIteration)?;
                subjects.insert((s.snapshot.clone(), s.id.clone()), s);
                for field in &s.fields {
                    control.checkpoint(Checkpoint::FiniteIteration)?;
                    fields.insert(
                        (s.snapshot.clone(), s.id.clone(), field.name.clone()),
                        field,
                    );
                    if let Slot::Known { atom, pointer, .. } = &field.slot {
                        atoms.insert(
                            pointer.clone(),
                            Fact {
                                snapshot: s.snapshot.clone(),
                                subject: s.id.clone(),
                                field: Some(field.name.clone()),
                                atom: Some(atom.clone()),
                            },
                        );
                    }
                    control.checkpoint(Checkpoint::FiniteIteration)?;
                }
                control.checkpoint(Checkpoint::FiniteIteration)?;
            }
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        control.checkpoint(Checkpoint::FiniteIteration)?;
        Ok(Self {
            inputs,
            subjects,
            fields,
            atoms,
            modes,
            snapshot_origins,
            expressions,
            control: control.clone(),
            context: Cell::new(None),
            scoped_context: Cell::new(None),
            validation_depth: Cell::new(0),
            cutoff: Cell::new(usize::MAX),
            cache: RefCell::new(ValidationCache::default()),
            #[cfg(test)]
            optional_name_context: Cell::new(None),
            #[cfg(test)]
            name_token_observer: RefCell::new(None),
        })
    }
    pub fn subject(&self, snapshot: &str, id: &str) -> Result<&'a Subject, String> {
        self.subjects
            .get(&(snapshot.into(), id.into()))
            .copied()
            .ok_or_else(|| "検査済み subject が見つからない".into())
    }
    pub fn origin_mode(&self, id: &str) -> Result<&'static str, String> {
        self.modes
            .get(id)
            .copied()
            .ok_or_else(|| "origin が見つからない".into())
    }
    pub fn field(
        &self,
        snapshot: &str,
        subject: &str,
        name: &str,
    ) -> Result<&'a crate::archmap::Field, String> {
        self.fields
            .get(&(snapshot.into(), subject.into(), name.into()))
            .copied()
            .ok_or_else(|| "field がない".into())
    }
    pub(super) fn finite_values(
        &self,
        ty: &Type,
        observer: &mut dyn FnMut(&'static str, usize),
    ) -> Result<super::finite::Enumeration, ValidationFailure> {
        // callbackは元の不変三表だけを読む。依存を再構成する呼出しごとに走査し、
        // Source解析・生成済みDomainの再検査へ実評価の結果を転記しない。
        let observer = RefCell::new(observer);
        super::finite::values(
            ty,
            self.inputs.law(),
            &self.control,
            &mut |entity| {
                self.reference_roster(entity, &mut |index| {
                    observer.borrow_mut()("ref_roster", index)
                })
            },
            &mut |index| observer.borrow_mut()("type_enum", index),
        )
    }
    fn reference_roster(
        &self,
        entity: &str,
        observer: &mut dyn FnMut(usize),
    ) -> Result<super::finite::Enumeration, ValidationFailure> {
        use crate::definition::PrimitiveSignature;
        if !matches!(
            self.inputs
                .law()
                .definitions
                .declarations
                .get(entity)
                .map(|d| &d.signature),
            Some(
                PrimitiveSignature::Entity { .. }
                    | PrimitiveSignature::Arrow { .. }
                    | PrimitiveSignature::Correspondence { .. }
            )
        ) {
            return Err("plain参照族の元完全型名が原始参照型でない".into());
        }
        let mut family = super::finite::Enumeration::default();
        for (index, snapshot) in self.inputs.archmap().snapshots.iter().enumerate() {
            observer(index);
            self.tick()?;
            family.scope.snapshots.insert(snapshot.id.clone());
            family
                .scope
                .modes
                .insert(self.origin_mode(&snapshot.origin)?.into());
            for subject in &snapshot.subjects {
                self.tick()?;
                if subject.ty == entity {
                    family.values.push(Scalar::Subject {
                        snapshot: snapshot.id.clone(),
                        subject: subject.id.clone(),
                        entity: entity.into(),
                    });
                    family
                        .scope
                        .modes
                        .insert(self.origin_mode(&subject.origin)?.into());
                    family.support.push(Fact {
                        snapshot: snapshot.id.clone(),
                        subject: subject.id.clone(),
                        field: None,
                        atom: None,
                    });
                }
                self.tick()?;
            }
            self.tick()?;
        }
        Ok(family)
    }
    fn tick(&self) -> Result<(), ValidationFailure> {
        self.control
            .clone()
            .checkpoint(Checkpoint::FiniteIteration)
            .map_err(ValidationFailure::Stop)
    }
    pub fn scope(
        &self,
        s: &Subject,
        reading: &str,
        atom_origin: Option<&str>,
    ) -> Result<Scope, String> {
        let mut scope = Scope::default();
        scope.readings.insert(reading.into());
        scope.snapshots.insert(s.snapshot.clone());
        scope.modes.insert(self.origin_mode(&s.origin)?.into());
        let origin = self
            .snapshot_origins
            .get(&s.snapshot)
            .ok_or("snapshot がない")?;
        scope.modes.insert(self.origin_mode(origin)?.into());
        if let Some(origin) = atom_origin {
            scope.modes.insert(self.origin_mode(origin)?.into());
        }
        Ok(scope)
    }
    pub fn fact(&self, f: &Fact) -> Result<(), String> {
        let s = self.subject(&f.snapshot, &f.subject)?;
        match (&f.field, &f.atom) {
            (None, None) => Ok(()),
            (Some(field), atom) => {
                let field = self.field(&s.snapshot, &s.id, field)?;
                match (&field.slot, atom) {
                    (Slot::Missing, None) => Ok(()),
                    (Slot::Known { atom: a, .. }, Some(b)) if a == b => Ok(()),
                    _ => Err("FactPointer が原始 slot と合わない".into()),
                }
            }
            _ => Err("subject 存在に atom が付いている".into()),
        }
    }
    pub fn validate(&self, graph: &Graph, node: &Node) -> Result<(), ValidationFailure> {
        self.validate_at(graph, node, graph.nodes.len())
    }
    #[cfg(test)]
    pub(super) fn recheck_node(
        &self,
        graph: &Graph,
        node: &Node,
        index: usize,
    ) -> Result<(), ValidationFailure> {
        self.validate_at(graph, node, index)
    }
    #[cfg(test)]
    pub(super) fn observe_optional_name_token(
        &self,
        observer: impl FnMut((usize, usize), super::call::Context) + 'static,
    ) {
        *self.name_token_observer.borrow_mut() = Some(Box::new(observer));
    }
    // 新規挿入時は prefix の長さ、既存 node はその挿入位置を cutoff とする。
    // 後からできた Source/Evaluation を、先行 Scalar の証人にしない。
    fn validate_at(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        self.validation_session(|| {
            self.tick()?;
            let context = graph.context_at(limit);
            // 渡されたcloneや未挿入nodeには既存nodeの照合成功を使わない。
            let resident = graph
                .nodes
                .get(limit)
                .is_some_and(|actual| std::ptr::eq(actual, node));
            let key = (context, limit);
            if resident && self.cache.borrow().checked.contains(&key) {
                return Ok(());
            }
            let previous = self.context.replace(Some(context));
            let old_cutoff = self.cutoff.replace(limit);
            let result = self
                .validate_in_context(graph, node, limit)
                .map_err(|failure| match failure {
                    ValidationFailure::UnsupportedExpression { feature, .. } => {
                        ValidationFailure::Internal(format!(
                            "未対応の元式から生成済みnodeを照合できない: {feature}"
                        ))
                    }
                    other => other,
                });
            self.cutoff.set(old_cutoff);
            self.context.set(previous);
            if resident && result.is_ok() {
                self.cache.borrow_mut().checked.insert(key);
            }
            result
        })
    }
    fn validation_session<T>(
        &self,
        run: impl FnOnce() -> Result<T, ValidationFailure>,
    ) -> Result<T, ValidationFailure> {
        let depth = self.validation_depth.get();
        if depth == 0 {
            *self.cache.borrow_mut() = ValidationCache::default();
        }
        self.validation_depth.set(depth + 1);
        let result = run();
        self.validation_depth.set(depth);
        // success/失敗/停止の全経路で、次のGraph/改変nodeへ成功を持ち越さない。
        if depth == 0 {
            *self.cache.borrow_mut() = ValidationCache::default();
        }
        result
    }
    fn resolve_analysis(
        &self,
        graph: &Graph,
        mut analysis: SourceAnalysis,
        arguments: &[NodeRef],
    ) -> Result<SourceAnalysis, ValidationFailure> {
        for reference in arguments {
            self.tick()?;
            let node = graph.get(*reference)?;
            if matches!(&node.payload, Some(Payload::Evaluation { .. })) {
                self.recheck_evaluation(graph, *reference)?;
            } else {
                self.validate_at(graph, node, reference.0)?;
            }
            analysis.scope.merge_quantifiers(&node.scope);
            if let Some(scope) = &mut analysis.scalar_scope {
                scope.merge_quantifiers(&node.scope);
            }
        }
        Ok(analysis)
    }
    fn iteration_syntax(
        &self,
        id: usize,
    ) -> Result<(Option<usize>, Vec<usize>), ValidationFailure> {
        match self.inputs.law().exprs[id].kind {
            ExprKind::SetComp {
                domain,
                elem,
                filter,
                ..
            } => Ok((Some(domain), std::iter::once(elem).chain(filter).collect())),
            ExprKind::Quant { .. } => {
                let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
                Ok((spec.domain, vec![spec.body]))
            }
            _ => Err("反復元が内包/In量化でない".into()),
        }
    }
    fn current_context(&self, graph: &Graph) -> super::call::Context {
        self.context.get().unwrap_or(graph.active)
    }
    fn validate_in_context(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        for (index, quantifier) in node.scope.quantifiers.iter().enumerate() {
            self.tick()?;
            if node.scope.quantifiers[..index].contains(quantifier) {
                return Err("Scopeに同じ実量化descriptorが重複する".into());
            }
        }
        for reference in node
            .arguments
            .iter()
            .chain(&node.evidence)
            .copied()
            .chain(node.scope.quantifiers.iter().filter_map(|q| q.domain))
        {
            self.tick()?;
            if reference.0 >= limit {
                return Err("nodeの元依存/証拠/量化域が既出でない".into());
            }
            graph.get(reference)?;
        }
        let context = self.current_context(graph);
        if let Some(index) = context.iteration {
            let iteration = graph.iterations.get(index).ok_or("nodeの反復がない")?;
            if iteration.caller.instance != context.instance
                || iteration.caller.request != context.request
                || iteration.caller.frame != context.frame
                || iteration
                    .caller
                    .iteration
                    .is_some_and(|parent| parent >= index)
            {
                return Err("反復の親Contextが違う".into());
            }
            self.iteration_input(graph, index)?;
            let own_span = match &node.payload {
                Some(Payload::Expression {
                    location: Location::Law { span },
                    ..
                }) => Some(*span),
                Some(Payload::Evaluation { expression, .. }) => {
                    Some(self.expression_span(graph, *expression)?)
                }
                _ => match &node.rule {
                    Rule::Input {
                        kind: "law",
                        location: Location::Law { span },
                    } => Some(*span),
                    _ => None,
                },
            };
            if let Some(span) = own_span {
                let comp_span = self.expression_span(graph, iteration.source)?;
                let (_, bodies) = self.iteration_syntax(
                    *self.expressions.get(&comp_span).ok_or("反復元ASTがない")?,
                )?;
                if !bodies.into_iter().any(|child| {
                    let body = self.inputs.law().exprs[child].span;
                    body.0 <= span.0 && span.1 <= body.1
                }) {
                    return Err("反復nodeの元出現がfilter/elem外にある".into());
                }
            }
        }
        if let Some(index) = context.instance {
            let record = graph.instances.get(index).ok_or("nodeの実instanceがない")?;
            if record.caller.request != context.request || record.caller.instance.is_some() {
                return Err("nodeの実instance Requestが違う".into());
            }
        }
        if !graph.requests.is_empty() && graph.requests.get(context.request).is_none() {
            return Err("nodeの元Requestがない".into());
        }
        if let Some(frame) = context.frame
            && graph
                .frames
                .get(frame)
                .ok_or("node frameがない")?
                .caller
                .request
                != context.request
        {
            return Err("nodeのRequestがcall元と違う".into());
        }
        if let Some(frame) = context.frame
            && graph
                .frames
                .get(frame)
                .ok_or("node frameがない")?
                .caller
                .instance
                != context.instance
        {
            return Err("nodeの実instanceがcall元と違う".into());
        }
        for f in &node.support {
            self.tick()?;
            self.fact(f)?;
            if f.field.is_some() && f.atom.is_none() {
                return Err("未観測 slot を support Atom にしている".into());
            }
            self.tick()?;
        }
        for reason in &node.reasons {
            self.tick()?;
            for f in &reason.missing {
                self.tick()?;
                self.fact(f)?;
                self.tick()?;
            }
            self.tick()?;
        }
        if self.validate_family_node(graph, node, limit)? {
            return Ok(());
        }
        if let Some(Payload::Scalar(scalar)) = &node.payload {
            data::check(scalar, self.inputs.law(), &self.control)?;
            match &node.rule {
                Rule::Input {
                    kind: "subject",
                    location: Location::ArchMap { pointer, .. },
                } => {
                    let Scalar::Subject {
                        snapshot,
                        subject,
                        entity,
                    } = scalar
                    else {
                        return Err("subject leaf の値が参照でない".into());
                    };
                    let s = self.subject(snapshot, subject)?;
                    if pointer != &s.pointer || entity != &s.ty {
                        return Err("subject leaf が原入力に合わない".into());
                    }
                }
                Rule::Input {
                    kind: "atom",
                    location: Location::ArchMap { pointer, .. },
                } => {
                    let mut found = false;
                    for f in &node.support {
                        self.tick()?;
                        if f.atom.is_some() {
                            let subject = self.subject(&f.snapshot, &f.subject)?;
                            let field = self.field(
                                &subject.snapshot,
                                &subject.id,
                                f.field.as_ref().ok_or("atom field がない")?,
                            )?;
                            if let Slot::Known {
                                value, pointer: p, ..
                            } = &field.slot
                                && p == pointer
                                && scalar_from(value, &field.ty, self.inputs.law(), &self.control)?
                                    .as_ref()
                                    == Some(scalar)
                            {
                                found = true;
                            }
                        }
                        self.tick()?;
                    }
                    if !found {
                        return Err("Atom 値が元 slot に合わない".into());
                    }
                    if self.current_context(graph).frame.is_some()
                        || self.current_context(graph).instance.is_some()
                        || self.current_context(graph).iteration.is_some()
                    {
                        self.call_field_source(graph, node, limit)?;
                    }
                }
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                } => {
                    let law = self.inputs.law();
                    let id = self.expressions.get(span).copied();
                    if id.is_some_and(|id| law.expr_type(id) != Some(&scalar.ty())) {
                        return Err("導出値が元式の型に合わない".into());
                    }
                    let computed = if let Some(id) = id {
                        match &law.exprs[id].kind {
                            ExprKind::Quant { .. } => self
                                .quant_scalar(graph, node, limit)?
                                .known_value
                                .ok_or("量化値が確定しない")?,
                            ExprKind::SetComp { .. } => self
                                .comprehension_source_analysis(graph, node, limit)?
                                .known_value
                                .ok_or("内包値が確定しない")?,
                            ExprKind::Call { .. } if self.named_view(id)?.is_some() => self
                                .call_source_analysis(graph, node, limit)?
                                .known_value
                                .ok_or("call結果が確定しない")?,
                            ExprKind::Let { .. } | ExprKind::If { .. } | ExprKind::Match { .. } => {
                                self.lexical_source_analysis(graph, node, limit)?
                                    .known_value
                                    .ok_or("let/if 値が全補完で確定しない")?
                            }
                            ExprKind::Binary { op, .. } if is_boolean_binary(*op) => self
                                .logic_source_analysis(graph, node, limit)?
                                .known_value
                                .ok_or("Bool 論理値が全補完で確定しない")?,
                            ExprKind::Unary { op: UnOp::Not, .. } => self
                                .logic_source_analysis(graph, node, limit)?
                                .known_value
                                .ok_or("Bool 否定値が確定しない")?,
                            ExprKind::Dotted(_)
                                if data::expression(law, id, &self.control)?.is_none() =>
                            {
                                self.lexical_source_analysis(graph, node, limit)?
                                    .known_value
                                    .ok_or("pattern値が確定しない")?
                            }
                            ExprKind::Dotted(_)
                            | ExprKind::Int(_)
                            | ExprKind::Bool(_)
                            | ExprKind::Binary { .. }
                            | ExprKind::Tuple(_)
                            | ExprKind::ListLit { .. }
                            | ExprKind::SetLit { .. }
                            | ExprKind::None(_)
                            | ExprKind::Some(_)
                            | ExprKind::Unit
                            | ExprKind::Str(_)
                            | ExprKind::Index { .. }
                            | ExprKind::Call { .. }
                            | ExprKind::Unary { op: UnOp::Neg, .. } => self
                                .scalar_source_analysis(graph, node, limit)?
                                .known_value
                                .ok_or("元 Source で生成値が確定しない")?,
                            _ => return Err("元式に対する値検査がない".into()),
                        }
                    } else {
                        self.lexical_source_analysis(graph, node, limit)?
                            .known_value
                            .ok_or("pattern fragment値がない")?
                    };
                    if &computed != scalar {
                        return Err("生成算術が元式に合わない".into());
                    }
                }
                Rule::Construction("domain") => self.domain_member(graph, node, limit)?,
                Rule::Construction("evidence") => {
                    self.quant_counter_parts(graph, node, limit)?;
                    if scalar != &Scalar::Bool(true)
                        || node.scope != graph.get(node.arguments[2])?.scope
                        || !node.support.is_empty()
                    {
                        return Err("量化のtrue要求値が違う".into());
                    }
                }
                Rule::Construction("proposition")
                    if scalar == &Scalar::Bool(true) && node.arguments.len() == 1 =>
                {
                    graph.expect(node.arguments[0], &NodeType::LawInstance)?
                }
                Rule::Construction("evaluation") if matches!(scalar, Scalar::Bool(_)) => {
                    if node.arguments.len() != 2 {
                        return Err("含意値の構成入力数が違う".into());
                    }
                    let instance = node.arguments[0];
                    let expression = node.arguments[1];
                    let expected = self.conditional_value(graph, instance, expression)?;
                    if expected.map(Scalar::Bool).as_ref() != Some(scalar) {
                        return Err("条件付き Law 値が元 guard/body の全補完と違う".into());
                    }
                    let (body, guard) = self.application_at(graph, instance)?;
                    if node.scope != self.application_context(graph, body, guard)?.1 {
                        return Err("含意 Scalar の範囲が元 Law 適用と違う".into());
                    }
                }
                Rule::Construction("evaluation") => {
                    self.residual_source_analysis(graph, node, limit)?;
                }
                _ => return Err("値 leaf の導出規則がない".into()),
            }
            let support = self.scalar_support(graph, node, limit)?;
            if node.support != support {
                return Err("値の支持が元入力・実引数の完全な集合と違う".into());
            }
        }
        if let Some(Payload::Expression {
            location: Location::Law { span },
            parameters,
            ..
        }) = &node.payload
        {
            if !matches!(&node.rule, Rule::Input {kind: "law", location: Location::Law {span: actual}} if actual == span)
                || !node.support.is_empty()
                || !node.evidence.is_empty()
                || !node.reasons.is_empty()
                || node.judgment.is_some()
            {
                return Err("元Sourceの規則・支持・証拠が違う".into());
            }
            if let Some(Payload::Expression { bindings, .. }) = &node.payload
                && node.arguments != self.source_arguments(graph, *span, bindings)?
            {
                return Err("Sourceの元束縛・call実引数辺が違う".into());
            }
            // この観測経路は元宣言parameterを全て明示束縛する。内部のlet名や
            // 欠測slotを自由parameterとして持ち込むことはできない。
            if !parameters.is_empty() {
                return Err("全明示束縛の元 Source に自由parameterがある".into());
            }
            let bytes = self.inputs.sources().law().bytes();
            if span.0 >= span.1 || bytes.get(span.0..span.1).is_none() {
                return Err("元 byte span の外".into());
            }
            let actual = self
                .expressions
                .get(span)
                .map(|&id| (id, &self.inputs.law().exprs[id]));
            if let Some((id, _)) = actual {
                let NodeType::Expression(ty) = &node.ty else {
                    return Err("式の型".into());
                };
                if self.inputs.law().expr_type(id) != Some(ty) {
                    return Err("Expression の型が元 AST に合わない".into());
                }
            } else {
                // fragment は型検査した実 Dotted の先頭 token だけである。
                // body 内の同綴りfield名・コメント・部分文字列では代用しない。
                let source = self.name_token(*span)?;
                let Some(Payload::Expression { bindings, .. }) = &node.payload else {
                    unreachable!()
                };
                let mut expected = None;
                for binding in bindings {
                    self.tick()?;
                    if binding.name == source {
                        expected = Some(binding.ty.clone());
                    }
                    self.tick()?;
                }
                if expected.is_none()
                    && let Some(argument) = self.call_parameter(graph, source)?
                    && let NodeType::Evaluation(ty) = &graph.get(argument)?.ty
                {
                    expected = Some(ty.clone());
                }
                if expected.is_none()
                    && let Some((_, value)) =
                        self.iteration_argument(graph, *span, source, bindings)?
                {
                    expected = Some(value.ty());
                }
                if expected.is_none()
                    && let Some((_, value)) =
                        self.type_iteration_argument(graph, *span, source, bindings)?
                {
                    expected = Some(value.ty());
                }
                if expected.is_none()
                    && let Some((_, _, binder)) = self.pattern_binding(*span, source)?
                {
                    expected = Some(binder.ty);
                }
                if expected.is_none() {
                    let rhs = self
                        .lexical_rhs(*span, source)?
                        .ok_or("元 AST にない式 fragment")?;
                    expected = self.inputs.law().expr_type(rhs).cloned();
                }
                if node.ty != NodeType::Expression(expected.ok_or("fragment の元型がない")?) {
                    return Err("fragment の型が元parameter/lexical右辺と違う".into());
                }
            }
        }
        if let Some(Payload::Expression {
            location: Location::Law { span },
            bindings,
            ..
        }) = &node.payload
            && node.scope != self.source_scope(graph, *span, bindings)?
        {
            return Err("Expression の範囲が元宣言・入力と違う".into());
        }
        if matches!(&node.payload, Some(Payload::Transform { .. })) {
            self.transform_scope(graph, node, limit)?;
        }
        if let Some(Payload::LawInstance {
            name,
            role,
            bindings,
            guard,
            body,
            occurrence,
        }) = &node.payload
        {
            use crate::law::{ast::Role, model::Signature};
            let d = self
                .inputs
                .law()
                .declarations
                .get(name)
                .ok_or("LawInstance の宣言がない")?;
            let Signature::Law {
                role: r,
                params,
                guard: g,
                body: b,
            } = &d.signature
            else {
                return Err("LawInstance が Law でない".into());
            };
            if role
                != &match r {
                    Role::Required => "required",
                    Role::Optional => "optional",
                }
                || occurrence != &(Location::Law { span: d.span })
            {
                return Err("LawInstance の宣言 metadata 不一致".into());
            }
            if params.len() != bindings.len() {
                return Err("LawInstance の未束縛 parameter".into());
            }
            for (p, b) in params.iter().zip(bindings) {
                self.tick()?;
                if p.name != b.name || p.ty.erase() != b.ty {
                    return Err("LawInstance の束縛署名不一致".into());
                }
                self.tick()?;
            }
            self.source_matches(graph, *body, *b)?;
            match (guard, g) {
                (Some(v), Some(e)) => self.source_matches(graph, *v, *e)?,
                (None, None) => {}
                _ => return Err("guard の出現不一致".into()),
            }
            self.application(graph, node)?;
        }
        if let Some(Payload::Evaluation {
            expression,
            bindings,
            parts,
            value,
            applicability,
        }) = &node.payload
        {
            let application = node
                .arguments
                .first()
                .copied()
                .filter(|r| matches!(graph.get(*r).map(|n| &n.ty), Ok(NodeType::LawInstance)));
            if let Some(instance) = application {
                self.validate_law_evaluation(graph, node, instance)?;
            } else {
                if *applicability != "applicable" {
                    return Err("通常式の評価に Law の適用判定を付けている".into());
                }
                if self.validate_type_binder_evaluation(graph, node, limit)? {
                    return Ok(());
                }
                if self.validate_quant_evaluation(graph, node, limit)? {
                    return Ok(());
                }
                if self.validate_comprehension_evaluation(graph, node, limit)? {
                    return Ok(());
                }
                if self.validate_call_evaluation(graph, node, limit)? {
                    return Ok(());
                }
                let span = self.expression_span(graph, *expression)?;
                let source_bindings = self.expression_bindings(graph, *expression)?;
                if graph.context_at(expression.0) != self.current_context(graph)
                    || source_bindings != bindings
                    || parts.len() != 1
                    || parts[0].location != (Location::Law { span })
                    || parts[0].value != *value
                {
                    return Err("Evaluation の原式・束縛・part が合わない".into());
                }
                let mut analysis = self.resolve_analysis(
                    graph,
                    self.analyze_source(graph, span, bindings)?,
                    &parts[0].children,
                )?;
                // 名前/括弧が再使用する値は元producerのScopeを保つ。
                // 子Evaluationの量化Scopeは、この使用位置の評価範囲である。
                if let Some(original) = self.reused_source_value(graph, span, bindings)? {
                    if *value != Some(original) || original.0 >= limit {
                        return Err("aliasの値が元ASTの実producerと違う".into());
                    }
                    self.validate_at(graph, graph.get(original)?, original.0)?;
                    analysis.scalar_scope = Some(graph.get(original)?.scope.clone());
                }
                let expected_scope = analysis.scope;
                if node.scope != expected_scope
                    || !graph
                        .get(*expression)?
                        .scope
                        .source_compatible(&expected_scope)
                {
                    return Err("Evaluation と元式の範囲が元入力と違う".into());
                }
                if node.support != analysis.support {
                    return Err("Evaluation の支持が元 AST・原始事実の完全な集合と違う".into());
                }
                let mut used_support = Vec::new();
                if let Some(reference) = value {
                    let expected = analysis
                        .scalar_scope
                        .as_ref()
                        .ok_or("元式に確定値の範囲がない")?;
                    if &graph.get(*reference)?.scope != expected {
                        return Err("評価値Scalarの範囲が元Source・束縛・originと違う".into());
                    }
                    used_support.extend(graph.get(*reference)?.support.iter().cloned());
                }
                let expected_evidence = if let Some(value) = value {
                    graph.get(*value)?.evidence.as_slice()
                } else {
                    &[]
                };
                if node.evidence != expected_evidence {
                    return Err("通常Evaluationの証拠が元値と違う".into());
                }
                let children = &parts[0].children;
                for &child in children {
                    self.tick()?;
                    used_support.extend(graph.get(child)?.support.iter().cloned());
                    self.tick()?;
                }
                used_support.sort();
                used_support.dedup();
                if node.support != used_support {
                    return Err("Evaluation の支持が使用した値・子評価の和集合と違う".into());
                }
                let children = &parts[0].children;
                let ast = self
                    .expressions
                    .get(&span)
                    .map(|id| &self.inputs.law().exprs[*id]);
                let generated_here = match ast.map(|e| &e.kind) {
                    Some(ExprKind::Dotted(parts)) => {
                        parts.len() > 1
                            || data::expression(
                                self.inputs.law(),
                                *self.expressions.get(&span).ok_or("名元ASTがない")?,
                                &self.control,
                            )?
                            .is_some()
                            || self.pattern_binding(span, &parts[0].name)?.is_some()
                            || self
                                .iteration_argument(graph, span, &parts[0].name, bindings)?
                                .is_some()
                    }
                    Some(
                        ExprKind::Int(_)
                        | ExprKind::Bool(_)
                        | ExprKind::Unary { .. }
                        | ExprKind::Binary { .. }
                        | ExprKind::Tuple(_)
                        | ExprKind::ListLit { .. }
                        | ExprKind::SetLit { .. }
                        | ExprKind::None(_)
                        | ExprKind::Some(_)
                        | ExprKind::Unit
                        | ExprKind::Str(_)
                        | ExprKind::Index { .. }
                        | ExprKind::Let { .. }
                        | ExprKind::If { .. }
                        | ExprKind::Match { .. }
                        | ExprKind::Field { .. }
                        | ExprKind::Call { .. },
                    ) => true,
                    None => {
                        if let Some(name) = self.find_name_token(span)? {
                            self.pattern_binding(span, name)?.is_some()
                                || self
                                    .iteration_argument(graph, span, name, bindings)?
                                    .is_some()
                        } else {
                            false
                        }
                    }
                    _ => false,
                };
                if generated_here
                    && value.is_some_and(|reference| {
                        graph.context_at(reference.0) != self.current_context(graph)
                    })
                {
                    return Err("元式の生成Scalarが別call/Request frameに属する".into());
                }
                // literal/演算はこの出現で新しい値を作る。op・値・引数の一致だけで
                // 別 AST や固定構成に帰属を付け替えられないよう、生成規則も結ぶ。
                // Group/field/parameter は既存の子値・原始値を再利用するため区別する。
                if matches!(
                    ast.map(|e| &e.kind),
                    Some(
                        ExprKind::Int(_)
                            | ExprKind::Bool(_)
                            | ExprKind::Unary { .. }
                            | ExprKind::Binary { .. }
                            | ExprKind::Tuple(_)
                            | ExprKind::ListLit { .. }
                            | ExprKind::SetLit { .. }
                            | ExprKind::None(_)
                            | ExprKind::Some(_)
                            | ExprKind::Unit
                            | ExprKind::Str(_)
                            | ExprKind::Index { .. }
                            | ExprKind::Call { .. }
                            | ExprKind::Let { .. }
                            | ExprKind::If { .. }
                            | ExprKind::Match { .. }
                    )
                ) && let Some(value) = value
                {
                    self.tick()?;
                    if !matches!(
                        &graph.get(*value)?.rule,
                        Rule::Input {
                            kind: "law",
                            location: Location::Law { span: source },
                        } if *source == span
                    ) {
                        return Err("生成値の規則・元 Law 出現が評価元 AST と違う".into());
                    }
                    self.tick()?;
                }
                if generated_here
                    && (ast.is_none()
                        || matches!(ast.map(|e| &e.kind), Some(ExprKind::Dotted(parts)) if parts.len() == 1 || data::expression(self.inputs.law(), *self.expressions.get(&span).ok_or("名元ASTがない")?, &self.control)?.is_some()))
                    && let Some(value) = value
                    && !matches!(&graph.get(*value)?.rule, Rule::Input { kind: "law", location: Location::Law { span: actual } } if *actual == span)
                {
                    return Err("constructor/binderの生成規則・元出現が違う".into());
                }
                let expected = match ast.map(|e| &e.kind) {
                    Some(ExprKind::Match { scrutinee, arms }) => {
                        let input = *children.first().ok_or("match実scrutinee辺がない")?;
                        let known = self
                            .evaluation(graph, input)?
                            .2
                            .map(|r| graph.scalar(r))
                            .transpose()?;
                        let id = *self.expressions.get(&span).ok_or("match元ASTがない")?;
                        let mut spans = vec![self.inputs.law().exprs[*scrutinee].span];
                        if let Some(arm) =
                            data::select(self.inputs.law(), id, known, &self.control)?
                        {
                            spans.push(self.inputs.law().exprs[arms[arm].body].span);
                        }
                        spans
                    }
                    Some(ExprKind::Let { value, body, .. }) => vec![
                        self.inputs.law().exprs[*value].span,
                        self.inputs.law().exprs[*body].span,
                    ],
                    Some(ExprKind::If {
                        cond,
                        then_branch,
                        else_branch,
                    }) => vec![
                        self.inputs.law().exprs[*cond].span,
                        self.inputs.law().exprs[*then_branch].span,
                        self.inputs.law().exprs[*else_branch].span,
                    ],
                    Some(ExprKind::Dotted(_))
                        if data::expression(
                            self.inputs.law(),
                            *self.expressions.get(&span).ok_or("constructor元式がない")?,
                            &self.control,
                        )?
                        .is_some() =>
                    {
                        vec![]
                    }
                    Some(ExprKind::Dotted(parts))
                        if parts.len() == 1
                            && self
                                .iteration_argument(graph, span, &parts[0].name, bindings)?
                                .is_some() =>
                    {
                        let (domain, _) = self
                            .iteration_argument(graph, span, &parts[0].name, bindings)?
                            .ok_or("反復domainがない")?;
                        vec![self.expression_span(graph, self.evaluation(graph, domain)?.0)?]
                    }
                    Some(ExprKind::Dotted(parts))
                        if parts.len() == 1
                            && self.pattern_binding(span, &parts[0].name)?.is_some() =>
                    {
                        let (input, _) = self
                            .pattern_argument(graph, span, &parts[0].name, bindings)?
                            .ok_or("pattern引数がない")?;
                        vec![self.expression_span(graph, self.evaluation(graph, input)?.0)?]
                    }
                    Some(ExprKind::Dotted(parts)) if parts.len() == 1 => self
                        .lexical_rhs(span, &parts[0].name)?
                        .map(|rhs| vec![self.inputs.law().exprs[rhs].span])
                        .unwrap_or_default(),
                    Some(ExprKind::Binary { lhs, rhs, .. }) => vec![
                        self.inputs.law().exprs[*lhs].span,
                        self.inputs.law().exprs[*rhs].span,
                    ],
                    Some(ExprKind::Unary { operand, .. } | ExprKind::Group(operand)) => {
                        vec![self.inputs.law().exprs[*operand].span]
                    }
                    Some(ExprKind::Field { base, .. }) => vec![self.inputs.law().exprs[*base].span],
                    Some(
                        ExprKind::Tuple(_)
                        | ExprKind::ListLit { .. }
                        | ExprKind::SetLit { .. }
                        | ExprKind::None(_)
                        | ExprKind::Some(_)
                        | ExprKind::Unit
                        | ExprKind::Str(_)
                        | ExprKind::Index { .. }
                        | ExprKind::Call { .. },
                    ) => {
                        let id = *self.expressions.get(&span).ok_or("数値構成の元式がない")?;
                        let mut spans = Vec::new();
                        for child in self.composite_children(id)?.ok_or("数値構成の子がない")?
                        {
                            self.tick()?;
                            spans.push(self.inputs.law().exprs[child].span);
                            self.tick()?;
                        }
                        spans
                    }
                    Some(ExprKind::Dotted(parts)) if parts.len() > 1 => {
                        vec![(parts[0].span.0, parts[parts.len() - 2].span.1)]
                    }
                    None => {
                        let token = std::str::from_utf8(
                            &self.inputs.sources().law().bytes()[span.0..span.1],
                        )
                        .map_err(|_| "lexical token がUTF8でない")?;
                        if let Some((input, _)) =
                            self.iteration_argument(graph, span, token, bindings)?
                        {
                            vec![self.expression_span(graph, self.evaluation(graph, input)?.0)?]
                        } else if let Some((input, _)) =
                            self.pattern_argument(graph, span, token, bindings)?
                        {
                            vec![self.expression_span(graph, self.evaluation(graph, input)?.0)?]
                        } else {
                            self.lexical_rhs(span, token)?
                                .map(|rhs| vec![self.inputs.law().exprs[rhs].span])
                                .unwrap_or_default()
                        }
                    }
                    _ => vec![],
                };
                let iteration_parameter = if let Some(name) = self.find_name_token(span)? {
                    self.iteration_argument(graph, span, name, bindings)?
                        .map(|(domain, _)| domain)
                } else {
                    None
                };
                let lexical_parameter = if let Some(name) = self.find_name_token(span)? {
                    if let Some((input, _)) = self.pattern_argument(graph, span, name, bindings)? {
                        Some(input)
                    } else {
                        self.lexical_argument(graph, span, name, bindings)?
                    }
                } else {
                    None
                };
                let parameter = if expected.is_empty() {
                    #[cfg(test)]
                    let previous_name_context = self
                        .optional_name_context
                        .replace(Some(self.current_context(graph)));
                    let name = self.find_name_token(span);
                    #[cfg(test)]
                    self.optional_name_context.set(previous_name_context);
                    let name = name?;
                    name.map(|name| self.call_parameter(graph, name))
                        .transpose()?
                        .flatten()
                } else {
                    None
                };
                let expected = if let Some(argument) = parameter {
                    vec![self.expression_span(graph, self.evaluation(graph, argument)?.0)?]
                } else {
                    expected
                };
                if iteration_parameter.is_some() && children.first().copied() != iteration_parameter
                {
                    return Err("反復名の実domain Evaluationが違う".into());
                }
                if parameter.is_some() && children.first().copied() != parameter {
                    return Err("callee parameterの実引数Evaluationが違う".into());
                }
                if lexical_parameter.is_some() && children.first().copied() != lexical_parameter {
                    return Err("lexical名の元実Evaluationが違う".into());
                }
                if children.len() != expected.len() {
                    return Err("元 AST と子 Evaluation の個数不一致".into());
                }
                let mut child_values = Vec::new();
                for (&child, expected_span) in children.iter().zip(expected) {
                    self.tick()?;
                    let (e, b, v) = self.evaluation(graph, child)?;
                    if self.expression_span(graph, e)? != expected_span
                        || ((parameter.is_none()
                            && iteration_parameter.is_none()
                            && lexical_parameter.is_none())
                            && (b != bindings
                                || graph.context_at(child.0) != self.current_context(graph)))
                    {
                        return Err("元 AST の子出現・束縛不一致".into());
                    }
                    child_values.push(v);
                    self.tick()?;
                }
                if !matches!(ast.map(|e| &e.kind), Some(ExprKind::Binary { .. }))
                    && parts[0].residual.is_some()
                {
                    return Err("比較以外の式に残差がある".into());
                }
                match ast.map(|e| &e.kind) {
                    Some(ExprKind::Match { .. }) => {
                        let known = child_values
                            .get(1)
                            .copied()
                            .flatten()
                            .map(|r| graph.scalar(r).cloned())
                            .transpose()?;
                        match (known, value) {
                            (Some(expected), Some(result))
                                if graph.scalar(*result)? == &expected
                                    && graph.get(*result)?.arguments == *children => {}
                            (None, None) => {}
                            _ => return Err("match元scrutinee・選択arm・結果辺が違う".into()),
                        }
                    }
                    Some(ExprKind::Let { .. } | ExprKind::If { .. }) => {
                        let known = match ast.map(|e| &e.kind) {
                            Some(ExprKind::Let { .. }) => child_values[1]
                                .map(|r| graph.scalar(r).cloned())
                                .transpose()?,
                            _ => conditional_branch(
                                child_values[0].map(|r| graph.scalar(r)).transpose()?,
                                child_values[1].map(|r| graph.scalar(r)).transpose()?,
                                child_values[2].map(|r| graph.scalar(r)).transpose()?,
                                &self.control,
                            )?,
                        };
                        match (known, value) {
                            (Some(expected), Some(result))
                                if graph.scalar(*result)? == &expected
                                    && graph.get(*result)?.arguments == *children => {}
                            (None, None) => {}
                            _ => return Err("let/if の元子・確定結果・構成引数が違う".into()),
                        }
                    }
                    Some(ExprKind::Int(n)) => {
                        let ty = self
                            .inputs
                            .law()
                            .expr_type(*self.expressions.get(&span).ok_or("literal元式がない")?)
                            .ok_or("literal型がない")?;
                        let expected = numeric::literal(n, ty, &self.control)?;
                        if value.map(|r| graph.scalar(r)).transpose()? != Some(&expected) {
                            return Err("整数 literal の評価値が元 AST と違う".into());
                        }
                    }
                    Some(ExprKind::Bool(b)) => {
                        if value.map(|r| graph.scalar(r)).transpose()? != Some(&Scalar::Bool(*b)) {
                            return Err("Bool literal の評価値が元 AST と違う".into());
                        }
                    }
                    Some(ExprKind::Binary { op, lhs, .. }) => {
                        let pair = child_values[0].zip(child_values[1]);
                        let computed = partial_binary(
                            *op,
                            child_values[0].map(|r| graph.scalar(r)).transpose()?,
                            child_values[1].map(|r| graph.scalar(r)).transpose()?,
                            &self.control,
                        )?;
                        match (computed, *value) {
                            (Some(expected), Some(result)) => {
                                let arguments = if is_boolean_binary(*op) {
                                    vec![children[0], children[1]]
                                } else {
                                    let (left, right) = pair.ok_or("二項演算の既知左右がない")?;
                                    vec![left, right]
                                };
                                if graph.scalar(result)? != &expected
                                    || graph.get(result)?.arguments != arguments
                                {
                                    return Err("生成演算値の元左右・演算結果が違う".into());
                                }
                            }
                            (None, None) => {}
                            _ => return Err("部分既知の元演算と結果値の有無が違う".into()),
                        }
                        match (op, pair, parts[0].residual) {
                            (BinOp::Eq, Some((left, right)), residual)
                                if numeric::is_numeric_type(
                                    self.inputs
                                        .law()
                                        .expr_type(*lhs)
                                        .ok_or("数値等号の型がない")?,
                                    &self.control,
                                )? =>
                            {
                                let residual = residual.ok_or("既知 数値等号の残差がない")?;
                                let ty = self
                                    .inputs
                                    .law()
                                    .expr_type(*lhs)
                                    .ok_or("数値等号の型がない")?;
                                graph.expect(residual, &NodeType::Value(ty.clone()))?;
                                if !matches!(
                                    graph.get(residual)?.rule,
                                    Rule::Construction("evaluation")
                                ) {
                                    return Err("数値等号残差の生成規則が違う".into());
                                }
                                if graph.get(residual)?.scope != expected_scope {
                                    return Err("数値等号残差Scalarの範囲が元等式と違う".into());
                                }
                                let difference = numeric::binary(
                                    BinOp::Sub,
                                    graph.scalar(left)?,
                                    graph.scalar(right)?,
                                    &self.control,
                                )?;
                                if graph.scalar(residual)? != &difference
                                    || graph.get(residual)?.arguments != [left, right]
                                {
                                    return Err("数値等号の残差が元左右の正確な差でない".into());
                                }
                                self.validate_at(graph, graph.get(residual)?, residual.0)?;
                            }
                            (_, _, None) => {}
                            _ => return Err("数値等号の既知左右以外に整数残差がある".into()),
                        }
                    }
                    Some(
                        ExprKind::Tuple(_)
                        | ExprKind::ListLit { .. }
                        | ExprKind::SetLit { .. }
                        | ExprKind::None(_)
                        | ExprKind::Some(_)
                        | ExprKind::Unit
                        | ExprKind::Str(_)
                        | ExprKind::Index { .. }
                        | ExprKind::Call { .. },
                    ) => {
                        let id = *self.expressions.get(&span).ok_or("数値構成の元式がない")?;
                        let mut values = Vec::new();
                        let mut arguments = Vec::new();
                        let mut known = true;
                        for child in &child_values {
                            self.tick()?;
                            if let Some(child) = child {
                                arguments.push(*child);
                                values.push(graph.scalar(*child)?.clone());
                            } else {
                                known = false;
                            }
                            self.tick()?;
                        }
                        match (known, *value) {
                            (true, Some(result)) => {
                                if graph.scalar(result)? != &self.composite_value(id, &values)?
                                    || graph.get(result)?.arguments != arguments
                                {
                                    return Err("数値構成の元子・結果値が違う".into());
                                }
                            }
                            (false, None) => {}
                            _ => return Err("未確定の数値構成から値を作っている".into()),
                        }
                    }
                    Some(ExprKind::Group(_)) => {
                        if *value != child_values[0] {
                            return Err("括弧の評価値不一致".into());
                        }
                    }
                    Some(ExprKind::Unary { op, .. }) => match (child_values[0], *value) {
                        (Some(operand), Some(result)) => {
                            let argument = if *op == UnOp::Not {
                                children[0]
                            } else {
                                operand
                            };
                            if graph.scalar(result)?
                                != &unary(*op, graph.scalar(operand)?, &self.control)?
                                || graph.get(result)?.arguments != [argument]
                            {
                                return Err("単項演算の元 operand・結果値が違う".into());
                            }
                        }
                        (None, None) => {}
                        _ => return Err("単項演算の子値と結果値の有無が違う".into()),
                    },
                    Some(ExprKind::Dotted(_))
                        if data::expression(
                            self.inputs.law(),
                            *self.expressions.get(&span).ok_or("constructor元式がない")?,
                            &self.control,
                        )?
                        .is_some() =>
                    {
                        let id = *self.expressions.get(&span).ok_or("constructor元式がない")?;
                        if value.map(|r| graph.scalar(r)).transpose()?
                            != Some(&self.composite_value(id, &[])?)
                        {
                            return Err("零引数constructor値が違う".into());
                        }
                    }
                    Some(ExprKind::Dotted(parts)) => {
                        if parts.len() == 1 {
                            self.check_name(
                                graph,
                                span,
                                bindings,
                                &parts[0].name,
                                *value,
                                &child_values,
                            )?;
                        } else {
                            self.check_field(
                                graph,
                                child_values[0],
                                &parts[parts.len() - 1].name,
                                *value,
                            )?;
                        }
                    }
                    Some(ExprKind::Field { name, .. }) => {
                        self.check_field(graph, child_values[0], &name.name, *value)?
                    }
                    None => {
                        let source = std::str::from_utf8(
                            &self.inputs.sources().law().bytes()[span.0..span.1],
                        )
                        .map_err(|_| "parameter token")?;
                        self.check_name(graph, span, bindings, source, *value, &child_values)?;
                    }
                    _ => {}
                }
            }
        }
        match &node.payload {
            Some(Payload::Domain { .. }) => self.validate_domain(graph, node, limit)?,
            Some(Payload::FiniteExhaustion { .. }) => {
                self.validate_finite_exhaustion(graph, node, limit)?
            }
            Some(Payload::Counterexample { .. })
                if node.arguments.first().is_some_and(|r| {
                    matches!(graph.get(*r).map(|n| &n.ty), Ok(NodeType::Expression(_)))
                }) =>
            {
                self.validate_quant_counter(graph, node, limit)?;
                return Ok(());
            }
            Some(Payload::EvaluationEvidence {
                instance,
                lhs,
                rhs,
                residual,
            }) => {
                let (evaluation, left, right) = self.evidence_operands(graph, node, *instance)?;
                if *lhs != left || *rhs != right {
                    return Err("評価証拠が元の左右値を指していない".into());
                }
                let Some(Payload::Evaluation { parts, .. }) = &graph.get(evaluation)?.payload
                else {
                    unreachable!()
                };
                let expression = self.evaluation(graph, evaluation)?.0;
                let expected = if matches!(
                    &graph.get(expression)?.payload,
                    Some(Payload::Transform { .. })
                ) {
                    None
                } else {
                    parts.last().ok_or("証拠の評価 part がない")?.residual
                };
                if *residual != expected {
                    return Err("証拠の残差が元評価と違う".into());
                }
            }
            Some(Payload::Counterexample {
                bindings,
                left,
                right,
                facts,
            }) => {
                let instance = *node.arguments.first().ok_or("反例に LawInstance がない")?;
                let (evaluation, l, r) = self.evidence_operands(graph, node, instance)?;
                if *left != l || *right != r {
                    return Err("反例が元式の左右値を指していない".into());
                }
                let (_, bs, v) = self.evaluation(graph, evaluation)?;
                if bs != bindings
                    || v.map(|r| graph.scalar(r)).transpose()? != Some(&Scalar::Bool(false))
                {
                    return Err("反例の元束縛・false 評価不一致".into());
                }
                if facts != &graph.get(evaluation)?.support {
                    return Err("反例 facts が元評価と違う".into());
                }
                for fact in facts {
                    self.tick()?;
                    self.fact(fact)?;
                    self.tick()?;
                }
            }
            Some(Payload::Proposition { instance }) => {
                graph.validate_proposition_evidence(node)?;
                for &reference in &node.evidence {
                    self.tick()?;
                    self.validate_at(graph, graph.get(reference)?, reference.0)?;
                    self.tick()?;
                }
                let evaluation = *node.arguments.get(1).ok_or("命題に元評価がない")?;
                self.instance_evaluation(graph, *instance, evaluation)?;
                let (_, _, v) = self.evaluation(graph, evaluation)?;
                let status = match v.map(|r| graph.scalar(r)).transpose()? {
                    Some(Scalar::Bool(true)) => Decision::Established,
                    Some(Scalar::Bool(false)) => Decision::Refuted,
                    None => Decision::Undetermined,
                    _ => return Err("命題 body の型".into()),
                };
                if node.judgment.as_ref().map(|j| j.status) != Some(status) {
                    return Err("命題判断が元 body と違う".into());
                }
            }
            _ => {}
        }
        if matches!(
            node.payload,
            Some(
                Payload::EvaluationEvidence { .. }
                    | Payload::Counterexample { .. }
                    | Payload::Proposition { .. }
            )
        ) {
            let evaluation = *node.arguments.get(1).ok_or("結論に適用評価がない")?;
            if node.support != graph.get(evaluation)?.support
                || node.scope != graph.get(evaluation)?.scope
            {
                return Err("結論の支持・範囲が適用評価と合わない".into());
            }
        }
        self.tick()?;
        Ok(())
    }
    // let/if の Scalar は未知の子を値へ補完せず、元順の子 Evaluation を引数にする。
    // Scalar の挿入位置で own Source と各子を再検査し、親がまだなくても帰属を確かめる。
    fn lexical_source_analysis(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<SourceAnalysis, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let Rule::Input {
                kind: "law",
                location: Location::Law { span },
            } = &node.rule
            else {
                return Err("let/if 値に元出現がない".into());
            };
            let id = self.expressions.get(span).copied();
            if let Some(domain) = node.arguments.first().copied()
                && graph.get(domain)?.ty == NodeType::Domain
                && let Some(name) = self.find_name_token(*span)?
            {
                let source = *graph
                    .get(domain)?
                    .arguments
                    .first()
                    .ok_or("型binder Domainの元Sourceがない")?;
                let bindings = self.expression_bindings(graph, source)?;
                if let Some((actual, expected)) =
                    self.type_iteration_argument(graph, *span, name, bindings)?
                {
                    let analysis = self.analyze_source(graph, *span, bindings)?;
                    if actual != domain
                        || node.arguments != [domain]
                        || !matches!(&node.payload,Some(Payload::Scalar(value)) if value==&expected)
                        || node.ty != NodeType::Value(expected.ty())
                        || node.scope != analysis.scope
                        || node.support != analysis.support
                        || !node.evidence.is_empty()
                        || !node.reasons.is_empty()
                    {
                        return Err("型binderの元型/要素/Domain/Scope/支持が違う".into());
                    }
                    return Ok(analysis);
                }
            }
            let binder = if let Some(name) = self.find_name_token(*span)? {
                {
                    let bindings = node
                        .arguments
                        .first()
                        .and_then(|reference| match &graph.get(*reference).ok()?.payload {
                            Some(Payload::Evaluation { bindings, .. }) => Some(bindings.as_slice()),
                            _ => None,
                        })
                        .unwrap_or(&[]);
                    if let Some(input) = self.iteration_argument(graph, *span, name, bindings)? {
                        Some(input)
                    } else {
                        self.pattern_argument(graph, *span, name, bindings)?
                    }
                }
            } else {
                None
            };
            let operands = if let Some((domain, _)) = &binder {
                let source = self.evaluation(graph, *domain)?.0;
                vec![
                    *self
                        .expressions
                        .get(&self.expression_span(graph, source)?)
                        .ok_or("反復domain元式がない")?,
                ]
            } else if let Some(id) = id {
                match self.inputs.law().exprs[id].kind {
                    ExprKind::Let { value, body, .. } => vec![value, body],
                    ExprKind::Match {
                        scrutinee,
                        ref arms,
                    } => {
                        let input = *node
                            .arguments
                            .first()
                            .ok_or("match生成値にscrutinee辺がない")?;
                        let value = self
                            .evaluation(graph, input)?
                            .2
                            .map(|v| graph.scalar(v))
                            .transpose()?;
                        let arm = data::select(self.inputs.law(), id, value, &self.control)?
                            .ok_or("未知matchに生成値がある")?;
                        vec![scrutinee, arms[arm].body]
                    }
                    ExprKind::Dotted(ref parts) if parts.len() == 1 => {
                        let (matching, _, _) = self
                            .pattern_binding(*span, &parts[0].name)?
                            .ok_or("生成値の元patternがない")?;
                        let ExprKind::Match { scrutinee, .. } =
                            self.inputs.law().exprs[matching].kind
                        else {
                            unreachable!()
                        };
                        vec![scrutinee]
                    }
                    ExprKind::If {
                        cond,
                        then_branch,
                        else_branch,
                    } => vec![cond, then_branch, else_branch],
                    _ => return Err("let/if 値の元式形が違う".into()),
                }
            } else {
                let (matching, _, _) = self
                    .pattern_binding(*span, self.name_token(*span)?)?
                    .ok_or("fragmentの元patternがない")?;
                let ExprKind::Match { scrutinee, .. } = self.inputs.law().exprs[matching].kind
                else {
                    unreachable!()
                };
                vec![scrutinee]
            };
            let Some(Payload::Scalar(scalar)) = &node.payload else {
                return Err("let/if 結果が通常値でない".into());
            };
            if node.ty != NodeType::Value(scalar.ty())
                || id.is_some_and(|id| self.inputs.law().expr_type(id) != Some(&scalar.ty()))
                || node.arguments.len() != operands.len()
            {
                return Err("let/if 値の元型・引数数が違う".into());
            }
            let mut bindings = None;
            for (&reference, operand) in node.arguments.iter().zip(operands) {
                self.tick()?;
                if reference.0 >= limit {
                    return Err("let/if の子評価が既出でない".into());
                }
                graph.expect(
                    reference,
                    &NodeType::Evaluation(
                        self.inputs
                            .law()
                            .expr_type(operand)
                            .ok_or("let/if 元子の型がない")?
                            .clone(),
                    ),
                )?;
                if binder
                    .as_ref()
                    .is_some_and(|(domain, _)| *domain != reference)
                    || (binder.is_none()
                        && graph.context_at(reference.0) != self.current_context(graph))
                {
                    return Err("let/if子が別frameに属する".into());
                }
                self.recheck_evaluation(graph, reference)?;
                let (expression, actual, _) = self.evaluation(graph, reference)?;
                self.source_matches(graph, expression, operand)?;
                if bindings.is_some_and(|previous| previous != actual) {
                    return Err("let/if の子束縛が違う".into());
                }
                bindings = Some(actual);
                self.tick()?;
            }
            let bindings = bindings.ok_or("let/if の子束縛がない")?;
            let mut source_found = false;
            for (index, source) in graph.nodes.iter().enumerate().take(limit) {
                self.tick()?;
                if graph.context_at(index) == self.current_context(graph)
                    && source.ty == NodeType::Expression(scalar.ty())
                    && matches!(&source.payload, Some(Payload::Expression {location: Location::Law {span: actual}, bindings: b, parameters}) if actual == span && b == bindings && parameters.is_empty())
                {
                    let candidate = (|| -> Result<(), ValidationFailure> {
                        if !matches!(&source.rule, Rule::Input {kind: "law", location: Location::Law {span: actual}} if actual == span)
                        {
                            return Err("let/if Source の元規則が違う".into());
                        }
                        let mut arguments = Vec::new();
                        for binding in bindings {
                            self.tick()?;
                            if binding.value.0 >= index {
                                return Err("let/if Source の束縛が既出でない".into());
                            }
                            arguments.push(binding.value);
                            self.tick()?;
                        }
                        if self.source_arguments(graph, *span, bindings)? != source.arguments {
                            return Err("let/if Source の引数と束縛が違う".into());
                        }
                        self.validate_at(graph, source, index)
                    })();
                    match candidate {
                        Ok(()) => source_found = true,
                        Err(ValidationFailure::Stop(reason)) => {
                            return Err(ValidationFailure::Stop(reason));
                        }
                        Err(ValidationFailure::Internal(_)) => {}
                        Err(failure @ ValidationFailure::UnsupportedExpression { .. }) => {
                            return Err(failure);
                        }
                    }
                }
                self.tick()?;
            }
            if !source_found {
                return Err("let/if 値に既出の own Source がない".into());
            }
            let analysis = self.resolve_analysis(
                graph,
                self.analyze_source(graph, *span, bindings)?,
                &node.arguments,
            )?;
            if analysis.known_value.as_ref() != Some(scalar)
                || analysis.support != node.support
                || analysis.scalar_scope.as_ref() != Some(&node.scope)
            {
                return Err("let/if 値・支持・Scope が元式・実入力と違う".into());
            }
            self.tick()?;
            Ok(analysis)
        })
    }
    /// law の値は親 Evaluation より先に挿入する。既存の Scalar 引数を保ったまま、
    /// cutoff 未満の own Source と元子 Evaluation を構成の証人として照合する。
    fn scalar_source_analysis(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<SourceAnalysis, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let Rule::Input {
                kind: "law",
                location: Location::Law { span },
            } = &node.rule
            else {
                return Err("生成値に元 Law 出現がない".into());
            };
            let Some(Payload::Scalar(scalar)) = &node.payload else {
                return Err("元 Law の生成値が通常 Scalar でない".into());
            };
            let id = *self.expressions.get(span).ok_or("生成値の元 AST がない")?;
            let law = self.inputs.law();
            let operands = match law.exprs[id].kind {
                ExprKind::Int(_) | ExprKind::Bool(_) => vec![],
                ExprKind::Dotted(_) if data::expression(law, id, &self.control)?.is_some() => {
                    vec![]
                }
                ExprKind::Unary {
                    op: UnOp::Neg,
                    operand,
                } => vec![operand],
                ExprKind::Binary { op, lhs, rhs } if !is_boolean_binary(op) => vec![lhs, rhs],
                ExprKind::Tuple(_)
                | ExprKind::ListLit { .. }
                | ExprKind::SetLit { .. }
                | ExprKind::None(_)
                | ExprKind::Some(_)
                | ExprKind::Unit
                | ExprKind::Str(_)
                | ExprKind::Index { .. }
                | ExprKind::Call { .. } => {
                    self.composite_children(id)?.ok_or("元数値構成の子がない")?
                }
                _ => return Err("Scalar 引数から構成できる元式でない".into()),
            };
            let ty = scalar.ty();
            if law.expr_type(id) != Some(&ty)
                || node.ty != NodeType::Value(ty.clone())
                || node.arguments.len() != operands.len()
            {
                return Err("生成 Scalar の型・引数数が元 AST と違う".into());
            }
            for (&argument, &operand) in node.arguments.iter().zip(&operands) {
                self.tick()?;
                if argument.0 >= limit {
                    return Err("生成値の引数 Scalar が既出でない".into());
                }
                graph.expect(
                    argument,
                    &NodeType::Value(law.expr_type(operand).ok_or("元子の型がない")?.clone()),
                )?;
                graph.scalar(argument)?;
                self.tick()?;
            }
            for (source_index, source) in graph.nodes.iter().enumerate().take(limit) {
                self.tick()?;
                let Some(Payload::Expression {
                    location: Location::Law { span: actual },
                    bindings,
                    parameters,
                }) = &source.payload
                else {
                    self.tick()?;
                    continue;
                };
                if actual != span || graph.context_at(source_index) != self.current_context(graph) {
                    self.tick()?;
                    continue;
                }
                let candidate = (|| -> Result<SourceAnalysis, ValidationFailure> {
                    if source.ty != NodeType::Expression(ty.clone())
                        || !parameters.is_empty()
                        || !matches!(&source.rule, Rule::Input { kind: "law", location: Location::Law { span: actual } } if actual == span)
                    {
                        return Err("生成値の own Source の型・出所が違う".into());
                    }
                    let mut arguments = Vec::new();
                    for binding in bindings {
                        self.tick()?;
                        if binding.value.0 >= source_index {
                            return Err("own Source の束縛が既出でない".into());
                        }
                        arguments.push(binding.value);
                        self.tick()?;
                    }
                    if source.arguments != self.source_arguments(graph, *span, bindings)? {
                        return Err("own Source の引数と束縛が違う".into());
                    }
                    self.validate_at(graph, source, source_index)?;
                    let analysis = self.resolve_analysis(
                        graph,
                        self.analyze_source(graph, *span, bindings)?,
                        &node.arguments,
                    )?;
                    if analysis.known_value.as_ref() != Some(scalar)
                        || analysis.support != node.support
                        || analysis.scalar_scope.as_ref() != Some(&node.scope)
                    {
                        return Err("生成値・支持・ScalarScope が own Source の実入力と違う".into());
                    }
                    for (&argument, &operand) in node.arguments.iter().zip(&operands) {
                        self.tick()?;
                        if !self
                            .has_operand_evaluation(graph, limit, operand, bindings, argument)?
                        {
                            return Err("生成値の引数に元子 Evaluation がない".into());
                        }
                        self.tick()?;
                    }
                    Ok(analysis)
                })();
                match candidate {
                    Ok(analysis) => {
                        self.tick()?;
                        return Ok(analysis);
                    }
                    Err(ValidationFailure::Stop(reason)) => {
                        return Err(ValidationFailure::Stop(reason));
                    }
                    Err(ValidationFailure::Internal(_)) => {}
                    Err(failure @ ValidationFailure::UnsupportedExpression { .. }) => {
                        return Err(failure);
                    }
                }
                self.tick()?;
            }
            self.tick()?;
            Err("生成 Scalar に既出の own Source・元子評価の証人がない".into())
        })
    }
    /// 数値の差というだけでは残差でない。既出の実数値等号と同じ束縛・左右の
    /// child Evaluation を証人にし、親 Evaluation 未挿入の prefix でも帰属を閉じる。
    fn residual_source_analysis(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<SourceAnalysis, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let Some(Payload::Scalar(residual)) = &node.payload else {
                return Err("残差が通常 Scalar でない".into());
            };
            let ty = residual.ty();
            if !numeric::is_numeric_type(&ty, &self.control)? {
                return Err("残差が数値型でない".into());
            }
            if node.ty != NodeType::Value(ty.clone())
                || !matches!(&node.rule, Rule::Construction("evaluation"))
                || node.arguments.len() != 2
            {
                return Err("残差の型・構成規則・引数数が違う".into());
            }
            for &argument in &node.arguments {
                self.tick()?;
                if argument.0 >= limit {
                    return Err("残差の引数 Scalar が既出でない".into());
                }
                graph.expect(argument, &NodeType::Value(ty.clone()))?;
                numeric::check(graph.scalar(argument)?, &self.control)?;
                self.tick()?;
            }
            let left = graph.scalar(node.arguments[0])?;
            let right = graph.scalar(node.arguments[1])?;
            if numeric::binary(BinOp::Sub, left, right, &self.control)? != *residual {
                return Err("残差が元左右の正確な差でない".into());
            }
            for (source_index, source) in graph.nodes.iter().enumerate().take(limit) {
                self.tick()?;
                if graph.context_at(source_index) != self.current_context(graph) {
                    continue;
                }
                let Some(Payload::Expression {
                    location: Location::Law { span },
                    bindings,
                    parameters,
                }) = &source.payload
                else {
                    self.tick()?;
                    continue;
                };
                let Some(&id) = self.expressions.get(span) else {
                    self.tick()?;
                    continue;
                };
                let law = self.inputs.law();
                let ExprKind::Binary {
                    op: BinOp::Eq,
                    lhs,
                    rhs,
                } = law.exprs[id].kind
                else {
                    self.tick()?;
                    continue;
                };
                let candidate = (|| -> Result<SourceAnalysis, ValidationFailure> {
                    if law.expr_type(id) != Some(&Type::Bool)
                        || law.expr_type(lhs) != Some(&ty)
                        || law.expr_type(rhs) != Some(&ty)
                        || source.ty != NodeType::Expression(Type::Bool)
                        || !parameters.is_empty()
                        || !matches!(&source.rule, Rule::Input { kind: "law", location: Location::Law { span: actual } } if actual == span)
                    {
                        return Err("残差の 数値等号 Source の型・出所が違う".into());
                    }
                    let mut arguments = Vec::new();
                    for binding in bindings {
                        self.tick()?;
                        if binding.value.0 >= source_index {
                            return Err("数値等号 Source の束縛が既出でない".into());
                        }
                        arguments.push(binding.value);
                        self.tick()?;
                    }
                    if source.arguments != self.source_arguments(graph, *span, bindings)? {
                        return Err("数値等号 Source の引数と束縛が違う".into());
                    }
                    self.validate_at(graph, source, source_index)?;
                    let analysis = self.resolve_analysis(
                        graph,
                        self.analyze_source(graph, *span, bindings)?,
                        &node.arguments,
                    )?;
                    if analysis.known_value != Some(Scalar::Bool(left == right))
                        || analysis.support != node.support
                        || analysis.scope != node.scope
                        || analysis.scalar_scope.as_ref() != Some(&node.scope)
                    {
                        return Err("残差の支持・Scope・等号値が元 Source の実入力と違う".into());
                    }
                    for (operand, argument) in [lhs, rhs].into_iter().zip(&node.arguments) {
                        self.tick()?;
                        let expected =
                            self.analyze_source(graph, law.exprs[operand].span, bindings)?;
                        if expected.known_value.as_ref() != Some(graph.scalar(*argument)?)
                            || !self.has_operand_evaluation(
                                graph, limit, operand, bindings, *argument,
                            )?
                        {
                            return Err("残差の左右に同じ束縛・値 Ref の元子評価がない".into());
                        }
                        self.tick()?;
                    }
                    Ok(analysis)
                })();
                match candidate {
                    Ok(analysis) => {
                        self.tick()?;
                        return Ok(analysis);
                    }
                    Err(ValidationFailure::Stop(reason)) => {
                        return Err(ValidationFailure::Stop(reason));
                    }
                    Err(ValidationFailure::Internal(_)) => {}
                    Err(failure @ ValidationFailure::UnsupportedExpression { .. }) => {
                        return Err(failure);
                    }
                }
                self.tick()?;
            }
            self.tick()?;
            Err("残差に既出の 数値等号 Source・元左右評価の証人がない".into())
        })
    }
    fn has_operand_evaluation(
        &self,
        graph: &Graph,
        limit: usize,
        operand: usize,
        bindings: &[Binding],
        argument: NodeRef,
    ) -> Result<bool, ValidationFailure> {
        self.tick()?;
        let span = self.inputs.law().exprs[operand].span;
        let ty = self
            .inputs
            .law()
            .expr_type(operand)
            .ok_or("元子評価の型がない")?;
        for (index, node) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            let Some(Payload::Evaluation {
                expression,
                bindings: actual_bindings,
                value,
                ..
            }) = &node.payload
            else {
                self.tick()?;
                continue;
            };
            if graph.context_at(index) != self.current_context(graph)
                || node.ty != NodeType::Evaluation(ty.clone())
                || actual_bindings != bindings
                || *value != Some(argument)
                || expression.0 >= index
                || argument.0 >= index
                || !matches!(&graph.get(*expression)?.payload, Some(Payload::Expression { location: Location::Law { span: actual }, .. }) if *actual == span)
            {
                self.tick()?;
                continue;
            }
            // payload/引数の全ての辺を元子の挿入位置より前に確認してから再検査する。
            // Scalar -> 子 Evaluation -> 引数 Scalar の位置は厳密に減少する。
            match self.recheck_evaluation(graph, NodeRef(index)) {
                Ok(()) => {
                    self.tick()?;
                    return Ok(true);
                }
                Err(ValidationFailure::Stop(reason)) => {
                    return Err(ValidationFailure::Stop(reason));
                }
                Err(ValidationFailure::Internal(_)) => {}
                Err(failure @ ValidationFailure::UnsupportedExpression { .. }) => {
                    return Err(failure);
                }
            }
            self.tick()?;
        }
        self.tick()?;
        Ok(false)
    }
    /// Bool 論理値の arguments は元の子 Evaluation。欠測を通常 Scalar にしない。
    /// 元 AST・実入力から期待値/支持/Scope を独立に求め、既出の各子も再検査する。
    fn logic_source_analysis(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<SourceAnalysis, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let Rule::Input {
                kind: "law",
                location: Location::Law { span },
            } = &node.rule
            else {
                return Err("Bool 論理値が元 Law 式を持たない".into());
            };
            let id = *self
                .expressions
                .get(span)
                .ok_or("Bool 論理値の元 AST がない")?;
            let law = self.inputs.law();
            let operands = match law.exprs[id].kind {
                ExprKind::Unary {
                    op: UnOp::Not,
                    operand,
                } => vec![operand],
                ExprKind::Binary { op, lhs, rhs } if is_boolean_binary(op) => vec![lhs, rhs],
                _ => return Err("子 Evaluation から構成できる Bool 演算でない".into()),
            };
            if law.expr_type(id) != Some(&Type::Bool)
                || node.ty != NodeType::Value(Type::Bool)
                || node.arguments.len() != operands.len()
            {
                return Err("Bool 論理値の型・引数数が元演算と違う".into());
            }
            let mut bindings: Option<&[Binding]> = None;
            for (&reference, id) in node.arguments.iter().zip(operands) {
                self.tick()?;
                if reference.0 >= limit {
                    return Err("Bool 論理値の子 Evaluation が既出でない".into());
                }
                graph.expect(reference, &NodeType::Evaluation(Type::Bool))?;
                if graph.context_at(reference.0) != self.current_context(graph) {
                    return Err("Bool子が別frameに属する".into());
                }
                self.recheck_evaluation(graph, reference)?;
                let (expression, actual_bindings, _) = self.evaluation(graph, reference)?;
                self.source_matches(graph, expression, id)?;
                if bindings.is_some_and(|bindings| bindings != actual_bindings) {
                    return Err("Bool 論理値の左右で元束縛が違う".into());
                }
                bindings = Some(actual_bindings);
                self.tick()?;
            }
            let analysis = self.resolve_analysis(
                graph,
                self.analyze_source(graph, *span, bindings.ok_or("Bool 論理値に子束縛がない")?)?,
                &node.arguments,
            )?;
            let Some(Payload::Scalar(Scalar::Bool(value))) = &node.payload else {
                return Err("Bool 論理値が通常 Bool Scalar でない".into());
            };
            if analysis.known_value.as_ref() != Some(&Scalar::Bool(*value))
                || analysis.scalar_scope.as_ref() != Some(&node.scope)
                || analysis.support != node.support
            {
                return Err("Bool 論理値・支持・Scope が元 AST・実入力と違う".into());
            }
            self.tick()?;
            Ok(analysis)
        })
    }
    // Scalar の支持も自己申告の集合を信じず、原始 leaf または実引数から復元する。
    fn scalar_support(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<Vec<Fact>, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let Some(Payload::Scalar(value)) = &node.payload else {
                return Err("支持の依存先が通常値でない".into());
            };
            for reference in &node.arguments {
                self.tick()?;
                if reference.0 >= limit {
                    return Err("値支持の引数が既出でない".into());
                }
                self.tick()?;
            }
            let mut support = match &node.rule {
                Rule::Input {
                    kind: "subject",
                    location: Location::ArchMap { pointer, .. },
                } => {
                    let Scalar::Subject {
                        snapshot,
                        subject,
                        entity,
                    } = value
                    else {
                        return Err("subject支持の値型".into());
                    };
                    let actual = self.subject(snapshot, subject)?;
                    if actual.pointer != *pointer
                        || actual.ty != *entity
                        || !node.arguments.is_empty()
                    {
                        return Err("subject支持の元入力不一致".into());
                    }
                    self.subject_support(value)?
                }
                Rule::Input {
                    kind: "atom",
                    location: Location::ArchMap { pointer, .. },
                } => {
                    let fact = self
                        .atoms
                        .get(pointer)
                        .ok_or("Atom支持の元入力位置がない")?;
                    let field = self.field(
                        &fact.snapshot,
                        &fact.subject,
                        fact.field.as_ref().ok_or("Atom fieldがない")?,
                    )?;
                    let Slot::Known { value: actual, .. } = &field.slot else {
                        return Err("Atom支持が欠測slotを指す".into());
                    };
                    if scalar_from(actual, &field.ty, self.inputs.law(), &self.control)?.as_ref()
                        != Some(value)
                        || node.arguments.len() != 1
                    {
                        return Err("Atom支持の原始値・owner引数数が違う".into());
                    }
                    let Scalar::Subject {
                        snapshot, subject, ..
                    } = graph.scalar(node.arguments[0])?
                    else {
                        return Err("Atom支持のownerがRefでない".into());
                    };
                    if snapshot != &fact.snapshot || subject != &fact.subject {
                        return Err("Atom支持のowner identity不一致".into());
                    }
                    vec![fact.clone()]
                }
                Rule::Input {
                    kind: "law",
                    location: Location::Law { span },
                } => {
                    if let Some(&id) = self.expressions.get(span) {
                        match self.inputs.law().exprs[id].kind {
                            ExprKind::Quant { .. } => {
                                self.quant_scalar(graph, node, limit)?.support
                            }
                            ExprKind::SetComp { .. } => {
                                self.comprehension_source_analysis(graph, node, limit)?
                                    .support
                            }
                            ExprKind::Call { .. }
                                if self
                                    .named_view(
                                        *self.expressions.get(span).ok_or("call ASTがない")?,
                                    )?
                                    .is_some() =>
                            {
                                self.call_source_analysis(graph, node, limit)?.support
                            }
                            ExprKind::Let { .. } | ExprKind::If { .. } | ExprKind::Match { .. } => {
                                self.lexical_source_analysis(graph, node, limit)?.support
                            }
                            ExprKind::Binary { op, .. } if is_boolean_binary(op) => {
                                self.logic_source_analysis(graph, node, limit)?.support
                            }
                            ExprKind::Unary { op: UnOp::Not, .. } => {
                                self.logic_source_analysis(graph, node, limit)?.support
                            }
                            ExprKind::Dotted(_)
                                if data::expression(
                                    self.inputs.law(),
                                    *self.expressions.get(span).ok_or("constructor元式がない")?,
                                    &self.control,
                                )?
                                .is_none() =>
                            {
                                self.lexical_source_analysis(graph, node, limit)?.support
                            }
                            ExprKind::Dotted(_)
                            | ExprKind::Int(_)
                            | ExprKind::Bool(_)
                            | ExprKind::Binary { .. }
                            | ExprKind::Tuple(_)
                            | ExprKind::ListLit { .. }
                            | ExprKind::SetLit { .. }
                            | ExprKind::None(_)
                            | ExprKind::Some(_)
                            | ExprKind::Unit
                            | ExprKind::Str(_)
                            | ExprKind::Index { .. }
                            | ExprKind::Call { .. }
                            | ExprKind::Unary { .. } => {
                                self.scalar_source_analysis(graph, node, limit)?.support
                            }
                            _ => return Err("値支持の未実装元式".into()),
                        }
                    } else {
                        self.lexical_source_analysis(graph, node, limit)?.support
                    }
                }
                Rule::Construction("evaluation") if matches!(value, Scalar::Bool(_)) => {
                    if node.arguments.len() != 2 {
                        return Err("含意値支持の構成入力数が違う".into());
                    }
                    let instance = node.arguments[0];
                    if self
                        .conditional_value(graph, instance, node.arguments[1])?
                        .map(Scalar::Bool)
                        .as_ref()
                        != Some(value)
                    {
                        return Err("含意値支持の元 guard/body 不一致".into());
                    }
                    let (body, guard) = self.application_at(graph, instance)?;
                    self.application_context(graph, body, guard)?.0
                }
                Rule::Construction("evaluation") => {
                    self.residual_source_analysis(graph, node, limit)?.support
                }
                Rule::Construction("domain") => {
                    self.domain_member(graph, node, limit)?;
                    node.support.clone()
                }
                Rule::Construction("evidence") => {
                    self.quant_counter_parts(graph, node, limit)?;
                    vec![]
                }
                Rule::Construction("proposition") => vec![],
                _ => return Err("値支持の導出規則がない".into()),
            };
            support.sort();
            support.dedup();
            self.tick()?;
            Ok(support)
        })
    }
    /// 完成 Answer の必須検査。構造検査と、元 Request への意味上の帰属を一緒に確かめる。
    pub(crate) fn validate_answer(
        &self,
        graph: &Graph,
        request: &Request,
        answer: &Answer,
    ) -> Result<(), ValidationFailure> {
        self.validation_session(|| {
            self.tick()?;
            let evaluation = *answer
                .outputs
                .get("evaluation")
                .ok_or("完成Answerに元評価がない")?;
            graph.get(evaluation)?;
            let context = graph.context_at(evaluation.0);
            if context.frame.is_some() || context.iteration.is_some() || context.instance.is_some()
            {
                return Err("Answerの返却評価がcallee frameに属する".into());
            }
            if !graph.requests.is_empty()
                && graph.requests.iter().position(|actual| actual == request)
                    != Some(context.request)
            {
                return Err("Answer返却評価が現在の元Requestに属さない".into());
            }
            let previous = self.context.replace(Some(context));
            let old_cutoff = self.cutoff.replace(graph.nodes.len());
            let result = self
                .validate_answer_in_context(graph, request, answer)
                .map_err(|failure| match failure {
                    ValidationFailure::UnsupportedExpression { feature, .. } => {
                        ValidationFailure::Internal(format!(
                            "未対応元式の生成済みAnswerを照合できない: {feature}"
                        ))
                    }
                    other => other,
                });
            self.cutoff.set(old_cutoff);
            self.context.set(previous);
            result
        })
    }
    fn validate_answer_in_context(
        &self,
        graph: &Graph,
        request: &Request,
        answer: &Answer,
    ) -> Result<(), ValidationFailure> {
        graph.validate_answer(answer, request.kind == QuestionKind::Check)?;
        if answer.id != request.id {
            return Err("Answer ID が元Requestと違う".into());
        }
        let Selector::Declaration { name } = &request.head else {
            return Err("解決済みRequestのheadが宣言でない".into());
        };
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(name)
            .ok_or("Requestの元宣言がない")?;
        let (params, body) = match (&request.kind, &declaration.signature) {
            (QuestionKind::Evaluate, crate::law::model::Signature::View { params, body, .. }) => {
                (params, *body)
            }
            (QuestionKind::Check, crate::law::model::Signature::Law { params, body, .. }) => {
                (params, *body)
            }
            _ => return Err("Request種別と元宣言が違う".into()),
        };
        if self.validate_family_answer(graph, request, answer)? {
            return Ok(());
        }
        let evaluation = *answer
            .outputs
            .get("evaluation")
            .ok_or("完成Answerに元評価がない")?;
        let (expression, bindings, _) = self.evaluation(graph, evaluation)?;
        let source = if request.kind == QuestionKind::Check
            && let Some(&instance) = graph.get(evaluation)?.arguments.first()
            && graph.get(instance)?.ty == NodeType::LawInstance
        {
            let raw_body = self.instance_evaluation(graph, instance, evaluation)?;
            self.evaluation(graph, raw_body)?.0
        } else {
            expression
        };
        self.source_matches(graph, source, body)?;
        self.recheck_evaluation(graph, evaluation)?;
        if bindings.len() != params.len() || request.arguments.len() != params.len() {
            return Err("Requestの明示束縛数がAnswerと違う".into());
        }
        for (parameter, binding) in params.iter().zip(bindings) {
            self.tick()?;
            if parameter.name != binding.name || parameter.ty.erase() != binding.ty {
                return Err("Requestのparameter署名がAnswerと違う".into());
            }
            let key = format!("bind.{}", parameter.name);
            let mut selected = None;
            for argument in &request.arguments {
                self.tick()?;
                if argument.name == key {
                    if selected.is_some() {
                        return Err("Requestの束縛名が重複".into());
                    }
                    selected = Some(&argument.value);
                }
                self.tick()?;
            }
            let Some(Selector::Subject { snapshot, subject }) = selected else {
                return Err("完成Answerの元明示subject束縛がない".into());
            };
            let Scalar::Subject {
                snapshot: actual_snapshot,
                subject: actual_subject,
                entity,
            } = graph.scalar(binding.value)?
            else {
                return Err("Answer束縛が通常のRef値でない".into());
            };
            if actual_snapshot != snapshot
                || actual_subject != subject
                || &self.subject(snapshot, subject)?.ty != entity
            {
                return Err("Answer束縛がRequestのsubject identityと違う".into());
            }
            self.tick()?;
        }
        if request.kind == QuestionKind::Check {
            let claim = answer.claim.ok_or("完成check Answerにclaimがない")?;
            let Some(Payload::Proposition { instance }) = &graph.get(claim)?.payload else {
                return Err("Requestのclaimが命題でない".into());
            };
            let Some(Payload::LawInstance {
                name: actual,
                bindings: instance_bindings,
                ..
            }) = &graph.get(*instance)?.payload
            else {
                return Err("RequestのclaimにLawInstanceがない".into());
            };
            if actual != name || instance_bindings != bindings {
                return Err("check AnswerのLawInstanceがRequestと違う".into());
            }
            self.instance_evaluation(graph, *instance, evaluation)?;
            self.validate_at(graph, graph.get(claim)?, claim.0)?;
        }
        self.tick()?;
        Ok(())
    }
    /// この段階で構成する数値組・射影・固定 rat の typed 子だけを返す。
    /// builtin callee は値でないため架空の型・Evaluation を付けない。
    fn builtin(&self, id: usize) -> Result<Option<&str>, ValidationFailure> {
        let law = self.inputs.law();
        let ExprKind::Call { callee, .. } = law.exprs[id].kind else {
            return Ok(None);
        };
        if data::expression(law, id, &self.control)?.is_some() {
            return Ok(None);
        }
        let mut callee = callee;
        while let ExprKind::Group(inner) = law.exprs[callee].kind {
            self.tick()?;
            callee = inner;
        }
        match &law.exprs[callee].kind {
            ExprKind::Dotted(parts)
                if parts.len() == 1
                    && matches!(parts[0].name.as_str(), "rat" | "count" | "sum") =>
            {
                Ok(Some(parts[0].name.as_str()))
            }
            _ => Ok(None),
        }
    }
    pub(crate) fn composite_children(
        &self,
        id: usize,
    ) -> Result<Option<Vec<usize>>, ValidationFailure> {
        self.tick()?;
        let law = self.inputs.law();
        let Some(ty) = law.expr_type(id) else {
            return Ok(None);
        };
        if !data::supported(ty, law, &self.control)? {
            return Err(ValidationFailure::UnsupportedExpression {
                location: Location::Law {
                    span: law.exprs[id].span,
                },
                feature: "未対応payload・型または再帰Dataの構成".into(),
            });
        }
        if let Some((_, args)) = data::expression(law, id, &self.control)? {
            return Ok(Some(args));
        }
        let children = match &law.exprs[id].kind {
            ExprKind::Unit | ExprKind::Str(_) | ExprKind::None(_) => Some(vec![]),
            ExprKind::Tuple(items)
            | ExprKind::ListLit { items, .. }
            | ExprKind::SetLit { items, .. } => Some(items.clone()),
            ExprKind::Index { base, .. } | ExprKind::Some(base) => Some(vec![*base]),
            ExprKind::Call { args, .. } if self.builtin(id)?.is_some() => Some(args.clone()),
            _ => None,
        };
        self.tick()?;
        Ok(children)
    }
    pub(crate) fn composite_value(
        &self,
        id: usize,
        values: &[Scalar],
    ) -> Result<Scalar, ValidationFailure> {
        self.tick()?;
        let law = self.inputs.law();
        let children = self
            .composite_children(id)?
            .ok_or("数値構成の元式が未対応")?;
        if children.len() != values.len() {
            return Err("数値構成の引数数が元式と違う".into());
        }
        for (&child, value) in children.iter().zip(values) {
            self.tick()?;
            if law.expr_type(child) != Some(&value.ty()) {
                return Err("数値構成の引数型が元式と違う".into());
            }
            data::check(value, law, &self.control)?;
            self.tick()?;
        }
        let value = if let Some((constructor, _)) = data::expression(law, id, &self.control)? {
            let Type::Data(family) = law.expr_type(id).ok_or("Data構成型がない")? else {
                return Err("Data構成型が違う".into());
            };
            Scalar::Data {
                family: family.clone(),
                constructor,
                args: values.to_vec(),
            }
        } else {
            match &law.exprs[id].kind {
                ExprKind::Unit => Scalar::Unit,
                ExprKind::Str(text) => Scalar::Text(text.clone()),
                ExprKind::Tuple(_) => Scalar::Tuple(values.to_vec()),
                ExprKind::ListLit { .. } => {
                    let Type::List(element) = law.expr_type(id).ok_or("List型がない")? else {
                        return Err("List構成型が違う".into());
                    };
                    Scalar::List {
                        element: (**element).clone(),
                        items: values.to_vec(),
                    }
                }
                ExprKind::SetLit { .. } => {
                    let Type::Set(element) = law.expr_type(id).ok_or("Set型がない")? else {
                        return Err("Set構成型が違う".into());
                    };
                    data::set((**element).clone(), values, &self.control)?
                }
                ExprKind::None(_) | ExprKind::Some(_) => {
                    let Type::Option(element) = law.expr_type(id).ok_or("Option型がない")?
                    else {
                        return Err("Option構成型が違う".into());
                    };
                    Scalar::Option {
                        element: (**element).clone(),
                        value: values.first().cloned().map(Box::new),
                    }
                }
                ExprKind::Index { index, .. } => {
                    let Scalar::Tuple(items) = &values[0] else {
                        return Err("数値射影元が Tuple でない".into());
                    };
                    items.get(*index).ok_or("数値射影位置の内部不整合")?.clone()
                }
                ExprKind::Call { .. } => match self.builtin(id)?.ok_or("固定演算がない")? {
                    "rat" => {
                        if values.len() != 2 {
                            return Err("rat arityが違う".into());
                        };
                        numeric::rational(&values[0], &values[1], &self.control)?
                    }
                    name => data::aggregate(
                        name,
                        values.first().ok_or("count/sum引数がない")?,
                        &self.control,
                    )?,
                },
                _ => return Err("元数値構成がない".into()),
            }
        };
        if law.expr_type(id) != Some(&value.ty()) {
            return Err("数値構成の結果型が元式と違う".into());
        }
        data::check(&value, law, &self.control)?;
        self.tick()?;
        Ok(value)
    }
    // 自己申告の node.scope へ依存せず、元宣言・束縛と原始 slot から再構成する。
    fn source_scope(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<Scope, ValidationFailure> {
        self.analyze_source(graph, span, bindings)
            .map(|analysis| analysis.scope)
    }
    // 元byteの綴りだけでなく、採用・型検査済みDottedの実先頭出現へ戻る。
    // 単独名は全体のSource、field読みの先頭名だけがfragmentとして使える。
    fn name_token(&self, span: (usize, usize)) -> Result<&str, ValidationFailure> {
        self.find_name_token(span)?
            .ok_or_else(|| "fragment が元Dottedの先頭tokenでない".into())
    }
    // 非一致だけをNoneとし、停止と元出現の不整合は任意照合でも伝播する。
    fn find_name_token(&self, span: (usize, usize)) -> Result<Option<&str>, ValidationFailure> {
        let mut name = None;
        let law = self.inputs.law();
        for (id, expression) in law.exprs.iter().enumerate() {
            #[cfg(test)]
            if let Some(context) = self.optional_name_context.get()
                && let Some(observer) = self.name_token_observer.borrow_mut().as_mut()
            {
                observer(span, context);
            }
            self.tick()?;
            if law.expr_type(id).is_some()
                && self.expressions.get(&expression.span) == Some(&id)
                && let ExprKind::Dotted(parts) = &expression.kind
                && let Some(first) = parts.first()
                && first.span == span
            {
                if name.is_some_and(|actual| actual != first.name.as_str()) {
                    return Err("名前tokenの元出現が一意でない".into());
                }
                name = Some(first.name.as_str());
            }
            self.tick()?;
        }
        Ok(name)
    }
    fn enclosing_matches(
        &self,
        span: (usize, usize),
    ) -> Result<Vec<(usize, usize)>, ValidationFailure> {
        let law = self.inputs.law();
        let mut result = Vec::new();
        for (id, expr) in law.exprs.iter().enumerate() {
            self.tick()?;
            if law.expr_type(id).is_none() || self.expressions.get(&expr.span) != Some(&id) {
                continue;
            }
            if let ExprKind::Match { arms, .. } = &expr.kind {
                for (arm, branch) in arms.iter().enumerate() {
                    self.tick()?;
                    let body = law.exprs[branch.body].span;
                    if body.0 <= span.0 && span.1 <= body.1 {
                        result.push((id, arm));
                    }
                }
            }
        }
        result.sort_by_key(|(id, _)| law.exprs[*id].span.0);
        Ok(result)
    }
    pub(crate) fn pattern_binding(
        &self,
        span: (usize, usize),
        name: &str,
    ) -> Result<Option<(usize, usize, data::Binder)>, ValidationFailure> {
        if self.name_token(span)? != name {
            return Err("pattern binderの実使用tokenが違う".into());
        }
        let mut found = None;
        for (actual, origin) in self.lexical_context(span)? {
            self.tick()?;
            if actual == name
                && let LexicalOrigin::Pattern {
                    matching,
                    arm,
                    binder,
                } = origin
            {
                if found.is_some() {
                    return Err("pattern binderが重複する".into());
                }
                found = Some((matching, arm, binder));
            }
        }
        Ok(found)
    }
    // lexical RHS/scrutinee は元 AST の位置で生成所属を決める。内包の外で
    // 完成した値を反復内へ移さず、当該式を含まない反復だけを親へ戻す。
    // call frame は越えず、同値ノードや任意祖先を代用することもない。
    fn lexical_evaluation_context(
        &self,
        graph: &Graph,
        id: usize,
    ) -> Result<super::call::Context, ValidationFailure> {
        let span = self.inputs.law().exprs[id].span;
        let mut context = self.current_context(graph);
        while let Some(index) = context.iteration {
            self.tick()?;
            let record = graph.iterations.get(index).ok_or("lexical反復元がない")?;
            if record.caller.instance != context.instance
                || record.caller.request != context.request
                || record.caller.frame != context.frame
                || record
                    .caller
                    .iteration
                    .is_some_and(|parent| parent >= index)
            {
                return Err("lexical反復の親Request/frame/先行性が違う".into());
            }
            self.iteration_input(graph, index)?;
            let comp = *self
                .expressions
                .get(&self.expression_span(graph, record.source)?)
                .ok_or("lexical反復の元ASTがない")?;
            let (_, bodies) = self.iteration_syntax(comp)?;
            if bodies.into_iter().any(|child| {
                let body = self.inputs.law().exprs[child].span;
                body.0 <= span.0 && span.1 <= body.1
            }) {
                return Ok(context);
            }
            context = record.caller;
        }
        Ok(context)
    }
    fn actual_evaluation(
        &self,
        graph: &Graph,
        id: usize,
        bindings: &[Binding],
    ) -> Result<NodeRef, ValidationFailure> {
        let context = self.lexical_evaluation_context(graph, id)?;
        let mut found = None;
        for (index, node) in graph
            .nodes
            .iter()
            .enumerate()
            .take(self.cutoff.get().min(graph.nodes.len()))
        {
            self.tick()?;
            if graph.context_at(index) != context {
                continue;
            }
            let Some(Payload::Evaluation {
                expression,
                bindings: actual,
                ..
            }) = &node.payload
            else {
                continue;
            };
            // Law適用/族集約は、元bodyを実評価したproducerではない。
            // true guardのwrapperもNAの未評価bodyも、このAST候補へ混ぜない。
            if let Some(&instance) = node.arguments.first()
                && graph.get(instance)?.ty == NodeType::LawInstance
            {
                continue;
            }
            let Some(Payload::Expression {
                location: Location::Law { span: actual_span },
                ..
            }) = &graph.get(*expression)?.payload
            else {
                // native Transformは元AST spanを持たない。結果の照合は適用側で行う。
                continue;
            };
            if actual == bindings && *actual_span == self.inputs.law().exprs[id].span {
                if found.is_some() {
                    return Err("同じ元式・Contextの実評価が一意でない".into());
                }
                found = Some(NodeRef(index));
            }
        }
        let reference = found.ok_or("元scrutineeの既出実Evaluationがない")?;
        self.recheck_evaluation(graph, reference)?;
        Ok(reference)
    }
    fn lexical_argument(
        &self,
        graph: &Graph,
        span: (usize, usize),
        name: &str,
        bindings: &[Binding],
    ) -> Result<Option<NodeRef>, ValidationFailure> {
        self.lexical_rhs(span, name)?
            .map(|rhs| self.actual_evaluation(graph, rhs, bindings))
            .transpose()
    }
    pub(crate) fn pattern_argument(
        &self,
        graph: &Graph,
        span: (usize, usize),
        name: &str,
        bindings: &[Binding],
    ) -> Result<Option<(NodeRef, Scalar)>, ValidationFailure> {
        let Some((matching, arm, binder)) = self.pattern_binding(span, name)? else {
            return Ok(None);
        };
        let ExprKind::Match { scrutinee, .. } = self.inputs.law().exprs[matching].kind else {
            unreachable!()
        };
        let input = self.actual_evaluation(graph, scrutinee, bindings)?;
        let value = self
            .evaluation(graph, input)?
            .2
            .ok_or("未知scrutineeにpattern binderがある")?;
        if data::select(
            self.inputs.law(),
            matching,
            Some(graph.scalar(value)?),
            &self.control,
        )? != Some(arm)
        {
            return Err("binderが選択されないarmに属する".into());
        }
        let value = data::project(graph.scalar(value)?, &binder.path, &self.control)?;
        if value.ty() != binder.ty {
            return Err("binder元型がpathと違う".into());
        }
        Ok(Some((input, value)))
    }
    // lexical scope は元 binder の body 範囲から復元する。右辺自身や同名の別出現を
    // 束縛としない。静的検査済みの shadowing 禁止により、外→内の順は一意になる。
    fn lexical_context(
        &self,
        span: (usize, usize),
    ) -> Result<Vec<(String, LexicalOrigin)>, ValidationFailure> {
        let mut enclosing = Vec::new();
        let law = self.inputs.law();
        for (id, expression) in law.exprs.iter().enumerate() {
            self.tick()?;
            if let ExprKind::Quant {
                var,
                split: crate::law::ast::QuantSplit::Fixed { domain: _, body },
                ..
            } = &expression.kind
                && law.expr_type(id).is_some()
                && self.expressions.get(&expression.span) == Some(&id)
                && law.exprs[*body].span.0 <= span.0
                && span.1 <= law.exprs[*body].span.1
            {
                enclosing.push((
                    expression.span.0,
                    var.name.clone(),
                    LexicalOrigin::Iteration(id),
                ));
            }
            if let ExprKind::SetComp {
                elem, var, filter, ..
            } = &expression.kind
                && law.expr_type(id).is_some()
                && self.expressions.get(&expression.span) == Some(&id)
                && std::iter::once(*elem).chain(*filter).any(|child| {
                    let body = law.exprs[child].span;
                    body.0 <= span.0 && span.1 <= body.1
                })
            {
                enclosing.push((
                    expression.span.0,
                    var.name.clone(),
                    LexicalOrigin::Iteration(id),
                ));
            }
            if let ExprKind::Let { name, value, body } = &expression.kind {
                let body_span = law.exprs[*body].span;
                let rhs_span = law.exprs[*value].span;
                // arena には構文解析の未採用候補もある。型検査した実出現だけを
                // lexical binder とし、Source が使う span 索引との同一性も確かめる。
                if law.expr_type(id).is_some()
                    && law.expr_type(*value).is_some()
                    && law.expr_type(*body).is_some()
                    && self.expressions.get(&expression.span) == Some(&id)
                    && self.expressions.get(&body_span) == Some(body)
                    && self.expressions.get(&rhs_span) == Some(value)
                    && body_span.0 <= span.0
                    && span.1 <= body_span.1
                {
                    enclosing.push((
                        expression.span.0,
                        name.name.clone(),
                        LexicalOrigin::Let(*value),
                    ));
                }
            }
            self.tick()?;
        }
        for (matching, arm) in self.enclosing_matches(span)? {
            let ExprKind::Match { scrutinee, arms } = &law.exprs[matching].kind else {
                unreachable!()
            };
            for binder in data::binders(
                &arms[arm].pattern,
                law.expr_type(*scrutinee).ok_or("pattern元型がない")?,
                law,
                &self.control,
            )? {
                enclosing.push((
                    law.exprs[matching].span.0,
                    binder.name.clone(),
                    LexicalOrigin::Pattern {
                        matching,
                        arm,
                        binder,
                    },
                ));
            }
        }
        enclosing.sort_by_key(|(start, _, _)| *start);
        self.tick()?;
        let mut result = Vec::new();
        for (_, name, rhs) in enclosing {
            self.tick()?;
            result.push((name, rhs));
            self.tick()?;
        }
        Ok(result)
    }
    pub(crate) fn lexical_rhs(
        &self,
        span: (usize, usize),
        name: &str,
    ) -> Result<Option<usize>, ValidationFailure> {
        if self.name_token(span)? != name {
            return Err("lexical 名の元使用tokenが違う".into());
        }
        let mut result = None;
        for (actual, rhs) in self.lexical_context(span)? {
            self.tick()?;
            if actual == name
                && let LexicalOrigin::Let(rhs) = rhs
            {
                if result.is_some() {
                    return Err("lexical binder が一意でない".into());
                }
                result = Some(rhs);
            }
            self.tick()?;
        }
        Ok(result)
    }
    fn projects_lexical_binding(
        &self,
        span: (usize, usize),
        name: &str,
    ) -> Result<bool, ValidationFailure> {
        for (actual, origin) in self.lexical_context(span)? {
            self.tick()?;
            if actual == name {
                return Ok(matches!(
                    origin,
                    LexicalOrigin::Iteration(_) | LexicalOrigin::Pattern { .. }
                ));
            }
        }
        Ok(false)
    }
    fn reused_source_value(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<Option<NodeRef>, ValidationFailure> {
        if let Some(id) = self.expressions.get(&span)
            && let ExprKind::Group(child) = self.inputs.law().exprs[*id].kind
        {
            let input = self.actual_evaluation(graph, child, bindings)?;
            return Ok(self.evaluation(graph, input)?.2);
        }
        let Some(name) = self.find_name_token(span)? else {
            return Ok(None);
        };
        if self.projects_lexical_binding(span, name)? {
            return Ok(None);
        }
        if let Some(argument) = self.call_parameter(graph, name)? {
            self.recheck_evaluation(graph, argument)?;
            return Ok(self.evaluation(graph, argument)?.2);
        }
        if let Some(binding) = bindings.iter().find(|binding| binding.name == name) {
            return Ok(Some(binding.value));
        }
        if let Some(input) = self.lexical_argument(graph, span, name, bindings)? {
            return Ok(self.evaluation(graph, input)?.2);
        }
        Ok(None)
    }
    // calleeのfield Scalarも、slot値の一致だけで別producerへ移せない。
    fn call_field_source(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let Some(Payload::Scalar(value)) = &node.payload else {
            return Err("field値がScalarでない".into());
        };
        if node.arguments.len() != 1 {
            return Err("field owner数が違う".into());
        }
        for (source_index, source) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if graph.context_at(source_index) != self.current_context(graph) {
                continue;
            }
            let Some(Payload::Expression {
                location: Location::Law { span },
                bindings,
                ..
            }) = &source.payload
            else {
                continue;
            };
            let Some(&id) = self.expressions.get(span) else {
                continue;
            };
            let (owner_span, field_name) = match &self.inputs.law().exprs[id].kind {
                ExprKind::Dotted(parts) if parts.len() > 1 => (
                    (parts[0].span.0, parts[parts.len() - 2].span.1),
                    parts.last().ok_or("元field名がない")?.name.as_str(),
                ),
                ExprKind::Field { base, name } => {
                    (self.inputs.law().exprs[*base].span, name.name.as_str())
                }
                _ => continue,
            };
            let analysis = self.resolve_analysis(
                graph,
                self.analyze_source(graph, *span, bindings)?,
                &node.arguments,
            )?;
            if analysis.known_value.as_ref() != Some(value)
                || analysis.scalar_scope.as_ref() != Some(&node.scope)
            {
                continue;
            }
            for (index, candidate) in graph.nodes.iter().enumerate().take(limit) {
                self.tick()?;
                if graph.context_at(index) != self.current_context(graph) {
                    continue;
                }
                let Some(Payload::Evaluation {
                    expression,
                    value: actual,
                    ..
                }) = &candidate.payload
                else {
                    continue;
                };
                if *actual != Some(node.arguments[0])
                    || self.expression_span(graph, *expression)? != owner_span
                {
                    continue;
                }
                self.validate_at(graph, source, source_index)?;
                self.recheck_evaluation(graph, NodeRef(index))?;
                // 候補の元owner出現と実Evaluationを確定してから、そのfieldを引く。
                // 他entityの候補field名を現在ownerへ付けて検索しない。
                let Scalar::Subject {
                    snapshot,
                    subject,
                    entity,
                } = graph.scalar(node.arguments[0])?
                else {
                    return Err("callee fieldの実ownerがRefでない".into());
                };
                let field = self.field(snapshot, subject, &format!("{entity}.{field_name}"))?;
                let Slot::Known { pointer, atom, .. } = &field.slot else {
                    continue;
                };
                let expected = Fact {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    field: Some(field.name.clone()),
                    atom: Some(atom.clone()),
                };
                if !matches!(&node.rule, Rule::Input {kind: "atom", location: Location::ArchMap {pointer: actual, ..}} if actual == pointer)
                    || node.support != [expected]
                {
                    continue;
                }

                return Ok(());
            }
        }
        Err("callee field Scalarに同frameの元field・実owner評価がない".into())
    }
    fn call_parts(
        &self,
        graph: &Graph,
        span: (usize, usize),
        children: &[NodeRef],
        limit: usize,
    ) -> Result<(NodeRef, SourceAnalysis, Option<NodeRef>), ValidationFailure> {
        let id = *self.expressions.get(&span).ok_or("call元ASTがない")?;
        let declaration = self.named_view(id)?.ok_or("call静的targetがない")?;
        let crate::law::model::Signature::View { body, params, .. } = &declaration.signature else {
            unreachable!()
        };
        if children.len() != params.len() + 1 {
            return Err("call子Evaluation数が元署名と違う".into());
        }
        for child in children {
            if child.0 >= limit {
                return Err("call子Evaluationが既出でない".into());
            }
        }
        let body_ref = *children.last().ok_or("call bodyがない")?;
        let context = graph.context_at(body_ref.0);
        let frame = graph
            .frames
            .get(context.frame.ok_or("callee bodyのframeがない")?)
            .ok_or("callee frameがない")?;
        if frame.caller != self.current_context(graph)
            || frame.arguments != children[..params.len()]
            || self.expression_span(graph, frame.source)? != span
            || frame.source.0 >= limit
        {
            return Err("call子と元call frameが違う".into());
        }
        self.frame_arguments(graph, context.frame.unwrap())?;
        self.recheck_evaluation(graph, body_ref)?;
        let (body_source, _, value) = self.evaluation(graph, body_ref)?;
        self.source_matches(graph, body_source, *body)?;
        if graph.context_at(body_source.0) != context {
            return Err("callee body Sourceのframeが違う".into());
        }
        let bindings = self.expression_bindings(graph, frame.source)?;
        let analysis =
            self.resolve_analysis(graph, self.analyze_source(graph, span, bindings)?, children)?;
        if value.map(|r| graph.scalar(r)).transpose()? != analysis.known_value.as_ref() {
            return Err("call body値が元入力展開と違う".into());
        }
        Ok((frame.source, analysis, value))
    }
    fn call_source_analysis(
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
            return Err("call Scalar元規則が違う".into());
        };
        let (_, analysis, _) = self.call_parts(graph, *span, &node.arguments, limit)?;
        if !matches!(&node.payload, Some(Payload::Scalar(value)) if analysis.known_value.as_ref() == Some(value))
            || node.support != analysis.support
            || analysis.scalar_scope.as_ref() != Some(&node.scope)
        {
            return Err("call Scalarが元call値・支持・Scopeと違う".into());
        }
        Ok(analysis)
    }
    fn validate_call_evaluation(
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
        let span = self.expression_span(graph, *expression)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(false);
        };
        if self.named_view(id)?.is_none() {
            return Ok(false);
        }
        if node.ty
            != NodeType::Evaluation(
                self.inputs
                    .law()
                    .expr_type(id)
                    .ok_or("内包元型がない")?
                    .clone(),
            )
            || parts.len() != 1
            || parts[0].location != (Location::Law { span })
            || parts[0].residual.is_some()
            || parts[0].value != *value
            || *applicability != "applicable"
            || bindings != self.expression_bindings(graph, *expression)?
            || graph.context_at(expression.0) != self.current_context(graph)
        {
            return Err("call Evaluationの元Source・partが違う".into());
        }
        let (source, analysis, body_value) =
            self.call_parts(graph, span, &parts[0].children, limit)?;
        if source != *expression
            || node.support != analysis.support
            || node.scope != analysis.scope
            || !graph.get(source)?.scope.source_compatible(&analysis.scope)
        {
            return Err("call Evaluationの元出現・支持・Scopeが違う".into());
        }
        match (*value, body_value) {
            (Some(result), Some(body)) if graph.scalar(result)? == graph.scalar(body)? => {
                if result.0 >= limit || graph.context_at(result.0) != self.current_context(graph) {
                    return Err("call値のframeが違う".into());
                }
                self.validate_at(graph, graph.get(result)?, result.0)?;
                if graph.get(result)?.arguments != parts[0].children {
                    return Err("call値の元子Evaluationが違う".into());
                }
            }
            (None, None) => {}
            _ => return Err("call値がcallee bodyの既知性と違う".into()),
        }
        let expected: Vec<_> = std::iter::once(*expression)
            .chain(parts[0].children.iter().copied())
            .chain(*value)
            .collect();
        if node.arguments != expected {
            return Err("call Evaluationの導出辺が違う".into());
        }
        Ok(true)
    }
    /// 名前tokenを解釈し直さず、静的検査で確定した参照出現を読む。
    pub(crate) fn named_view(
        &self,
        id: usize,
    ) -> Result<Option<&'a crate::law::model::Declaration>, ValidationFailure> {
        let law = self.inputs.law();
        let ExprKind::Call { callee, .. } = &law.exprs[id].kind else {
            return Ok(None);
        };
        let mut callee = *callee;
        while let ExprKind::Group(inner) = &law.exprs[callee].kind {
            self.tick()?;
            callee = *inner;
        }
        let span = law.exprs[callee].span;
        let mut found = None;
        for info in &law.infos {
            self.tick()?;
            for (at, target) in &info.references {
                self.tick()?;
                if *at == span
                    && let Some(d) = law.declarations.get(target)
                    && matches!(d.signature, crate::law::model::Signature::View { .. })
                {
                    if found.is_some() {
                        return Err("calleeの静的解決先が重複する".into());
                    }
                    found = Some(d);
                }
            }
        }
        let Some(declaration) = found else {
            return Ok(None);
        };
        let crate::law::model::Signature::View {
            params, returns, ..
        } = &declaration.signature
        else {
            unreachable!()
        };
        // 式型へeraseする前の宣言型を読む。所属条件を確認するcall評価は未提供。
        let mut pending = vec![returns];
        for parameter in params {
            self.tick()?;
            pending.push(&parameter.ty);
            self.tick()?;
        }
        while let Some(ty) = pending.pop() {
            self.tick()?;
            match ty {
                Type::Owned(_, _) => {
                    self.tick()?;
                    return Err(ValidationFailure::UnsupportedExpression {
                        location: Location::Law {
                            span: law.exprs[id].span,
                        },
                        feature: "依存 owner 制約を持つ view parameter・戻り型の呼出し評価".into(),
                    });
                }
                Type::Tuple(items) => {
                    for item in items {
                        self.tick()?;
                        pending.push(item);
                        self.tick()?;
                    }
                }
                Type::List(item) | Type::Set(item) | Type::Option(item) => pending.push(item),
                Type::Map(from, to) => {
                    pending.push(from);
                    pending.push(to);
                }
                Type::Term(params, returns) => {
                    pending.push(returns);
                    for parameter in params {
                        self.tick()?;
                        pending.push(parameter);
                        self.tick()?;
                    }
                }
                _ => {}
            }
            self.tick()?;
        }
        Ok(Some(declaration))
    }
    fn frame_arguments(
        &self,
        graph: &Graph,
        index: usize,
    ) -> Result<FrameInputs, ValidationFailure> {
        self.tick()?;
        let cache_key = (index, self.cutoff.get().min(graph.nodes.len()));
        if let Some(value) = self.cache.borrow().frames.get(&cache_key).cloned() {
            return Ok(value);
        }
        let frame = graph.frames.get(index).ok_or("call frameがない")?;
        if frame.caller.frame.is_some_and(|parent| parent >= index) {
            return Err("call frameの親が先行しない".into());
        }
        if graph.context_at(frame.source.0) != frame.caller {
            return Err("call Sourceがcaller frameと違う".into());
        }
        let span = self.expression_span(graph, frame.source)?;
        let id = *self
            .expressions
            .get(&span)
            .ok_or("call frameの元ASTがない")?;
        let d = self.named_view(id)?.ok_or("call frameがnamed viewでない")?;
        let crate::law::model::Signature::View { params, .. } = &d.signature else {
            unreachable!()
        };
        let ExprKind::Call { args, .. } = &self.inputs.law().exprs[id].kind else {
            unreachable!()
        };
        if args.len() != frame.arguments.len() || params.len() != args.len() {
            return Err("call引数数が元署名と違う".into());
        }
        let previous = self.context.replace(Some(frame.caller));
        let result = (|| {
            self.validate_at(graph, graph.get(frame.source)?, frame.source.0)?;
            let mut bindings = Vec::new();
            let mut variables = BTreeMap::new();
            let mut base = graph.get(frame.source)?.scope.clone();
            base.readings.insert(d.reading.clone());
            for ((parameter, &arg), &reference) in params.iter().zip(args).zip(&frame.arguments) {
                self.tick()?;
                if reference.0 <= frame.source.0 || graph.context_at(reference.0) != frame.caller {
                    return Err("call実引数が元callerの既出評価でない".into());
                }
                self.recheck_evaluation(graph, reference)?;
                let (expression, actual, value) = self.evaluation(graph, reference)?;
                self.source_matches(graph, expression, arg)?;
                if graph.context_at(expression.0) != frame.caller {
                    return Err("実引数Sourceのframeが違う".into());
                }
                let mut analysis =
                    self.analyze_source(graph, self.inputs.law().exprs[arg].span, actual)?;
                analysis
                    .scope
                    .merge_quantifiers(&graph.get(reference)?.scope);
                if let Some(scope) = &mut analysis.scalar_scope
                    && let Some(value) = value
                {
                    scope.merge_quantifiers(&graph.get(value)?.scope);
                }
                if value.map(|r| graph.scalar(r)).transpose()? != analysis.known_value.as_ref() {
                    return Err("call実引数が元入力の値と違う".into());
                }
                if let Some(value) = value {
                    bindings.push(Binding {
                        name: parameter.name.clone(),
                        ty: parameter.ty.erase(),
                        value,
                    });
                }
                variables.insert(
                    parameter.name.clone(),
                    SourceValue {
                        scope: analysis.scope,
                        known_value: analysis.known_value,
                        support: analysis.support,
                        scalar_scope: analysis.scalar_scope,
                    },
                );
            }
            for variable in variables.values_mut() {
                variable.scope.merge(&base);
            }
            Ok((bindings, variables, base))
        })();
        self.context.set(previous);
        if let Ok(value) = &result {
            self.cache
                .borrow_mut()
                .frames
                .insert(cache_key, value.clone());
        }
        result
    }
    fn comprehension_parts(
        &self,
        graph: &Graph,
        span: (usize, usize),
        children: &[NodeRef],
        limit: usize,
    ) -> Result<(NodeRef, SourceAnalysis), ValidationFailure> {
        let id = *self.expressions.get(&span).ok_or("内包元ASTがない")?;
        let ExprKind::SetComp {
            elem,
            domain,
            filter,
            ..
        } = self.inputs.law().exprs[id].kind
        else {
            return Err("内包元式が違う".into());
        };
        let input = *children.first().ok_or("内包domain子がない")?;
        if children.iter().any(|child| child.0 >= limit)
            || graph.context_at(input.0) != self.current_context(graph)
        {
            return Err("内包子の既出性/親Contextが違う".into());
        }
        self.recheck_evaluation(graph, input)?;
        let (domain_source, bindings, value) = self.evaluation(graph, input)?;
        self.source_matches(graph, domain_source, domain)?;
        let mut own = None;
        for (index, node) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            if graph.context_at(index) == self.current_context(graph)
                && matches!(&node.payload,Some(Payload::Expression {location:Location::Law {span:actual},bindings:actual_bindings,..}) if *actual==span && actual_bindings==bindings)
            {
                self.validate_at(graph, node, index)?;
                own = Some(NodeRef(index));
                break;
            }
        }
        let own = own.ok_or("内包値の既出own Sourceがない")?;
        let analysis =
            self.resolve_analysis(graph, self.analyze_source(graph, span, bindings)?, children)?;
        let items = match value.map(|r| graph.scalar(r)).transpose()? {
            Some(Scalar::List { items, .. }) => Some((items, true)),
            Some(Scalar::Set { items, .. }) => Some((items, false)),
            None => None,
            _ => return Err("実内包域がList/Setでない".into()),
        };
        let mut cursor = 1;
        let mut seen = Vec::new();
        let mut used_support = graph.get(input)?.support.clone();
        let mut scope = graph.get(input)?.scope.clone();
        let mut collected = Vec::new();
        let mut known = items.is_some();
        if let Some((items, is_list)) = items {
            for position in 0..items.len() {
                self.tick()?;
                let first = *children.get(cursor).ok_or("内包に反復漏れがある")?;
                let context = graph.context_at(first.0);
                let index = context.iteration.ok_or("内包子に反復Contextがない")?;
                let record = graph.iterations.get(index).ok_or("内包反復元がない")?;
                if record.caller != self.current_context(graph)
                    || record.source != own
                    || record.domain != input
                    || context.frame != record.caller.frame
                    || context.instance != record.caller.instance
                    || context.request != record.caller.request
                {
                    return Err("内包子の元Source/domain/親Contextが違う".into());
                }
                let (_, member, _) = self.iteration_input(graph, index)?;
                match (&record.member, is_list) {
                    (super::call::Member::ListPosition(actual), true) if *actual == position => {}
                    (super::call::Member::SetElement(_), false)
                        if !data::contains(&seen, &member, &self.control)? => {}
                    _ => return Err("内包走査のList位置/Set要素が重複または不一致".into()),
                }
                seen.push(member);
                let mut consume = |expected: usize| -> Result<Option<NodeRef>, ValidationFailure> {
                    let reference = *children.get(cursor).ok_or("内包の必要子がない")?;
                    cursor += 1;
                    if graph.context_at(reference.0) != context {
                        return Err("内包子が別反復に属する".into());
                    }
                    self.recheck_evaluation(graph, reference)?;
                    let (source, actual, value) = self.evaluation(graph, reference)?;
                    self.source_matches(graph, source, expected)?;
                    if actual != bindings {
                        return Err("内包子の宣言束縛が違う".into());
                    }
                    used_support.extend(graph.get(reference)?.support.iter().cloned());
                    scope.merge(&graph.get(reference)?.scope);
                    Ok(value)
                };
                let condition = if let Some(filter) = filter {
                    match consume(filter)?.map(|r| graph.scalar(r)).transpose()? {
                        Some(Scalar::Bool(value)) => Some(*value),
                        None => None,
                        _ => return Err("内包filter実値がBoolでない".into()),
                    }
                } else {
                    Some(true)
                };
                match condition {
                    Some(true) => {
                        if let Some(value) = consume(elem)? {
                            collected.push(graph.scalar(value)?.clone());
                        } else {
                            known = false;
                        }
                    }
                    Some(false) => {}
                    None => known = false,
                }
            }
        }
        if cursor != children.len() {
            return Err("内包に余分な反復/除外elemがある".into());
        }
        used_support.sort();
        used_support.dedup();
        let Type::Set(element) = self.inputs.law().expr_type(id).ok_or("内包型がない")?
        else {
            return Err("内包型がSetでない".into());
        };
        let computed = if known {
            Some(data::set((**element).clone(), &collected, &self.control)?)
        } else {
            None
        };
        if computed != analysis.known_value
            || scope != analysis.scope
            || used_support != analysis.support
        {
            return Err("内包の元domain/filter/採用値・支持・範囲が違う".into());
        }
        Ok((own, analysis))
    }
    fn comprehension_source_analysis(
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
            return Err("内包Scalarの元規則がない".into());
        };
        let (_, analysis) = self.comprehension_parts(graph, *span, &node.arguments, limit)?;
        if !matches!(&node.payload,Some(Payload::Scalar(value)) if analysis.known_value.as_ref()==Some(value))
            || node.support != analysis.support
            || analysis.scalar_scope.as_ref() != Some(&node.scope)
        {
            return Err("内包Scalarが元入力/値/支持/Scopeと違う".into());
        }
        Ok(analysis)
    }
    fn validate_comprehension_evaluation(
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
        let span = self.expression_span(graph, *expression)?;
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(false);
        };
        if !matches!(self.inputs.law().exprs[id].kind, ExprKind::SetComp { .. }) {
            return Ok(false);
        }
        if parts.len() != 1
            || parts[0].location != (Location::Law { span })
            || parts[0].value != *value
            || parts[0].residual.is_some()
            || *applicability != "applicable"
            || graph.context_at(expression.0) != self.current_context(graph)
        {
            return Err("内包Evaluationの元出現/型/partが違う".into());
        }
        let (own, analysis) = self.comprehension_parts(graph, span, &parts[0].children, limit)?;
        if own != *expression
            || self.expression_bindings(graph, own)? != bindings
            || node.scope != analysis.scope
            || node.support != analysis.support
        {
            return Err("内包Evaluationが元Source/支持/Scopeと違う".into());
        }
        let arguments: Vec<_> = std::iter::once(*expression)
            .chain(parts[0].children.iter().copied())
            .chain(*value)
            .collect();
        if node.arguments != arguments {
            return Err("内包Evaluationの構成辺が違う".into());
        }
        let mut reasons = Vec::new();
        for child in &parts[0].children {
            self.tick()?;
            reasons.extend(graph.get(*child)?.reasons.iter().cloned());
        }
        sort_reasons(&mut reasons);
        if node.reasons.len() != reasons.len() {
            return Err("内包Evaluationの元欠測理由数が違う".into());
        }
        for (actual, expected) in node.reasons.iter().zip(&reasons) {
            self.tick()?;
            // canonical理由の既存dedupと同じ、全wire欄の同一性を照合する。
            if actual.wire() != expected.wire() {
                return Err("内包Evaluationの元欠測理由が違う".into());
            }
        }
        match (value, &analysis.known_value) {
            (Some(value), Some(expected)) => {
                let scalar = graph.get(*value)?;
                if graph.context_at(value.0) != self.current_context(graph)
                    || graph.scalar(*value)? != expected
                    || scalar.arguments != parts[0].children
                    || !matches!(&scalar.rule,Rule::Input {kind:"law",location:Location::Law {span:actual}} if *actual==span)
                {
                    return Err("内包の生成値の元出現/反復辺が違う".into());
                }
                self.validate_at(graph, scalar, value.0)?;
            }
            (None, None) => {}
            _ => return Err("未知の内包を通常値へ変えている".into()),
        }
        Ok(true)
    }
    fn iteration_for(
        &self,
        graph: &Graph,
        comp: usize,
    ) -> Result<Option<usize>, ValidationFailure> {
        let mut current = self.current_context(graph).iteration;
        while let Some(index) = current {
            self.tick()?;
            let record = graph.iterations.get(index).ok_or("反復索引がない")?;
            if self.expression_span(graph, record.source)? == self.inputs.law().exprs[comp].span {
                return Ok(Some(index));
            }
            if record
                .caller
                .iteration
                .is_some_and(|parent| parent >= index)
            {
                return Err("反復の親が先行しない".into());
            }
            current = record.caller.iteration;
        }
        Ok(None)
    }
    fn iteration_input(
        &self,
        graph: &Graph,
        index: usize,
    ) -> Result<IterationInputs, ValidationFailure> {
        self.tick()?;
        let cache_key = (index, self.cutoff.get().min(graph.nodes.len()));
        if let Some(value) = self.cache.borrow().iterations.get(&cache_key).cloned() {
            return Ok(value);
        }
        let record = graph.iterations.get(index).ok_or("反復元がない")?;
        if record
            .caller
            .iteration
            .is_some_and(|parent| parent >= index)
            || record.source.0 >= record.domain.0
            || record.domain.0 >= self.cutoff.get().min(graph.nodes.len())
        {
            return Err("反復元Source/domain/親の先行性が違う".into());
        }
        if graph.context_at(record.source.0) != record.caller
            || graph.context_at(record.domain.0) != record.caller
        {
            return Err("反復元が親Contextに属さない".into());
        }
        let span = self.expression_span(graph, record.source)?;
        let id = *self.expressions.get(&span).ok_or("反復元ASTがない")?;
        let (domain, _) = self.iteration_syntax(id)?;
        let previous = self.context.replace(Some(record.caller));
        let result = (|| {
            self.validate_at(graph, graph.get(record.source)?, record.source.0)?;
            if domain.is_none() {
                let finite = record.finite.ok_or("型量化反復にDomainがない")?;
                if record.domain != finite {
                    return Err("型量化の元域が型Domainでない".into());
                }
                self.validate_at(graph, graph.get(finite)?, finite.0)?;
                let node = graph.get(finite)?;
                if node.arguments.first() != Some(&record.source) {
                    return Err("型量化Domainの元Sourceが違う".into());
                }
                let Some(Payload::Domain { ty, elements }) = &node.payload else {
                    return Err("型量化の有限域がない".into());
                };
                let super::call::Member::SetElement(member) = &record.member else {
                    return Err("型量化binderが要素でない".into());
                };
                if member.ty() != *ty
                    || !elements
                        .iter()
                        .any(|r| graph.scalar(*r).is_ok_and(|value| value == member))
                {
                    return Err("型量化binderが実型域に属さない".into());
                }
                let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
                let mut scope = node.scope.clone();
                scope.add_quantifier(spec.descriptor(Some(finite), Some(record.caller)));
                return Ok((
                    finite,
                    member.clone(),
                    SourceAnalysis {
                        scope: scope.clone(),
                        known_value: None,
                        support: node.support.clone(),
                        scalar_scope: Some(scope),
                        missing: None,
                    },
                ));
            }
            let domain = domain.ok_or("反復元collectionASTがない")?;
            self.recheck_evaluation(graph, record.domain)?;
            let (source, bindings, value) = self.evaluation(graph, record.domain)?;
            self.source_matches(graph, source, domain)?;
            if self.expression_bindings(graph, record.source)? != bindings {
                return Err("反復元の実束縛が違う".into());
            }
            let mut analysis =
                self.analyze_source(graph, self.inputs.law().exprs[domain].span, bindings)?;
            if value.map(|r| graph.scalar(r)).transpose()? != analysis.known_value.as_ref() {
                return Err("反復域値が元入力と違う".into());
            }
            analysis
                .scope
                .merge_quantifiers(&graph.get(record.domain)?.scope);
            let value = graph.scalar(value.ok_or("未知domainに反復がある")?)?;
            let quantified = matches!(self.inputs.law().exprs[id].kind, ExprKind::Quant { .. });
            if quantified {
                let finite = record.finite.ok_or("量化反復にDomainがない")?;
                self.validate_at(graph, graph.get(finite)?, finite.0)?;
                if graph.get(finite)?.arguments.get(..2)
                    != Some([record.source, record.domain].as_slice())
                {
                    return Err("量化反復Domainの元辺が違う".into());
                }
                let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
                let mut scope = Scope::default();
                scope.add_quantifier(spec.descriptor(Some(finite), Some(record.caller)));
                analysis.scope.merge(&scope);
                analysis
                    .scope
                    .order_quantifiers_like(&graph.get(record.source)?.scope);
            } else if record.finite.is_some() {
                return Err("内包反復に量化Domainがある".into());
            }
            let member = match (&record.member, value) {
                (
                    super::call::Member::SetElement(member),
                    Scalar::List { element, items } | Scalar::Set { element, items },
                ) if quantified
                    && member.ty() == *element
                    && data::contains(items, member, &self.control)? =>
                {
                    let Some(Payload::Domain { elements, .. }) = &graph
                        .get(record.finite.ok_or("量化反復にDomainがない")?)?
                        .payload
                    else {
                        return Err("量化反復の有限域がない".into());
                    };
                    if !elements
                        .iter()
                        .any(|r| graph.scalar(*r).is_ok_and(|value| value == member))
                    {
                        return Err("量化binderが実Domain要素でない".into());
                    }
                    member.clone()
                }
                (super::call::Member::ListPosition(position), Scalar::List { items, .. })
                    if !quantified =>
                {
                    items.get(*position).ok_or("List反復位置が域外")?.clone()
                }
                (super::call::Member::SetElement(member), Scalar::Set { element, items })
                    if !quantified
                        && member.ty() == *element
                        && data::contains(items, member, &self.control)? =>
                {
                    member.clone()
                }
                _ => return Err("List位置/Set要素が元domainと違う".into()),
            };
            Ok((record.domain, member, analysis))
        })();
        self.context.set(previous);
        if let Ok(value) = &result {
            self.cache
                .borrow_mut()
                .iterations
                .insert(cache_key, value.clone());
        }
        result
    }
    fn iteration_binding(
        &self,
        graph: &Graph,
        span: (usize, usize),
        name: &str,
        bindings: &[Binding],
    ) -> Result<Option<(NodeRef, Scalar)>, ValidationFailure> {
        if self.name_token(span)? != name {
            return Err("反復名の元使用tokenが違う".into());
        }
        let mut result = None;
        for (actual, origin) in self.lexical_context(span)? {
            self.tick()?;
            if actual == name
                && let LexicalOrigin::Iteration(comp) = origin
            {
                let index = self
                    .iteration_for(graph, comp)?
                    .ok_or("反復binderの実Contextがない")?;
                let record = &graph.iterations[index];
                if self.expression_bindings(graph, record.source)? != bindings {
                    return Err("反復binderの宣言束縛が違う".into());
                }
                let (domain, member, _) = self.iteration_input(graph, index)?;
                if result.replace((domain, member)).is_some() {
                    return Err("反復binderが一意でない".into());
                }
            }
        }
        Ok(result)
    }
    pub(crate) fn iteration_argument(
        &self,
        graph: &Graph,
        span: (usize, usize),
        name: &str,
        bindings: &[Binding],
    ) -> Result<Option<(NodeRef, Scalar)>, ValidationFailure> {
        Ok(self
            .iteration_binding(graph, span, name, bindings)?
            .filter(|(input, _)| {
                matches!(
                    graph.get(*input).map(|n| &n.ty),
                    Ok(NodeType::Evaluation(_))
                )
            }))
    }
    pub(super) fn type_iteration_argument(
        &self,
        graph: &Graph,
        span: (usize, usize),
        name: &str,
        bindings: &[Binding],
    ) -> Result<Option<(NodeRef, Scalar)>, ValidationFailure> {
        Ok(self
            .iteration_binding(graph, span, name, bindings)?
            .filter(|(input, _)| matches!(graph.get(*input).map(|n| &n.ty), Ok(NodeType::Domain))))
    }
    pub(crate) fn source_arguments(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<Vec<NodeRef>, ValidationFailure> {
        let mut arguments: Vec<_> = bindings.iter().map(|b| b.value).collect();
        if let Some(index) = self.current_context(graph).frame {
            let frame = graph.frames.get(index).ok_or("Sourceのcall frameがない")?;
            arguments.push(frame.source);
            arguments.extend(&frame.arguments);
        }
        if let Some(index) = self.current_context(graph).iteration {
            let record = graph.iterations.get(index).ok_or("Sourceの反復がない")?;
            arguments.extend([record.source, record.domain]);
            if record.finite != Some(record.domain) {
                arguments.extend(record.finite);
            }
            if let Some(domain) = record.finite {
                let (_, member, _) = self.iteration_input(graph, index)?;
                let Some(Payload::Domain { elements, .. }) = &graph.get(domain)?.payload else {
                    return Err("量化SourceのDomain要素がない".into());
                };
                let reference = *elements
                    .iter()
                    .find(|r| graph.scalar(**r).is_ok_and(|v| v == &member))
                    .ok_or("量化Sourceの実memberがない")?;
                arguments.push(reference);
            }
        }
        if let Some(index) = self.current_context(graph).instance {
            let record = graph
                .instances
                .get(index)
                .ok_or("Sourceの実instanceがない")?;
            arguments.extend([record.source, record.domain, record.member]);
        }
        for (matching, arm) in self.enclosing_matches(span)? {
            let ExprKind::Match { scrutinee, .. } = self.inputs.law().exprs[matching].kind else {
                unreachable!()
            };
            let input = self.actual_evaluation(graph, scrutinee, bindings)?;
            let value = self
                .evaluation(graph, input)?
                .2
                .map(|r| graph.scalar(r))
                .transpose()?;
            if data::select(self.inputs.law(), matching, value, &self.control)? != Some(arm) {
                return Err("Sourceが実選択armに属さない".into());
            }
            arguments.push(input);
        }
        Ok(arguments)
    }
    pub(crate) fn call_parameter(
        &self,
        graph: &Graph,
        name: &str,
    ) -> Result<Option<NodeRef>, ValidationFailure> {
        let Some(index) = self.current_context(graph).frame else {
            return Ok(None);
        };
        let frame = graph.frames.get(index).ok_or("parameterのframeがない")?;
        let span = self.expression_span(graph, frame.source)?;
        let d = self
            .named_view(*self.expressions.get(&span).ok_or("call ASTがない")?)?
            .ok_or("call targetがない")?;
        let crate::law::model::Signature::View { params, .. } = &d.signature else {
            unreachable!()
        };
        Ok(params
            .iter()
            .position(|p| p.name == name)
            .map(|i| frame.arguments[i]))
    }
    pub(crate) fn analyze_source(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<SourceAnalysis, ValidationFailure> {
        self.validation_session(|| {
            self.tick()?;
            let context = self.current_context(graph);
            let cutoff = self.cutoff.get().min(graph.nodes.len());
            let cached = self
                .cache
                .borrow()
                .sources
                .iter()
                .find(|(c, l, at, actual, _)| {
                    *c == context && *l == cutoff && *at == span && actual == bindings
                })
                .map(|entry| entry.4.clone());
            if let Some(value) = cached {
                return Ok(value);
            }
            let previous = self.scoped_context.replace(Some(context));
            let result = self.analyze_source_uncached(graph, span, bindings);
            self.scoped_context.set(previous);
            let value = result?;
            self.cache.borrow_mut().sources.push((
                context,
                cutoff,
                span,
                bindings.to_vec(),
                value.clone(),
            ));
            Ok(value)
        })
    }
    fn analyze_source_uncached(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
    ) -> Result<SourceAnalysis, ValidationFailure> {
        let mut declaration = None;
        for d in self.inputs.law().declarations.values() {
            self.tick()?;
            if d.span.0 <= span.0 && span.1 <= d.span.1 {
                if declaration.is_some() {
                    return Err("原式を所有する宣言が一意でない".into());
                }
                declaration = Some(d);
            }
            self.tick()?;
        }
        let declaration = declaration.ok_or("原式を所有する宣言がない")?;
        let params = match &declaration.signature {
            crate::law::model::Signature::View { params, .. }
            | crate::law::model::Signature::Law { params, .. } => params,
            _ => return Err("評価範囲の元宣言が view/Law でない".into()),
        };
        let (mut base, mut variables) = if let Some(index) = self.current_context(graph).frame {
            let frame = graph.frames.get(index).ok_or("元式のframeがない")?;
            let call_span = self.expression_span(graph, frame.source)?;
            let target = self
                .named_view(
                    *self
                        .expressions
                        .get(&call_span)
                        .ok_or("callの元ASTがない")?,
                )?
                .ok_or("call targetがない")?;
            if target.span != declaration.span {
                return Err("callee元式が静的targetのbodyでない".into());
            }
            let (expected, variables, base) = self.frame_arguments(graph, index)?;
            if expected != bindings {
                return Err("calleeの既知束縛が実引数と違う".into());
            }
            (base, variables)
        } else if let Some(index) = self.current_context(graph).instance {
            let request = graph
                .requests
                .get(self.current_context(graph).request)
                .ok_or("実instance元Requestがない")?;
            if request.declaration() != declaration.name {
                return Err("instance Sourceが別宣言".into());
            }
            let (expected, variables, base) = self.family_instance_inputs(graph, index)?;
            if expected != bindings {
                return Err("Sourceの実instance bindingsが元直積と違う".into());
            }
            (base, variables)
        } else {
            if params.len() != bindings.len() {
                return Err("評価範囲のparameter束縛数が違う".into());
            }
            let mut base = Scope::default();
            base.readings.insert(declaration.reading.clone());
            let mut variables = BTreeMap::new();
            for (parameter, binding) in params.iter().zip(bindings) {
                self.tick()?;
                if parameter.name != binding.name || parameter.ty.erase() != binding.ty {
                    return Err("評価範囲の元parameter署名が違う".into());
                }
                let value = graph.scalar(binding.value)?;
                let Scalar::Subject {
                    snapshot,
                    subject,
                    entity,
                } = value
                else {
                    return Err("未実装の値parameterを評価範囲へ持ち込んでいる".into());
                };
                let actual = self.subject(snapshot, subject)?;
                if &actual.ty != entity || value.ty() != binding.ty {
                    return Err("評価範囲の束縛subject型が違う".into());
                }
                let subject_scope = self.scope(actual, &declaration.reading, None)?;
                if graph.get(binding.value)?.scope != subject_scope {
                    return Err("束縛subject値の範囲が元宣言・subject由来と違う".into());
                }
                base.merge(&subject_scope);
                variables.insert(
                    binding.name.clone(),
                    SourceValue {
                        scope: base.clone(),
                        known_value: Some(value.clone()),
                        support: self.subject_support(value)?,
                        scalar_scope: Some(subject_scope),
                    },
                );
                self.tick()?;
            }

            if let Some(request) = graph.requests.get(self.current_context(graph).request) {
                if request.declaration() != declaration.name {
                    return Err("元SourceがRequest宣言と違う".into());
                }
                for binding in bindings {
                    let arg = request
                        .arguments
                        .iter()
                        .find(|a| a.name == format!("bind.{}", binding.name))
                        .ok_or("Requestの元束縛がない")?;
                    match (&arg.value, graph.scalar(binding.value)?) {
                        (
                            Selector::Subject { snapshot, subject },
                            Scalar::Subject {
                                snapshot: s,
                                subject: v,
                                ..
                            },
                        ) if snapshot == s && subject == v => {}
                        _ => return Err("元Source束縛がRequest実入力と違う".into()),
                    }
                }
            }
            (base, variables)
        };
        // parameter の範囲は全明示束縛を含む。Scalar 自体の由来範囲とは区別する。
        for variable in variables.values_mut() {
            self.tick()?;
            variable.scope = base.clone();
            self.tick()?;
        }
        for (name, rhs) in self.lexical_context(span)? {
            self.tick()?;
            let value = match rhs {
                LexicalOrigin::Let(rhs) => self.scoped_ast_at(
                    rhs,
                    &variables,
                    &base,
                    &declaration.reading,
                    Some(self.lexical_evaluation_context(graph, rhs)?),
                )?,
                LexicalOrigin::Iteration(comp) => {
                    let index = self
                        .iteration_for(graph, comp)?
                        .ok_or("元内包binderに実反復がない")?;
                    let (_, member, analysis) = self.iteration_input(graph, index)?;
                    base.merge(&analysis.scope);
                    for value in variables.values_mut() {
                        value.scope.merge(&base);
                    }
                    SourceValue {
                        scope: base.clone(),
                        known_value: Some(member),
                        support: analysis.support,
                        scalar_scope: Some(base.clone()),
                    }
                }
                LexicalOrigin::Pattern {
                    matching,
                    arm,
                    binder,
                } => {
                    let ExprKind::Match { scrutinee, .. } = self.inputs.law().exprs[matching].kind
                    else {
                        unreachable!()
                    };
                    let mut input = self.scoped_ast_at(
                        scrutinee,
                        &variables,
                        &base,
                        &declaration.reading,
                        Some(self.lexical_evaluation_context(graph, scrutinee)?),
                    )?;
                    if data::select(
                        self.inputs.law(),
                        matching,
                        input.known_value.as_ref(),
                        &self.control,
                    )? != Some(arm)
                    {
                        return Err("Sourceが実選択armに属さない".into());
                    }
                    input.known_value = input
                        .known_value
                        .as_ref()
                        .map(|value| data::project(value, &binder.path, &self.control))
                        .transpose()?;
                    input.scalar_scope = input.known_value.as_ref().map(|_| input.scope.clone());
                    input
                }
            };
            if variables.insert(name, value).is_some() {
                return Err("lexical 名が元parameterと重複する".into());
            }
            self.tick()?;
        }
        if let Some(&id) = self.expressions.get(&span) {
            let SourceValue {
                scope,
                known_value,
                support,
                scalar_scope,
            } = self.scoped_ast(id, &variables, &base, &declaration.reading)?;
            let direct_field = match &self.inputs.law().exprs[id].kind {
                ExprKind::Dotted(parts) if parts.len() == 2 => Some((
                    variables
                        .get(&parts[0].name)
                        .and_then(|v| v.known_value.clone()),
                    parts[1].name.as_str(),
                )),
                ExprKind::Field { base: owner, name } => Some((
                    self.scoped_ast(*owner, &variables, &base, &declaration.reading)?
                        .known_value,
                    name.name.as_str(),
                )),
                _ => None,
            };
            let missing = if let Some((
                Some(Scalar::Subject {
                    ref snapshot,
                    ref subject,
                    ref entity,
                }),
                name,
            )) = direct_field
            {
                let field = self.field(snapshot, subject, &format!("{entity}.{name}"))?;
                match &field.slot {
                    Slot::Missing => Some(PendingMissing {
                        fact: Fact {
                            snapshot: snapshot.clone(),
                            subject: subject.clone(),
                            field: Some(field.name.clone()),
                            atom: None,
                        },
                    }),
                    Slot::Known { .. } => None,
                }
            } else {
                None
            };
            return Ok(SourceAnalysis {
                scope,
                known_value,
                missing,
                support,
                scalar_scope,
            });
        }
        // prefix の独立再分析も、Source validation と同じ実token照合を必須にする。
        let name = self.name_token(span)?;
        let value = variables
            .get(name)
            .ok_or("評価範囲に元束縛以外のfragmentがある")?;
        Ok(SourceAnalysis {
            scope: value.scope.clone(),
            known_value: value.known_value.clone(),
            missing: None,
            support: value.support.clone(),
            scalar_scope: if self.projects_lexical_binding(span, name)? {
                value.known_value.as_ref().map(|_| value.scope.clone())
            } else {
                value.scalar_scope.clone()
            },
        })
    }
    fn subject_support(&self, value: &Scalar) -> Result<Vec<Fact>, ValidationFailure> {
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = value
        else {
            return Err("支持の元parameterがRefでない".into());
        };
        if self.subject(snapshot, subject)?.ty != *entity {
            return Err("支持の元subject型が違う".into());
        }
        Ok(vec![Fact {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: None,
            atom: None,
        }])
    }
    fn copy_variables(
        &self,
        variables: &BTreeMap<String, SourceValue>,
    ) -> Result<BTreeMap<String, SourceValue>, ValidationFailure> {
        let mut copy = BTreeMap::new();
        for (name, value) in variables {
            self.tick()?;
            copy.insert(name.clone(), value.clone());
            self.tick()?;
        }
        Ok(copy)
    }
    fn scoped_ast_at(
        &self,
        id: usize,
        variables: &BTreeMap<String, SourceValue>,
        base: &Scope,
        reading: &str,
        context: Option<super::call::Context>,
    ) -> Result<SourceValue, ValidationFailure> {
        let previous = self.scoped_context.replace(context);
        let result = self.scoped_ast(id, variables, base, reading);
        self.scoped_context.set(previous);
        result
    }
    fn scoped_ast(
        &self,
        id: usize,
        variables: &BTreeMap<String, SourceValue>,
        base: &Scope,
        reading: &str,
    ) -> Result<SourceValue, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let expression = &self.inputs.law().exprs[id];
            let result = match &expression.kind {
                ExprKind::Int(n) => SourceValue {
                    scope: base.clone(),
                    known_value: Some(numeric::literal(
                        n,
                        self.inputs
                            .law()
                            .expr_type(id)
                            .ok_or("literal の型がない")?,
                        &self.control,
                    )?),
                    support: vec![],
                    scalar_scope: Some(base.clone()),
                },
                ExprKind::Bool(b) => SourceValue {
                    scope: base.clone(),
                    known_value: Some(Scalar::Bool(*b)),
                    support: vec![],
                    scalar_scope: Some(base.clone()),
                },
                ExprKind::Dotted(_)
                    if data::expression(self.inputs.law(), id, &self.control)?.is_some() =>
                {
                    SourceValue {
                        scope: base.clone(),
                        known_value: Some(self.composite_value(id, &[])?),
                        support: vec![],
                        scalar_scope: Some(base.clone()),
                    }
                }
                ExprKind::Dotted(parts) => {
                    let first = parts.first().ok_or("範囲検査の空Dotted")?;
                    let mut result = variables
                        .get(&first.name)
                        .ok_or("範囲検査の未知lexical名")?
                        .clone();
                    // pattern/反復binderは使用位置で射影Scalarを作る。let alias
                    // は元RHS Scalarを参照するので、そのscalar_scopeを変えない。
                    if self.projects_lexical_binding(first.span, &first.name)? {
                        result.scope.merge(base);
                        result.scalar_scope =
                            result.known_value.as_ref().map(|_| result.scope.clone());
                    }
                    for part in parts.iter().skip(1) {
                        self.tick()?;
                        result = self.scoped_field(
                            result,
                            &part.name,
                            base,
                            reading,
                            (first.span.0, part.span.1),
                        )?;
                        self.tick()?;
                    }
                    result
                }
                ExprKind::Field { base: owner, name } => self.scoped_field(
                    self.scoped_ast(*owner, variables, base, reading)?,
                    &name.name,
                    base,
                    reading,
                    expression.span,
                )?,
                ExprKind::Group(child) => self.scoped_ast(*child, variables, base, reading)?,
                ExprKind::Unary { op, operand } => {
                    let ty = self
                        .inputs
                        .law()
                        .expr_type(id)
                        .ok_or("単項元式の型がない")?;
                    if !((*op == UnOp::Neg && numeric::is_numeric_type(ty, &self.control)?)
                        || (*op == UnOp::Not && ty == &Type::Bool))
                    {
                        return Err(ValidationFailure::UnsupportedExpression {
                            location: Location::Law {
                                span: expression.span,
                            },
                            feature: "対応済み数値/Bool単項演算以外".into(),
                        });
                    }
                    let SourceValue {
                        scope,
                        known_value,
                        support,
                        ..
                    } = self.scoped_ast(*operand, variables, base, reading)?;
                    let known_value = known_value
                        .as_ref()
                        .map(|value| unary(*op, value, &self.control))
                        .transpose()?;
                    let scalar_scope = known_value.as_ref().map(|_| scope.clone());
                    SourceValue {
                        scope,
                        known_value,
                        support,
                        scalar_scope,
                    }
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    if !supports_binary(
                        *op,
                        self.inputs
                            .law()
                            .expr_type(*lhs)
                            .ok_or("二項元式の型がない")?,
                        &self.control,
                    )? {
                        return Err(ValidationFailure::UnsupportedExpression {
                            location: Location::Law {
                                span: expression.span,
                            },
                            feature: "対応済み Z/Bool 二項演算以外".into(),
                        });
                    }
                    let SourceValue {
                        mut scope,
                        known_value: left,
                        mut support,
                        ..
                    } = self.scoped_ast(*lhs, variables, base, reading)?;
                    let right = self.scoped_ast(*rhs, variables, base, reading)?;
                    scope.merge(&right.scope);
                    support.extend(right.support);
                    support.sort();
                    support.dedup();
                    let known_value = partial_binary(
                        *op,
                        left.as_ref(),
                        right.known_value.as_ref(),
                        &self.control,
                    )?;
                    let scalar_scope = known_value.as_ref().map(|_| scope.clone());
                    SourceValue {
                        scope,
                        known_value,
                        support,
                        scalar_scope,
                    }
                }
                ExprKind::Quant { .. } => {
                    let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
                    let (input, members) = if let Some(domain) = spec.domain {
                        let input = self.scoped_ast(domain, variables, base, reading)?;
                        let members = match &input.known_value {
                            Some(Scalar::List { items, .. } | Scalar::Set { items, .. }) => {
                                let value = data::set(spec.element.clone(), items, &self.control)?;
                                let Scalar::Set { items, .. } = &value else {
                                    unreachable!()
                                };
                                Some(items.clone())
                            }
                            None => None,
                            _ => return Err("量化域がList/Setでない".into()),
                        };
                        (input, members)
                    } else {
                        let enumeration = self.finite_values(&spec.element, &mut |_, _| {})?;
                        let mut scope = base.clone();
                        scope.merge(&enumeration.scope);
                        (
                            SourceValue {
                                scope,
                                known_value: None,
                                support: enumeration.support,
                                scalar_scope: None,
                            },
                            Some(enumeration.values),
                        )
                    };
                    // 親/lexical値が既に持つ出現はその由来順を保つ。
                    // このdomain式で新たに現れる量化は自身より後に置く。
                    let mut inherited = base.clone();
                    for value in variables.values() {
                        self.tick()?;
                        inherited.merge_quantifiers(&value.scope);
                    }
                    let mut scope = input.scope.clone();
                    scope.quantifiers.retain(|q| {
                        inherited
                            .quantifiers
                            .iter()
                            .any(|old| old.occurrence == q.occurrence)
                    });
                    scope.add_quantifier(spec.descriptor(None, self.scoped_context.get()));
                    scope.merge_quantifiers(&input.scope);
                    let Some(items) = members else {
                        return Ok(SourceValue {
                            scope,
                            known_value: None,
                            support: input.support,
                            scalar_scope: None,
                        });
                    };
                    let mut support = input.support.clone();
                    let mut values = Vec::new();
                    for item in items {
                        self.tick()?;
                        let mut local = self.copy_variables(variables)?;
                        for value in local.values_mut() {
                            value.scope.merge(&scope);
                        }
                        if local
                            .insert(
                                spec.name.into(),
                                SourceValue {
                                    scope: scope.clone(),
                                    known_value: Some(item.clone()),
                                    support: input.support.clone(),
                                    scalar_scope: Some(scope.clone()),
                                },
                            )
                            .is_some()
                        {
                            return Err("量化binderが重複する".into());
                        }
                        let body = self.scoped_ast_at(spec.body, &local, &scope, reading, None)?;
                        scope.merge(&body.scope);
                        support.extend(body.support);
                        values.push(match body.known_value {
                            Some(Scalar::Bool(value)) => Some(value),
                            None => None,
                            _ => return Err("量化本体がBoolでない".into()),
                        });
                        self.tick()?;
                    }
                    support.sort();
                    support.dedup();
                    let known_value =
                        quantifier::reduce(spec.kind, &values, &self.control)?.map(Scalar::Bool);
                    SourceValue {
                        scalar_scope: known_value.as_ref().map(|_| scope.clone()),
                        scope,
                        known_value,
                        support,
                    }
                }
                ExprKind::SetComp {
                    elem,
                    var,
                    domain,
                    filter,
                } => {
                    if !data::supported(
                        self.inputs.law().expr_type(id).ok_or("内包結果型がない")?,
                        self.inputs.law(),
                        &self.control,
                    )? {
                        return Err(ValidationFailure::UnsupportedExpression {
                            location: Location::Law {
                                span: expression.span,
                            },
                            feature: "未対応payload・型または再帰DataのSet内包".into(),
                        });
                    }
                    let input = self.scoped_ast(*domain, variables, base, reading)?;
                    let Some(container) = input.known_value.as_ref() else {
                        return Ok(SourceValue {
                            scalar_scope: None,
                            ..input
                        });
                    };
                    let items = match container {
                        Scalar::List { items, .. } | Scalar::Set { items, .. } => items,
                        _ => return Err("内包元域がList/Setでない".into()),
                    };
                    let mut scope = input.scope.clone();
                    let mut support = input.support.clone();
                    let mut values = Vec::new();
                    let mut known = true;
                    for item in items {
                        self.tick()?;
                        let mut local = self.copy_variables(variables)?;
                        for value in local.values_mut() {
                            value.scope.merge(&input.scope);
                        }
                        if local
                            .insert(
                                var.name.clone(),
                                SourceValue {
                                    scope: input.scope.clone(),
                                    known_value: Some(item.clone()),
                                    support: input.support.clone(),
                                    scalar_scope: Some(input.scope.clone()),
                                },
                            )
                            .is_some()
                        {
                            return Err("内包binderが重複する".into());
                        }
                        let condition = if let Some(filter) = filter {
                            let value =
                                self.scoped_ast_at(*filter, &local, &input.scope, reading, None)?;
                            scope.merge(&value.scope);
                            support.extend(value.support);
                            match value.known_value.as_ref() {
                                Some(Scalar::Bool(b)) => Some(*b),
                                None => None,
                                _ => return Err("内包filterがBoolでない".into()),
                            }
                        } else {
                            Some(true)
                        };
                        match condition {
                            Some(true) => {
                                let value =
                                    self.scoped_ast_at(*elem, &local, &input.scope, reading, None)?;
                                scope.merge(&value.scope);
                                support.extend(value.support);
                                if let Some(value) = value.known_value {
                                    values.push(value);
                                } else {
                                    known = false;
                                }
                            }
                            Some(false) => {}
                            None => known = false,
                        }
                        self.tick()?;
                    }
                    support.sort();
                    support.dedup();
                    let Type::Set(element) =
                        self.inputs.law().expr_type(id).ok_or("内包結果型がない")?
                    else {
                        return Err("内包結果型がSetでない".into());
                    };
                    let known_value = if known {
                        Some(data::set((**element).clone(), &values, &self.control)?)
                    } else {
                        None
                    };
                    SourceValue {
                        scalar_scope: known_value.as_ref().map(|_| scope.clone()),
                        scope,
                        known_value,
                        support,
                    }
                }
                ExprKind::Match { scrutinee, arms } => {
                    let input = self.scoped_ast(*scrutinee, variables, base, reading)?;
                    let Some(arm) = data::select(
                        self.inputs.law(),
                        id,
                        input.known_value.as_ref(),
                        &self.control,
                    )?
                    else {
                        return Ok(SourceValue {
                            scalar_scope: None,
                            ..input
                        });
                    };
                    let mut local = self.copy_variables(variables)?;
                    let value = input.known_value.as_ref().ok_or("選択済matchの値がない")?;
                    for (name, value) in
                        data::bindings(self.inputs.law(), id, arm, value, &self.control)?
                    {
                        if local
                            .insert(
                                name,
                                SourceValue {
                                    scope: input.scope.clone(),
                                    known_value: Some(value),
                                    support: input.support.clone(),
                                    scalar_scope: Some(input.scope.clone()),
                                },
                            )
                            .is_some()
                        {
                            return Err("pattern名が重複する".into());
                        }
                    }
                    let body = self.scoped_ast(arms[arm].body, &local, base, reading)?;
                    let mut scope = input.scope;
                    scope.merge(&body.scope);
                    let mut support = input.support;
                    support.extend(body.support);
                    support.sort();
                    support.dedup();
                    SourceValue {
                        scalar_scope: body.known_value.as_ref().map(|_| scope.clone()),
                        scope,
                        known_value: body.known_value,
                        support,
                    }
                }
                ExprKind::Let { name, value, body } => {
                    let rhs = self.scoped_ast(*value, variables, base, reading)?;
                    let mut local = self.copy_variables(variables)?;
                    if local.insert(name.name.clone(), rhs.clone()).is_some() {
                        return Err("let 名が重複する".into());
                    }
                    let body = self.scoped_ast(*body, &local, base, reading)?;
                    let mut scope = rhs.scope;
                    scope.merge(&body.scope);
                    let mut support = rhs.support;
                    support.extend(body.support);
                    support.sort();
                    support.dedup();
                    let known_value = body.known_value;
                    let scalar_scope = known_value.as_ref().map(|_| scope.clone());
                    SourceValue {
                        scope,
                        support,
                        known_value,
                        scalar_scope,
                    }
                }
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    let condition = self.scoped_ast(*cond, variables, base, reading)?;
                    let left = self.scoped_ast(*then_branch, variables, base, reading)?;
                    let right = self.scoped_ast(*else_branch, variables, base, reading)?;
                    let known_value = conditional_branch(
                        condition.known_value.as_ref(),
                        left.known_value.as_ref(),
                        right.known_value.as_ref(),
                        &self.control,
                    )?;
                    let mut scope = condition.scope;
                    scope.merge(&left.scope);
                    scope.merge(&right.scope);
                    let mut support = condition.support;
                    support.extend(left.support);
                    support.extend(right.support);
                    support.sort();
                    support.dedup();
                    let scalar_scope = known_value.as_ref().map(|_| scope.clone());
                    SourceValue {
                        scope,
                        support,
                        known_value,
                        scalar_scope,
                    }
                }
                ExprKind::Call { args, .. } if self.named_view(id)?.is_some() => {
                    let declaration = self.named_view(id)?.ok_or("named viewがない")?;
                    let crate::law::model::Signature::View { params, body, .. } =
                        &declaration.signature
                    else {
                        unreachable!()
                    };
                    let mut local = BTreeMap::new();
                    let mut call_base = base.clone();
                    call_base.readings.insert(declaration.reading.clone());
                    let mut support = Vec::new();
                    for (parameter, &arg) in params.iter().zip(args) {
                        self.tick()?;
                        let value = self.scoped_ast(arg, variables, base, reading)?;
                        call_base.merge(&value.scope);
                        support.extend(value.support.iter().cloned());
                        local.insert(parameter.name.clone(), value);
                    }
                    for value in local.values_mut() {
                        value.scope.merge(&call_base);
                    }
                    let body =
                        self.scoped_ast_at(*body, &local, &call_base, &declaration.reading, None)?;
                    call_base.merge(&body.scope);
                    support.extend(body.support);
                    support.sort();
                    support.dedup();
                    SourceValue {
                        scalar_scope: body.known_value.as_ref().map(|_| call_base.clone()),
                        scope: call_base,
                        known_value: body.known_value,
                        support,
                    }
                }
                ExprKind::Tuple(_)
                | ExprKind::ListLit { .. }
                | ExprKind::SetLit { .. }
                | ExprKind::None(_)
                | ExprKind::Some(_)
                | ExprKind::Unit
                | ExprKind::Str(_)
                | ExprKind::Index { .. }
                | ExprKind::Call { .. } => {
                    let children = self.composite_children(id)?.ok_or_else(|| {
                        ValidationFailure::UnsupportedExpression {
                            location: Location::Law {
                                span: expression.span,
                            },
                            feature: "数値組・射影・rat 以外の構成".into(),
                        }
                    })?;
                    let mut scope = base.clone();
                    let mut support = Vec::new();
                    let mut values = Vec::new();
                    let mut known = true;
                    for child in children {
                        self.tick()?;
                        let child = self.scoped_ast(child, variables, base, reading)?;
                        scope.merge(&child.scope);
                        support.extend(child.support);
                        if let Some(value) = child.known_value {
                            values.push(value)
                        } else {
                            known = false
                        }
                        self.tick()?;
                    }
                    support.sort();
                    support.dedup();
                    let known_value = if known {
                        Some(self.composite_value(id, &values)?)
                    } else {
                        None
                    };
                    let scalar_scope = known_value.as_ref().map(|_| scope.clone());
                    SourceValue {
                        scope,
                        support,
                        known_value,
                        scalar_scope,
                    }
                }
                _ => {
                    return Err(ValidationFailure::UnsupportedExpression {
                        location: Location::Law {
                            span: expression.span,
                        },
                        feature: format!("式形 {:?}", expression.kind),
                    });
                }
            };
            self.tick()?;
            Ok(result)
        })
    }
    fn scoped_field(
        &self,
        base: SourceValue,
        name: &str,
        request_base: &Scope,
        reading: &str,
        span: (usize, usize),
    ) -> Result<SourceValue, ValidationFailure> {
        let SourceValue {
            mut scope,
            known_value,
            mut support,
            ..
        } = base;
        if known_value.is_none() {
            return Err(ValidationFailure::UnsupportedExpression {
                location: Location::Law { span },
                feature: "未確定の参照からの field 読取り".into(),
            });
        }
        let Some(Scalar::Subject {
            snapshot,
            subject,
            entity,
        }) = known_value.as_ref()
        else {
            return Err("範囲検査のfield ownerがRef以外".into());
        };
        let (snapshot, subject, entity) = (snapshot.clone(), subject.clone(), entity.clone());
        let owner = self.subject(&snapshot, &subject)?;
        if owner.ty != entity {
            return Err("範囲検査のfield owner型不一致".into());
        }
        let field = self.field(&snapshot, &subject, &format!("{entity}.{name}"))?;
        let (known_value, scalar_scope) = match &field.slot {
            Slot::Known {
                atom,
                origin,
                value,
                ..
            } => {
                let owner_scope = self.scope(owner, reading, Some(origin))?;
                scope.merge(&owner_scope);
                let mut scalar_scope = request_base.clone();
                scalar_scope.merge(&owner_scope);
                support.push(Fact {
                    snapshot,
                    subject,
                    field: Some(field.name.clone()),
                    atom: Some(atom.clone()),
                });
                (
                    Some(
                        scalar_from(value, &field.ty, self.inputs.law(), &self.control)?
                            .ok_or_else(|| ValidationFailure::UnsupportedExpression {
                                location: Location::Law { span },
                                feature: "Z/Bool/Ref 以外の原始値読取り".into(),
                            })?,
                    ),
                    Some(scalar_scope),
                )
            }
            Slot::Missing => {
                scope.merge(&self.scope(owner, reading, None)?);
                scope.completions = true;
                (None, None)
            }
        };
        support.sort();
        support.dedup();
        Ok(SourceValue {
            scope,
            known_value,
            support,
            scalar_scope,
        })
    }
    // 変換の Scope は元 Source と実束縛から再構成し、中間 node の自己申告を使わない。
    fn transform_scope(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<Scope, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            let Some(Payload::Transform {
                operation,
                operands,
                bindings,
            }) = &node.payload
            else {
                return Err("Bool 固定変換でない".into());
            };
            if node.ty != NodeType::Expression(Type::Bool)
                || !matches!(&node.rule, Rule::Construction("expression"))
                || operands.len() != operation.arity()
                || !node.support.is_empty()
                || !node.evidence.is_empty()
                || !node.reasons.is_empty()
                || node.judgment.is_some()
            {
                return Err("Bool 固定変換の型・構成条件が違う".into());
            }
            let mut arguments = Vec::new();
            let mut scope = Scope::default();
            for &reference in operands {
                self.tick()?;
                if reference.0 >= limit {
                    return Err("Bool 変換の operand が既出でない".into());
                }
                graph.expect(reference, &NodeType::Expression(Type::Bool))?;
                if self.expression_bindings(graph, reference)? != bindings {
                    return Err("Bool 変換の元 operand 束縛が違う".into());
                }
                let operand = graph.get(reference)?;
                let original_scope = match &operand.payload {
                    Some(Payload::Expression {
                        location: Location::Law { span },
                        bindings,
                        ..
                    }) => {
                        self.validate_at(graph, operand, reference.0)?;
                        let mut scope = self.source_scope(graph, *span, bindings)?;
                        if !scope.quantifiers.is_empty() {
                            let id = *self.expressions.get(span).ok_or("変換元量化ASTがない")?;
                            let actual = self.actual_evaluation(graph, id, bindings)?;
                            scope.merge_quantifiers(&graph.get(actual)?.scope);
                        }
                        scope
                    }
                    Some(Payload::Transform { .. }) => {
                        self.transform_scope(graph, operand, reference.0)?
                    }
                    _ => return Err("Bool 変換が元式・固定変換以外に依存する".into()),
                };
                scope.merge(&original_scope);
                arguments.push(reference);
                self.tick()?;
            }
            for binding in bindings {
                self.tick()?;
                if binding.value.0 >= limit {
                    return Err("Bool 変換の束縛が既出でない".into());
                }
                graph.expect(binding.value, &NodeType::Value(binding.ty.clone()))?;
                arguments.push(binding.value);
                self.tick()?;
            }
            if node.arguments != arguments || node.scope != scope {
                return Err("Bool 変換の依存・範囲が元式と違う".into());
            }
            self.tick()?;
            Ok(scope)
        })
    }
    fn transform_operands<'g>(
        &self,
        graph: &'g Graph,
        expression: NodeRef,
        operation: TransformOp,
        bindings: &[Binding],
    ) -> Result<&'g [NodeRef], ValidationFailure> {
        self.tick()?;
        let Some(Payload::Transform {
            operation: actual,
            operands,
            bindings: actual_bindings,
        }) = &graph.get(expression)?.payload
        else {
            return Err("含意の native Bool 変換がない".into());
        };
        if *actual != operation
            || operands.len() != operation.arity()
            || actual_bindings != bindings
        {
            return Err("含意の変換・束縛が元 Law と違う".into());
        }
        self.tick()?;
        Ok(operands)
    }
    // 未知 guard を false にせず、元 guard/body の再検査済み値から含意を確認する。
    fn conditional_value(
        &self,
        graph: &Graph,
        instance: NodeRef,
        expression: NodeRef,
    ) -> Result<Option<bool>, ValidationFailure> {
        self.tick()?;
        let (body, guard) = self.application_at(graph, instance)?;
        let guard = guard.ok_or("省略 guard に含意変換を作っている")?;
        let (body_expression, bindings, body_value) = self.evaluation(graph, body)?;
        let (guard_expression, _, guard_value) = self.evaluation(graph, guard)?;
        let guard_value = graph.boolean(guard_value)?;
        if guard_value == Some(true) {
            return Err("既知 true guard の適用は元 body を評価する".into());
        }
        self.transform_scope(graph, graph.get(expression)?, expression.0)?;
        let violation = self.transform_operands(graph, expression, TransformOp::Not, bindings)?[0];
        let conjunction = self.transform_operands(graph, violation, TransformOp::And, bindings)?;
        if conjunction[0] != guard_expression {
            return Err("含意の guard が元出現と違う".into());
        }
        let negated_body =
            self.transform_operands(graph, conjunction[1], TransformOp::Not, bindings)?;
        if negated_body != [body_expression] {
            return Err("含意の body が元出現と違う".into());
        }
        let value = conditional_bool(guard_value, graph.boolean(body_value)?);
        self.tick()?;
        Ok(value)
    }
    fn expression_span(&self, graph: &Graph, r: NodeRef) -> Result<(usize, usize), String> {
        match &graph.get(r)?.payload {
            Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) => Ok(*span),
            _ => Err("元式 span がない".into()),
        }
    }
    fn expression_bindings<'g>(
        &self,
        graph: &'g Graph,
        r: NodeRef,
    ) -> Result<&'g [Binding], String> {
        match &graph.get(r)?.payload {
            Some(Payload::Expression { bindings, .. } | Payload::Transform { bindings, .. }) => {
                Ok(bindings)
            }
            _ => Err("式束縛がない".into()),
        }
    }
    fn evaluation<'g>(
        &self,
        graph: &'g Graph,
        r: NodeRef,
    ) -> Result<(NodeRef, &'g [Binding], Option<NodeRef>), String> {
        match &graph.get(r)?.payload {
            Some(Payload::Evaluation {
                expression,
                bindings,
                value,
                ..
            }) => Ok((*expression, bindings, *value)),
            _ => Err("Evaluation でない".into()),
        }
    }
    fn check_name(
        &self,
        graph: &Graph,
        span: (usize, usize),
        bindings: &[Binding],
        name: &str,
        value: Option<NodeRef>,
        children: &[Option<NodeRef>],
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        if let Some((input, expected)) = self.iteration_argument(graph, span, name, bindings)? {
            if children.len() != 1
                || children[0] != self.evaluation(graph, input)?.2
                || value.map(|r| graph.scalar(r)).transpose()? != Some(&expected)
                || value.is_none_or(|r| graph.get(r).map_or(true, |node| node.arguments != [input]))
            {
                return Err("反復binder値・元位置/要素・domain辺が違う".into());
            }
        } else if let Some((input, expected)) =
            self.pattern_argument(graph, span, name, bindings)?
        {
            if children.len() != 1
                || children[0] != self.evaluation(graph, input)?.2
                || value.map(|r| graph.scalar(r)).transpose()? != Some(&expected)
                || value.is_none_or(|r| graph.get(r).map_or(true, |n| n.arguments != [input]))
            {
                return Err("pattern binderの元path・値・実scrutinee辺が違う".into());
            }
        } else if let Some(input) = self.lexical_argument(graph, span, name, bindings)? {
            if children.len() != 1
                || value != self.evaluation(graph, input)?.2
                || value != children[0]
            {
                return Err("lexical 名が実右辺の値を参照していない".into());
            }
        } else if let Some(argument) = self.call_parameter(graph, name)? {
            if children.len() != 1
                || value != self.evaluation(graph, argument)?.2
                || value != children[0]
            {
                return Err("callee parameterが実引数値を保持しない".into());
            }
        } else {
            self.check_parameter(graph, bindings, name, value)?;
        }
        self.tick()?;
        Ok(())
    }
    fn check_parameter(
        &self,
        graph: &Graph,
        bindings: &[Binding],
        name: &str,
        value: Option<NodeRef>,
    ) -> Result<(), ValidationFailure> {
        let mut binding = None;
        for b in bindings {
            self.tick()?;
            if b.name == name {
                binding = Some(b);
            }
            self.tick()?;
        }
        let b = binding.ok_or("元 parameter 束縛がない")?;
        graph.expect(b.value, &NodeType::Value(b.ty.clone()))?;
        if value != Some(b.value) {
            return Err("parameter の値 Ref 不一致".into());
        }
        Ok(())
    }
    fn check_field(
        &self,
        graph: &Graph,
        base: Option<NodeRef>,
        name: &str,
        value: Option<NodeRef>,
    ) -> Result<(), ValidationFailure> {
        let base = base.ok_or("field の base が未確定")?;
        let Scalar::Subject {
            snapshot,
            subject,
            entity,
        } = graph.scalar(base)?
        else {
            return Err("field の base 型不一致".into());
        };
        let field = self.field(snapshot, subject, &format!("{entity}.{name}"))?;
        match (&field.slot, value) {
            (Slot::Missing, None) => Ok(()),
            (
                Slot::Known {
                    value: expected, ..
                },
                Some(actual),
            ) if scalar_from(expected, &field.ty, self.inputs.law(), &self.control)?.as_ref()
                == Some(graph.scalar(actual)?)
                && graph.get(actual)?.arguments == [base] =>
            {
                Ok(())
            }
            _ => Err("field の元 slot と導出値が合わない".into()),
        }
    }
    fn recheck_evaluation(&self, graph: &Graph, root: NodeRef) -> Result<(), ValidationFailure> {
        self.validation_session(|| {
            self.tick()?;
            let key = (graph.context_at(root.0), root.0);
            if self.cache.borrow().rechecked.contains(&key) {
                return Ok(());
            }
            self.recheck_evaluation_uncached(graph, root)?;
            self.cache.borrow_mut().rechecked.insert(key);
            Ok(())
        })
    }
    fn recheck_evaluation_uncached(
        &self,
        graph: &Graph,
        root: NodeRef,
    ) -> Result<(), ValidationFailure> {
        let mut pending = vec![root];
        let mut checked = Vec::new();
        while let Some(reference) = pending.pop() {
            self.tick()?;
            let key = (graph.context_at(reference.0), reference.0);
            if self.cache.borrow().rechecked.contains(&key) {
                continue;
            }
            checked.push(key);
            let node = graph.get(reference)?;
            // aggregate の適用検査へ入る前に、子・適用依存が既出であることを確かめる。
            for argument in &node.arguments {
                self.tick()?;
                if argument.0 >= reference.0 {
                    return Err("再検査する評価の引数が既出でない".into());
                }
                self.tick()?;
            }
            let Some(Payload::Evaluation {
                expression,
                bindings,
                parts,
                value,
                ..
            }) = &node.payload
            else {
                return Err("再検査対象が Evaluation でない".into());
            };
            // Bool Scalar は子 Evaluation を使う。値の再検査へ入る前に payload の
            // 全ての計算辺も既出と確認し、未来の Scalar を経由する循環を拒否する。
            for dependency in std::iter::once(*expression)
                .chain(*value)
                .chain(bindings.iter().map(|binding| binding.value))
            {
                self.tick()?;
                if dependency.0 >= reference.0 {
                    return Err("再検査する評価 payload の参照が既出でない".into());
                }
                graph.get(dependency)?;
                self.tick()?;
            }
            for part in parts {
                self.tick()?;
                for dependency in part
                    .value
                    .iter()
                    .chain(&part.residual)
                    .chain(&part.children)
                {
                    self.tick()?;
                    if dependency.0 >= reference.0 {
                        return Err("再検査する評価 part の参照が既出でない".into());
                    }
                    graph.get(*dependency)?;
                    self.tick()?;
                }
                self.tick()?;
            }
            self.validate_at(graph, node, reference.0)?;
            self.validate_at(graph, graph.get(*expression)?, expression.0)?;
            if let Some(&instance) = node.arguments.first()
                && self.family_template(graph, instance)?
            {
                continue;
            }

            let mut support = Vec::new();
            if let Some(value) = value {
                self.validate_at(graph, graph.get(*value)?, value.0)?;
                support.extend(graph.get(*value)?.support.iter().cloned());
            }
            for part in parts {
                self.tick()?;
                for &child in &part.children {
                    self.tick()?;
                    if child.0 >= reference.0 {
                        return Err("再検査する子評価が既出でない".into());
                    }
                    pending.push(child);
                    support.extend(graph.get(child)?.support.iter().cloned());
                    self.tick()?;
                }
                self.tick()?;
            }
            support.sort();
            support.dedup();
            if node.support != support {
                return Err("評価の支持が元値・子評価に合わない".into());
            }
            self.tick()?;
        }
        self.cache.borrow_mut().rechecked.extend(checked);
        Ok(())
    }
    // LawInstance の適用根拠を元 guard/body と同じ束縛で照合する。
    fn application(
        &self,
        graph: &Graph,
        instance: &Node,
    ) -> Result<(NodeRef, Option<NodeRef>), ValidationFailure> {
        let Some(Payload::LawInstance {
            name,
            body,
            guard,
            bindings,
            ..
        }) = &instance.payload
        else {
            return Err("LawInstance がない".into());
        };
        let declaration = self
            .inputs
            .law()
            .declarations
            .get(name)
            .ok_or("適用の Law 宣言がない")?;
        let crate::law::model::Signature::Law {
            body: source_body,
            guard: source_guard,
            ..
        } = &declaration.signature
        else {
            return Err("適用対象が Law でない".into());
        };
        self.source_matches(graph, *body, *source_body)?;
        match (guard, source_guard) {
            (Some(expression), Some(id)) => self.source_matches(graph, *expression, *id)?,
            (None, None) => {}
            _ => return Err("適用 guard の元宣言不一致".into()),
        }
        let count = 1 + usize::from(guard.is_some());
        if instance.arguments.len() != count + bindings.len() {
            return Err("LawInstance の適用引数数が違う".into());
        }
        let body_evaluation = instance.arguments[0];
        let (expression, body_bindings, _) = self.evaluation(graph, body_evaluation)?;
        if expression != *body
            || body_bindings != bindings
            || self.expression_bindings(graph, expression)? != bindings
        {
            return Err("LawInstance の元 body 評価・束縛不一致".into());
        }
        self.recheck_evaluation(graph, body_evaluation)?;
        let guard_evaluation = if let Some(guard) = guard {
            let reference = instance.arguments[1];
            let (expression, guard_bindings, value) = self.evaluation(graph, reference)?;
            if expression != *guard
                || guard_bindings != bindings
                || self.expression_bindings(graph, expression)? != bindings
            {
                return Err("guard 評価の元出現・束縛不一致".into());
            }
            graph.boolean(value)?;
            self.recheck_evaluation(graph, reference)?;
            Some(reference)
        } else {
            None
        };
        for (binding, &argument) in bindings.iter().zip(&instance.arguments[count..]) {
            self.tick()?;
            if binding.value != argument {
                return Err("適用根拠の parameter identity 不一致".into());
            }
            self.tick()?;
        }
        let (support, scope) =
            self.application_context(graph, body_evaluation, guard_evaluation)?;
        if instance.support != support || instance.scope != scope {
            return Err("LawInstance の適用支持・範囲不一致".into());
        }
        Ok((body_evaluation, guard_evaluation))
    }
    fn application_context(
        &self,
        graph: &Graph,
        body: NodeRef,
        guard: Option<NodeRef>,
    ) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
        let mut support = graph.get(body)?.support.clone();
        let mut scope = graph.get(body)?.scope.clone();
        if let Some(guard) = guard {
            self.tick()?;
            support.extend(graph.get(guard)?.support.iter().cloned());
            scope.merge(&graph.get(guard)?.scope);
            self.tick()?;
        }
        support.sort();
        support.dedup();
        Ok((support, scope))
    }
    fn application_at(
        &self,
        graph: &Graph,
        instance: NodeRef,
    ) -> Result<(NodeRef, Option<NodeRef>), ValidationFailure> {
        let node = graph.get(instance)?;
        for reference in &node.arguments {
            self.tick()?;
            if reference.0 >= instance.0 {
                return Err("LawInstanceの適用引数が既出でない".into());
            }
            self.tick()?;
        }
        self.application(graph, node)
    }
    fn validate_law_evaluation(
        &self,
        graph: &Graph,
        node: &Node,
        instance: NodeRef,
    ) -> Result<(), ValidationFailure> {
        let (body, guard) = self.application_at(graph, instance)?;
        let guard = guard.ok_or("省略 guard に適用集約評価を作っている")?;
        if node.arguments != [instance, body, guard] {
            return Err("適用評価の元引数不一致".into());
        }
        let Some(Payload::Evaluation {
            expression,
            bindings,
            parts,
            value,
            applicability,
        }) = &node.payload
        else {
            return Err("適用評価でない".into());
        };
        let (body_expression, body_bindings, body_value) = self.evaluation(graph, body)?;
        let guard_value = graph.boolean(self.evaluation(graph, guard)?.2)?;
        let expected_applicability = match guard_value {
            Some(true) => "applicable",
            Some(false) => "not_applicable",
            None => "undetermined",
        };
        if bindings != body_bindings || *applicability != expected_applicability || parts.len() != 2
        {
            return Err("適用評価の元束縛・適用表示不一致".into());
        }
        if guard_value == Some(true) {
            if *expression != body_expression || *value != body_value {
                return Err("既知 true guard の元 body 評価不一致".into());
            }
        } else {
            let expected = self.conditional_value(graph, instance, *expression)?;
            if graph.boolean(*value)? != expected {
                return Err("条件付き Law 評価が全補完での含意値と違う".into());
            }
            if let Some(value) = value {
                let scalar = graph.get(*value)?;
                if !matches!(&scalar.rule, Rule::Construction("evaluation"))
                    || scalar.arguments != [instance, *expression]
                {
                    return Err("条件付き Law 値が当該の元式・適用から導出されていない".into());
                }
                self.validate_at(graph, scalar, value.0)?;
            }
        }
        for (part, evaluation) in parts.iter().zip([guard, body]) {
            self.tick()?;
            let (expression, _, value) = self.evaluation(graph, evaluation)?;
            let Some(Payload::Evaluation {
                parts: original, ..
            }) = &graph.get(evaluation)?.payload
            else {
                unreachable!()
            };
            if part.location
                != (Location::Law {
                    span: self.expression_span(graph, expression)?,
                })
                || part.value != value
                || part.residual != original.last().ok_or("元評価 part がない")?.residual
                || part.children != [evaluation]
            {
                return Err("適用評価 part の出現・値・子評価不一致".into());
            }
            self.tick()?;
        }
        let (support, scope) = self.application_context(graph, body, Some(guard))?;
        if node.support != support || node.scope != scope {
            return Err("適用評価の支持・範囲不一致".into());
        }
        Ok(())
    }
    fn instance_evaluation(
        &self,
        graph: &Graph,
        instance: NodeRef,
        evaluation: NodeRef,
    ) -> Result<NodeRef, ValidationFailure> {
        let (body, guard) = self.application_at(graph, instance)?;
        if guard.is_some() {
            self.validate_law_evaluation(graph, graph.get(evaluation)?, instance)?;
        } else if evaluation != body {
            return Err("省略 guard の元 body 評価不一致".into());
        }
        Ok(body)
    }
    fn evidence_operands(
        &self,
        graph: &Graph,
        node: &Node,
        instance: NodeRef,
    ) -> Result<(NodeRef, NodeRef, NodeRef), ValidationFailure> {
        if node.arguments.len() != 2 || node.arguments[0] != instance {
            return Err("証拠の構成入力不一致".into());
        }
        let evaluation = node.arguments[1];
        let body = self.instance_evaluation(graph, instance, evaluation)?;
        let (expression, _, value) = self.evaluation(graph, body)?;
        let span = self.expression_span(graph, expression)?;
        let expr =
            &self.inputs.law().exprs[*self.expressions.get(&span).ok_or("証拠の元 AST がない")?];
        let (law_expression, _, law_value) = self.evaluation(graph, evaluation)?;
        let conditional = matches!(
            &graph.get(law_expression)?.payload,
            Some(Payload::Transform { .. })
        );
        if !conditional && matches!(expr.kind, ExprKind::Binary { op, .. } if is_comparison(op)) {
            let Some(Payload::Evaluation { parts, .. }) = &graph.get(body)?.payload else {
                unreachable!()
            };
            if parts[0].children.len() != 2 {
                return Err("比較証拠の子評価数".into());
            }
            let (_, _, left) = self.evaluation(graph, parts[0].children[0])?;
            let (_, _, right) = self.evaluation(graph, parts[0].children[1])?;
            Ok((
                evaluation,
                left.ok_or("左辺が未確定")?,
                right.ok_or("右辺が未確定")?,
            ))
        } else {
            let left = if conditional { law_value } else { value }.ok_or("Bool Law が未確定")?;
            let supplied_right = match &node.payload {
                Some(Payload::Counterexample { right, .. }) => *right,
                Some(Payload::EvaluationEvidence { rhs, .. }) => *rhs,
                _ => return Err("証拠 payload の種類".into()),
            };
            if graph.scalar(supplied_right)? != &Scalar::Bool(true)
                || graph.get(supplied_right)?.arguments != [instance]
            {
                return Err("Bool 証拠の true 要求が違う".into());
            }
            let (body, guard) = self.application_at(graph, instance)?;
            let expected = self.application_context(graph, body, guard)?.1;
            if graph.get(supplied_right)?.scope != expected {
                return Err("固定true Scalarの範囲が元Law適用と違う".into());
            }
            Ok((evaluation, left, supplied_right))
        }
    }
    fn source_matches(&self, graph: &Graph, r: NodeRef, id: usize) -> Result<(), String> {
        match &graph.get(r)?.payload {
            Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) if *span == self.inputs.law().exprs[id].span => Ok(()),
            _ => Err("元式との出現不一致".into()),
        }
    }
    fn validate_type_binder_evaluation(
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
        let span = self.expression_span(graph, *expression)?;
        let Some(name) = self.find_name_token(span)? else {
            return Ok(false);
        };
        let Some((domain, expected)) = self.type_iteration_argument(graph, span, name, bindings)?
        else {
            return Ok(false);
        };
        let value = value.ok_or("型binder Evalの値がない")?;
        if expression.0 >= limit
            || value.0 >= limit
            || domain.0 >= limit
            || graph.context_at(expression.0) != self.current_context(graph)
            || graph.context_at(value.0) != self.current_context(graph)
            || self.expression_bindings(graph, *expression)? != bindings
            || parts.len() != 1
            || parts[0].location != (Location::Law { span })
            || parts[0].value != Some(value)
            || !parts[0].children.is_empty()
            || parts[0].residual.is_some()
            || *applicability != "applicable"
            || node.ty != NodeType::Evaluation(expected.ty())
            || node.arguments != [*expression, value]
            || graph.scalar(value)? != &expected
            || graph.get(value)?.arguments != [domain]
            || !matches!(&graph.get(value)?.rule,Rule::Input {kind:"law",location:Location::Law {span:actual}} if *actual==span)
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
        {
            return Err("型binder Evaluationの元出現/値/Domain/Contextが違う".into());
        }
        self.validate_at(graph, graph.get(*expression)?, expression.0)?;
        self.validate_at(graph, graph.get(value)?, value.0)?;
        let analysis = self.analyze_source(graph, span, bindings)?;
        if node.scope != analysis.scope
            || node.support != analysis.support
            || analysis.known_value.as_ref() != Some(&expected)
        {
            return Err("型binder Evaluationの元Scope/支持が違う".into());
        }
        Ok(true)
    }
    fn quant_input(
        &self,
        graph: &Graph,
        source: NodeRef,
        input: Option<NodeRef>,
        limit: usize,
    ) -> Result<(quantifier::Spec<'_>, super::finite::Enumeration), ValidationFailure> {
        if source.0 >= limit
            || input.is_some_and(|input| input.0 >= limit)
            || graph.context_at(source.0) != self.current_context(graph)
            || input.is_some_and(|input| graph.context_at(input.0) != self.current_context(graph))
        {
            return Err("量化元Source/collectionの既出性・Contextが違う".into());
        }
        let id = *self
            .expressions
            .get(&self.expression_span(graph, source)?)
            .ok_or("量化元ASTがない")?;
        let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
        self.validate_at(graph, graph.get(source)?, source.0)?;
        let Some(input) = input else {
            if spec.domain.is_some() {
                return Err("In量化のcollection辺がない".into());
            }
            let values = self.finite_values(&spec.element, &mut |_, _| {})?;
            return Ok((spec, values));
        };
        self.recheck_evaluation(graph, input)?;
        let (actual, bindings, value) = self.evaluation(graph, input)?;
        self.source_matches(
            graph,
            actual,
            spec.domain.ok_or("型量化にcollection元式を付けた")?,
        )?;
        if self.expression_bindings(graph, source)? != bindings {
            return Err("量化collectionの宣言束縛が違う".into());
        }
        let items = match value.map(|r| graph.scalar(r)).transpose()? {
            Some(Scalar::List { element, items } | Scalar::Set { element, items })
                if *element == spec.element =>
            {
                items
            }
            _ => return Err("量化の既知collection/typeがない".into()),
        };
        let Scalar::Set { ref items, .. } = data::set(spec.element.clone(), items, &self.control)?
        else {
            unreachable!()
        };
        Ok((
            spec,
            super::finite::Enumeration {
                values: items.clone(),
                scope: graph.get(input)?.scope.clone(),
                support: graph.get(input)?.support.clone(),
            },
        ))
    }
    fn domain_member(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        if !(1..=2).contains(&node.arguments.len())
            || !matches!(&node.rule, Rule::Construction("domain"))
        {
            return Err("Domain要素の元辺が違う".into());
        }
        let (spec, enumeration) = self.quant_input(
            graph,
            node.arguments[0],
            node.arguments.get(1).copied(),
            limit,
        )?;
        let Some(Payload::Scalar(value)) = &node.payload else {
            return Err("Domain要素が通常値でない".into());
        };
        let input = graph.get(*node.arguments.get(1).unwrap_or(&node.arguments[0]))?;
        if value.ty() != spec.element
            || !data::contains(&enumeration.values, value, &self.control)?
            || node.support != enumeration.support
            || node.scope != input.scope
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
        {
            return Err("Domain要素が元collection/型/支持/Scopeと違う".into());
        }
        Ok(())
    }
    fn validate_domain(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        let Some(Payload::Domain { ty, elements }) = &node.payload else {
            return Err("Domain payloadがない".into());
        };
        let source = *node.arguments.first().ok_or("Domainの元Sourceがない")?;
        let spec = quantifier::spec(
            self.inputs.law(),
            *self
                .expressions
                .get(&self.expression_span(graph, source)?)
                .ok_or("Domain元ASTがない")?,
            &self.control,
        )?;
        let offset = 1 + usize::from(spec.domain.is_some());
        if node.ty != NodeType::Domain
            || !matches!(&node.rule, Rule::Construction("domain"))
            || node.arguments.len() != offset + elements.len()
            || node.arguments[offset..] != *elements
        {
            return Err("Domainの型/規則/元辺が違う".into());
        }
        let (spec, enumeration) = self.quant_input(
            graph,
            source,
            if offset == 2 {
                node.arguments.get(1).copied()
            } else {
                None
            },
            limit,
        )?;
        if *ty != spec.element || elements.len() != enumeration.values.len() {
            return Err("Domainの元型/全要素数が違う".into());
        }
        let mut seen = Vec::new();
        for reference in elements {
            #[cfg(test)]
            if spec.domain.is_none() {
                data::observe_actual(
                    spec.span,
                    self.current_context(graph),
                    "ref_recheck",
                    seen.len(),
                );
            }
            self.tick()?;
            if reference.0 >= limit || graph.context_at(reference.0) != self.current_context(graph)
            {
                return Err("Domain要素の既出Contextが違う".into());
            }
            let member = graph.get(*reference)?;
            self.validate_at(graph, member, reference.0)?;
            if member.arguments != node.arguments[..offset] {
                return Err("Domain要素が別collection出現に属する".into());
            }
            let value = graph.scalar(*reference)?;
            if !data::contains(&enumeration.values, value, &self.control)?
                || data::contains(&seen, value, &self.control)?
            {
                return Err("Domain要素の漏れ/重複/別値".into());
            }
            seen.push(value.clone());
        }
        let input = graph.get(node.arguments[if offset == 2 { 1 } else { 0 }])?;
        let mut scope = input.scope.clone();
        scope.add_quantifier(spec.descriptor(None, Some(self.current_context(graph))));
        scope.order_quantifiers_like(&graph.get(node.arguments[0])?.scope);
        if node.scope != scope
            || node.support != enumeration.support
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
        {
            return Err("DomainのScope/支持/証拠が違う".into());
        }
        Ok(())
    }
    fn quant_parts(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
        claimed: &Scope,
        limit: usize,
    ) -> Result<(SourceAnalysis, Option<NodeRef>), ValidationFailure> {
        let input = *children.first().ok_or("量化collection辺がない")?;
        if source.0 >= limit
            || input.0 >= limit
            || graph.context_at(source.0) != self.current_context(graph)
            || graph.context_at(input.0) != self.current_context(graph)
        {
            return Err("量化元の既出Contextが違う".into());
        }
        let span = self.expression_span(graph, source)?;
        let id = *self.expressions.get(&span).ok_or("量化ASTがない")?;
        let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
        self.validate_at(graph, graph.get(source)?, source.0)?;
        let (bindings, known) = if let Some(domain) = spec.domain {
            self.recheck_evaluation(graph, input)?;
            let (expression, bindings, value) = self.evaluation(graph, input)?;
            self.source_matches(graph, expression, domain)?;
            (bindings, value.is_some())
        } else {
            self.validate_at(graph, graph.get(input)?, input.0)?;
            (self.expression_bindings(graph, source)?, true)
        };
        if self.expression_bindings(graph, source)? != bindings {
            return Err("量化元束縛が違う".into());
        }
        let mut own = claimed
            .quantifiers
            .iter()
            .filter(|q| q.occurrence == span && q.context == Some(self.current_context(graph)));
        let descriptor = own.next().ok_or("量化Scopeがない")?;
        if own.next().is_some()
            || *descriptor != spec.descriptor(descriptor.domain, Some(self.current_context(graph)))
        {
            return Err("量化Scopeのkind/name/type/元出現が違う".into());
        }
        let mut scope = graph.get(input)?.scope.clone();
        scope.add_quantifier(descriptor.clone());
        scope.order_quantifiers_like(&graph.get(source)?.scope);
        let mut support = graph.get(input)?.support.clone();
        let mut results = Vec::new();
        let mut seen = Vec::new();
        let finite = descriptor.domain;
        match known {
            false => {
                if finite.is_some() || children.len() != 1 {
                    return Err("未知collectionに域/instanceがある".into());
                }
            }
            true => {
                let domain = finite.ok_or("既知量化に有限Domainがない")?;
                if domain.0 >= limit || graph.context_at(domain.0) != self.current_context(graph) {
                    return Err("量化Domainの既出Contextが違う".into());
                }
                self.validate_at(graph, graph.get(domain)?, domain.0)?;
                if if spec.domain.is_some() {
                    graph.get(domain)?.arguments.get(..2) != Some([source, input].as_slice())
                } else {
                    domain != input || graph.get(domain)?.arguments.first() != Some(&source)
                } {
                    return Err("量化Domainが別元collectionに属する".into());
                }
                let Some(Payload::Domain { elements, .. }) = &graph.get(domain)?.payload else {
                    return Err("量化域が有限でない".into());
                };
                if children.len() != 1 + elements.len() {
                    return Err("量化instance全coverageの件数が違う".into());
                }
                for body in &children[1..] {
                    self.tick()?;
                    if body.0 >= limit {
                        return Err("量化bodyが未来を指す".into());
                    }
                    let context = graph.context_at(body.0);
                    let index = context.iteration.ok_or("量化bodyにbinderContextがない")?;
                    let record = graph.iterations.get(index).ok_or("量化binder元がない")?;
                    if record.caller != self.current_context(graph)
                        || record.source != source
                        || record.domain != input
                        || record.finite != finite
                        || context.instance != record.caller.instance
                        || context.request != record.caller.request
                        || context.frame != record.caller.frame
                    {
                        return Err("量化bodyの元域/binder/親Contextが違う".into());
                    }
                    let (_, member, _) = self.iteration_input(graph, index)?;
                    if !matches!(record.member, super::call::Member::SetElement(_))
                        || data::contains(&seen, &member, &self.control)?
                        || !elements
                            .iter()
                            .any(|r| graph.scalar(*r).is_ok_and(|v| v == &member))
                    {
                        return Err("量化binderの漏れ/重複/別要素".into());
                    }
                    seen.push(member);
                    self.recheck_evaluation(graph, *body)?;
                    let (expression, actual, value) = self.evaluation(graph, *body)?;
                    self.source_matches(graph, expression, spec.body)?;
                    if actual != bindings {
                        return Err("量化bodyの元宣言束縛が違う".into());
                    }
                    results.push(graph.boolean(value)?);
                    scope.merge(&graph.get(*body)?.scope);
                    support.extend(graph.get(*body)?.support.iter().cloned());
                }
            }
        }
        support.sort();
        support.dedup();
        let computed = if known {
            quantifier::reduce(spec.kind, &results, &self.control)?.map(Scalar::Bool)
        } else {
            None
        };
        let analysis = self.analyze_source(graph, span, bindings)?;
        if analysis.known_value != computed
            || analysis.support != support
            || !analysis.scope.source_compatible(&scope)
            || !graph.get(source)?.scope.source_compatible(&scope)
        {
            return Err("量化の元AST/Bool集約/支持/Scopeが違う".into());
        }
        Ok((
            SourceAnalysis {
                scalar_scope: computed.as_ref().map(|_| scope.clone()),
                scope,
                known_value: computed,
                support,
                missing: None,
            },
            finite,
        ))
    }
    fn quant_scalar(
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
            return Err("量化Scalarの元規則がない".into());
        };
        let mut descriptors =
            node.scope.quantifiers.iter().filter(|q| {
                q.occurrence == *span && q.context == Some(self.current_context(graph))
            });
        let descriptor = descriptors
            .next()
            .ok_or("量化Scalarに自身の量化Scopeがない")?;
        if descriptors.next().is_some() {
            return Err("量化Scalarに自身の域が複数ある".into());
        }
        let finite = descriptor.domain.ok_or("量化Scalarの実Domainがない")?;
        let source = *graph
            .get(finite)?
            .arguments
            .first()
            .ok_or("量化ScalarのDomain元Sourceがない")?;
        if self.expression_span(graph, source)? != *span {
            return Err("量化Scalarが別元出現のDomainを指す".into());
        }
        let (analysis, domain) =
            self.quant_parts(graph, source, &node.arguments, &node.scope, limit)?;
        if !matches!(&node.payload,Some(Payload::Scalar(value)) if analysis.known_value.as_ref()==Some(value))
            || node.scope != analysis.scope
            || node.support != analysis.support
        {
            return Err("量化Scalarの値/元Scope/支持が違う".into());
        }
        self.quant_evidence(
            graph,
            source,
            domain,
            &node.arguments[1..],
            &analysis,
            &node.evidence,
        )?;
        Ok(analysis)
    }
    fn validate_quant_evaluation(
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
        let span = self.expression_span(graph, *expression)?;
        let Some(id) = self.expressions.get(&span) else {
            return Ok(false);
        };
        if !matches!(self.inputs.law().exprs[*id].kind, ExprKind::Quant { .. }) {
            return Ok(false);
        }
        if parts.len() != 1
            || parts[0].location != (Location::Law { span })
            || parts[0].value != *value
            || parts[0].residual.is_some()
            || *applicability != "applicable"
            || self.expression_bindings(graph, *expression)? != bindings
        {
            return Err("量化Evaluationの元part/束縛が違う".into());
        }
        let spec = quantifier::spec(self.inputs.law(), *id, &self.control)?;
        let mut children = parts[0].children.clone();
        if spec.domain.is_none() {
            let domain = node
                .scope
                .quantifiers
                .iter()
                .find(|q| q.occurrence == span && q.context == Some(self.current_context(graph)))
                .and_then(|q| q.domain)
                .ok_or("型量化EvalのDomainがない")?;
            children.insert(0, domain);
        }
        let (analysis, domain) =
            self.quant_parts(graph, *expression, &children, &node.scope, limit)?;
        if node.scope != analysis.scope
            || node.support != analysis.support
            || value.map(|r| graph.scalar(r)).transpose() != Ok(analysis.known_value.as_ref())
        {
            return Err("量化Evaluationの値/Scope/支持が違う".into());
        }
        let expected: Vec<_> = std::iter::once(*expression)
            .chain(parts[0].children.iter().copied())
            .chain(*value)
            .collect();
        if node.arguments != expected {
            return Err("量化Evaluationの元依存辺が違う".into());
        }
        if let Some(value) = value {
            if value.0 >= limit
                || graph.context_at(value.0) != self.current_context(graph)
                || graph.get(*value)?.arguments != children
            {
                return Err("量化結果のproducerが違う".into());
            }
            self.validate_at(graph, graph.get(*value)?, value.0)?;
            if graph.get(*value)?.evidence != node.evidence {
                return Err("量化Scalar/Evaluationの証拠が違う".into());
            }
        }
        self.quant_evidence(
            graph,
            *expression,
            domain,
            &children[1..],
            &analysis,
            &node.evidence,
        )?;
        let mut reasons = Vec::new();
        for child in &parts[0].children {
            reasons.extend(graph.get(*child)?.reasons.iter().cloned());
        }
        sort_reasons(&mut reasons);
        if node.reasons.len() != reasons.len()
            || node
                .reasons
                .iter()
                .zip(&reasons)
                .any(|(a, b)| a.wire() != b.wire())
        {
            return Err("量化が元missing/理由を捨てている".into());
        }
        Ok(true)
    }
    fn quant_evidence(
        &self,
        graph: &Graph,
        source: NodeRef,
        domain: Option<NodeRef>,
        bodies: &[NodeRef],
        analysis: &SourceAnalysis,
        evidence: &[NodeRef],
    ) -> Result<(), ValidationFailure> {
        let id = *self
            .expressions
            .get(&self.expression_span(graph, source)?)
            .ok_or("証拠量化ASTがない")?;
        let spec = quantifier::spec(self.inputs.law(), id, &self.control)?;
        let exhaustive = matches!(
            (&analysis.known_value, spec.kind),
            (Some(Scalar::Bool(true)), crate::law::ast::QuantKind::Forall)
                | (
                    Some(Scalar::Bool(false)),
                    crate::law::ast::QuantKind::Exists
                )
        );
        let mut full = false;
        let mut false_bodies = Vec::new();
        for reference in evidence {
            self.tick()?;
            self.validate_at(graph, graph.get(*reference)?, reference.0)?;
            match &graph.get(*reference)?.payload {
                Some(Payload::FiniteExhaustion {
                    domain: actual,
                    instances,
                    ..
                }) if Some(*actual) == domain
                    && instances.len() == bodies.len()
                    && instances.iter().all(|r| bodies.contains(r))
                    && graph.get(*reference)?.arguments.first() == Some(&source) =>
                {
                    if full {
                        return Err("全検査証拠が重複する".into());
                    }
                    full = true;
                }
                Some(Payload::Counterexample { .. })
                    if spec.kind == crate::law::ast::QuantKind::Forall
                        && graph.get(*reference)?.arguments.get(..2)
                            == domain.map(|d| [source, d]).as_ref().map(|a| a.as_slice()) =>
                {
                    let body = *graph
                        .get(*reference)?
                        .arguments
                        .get(2)
                        .ok_or("量化反例のbodyがない")?;
                    if !bodies.contains(&body) || false_bodies.contains(&body) {
                        return Err("量化反例が別body/重複である".into());
                    }
                    false_bodies.push(body);
                }
                _ => return Err("量化に別の証拠を添付している".into()),
            }
        }
        if full != exhaustive {
            return Err("全域判断に対応する全検査証拠がない/余分".into());
        }
        if spec.kind == crate::law::ast::QuantKind::Forall {
            for body in bodies {
                self.tick()?;
                if graph.boolean(self.evaluation(graph, *body)?.2)? == Some(false)
                    && !false_bodies.contains(body)
                {
                    return Err("既知falseinstanceの反例を落としている".into());
                }
            }
        }
        Ok(())
    }
    pub(super) fn quant_bindings(
        &self,
        graph: &Graph,
        context: super::call::Context,
    ) -> Result<Vec<Binding>, ValidationFailure> {
        let mut records = Vec::new();
        let mut current = context.iteration;
        while let Some(index) = current {
            self.tick()?;
            let record = graph.iterations.get(index).ok_or("反例binder元がない")?;
            if record.caller.iteration.is_some_and(|p| p >= index) {
                return Err("反例binderの親が先行しない".into());
            }
            records.push(index);
            current = record.caller.iteration;
        }
        records.reverse();
        let first = *records.last().ok_or("量化反例に反復がない")?;
        let mut bindings = self
            .expression_bindings(graph, graph.iterations[first].source)?
            .to_vec();
        for index in records {
            self.tick()?;
            let record = &graph.iterations[index];
            if let Some(domain) = record.finite {
                let spec = quantifier::spec(
                    self.inputs.law(),
                    *self
                        .expressions
                        .get(&self.expression_span(graph, record.source)?)
                        .ok_or("binder量化ASTがない")?,
                    &self.control,
                )?;
                let Some(Payload::Domain { elements, .. }) = &graph.get(domain)?.payload else {
                    return Err("binderDomainがない".into());
                };
                let (_, member, _) = self.iteration_input(graph, index)?;
                let value = *elements
                    .iter()
                    .find(|r| graph.scalar(**r).is_ok_and(|v| v == &member))
                    .ok_or("反例binder要素がDomainにない")?;
                bindings.push(Binding {
                    name: spec.name.into(),
                    ty: spec.element,
                    value,
                });
            }
        }
        Ok(bindings)
    }
    fn quant_counter_parts(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(Vec<Binding>, NodeRef), ValidationFailure> {
        let [source, domain, body] = node.arguments.as_slice() else {
            return Err("量化反例の元依存辺数が違う".into());
        };
        if node.arguments.iter().any(|r| r.0 >= limit) {
            return Err("量化反例が未来を参照する".into());
        }
        self.validate_at(graph, graph.get(*domain)?, domain.0)?;
        self.recheck_evaluation(graph, *body)?;
        let context = graph.context_at(body.0);
        let record = graph
            .iterations
            .get(context.iteration.ok_or("量化反例のbinderContextがない")?)
            .ok_or("量化反例の反復がない")?;
        if self.current_context(graph) != context
            || record.source != *source
            || record.finite != Some(*domain)
            || if record.domain == *domain {
                graph.get(*domain)?.arguments.first() != Some(source)
            } else {
                graph.get(*domain)?.arguments.get(..2) != Some([*source, record.domain].as_slice())
            }
        {
            return Err("量化反例が元Domain/body/binderに属さない".into());
        }
        let spec = quantifier::spec(
            self.inputs.law(),
            *self
                .expressions
                .get(&self.expression_span(graph, *source)?)
                .ok_or("反例量化ASTがない")?,
            &self.control,
        )?;
        if spec.kind != crate::law::ast::QuantKind::Forall {
            return Err("forall以外のfalsebodyを全称反例にしている".into());
        }
        let (expression, _, value) = self.evaluation(graph, *body)?;
        self.source_matches(graph, expression, spec.body)?;
        let left = value.ok_or("未知bodyに反例がある")?;
        if graph.scalar(left)? != &Scalar::Bool(false) {
            return Err("量化反例のbodyがfalseでない".into());
        }
        Ok((self.quant_bindings(graph, context)?, left))
    }
    fn validate_quant_counter(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        if node.ty != NodeType::Evidence
            || !matches!(&node.rule, Rule::Construction("evidence"))
            || !node.evidence.is_empty()
            || node.judgment.is_some()
        {
            return Err("量化反例の型/規則/証拠が違う".into());
        }
        let (expected, left) = self.quant_counter_parts(graph, node, limit)?;
        let Some(Payload::Counterexample {
            bindings,
            left: actual,
            right,
            facts,
        }) = &node.payload
        else {
            return Err("量化反例payloadがない".into());
        };
        let body = graph.get(node.arguments[2])?;
        let mut support = graph.get(node.arguments[1])?.support.clone();
        support.extend(body.support.iter().cloned());
        support.sort();
        support.dedup();
        if bindings != &expected
            || *actual != left
            || graph.scalar(*right)? != &Scalar::Bool(true)
            || graph.get(*right)?.arguments != node.arguments
            || facts != &support
            || node.support != support
            || node.scope != body.scope
            || !node.reasons.is_empty()
        {
            return Err("量化反例の実binder/falsebody/要求/支持/Scopeが違う".into());
        }
        self.validate_at(graph, graph.get(*right)?, right.0)?;
        Ok(())
    }
    fn validate_finite_exhaustion(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<(), ValidationFailure> {
        if node.ty != NodeType::Evidence
            || !matches!(&node.rule, Rule::Construction("evidence"))
            || node.judgment.is_some()
        {
            return Err("全検査証拠の型/規則が違う".into());
        }
        let Some(Payload::FiniteExhaustion {
            domain,
            checked,
            instances,
        }) = &node.payload
        else {
            return Err("全検査payloadがない".into());
        };
        let source = *node.arguments.first().ok_or("全検査元Sourceがない")?;
        let spec = quantifier::spec(
            self.inputs.law(),
            *self
                .expressions
                .get(&self.expression_span(graph, source)?)
                .ok_or("全検査元量化がない")?,
            &self.control,
        )?;
        let input = if spec.domain.is_none() {
            *domain
        } else {
            *graph
                .get(*domain)?
                .arguments
                .get(1)
                .ok_or("全検査元域Evalがない")?
        };
        let children: Vec<_> = std::iter::once(input)
            .chain(instances.iter().copied())
            .collect();
        let (analysis, actual) = self.quant_parts(graph, source, &children, &node.scope, limit)?;
        let spec = quantifier::spec(
            self.inputs.law(),
            *self
                .expressions
                .get(&self.expression_span(graph, source)?)
                .ok_or("全検査元量化がない")?,
            &self.control,
        )?;
        if actual != Some(*domain)
            || *checked != instances.len()
            || node.arguments
                != std::iter::once(source)
                    .chain([*domain])
                    .chain(instances.iter().copied())
                    .collect::<Vec<_>>()
            || node.support != analysis.support
            || node.scope != analysis.scope
            || !node.evidence.is_empty()
            || !node.reasons.is_empty()
            || !matches!(
                (spec.kind, analysis.known_value),
                (crate::law::ast::QuantKind::Forall, Some(Scalar::Bool(true)))
                    | (
                        crate::law::ast::QuantKind::Exists,
                        Some(Scalar::Bool(false))
                    )
            )
        {
            return Err("全検査証拠の元域/coverage/body/件数/判断が違う".into());
        }
        Ok(())
    }
}
pub(crate) fn scalar_from(
    value: &Value,
    ty: &Type,
    law: &crate::law::CheckedLaw,
    control: &Control,
) -> Result<Option<Scalar>, ValidationFailure> {
    match value {
        Value::Bool(b) if ty == &Type::Bool => Ok(Some(Scalar::Bool(*b))),
        Value::Ref { snapshot, subject } => Ok(ty.ref_target().map(|entity| Scalar::Subject {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            entity: entity.into(),
        })),
        _ => data::from_input(value, ty, law, control),
    }
}
pub(crate) fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}
// 元の条件と両枝だけから全補完で固定する値を求める。未知をBoolへ補わない。
pub(crate) fn conditional_branch(
    condition: Option<&Scalar>,
    left: Option<&Scalar>,
    right: Option<&Scalar>,
    control: &Control,
) -> Result<Option<Scalar>, ValidationFailure> {
    control
        .clone()
        .checkpoint(Checkpoint::FiniteIteration)
        .map_err(ValidationFailure::Stop)?;
    let value = match condition {
        Some(Scalar::Bool(true)) => left.cloned(),
        Some(Scalar::Bool(false)) => right.cloned(),
        None => {
            let equal = if let Some((left, right)) = left.zip(right) {
                if left.ty() != right.ty() {
                    return Err("if の既知両枝の型が違う".into());
                }
                data::equal(left, right, control)?
            } else {
                false
            };
            if equal { left.cloned() } else { None }
        }
        _ => return Err("if の条件が Bool でない".into()),
    };
    control
        .clone()
        .checkpoint(Checkpoint::FiniteIteration)
        .map_err(ValidationFailure::Stop)?;
    Ok(value)
}
pub(crate) fn is_boolean_binary(op: BinOp) -> bool {
    matches!(op, BinOp::And | BinOp::Or | BinOp::Implies)
}
pub(crate) fn supports_binary(
    op: BinOp,
    input: &Type,
    control: &Control,
) -> Result<bool, ValidationFailure> {
    if matches!(op, BinOp::Eq | BinOp::Ne | BinOp::In) && data::primitive_type(input, control)? {
        return Ok(true);
    }
    if input == &Type::Bool {
        return Ok(matches!(op, BinOp::Eq | BinOp::Ne) || is_boolean_binary(op));
    }
    Ok(numeric::is_numeric_type(input, control)?
        && (matches!(
            op,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Eq | BinOp::Ne
        ) || matches!(input, Type::Z | Type::Q) && is_comparison(op)))
}
pub(crate) fn unary(
    op: UnOp,
    value: &Scalar,
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    match (op, value) {
        (UnOp::Not, Scalar::Bool(value)) => Ok(Scalar::Bool(!value)),
        _ => numeric::unary(op, value, control),
    }
}
/// 未知は通常値で埋めない。Bool の定数規則以外では両辺の既知値を要求する。
pub(crate) fn partial_binary(
    op: BinOp,
    left: Option<&Scalar>,
    right: Option<&Scalar>,
    control: &Control,
) -> Result<Option<Scalar>, ValidationFailure> {
    if !is_boolean_binary(op) {
        return left
            .zip(right)
            .map(|(left, right)| binary(op, left, right, control))
            .transpose();
    }
    let boolean = |value: &Scalar| match value {
        Scalar::Bool(value) => Ok(*value),
        _ => Err(ValidationFailure::from("Bool 論理演算の値が Bool でない")),
    };
    let left = left.map(boolean).transpose()?;
    let right = right.map(boolean).transpose()?;
    let value = match op {
        BinOp::And => match (left, right) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        },
        BinOp::Or => match (left, right) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        },
        BinOp::Implies => conditional_bool(left, right),
        _ => unreachable!("Bool 論理演算だけを選択済み"),
    };
    Ok(value.map(Scalar::Bool))
}
pub(crate) fn binary(
    op: BinOp,
    left: &Scalar,
    right: &Scalar,
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    if op == BinOp::In {
        let (element, items) = match right {
            Scalar::List { element, items } | Scalar::Set { element, items } => (element, items),
            _ => return Err("inの右辺がList/Setでない".into()),
        };
        if &left.ty() != element {
            return Err("in要素型が違う".into());
        };
        return Ok(Scalar::Bool(data::contains(items, left, control)?));
    }
    if matches!(op, BinOp::Eq | BinOp::Ne) {
        let equal = data::equal(left, right, control)?;
        return Ok(Scalar::Bool(if op == BinOp::Eq { equal } else { !equal }));
    }
    if let (Scalar::Bool(a), Scalar::Bool(b)) = (left, right) {
        let value = match op {
            BinOp::Eq => a == b,
            BinOp::Ne => a != b,
            BinOp::And => *a && *b,
            BinOp::Or => *a || *b,
            BinOp::Implies => !*a || *b,
            _ => return Err("未実装の Bool 演算".into()),
        };
        return Ok(Scalar::Bool(value));
    }
    numeric::binary(op, left, right, control)
}
