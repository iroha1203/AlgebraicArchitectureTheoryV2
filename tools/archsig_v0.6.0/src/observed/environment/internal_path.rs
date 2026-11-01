//! 元の内部arrowから、共通Atom carrier上の1段作用を再構成する。
use super::super::path_value::{PathValue, Step};
use super::*;
use crate::definition::model::PrimitiveSignature;
use crate::observed::environment::state::ScopedReplace;

pub(in crate::observed) struct PathResult {
    pub(in crate::observed) value: Option<Scalar>,
    pub(in crate::observed) scope: Scope,
    pub(in crate::observed) support: Vec<Fact>,
    pub(in crate::observed) missing: Vec<Fact>,
    pub(in crate::observed) failure: Option<(Scalar, Scalar)>,
}
// 参照へ至る構造を平坦なtoken列へし、深い値の比較・破棄も再帰させない。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Token {
    Open(String),
    Close,
    Quantity,
    Reference(String, String),
}
pub(super) type Shape = Vec<Token>;
impl Environment<'_> {
    pub(super) fn path_shape(
        &self,
        value: &Value,
        moving: Option<&BTreeMap<(String, String), (String, String)>>,
        references: &mut BTreeSet<Fact>,
    ) -> Result<Option<Shape>, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            if let Value::Ref { snapshot, subject } = value {
                self.indexes.subject(snapshot, subject)?;
                references.insert(Fact {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    field: None,
                    atom: None,
                });
                let point = moving
                    .and_then(|mapping| mapping.get(&(snapshot.clone(), subject.clone())))
                    .cloned()
                    .unwrap_or_else(|| (snapshot.clone(), subject.clone()));
                return Ok(Some(vec![Token::Reference(point.0.into(), point.1.into())]));
            }
            let (name, mut shapes) = match value {
                Value::Tuple(xs) | Value::List(xs) | Value::Set(xs) => {
                    let mut out = Vec::new();
                    for x in xs {
                        self.tick()?;
                        out.push(self.path_shape(x, moving, references)?)
                    }
                    (
                        match value {
                            Value::Tuple(_) => "tuple",
                            Value::List(_) => "list",
                            _ => "set",
                        }
                        .to_owned(),
                        out,
                    )
                }
                Value::Option(Some(x)) => {
                    ("some".into(), vec![self.path_shape(x, moving, references)?])
                }
                Value::Data { constructor, args } => {
                    let mut out = Vec::new();
                    for x in args {
                        self.tick()?;
                        out.push(self.path_shape(x, moving, references)?)
                    }
                    (format!("data:{constructor}"), out)
                }
                Value::Map(xs) => {
                    let mut out = Vec::new();
                    for (k, v) in xs {
                        self.tick()?;
                        let a = self.path_shape(k, moving, references)?;
                        let b = self.path_shape(v, moving, references)?;
                        out.push(if a.is_some() || b.is_some() {
                            let mut row = vec![Token::Open("row".into())];
                            for shape in [a, b] {
                                if let Some(shape) = shape {
                                    for token in shape {
                                        self.tick()?;
                                        row.push(token)
                                    }
                                } else {
                                    row.push(Token::Quantity)
                                }
                            }
                            row.push(Token::Close);
                            Some(row)
                        } else {
                            None
                        });
                    }
                    out.sort();
                    out.dedup();
                    ("map".into(), out)
                }
                _ => return Ok(None),
            };
            if shapes.iter().all(Option::is_none) {
                return Ok(None);
            }
            if matches!(value, Value::Set(_)) {
                shapes.sort();
                shapes.dedup();
            }
            let mut out = vec![Token::Open(name)];
            for shape in shapes {
                self.tick()?;
                if let Some(shape) = shape {
                    out.push(Token::Open("item".into()));
                    for token in shape {
                        self.tick()?;
                        out.push(token)
                    }
                    out.push(Token::Close)
                } else {
                    out.push(Token::Quantity)
                }
            }
            out.push(Token::Close);
            self.tick()?;
            Ok(Some(out))
        })
    }
    pub(super) fn path_shape_same(
        &self,
        a: &Option<Shape>,
        b: &Option<Shape>,
    ) -> Result<bool, ValidationFailure> {
        match (a, b) {
            (None, None) => Ok(true),
            (Some(a), Some(b)) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (x, y) in a.iter().zip(b) {
                    self.tick()?;
                    if x != y {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }
    pub(super) fn path_shape_text(
        &self,
        shape: &Option<Shape>,
    ) -> Result<String, ValidationFailure> {
        let mut out = String::new();
        if let Some(shape) = shape {
            for token in shape {
                self.tick()?;
                out.push_str(&format!("{token:?};"))
            }
        } else {
            out.push_str("quantity")
        };
        self.tick()?;
        Ok(out)
    }
    pub(super) fn path_reading(&self, id: usize) -> Result<&str, ValidationFailure> {
        let span = self.indexes.inputs.law().exprs()[id].span;
        let mut reading = None;
        for d in self.indexes.inputs.law().declarations().values() {
            self.tick()?;
            if d.span.0 <= span.0
                && span.1 <= d.span.1
                && reading.replace(d.reading.as_str()).is_some()
            {
                return Err("Pathの元宣言が一意でない".into());
            }
        }
        reading.ok_or_else(|| "Pathの元readingがない".into())
    }
    // 観測値がnone/空であっても、元型が参照を含み得るなら値依存を残す。
    fn path_reads_value(&self, ty: &Type) -> Result<bool, ValidationFailure> {
        let mut pending = vec![ty];
        let mut seen = BTreeSet::new();
        while let Some(ty) = pending.pop() {
            self.tick()?;
            match ty {
                Type::Ref(_) | Type::Owned(..) | Type::Path(..) => return Ok(true),
                Type::Tuple(items) => pending.extend(items),
                Type::List(item) | Type::Set(item) | Type::Option(item) => pending.push(item),
                Type::Map(a, b) => pending.extend([a.as_ref(), b.as_ref()]),
                Type::Data(name) if seen.insert(name.as_str()) => {
                    for constructor in data::constructors(self.indexes.inputs.law(), name)? {
                        self.tick()?;
                        pending.extend(&constructor.arguments);
                    }
                }
                _ => {}
            }
        }
        Ok(false)
    }
    // 型・slot・Atomの所在だけのlookupは、field値を候補記号へ加えない。
    fn path_structure_field(
        &self,
        owner: &Subject,
        name: &str,
    ) -> Result<&crate::archmap::Field, ValidationFailure> {
        self.tick()?;
        self.indexes
            .inputs
            .law()
            .resolved_names()
            .get(name)
            .and_then(|name| {
                self.indexes
                    .fields
                    .get(&(owner.snapshot.clone(), owner.id.clone(), name.clone()))
            })
            .copied()
            .ok_or_else(|| "Path構造の元fieldがない".into())
    }
    pub(super) fn path_structure_slot(
        &self,
        owner: &Subject,
        field: &crate::archmap::Field,
        reading: &str,
        out: &mut PathResult,
    ) -> Result<(), ValidationFailure> {
        self.tick()?;
        if self.path_reads_value(&field.ty)? {
            self.path_slot(owner, field, reading, out)?;
            return Ok(());
        }
        let position = Fact {
            snapshot: owner.snapshot.clone(),
            subject: owner.id.clone(),
            field: Some(field.name.clone()),
            atom: None,
        };
        match &field.slot {
            Slot::Known { atom, origin, .. } => {
                out.scope
                    .merge(&self.indexes.scope(owner, reading, Some(origin))?);
                let mut fact = position;
                fact.atom = Some(atom.clone());
                out.support.push(self.path_atom_support(&fact));
            }
            Slot::Missing => {
                out.scope.merge(&self.indexes.scope(owner, reading, None)?);
                out.scope.completions = true;
                if let Some(reads) = self.state.missing_slot_reads.borrow_mut().as_mut() {
                    reads.insert(position.clone());
                }
                out.missing.push(position);
            }
        }
        self.tick()?;
        Ok(())
    }
    // 元型で検査した候補のdecoded値を、同じ位置の参照構造検査へ渡す。
    pub(super) fn path_input_value<'b>(
        &'b self,
        owner: &Subject,
        field: &'b crate::archmap::Field,
    ) -> Result<Option<&'b Value>, ValidationFailure> {
        if self.path_reads_value(&field.ty)? {
            self.indexes
                .field(&self.state, &owner.snapshot, &owner.id, &field.name)?;
        }
        let position = Fact {
            snapshot: owner.snapshot.clone(),
            subject: owner.id.clone(),
            field: Some(field.name.clone()),
            atom: None,
        };
        if let Some(value) = self
            .indexes
            .primitive_input_valuation
            .as_ref()
            .and_then(|v| v.get(&position))
        {
            return Ok(Some(value));
        }
        Ok(match &field.slot {
            Slot::Known { value, .. } => Some(value),
            Slot::Missing => None,
        })
    }
    pub(super) fn path_atom_support(&self, fact: &Fact) -> Fact {
        let mut position = fact.clone();
        position.atom = None;
        if self
            .indexes
            .primitive_valuation
            .as_ref()
            .is_some_and(|v| v.contains_key(&position))
        {
            position
        } else {
            fact.clone()
        }
    }
    pub(super) fn path_slot(
        &self,
        owner: &Subject,
        field: &crate::archmap::Field,
        reading: &str,
        out: &mut PathResult,
    ) -> Result<Option<Scalar>, ValidationFailure> {
        self.tick()?;
        self.indexes
            .field(&self.state, &owner.snapshot, &owner.id, &field.name)?;
        let position = Fact {
            snapshot: owner.snapshot.clone(),
            subject: owner.id.clone(),
            field: Some(field.name.clone()),
            atom: None,
        };
        if let Some(value) = self
            .indexes
            .primitive_valuation
            .as_ref()
            .and_then(|v| v.get(&position))
        {
            out.scope.merge(&self.indexes.scope(owner, reading, None)?);
            out.scope.assignments = true;
            out.support.push(position.clone());
            if matches!(field.slot, Slot::Missing) {
                out.scope.completions = true;
                out.missing.push(position);
            }
            return Ok(Some(value.clone()));
        }
        match &field.slot {
            Slot::Known {
                atom,
                origin,
                value,
                ..
            } => {
                out.scope
                    .merge(&self.indexes.scope(owner, reading, Some(origin))?);
                out.support.push(Fact {
                    snapshot: owner.snapshot.clone(),
                    subject: owner.id.clone(),
                    field: Some(field.name.clone()),
                    atom: Some(atom.clone()),
                });
                scalar_from(value, &field.ty, self.indexes.inputs.law(), &self.control)
            }
            Slot::Missing => {
                out.scope.merge(&self.indexes.scope(owner, reading, None)?);
                out.scope.completions = true;
                let fact = Fact {
                    snapshot: owner.snapshot.clone(),
                    subject: owner.id.clone(),
                    field: Some(field.name.clone()),
                    atom: None,
                };
                out.missing.push(fact.clone());
                Ok(self
                    .state
                    .completion_values
                    .borrow()
                    .iter()
                    .find(|(f, _, _)| {
                        f.snapshot == fact.snapshot
                            && f.subject == fact.subject
                            && f.field == fact.field
                    })
                    .map(|(_, _, v)| v.clone()))
            }
        }
    }
    pub(in crate::observed) fn internal_path(
        &self,
        id: usize,
        values: &[Scalar],
    ) -> Result<PathResult, ValidationFailure> {
        self.tick()?;
        let reading = self.path_reading(id)?;
        self.generator_path(reading, values, self.indexes.inputs.law().exprs()[id].span)
    }
    pub(in crate::observed) fn generator_path(
        &self,
        reading: &str,
        values: &[Scalar],
        span: (usize, usize),
    ) -> Result<PathResult, ValidationFailure> {
        let [generator @ Scalar::Subject { entity, .. }] = values else {
            return Err("pathの元引数が原始参照1個でない".into());
        };
        let declaration = self
            .indexes
            .inputs
            .definitions()
            .declarations()
            .get(entity)
            .ok_or("pathの原始宣言がない")?;
        if matches!(
            &declaration.signature,
            PrimitiveSignature::Correspondence { .. }
        ) {
            return self.correspondence_path(reading, generator, &declaration.signature, span);
        }
        self.internal_arrow_path(reading, values, span)
    }
    pub(in crate::observed) fn internal_arrow_path(
        &self,
        reading: &str,
        values: &[Scalar],
        _span: (usize, usize),
    ) -> Result<PathResult, ValidationFailure> {
        self.tick()?;
        let mut out = PathResult {
            value: None,
            scope: Scope::default(),
            support: vec![],
            missing: vec![],
            failure: None,
        };
        out.scope.readings.insert(reading.into());
        out.scope.assignments = self.indexes.primitive_valuation.is_some();
        let [
            generator @ Scalar::Subject {
                snapshot,
                subject,
                entity,
            },
        ] = values
        else {
            return Err("pathの元引数が原始参照1個でない".into());
        };
        let declaration = self
            .indexes
            .inputs
            .definitions()
            .declarations()
            .get(entity)
            .ok_or("pathの原始宣言がない")?;
        let PrimitiveSignature::Arrow { endpoint, .. } = &declaration.signature else {
            return Err("pathの元宣言がarrow/correspondenceでない".into());
        };
        let arrow = self.indexes.subject(snapshot, subject)?;
        if arrow.ty != *entity {
            return Err("pathの元arrow型が違う".into());
        }
        let from = self.path_slot(
            arrow,
            self.indexes
                .field(&self.state, snapshot, subject, &format!("{entity}.from"))?,
            reading,
            &mut out,
        )?;
        let to = self.path_slot(
            arrow,
            self.indexes
                .field(&self.state, snapshot, subject, &format!("{entity}.to"))?,
            reading,
            &mut out,
        )?;
        let (Some(from @ Scalar::Subject { .. }), Some(to @ Scalar::Subject { .. })) = (from, to)
        else {
            out.missing.sort();
            out.missing.dedup();
            return Ok(out);
        };
        if from.ty() != Type::Ref(endpoint.clone()) || to.ty() != Type::Ref(endpoint.clone()) {
            return Err("pathの実端点型が元arrowと違う".into());
        }
        let Scalar::Subject {
            snapshot: fs,
            subject: fp,
            entity: fe,
        } = &from
        else {
            unreachable!()
        };
        let Scalar::Subject {
            snapshot: ts,
            subject: tp,
            entity: te,
        } = &to
        else {
            unreachable!()
        };
        let source = self.indexes.subject(fs, fp)?;
        let target = self.indexes.subject(ts, tp)?;
        if source.ty != *fe || target.ty != *te {
            return Err("pathの端点subjectが元入力と違う".into());
        }
        // Uは選択した端点のsnapshotだけへ縮めず、全入力の原始identityで構成する。
        let mut universe = BTreeSet::new();
        for snapshot in self.indexes.inputs.archmap().snapshots() {
            self.tick()?;
            for s in &snapshot.subjects {
                self.tick()?;
                out.scope.merge(&self.indexes.scope(s, reading, None)?);
                universe.insert(Fact {
                    snapshot: s.snapshot.clone(),
                    subject: s.id.clone(),
                    field: None,
                    atom: None,
                });
                for f in &s.fields {
                    self.tick()?;
                    if let Slot::Known { atom, origin, .. } = &f.slot {
                        out.scope
                            .merge(&self.indexes.scope(s, reading, Some(origin))?);
                        universe.insert(Fact {
                            snapshot: s.snapshot.clone(),
                            subject: s.id.clone(),
                            field: Some(f.name.clone()),
                            atom: Some(atom.clone()),
                        });
                    }
                }
            }
        }
        let source_fact = Fact {
            snapshot: fs.clone(),
            subject: fp.clone(),
            field: None,
            atom: None,
        };
        let target_fact = Fact {
            snapshot: ts.clone(),
            subject: tp.clone(),
            field: None,
            atom: None,
        };
        let mut images = BTreeMap::new();
        images.insert(source_fact.clone(), target_fact.clone());
        let mut family = BTreeSet::from([source_fact]);
        let mut missing_field = false;
        for field in &source.fields {
            self.tick()?;
            let Slot::Known { atom, .. } = &field.slot else {
                self.path_structure_slot(source, field, reading, &mut out)?;
                missing_field = true;
                continue;
            };
            let target_field = self.path_structure_field(target, &field.name)?;
            self.path_structure_slot(target, target_field, reading, &mut out)?;
            let Slot::Known {
                atom: target_atom, ..
            } = &target_field.slot
            else {
                missing_field = true;
                continue;
            };
            let fact = Fact {
                snapshot: fs.clone(),
                subject: fp.clone(),
                field: Some(field.name.clone()),
                atom: Some(atom.clone()),
            };
            let image = Fact {
                snapshot: ts.clone(),
                subject: tp.clone(),
                field: Some(target_field.name.clone()),
                atom: Some(target_atom.clone()),
            };
            let mut refs = BTreeSet::new();
            let moving = BTreeMap::from([((fs.clone(), fp.clone()), (ts.clone(), tp.clone()))]);
            let value = self
                .path_input_value(source, field)?
                .ok_or("元Pathのfield値がない")?;
            let target_value = self
                .path_input_value(target, target_field)?
                .ok_or("Pathの像field値がない")?;
            let expected = self.path_shape(value, Some(&moving), &mut refs)?;
            let actual = self.path_shape(target_value, None, &mut BTreeSet::new())?;
            if !self.path_shape_same(&expected, &actual)? {
                out.failure = Some((
                    Scalar::Text(self.path_shape_text(&actual)?),
                    Scalar::Text(self.path_shape_text(&expected)?),
                ));
            }
            family.insert(fact.clone());
            family.extend(refs);
            images.insert(fact, image);
        }
        out.support
            .extend(universe.iter().map(|fact| self.path_atom_support(fact)));
        out.support.sort();
        out.support.dedup();
        out.missing.sort();
        out.missing.dedup();
        // targetに像Atomが実在しなければ、補完値を新しい原始AtomとしてUへ追加しない。
        if missing_field {
            return Ok(out);
        }
        if out.failure.is_some() {
            return Ok(out);
        }
        let mut carrier = Vec::new();
        let mut action = Vec::new();
        for fact in universe {
            self.tick()?;
            let image = if let Some(image) = images.get(&fact) {
                image.clone()
            } else {
                fact.clone()
            };
            if family.contains(&fact)
                && fact.field.is_none()
                && fact.snapshot == *fs
                && fact.subject == *fp
                && image != target_fact
            {
                return Err("pathの端点像が標準規則と違う".into());
            }
            carrier.push(fact);
            action.push(image);
            #[cfg(test)]
            data::observe_actual(
                _span,
                self.state
                    .scoped_context
                    .get()
                    .or(self.state.context.get())
                    .unwrap_or_default(),
                "path_action",
                carrier.len(),
            );
            self.tick()?;
        }
        let path = PathValue {
            reading: reading.into(),
            snapshot: fs.clone(),
            subject: fp.clone(),
            entity: fe.clone(),
            step: Some(Box::new(Step {
                generator: generator.clone(),
                word_tail: vec![],
                target: to,
                carrier,
                images: action,
            })),
        };
        path.check(&self.control)?;
        out.value = Some(Scalar::Path(Box::new(path)));
        self.tick()?;
        Ok(out)
    }
}

impl Environment<'_> {
    pub(in crate::observed) fn is_path(&self, id: usize) -> Result<bool, ValidationFailure> {
        Ok(matches!(self.builtin(id)?, Some("path" | "then")))
    }
    pub(in crate::observed) fn internal_path_at(
        &self,
        graph: &Graph,
        id: usize,
        values: &[Scalar],
    ) -> Result<PathResult, ValidationFailure> {
        self.validation_graph_session(graph, || {
            let actual_context = self.current_context(graph);
            let context = self.state.context.scoped(Some(actual_context));
            let cutoff = self.state.cutoff.scoped(graph.nodes.len());
            let old = self.state.completion_values.scoped(vec![]);
            let result = (|| {
                if let Some(case) = actual_context.case {
                    *self.state.completion_values.borrow_mut() =
                        self.completion_values(graph, case)?;
                }
                self.path_operation(id, values)
            })();
            old.restore();
            context.restore();
            cutoff.restore();
            result
        })
    }
    pub(super) fn path_scalar_analysis(
        &self,
        graph: &Graph,
        node: &Node,
        limit: usize,
    ) -> Result<Option<SourceAnalysis>, ValidationFailure> {
        let Rule::Input {
            kind: "law",
            location: Location::Law { span },
        } = &node.rule
        else {
            return Ok(None);
        };
        let Some(&id) = self.indexes.inputs.law().program().expressions.get(span) else {
            return Ok(None);
        };
        if !self.is_path(id)? {
            return Ok(None);
        }
        #[cfg(test)]
        data::observe_actual(
            *span,
            self.current_context(graph),
            if self.builtin(id)? == Some("then") {
                "path_composition_recheck"
            } else {
                "path_scalar_recheck"
            },
            0,
        );
        self.tick()?;
        let Some(Payload::Scalar(Scalar::Path(path))) = &node.payload else {
            return Err("元path式の結果値がPathでない".into());
        };
        if node.ty != NodeType::Value(Scalar::Path(path.clone()).ty())
            || self.indexes.inputs.law().expr_type(id) != Some(&Scalar::Path(path.clone()).ty())
            || !node.evidence.is_empty()
            || node.judgment.is_some()
            || !node.reasons.is_empty()
        {
            return Err("Pathの元型・証拠・理由が違う".into());
        }
        let ExprKind::Call { args, .. } = &self.indexes.inputs.law().exprs()[id].kind else {
            unreachable!()
        };
        if node.arguments.len() != args.len() + 2 {
            return Err("Pathの元引数と既出端点が揃わない".into());
        }
        let (operands, endpoints) = node.arguments.split_at(args.len());
        let [from, to] = endpoints else {
            unreachable!()
        };
        // 元引数はcallerから再利用でき、callee内の各実子Evaluationと下で照合する。
        for (i, r) in node.arguments.iter().enumerate() {
            self.tick()?;
            if r.0 >= limit
                || (i >= args.len() && graph.context_at(r.0) != self.current_context(graph))
            {
                return Err("Pathの依存が既出・同Contextでない".into());
            }
            self.validate_at(graph, graph.get(*r)?, r.0)?;
        }
        if graph.scalar(*from)? != &path.object() || graph.scalar(*to)? != &path.target() {
            return Err("Pathの既出Refと実端点が違う".into());
        }
        for (i, source) in graph.nodes.iter().enumerate().take(limit) {
            self.tick()?;
            let Some(Payload::Expression {
                location: Location::Law { span: at },
                bindings,
                ..
            }) = &source.payload
            else {
                continue;
            };
            if at != span || graph.context_at(i) != self.current_context(graph) {
                continue;
            }
            let result = (|| {
                self.validate_at(graph, source, i)?;
                for (&arg, &value) in args.iter().zip(operands) {
                    if !self.has_operand_evaluation(graph, limit, arg, bindings, value)? {
                        return Err("Pathの実引数が元実子の値でない".into());
                    }
                }
                let analysis = self.analyze_source(graph, *span, bindings)?;
                if analysis.known_value.as_ref() != Some(&Scalar::Path(path.clone()))
                    || analysis.support != node.support
                    || analysis.scalar_scope.as_ref() != Some(&node.scope)
                {
                    return Err("Pathの値・支持・Scopeが元三入力と違う".into());
                }
                Ok::<_, ValidationFailure>(analysis)
            })();
            match result {
                Ok(a) => return Ok(Some(a)),
                Err(ValidationFailure::Internal(_)) => {}
                Err(e) => return Err(e),
            }
        }
        Err("Path値の元Sourceと実子評価がない".into())
    }
    pub(super) fn path_missing_slots(
        &self,
        graph: &Graph,
        source: NodeRef,
    ) -> Result<Option<Vec<Fact>>, ValidationFailure> {
        let span = self.expression_span(graph, source)?;
        let Some(&id) = self.indexes.inputs.law().program().expressions.get(&span) else {
            return Ok(None);
        };
        if self.builtin(id)? != Some("path") {
            return Ok(None);
        }
        let ExprKind::Call { args, .. } = &self.indexes.inputs.law().exprs()[id].kind else {
            unreachable!()
        };
        let bindings = self.expression_bindings(graph, source)?;
        let Some(value) = self
            .analyze_source(
                graph,
                self.indexes.inputs.law().exprs()[args[0]].span,
                bindings,
            )?
            .known_value
        else {
            return Ok(None);
        };
        let info = self.internal_path(id, &[value])?;
        Ok((!info.missing.is_empty()).then_some(info.missing))
    }
}

impl Environment<'_> {
    pub(super) fn path_used_support(
        &self,
        graph: &Graph,
        source: NodeRef,
        children: &[NodeRef],
    ) -> Result<Option<Vec<Fact>>, ValidationFailure> {
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &graph.get(source)?.payload
        else {
            return Ok(None);
        };
        let span = *span;
        let Some(&id) = self.indexes.inputs.law().program().expressions.get(&span) else {
            return Ok(None);
        };
        if !self.is_path(id)? {
            return Ok(None);
        }
        let previous = self.state.context.scoped(Some(graph.context_at(source.0)));
        let result = (|| {
            let bindings = self.expression_bindings(graph, source)?;
            let ExprKind::Call { args, .. } = &self.indexes.inputs.law().exprs()[id].kind else {
                unreachable!()
            };
            if children.len() != args.len() {
                return Err("Path支持の元実子数が違う".into());
            }
            let mut values = Vec::new();
            for (&arg, &child) in args.iter().zip(children) {
                self.tick()?;
                if self.actual_evaluation(graph, arg, bindings)? != child {
                    return Err("Path支持の実子が元producerでない".into());
                }
                let Some(value) = self.evaluation(graph, child)?.2 else {
                    return Ok(Some(vec![]));
                };
                values.push(graph.scalar(value)?.clone());
            }
            Ok(Some(self.internal_path_at(graph, id, &values)?.support))
        })();
        previous.restore();
        result
    }
}
