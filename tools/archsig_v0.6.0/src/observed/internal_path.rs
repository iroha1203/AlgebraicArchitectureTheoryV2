//! 元の内部arrowから、共通Atom carrier上の1段作用を再構成する。
use super::super::path_value::{PathValue, Step};
use super::*;
use crate::definition::model::PrimitiveSignature;

pub(in crate::observed) struct PathResult {
    pub(in crate::observed) value: Option<Scalar>,
    pub(in crate::observed) scope: Scope,
    pub(in crate::observed) support: Vec<Fact>,
    pub(in crate::observed) missing: Vec<Fact>,
    pub(in crate::observed) failure: Option<(Scalar, Scalar)>,
}
// 参照へ至る構造を平坦なtoken列へし、深い値の比較・破棄も再帰させない。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Token {
    Open(String),
    Close,
    Quantity,
    Reference(String, String),
}
type Shape = Vec<Token>;
impl Environment<'_> {
    fn path_shape(
        &self,
        value: &Value,
        moving: Option<((&str, &str), (&str, &str))>,
        references: &mut BTreeSet<Fact>,
    ) -> Result<Option<Shape>, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            self.tick()?;
            if let Value::Ref { snapshot, subject } = value {
                self.subject(snapshot, subject)?;
                references.insert(Fact {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    field: None,
                    atom: None,
                });
                let point = if let Some((from, to)) = moving {
                    if from == (snapshot.as_str(), subject.as_str()) {
                        to
                    } else {
                        (snapshot.as_str(), subject.as_str())
                    }
                } else {
                    (snapshot.as_str(), subject.as_str())
                };
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
    fn path_shape_same(
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
    fn path_shape_text(&self, shape: &Option<Shape>) -> Result<String, ValidationFailure> {
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
        let span = self.inputs.law().exprs[id].span;
        let mut reading = None;
        for d in self.inputs.law().declarations.values() {
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
    fn path_slot(
        &self,
        owner: &Subject,
        field: &crate::archmap::Field,
        reading: &str,
        out: &mut PathResult,
    ) -> Result<Option<Scalar>, ValidationFailure> {
        self.tick()?;
        match &field.slot {
            Slot::Known {
                atom,
                origin,
                value,
                ..
            } => {
                out.scope.merge(&self.scope(owner, reading, Some(origin))?);
                out.support.push(Fact {
                    snapshot: owner.snapshot.clone(),
                    subject: owner.id.clone(),
                    field: Some(field.name.clone()),
                    atom: Some(atom.clone()),
                });
                scalar_from(value, &field.ty, self.inputs.law(), &self.control)
            }
            Slot::Missing => {
                out.scope.merge(&self.scope(owner, reading, None)?);
                out.scope.completions = true;
                let fact = Fact {
                    snapshot: owner.snapshot.clone(),
                    subject: owner.id.clone(),
                    field: Some(field.name.clone()),
                    atom: None,
                };
                out.missing.push(fact.clone());
                Ok(self
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
        let mut out = PathResult {
            value: None,
            scope: Scope::default(),
            support: vec![],
            missing: vec![],
            failure: None,
        };
        out.scope.readings.insert(reading.into());
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
            .inputs
            .definitions()
            .declarations
            .get(entity)
            .ok_or("pathの原始宣言がない")?;
        let PrimitiveSignature::Arrow { endpoint, .. } = &declaration.signature else {
            return Err(ValidationFailure::UnsupportedExpression {
                location: Location::Law {
                    span: self.inputs.law().exprs[id].span,
                },
                feature: "correspondence生成Pathの実作用".into(),
            });
        };
        let arrow = self.subject(snapshot, subject)?;
        if arrow.ty != *entity {
            return Err("pathの元arrow型が違う".into());
        }
        let from = self.path_slot(
            arrow,
            self.field(snapshot, subject, &format!("{entity}.from"))?,
            reading,
            &mut out,
        )?;
        let to = self.path_slot(
            arrow,
            self.field(snapshot, subject, &format!("{entity}.to"))?,
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
        let source = self.subject(fs, fp)?;
        let target = self.subject(ts, tp)?;
        if source.ty != *fe || target.ty != *te {
            return Err("pathの端点subjectが元入力と違う".into());
        }
        // Uは選択した端点のsnapshotだけへ縮めず、全入力の原始identityで構成する。
        let mut universe = BTreeSet::new();
        for snapshot in &self.inputs.archmap().snapshots {
            self.tick()?;
            for s in &snapshot.subjects {
                self.tick()?;
                out.scope.merge(&self.scope(s, reading, None)?);
                universe.insert(Fact {
                    snapshot: s.snapshot.clone(),
                    subject: s.id.clone(),
                    field: None,
                    atom: None,
                });
                for f in &s.fields {
                    self.tick()?;
                    if let Slot::Known { atom, origin, .. } = &f.slot {
                        out.scope.merge(&self.scope(s, reading, Some(origin))?);
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
            let Slot::Known { atom, value, .. } = &field.slot else {
                self.path_slot(source, field, reading, &mut out)?;
                missing_field = true;
                continue;
            };
            let target_field = self.field(ts, tp, &field.name)?;
            let got = self.path_slot(target, target_field, reading, &mut out)?;
            let Slot::Known {
                atom: target_atom,
                value: target_value,
                ..
            } = &target_field.slot
            else {
                let _ = got;
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
            let expected = self.path_shape(value, Some(((fs, fp), (ts, tp))), &mut refs)?;
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
        out.support.extend(universe.iter().cloned());
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
                self.inputs.law().exprs[id].span,
                self.scoped_context
                    .get()
                    .or(self.context.get())
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
        Ok(self.builtin(id)? == Some("path"))
    }
    pub(in crate::observed) fn internal_path_at(
        &self,
        graph: &Graph,
        id: usize,
        values: &[Scalar],
    ) -> Result<PathResult, ValidationFailure> {
        self.validation_graph_session(graph, || {
            let actual_context = self.current_context(graph);
            let context = self.context.replace(Some(actual_context));
            let cutoff = self.cutoff.replace(graph.nodes.len());
            let old = self.completion_values.replace(vec![]);
            let result = (|| {
                if let Some(case) = actual_context.case {
                    *self.completion_values.borrow_mut() = self.completion_values(graph, case)?;
                }
                self.internal_path(id, values)
            })();
            self.completion_values.replace(old);
            self.context.set(context);
            self.cutoff.set(cutoff);
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
        let Some(&id) = self.expressions.get(span) else {
            return Ok(None);
        };
        if !self.is_path(id)? {
            return Ok(None);
        }
        #[cfg(test)]
        data::observe_actual(*span, self.current_context(graph), "path_scalar_recheck", 0);
        self.tick()?;
        let Some(Payload::Scalar(Scalar::Path(path))) = &node.payload else {
            return Err("元path式の結果値がPathでない".into());
        };
        if node.ty != NodeType::Value(Scalar::Path(path.clone()).ty())
            || self.inputs.law().expr_type(id) != Some(&Scalar::Path(path.clone()).ty())
            || !node.evidence.is_empty()
            || node.judgment.is_some()
            || !node.reasons.is_empty()
        {
            return Err("Pathの元型・証拠・理由が違う".into());
        }
        let [generator, from, to] = node.arguments.as_slice() else {
            return Err("Pathの元引数と既出端点が揃わない".into());
        };
        // 元引数はcallerから再利用できる。callee内の実子Evaluationとの一致を下で検査する。
        // 端点表示用RefはこのPathと同じContextで新しく構成される。
        for r in [generator, from, to] {
            self.tick()?;
            if r.0 >= limit
                || (r != generator && graph.context_at(r.0) != self.current_context(graph))
            {
                return Err("Pathの依存が既出・同Contextでない".into());
            }
            self.validate_at(graph, graph.get(*r)?, r.0)?;
        }
        if graph.scalar(*from)? != &path.object() || graph.scalar(*to)? != &path.target() {
            return Err("Pathの既出Refと実端点が違う".into());
        }
        let ExprKind::Call { args, .. } = &self.inputs.law().exprs[id].kind else {
            unreachable!()
        };
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
                if !self.has_operand_evaluation(graph, limit, args[0], bindings, *generator)? {
                    return Err("Pathの生成元が元実子の値でない".into());
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
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        if !self.is_path(id)? {
            return Ok(None);
        }
        let ExprKind::Call { args, .. } = &self.inputs.law().exprs[id].kind else {
            unreachable!()
        };
        let bindings = self.expression_bindings(graph, source)?;
        let Some(value) = self
            .analyze_source(graph, self.inputs.law().exprs[args[0]].span, bindings)?
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
        let Some(&id) = self.expressions.get(&span) else {
            return Ok(None);
        };
        if !self.is_path(id)? {
            return Ok(None);
        }
        let [child] = children else {
            return Err("Path支持の元実子数が違う".into());
        };
        let previous = self.context.replace(Some(graph.context_at(source.0)));
        let result = (|| {
            let bindings = self.expression_bindings(graph, source)?;
            let ExprKind::Call { args, .. } = &self.inputs.law().exprs[id].kind else {
                unreachable!()
            };
            if self.actual_evaluation(graph, args[0], bindings)? != *child {
                return Err("Path支持の実子が元producerでない".into());
            }
            let Some(value) = self.evaluation(graph, *child)?.2 else {
                return Ok(Some(vec![]));
            };
            Ok(Some(
                self.internal_path_at(graph, id, &[graph.scalar(value)?.clone()])?
                    .support,
            ))
        })();
        self.context.set(previous);
        result
    }
}
