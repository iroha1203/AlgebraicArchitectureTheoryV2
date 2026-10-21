//! 型付きの原始値から外延等値と完成済みの証拠を計算する。
use super::*;
use crate::observed::{finite, term};
use crate::types::Type;
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Data {
    Value {
        value: Scalar,
        arguments: Vec<NodeRef>,
    },
    Expression {
        left: NodeRef,
        right: NodeRef,
    },
    Domain {
        ty: Type,
        elements: Vec<NodeRef>,
        source: NodeRef,
    },
    Exhaustion {
        domain: NodeRef,
        checked: usize,
        instances: Vec<NodeRef>,
    },
    Normalization {
        before: NodeRef,
        after: NodeRef,
        source: NodeRef,
    },
    Counterexample {
        bindings: Vec<Binding>,
        left: NodeRef,
        right: NodeRef,
        facts: Vec<Fact>,
        source: NodeRef,
        originals: [NodeRef; 2],
    },
    Claim {
        left: NodeRef,
        right: NodeRef,
        source: NodeRef,
        arguments: Vec<NodeRef>,
        status: Decision,
        evidence: Vec<NodeRef>,
        reasons: Vec<Reason>,
    },
}
impl Data {
    pub fn scalar(&self) -> Option<&Scalar> {
        match self {
            Self::Value { value, .. } => Some(value),
            _ => None,
        }
    }
    pub fn ty(&self) -> NodeType {
        match self {
            Self::Value { value, .. } => NodeType::Value(value.ty()),
            Self::Expression { .. } => NodeType::Expression(Type::Bool),
            Self::Domain { .. } => NodeType::Domain,
            Self::Claim { .. } => NodeType::Proposition,
            _ => NodeType::Evidence,
        }
    }
    pub fn construction(&self) -> &'static str {
        match self {
            Self::Value { .. } => "evaluation",
            Self::Expression { .. } => "expression",
            Self::Domain { .. } => "domain",
            Self::Claim { .. } => "proposition",
            _ => "evidence",
        }
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Value { arguments, .. } => arguments.clone(),
            Self::Expression { left, right } => vec![*left, *right],
            Self::Domain {
                elements, source, ..
            } => std::iter::once(*source)
                .chain(elements.iter().copied())
                .collect(),
            Self::Exhaustion {
                domain, instances, ..
            } => std::iter::once(*domain)
                .chain(instances.iter().copied())
                .collect(),
            Self::Normalization {
                before,
                after,
                source,
            } => vec![*source, *before, *after],
            Self::Counterexample {
                bindings,
                left,
                right,
                source,
                originals,
                ..
            } => std::iter::once(*source)
                .chain(originals.iter().copied())
                .chain(bindings.iter().map(|b| b.value))
                .chain([*left, *right])
                .collect(),
            Self::Claim {
                left,
                right,
                source,
                arguments,
                ..
            } => std::iter::once(*source)
                .chain(arguments.iter().copied())
                .chain([*left, *right])
                .collect(),
        }
    }
    pub fn judgment(&self) -> Option<Judgment> {
        match self {
            Self::Claim {
                status,
                evidence,
                reasons,
                ..
            } => Some(Judgment {
                status: *status,
                evidence: evidence.clone(),
                reasons: reasons.clone(),
            }),
            _ => None,
        }
    }
    pub fn evidence(&self) -> Vec<NodeRef> {
        self.judgment().map(|j| j.evidence).unwrap_or_default()
    }
    pub fn wire(&self) -> Json {
        match self {
            Self::Value { value, .. } => value.wire(),
            Self::Expression { left, right } => Json::obj([
                ("kind", Json::str("transform")),
                ("operation", Json::str("equal")),
                ("operands", refs(&[*left, *right])),
                ("parameters", Json::Arr(vec![])),
                ("bindings", Json::Arr(vec![])),
            ]),
            Self::Domain { ty, elements, .. } => Json::obj([
                ("kind", Json::str("finite")),
                ("type", ty.wire()),
                ("elements", refs(elements)),
            ]),
            Self::Claim { left, right, .. } => Json::obj([
                ("predicate", Json::str("equal")),
                ("operands", refs(&[*left, *right])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            Self::Exhaustion {
                domain,
                checked,
                instances,
            } => Json::obj([
                ("kind", Json::str("finite_exhaustion")),
                (
                    "data",
                    Json::obj([
                        ("domain", domain.wire()),
                        ("checked", Json::Nat(*checked as u64)),
                        ("instances", refs(instances)),
                    ]),
                ),
            ]),
            Self::Normalization {
                before,
                after,
                source,
            } => Json::obj([
                ("kind", Json::str("normalization")),
                (
                    "data",
                    Json::obj([
                        ("before", before.wire()),
                        ("after", after.wire()),
                        ("steps", refs(&[*source])),
                    ]),
                ),
            ]),
            Self::Counterexample {
                bindings,
                left,
                right,
                facts,
                ..
            } => Json::obj([
                ("kind", Json::str("counterexample")),
                (
                    "data",
                    Json::obj([
                        (
                            "bindings",
                            Json::Arr(
                                bindings
                                    .iter()
                                    .map(|b| {
                                        Json::obj([
                                            ("name", Json::str(&b.name)),
                                            ("value", b.value.wire()),
                                        ])
                                    })
                                    .collect(),
                            ),
                        ),
                        ("paths", Json::Arr(vec![])),
                        ("left", left.wire()),
                        ("right", right.wire()),
                        ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                    ]),
                ),
            ]),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ResultData {
    pub equal: Option<bool>,
    pub evidence: Vec<NodeRef>,
    pub reasons: Vec<Reason>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Plan {
    pub base: usize,
    pub nodes: Vec<Data>,
    pub result: ResultData,
    pub stopped: Option<StopReason>,
    pub finished: bool,
}
struct Calculator<'a> {
    base: usize,
    nodes: Vec<Data>,
    law: &'a crate::law::CheckedLaw,
    c: &'a Control,
    request: &'a str,
    facts: &'a [Fact],
    completed: Option<ResultData>,
}
fn decision(v: Option<bool>) -> Decision {
    match v {
        Some(true) => Decision::Established,
        Some(false) => Decision::Refuted,
        None => Decision::Undetermined,
    }
}
impl Calculator<'_> {
    fn tick(&self) -> Result<(), ValidationFailure> {
        self.c.clone().checkpoint(Checkpoint::FiniteIteration)?;
        Ok(())
    }
    fn add(&mut self, data: Data) -> Result<NodeRef, ValidationFailure> {
        self.tick()?;
        let r = NodeRef(self.base + self.nodes.len());
        self.nodes.push(data);
        self.tick()?;
        Ok(r)
    }
    fn value(&mut self, value: Scalar, args: Vec<NodeRef>) -> Result<NodeRef, ValidationFailure> {
        self.add(Data::Value {
            value,
            arguments: args,
        })
    }
    fn counterexample(
        &mut self,
        source: NodeRef,
        originals: [NodeRef; 2],
        bindings: Vec<Binding>,
        left: NodeRef,
        right: NodeRef,
    ) -> Result<NodeRef, ValidationFailure> {
        self.add(Data::Counterexample {
            bindings,
            left,
            right,
            facts: self.facts.to_vec(),
            source,
            originals,
        })
    }
    fn unsupported(
        &self,
        source: NodeRef,
        left: NodeRef,
        right: NodeRef,
        a: &Scalar,
        b: &Scalar,
        method: &str,
    ) -> ResultData {
        ResultData {
            equal: None,
            evidence: vec![],
            reasons: vec![Reason {
                kind: ReasonKind::UnsupportedAlgorithm {
                    question: QuestionKind::Compare,
                    operand_types: vec![a.ty(), b.ty()],
                    method: method.into(),
                },
                request: self.request.into(),
                dependencies: vec![source, left, right],
                missing: vec![],
                location: None,
            }],
        }
    }
    fn compare(
        &mut self,
        a: &Scalar,
        b: &Scalar,
        left: NodeRef,
        right: NodeRef,
        root: bool,
    ) -> Result<ResultData, ValidationFailure> {
        stacker::maybe_grow(128 * 1024, 1024 * 1024, || {
            self.tick()?;
            if a.ty() != b.ty() {
                return Err("公開値比較の左右型が違う".into());
            }
            let source = self.add(Data::Expression { left, right })?;
            let result = if !term::contains(&a.ty(), self.law, self.c)? {
                let equal = super::super::data::equal(a, b, self.c)?;
                let evidence = if equal {
                    vec![]
                } else {
                    vec![self.counterexample(source, [left, right], vec![], left, right)?]
                };
                ResultData {
                    equal: Some(equal),
                    evidence,
                    reasons: vec![],
                }
            } else {
                match (a, b) {
                    (Scalar::Term(a), Scalar::Term(b)) => self.terms(a, b, left, right, source)?,
                    (Scalar::Tuple(a), Scalar::Tuple(b))
                    | (Scalar::List { items: a, .. }, Scalar::List { items: b, .. }) => {
                        self.sequence(a, b, left, right, source)?
                    }
                    (Scalar::Option { value: a, .. }, Scalar::Option { value: b, .. }) => {
                        match (a, b) {
                            (None, None) => ResultData {
                                equal: Some(true),
                                evidence: vec![],
                                reasons: vec![],
                            },
                            (Some(a), Some(b)) => self.children(
                                std::iter::once(a.as_ref()),
                                std::iter::once(b.as_ref()),
                                left,
                                right,
                                source,
                            )?,
                            _ => ResultData {
                                equal: Some(false),
                                evidence: vec![self.counterexample(
                                    source,
                                    [left, right],
                                    vec![],
                                    left,
                                    right,
                                )?],
                                reasons: vec![],
                            },
                        }
                    }
                    (
                        Scalar::Data {
                            constructor: a,
                            args: x,
                            ..
                        },
                        Scalar::Data {
                            constructor: b,
                            args: y,
                            ..
                        },
                    ) => {
                        if a != b {
                            ResultData {
                                equal: Some(false),
                                evidence: vec![self.counterexample(
                                    source,
                                    [left, right],
                                    vec![],
                                    left,
                                    right,
                                )?],
                                reasons: vec![],
                            }
                        } else {
                            self.sequence(x, y, left, right, source)?
                        }
                    }
                    _ => return Err("Termを含む原始値比較の値形が違う".into()),
                }
            };
            if root {
                self.completed = Some(result.clone());
            }
            self.tick()?;
            Ok(result)
        })
    }
    fn sequence(
        &mut self,
        a: &[Scalar],
        b: &[Scalar],
        left: NodeRef,
        right: NodeRef,
        source: NodeRef,
    ) -> Result<ResultData, ValidationFailure> {
        if a.len() != b.len() {
            return Ok(ResultData {
                equal: Some(false),
                evidence: vec![self.counterexample(source, [left, right], vec![], left, right)?],
                reasons: vec![],
            });
        }
        self.children(a.iter(), b.iter(), left, right, source)
    }
    fn children<'v>(
        &mut self,
        a: impl Iterator<Item = &'v Scalar>,
        b: impl Iterator<Item = &'v Scalar>,
        left: NodeRef,
        right: NodeRef,
        source: NodeRef,
    ) -> Result<ResultData, ValidationFailure> {
        let mut result = ResultData {
            equal: Some(true),
            evidence: vec![],
            reasons: vec![],
        };
        for (a, b) in a.zip(b) {
            self.tick()?;
            let l = self.value(a.clone(), vec![source, left])?;
            let r = self.value(b.clone(), vec![source, right])?;
            let child = self.compare(a, b, l, r, false)?;
            result.evidence.extend(child.evidence);
            match child.equal {
                Some(false) => {
                    result.equal = Some(false);
                    result.reasons.clear();
                    return Ok(result);
                }
                None => {
                    result.equal = None;
                    result.reasons.extend(child.reasons);
                }
                _ => {}
            }
        }
        Ok(result)
    }
    fn terms(
        &mut self,
        a: &term::Term,
        b: &term::Term,
        left: NodeRef,
        right: NodeRef,
        source: NodeRef,
    ) -> Result<ResultData, ValidationFailure> {
        a.check(self.c)?;
        b.check(self.c)?;
        let mut finite = true;
        for (_, ty) in &a.params {
            self.tick()?;
            finite &= finite::completion_supported(ty, self.law, self.c)?;
        }
        if finite {
            return self.finite_terms(a, b, left, right, source);
        }
        let Some(certificate) = term::affine::comparison(a, b, self.law, self.c)? else {
            if a == b {
                let e = self.add(Data::Normalization {
                    before: left,
                    after: right,
                    source,
                })?;
                return Ok(ResultData {
                    equal: Some(true),
                    evidence: vec![e],
                    reasons: vec![],
                });
            }
            return Ok(self.unsupported(
                source,
                left,
                right,
                &Scalar::Term(Box::new(a.clone())),
                &Scalar::Term(Box::new(b.clone())),
                "term_extensional_equality",
            ));
        };
        let mut evidence = vec![];
        for (term, is_left, before) in [(a, true, left), (b, false, right)] {
            let normal = certificate.presentation(term, is_left, self.c)?;
            let after = self.value(normal, vec![source, before])?;
            evidence.push(self.add(Data::Normalization {
                before,
                after,
                source,
            })?);
        }
        if let Some(point) = &certificate.point {
            let bindings = self.bindings(&a.params, &point.arguments, source)?;
            let mut args = vec![source, left, right];
            args.extend(bindings.iter().map(|b| b.value));
            let l = self.value(point.left.clone(), args.clone())?;
            let r = self.value(point.right.clone(), args)?;
            evidence.push(self.counterexample(source, [left, right], bindings, l, r)?);
        }
        Ok(ResultData {
            equal: Some(certificate.equal()),
            evidence,
            reasons: vec![],
        })
    }
    fn bindings(
        &mut self,
        params: &[(String, Type)],
        row: &[Scalar],
        source: NodeRef,
    ) -> Result<Vec<Binding>, ValidationFailure> {
        if params.len() != row.len() {
            return Err("Term代入の元parameter数が違う".into());
        }
        let mut out = vec![];
        for ((name, ty), value) in params.iter().zip(row) {
            self.tick()?;
            if *ty != value.ty() {
                return Err("Term代入の型が違う".into());
            }
            out.push(Binding {
                name: name.clone(),
                ty: ty.clone(),
                value: self.value(value.clone(), vec![source])?,
            });
        }
        Ok(out)
    }
    fn finite_terms(
        &mut self,
        a: &term::Term,
        b: &term::Term,
        left: NodeRef,
        right: NodeRef,
        source: NodeRef,
    ) -> Result<ResultData, ValidationFailure> {
        let mut rows = vec![vec![]];
        for (_, ty) in &a.params {
            let values = finite::values(
                ty,
                self.law,
                self.c,
                &mut |_| Err("Term比較に参照族を置けない".into()),
                &mut |_| {},
            )?
            .values;
            let mut next = vec![];
            for row in &rows {
                for value in &values {
                    self.tick()?;
                    let mut r = row.clone();
                    r.push(value.clone());
                    next.push(r);
                    self.tick()?;
                }
            }
            rows = next;
        }
        let ty = match a.params.as_slice() {
            [] => Type::Unit,
            [(_, ty)] => ty.clone(),
            many => Type::Tuple(many.iter().map(|(_, ty)| ty.clone()).collect()),
        };
        let mut elements = vec![];
        for row in &rows {
            let packed = match row.as_slice() {
                [] => Scalar::Unit,
                [v] => v.clone(),
                many => Scalar::Tuple(many.to_vec()),
            };
            elements.push(self.value(packed, vec![source])?);
        }
        let domain = self.add(Data::Domain {
            ty,
            elements,
            source,
        })?;
        let mut result = ResultData {
            equal: Some(true),
            evidence: vec![],
            reasons: vec![],
        };
        let mut instances = vec![];
        for row in &rows {
            self.tick()?;
            let bindings = self.bindings(&a.params, row, source)?;
            let mut args = vec![source, left, right, domain];
            args.extend(bindings.iter().map(|b| b.value));
            let mut outputs = vec![];
            for term in [a, b] {
                match term.apply(row, self.law, self.c) {
                    Ok(value) => outputs.push(self.value(value, args.clone())?),
                    Err(ValidationFailure::UnsupportedExpression { .. }) => break,
                    Err(e) => return Err(e),
                }
            }
            if outputs.len() != 2 {
                let unknown = self.unsupported(
                    source,
                    left,
                    right,
                    &Scalar::Term(Box::new(a.clone())),
                    &Scalar::Term(Box::new(b.clone())),
                    "term_application",
                );
                result.equal = None;
                result.reasons.extend(unknown.reasons);
                continue;
            }
            let (l, r) = (outputs[0], outputs[1]);
            let lv = match &self.nodes[l.0 - self.base] {
                Data::Value { value, .. } => value.clone(),
                _ => return Err("Term適用の左値がない".into()),
            };
            let rv = match &self.nodes[r.0 - self.base] {
                Data::Value { value, .. } => value.clone(),
                _ => return Err("Term適用の右値がない".into()),
            };
            let child = self.compare(&lv, &rv, l, r, false)?;
            instances.push(self.add(Data::Claim {
                left: l,
                right: r,
                source,
                arguments: args,
                status: decision(child.equal),
                evidence: child.evidence.clone(),
                reasons: child.reasons.clone(),
            })?);
            result.evidence.extend(child.evidence);
            match child.equal {
                Some(false) => {
                    result.equal = Some(false);
                    result.reasons.clear();
                    result.evidence.push(self.counterexample(
                        source,
                        [left, right],
                        bindings,
                        l,
                        r,
                    )?);
                    return Ok(result);
                }
                None => {
                    result.equal = None;
                    result.reasons.extend(child.reasons);
                }
                _ => {}
            }
        }
        if result.equal == Some(true) {
            result.evidence.push(self.add(Data::Exhaustion {
                domain,
                checked: rows.len(),
                instances,
            })?);
        }
        Ok(result)
    }
}
pub(super) fn evaluate(
    a: &Scalar,
    b: &Scalar,
    left: NodeRef,
    right: NodeRef,
    base: usize,
    law: &crate::law::CheckedLaw,
    request: &str,
    facts: &[Fact],
    c: &Control,
) -> Result<Plan, ValidationFailure> {
    let mut calc = Calculator {
        base,
        nodes: vec![],
        law,
        c,
        request,
        facts,
        completed: None,
    };
    let (result, stopped) = match calc.compare(a, b, left, right, true) {
        Ok(result) => (result, None),
        Err(ValidationFailure::Stop(s)) => {
            let result = calc.completed.clone().unwrap_or_else(|| ResultData {
                equal: None,
                evidence: calc
                    .nodes
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| n.ty() == NodeType::Evidence)
                    .map(|(i, _)| NodeRef(base + i))
                    .collect(),
                reasons: vec![],
            });
            (result, Some(s))
        }
        Err(e) => return Err(e),
    };
    let finished = calc.completed.is_some() || stopped.is_none();
    Ok(Plan {
        base,
        nodes: calc.nodes,
        result,
        stopped,
        finished,
    })
}
