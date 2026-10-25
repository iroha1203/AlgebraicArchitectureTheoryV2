//! buildの検査済み計画を、構成命題・circuit・ObjectAlgebraへ接続する。
use super::{
    PreparedObserved, build_circuit_plan, build_compare,
    build_plan::{self, Plan},
    construction_result::{
        self as native, ConstructionData as D, ConstructionType as T, ConstructionValue, Witness,
    },
    control::{Checkpoint, Control},
    environment::Environment,
    request::Request,
    result::*,
};
use crate::{canonical::Json, types::Type};
use std::{collections::BTreeMap, sync::Arc};

fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::NativeResultNode)?;
    Ok(())
}
fn refs(v: &[NodeRef]) -> Json {
    Json::Arr(v.iter().map(|r| r.wire()).collect())
}
fn path(v: &[usize]) -> Json {
    Json::Arr(v.iter().map(|n| Json::Nat(*n as u64)).collect())
}
fn bindings(v: &[Binding]) -> Json {
    Json::Arr(
        v.iter()
            .map(|b| Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())]))
            .collect(),
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Part {
    pub(super) ty: NodeType,
    pub(super) construction: &'static str,
    pub(super) wire: Json,
    pub(super) arguments: Vec<NodeRef>,
    pub(super) support: Vec<Fact>,
    pub(super) scope: Scope,
    pub(super) reasons: Vec<Reason>,
    pub(super) judgment: Option<Judgment>,
    pub(super) evidence: Vec<NodeRef>,
    pub(super) scalar: Option<Scalar>,
}
#[derive(Debug)]
pub(super) struct Source {
    plan: Plan,
    base: usize,
    parts: Vec<Part>,
    answer: Answer,
}
#[derive(Clone, Debug)]
pub(crate) struct Data {
    source: Arc<Source>,
    index: usize,
}
impl PartialEq for Data {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.source, &other.source) && self.index == other.index
    }
}
impl Eq for Data {}
impl Data {
    fn part(&self) -> &Part {
        &self.source.parts[self.index]
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty.clone()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction
    }
    pub(super) fn wire(&self) -> Json {
        self.part().wire.clone()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        self.part().arguments.clone()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.part().support.clone(), self.part().scope.clone())
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        self.part().scalar.as_ref()
    }
    pub(super) fn plan(&self) -> &Plan {
        &self.source.plan
    }
    pub(super) fn algebra_base(&self) -> Option<NodeRef> {
        (self.ty() == NodeType::Construction(T::ObjectAlgebra))
            .then(|| self.source.plan.objects.as_ref().map(|o| o.base))
            .flatten()
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if self.index >= self.source.parts.len()
            || at != self.source.base + self.index
            || self.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("build構成の位置/既出参照が違う".into());
        }
        Ok(())
    }
}

pub(super) struct Builder<'a> {
    pub(super) g: &'a Graph,
    pub(super) base: usize,
    pub(super) parts: Vec<Part>,
}
impl Builder<'_> {
    pub(super) fn push(
        &mut self,
        ty: NodeType,
        construction: &'static str,
        wire: Json,
        mut arguments: Vec<NodeRef>,
        scalar: Option<Scalar>,
        decision: Option<Decision>,
    ) -> Result<NodeRef, ValidationFailure> {
        arguments.sort_by_key(|r| r.0);
        arguments.dedup();
        let r = NodeRef(self.base + self.parts.len());
        let mut support = vec![];
        let mut scope = Scope::default();
        let mut reasons = vec![];
        for input in &arguments {
            self.g.tick()?;
            if input.0 >= r.0 {
                return Err("buildの未出参照".into());
            }
            let (s, q, why) = if input.0 < self.base {
                let n = self.g.get(*input)?;
                (&n.support, &n.scope, &n.reasons)
            } else {
                let p = &self.parts[input.0 - self.base];
                (&p.support, &p.scope, &p.reasons)
            };
            support.extend(s.iter().cloned());
            scope.merge(q);
            reasons.extend(why.iter().cloned());
        }
        support.sort();
        support.dedup();
        sort_reasons(&mut reasons);
        let judgment = decision.map(|status| Judgment {
            status,
            evidence: vec![],
            reasons: reasons.clone(),
        });
        self.parts.push(Part {
            ty,
            construction,
            wire,
            arguments,
            support,
            scope,
            reasons,
            judgment,
            evidence: vec![],
            scalar,
        });
        Ok(r)
    }
    fn expression(
        &mut self,
        operation: &str,
        operands: Vec<NodeRef>,
        bs: &[Binding],
    ) -> Result<NodeRef, ValidationFailure> {
        let mut args = operands.clone();
        args.extend(bs.iter().map(|b| b.value));
        self.push(
            NodeType::Expression(Type::Bool),
            "expression",
            Json::obj([
                ("kind", Json::str("transform")),
                ("operation", Json::str(operation)),
                ("operands", refs(&operands)),
                ("parameters", Json::Arr(vec![])),
                ("bindings", bindings(bs)),
            ]),
            args,
            None,
            None,
        )
    }
    pub(super) fn proposition(
        &mut self,
        predicate: &str,
        operands: Vec<NodeRef>,
        mut arguments: Vec<NodeRef>,
        status: Decision,
    ) -> Result<NodeRef, ValidationFailure> {
        arguments.extend(operands.iter().copied());
        let r = self.push(
            NodeType::Proposition,
            "proposition",
            Json::Arr(vec![]),
            arguments,
            None,
            Some(status),
        )?;
        let p = &mut self.parts[r.0 - self.base];
        p.wire = Json::obj([
            ("predicate", Json::str(predicate)),
            ("operands", refs(&operands)),
            (
                "quantifiers",
                Json::Arr(p.scope.quantifiers.iter().map(Quantifier::wire).collect()),
            ),
        ]);
        Ok(r)
    }
}

fn compute(
    env: &Environment<'_>,
    g: &Graph,
    plan: &Plan,
    base: usize,
    request: &Request,
    c: &mut Control,
) -> Result<(Vec<Part>, Answer), ValidationFailure> {
    env.validation_graph_session(g, || compute_inner(env, g, plan, base, request, c))
}

fn compute_inner(
    env: &Environment<'_>,
    g: &Graph,
    plan: &Plan,
    base: usize,
    request: &Request,
    c: &mut Control,
) -> Result<(Vec<Part>, Answer), ValidationFailure> {
    tick(c)?;
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let mut dependencies = plan.boundary.inputs().to_vec();
    let mut status = Decision::Established;
    let mut reasons = plan.architecture.reasons.clone();
    // 必要な読取りの欠測は、Lawが同じslotを読むか・同pattern対があるかに
    // 依存しない。viewや操作も含む全入力の理由を、成立判定より前に集める。
    for dependency in &dependencies {
        tick(c)?;
        reasons.extend(g.get(*dependency)?.reasons.iter().cloned());
    }
    if let Some(table) = &plan.laws {
        reasons.extend(table.reasons.iter().cloned());
    }
    if let Some(layout) = &plan.polynomial {
        reasons.extend(layout.data.reasons.iter().cloned());
    }
    // 多項式表示が明示的に算法非対応で、有限表示も得られない場合を配送する。
    // 未完成の全般を非対応へ置き換えず、元の出現と型を保持する。
    if plan.equations.is_none() && plan.finite.is_none() {
        if let Some(table) = &plan.laws {
            for diagram in table.diagrams()? {
                for coordinate in &diagram.coordinates {
                    tick(c)?;
                    if coordinate.status != super::object_equation_presentation::EquationPresentationStatus::UnsupportedAlgorithm {
                        continue;
                    }
                    let original = diagram.originals.iter().find(|o| o.reference == coordinate.instance)
                        .ok_or("非対応方程式の元Lawがない")?;
                    let origin = super::law_evaluation::origin(g, original.reference)?
                        .ok_or("非対応方程式の宣言がない")?;
                    let declaration = env.inputs.law().declarations.get(&origin.declaration)
                        .ok_or("非対応方程式の宣言が現在の入力にない")?;
                    let crate::law::model::Signature::Law { body, .. } = declaration.signature else {
                        return Err("非対応方程式の元宣言がLawでない".into());
                    };
                    let mut body = body;
                    while let crate::law::ast::ExprKind::Group(inner) = env.inputs.law().exprs[body].kind {
                        tick(c)?;
                        body = inner;
                    }
                    let crate::law::ast::ExprKind::Binary {
                        op: crate::law::ast::BinOp::Lt | crate::law::ast::BinOp::Le
                            | crate::law::ast::BinOp::Gt | crate::law::ast::BinOp::Ge,
                        lhs, rhs,
                    } = env.inputs.law().exprs[body].kind else { continue; };
                    // Z上の順序述語は多項式等式でも全operand有限域でもない。
                    // 有限Bool域の欠測などを算法非対応へ変換しない。
                    if env.inputs.law().expr_types[lhs].as_ref() != Some(&Type::Z)
                        || env.inputs.law().expr_types[rhs].as_ref() != Some(&Type::Z) {
                        continue;
                    }
                    let mut dependencies = vec![original.body];
                    dependencies.extend(original.guard);
                    dependencies.sort_by_key(|r| r.0);
                    dependencies.dedup();
                    reasons.push(Reason {
                        kind: ReasonKind::UnsupportedAlgorithm {
                            question: super::request::QuestionKind::Build,
                            operand_types: vec![Type::Z, Type::Z],
                            method: "integer_order_equation_presentation".into(),
                        },
                        request: request.id.clone(), dependencies, missing: vec![], location: None,
                    });
                }
            }
        }
    }
    let mut compatibility = vec![];
    let mut evidence = vec![];
    let mut failed_conditions = vec![];
    let mut circuits = vec![];
    let ready = plan.equations.is_some() && plan.objects.is_some() && plan.patterns.is_some();
    if ready {
        for comparison in build_compare::compare(env, g, plan, c)? {
            tick(c)?;
            let patterns = plan.patterns.as_ref().unwrap();
            let pattern = |object| {
                patterns
                    .rows
                    .iter()
                    .find(|p| p.object == object)
                    .map(|p| p.pattern)
                    .ok_or("build互換性の対象patternがない")
            };
            let s = match comparison.equal {
                Some(true) => Decision::Established,
                Some(false) => Decision::Refuted,
                None => Decision::Undetermined,
            };
            if s == Decision::Refuted {
                status = s;
            } else if s == Decision::Undetermined && status != Decision::Refuted {
                status = s;
            }
            let mut inputs = comparison.inputs;
            let counterexample = if s == Decision::Refuted {
                let facts = inputs
                    .iter()
                    .map(|r| g.get(*r))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flat_map(|n| n.support.iter().cloned())
                    .collect::<std::collections::BTreeSet<_>>();
                let proof = b.push(
                    NodeType::Evidence,
                    "evidence",
                    Json::obj([
                        ("kind", Json::str("counterexample")),
                        (
                            "data",
                            Json::obj([
                                ("bindings", Json::Arr(vec![])),
                                ("paths", Json::Arr(vec![])),
                                ("left", comparison.source.wire()),
                                ("right", comparison.target.wire()),
                                ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                            ]),
                        ),
                    ]),
                    inputs.clone(),
                    None,
                    None,
                )?;
                inputs.push(proof);
                evidence.push(proof);
                Some(proof)
            } else {
                None
            };
            let condition = b.proposition(
                "profile_compatible",
                vec![
                    comparison.source,
                    comparison.target,
                    pattern(comparison.source)?,
                    pattern(comparison.target)?,
                ],
                inputs,
                s,
            )?;
            if let Some(proof) = counterexample {
                let p = &mut b.parts[condition.0 - base];
                p.evidence.push(proof);
                p.judgment
                    .as_mut()
                    .ok_or("互換性命題の判断がない")?
                    .evidence
                    .push(proof);
            }
            compatibility.push(condition);
            if s == Decision::Refuted {
                failed_conditions.push(condition);
            }
        }
        let Some(detectors) = build_circuit_plan::closed(env, g, plan, c)? else {
            return Err("buildの未束縛parameterまたは非定数残差のcircuit配送は未実装".into());
        };
        for detector in detectors {
            tick(c)?;
            let mut cases = vec![];
            for case in detector.cases {
                let equal = b.expression("equal", vec![case.lhs, case.rhs], &case.bindings)?;
                let when = b.expression("not", vec![equal], &case.bindings)?;
                let value = b.push(
                    NodeType::Value(Type::Bool),
                    "binding",
                    Json::Bool(case.when),
                    vec![case.epsilon, case.evaluation],
                    Some(Scalar::Bool(case.when)),
                    None,
                )?;
                let evaluation = b.push(
                    NodeType::Evaluation(Type::Bool),
                    "evaluation",
                    Json::obj([
                        ("expression", when.wire()),
                        ("bindings", bindings(&case.bindings)),
                        ("environment", case.architecture.wire()),
                        ("value", value.wire()),
                        ("applicability", Json::str("applicable")),
                        (
                            "parts",
                            Json::Arr(vec![Json::obj([
                                ("location", crate::result::location_wire(&case.location)),
                                ("children", refs(&[case.evaluation])),
                                ("residual", case.epsilon.wire()),
                            ])]),
                        ),
                    ]),
                    vec![
                        when,
                        value,
                        case.architecture,
                        case.evaluation,
                        case.epsilon,
                    ],
                    None,
                    None,
                )?;
                let soundness = b.proposition(
                    "circuit_sound",
                    vec![case.pattern, when, case.lhs, case.rhs],
                    vec![evaluation, case.epsilon, case.object],
                    Decision::Established,
                )?;
                cases.push(b.push(
                    NodeType::Construction(T::CircuitCase),
                    "circuit_case",
                    Json::obj([
                        ("object", case.object.wire()),
                        ("index", case.index.wire()),
                        ("component", path(&case.component)),
                        ("pattern", case.pattern.wire()),
                        ("when", when.wire()),
                        ("refutation", evaluation.wire()),
                        ("soundness", soundness.wire()),
                    ]),
                    vec![
                        case.object,
                        case.index,
                        case.pattern,
                        when,
                        evaluation,
                        soundness,
                    ],
                    None,
                    None,
                )?);
            }
            let mut args = cases.clone();
            args.push(detector.index);
            circuits.push(b.push(
                NodeType::Construction(T::CircuitDetector),
                "circuit_detector",
                Json::obj([
                    ("index", detector.index.wire()),
                    ("component", path(&detector.component)),
                    ("parameters", Json::Arr(vec![])),
                    ("cases", refs(&cases)),
                ]),
                args,
                None,
                None,
            )?);
        }
    } else {
        status = Decision::Undetermined;
    }
    if let Some(arrows) = &plan.arrows {
        evidence.extend(arrows.rows.iter().flat_map(|r| r.evidence.iter().copied()));
        if !arrows.all_preserved {
            if arrows
                .rows
                .iter()
                .any(|r| r.operation.is_none() && r.missing.is_empty())
            {
                status = Decision::Refuted;
            } else if status != Decision::Refuted {
                status = Decision::Undetermined;
            }
        }
    } else if status != Decision::Refuted {
        status = Decision::Undetermined;
    }
    if let Some(views) = &plan.views {
        if !views.pending.is_empty() {
            return Err("buildの非有限view全域配送は未実装".into());
        }
    }
    sort_reasons(&mut reasons);
    if !reasons.is_empty() && status == Decision::Established {
        status = Decision::Undetermined;
    }
    if status == Decision::Undetermined && reasons.is_empty() {
        return Err("buildの構成に必要な配送が未実装で、数学的未決の理由ではない".into());
    }
    dependencies.extend(compatibility.iter().copied());
    dependencies.extend(circuits.iter().copied());
    let label = b.push(
        NodeType::Value(Type::Text),
        "binding",
        Json::str("object_algebra"),
        vec![plan.architecture.reference],
        Some(Scalar::Text("object_algebra".into())),
        None,
    )?;
    let mut operands = vec![label];
    operands.extend(dependencies.iter().copied());
    if status == Decision::Refuted && failed_conditions.is_empty() {
        failed_conditions.push(b.proposition(
            "constructible",
            operands.clone(),
            dependencies.clone(),
            status,
        )?);
    }
    for condition in &failed_conditions {
        reasons.push(Reason {
            kind: ReasonKind::ConditionFailed {
                condition: *condition,
                construction: "object_algebra",
            },
            request: request.id.clone(),
            dependencies: vec![*condition],
            missing: vec![],
            location: None,
        });
    }
    dependencies.extend(failed_conditions);
    dependencies.extend(evidence.iter().copied());
    let claim = b.proposition("constructible", operands, dependencies.clone(), status)?;
    // neededと回答は、構成命題に保持した同じ理由を読む。
    let proposition = &mut b.parts[claim.0 - base];
    proposition.evidence = evidence.clone();
    proposition
        .judgment
        .as_mut()
        .ok_or("build構成命題に判断がない")?
        .evidence = evidence.clone();
    proposition.reasons.extend(reasons);
    proposition.reasons.sort_by_key(|r| r.wire().canonical());
    sort_reasons(&mut proposition.reasons);
    let reasons = proposition.reasons.clone();
    proposition
        .judgment
        .as_mut()
        .ok_or("build構成命題に判断がない")?
        .reasons = reasons.clone();
    let mut outputs = BTreeMap::from([("proposition".into(), claim)]);
    if plan.architecture.complete {
        outputs.insert("object".into(), plan.architecture.reference);
    }
    if status == Decision::Established {
        let objects = plan.objects.as_ref().ok_or("buildの全対象がない")?;
        let patterns = plan.patterns.as_ref().ok_or("buildの全patternがない")?;
        let views = plan.views.as_ref().ok_or("buildの全viewがない")?;
        let arrows = plan.arrows.as_ref().ok_or("buildの内部操作がない")?;
        let equations = plan.equations.ok_or("buildの方程式族がない")?;
        let generators = arrows
            .rows
            .iter()
            .map(|r| r.operation)
            .collect::<Option<Vec<_>>>()
            .ok_or("buildの全内部操作が保存済みでない")?;
        let invariants = views
            .axes
            .iter()
            .map(|r| r.invariant)
            .chain(plan.predicates.iter().map(|r| r.invariant))
            .collect::<Vec<_>>();
        let signature = views.axes.iter().map(|r| r.signature).collect::<Vec<_>>();
        dependencies.push(claim);
        let algebra = b.push(
            NodeType::Construction(T::ObjectAlgebra),
            "object_algebra",
            Json::obj([
                ("universe", plan.architecture.universe.wire()),
                ("objects", refs(&objects.objects)),
                ("base", objects.base.wire()),
                (
                    "extension",
                    Json::obj([
                        ("kind", Json::str("finite_pattern")),
                        (
                            "profiles",
                            Json::Arr(
                                patterns
                                    .rows
                                    .iter()
                                    .map(|r| {
                                        Json::obj([
                                            ("object", r.object.wire()),
                                            ("pattern", r.pattern.wire()),
                                        ])
                                    })
                                    .collect(),
                            ),
                        ),
                        ("compatibility", refs(&compatibility)),
                    ]),
                ),
                ("equations", equations.wire()),
                ("circuits", refs(&circuits)),
                (
                    "operations",
                    Json::obj([
                        ("kind", Json::str("typed_free_words")),
                        ("generators", refs(&generators)),
                    ]),
                ),
                ("invariants", refs(&invariants)),
                ("signature", refs(&signature)),
            ]),
            dependencies,
            None,
            None,
        )?;
        outputs.insert("algebra".into(), algebra);
    }
    let scope = b.parts[claim.0 - base].scope.clone();
    Ok((
        b.parts,
        Answer {
            id: request.id.clone(),
            status,
            outputs,
            claim: Some(claim),
            evidence,
            reasons,
            scope,
        },
    ))
}

pub(super) fn evaluate(
    prepared: &PreparedObserved,
    env: &Environment<'_>,
    g: &mut Graph,
    request: &Request,
    c: &mut Control,
) -> Result<Answer, ValidationFailure> {
    match evaluate_inner(prepared, env, g, request, c) {
        Err(ValidationFailure::Stop(stop)) => {
            let mut outputs = BTreeMap::new();
            let mut scope = Scope::default();
            for (index, node) in g.nodes.iter().enumerate() {
                if let Some(Payload::Construction(v)) = &node.payload
                    && v.witness.request() == request
                    && matches!(v.data, D::Architecture { .. })
                {
                    outputs.insert("object".into(), NodeRef(index));
                    scope.merge(&node.scope);
                }
            }
            Ok(Answer {
                id: request.id.clone(),
                status: Decision::Undetermined,
                outputs,
                claim: None,
                evidence: vec![],
                reasons: vec![Reason::stopped(&request.id, stop)],
                scope,
            })
        }
        other => other,
    }
}
fn evaluate_inner(
    prepared: &PreparedObserved,
    env: &Environment<'_>,
    g: &mut Graph,
    request: &Request,
    c: &mut Control,
) -> Result<Answer, ValidationFailure> {
    if let Some(answer) = super::public_map::unavailable(env, g, request)? {
        return Ok(answer);
    }
    let plan = build_plan::prepare(env, g, prepared.shared_inputs(), request, c)?;
    retain_plan(env, g, plan, request, c)
}

pub(super) fn retain_plan(
    env: &Environment<'_>,
    g: &mut Graph,
    plan: Plan,
    request: &Request,
    c: &mut Control,
) -> Result<Answer, ValidationFailure> {
    let base = g.nodes.len();
    let (parts, answer) = compute(env, g, &plan, base, request, c)?;
    let source = Arc::new(Source {
        plan,
        base,
        parts,
        answer,
    });
    for index in 0..source.parts.len() {
        tick(c)?;
        let p = &source.parts[index];
        native::retain(
            g,
            ConstructionValue {
                witness: Witness::Architecture(source.plan.architecture.witness.clone()),
                data: D::Build(Data {
                    source: source.clone(),
                    index,
                }),
            },
            p.reasons.clone(),
            p.evidence.clone(),
            p.judgment.clone(),
        )?;
    }
    Ok(source.answer.clone())
}

pub(super) fn validate_node(
    g: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let Witness::Architecture(a) = &v.witness else {
        return Err("buildの元Architectureがない".into());
    };
    let p = d.part();
    if !Arc::ptr_eq(a, &d.source.plan.architecture.witness)
        || !Arc::ptr_eq(
            a,
            native::architecture_origin(g, d.source.plan.architecture.reference, 0)?,
        )
        || n.ty != p.ty
        || n.rule != Rule::Construction(p.construction)
        || n.arguments != p.arguments
        || n.support != p.support
        || n.scope != p.scope
        || n.reasons != p.reasons
        || n.judgment != p.judgment
        || n.evidence != p.evidence
    {
        return Err("buildの元構成/型/辺/判断/metadataが違う".into());
    }
    for r in &p.arguments {
        g.get(*r)?;
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_build(
        &self,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        let D::Build(d) = &v.data else {
            return Ok(());
        };
        d.position(at)?;
        let mut c = self.control.clone();
        d.source.plan.boundary.recheck(self, g, at, &mut c)?;
        if self.build_source_checked(&d.source) {
            return Ok(());
        }
        let producer = g.context_at(d.source.plan.architecture.reference.0).request;
        let request = g.requests.get(producer).ok_or("buildの元Requestがない")?;
        let (parts, answer) = compute(self, g, &d.source.plan, d.source.base, request, &mut c)?;
        if parts != d.source.parts || answer != d.source.answer {
            return Err("buildの全構成が元計画の再検査と違う".into());
        }
        self.remember_build_source(d.source.clone());
        Ok(())
    }
}
pub(super) fn validate_answer(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    answer: &Answer,
) -> Result<(), ValidationFailure> {
    if let Some(expected) = super::public_map::unavailable(env, g, request)? {
        return if answer == &expected {
            Ok(())
        } else {
            Err("buildの依存停止回答が元理由と違う".into())
        };
    }
    let r = answer.claim.ok_or("buildの構成命題がない")?;
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("build命題がnativeでない".into());
    };
    let D::Build(d) = &v.data else {
        return Err("build命題が別構成".into());
    };
    super::architecture_result::validate_build_origin(env, g, request, v)?;
    env.recheck_build(g, v, r.0)?;
    if answer != &d.source.answer {
        return Err("build回答が元構成と違う".into());
    }
    Ok(())
}

pub(super) fn validate_failure(g: &Graph, reason: &Reason) -> Result<(), ValidationFailure> {
    let ReasonKind::ConditionFailed {
        condition,
        construction: "object_algebra",
    } = reason.kind
    else {
        return Err("buildの構成条件失敗が別種".into());
    };
    let node = g.get(condition)?;
    let Some(Payload::Construction(v)) = &node.payload else {
        return Err("buildの条件命題がnativeでない".into());
    };
    let D::Build(d) = &v.data else {
        return Err("buildの条件命題が別構成".into());
    };
    if node.ty != NodeType::Proposition
        || node.judgment.as_ref().map(|j| j.status) != Some(Decision::Refuted)
        || v.witness.request().id != reason.request
        || reason.dependencies != [condition]
        || !reason.missing.is_empty()
    {
        return Err("buildの構成反証と元理由が違う".into());
    }
    validate_node(g, node, v, d)
}
