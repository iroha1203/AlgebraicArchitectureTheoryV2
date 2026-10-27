//! 原始対応の全対象・全生成元の保存を公開ObjectAlgebraMapへ配送する。
use super::{
    PreparedObserved,
    architecture_result::Architecture,
    build_plan, build_result,
    build_result::{Builder, Part},
    construction_result::{
        self as native, ConstructionData as D, ConstructionType as T, ConstructionValue,
        MapWitness, Witness,
    },
    control::{Checkpoint, Control},
    environment::Environment,
    native_source::Boundary,
    projection::{ProjectionStep, ProjectionType},
    request::Request,
    result::*,
};
use crate::{
    canonical::Json,
    construction::{ConstructionFailure, maps as construction},
    definition::PrimitiveSignature,
};
use std::sync::Arc;
#[path = "object_declaration_transport.rs"]
mod declaration_transport;

fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ConfigurationTransport)?;
    Ok(())
}
fn failure(e: ConstructionFailure) -> ValidationFailure {
    match e {
        ConstructionFailure::Stopped(s) => s.into(),
        e => format!("ObjectAlgebra map: {e:?}").into(),
    }
}

#[derive(Debug)]
pub(super) struct Source {
    witness: Arc<MapWitness>,
    configuration: Answer,
    algebras: Option<[NodeRef; 2]>,
    pending: Option<[NodeRef; 2]>,
    boundary: Boundary,
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
    pub(super) fn scope_domain_type(&self) -> Option<&crate::types::Type> {
        if self.part().ty == NodeType::Domain { self.part().domain_type.as_ref() } else { None }
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
    pub(super) fn conditions(&self) -> Vec<NodeRef> {
        if !matches!(
            self.ty(),
            NodeType::Construction(
                T::ConfigurationMap
                    | T::ObjectAlgebraMap
                    | T::EquationMap
                    | T::CircuitMap
                    | T::InvariantMap
                    | T::SignatureMap
                    | T::ValueEquivalence
            )
        ) {
            return vec![];
        }
        self.part()
            .arguments
            .iter()
            .copied()
            .filter(|r| {
                r.0 >= self.source.base
                    && self
                        .source
                        .parts
                        .get(r.0 - self.source.base)
                        .is_some_and(|p| p.ty == NodeType::Proposition)
            })
            .collect()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.part().support.clone(), self.part().scope.clone())
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        self.part().scalar.as_ref()
    }
    pub(super) fn projection_type(&self) -> Option<ProjectionType> {
        (self.ty() == NodeType::Construction(T::ObjectAlgebraMap))
            .then(|| ProjectionType::ObjectAlgebraMap(self.source.witness.shape().clone()))
    }
    pub(super) fn project(&self, path: &[ProjectionStep]) -> Option<(NodeRef, usize)> {
        if self.ty() != NodeType::Construction(T::ObjectAlgebraMap) {
            return None;
        }
        let ProjectionStep::Field(f) = path.first()? else {
            return None;
        };
        let [a, b] = self.source.algebras?;
        match f.as_str() {
            "source" => Some((a, 1)),
            "target" => Some((b, 1)),
            "configuration_map" => Some((*self.source.configuration.outputs.get("map")?, 1)),
            _ => None,
        }
    }
    fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if self.index >= self.source.parts.len()
            || at != self.source.base + self.index
            || self.arguments().iter().any(|r| r.0 >= at)
        {
            return Err("ObjectAlgebra mapの位置/既出参照が違う".into());
        }
        Ok(())
    }
}
fn plan(g: &Graph, r: NodeRef) -> Result<&build_plan::Plan, ValidationFailure> {
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("移送先のalgebraがnativeでない".into());
    };
    let D::Build(d) = &v.data else {
        return Err("移送先のalgebraに元buildがない".into());
    };
    g.expect(r, &NodeType::Construction(T::ObjectAlgebra))?;
    Ok(d.plan())
}
fn retained_architecture(g: &Graph, r: NodeRef) -> Result<Architecture, ValidationFailure> {
    let witness = native::architecture_origin(g, r, 0)?.clone();
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("Architectureがnativeでない".into());
    };
    let D::Architecture { root, .. } = v.data else {
        return Err("mapの端点Architectureが未完成".into());
    };
    let universe = g.nodes.iter().enumerate().find_map(|(i,n)| match &n.payload {
        Some(Payload::Construction(v)) if matches!(&v.data,D::AtomUniverse(xs) if xs==witness.construction().universe()) => Some(NodeRef(i)), _=>None,
    }).ok_or("元ArchitectureのUがない")?;
    Ok(Architecture {
        witness,
        reference: r,
        root,
        universe,
        complete: true,
        reasons: vec![],
    })
}
pub(super) fn extend(
    prepared: &PreparedObserved,
    env: &Environment<'_>,
    g: &mut Graph,
    request: &Request,
    configuration: Answer,
    c: &mut Control,
) -> Result<Answer, ValidationFailure> {
    let candidate = configuration.outputs["candidate"];
    let Some(Payload::Construction(v)) = &g.get(candidate)?.payload else {
        return Err("元候補がnativeでない".into());
    };
    let Witness::Map(witness) = &v.witness else {
        return Err("元候補のmap検査がない".into());
    };
    let witness = witness.clone();
    let D::MapCandidate { source, target, .. } = v.data else {
        return Err("元候補が未完成".into());
    };
    let declarations = construction::declaration_correspondence(
        prepared.inputs(),
        witness.result().map().ok_or("元ConfigurationMapがない")?,
        c,
    )
    .map_err(failure)?;
    let mut pending = None;
    let algebras = if declarations.all_signatures_compatible() {
        // local/change/relationには句の移送配送も必要。
        // 未対応の宣言を空の表へ置換しない。
        if declarations
            .candidates()
            .iter()
            .any(|d| !matches!(d.source().kind, "law" | "view" | "local" | "change" | "relation"))
        {
            return Err("ObjectAlgebra mapの読取り宣言移送配送は未実装".into());
        }
        let mut result = vec![];
        let mut claims = vec![];
        for endpoint in [source, target] {
            tick(c)?;
            let architecture = retained_architecture(g, endpoint)?;
            let plan = build_plan::prepare_architecture(
                env,
                g,
                prepared.shared_inputs(),
                architecture,
                c,
            )?;
            let answer = build_result::retain_plan(env, g, plan, request, c)?;
            claims.push(answer.claim.ok_or("端点buildの構成命題がない")?);
            result.extend(answer.outputs.get("algebra").copied());
        }
        if result.len() == 2 {
            Some([result[0], result[1]])
        } else {
            pending = Some([claims[0], claims[1]]);
            None
        }
    } else {
        None
    };
    let mut dependencies = configuration.outputs.values().copied().collect::<Vec<_>>();
    dependencies.extend(algebras.into_iter().flatten());
    dependencies.extend(pending.into_iter().flatten());
    let boundary = Boundary::capture(env, g, source, dependencies, c)?;
    let base = g.nodes.len();
    let (parts, answer) = compute(
        env, g, &witness, &configuration, algebras, pending, base, request, c,
    )?;
    let source = Arc::new(Source {
        witness,
        configuration,
        algebras,
        pending,
        boundary,
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
                witness: Witness::Map(source.witness.clone()),
                data: D::ObjectMap(Data {
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

fn compute(
    env: &Environment<'_>,
    g: &Graph,
    witness: &Arc<MapWitness>,
    configuration: &Answer,
    algebras: Option<[NodeRef; 2]>,
    pending: Option<[NodeRef; 2]>,
    base: usize,
    request: &Request,
    c: &mut Control,
) -> Result<(Vec<Part>, Answer), ValidationFailure> {
    env.validation_graph_session(g, || {
        compute_inner(
            env, g, witness, configuration, algebras, pending, base, request, c,
        )
    })
}

fn compute_inner(
    env: &Environment<'_>,
    g: &Graph,
    witness: &Arc<MapWitness>,
    configuration: &Answer,
    algebras: Option<[NodeRef; 2]>,
    pending: Option<[NodeRef; 2]>,
    base: usize,
    request: &Request,
    c: &mut Control,
) -> Result<(Vec<Part>, Answer), ValidationFailure> {
    tick(c)?;
    let origin = Witness::Map(witness.clone());
    let inputs = origin.inputs();
    let map = witness
        .result()
        .map()
        .ok_or("移送元ConfigurationMapがない")?;
    let declarations =
        construction::declaration_correspondence(&inputs, map, c).map_err(failure)?;
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let candidate = configuration.outputs["candidate"];
    let mut dependencies = configuration.outputs.values().copied().collect::<Vec<_>>();
    let mut outputs = configuration.outputs.clone();
    outputs.remove("map");
    let mut object_rows = vec![];
    let mut operation_rows = vec![];
    let mut declaration_rows = vec![];
    let mut equation_map = None;
    let mut signature = None;
    let mut circuit_maps = vec![];
    let mut invariant_maps = vec![];
    let mut declaration_transports = vec![];
    let mut declaration_status = Decision::Established;
    let mut declaration_reasons = vec![];
    let mut declaration_evidence = vec![];
    let mut preserved = declarations.all_signatures_compatible();
    if let Some(claims) = pending {
        let Some(Payload::Construction(candidate)) = &g.get(candidate)?.payload else {
            return Err("元候補がnativeでない".into());
        };
        let D::MapCandidate { source, target, .. } = candidate.data else {
            return Err("元候補の端点がない".into());
        };
        let mut incomplete = false;
        for (claim, expected) in claims.into_iter().zip([source, target]) {
            tick(c)?;
            let Some(Payload::Construction(value)) = &g.get(claim)?.payload else {
                return Err("端点buildの命題がnativeでない".into());
            };
            let D::Build(data) = &value.data else {
                return Err("端点buildの命題が別種".into());
            };
            if data.plan().architecture.reference != expected || data.answer().claim != Some(claim) {
                return Err("端点buildの元Architectureまたは命題が違う".into());
            }
            env.recheck_build(g, value, claim.0)?;
            let endpoint = data.answer();
            incomplete |= !endpoint.outputs.contains_key("algebra");
            declaration_status = if declaration_status == Decision::Refuted
                || endpoint.status == Decision::Refuted
            {
                Decision::Refuted
            } else if endpoint.status == Decision::Undetermined {
                Decision::Undetermined
            } else {
                declaration_status
            };
            dependencies.extend(endpoint.outputs.values().copied());
            dependencies.push(claim);
            declaration_reasons.extend(endpoint.reasons.iter().cloned());
            declaration_evidence.extend(endpoint.evidence.iter().copied());
        }
        if !incomplete || declaration_status == Decision::Established || algebras.is_some() {
            return Err("未完成端点の判断が違う".into());
        }
        sort_reasons(&mut declaration_reasons);
        declaration_evidence.sort_by_key(|r| r.0);
        declaration_evidence.dedup();
    }
    if preserved && pending.is_none() {
        if declarations
            .candidates()
            .iter()
            .any(|d| !matches!(d.source().kind, "law" | "view" | "local" | "change" | "relation"))
        {
            return Err("ObjectAlgebra mapの読取り宣言配送は未実装".into());
        }
        let [left, right] = algebras.ok_or("ObjectAlgebra mapの端点がない")?;
        dependencies.extend([left, right]);
        let a = plan(g, left)?;
        let z = plan(g, right)?;
        let transport = construction::configuration_transport(&inputs, map, c)
            .map_err(|e| failure(e.cause().clone()))?;
        preserved = transport.all_preserved();
        if !preserved
            && !transport
                .objects()
                .iter()
                .any(|r| r.condition_failure().is_some())
            && !transport
                .generators()
                .iter()
                .any(|r| r.condition_failure().is_some())
        {
            return Err("ObjectAlgebra mapの保存反例配送は未実装".into());
        }
        if preserved {
            let ao = a.objects.as_ref().ok_or("元対象族がない")?;
            let zo = z.objects.as_ref().ok_or("先対象族がない")?;
            let aa = a.arrows.as_ref().ok_or("元生成元族がない")?;
            let za = z.arrows.as_ref().ok_or("先生成元族がない")?;
            if transport.objects().len() != ao.objects.len()
                || transport.generators().len() != aa.rows.len()
            {
                return Err("全対象・全生成元の移送表が一致しない".into());
            }
            let mut target_subjects = vec![transport.target().construction().root()];
            target_subjects.extend(
                transport
                    .target()
                    .construction()
                    .components()
                    .iter()
                    .map(|v| v.subject()),
            );
            let Some(Payload::Construction(cv)) = &g.get(candidate)?.payload else {
                return Err("元候補がない".into());
            };
            let D::MapCandidate {
                subject, action, ..
            } = cv.data
            else {
                return Err("元候補の作用がない".into());
            };
            for (i, row) in transport.objects().iter().enumerate() {
                tick(c)?;
                let target = row.target().ok_or("保存済み対象の像がない")?;
                let j = target_subjects
                    .iter()
                    .position(|s| **s == *target.subject())
                    .ok_or("対象像が終域にない")?;
                let object_map = if i == 0 {
                    configuration.outputs["map"]
                } else {
                    let mc = b.push(
                        NodeType::Construction(T::MapCandidate),
                        "map_candidate",
                        Json::obj([
                            ("declaration", Json::str(&witness.shape().declaration)),
                            ("subject", subject.wire()),
                            ("source", ao.architectures[i].wire()),
                            ("target", zo.architectures[j].wire()),
                            ("action", action.wire()),
                        ]),
                        vec![subject, ao.architectures[i], zo.architectures[j], action],
                        None,
                        None,
                    )?;
                    let proof = b.proposition(
                        "configuration_preserved",
                        vec![mc],
                        vec![],
                        Decision::Established,
                    )?;
                    b.push(
                        NodeType::Construction(T::ConfigurationMap),
                        "configuration_map",
                        Json::obj([("candidate", mc.wire())]),
                        vec![mc, proof],
                        None,
                        None,
                    )?
                };
                dependencies.push(object_map);
                object_rows.push(Json::obj([
                    ("source", ao.objects[i].wire()),
                    ("target", zo.objects[j].wire()),
                    ("map", object_map.wire()),
                ]));
                dependencies.extend([ao.objects[i], zo.objects[j]]);
            }
            let mu = map.candidate();
            for (i, row) in transport.generators().iter().enumerate() {
                tick(c)?;
                let j = transport
                    .target()
                    .arrows()
                    .iter()
                    .position(|r| r.arrow() == row.target())
                    .ok_or("生成元像が終域にない")?;
                let e = transport.source().arrows()[i]
                    .map()
                    .ok_or("元生成元の保存がない")?
                    .candidate();
                let f = transport.target().arrows()[j]
                    .map()
                    .ok_or("先生成元の保存がない")?
                    .candidate();
                let compose = |first: &construction::MapCandidate,
                               second: &construction::MapCandidate,
                               c: &mut Control|
                 -> Result<Vec<Fact>, ValidationFailure> {
                    let mut action = std::collections::BTreeMap::new();
                    for (subject, image) in second.universe().iter().zip(second.images()) {
                        tick(c)?;
                        action.insert(subject, image);
                    }
                    let mut images = vec![];
                    for subject in first.images() {
                        tick(c)?;
                        images
                            .push((*action.get(subject).ok_or("総写像の合成位置がない")?).clone());
                    }
                    Ok(images)
                };
                let mut maps = vec![];
                let source_op = aa.rows[i].operation.ok_or("元生成元Operationがない")?;
                let target_op = za.rows[j].operation.ok_or("先生成元Operationがない")?;
                for images in [compose(e, mu, c)?, compose(mu, f, c)?] {
                    tick(c)?;
                    maps.push(b.push(
                        NodeType::Construction(T::AtomMap),
                        "atom_map",
                        Json::obj([
                            ("universe", a.architecture.universe.wire()),
                            ("images", Json::Arr(images.iter().map(Fact::wire).collect())),
                        ]),
                        vec![a.architecture.universe, action, source_op, target_op],
                        None,
                        None,
                    )?);
                }
                let naturality =
                    b.proposition("naturality", maps, vec![], Decision::Established)?;
                dependencies.extend([source_op, target_op, naturality]);
                operation_rows.push(Json::obj([
                    ("source", source_op.wire()),
                    ("target", target_op.wire()),
                    ("naturality", naturality.wire()),
                ]));
            }
            let def = inputs
                .definitions()
                .declarations
                .get(&witness.shape().declaration)
                .ok_or("原始対応の定義がない")?;
            let PrimitiveSignature::Correspondence {
                alignments,
                implicit,
                ..
            } = &def.signature
            else {
                return Err("原始対応の定義型が違う".into());
            };
            for (source, target) in declarations.types() {
                tick(c)?;
                let parameters = |name: &str| -> Result<_, ValidationFailure> {
                    let d = inputs
                        .definitions()
                        .declarations
                        .get(name)
                        .ok_or("対応型の定義がない")?;
                    let (parameters, _) = d
                        .signature
                        .record_fields()
                        .ok_or("対応型が原始recordでない")?;
                    Ok(parameters)
                };
                let sp = parameters(source)?;
                let tp = parameters(target)?;
                if sp.len() != tp.len() {
                    return Err("原始宣言parameter対応の配送は未実装".into());
                }
                let parameters = sp
                    .iter()
                    .zip(tp)
                    .map(|(s, t)| Json::Arr(vec![Json::str(&s.name), Json::str(&t.name)]))
                    .collect();
                let mut fields = alignments
                    .iter()
                    .map(|a| (&a.source, &a.target))
                    .chain(implicit.iter().map(|(s, t)| (s, t)))
                    .filter(|(s, _)| s.rsplit_once('.').is_some_and(|(owner, _)| owner == source))
                    .map(|(s, t)| Json::Arr(vec![Json::str(s), Json::str(t)]))
                    .collect::<Vec<_>>();
                fields.sort_by_key(Json::canonical);
                declaration_rows.push(Json::obj([
                    ("source", Json::str(source)),
                    ("target", Json::str(target)),
                    ("parameters", Json::Arr(parameters)),
                    ("fields", Json::Arr(fields)),
                ]));
            }
            let se = a.equations.ok_or("元方程式族がない")?;
            let te = z.equations.ok_or("先方程式族がない")?;
            let laws = super::object_law_map::retain(
                env,
                &mut b,
                &origin.shared_inputs(),
                &declarations,
                [left, right],
                [a, z],
                c,
            )?;
            preserved &= laws.preserved;
            declaration_rows.extend(laws.declarations);
            circuit_maps = laws.circuits;
            invariant_maps = laws.invariants;
            dependencies.extend(laws.conditions);
            dependencies.extend(circuit_maps.iter().copied());
            dependencies.extend(invariant_maps.iter().copied());
            if laws.preserved {
                equation_map = Some(b.push(
                    NodeType::Construction(T::EquationMap),
                    "equation_map",
                    Json::obj([
                        ("source", se.wire()),
                        ("target", te.wire()),
                        ("indices", Json::Arr(laws.indices)),
                    ]),
                    dependencies.iter().copied().chain([se, te]).collect(),
                    None,
                    None,
                )?);
            }
            let views = super::object_view_map::retain(
                env, &mut b, &origin.shared_inputs(), &declarations, [a, z], c,
            )?;
            preserved &= views.preserved;
            let mut signature_dependencies = views.conditions.clone();
            signature_dependencies.extend(views.axis_dependencies);
            invariant_maps.extend(views.invariants);
            dependencies.extend(views.conditions);
            dependencies.extend(invariant_maps.iter().copied());
            if views.preserved {
                signature = Some(b.push(
                    NodeType::Construction(T::SignatureMap),
                    "signature_map",
                    Json::obj([("axes", Json::Arr(views.axes))]),
                    signature_dependencies.into_iter().chain([left, right]).collect(),
                    None,
                    None,
                )?);
            }
            dependencies.extend(equation_map);
            dependencies.extend(signature);
            let transported = declaration_transport::retain(env, &mut b, &inputs, &declarations, &[left,right], request, c)?;
            declaration_transports = transported.transports;
            declaration_status = transported.status;
            declaration_reasons = transported.reasons;
            declaration_evidence = transported.evidence;
            dependencies.extend(declaration_transports.iter().copied());
            dependencies.extend(declaration_evidence.iter().copied());
            dependencies.extend(declaration_reasons.iter().flat_map(|r| r.dependencies.iter().copied()));
        }
    }
    let status = if preserved {
        declaration_status
    } else {
        Decision::Refuted
    };
    dependencies.sort_by_key(|r| r.0);
    dependencies.dedup();
    let label = b.push(
        NodeType::Value(crate::types::Type::Text),
        "binding",
        Json::str("object_algebra_map"),
        vec![candidate],
        Some(Scalar::Text("object_algebra_map".into())),
        None,
    )?;
    let mut operands = vec![label];
    operands.extend(dependencies.iter().copied());
    let mut claim = b.proposition(
        "constructible",
        operands.clone(),
        dependencies.clone(),
        status,
    )?;
    let mut reasons = declaration_reasons;
    sort_reasons(&mut reasons);
    if status == Decision::Refuted {
        reasons.push(Reason {
            kind: ReasonKind::ConditionFailed {
                condition: claim,
                construction: "object_algebra_map",
            },
            request: request.id.clone(),
            dependencies: vec![claim],
            missing: vec![],
            location: None,
        });
        sort_reasons(&mut reasons);
        dependencies.push(claim);
        claim = b.proposition("constructible", operands, dependencies.clone(), status)?;
    }
    let part = &mut b.parts[claim.0 - base];
    part.reasons = reasons.clone();
    part.judgment.as_mut().ok_or("ObjectAlgebra mapの判断がない")?.reasons = reasons.clone();
    part.evidence = declaration_evidence.clone();
    part.judgment.as_mut().ok_or("ObjectAlgebra mapの判断がない")?.evidence = declaration_evidence.clone();
    outputs.insert("proposition".into(), claim);
    if status == Decision::Established {
        let [left, right] = algebras.ok_or("構成済みalgebraがない")?;
        dependencies.push(claim);
        let r = b.push(
            NodeType::Construction(T::ObjectAlgebraMap),
            "object_algebra_map",
            Json::obj([
                ("source", left.wire()),
                ("target", right.wire()),
                ("configuration_map", configuration.outputs["map"].wire()),
                ("declarations", Json::Arr(declaration_rows)),
                ("object_maps", Json::Arr(object_rows)),
                ("equations", equation_map.ok_or("EquationMapがない")?.wire()),
                (
                    "circuits",
                    Json::Arr(circuit_maps.iter().map(|r| r.wire()).collect()),
                ),
                ("operation_maps", Json::Arr(operation_rows)),
                (
                    "invariants",
                    Json::Arr(invariant_maps.iter().map(|r| r.wire()).collect()),
                ),
                ("signature", signature.ok_or("SignatureMapがない")?.wire()),
                ("transports", Json::Arr(declaration_transports.iter().map(|r|r.wire()).collect())),
            ]),
            dependencies,
            None,
            None,
        )?;
        outputs.insert("map".into(), r);
    }
    let scope = b.parts[claim.0 - base].scope.clone();
    Ok((
        b.parts,
        Answer {
            id: request.id.clone(),
            status,
            outputs,
            claim: Some(claim),
            evidence: declaration_evidence,
            reasons,
            scope,
        },
    ))
}

pub(super) fn validate_node(
    g: &Graph,
    n: &Node,
    v: &ConstructionValue,
    d: &Data,
) -> Result<(), ValidationFailure> {
    let Witness::Map(w) = &v.witness else {
        return Err("ObjectAlgebra mapの元対応がない".into());
    };
    let p = d.part();
    if !Arc::ptr_eq(w, &d.source.witness)
        || n.ty != p.ty
        || n.rule != Rule::Construction(p.construction)
        || n.arguments != p.arguments
        || n.support != p.support
        || n.scope != p.scope
        || n.reasons != p.reasons
        || n.judgment != p.judgment
        || n.evidence != p.evidence
    {
        return Err("ObjectAlgebra mapの元構成/辺/判断が違う".into());
    }
    for r in &p.arguments {
        g.get(*r)?;
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_object_map(
        &self,
        g: &Graph,
        v: &ConstructionValue,
        at: usize,
    ) -> Result<(), ValidationFailure> {
        let D::ObjectMap(d) = &v.data else {
            return Ok(());
        };
        d.position(at)?;
        let mut c = self.control.clone();
        d.source.boundary.recheck(self, g, at, &mut c)?;
        if self.object_map_source_checked(&d.source) {
            return Ok(());
        }
        let request = g
            .requests
            .get(
                g.context_at(d.source.configuration.outputs["candidate"].0)
                    .request,
            )
            .ok_or("元map Requestがない")?;
        super::public_map::validate_configuration_answer(
            self,
            g,
            request,
            &d.source.configuration,
        )?;
        let (parts, answer) = compute(
            self,
            g,
            &d.source.witness,
            &d.source.configuration,
            d.source.algebras,
            d.source.pending,
            d.source.base,
            request,
            &mut c,
        )?;
        if parts != d.source.parts || answer != d.source.answer {
            return Err("ObjectAlgebra mapの再構成が違う".into());
        }
        self.remember_object_map_source(d.source.clone());
        Ok(())
    }
}
pub(super) fn validate_answer(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    answer: &Answer,
) -> Result<(), ValidationFailure> {
    let r = answer.claim.ok_or("map構成命題がない")?;
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("map構成命題がnativeでない".into());
    };
    let D::ObjectMap(d) = &v.data else {
        return Err("map構成命題が別種".into());
    };
    super::public_map::validate_configuration_answer(env, g, request, &d.source.configuration)?;
    env.recheck_object_map(g, v, r.0)?;
    if answer != &d.source.answer {
        return Err("map回答が再検査結果と違う".into());
    }
    Ok(())
}
pub(super) fn validate_failure(g: &Graph, reason: &Reason) -> Result<(), ValidationFailure> {
    let ReasonKind::ConditionFailed {
        condition,
        construction: "object_algebra_map",
    } = reason.kind
    else {
        return Err("map構成反証が別種".into());
    };
    let n = g.get(condition)?;
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("map反証がnativeでない".into());
    };
    let D::ObjectMap(d) = &v.data else {
        return Err("map反証が別構成".into());
    };
    if n.judgment.as_ref().map(|j| j.status) != Some(Decision::Refuted)
        || v.witness.request().id != reason.request
        || reason.dependencies != [condition]
        || !reason.missing.is_empty()
        || !d.source.answer.reasons.contains(reason)
    {
        return Err("map構成反証の由来が違う".into());
    }
    validate_node(g, n, v, d)
}
