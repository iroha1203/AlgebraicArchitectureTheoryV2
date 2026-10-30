//! Lawの全引数の実評価と既存buildの全成分・全patternを公開移送表へ接続する。
use super::{
    build_plan::Plan,
    build_result::Builder,
    construction_result::{ConstructionData as D, ConstructionType as T},
    control::{Checkpoint, Control},
    environment::Environment,
    input::CheckedInputs,
    law_evaluation, object_law_transport,
    result::*,
};
use crate::{
    canonical::Json,
    construction::{maps::DeclarationCorrespondence, readings::ObjectInstance},
    types::Type,
};
use std::sync::Arc;

// Graphの参照を含まない、同じ不変三入力上の保存計算だけを再利用する。
// 公開DAG・producer・端点buildの再検査結果はこのcacheに含めない。
pub(super) struct KernelCacheEntry {
    declarations: DeclarationCorrespondence,
    object: usize,
    instance: usize,
    result: Arc<object_law_transport::ObjectLawTransport>,
}
fn transport(
    env: &Environment<'_>,
    inputs: &Arc<CheckedInputs>,
    declarations: &DeclarationCorrespondence,
    object: usize,
    instance: usize,
    c: &mut Control,
) -> Result<Arc<object_law_transport::ObjectLawTransport>, ValidationFailure> {
    if !std::ptr::eq(env.inputs, inputs.as_ref()) {
        return Err("Law保存cacheの元入力が違う".into());
    }
    for entry in env.verified_law_transports.borrow().iter() {
        tick(c)?;
        if entry.object == object
            && entry.instance == instance
            && entry.declarations == *declarations
        {
            return Ok(entry.result.clone());
        }
    }
    let result = Arc::new(
        object_law_transport::object_law_transport(
            inputs.clone(),
            declarations,
            object,
            instance,
            c,
        )
        .map_err(|e| {
            c.stop_reason()
                .map(ValidationFailure::Stop)
                .unwrap_or_else(|| format!("Law保存検査: {e:?}").into())
        })?,
    );
    env.verified_law_transports
        .borrow_mut()
        .push(KernelCacheEntry {
            declarations: declarations.clone(),
            object,
            instance,
            result: result.clone(),
        });
    Ok(result)
}

pub(super) struct Output {
    pub preserved: bool,
    pub declarations: Vec<Json>,
    pub indices: Vec<Json>,
    pub circuits: Vec<NodeRef>,
    pub invariants: Vec<NodeRef>,
    pub conditions: Vec<NodeRef>,
    pub pending: Option<super::environment::numeric_law_function::Pending>,
    pub evidence: Vec<NodeRef>,
}
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectLawCircuitTransport)?;
    Ok(())
}
fn field<'a>(v: &'a Json, key: &str) -> Result<&'a Json, ValidationFailure> {
    let Json::Obj(m) = v else {
        return Err("Law移送のrecord型が違う".into());
    };
    m.get(key)
        .ok_or_else(|| format!("Law移送の{key}がない").into())
}
fn array(v: &Json) -> Result<&[Json], ValidationFailure> {
    let Json::Arr(v) = v else {
        return Err("Law移送の配列型が違う".into());
    };
    Ok(v)
}
fn reference(v: &Json) -> Result<NodeRef, ValidationFailure> {
    let Json::Str(id) = field(v, "node")? else {
        return Err("Law移送の参照型が違う".into());
    };
    Ok(NodeRef(
        id.strip_prefix('n')
            .and_then(|s| s.parse().ok())
            .ok_or("Law移送の参照番号が違う")?,
    ))
}
fn wire(g: &Graph, r: NodeRef) -> Result<Json, ValidationFailure> {
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("Law移送の元buildがnativeでない".into());
    };
    Ok(v.wire())
}
fn same_origin(
    g: &Graph,
    r: NodeRef,
    instance: &ObjectInstance,
) -> Result<bool, ValidationFailure> {
    let o = law_evaluation::origin(g, r)?.ok_or("Law移送の元添字がない")?;
    if o.declaration != instance.declaration().name || o.bindings.len() != instance.bindings().len()
    {
        return Ok(false);
    }
    for (a, b) in o.bindings.iter().zip(instance.bindings()) {
        g.tick()?;
        if a.name != b.parameter().name {
            return Ok(false);
        }
        let Scalar::Subject {
            snapshot, subject, ..
        } = g.scalar(a.value)?
        else {
            return Ok(false);
        };
        if snapshot != &b.subject().snapshot || subject != &b.subject().subject {
            return Ok(false);
        }
    }
    Ok(true)
}
// 有限parameterを代入済みの成分は、元instanceの固定参照束縛を保つ。
fn contains_origin(
    g: &Graph,
    r: NodeRef,
    instance: &ObjectInstance,
) -> Result<bool, ValidationFailure> {
    let o = law_evaluation::origin(g, r)?.ok_or("Law成分の元添字がない")?;
    if o.declaration != instance.declaration().name {
        return Ok(false);
    }
    for binding in instance.bindings() {
        let Some(actual) = o
            .bindings
            .iter()
            .find(|b| b.name == binding.parameter().name)
        else {
            return Ok(false);
        };
        let Scalar::Subject {
            snapshot, subject, ..
        } = g.scalar(actual.value)?
        else {
            return Ok(false);
        };
        if snapshot != &binding.subject().snapshot || subject != &binding.subject().subject {
            return Ok(false);
        }
    }
    Ok(o.bindings.iter().all(|b| {
        instance
            .bindings()
            .iter()
            .any(|fixed| fixed.parameter().name == b.name)
            || instance.parameters().iter().any(|p| p.name == b.name)
    }))
}
fn matching_component(
    g: &Graph,
    source: &Detector,
    target: &Detector,
    inputs: &CheckedInputs,
    declarations: &DeclarationCorrespondence,
    c: &mut Control,
) -> Result<bool, ValidationFailure> {
    if source.component != target.component {
        return Ok(false);
    }
    let a = law_evaluation::origin(g, source.index)?.ok_or("元成分の添字がない")?;
    let z = law_evaluation::origin(g, target.index)?.ok_or("先成分の添字がない")?;
    let pair = declarations
        .candidates()
        .iter()
        .filter_map(|d| d.pair())
        .find(|p| p.source() == a.declaration)
        .ok_or("成分宣言の対応がない")?;
    if pair.target() != z.declaration || a.bindings.len() != z.bindings.len() {
        return Ok(false);
    }
    for binding in &a.bindings {
        tick(c)?;
        let Some((_, name)) = pair
            .parameters()
            .iter()
            .find(|(name, _)| name == &binding.name)
        else {
            return Ok(false);
        };
        let Some(image) = z.bindings.iter().find(|b| &b.name == name) else {
            return Ok(false);
        };
        let moved = super::value_transport::candidate_image(
            inputs,
            declarations,
            &a.declaration,
            g.scalar(binding.value)?,
            c,
        )
        .map_err(|e| {
            c.stop_reason()
                .map(ValidationFailure::Stop)
                .unwrap_or_else(|| format!("成分の引数移送: {e:?}").into())
        })?;
        if !super::data::equal(&moved, g.scalar(image.value)?, c)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn locate(
    g: &Graph,
    indices: &[NodeRef],
    instance: &ObjectInstance,
) -> Result<usize, ValidationFailure> {
    let mut found = None;
    for (i, r) in indices.iter().enumerate() {
        if same_origin(g, *r, instance)? {
            if found.replace(i).is_some() {
                return Err("Law移送の添字が一意でない".into());
            }
        }
    }
    found.ok_or_else(|| "Law移送の対応添字がない".into())
}
struct Case {
    reference: NodeRef,
    object: NodeRef,
    pattern: NodeRef,
    when: NodeRef,
    value: Option<bool>,
}
struct Detector {
    reference: NodeRef,
    index: NodeRef,
    component: Json,
    ty: Type,
    cases: Vec<Case>,
}
fn detectors(
    g: &Graph,
    algebra: NodeRef,
    plan: &Plan,
    c: &mut Control,
) -> Result<Vec<Detector>, ValidationFailure> {
    let mut out = vec![];
    let layout = plan
        .polynomial
        .as_ref()
        .filter(|p| p.data.complete)
        .or_else(|| plan.finite.as_ref().filter(|p| p.data.complete))
        .ok_or("Law移送の完了済み方程式表示がない")?;
    let coordinates = &layout
        .data
        .objects
        .first()
        .ok_or("Law移送のbase座標がない")?
        .coordinates;
    let algebra_wire = wire(g, algebra)?;
    let circuits = array(field(&algebra_wire, "circuits")?)?;
    if circuits.len() != coordinates.len() {
        return Err("Law移送のdetectorと全成分の数が違う".into());
    }
    for (r, coordinate) in circuits.iter().zip(coordinates) {
        tick(c)?;
        let r = reference(r)?;
        g.expect(r, &NodeType::Construction(T::CircuitDetector))?;
        let v = wire(g, r)?;
        let mut cases = vec![];
        for r in array(field(&v, "cases")?)? {
            tick(c)?;
            let r = reference(r)?;
            g.expect(r, &NodeType::Construction(T::CircuitCase))?;
            let v = wire(g, r)?;
            let evaluation = wire(g, reference(field(&v, "refutation")?)?)?;
            let Json::Obj(evaluation) = &evaluation else {
                return Err("circuitの評価がrecordでない".into());
            };
            let value = evaluation
                .get("value")
                .map(|r| -> Result<bool, ValidationFailure> {
                    match g.scalar(reference(r)?)? {
                        Scalar::Bool(v) => Ok(*v),
                        _ => Err("circuitの実真値がBoolでない".into()),
                    }
                })
                .transpose()?;
            cases.push(Case {
                reference: r,
                object: reference(field(&v, "object")?)?,
                pattern: reference(field(&v, "pattern")?)?,
                when: reference(field(&v, "when")?)?,
                value,
            });
        }
        let (index, component, lhs) = match &coordinate.source {
            super::observable_layout::Source::Polynomial(p) => (p.instance, &p.component, p.lhs),
            super::observable_layout::Source::Finite(p) => {
                (p.value.instance, &p.value.component, p.value.lhs)
            }
        };
        if reference(field(&v, "index")?)? != index
            || *field(&v, "component")?
                != Json::Arr(component.iter().map(|n| Json::Nat(*n as u64)).collect())
        {
            return Err("Law移送のdetectorが別の成分を指す".into());
        }
        let NodeType::Expression(ty) = g.get(lhs)?.ty.clone() else {
            return Err("Law移送の成分が型付き式でない".into());
        };
        out.push(Detector {
            reference: r,
            ty,
            index: reference(field(&v, "index")?)?,
            component: field(&v, "component")?.clone(),
            cases,
        });
    }
    Ok(out)
}
fn pattern(g: &Graph, a: NodeRef, b: NodeRef) -> Result<bool, ValidationFailure> {
    let get = |r| -> Result<_, ValidationFailure> {
        let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
            return Err("比較patternがnativeでない".into());
        };
        let D::CircuitPattern(d) = &v.data else {
            return Err("比較patternが別型".into());
        };
        Ok(d)
    };
    Ok(get(a)?.same_pattern(get(b)?))
}
fn proof(
    b: &mut Builder<'_>,
    out: &mut Output,
    name: &str,
    args: Vec<NodeRef>,
    value: bool,
) -> Result<NodeRef, ValidationFailure> {
    out.preserved &= value;
    let r = b.proposition(
        name,
        args,
        vec![],
        if value {
            Decision::Established
        } else {
            Decision::Refuted
        },
    )?;
    out.conditions.push(r);
    Ok(r)
}
fn attach(b: &mut Builder<'_>, r: NodeRef, evidence: NodeRef) -> Result<(), ValidationFailure> {
    let part = &mut b.parts[r.0 - b.base];
    part.evidence.push(evidence);
    part.judgment
        .as_mut()
        .ok_or("数値Law反例の判断がない")?
        .evidence
        .push(evidence);
    Ok(())
}
fn path(b: &mut Builder<'_>, p: &Json, parent: NodeRef) -> Result<NodeRef, ValidationFailure> {
    let mut items = vec![];
    for n in array(p)? {
        b.g.tick()?;
        let Json::Nat(n) = n else {
            return Err("成分pathが非負整数でない".into());
        };
        items.push(Scalar::Z((*n).into()));
    }
    let value = Scalar::List {
        element: Type::Z,
        items,
    };
    b.push(
        NodeType::Value(value.ty()),
        "binding",
        value.wire(),
        vec![parent],
        Some(value),
        None,
    )
}
pub(super) fn retain(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    inputs: &Arc<CheckedInputs>,
    declarations: &DeclarationCorrespondence,
    algebras: [NodeRef; 2],
    plans: [&Plan; 2],
    c: &mut Control,
) -> Result<Output, ValidationFailure> {
    let mut out = Output {
        preserved: true,
        declarations: vec![],
        indices: vec![],
        circuits: vec![],
        invariants: vec![],
        conditions: vec![],
        pending: None,
        evidence: vec![],
    };
    if declarations.candidates().is_empty() {
        return Ok(out);
    }
    for d in declarations.candidates() {
        tick(c)?;
        let pair = d.pair().ok_or("Law宣言の対応がない")?;
        out.declarations.push(Json::obj([
            ("source", Json::str(pair.source())),
            ("target", Json::str(pair.target())),
            (
                "parameters",
                Json::Arr(
                    pair.parameters()
                        .iter()
                        .map(|(s, t)| Json::Arr(vec![Json::str(s), Json::str(t)]))
                        .collect(),
                ),
            ),
            ("fields", Json::Arr(vec![])),
        ]));
    }
    if !declarations
        .candidates()
        .iter()
        .any(|d| d.source().kind == "law")
    {
        return Ok(out);
    }
    let [a, z] = plans;
    let at = a.laws.as_ref().ok_or("元Law表がない")?;
    let zt = z.laws.as_ref().ok_or("先Law表がない")?;
    let ar = a.architecture.witness.readings();
    let zr = z.architecture.witness.readings();
    let ad = detectors(b.g, algebras[0], a, c)?;
    let zd = detectors(b.g, algebras[1], z, c)?;
    for index in &at.indices {
        tick(c)?;
        let mut matching = vec![];
        for (i, instance) in ar.instances().iter().enumerate() {
            if same_origin(b.g, *index, instance)? {
                matching.push(i)
            }
        }
        let [instance_index] = matching.as_slice() else {
            return Err("元Lawのinstance対応が一意でない".into());
        };
        let instance = &ar.instances()[*instance_index];
        let mut target_index = None;
        let mut holds = vec![];
        let mut rows = vec![];
        let mut required = None;
        for (oi, object) in at.objects.iter().enumerate() {
            tick(c)?;
            let transfer = transport(env, inputs, declarations, oi, *instance_index, c)?;
            if matches!(
                transfer.outcome(),
                object_law_transport::LawTransportOutcome::Refuted(
                    object_law_transport::LawConditionFailure::ParameterType { .. }
                )
            ) {
                out.preserved = false;
                return Ok(out);
            }
            let ti = transfer
                .target_instance()
                .ok_or("移送先Law instance未完成の配送は未実装")?;
            let zi = locate(b.g, &zt.indices, ti)?;
            // required statusの不一致ではkernelは値の比較を始めない。
            // 確定した構成失敗を未実装エラーへ変換しない。
            if instance.declaration().role != ti.declaration().role {
                proof(
                    b,
                    &mut out,
                    "required_iff",
                    vec![*index, zt.indices[zi]],
                    false,
                )?;
                return Ok(out);
            }
            if target_index.is_some_and(|old| old != zi) {
                return Err("対象間で移送添字が変わる".into());
            }
            target_index = Some(zi);
            let target_object = transfer.target_object().ok_or("Law移送の対象像がない")?;
            let oj = zr
                .objects()
                .iter()
                .position(|o| o.identity() == target_object)
                .ok_or("Law移送の対象像が表にない")?;
            let target = &zt.objects[oj];
            if required.is_none() {
                required = Some(proof(
                    b,
                    &mut out,
                    "required_iff",
                    vec![*index, zt.indices[zi]],
                    instance.declaration().role == ti.declaration().role,
                )?);
            }
            let numeric = transfer.numeric_family();
            if let Some(pending) = numeric.and_then(|f| f.pending.as_ref()) {
                out.pending = Some(pending.clone());
                return Ok(out);
            }
            let (applicable_equal, holds_equal) = if let Some(family) = numeric {
                (
                    family.applicable.ok_or("数値Lawの適用が未決")?,
                    family.equivalent.ok_or("数値Lawの零集合比較が未決")?,
                )
            } else if let Some(family) = transfer.family() {
                if matches!(
                    transfer.outcome(),
                    object_law_transport::LawTransportOutcome::Undetermined
                ) {
                    return Err("Law族の全域比較が未決".into());
                }
                let mut app = true;
                let mut holds = true;
                for row in family.rows() {
                    tick(c)?;
                    let a = row
                        .source()
                        .application()
                        .value()
                        .zip(row.target().application().value())
                        .ok_or("Law族の適用条件が未決")?;
                    let h = row
                        .source()
                        .conditional()
                        .zip(row.target().conditional())
                        .ok_or("Law族の成立が未決")?;
                    app &= a.0 == a.1;
                    holds &= h.0 == h.1;
                }
                (app, holds)
            } else {
                let sr = transfer
                    .source_reading()
                    .ok_or("元Law読取り未完成の配送は未実装")?;
                let tr = transfer
                    .target_reading()
                    .ok_or("先Law読取り未完成の配送は未実装")?;
                let app = sr
                    .application()
                    .value()
                    .zip(tr.application().value())
                    .ok_or("Law適用条件の未決配送は未実装")?;
                let value = sr
                    .conditional()
                    .zip(tr.conditional())
                    .ok_or("Law成立の未決配送は未実装")?;
                (app.0 == app.1, value.0 == value.1)
            };
            let args = vec![*index, zt.indices[zi], object.object, target.object];
            let evidence = numeric
                .and_then(|f| f.example.as_ref())
                .map(|e| {
                    super::object_view_map::counterexample(
                        b,
                        e,
                        &e.left.ty(),
                        &e.right.ty(),
                        &args,
                        false,
                    )
                })
                .transpose()?;
            let application_evidence = numeric
                .and_then(|f| f.application_example.as_ref())
                .map(|e| {
                    super::object_view_map::counterexample(
                        b,
                        e,
                        &e.left.ty(),
                        &e.right.ty(),
                        &args,
                        false,
                    )
                })
                .transpose()?;
            let applicable = proof(
                b,
                &mut out,
                "applicability_iff",
                args.clone(),
                applicable_equal,
            )?;
            let equivalent = proof(b, &mut out, "equation_holds_iff", args, holds_equal)?;
            if numeric.is_some() {
                for r in [applicable, equivalent] {
                    super::object_view_map::quantify_parameters(b, r, instance.parameters());
                }
            }
            for (r, evidence) in [(applicable, application_evidence), (equivalent, evidence)] {
                if let Some(evidence) = evidence {
                    out.evidence.push(evidence);
                    attach(b, r, evidence)?;
                }
            }
            holds.push(Json::obj([
                ("source", object.object.wire()),
                ("target", target.object.wire()),
                ("applicable", applicable.wire()),
                ("equivalent", equivalent.wire()),
            ]));
            rows.push((oi, oj, equivalent, numeric.map(|_| holds_equal), evidence));
        }
        let zi = target_index.ok_or("Law移送の全対象表が空")?;
        let mut target_instances = vec![];
        for i in zr.instances() {
            if same_origin(b.g, zt.indices[zi], i)? {
                target_instances.push(i)
            }
        }
        let [target_instance] = target_instances.as_slice() else {
            return Err("先Lawの実instanceが一意でない".into());
        };
        let pair = declarations
            .candidates()
            .iter()
            .filter_map(|d| d.pair())
            .find(|p| p.source() == instance.declaration().name)
            .ok_or("Lawの型移送宣言がない")?;
        let mu = declarations.types().iter().cloned().collect();
        let alpha = pair.parameters().iter().cloned().collect();
        let mut source_components = vec![];
        let mut target_components = vec![];
        for d in &ad {
            if contains_origin(b.g, d.index, instance)? {
                let moved =
                    crate::construction::maps::moved_declaration_type(&d.ty, &mu, &alpha, c)
                        .map_err(|e| {
                            c.stop_reason()
                                .map(ValidationFailure::Stop)
                                .unwrap_or_else(|| format!("Lawの成分型移送: {e:?}").into())
                        })?;
                source_components.push((d.component.clone(), moved))
            }
        }
        for d in &zd {
            if contains_origin(b.g, d.index, target_instance)? {
                target_components.push((d.component.clone(), d.ty.clone()))
            }
        }
        if source_components != target_components {
            out.preserved = false;
            return Ok(out);
        }
        let mut components = vec![];
        for source in &ad {
            tick(c)?;
            if !contains_origin(b.g, source.index, instance)? {
                continue;
            }
            let targets = zd
                .iter()
                .filter_map(|d| {
                    match contains_origin(b.g, d.index, target_instance).and_then(|yes| {
                        if yes {
                            matching_component(b.g, source, d, inputs, declarations, c)
                        } else {
                            Ok(false)
                        }
                    }) {
                        Ok(true) => Some(Ok(d)),
                        Ok(false) => None,
                        Err(e) => Some(Err(e)),
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            let [target] = targets.as_slice() else {
                return Err("Law移送の成分対応が一意でない".into());
            };
            let sp = path(b, &source.component, source.reference)?;
            let tp = path(b, &target.component, target.reference)?;
            let mut zeros = vec![];
            let mut cases = vec![];
            for &(oi, oj, _, numeric, evidence) in &rows {
                tick(c)?;
                let so = at.objects[oi].object;
                let to = zt.objects[oj].object;
                let sc = source.cases.iter().find(|r| r.object == so);
                let tc = target.cases.iter().find(|r| r.object == to);
                // 完了済みbuildのclosed detectorは、適用外/guard=falseだけcaseを省く。
                // そのときAAT residualは零。欠測の端点buildからはここへ到達しない。
                let equivalent = proof(
                    b,
                    &mut out,
                    "residual_zero_iff",
                    vec![
                        a.equations.ok_or("元方程式族がない")?,
                        source.index,
                        so,
                        sp,
                        z.equations.ok_or("先方程式族がない")?,
                        target.index,
                        to,
                        tp,
                    ],
                    match numeric {
                        Some(equal) => equal,
                        None => {
                            sc.map(|r| r.value.ok_or("元circuitの真値が未決"))
                                .transpose()?
                                .unwrap_or(false)
                                == tc
                                    .map(|r| r.value.ok_or("先circuitの真値が未決"))
                                    .transpose()?
                                    .unwrap_or(false)
                        }
                    },
                )?;
                if numeric.is_some() {
                    super::object_view_map::quantify_parameters(
                        b,
                        equivalent,
                        instance.parameters(),
                    );
                }
                if let Some(evidence) = evidence.filter(|_| numeric == Some(false)) {
                    attach(b, equivalent, evidence)?;
                }
                zeros.push(Json::obj([
                    ("source", so.wire()),
                    ("target", to.wire()),
                    ("equivalent", equivalent.wire()),
                ]));
                let source_pattern =
                    a.patterns.as_ref().ok_or("元pattern表がない")?.rows[oi].pattern;
                let target_pattern =
                    z.patterns.as_ref().ok_or("先pattern表がない")?.rows[oj].pattern;
                for sc in &source.cases {
                    tick(c)?;
                    if !pattern(b.g, sc.pattern, source_pattern)? {
                        continue;
                    }
                    let Some(tc) = tc else {
                        out.preserved = false;
                        continue;
                    };
                    let matching = proof(
                        b,
                        &mut out,
                        "circuit_matches",
                        vec![tc.pattern, to],
                        pattern(b.g, tc.pattern, target_pattern)?,
                    )?;
                    let implies = proof(
                        b,
                        &mut out,
                        "implies",
                        vec![sc.when, tc.when],
                        match numeric {
                            Some(equal) => equal,
                            None => {
                                !sc.value.ok_or("元circuitの真値が未決")?
                                    || tc.value.ok_or("先circuitの真値が未決")?
                            }
                        },
                    )?;
                    let mut accepts = false;
                    for case in &target.cases {
                        tick(c)?;
                        if numeric.is_some() {
                            accepts |=
                                case.when == tc.when && pattern(b.g, case.pattern, tc.pattern)?;
                        } else {
                            accepts |= case.value.ok_or("先circuitの真値が未決")?
                                && pattern(b.g, case.pattern, tc.pattern)?;
                        }
                    }
                    let accepted = proof(
                        b,
                        &mut out,
                        "circuit_accepts",
                        vec![target.reference, tc.pattern, tc.when],
                        if numeric.is_some() {
                            accepts
                        } else {
                            !tc.value.ok_or("先circuitの真値が未決")? || accepts
                        },
                    )?;
                    if numeric.is_some() {
                        for r in [implies, accepted] {
                            super::object_view_map::quantify_parameters(
                                b,
                                r,
                                instance.parameters(),
                            );
                        }
                    }
                    if let Some(evidence) = evidence.filter(|_| numeric == Some(false)) {
                        attach(b, implies, evidence)?;
                    }
                    cases.push(Json::obj([
                        ("source_object", so.wire()),
                        ("target_object", to.wire()),
                        ("source", sc.reference.wire()),
                        ("target", tc.reference.wire()),
                        ("matching", matching.wire()),
                        ("when_implies", implies.wire()),
                        ("accepted", accepted.wire()),
                    ]));
                }
            }
            components.push(Json::obj([
                ("source", source.component.clone()),
                ("target", target.component.clone()),
                ("zeros", Json::Arr(zeros)),
            ]));
            if out.preserved {
                let r = b.push(
                    NodeType::Construction(T::CircuitMap),
                    "circuit_map",
                    Json::obj([
                        ("source", source.reference.wire()),
                        ("target", target.reference.wire()),
                        ("cases", Json::Arr(cases)),
                    ]),
                    out.conditions
                        .iter()
                        .copied()
                        .chain([source.reference, target.reference])
                        .collect(),
                    None,
                    None,
                )?;
                out.circuits.push(r);
            }
        }
        let si = a
            .predicates
            .iter()
            .find(|p| p.law == *index)
            .ok_or("元述語Invariantがない")?;
        let ti = z
            .predicates
            .iter()
            .find(|p| p.law == zt.indices[zi])
            .ok_or("先述語Invariantがない")?;
        let checks = rows
            .iter()
            .map(|&(i, j, e, _, _)| {
                Json::obj([
                    ("source", at.objects[i].object.wire()),
                    ("target", zt.objects[j].object.wire()),
                    ("equivalent", e.wire()),
                ])
            })
            .collect();
        if out.preserved {
            out.invariants.push(
                b.push(
                    NodeType::Construction(T::InvariantMap),
                    "invariant_map",
                    Json::obj([
                        ("kind", Json::str("predicate")),
                        ("source", si.invariant.wire()),
                        ("target", ti.invariant.wire()),
                        ("checks", Json::Arr(checks)),
                    ]),
                    rows.iter()
                        .map(|r| r.2)
                        .chain([si.invariant, ti.invariant])
                        .collect(),
                    None,
                    None,
                )?,
            );
        }
        out.indices.push(Json::obj([
            ("source", index.wire()),
            ("target", zt.indices[zi].wire()),
            ("required", required.ok_or("required比較がない")?.wire()),
            ("holds", Json::Arr(holds)),
            ("components", Json::Arr(components)),
        ]));
    }
    Ok(out)
}
