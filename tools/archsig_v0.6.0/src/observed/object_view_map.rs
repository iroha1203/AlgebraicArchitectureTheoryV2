//! 閉じたviewの値保存と型全域の構造的恒等を公開Invariant/Signatureへ接続する。
use super::{
    build_plan::Plan,
    build_result::Builder,
    construction_result::ConstructionType as T,
    control::{Checkpoint, Control},
    environment::Environment,
    input::CheckedInputs,
    object_view_transport::{self, ObjectViewTransport, ViewTransportOutcome},
    result::*,
};
use crate::{canonical::Json, construction::maps::DeclarationCorrespondence, types::Type};
use std::sync::Arc;

pub(super) struct KernelCacheEntry {
    declarations: DeclarationCorrespondence,
    object: usize,
    instance: usize,
    result: Arc<ObjectViewTransport>,
}
fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ObjectViewTransport)?;
    Ok(())
}
fn transport(
    env: &Environment<'_>,
    inputs: &Arc<CheckedInputs>,
    d: &DeclarationCorrespondence,
    object: usize,
    instance: usize,
    c: &mut Control,
) -> Result<Arc<ObjectViewTransport>, ValidationFailure> {
    if !std::ptr::eq(env.inputs, inputs.as_ref()) {
        return Err("view保存cacheの元入力が違う".into());
    }
    for e in env.verified_view_transports.borrow().iter() {
        tick(c)?;
        if e.object == object && e.instance == instance && e.declarations == *d {
            return Ok(e.result.clone());
        }
    }
    let result = Arc::new(
        object_view_transport::object_view_transport(inputs.clone(), d, object, instance, c)
            .map_err(|e| {
                c.stop_reason()
                    .map(ValidationFailure::Stop)
                    .unwrap_or_else(|| format!("view保存検査: {e:?}").into())
            })?,
    );
    env.verified_view_transports
        .borrow_mut()
        .push(KernelCacheEntry {
            declarations: d.clone(),
            object,
            instance,
            result: result.clone(),
        });
    Ok(result)
}
pub(super) struct Output {
    pub preserved: bool,
    pub invariants: Vec<NodeRef>,
    pub axes: Vec<Json>,
    pub conditions: Vec<NodeRef>,
    pub axis_dependencies: Vec<NodeRef>,
}
fn field<'a>(v: &'a Json, name: &str) -> Result<&'a Json, ValidationFailure> {
    let Json::Obj(v) = v else {
        return Err("view移送のrecord型が違う".into());
    };
    v.get(name)
        .ok_or_else(|| format!("view移送の{name}がない").into())
}
fn array(v: &Json) -> Result<&[Json], ValidationFailure> {
    let Json::Arr(v) = v else {
        return Err("view移送の配列型が違う".into());
    };
    Ok(v)
}
fn reference(v: &Json) -> Result<NodeRef, ValidationFailure> {
    let Json::Str(id) = field(v, "node")? else {
        return Err("view移送の参照型が違う".into());
    };
    Ok(NodeRef(
        id.strip_prefix('n')
            .and_then(|v| v.parse().ok())
            .ok_or("view移送の参照番号が違う")?,
    ))
}
fn wire(g: &Graph, r: NodeRef) -> Result<Json, ValidationFailure> {
    let Some(Payload::Construction(v)) = &g.get(r)?.payload else {
        return Err("view移送の元不変量がnativeでない".into());
    };
    Ok(v.wire())
}
// 参照/data/Path等を空のsubject/宣言表で運ばない。原始値と有限積だけを接続する。
fn primitive_product(ty: &Type, c: &mut Control) -> Result<bool, ValidationFailure> {
    let mut todo = vec![ty];
    while let Some(t) = todo.pop() {
        tick(c)?;
        match t {
            Type::Bool | Type::Z | Type::Q | Type::Fp(_) => {}
            Type::Tuple(ts) => todo.extend(ts),
            _ => return Ok(false),
        }
    }
    Ok(true)
}
fn proposition(
    b: &mut Builder<'_>,
    out: &mut Output,
    name: &str,
    args: Vec<NodeRef>,
    holds: bool,
) -> Result<NodeRef, ValidationFailure> {
    out.preserved &= holds;
    let r = b.proposition(
        name,
        args,
        vec![],
        if holds {
            Decision::Established
        } else {
            Decision::Refuted
        },
    )?;
    out.conditions.push(r);
    Ok(r)
}
fn inverse(
    b: &mut Builder<'_>,
    out: &mut Output,
    maps: [NodeRef; 2],
    ty: &Type,
    origin: NodeRef,
) -> Result<NodeRef, ValidationFailure> {
    let r = proposition(b, out, "inverse_maps", maps.to_vec(), true)?;
    let p = &mut b.parts[r.0 - b.base];
    // 恒等の両逆性は標本ではなく、このOption型の全域について成立する。
    p.scope.assignments = true;
    p.scope.quantifiers.push(Quantifier {
        kind: crate::law::ast::QuantKind::Forall,
        name: "value".into(),
        ty: ty.clone(),
        domain: None,
        occurrence: (origin.0, 0),
        context: None,
    });
    p.wire = Json::obj([
        ("predicate", Json::str("inverse_maps")),
        (
            "operands",
            Json::Arr(maps.iter().map(|r| r.wire()).collect()),
        ),
        (
            "quantifiers",
            Json::Arr(p.scope.quantifiers.iter().map(Quantifier::wire).collect()),
        ),
    ]);
    Ok(r)
}
fn equivalence(
    b: &mut Builder<'_>,
    out: &mut Output,
    ty: &Type,
    source: NodeRef,
    target: NodeRef,
) -> Result<(NodeRef, NodeRef), ValidationFailure> {
    let mut domains = vec![];
    for origin in [source, target] {
        domains.push(b.push(
            NodeType::Domain,
            "domain",
            Json::obj([("kind", Json::str("type")), ("type", ty.wire())]),
            vec![origin],
            None,
            None,
        )?);
    }
    let mut maps = vec![];
    for (a, z) in [(domains[0], domains[1]), (domains[1], domains[0])] {
        maps.push(b.push(
            NodeType::Construction(T::ValueMap),
            "value_map",
            Json::obj([
                ("source", a.wire()),
                ("target", z.wire()),
                ("source_type", ty.wire()),
                ("target_type", ty.wire()),
                ("subjects", Json::Arr(vec![])),
                ("declarations", Json::Arr(vec![])),
                ("generators", Json::Arr(vec![])),
            ]),
            vec![a, z],
            None,
            None,
        )?);
    }
    // primitive/tupleの恒等をOptionへ持ち上げる。NoneもSomeの全元も固定する。
    let left = inverse(b, out, [maps[0], maps[1]], ty, source)?;
    let right = inverse(b, out, [maps[1], maps[0]], ty, source)?;
    let r = b.push(
        NodeType::Construction(T::ValueEquivalence),
        "value_equivalence",
        Json::obj([
            ("source", domains[0].wire()),
            ("target", domains[1].wire()),
            ("forward", maps[0].wire()),
            ("inverse", maps[1].wire()),
            ("left_inverse", left.wire()),
            ("right_inverse", right.wire()),
        ]),
        domains
            .into_iter()
            .chain(maps.iter().copied())
            .chain([left, right])
            .collect(),
        None,
        None,
    )?;
    Ok((r, maps[0]))
}
fn expression(
    g: &Graph,
    invariant: NodeRef,
    object: NodeRef,
) -> Result<NodeRef, ValidationFailure> {
    let v = wire(g, invariant)?;
    let mut found = None;
    for row in array(field(&v, "values")?)? {
        g.tick()?;
        if reference(field(row, "object")?)? == object {
            if found
                .replace(reference(field(row, "expression")?)?)
                .is_some()
            {
                return Err("viewの対象読取りが一意でない".into());
            }
        }
    }
    found.ok_or_else(|| "viewの対象読取りがない".into())
}
pub(super) fn retain(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    inputs: &Arc<CheckedInputs>,
    declarations: &DeclarationCorrespondence,
    plans: [&Plan; 2],
    c: &mut Control,
) -> Result<Output, ValidationFailure> {
    let mut out = Output {
        preserved: true,
        invariants: vec![],
        axes: vec![],
        conditions: vec![],
        axis_dependencies: vec![],
    };
    if !declarations
        .candidates()
        .iter()
        .any(|d| d.source().kind == "view")
    {
        return Ok(out);
    }
    let [a, z] = plans;
    let av = a.views.as_ref().ok_or("元view表がない")?;
    let zv = z.views.as_ref().ok_or("先view表がない")?;
    let ao = a.objects.as_ref().ok_or("元対象表がない")?;
    let zo = z.objects.as_ref().ok_or("先対象表がない")?;
    let ar = a.architecture.witness.readings();
    let zr = z.architecture.witness.readings();
    for axis in &av.axes {
        tick(c)?;
        let instance = ar
            .instances()
            .get(axis.instance)
            .ok_or("元view instanceがない")?;
        if !instance.parameters().is_empty() {
            return Err("parameterを残すview移送の配送は未実装".into());
        }
        let returns = instance
            .declaration()
            .returns
            .as_ref()
            .ok_or("元viewの返り型がない")?;
        if !primitive_product(returns, c)? {
            return Err("このview値型の全域写像配送は未実装".into());
        }
        let ty = Type::Option(Box::new(returns.clone()));
        let mut target_axis = None;
        let mut rows = vec![];
        for (oi, source_object) in ao.objects.iter().enumerate() {
            tick(c)?;
            let t = transport(env, inputs, declarations, oi, axis.instance, c)?;
            let ti = t
                .target_instance()
                .ok_or("先view instance未完成の配送は未実装")?;
            if !ti.parameters().is_empty() {
                return Err("先viewのparameter配送は未実装".into());
            }
            if ti.declaration().returns.as_ref() != Some(returns) {
                out.preserved = false;
                return Ok(out);
            }
            let mut matches = vec![];
            for candidate in &zv.axes {
                tick(c)?;
                if zr.instances().get(candidate.instance) == Some(ti) {
                    matches.push(candidate);
                }
            }
            let [ta] = matches.as_slice() else {
                return Err("先view軸が一意でない".into());
            };
            if target_axis.is_some_and(|old| old != ta.invariant) {
                return Err("対象間でviewの移送先軸が変わる".into());
            }
            target_axis = Some(ta.invariant);
            let target = t.target_object().ok_or("view移送の対象像がない")?;
            let oj = zr
                .objects()
                .iter()
                .position(|o| o.identity() == target)
                .ok_or("view対象像が表にない")?;
            let preserved = match t.outcome() {
                ViewTransportOutcome::Preserved => true,
                ViewTransportOutcome::Refuted(_) => false,
                ViewTransportOutcome::Undetermined => {
                    return Err("未決view保存の配送は未実装".into());
                }
            };
            rows.push((
                *source_object,
                zo.objects[oj],
                ta.invariant,
                ta.signature,
                preserved,
            ));
        }
        let first = rows.first().ok_or("view移送の対象族が空")?;
        let target_invariant = first.2;
        let target_signature = first.3;
        let source_wire = wire(b.g, axis.invariant)?;
        let target_wire = wire(b.g, target_invariant)?;
        if field(&source_wire, "returns")? != &ty.wire()
            || field(&target_wire, "returns")? != &ty.wire()
        {
            return Err("viewのOption読取り型が元返り型と違う".into());
        }
        let (values, forward) = equivalence(b, &mut out, &ty, axis.invariant, target_invariant)?;
        let mut checks = vec![];
        let mut coordinate_checks = vec![];
        for (so, to, _, _, holds) in rows {
            tick(c)?;
            let se = expression(b.g, axis.invariant, so)?;
            let te = expression(b.g, target_invariant, to)?;
            let args = vec![se, te, forward];
            let commutes = proposition(b, &mut out, "invariant_transport", args.clone(), holds)?;
            let coordinate = proposition(b, &mut out, "signature_transport", args, holds)?;
            checks.push(Json::obj([
                ("source", so.wire()),
                ("target", to.wire()),
                ("commutes", commutes.wire()),
            ]));
            coordinate_checks.push(Json::obj([
                ("source", so.wire()),
                ("target", to.wire()),
                ("commutes", coordinate.wire()),
            ]));
        }
        let selected = |g: &Graph, r| -> Result<bool, ValidationFailure> {
            let v = wire(g, r)?;
            let Json::Bool(value) = field(&v, "selected")? else {
                return Err("signature選択がBoolでない".into());
            };
            Ok(*value)
        };
        let mut selected_values = vec![];
        for r in [axis.signature, target_signature] {
            let v = Scalar::Bool(selected(b.g, r)?);
            selected_values.push(b.push(
                NodeType::Value(Type::Bool),
                "binding",
                v.wire(),
                vec![r],
                Some(v),
                None,
            )?);
        }
        let selected = proposition(
            b,
            &mut out,
            "equal",
            selected_values,
            selected(b.g, axis.signature)? == selected(b.g, target_signature)?,
        )?;
        if out.preserved {
            out.invariants.push(
                b.push(
                    NodeType::Construction(T::InvariantMap),
                    "invariant_map",
                    Json::obj([
                        ("kind", Json::str("function")),
                        ("source", axis.invariant.wire()),
                        ("target", target_invariant.wire()),
                        ("values", values.wire()),
                        ("checks", Json::Arr(checks)),
                    ]),
                    out.conditions
                        .iter()
                        .copied()
                        .chain([axis.invariant, target_invariant, values])
                        .collect(),
                    None,
                    None,
                )?,
            );
            out.axis_dependencies
                .extend([axis.signature, target_signature, values]);
            out.axes.push(Json::obj([
                ("source", axis.signature.wire()),
                ("target", target_signature.wire()),
                ("coordinates", values.wire()),
                ("selected", selected.wire()),
                ("checks", Json::Arr(coordinate_checks)),
            ]));
        }
    }
    Ok(out)
}
