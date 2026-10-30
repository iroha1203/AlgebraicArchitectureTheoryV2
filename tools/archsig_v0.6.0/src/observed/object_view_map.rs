//! viewの値保存と型全域の写像を公開Invariant/Signatureへ接続する。
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
    pub pending: Option<(crate::issue::Location, Vec<Fact>)>,
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
fn supported_parameter(
    ty: &Type,
    inputs: &CheckedInputs,
    c: &mut Control,
) -> Result<bool, ValidationFailure> {
    Ok(
        super::environment::numeric_parameters::numeric_width(ty).is_some()
            || (super::finite::supported(ty, inputs.law(), c)?
                && super::value_transport::identity_declarations(ty, inputs.law(), c)?.is_some()),
    )
}
fn quantify_parameters(b: &mut Builder<'_>, r: NodeRef, parameters: &[crate::law::model::Param]) {
    let p = &mut b.parts[r.0 - b.base];
    let mut quantifiers = vec![];
    for parameter in parameters {
        p.scope.assignments = true;
        let q = Quantifier {
            kind: crate::law::ast::QuantKind::Forall,
            name: parameter.name.clone(),
            ty: parameter.ty.erase(),
            domain: None,
            occurrence: parameter.span,
            context: None,
        };
        p.scope.quantifiers.push(q.clone());
        quantifiers.push(q);
    }
    // Scopeは元評価の全域を保持する。命題のbinderは元parameterだけであり、
    // 先parameterはDeclarationPairの位置対応で束縛する。独立には量化しない。
    if let Json::Obj(wire) = &mut p.wire {
        wire.insert(
            "quantifiers".into(),
            Json::Arr(quantifiers.iter().map(Quantifier::wire).collect()),
        );
    }
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
    // 両逆性は標本ではなく、このOption型の全域について検査している。
    p.scope.assignments = true;
    let q = Quantifier {
        kind: crate::law::ast::QuantKind::Forall,
        name: "value".into(),
        ty: ty.clone(),
        domain: None,
        occurrence: (origin.0, 0),
        context: None,
    };
    p.scope.quantifiers.push(q.clone());
    p.wire = Json::obj([
        ("predicate", Json::str("inverse_maps")),
        (
            "operands",
            Json::Arr(maps.iter().map(|r| r.wire()).collect()),
        ),
        ("quantifiers", Json::Arr(vec![q.wire()])),
    ]);
    Ok(r)
}
struct ValueAction {
    subjects: Vec<(NodeRef, NodeRef)>,
    declarations: Vec<(String, String)>,
}
// 型構造に現れる全参照域を検査し、無住の枝の参照も公開表へ接続する。
fn finite_action(
    b: &mut Builder<'_>,
    inputs: &CheckedInputs,
    declarations: &DeclarationCorrespondence,
    values: &super::value_transport::FiniteValueTransport,
    dependencies: &[NodeRef],
    c: &mut Control,
) -> Result<Option<ValueAction>, ValidationFailure> {
    let mut action = ValueAction {
        subjects: vec![],
        declarations: vec![],
    };
    let mut references = std::collections::BTreeSet::new();
    let mut families = std::collections::BTreeSet::new();
    let mut pending = vec![values.source_type()];
    while let Some(ty) = pending.pop() {
        tick(c)?;
        match ty {
            Type::Ref(entity) => {
                references.insert(entity.clone());
            }
            Type::Tuple(items) => pending.extend(items),
            Type::Option(item) | Type::List(item) | Type::Set(item) => pending.push(item),
            Type::Map(a, z) => pending.extend([a.as_ref(), z.as_ref()]),
            Type::Data(family) if families.insert(family.clone()) => {
                action.declarations.push((family.clone(), family.clone()));
                for constructor in super::data::constructors(inputs.law(), family)? {
                    tick(c)?;
                    let name = format!("{family}.{}", constructor.name);
                    action.declarations.push((name.clone(), name));
                    pending.extend(&constructor.arguments);
                }
            }
            _ => {}
        }
    }
    for entity in references {
        tick(c)?;
        let transport =
            crate::construction::maps::reference_type_transport(inputs, declarations, &entity, c)
                .map_err(|e| {
                    c.stop_reason()
                        .map(ValidationFailure::Stop)
                        .unwrap_or_else(|| format!("有限view参照型の全域検査: {e:?}").into())
                })?;
        if transport.bijection().is_none() {
            return Ok(None);
        }
        action
            .declarations
            .push((entity.clone(), transport.target_type().to_owned()));
        for (source, target) in transport.source().iter().zip(transport.images()) {
            tick(c)?;
            let mut refs = vec![];
            for (fact, entity) in [
                (source, transport.source_type()),
                (target, transport.target_type()),
            ] {
                let value = Scalar::Subject {
                    snapshot: fact.snapshot.clone(),
                    subject: fact.subject.clone(),
                    entity: entity.into(),
                };
                refs.push(b.push(
                    NodeType::Value(value.ty()),
                    "binding",
                    value.wire(),
                    dependencies.to_vec(),
                    Some(value),
                    None,
                )?);
            }
            action.subjects.push((refs[0], refs[1]));
        }
    }
    action.declarations.sort();
    action.declarations.dedup();
    Ok(Some(action))
}

fn reject_equivalence(
    b: &mut Builder<'_>,
    out: &mut Output,
    types: [&Type; 2],
    origin: NodeRef,
) -> Result<(), ValidationFailure> {
    let label = b.push(
        NodeType::Value(Type::Text),
        "binding",
        Json::str("value_equivalence"),
        vec![origin],
        Some(Scalar::Text("value_equivalence".into())),
        None,
    )?;
    let mut args = vec![label];
    for ty in types {
        args.push(b.push(
            NodeType::Domain,
            "domain",
            Json::obj([("kind", Json::str("type")), ("type", ty.wire())]),
            vec![origin],
            None,
            None,
        )?);
    }
    proposition(b, out, "constructible", args, false)?;
    Ok(())
}
fn equivalence(
    b: &mut Builder<'_>,
    out: &mut Output,
    types: [&Type; 2],
    source: NodeRef,
    target: NodeRef,
    action: &ValueAction,
) -> Result<(NodeRef, NodeRef), ValidationFailure> {
    let mut domains = vec![];
    for (origin, ty) in [source, target].into_iter().zip(types) {
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
    for (direction, (a, z)) in [(domains[0], domains[1]), (domains[1], domains[0])]
        .into_iter()
        .enumerate()
    {
        let subjects = action
            .subjects
            .iter()
            .map(|(a, z)| if direction == 0 { (*a, *z) } else { (*z, *a) })
            .collect::<Vec<_>>();
        let declarations = action
            .declarations
            .iter()
            .map(|(a, z)| if direction == 0 { (a, z) } else { (z, a) })
            .collect::<Vec<_>>();
        maps.push(
            b.push(
                NodeType::Construction(T::ValueMap),
                "value_map",
                Json::obj([
                    ("source", a.wire()),
                    ("target", z.wire()),
                    ("source_type", types[direction].wire()),
                    ("target_type", types[1 - direction].wire()),
                    (
                        "subjects",
                        Json::Arr(
                            subjects
                                .iter()
                                .map(|(a, z)| Json::Arr(vec![a.wire(), z.wire()]))
                                .collect(),
                        ),
                    ),
                    (
                        "declarations",
                        Json::Arr(
                            declarations
                                .iter()
                                .map(|(a, z)| Json::Arr(vec![Json::str(*a), Json::str(*z)]))
                                .collect(),
                        ),
                    ),
                    ("generators", Json::Arr(vec![])),
                ]),
                [a, z]
                    .into_iter()
                    .chain(subjects.iter().flat_map(|(a, z)| [*a, *z]))
                    .collect(),
                None,
                None,
            )?,
        );
    }
    // 検査済みの型全域の順逆作用をOptionへ持ち上げ、Noneを固定する。
    let left = inverse(b, out, [maps[0], maps[1]], types[0], source)?;
    let right = inverse(b, out, [maps[1], maps[0]], types[1], target)?;
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
        pending: None,
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
        for p in instance.parameters() {
            if !supported_parameter(&p.ty, inputs, c)? {
                return Err("このparameter型のview移送配送は未実装".into());
            }
        }
        let returns = instance
            .declaration()
            .returns
            .as_ref()
            .ok_or("元viewの返り型がない")?;
        let value_declarations =
            super::value_transport::identity_declarations(returns, inputs.law(), c)?;
        let finite_values = if value_declarations.is_none() {
            if !super::finite::supported(returns, inputs.law(), c)? {
                return Err("このview値型の全域写像配送は未実装".into());
            }
            Some(
                super::value_transport::finite_declaration_value_transport(
                    inputs,
                    declarations,
                    &instance.declaration().name,
                    super::value_transport::DeclarationValuePosition::Return,
                    c,
                )
                .map_err(|e| {
                    c.stop_reason()
                        .map(ValidationFailure::Stop)
                        .unwrap_or_else(|| format!("有限view値の全域検査: {e:?}").into())
                })?,
            )
        } else {
            None
        };
        let ty = Type::Option(Box::new(returns.clone()));
        let target_returns = finite_values
            .as_ref()
            .map(|v| v.target_type())
            .unwrap_or(returns);
        let target_ty = Type::Option(Box::new(target_returns.clone()));
        if finite_values
            .as_ref()
            .is_some_and(|v| v.bijection().is_none())
        {
            reject_equivalence(b, &mut out, [&ty, &target_ty], axis.invariant)?;
            return Ok(out);
        }
        let mut target_axis = None;
        let mut rows = vec![];
        for (oi, source_object) in ao.objects.iter().enumerate() {
            tick(c)?;
            let t = transport(env, inputs, declarations, oi, axis.instance, c)?;
            let ti = t
                .target_instance()
                .ok_or("先view instance未完成の配送は未実装")?;
            if instance.parameters().len() != ti.parameters().len()
                || instance
                    .parameters()
                    .iter()
                    .zip(ti.parameters())
                    .any(|(s, t)| s.ty.erase() != t.ty.erase())
            {
                return Err("対応parameterの型が異なるview移送配送は未実装".into());
            }
            if ti.declaration().returns.as_ref() != Some(target_returns) {
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
                    if let Some(missing) = t.numeric_pending() {
                        let declaration = &inputs.law().declarations[&instance.declaration().name];
                        let crate::law::model::Signature::View { body, .. } = &declaration.signature else {
                            return Err("元viewのbodyがない".into());
                        };
                        out.pending.get_or_insert((
                            crate::issue::Location::Law {
                                span: inputs.law().exprs[*body].span,
                            },
                            missing,
                        ));
                        continue;
                    }
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
        if rows.is_empty() && out.pending.is_some() {
            continue;
        }
        let first = rows.first().ok_or("view移送の対象族が空")?;
        let target_invariant = first.2;
        let target_signature = first.3;
        let source_wire = wire(b.g, axis.invariant)?;
        let target_wire = wire(b.g, target_invariant)?;
        if field(&source_wire, "returns")? != &ty.wire()
            || field(&target_wire, "returns")? != &target_ty.wire()
        {
            return Err("viewのOption読取り型が元返り型と違う".into());
        }
        let action = if let Some(declarations) = value_declarations {
            ValueAction {
                subjects: vec![],
                declarations,
            }
        } else {
            let Some(action) = finite_action(
                b,
                inputs,
                declarations,
                finite_values.as_ref().ok_or("有限view値写像がない")?,
                &[axis.invariant, target_invariant],
                c,
            )?
            else {
                reject_equivalence(b, &mut out, [&ty, &target_ty], axis.invariant)?;
                return Ok(out);
            };
            action
        };
        let (values, forward) = equivalence(
            b,
            &mut out,
            [&ty, &target_ty],
            axis.invariant,
            target_invariant,
            &action,
        )?;
        let mut checks = vec![];
        let mut coordinate_checks = vec![];
        for (so, to, _, _, holds) in rows {
            tick(c)?;
            let se = expression(b.g, axis.invariant, so)?;
            let te = expression(b.g, target_invariant, to)?;
            let args = vec![se, te, forward];
            let commutes = proposition(b, &mut out, "invariant_transport", args.clone(), holds)?;
            quantify_parameters(b, commutes, instance.parameters());
            let coordinate = proposition(b, &mut out, "signature_transport", args, holds)?;
            quantify_parameters(b, coordinate, instance.parameters());
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
        if out.preserved && out.pending.is_none() {
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
