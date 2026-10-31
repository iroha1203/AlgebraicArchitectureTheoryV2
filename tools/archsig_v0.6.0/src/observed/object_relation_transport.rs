//! relationの各辺を、型域全体の名前付き生成元対応で運ぶ。
use super::*;
use crate::{
    definition::model::PrimitiveSignature,
    observed::{
        change_result,
        environment::{
            numeric_parameters,
            relation_instances::{self, RelationState},
        },
        path_compose,
        path_value::PathValue,
    },
};

type Inputs = crate::input::CheckedInputs;
fn pending(
    out: &mut Output,
    request: &Request,
    origins: &[NodeRef],
    span: (usize, usize),
    missing: Vec<Fact>,
) {
    out.status = merge_status(out.status, Decision::Undetermined);
    out.reasons.push(Reason {
        kind: if missing.is_empty() {
            ReasonKind::UnsupportedAlgorithm {
                question: request.kind,
                operand_types: vec![],
                method: "relation_transport".into(),
            }
        } else {
            ReasonKind::Missing
        },
        request: request.id.clone(),
        dependencies: origins.to_vec(),
        missing,
        location: Some(crate::issue::Location::Law { span }),
    });
}
fn ensure_map(
    b: &mut Builder<'_>,
    inputs: &Inputs,
    correspondence: &construction::DeclarationCorrespondence,
    source: &str,
    target: &str,
    deps: &[NodeRef],
    maps: &mut Vec<Arc<ParameterMap>>,
    c: &mut Control,
) -> Result<usize, ValidationFailure> {
    if let Some(i) = maps
        .iter()
        .position(|m| m.source == source && m.target == target)
    {
        return Ok(i);
    }
    maps.push(reference_map(
        b,
        inputs,
        correspondence,
        source,
        target,
        deps,
        c,
    )?);
    Ok(maps.len() - 1)
}
fn moved(
    value: &Scalar,
    maps: &[Arc<ParameterMap>],
    c: &mut Control,
) -> Result<Scalar, ValidationFailure> {
    if let Scalar::Subject {
        snapshot,
        subject,
        entity,
    } = value
    {
        let map = maps
            .iter()
            .find(|m| m.source == *entity)
            .ok_or("relationの元参照型写像がない")?;
        for (s, t) in map.transport.source().iter().zip(map.transport.images()) {
            tick(c)?;
            if s.snapshot == *snapshot && s.subject == *subject {
                return Ok(Scalar::Subject {
                    snapshot: t.snapshot.clone(),
                    subject: t.subject.clone(),
                    entity: map.target.clone(),
                });
            }
        }
        return Err("relationの元参照が全型域写像にない".into());
    }
    Ok(value.clone())
}
// Pathのwireは既出の型付き参照を必要とする。作用はScalar自身から再検査される。
fn path_binding(
    b: &mut Builder<'_>,
    path: &PathValue,
    deps: &[NodeRef],
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    path.check(c)?;
    let mut args = deps.to_vec();
    let source = change_result::value(b, &path.object())?;
    let target = change_result::value(b, &path.target())?;
    args.extend([source, target]);
    let mut generators = vec![];
    if let Some(step) = &path.step {
        for generator in std::iter::once(&step.generator).chain(&step.word_tail) {
            tick(c)?;
            let reference = change_result::value(b, generator)?;
            args.push(reference);
            generators.push(reference.wire());
        }
    }
    let scalar = Scalar::Path(Box::new(path.clone()));
    b.push(
        NodeType::Value(scalar.ty()),
        "binding",
        Json::obj([
            ("reading", Json::str(&path.reading)),
            ("source", source.wire()),
            ("target", target.wire()),
            ("generators", Json::Arr(generators)),
        ]),
        args,
        Some(scalar),
        None,
    )
}
// 族全体で適用条件と比較する語が確定した後にだけ、実際の反例割当てを作る。
fn witness_bindings(
    params: &[Param],
    row: &relation_instances::RelationInstance,
    numeric_point: Option<&[Scalar]>,
    c: &mut Control,
) -> Result<Vec<(String, Scalar)>, ValidationFailure> {
    if numeric_point.is_none()
        && row
            .numeric_domain
            .as_ref()
            .is_some_and(|domain| domain.particular.is_none())
    {
        return Err("空のrelation適用域に反例はない".into());
    }
    params
        .iter()
        .map(|p| {
            tick(c)?;
            let value =
                if let Some((_, value)) = row.bindings.iter().find(|(name, _)| name == &p.name) {
                    value.clone()
                } else if row.numeric_parameters.contains(p) && numeric_parameters::numeric_width(&p.ty).is_some() {
                    if let Some(point) = numeric_point.or_else(|| {
                        row.numeric_domain
                            .as_ref()
                            .and_then(|domain| domain.particular.as_deref())
                    }) {
                        numeric_parameters::point_value(
                            &row.numeric_parameters, p, point, c,
                        )?
                    } else {
                        crate::observed::numeric::zero(&p.ty, c)?
                    }
                } else {
                    return Err("relation反例の元parameter束縛がない".into());
                };
            Ok((p.name.clone(), value))
        })
        .collect()
}
fn example(
    b: &mut Builder<'_>,
    params: &[Param],
    bindings: &[(String, Scalar)],
    left: &Scalar,
    right: &Scalar,
    deps: &[NodeRef],
    facts: &[Fact],
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let paths = matches!((left, right), (Scalar::Path(_), Scalar::Path(_)));
    let left = match left {
        Scalar::Path(path) => path_binding(b, path, deps, c)?,
        value => change_result::value(b, value)?,
    };
    let right = match right {
        Scalar::Path(path) => path_binding(b, path, deps, c)?,
        value => change_result::value(b, value)?,
    };
    let mut args = vec![left, right];
    let mut bound = vec![];
    for (p, (name, v)) in params.iter().zip(bindings) {
        tick(c)?;
        let value = change_result::value(b, v)?;
        args.push(value);
        bound.push(Json::obj([
            ("name", Json::str(name)),
            ("type", p.ty.wire()),
            ("value", value.wire()),
        ]));
    }
    b.push(
        NodeType::Evidence,
        "evidence",
        Json::obj([
            ("kind", Json::str("counterexample")),
            (
                "data",
                Json::obj([
                    ("bindings", Json::Arr(bound)),
                    (
                        "paths",
                        Json::Arr(if paths {
                            vec![left.wire(), right.wire()]
                        } else {
                            vec![]
                        }),
                    ),
                    ("left", left.wire()),
                    ("right", right.wire()),
                    ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                ]),
            ),
        ]),
        args,
        None,
        None,
    )
}
struct Generator {
    source: Scalar,
    path: PathValue,
    target: Option<PathValue>,
    subjects: (NodeRef, NodeRef),
    missing: Vec<Fact>,
}
type Point = (String, String);
fn point(value: &Scalar) -> Result<Point, ValidationFailure> {
    let Scalar::Subject {
        snapshot, subject, ..
    } = value
    else {
        return Err("relationの経路端点が原始参照でない".into());
    };
    Ok((snapshot.clone(), subject.clone()))
}
// 実端点の有限グラフ上で経路の存在と証人を構成する。語の長さで打ち切らない。
fn reach(
    generators: &[Generator],
    seeds: Vec<Point>,
    reverse: bool,
    c: &mut Control,
) -> Result<std::collections::BTreeMap<Point, Vec<usize>>, ValidationFailure> {
    let mut paths = seeds
        .into_iter()
        .map(|p| (p, vec![]))
        .collect::<std::collections::BTreeMap<_, _>>();
    loop {
        let mut changed = false;
        for (i, g) in generators.iter().enumerate() {
            tick(c)?;
            let a = point(&g.path.object())?;
            let z = point(&g.path.target())?;
            let (from, to) = if reverse { (z, a) } else { (a, z) };
            if !paths.contains_key(&to) {
                if let Some(path) = paths.get(&from) {
                    let mut path = path.clone();
                    if reverse {
                        path.insert(0, i);
                    } else {
                        path.push(i);
                    }
                    paths.insert(to, path);
                    changed = true;
                }
            }
        }
        if !changed {
            return Ok(paths);
        }
    }
}
fn route(
    generators: &[Generator],
    edges: &[usize],
    reading: &str,
    c: &mut Control,
) -> Result<PathValue, ValidationFailure> {
    let (&first, rest) = edges.split_first().ok_or("生成元の経路証人が空")?;
    let mut path = generators[first].path.clone();
    for &i in rest {
        tick(c)?;
        path = path_compose::compose_retained(&path, &generators[i].path, reading, c, |_, _| {})
            .map_err(|e| e.cause)?
            .value
            .ok_or("生成元の経路証人の端点が不整合")?;
    }
    Ok(path)
}
fn endpoints(signature: &PrimitiveSignature) -> Option<(&str, &str)> {
    match signature {
        PrimitiveSignature::Arrow { endpoint, .. } => Some((endpoint, endpoint)),
        PrimitiveSignature::Correspondence { from, to, .. } => Some((from, to)),
        _ => None,
    }
}
fn word(
    path: &PathValue,
    reading: &str,
    maps: &[Arc<ParameterMap>],
    generators: &[&Generator],
    c: &mut Control,
) -> Result<Option<PathValue>, ValidationFailure> {
    let Scalar::Subject {
        snapshot,
        subject,
        entity,
    } = &moved(&path.object(), maps, c)?
    else {
        return Err("relationの移送端点が参照でない".into());
    };
    let mut result = PathValue {
        reading: reading.into(),
        snapshot: snapshot.clone(),
        subject: subject.clone(),
        entity: entity.clone(),
        step: None,
    };
    if let Some(step) = &path.step {
        for source in std::iter::once(&step.generator).chain(&step.word_tail) {
            tick(c)?;
            let Some(generator) = generators.iter().find(|g| g.source == *source) else {
                return Ok(None);
            };
            let Some(target) = &generator.target else {
                return Ok(None);
            };
            let composed = path_compose::compose_retained(&result, target, reading, c, |_, _| {})
                .map_err(|e| e.cause)?;
            let Some(value) = composed.value else {
                return Err("relationの生成元移送が合成端点を保存しない".into());
            };
            result = value;
        }
    }
    Ok(Some(result))
}
pub(super) fn retain(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    inputs: &Inputs,
    correspondence: &construction::DeclarationCorrespondence,
    deps: &[NodeRef],
    request: &Request,
    c: &mut Control,
) -> Result<Output, ValidationFailure> {
    let mut out = Output {
        transports: vec![],
        failed_arguments: vec![],
        status: Decision::Established,
        reasons: vec![],
        evidence: vec![],
    };
    let mut instance_tables: [Option<relation_instances::RelationInstances>; 2] = [None, None];
    for candidate in correspondence
        .candidates()
        .iter()
        .filter(|d| d.source().kind == "relation")
    {
        tick(c)?;
        let pair = candidate.pair().ok_or("relationの対応署名がない")?;
        let declarations = [
            &inputs.law().declarations[pair.source()],
            &inputs.law().declarations[pair.target()],
        ];
        let (
            Signature::Relation {
                params: sp,
                guard: sg,
                left: sl,
                right: sr,
            },
            Signature::Relation {
                params: tp,
                guard: tg,
                left: tl,
                right: tr,
            },
        ) = (&declarations[0].signature, &declarations[1].signature)
        else {
            return Err("relation移送の元宣言が違う".into());
        };
        let origins =
            [[*sl, *tl], [*sr, *tr]].map(|ids| -> Result<[NodeRef; 2], ValidationFailure> {
                Ok([
                    expression(b, inputs, ids[0], sp, deps)?,
                    expression(b, inputs, ids[1], tp, deps)?,
                ])
            });
        let [left, right] = origins;
        let origins = [left?, right?];
        let mut origin_deps = origins.iter().flatten().copied().collect::<Vec<_>>();
        for (guard, params) in [(*sg, sp), (*tg, tp)] {
            if let Some(id) = guard {
                origin_deps.push(expression(b, inputs, id, params, deps)?);
            }
        }
        let start_reasons = out.reasons.len();
        let start_evidence = out.evidence.len();
        let (Some(Type::Path(sa, sb)), Some(Type::Path(ta, tb))) =
            (inputs.law().expr_type(*sl), inputs.law().expr_type(*tl))
        else {
            return Err("relationの辺がPathでない".into());
        };
        let mut maps = vec![];
        let mut identity = correspondence.types().to_vec();
        let start_map = ensure_map(b, inputs, correspondence, sa, ta, deps, &mut maps, c)?;
        let end_map = ensure_map(b, inputs, correspondence, sb, tb, deps, &mut maps, c)?;
        let mut supported = true;
        for (s, t) in sp.iter().zip(tp) {
            match (&s.ty.erase(), &t.ty.erase()) {
                (Type::Ref(a), Type::Ref(z)) => {
                    ensure_map(b, inputs, correspondence, &a, &z, deps, &mut maps, c)?;
                }
                (a, z) if a == z => {
                    if let Some(ds) = super::super::super::value_transport::identity_declarations(
                        &a,
                        inputs.law(),
                        c,
                    )? {
                        identity.extend(ds);
                    } else {
                        supported = false;
                    }
                }
                _ => supported = false,
            }
        }
        if !supported {
            pending(
                &mut out,
                request,
                &origin_deps,
                declarations[0].span,
                vec![],
            );
            continue;
        }
        // Path型域の全生成元を運ぶ。実際のrelationに現れた語だけに写像を狭めない。
        let namespaces =
            crate::construction::reading_namespaces(inputs.law(), &declarations[0].reading, c)
                .map_err(failure)?;
        let definitions = inputs
            .definitions()
            .declarations
            .iter()
            .filter(|(_, d)| namespaces.contains(&d.namespace))
            .filter_map(|(name, d)| endpoints(&d.signature).map(|(from, to)| (name, d, from, to)))
            .collect::<Vec<_>>();
        let mut forward = std::collections::BTreeSet::from([sa.as_str()]);
        let mut backward = std::collections::BTreeSet::from([sb.as_str()]);
        loop {
            let mut changed = false;
            for (_, _, from, to) in &definitions {
                tick(c)?;
                if forward.contains(from) {
                    changed |= forward.insert(to);
                }
                if backward.contains(to) {
                    changed |= backward.insert(from);
                }
            }
            if !changed {
                break;
            }
        }
        let map_type = |name: &str| {
            correspondence
                .types()
                .iter()
                .find(|(s, _)| s == name)
                .map(|(_, t)| t.clone())
                .unwrap_or_else(|| name.to_owned())
        };
        let mut generator_types = vec![];
        for (name, def, from, to) in definitions {
            tick(c)?;
            if !forward.contains(from) || !backward.contains(to) {
                continue;
            }
            let target = map_type(name);
            let Some(target_def) = inputs.definitions().declarations.get(&target) else {
                return Err("relation生成元の像宣言がない".into());
            };
            let ft = map_type(from);
            let tt = map_type(to);
            let kind_matches = matches!(
                (&def.signature, &target_def.signature),
                (
                    PrimitiveSignature::Arrow { .. },
                    PrimitiveSignature::Arrow { .. }
                ) | (
                    PrimitiveSignature::Correspondence { .. },
                    PrimitiveSignature::Correspondence { .. }
                )
            );
            if !kind_matches || endpoints(&target_def.signature) != Some((ft.as_str(), tt.as_str()))
            {
                supported = false;
                break;
            }
            ensure_map(b, inputs, correspondence, from, &ft, deps, &mut maps, c)?;
            ensure_map(b, inputs, correspondence, to, &tt, deps, &mut maps, c)?;
            generator_types.push((name.clone(), target));
        }
        if !supported {
            pending(
                &mut out,
                request,
                &origin_deps,
                declarations[0].span,
                vec![],
            );
            continue;
        }
        let mut generators = vec![];
        let mut generator_refs = vec![];
        let mut complete = true;
        let mut support = vec![];
        let mut scope = Scope::default();
        for (s, t) in generator_types {
            let index = ensure_map(b, inputs, correspondence, &s, &t, deps, &mut maps, c)?;
            let map = maps[index].clone();
            for ((sf, tf), (sref, tref)) in map
                .transport
                .source()
                .iter()
                .zip(map.transport.images())
                .zip(&map.subjects)
            {
                tick(c)?;
                let sv = Scalar::Subject {
                    snapshot: sf.snapshot.clone(),
                    subject: sf.subject.clone(),
                    entity: s.clone(),
                };
                let tv = Scalar::Subject {
                    snapshot: tf.snapshot.clone(),
                    subject: tf.subject.clone(),
                    entity: t.clone(),
                };
                let source = env.generator_path(
                    &declarations[0].reading,
                    &[sv.clone()],
                    declarations[0].span,
                )?;
                let target =
                    env.generator_path(&declarations[1].reading, &[tv], declarations[1].span)?;
                for result in [&source, &target] {
                    support.extend(result.support.iter().cloned());
                    scope.merge(&result.scope);
                }
                let mut absent = source.missing.clone();
                absent.extend(target.missing.iter().cloned());
                let Some(Scalar::Path(source)) = &source.value else {
                    complete = false;
                    pending(
                        &mut out,
                        request,
                        &origin_deps,
                        declarations[0].span,
                        absent,
                    );
                    continue;
                };
                let target = match &target.value {
                    Some(Scalar::Path(path)) => Some((**path).clone()),
                    _ => None,
                };
                generators.push(Generator {
                    source: sv,
                    path: (**source).clone(),
                    target,
                    subjects: (*sref, *tref),
                    missing: absent,
                });
            }
        }
        let seeds = |index: usize| {
            maps[index]
                .transport
                .source()
                .iter()
                .map(|p| (p.snapshot.clone(), p.subject.clone()))
                .collect::<Vec<_>>()
        };
        let forward = reach(&generators, seeds(start_map), false, c)?;
        let backward = reach(&generators, seeds(end_map), true, c)?;
        let all_generators = generators;
        let mut generators = vec![];
        for (i, g) in all_generators.iter().enumerate() {
            tick(c)?;
            let (Some(prefix), Some(suffix)) = (
                forward.get(&point(&g.path.object())?),
                backward.get(&point(&g.path.target())?),
            ) else {
                continue;
            };
            let Some(target) = &g.target else {
                complete = false;
                pending(
                    &mut out,
                    request,
                    &origin_deps,
                    declarations[0].span,
                    g.missing.clone(),
                );
                continue;
            };
            let points = [
                (moved(&g.path.object(), &maps, c)?, target.object()),
                (moved(&g.path.target(), &maps, c)?, target.target()),
            ];
            if let Some((left, right)) = points.iter().find(|(a, z)| a != z) {
                complete = false;
                let mut edges = prefix.clone();
                edges.push(i);
                edges.extend(suffix);
                let source = route(&all_generators, &edges, &declarations[0].reading, c)?;
                let paths = [
                    path_binding(b, &source, &origin_deps, c)?,
                    path_binding(b, target, &origin_deps, c)?,
                ];
                let witness = example(b, &[], &[], left, right, &origin_deps, &support, c)?;
                let part = &mut b.parts[witness.0 - b.base];
                part.arguments.extend(paths);
                if let Json::Obj(wire) = &mut part.wire {
                    if let Some(Json::Obj(data)) = wire.get_mut("data") {
                        data.insert(
                            "paths".into(),
                            Json::Arr(paths.iter().map(|r| r.wire()).collect()),
                        );
                    }
                }
                out.evidence.push(witness);
                out.status = Decision::Refuted;
                continue;
            }
            generator_refs.push(g.subjects);
            generators.push(g);
        }
        for side in 0..2 {
            if !instance_tables[side]
                .as_ref()
                .is_some_and(|table| table.reading() == declarations[side].reading)
            {
                instance_tables[side] = Some(
                    relation_instances::relation_transport_instances(
                        inputs,
                        &declarations[side].reading,
                        c,
                    )
                    .map_err(|e| e.cause)?,
                );
            }
        }
        let tables = [
            instance_tables[0]
                .as_ref()
                .ok_or("source relation表がない")?,
            instance_tables[1]
                .as_ref()
                .ok_or("target relation表がない")?,
        ];
        if tables[0]
            .outside_finite
            .iter()
            .any(|r| r.declaration == declarations[0].name)
        {
            pending(
                &mut out,
                request,
                &origin_deps,
                declarations[0].span,
                vec![],
            );
        }
        for absent in tables[0]
            .pending_domains
            .iter()
            .filter(|r| r.declaration == declarations[0].name)
        {
            pending(
                &mut out,
                request,
                &origin_deps,
                declarations[0].span,
                absent.missing.clone(),
            );
        }
        let mut statuses = [Decision::Established; 2];
        let mut evidence = [vec![], vec![]];
        for row in tables[0]
            .instances
            .iter()
            .filter(|r| r.declaration == declarations[0].name)
        {
            tick(c)?;
            if row.state == RelationState::OutsideDomain {
                continue;
            }
            support.extend(row.support.iter().cloned());
            scope.merge(&row.scope);
            if row.guard_checked && row.guard == Some(false) {
                continue;
            }
            if !row.guard_checked || row.guard != Some(true) {
                pending(
                    &mut out,
                    request,
                    &origin_deps,
                    declarations[0].span,
                    row.missing.clone(),
                );
                continue;
            }
            let mut target_bindings = vec![];
            for (source, target) in sp.iter().zip(tp) {
                if let Some((_, value)) = row.bindings.iter().find(|(name, _)| name == &source.name)
                {
                    target_bindings.push((target.name.clone(), moved(value, &maps, c)?));
                }
            }
            let Some(target) = tables[1]
                .instances
                .iter()
                .find(|r| r.declaration == declarations[1].name && r.bindings == target_bindings)
            else {
                let mut missing = vec![];
                for absent in tables[1]
                    .pending_domains
                    .iter()
                    .filter(|r| r.declaration == declarations[1].name)
                {
                    tick(c)?;
                    if absent
                        .bindings
                        .iter()
                        .all(|binding| target_bindings.contains(binding))
                    {
                        missing.extend(absent.missing.iter().cloned());
                    }
                }
                pending(
                    &mut out,
                    request,
                    &origin_deps,
                    declarations[1].span,
                    missing,
                );
                continue;
            };
            let guard_point = match (&row.numeric_domain, &target.numeric_domain) {
                (Some(source), Some(target)) => source.outside(target, env)?,
                _ => None,
            };
            let restricted;
            let target = if let Some(point) = &guard_point {
                let bindings = witness_bindings(tp, target, Some(point), c)?;
                restricted = relation_instances::at_numeric_point(env, declarations[1], bindings)?;
                if !restricted.guard_checked || restricted.guard != Some(false) {
                    return Err("relation適用域の反例が元guardを反証しない".into());
                }
                &restricted
            } else if let Some(domain) = &row.numeric_domain {
                restricted = relation_instances::on_numeric_domain(
                    env,
                    declarations[1],
                    target_bindings,
                    domain,
                )?;
                &restricted
            } else {
                target
            };
            support.extend(target.support.iter().cloned());
            scope.merge(&target.scope);
            if target.guard_checked && target.guard == Some(false) {
                let bindings = witness_bindings(sp, row, guard_point.as_deref(), c)?;
                let witness = example(
                    b,
                    sp,
                    &bindings,
                    &Scalar::Bool(true),
                    &Scalar::Bool(false),
                    &origin_deps,
                    &support,
                    c,
                )?;
                for index in 0..2 {
                    statuses[index] = Decision::Refuted;
                    evidence[index].push(witness);
                }
                out.evidence.push(witness);
                out.status = Decision::Refuted;
                continue;
            }
            if !target.guard_checked || target.guard != Some(true) {
                pending(
                    &mut out,
                    request,
                    &origin_deps,
                    declarations[1].span,
                    target.missing.clone(),
                );
                continue;
            }
            for r in [row, target] {
                if !matches!(r.state, RelationState::Established | RelationState::Refuted) {
                    pending(
                        &mut out,
                        request,
                        &origin_deps,
                        declarations[0].span,
                        r.missing.clone(),
                    );
                }
            }
            for (index, (sv, tv, checked)) in [
                (
                    &row.left,
                    &target.left,
                    row.left_checked && target.left_checked,
                ),
                (
                    &row.right,
                    &target.right,
                    row.right_checked && target.right_checked,
                ),
            ]
            .into_iter()
            .enumerate()
            {
                if !checked {
                    statuses[index] = merge_status(statuses[index], Decision::Undetermined);
                    continue;
                }
                let (Some(Scalar::Path(s)), Some(Scalar::Path(t))) = (sv, tv) else {
                    statuses[index] = merge_status(statuses[index], Decision::Undetermined);
                    continue;
                };
                let Some(expected) = word(s, &declarations[1].reading, &maps, &generators, c)?
                else {
                    statuses[index] = merge_status(statuses[index], Decision::Undetermined);
                    continue;
                };
                if !expected.same_program(t, c)? {
                    statuses[index] = Decision::Refuted;
                    let bindings = witness_bindings(sp, row, None, c)?;
                    let witness = example(
                        b,
                        sp,
                        &bindings,
                        &Scalar::Path(Box::new(expected)),
                        &Scalar::Path(t.clone()),
                        &origin_deps,
                        &support,
                        c,
                    )?;
                    evidence[index].push(witness);
                    out.evidence.push(witness);
                    out.status = Decision::Refuted;
                }
            }
        }
        if !complete {
            continue;
        }
        identity.sort();
        identity.dedup();
        let subjects = maps
            .iter()
            .flat_map(|m| m.subjects.iter().copied())
            .collect::<Vec<_>>();
        let types = [
            Type::Tuple(sp.iter().map(|p| p.ty.clone()).collect()),
            Type::Tuple(tp.iter().map(|p| p.ty.clone()).collect()),
        ];
        let arguments = value_map(b, [&types[0], &types[1]], &subjects, &identity, deps)?;
        let st = Type::Path(sa.clone(), sb.clone());
        let tt = Type::Path(ta.clone(), tb.clone());
        let values = value_map(b, [&st, &tt], &subjects, &identity, deps)?;
        let part = &mut b.parts[values.0 - b.base];
        if let Json::Obj(wire) = &mut part.wire {
            wire.insert(
                "generators".into(),
                Json::Arr(
                    generator_refs
                        .iter()
                        .map(|(s, t)| Json::Arr(vec![s.wire(), t.wire()]))
                        .collect(),
                ),
            );
        }
        part.arguments
            .extend(generator_refs.iter().flat_map(|(s, t)| [*s, *t]));
        let mut reasons = out.reasons[start_reasons..].to_vec();
        sort_reasons(&mut reasons);
        let mut clauses = vec![];
        let mut all = deps.to_vec();
        all.extend(origin_deps.iter().copied());
        all.extend([arguments, values]);
        for (index, origin) in origins.iter().enumerate() {
            let status = if reasons.is_empty() {
                statuses[index]
            } else {
                merge_status(statuses[index], Decision::Undetermined)
            };
            let proposition = b.proposition(
                "declaration_transport",
                vec![origin[0], origin[1], arguments, values],
                evidence[index]
                    .iter()
                    .copied()
                    .chain(origin_deps.iter().copied())
                    .collect(),
                status,
            )?;
            let part = &mut b.parts[proposition.0 - b.base];
            part.support = support.clone();
            part.support.sort();
            part.support.dedup();
            part.scope.merge(&scope);
            part.scope.assignments = true;
            let quantifiers = sp
                .iter()
                .map(|p| Quantifier {
                    kind: crate::law::ast::QuantKind::Forall,
                    name: p.name.clone(),
                    ty: p.ty.clone(),
                    domain: None,
                    occurrence: p.span,
                    context: None,
                })
                .collect::<Vec<_>>();
            part.scope.quantifiers.extend(quantifiers.iter().cloned());
            if let Json::Obj(wire) = &mut part.wire {
                wire.insert(
                    "quantifiers".into(),
                    Json::Arr(quantifiers.iter().map(Quantifier::wire).collect()),
                );
            }
            part.reasons = reasons.clone();
            part.evidence = evidence[index].clone();
            if let Some(j) = &mut part.judgment {
                j.reasons = part.reasons.clone();
                j.evidence = part.evidence.clone();
            }
            out.status = merge_status(out.status, status);
            all.extend([origin[0], origin[1], proposition]);
            all.extend(out.evidence[start_evidence..].iter().copied());
            clauses.push(Json::obj([
                ("source", origin[0].wire()),
                ("target", origin[1].wire()),
                ("arguments", arguments.wire()),
                ("values", values.wire()),
                ("commutes", proposition.wire()),
            ]));
        }
        out.transports.push(
            b.push(
                NodeType::Construction(T::DeclarationTransport),
                "declaration_transport",
                Json::obj([
                    ("kind", Json::str("relation")),
                    ("source", Json::str(&declarations[0].name)),
                    ("target", Json::str(&declarations[1].name)),
                    (
                        "parameters",
                        Json::Arr(
                            pair.parameters()
                                .iter()
                                .map(|(s, t)| Json::Arr(vec![Json::str(s), Json::str(t)]))
                                .collect(),
                        ),
                    ),
                    ("clauses", Json::Arr(clauses)),
                ]),
                all,
                None,
                None,
            )?,
        );
    }
    Ok(out)
}
