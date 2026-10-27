//! localの参照・field readを、実参照写像と可換な宣言式として保持する。
use super::*;
use crate::{
    law::{
        ast::ExprKind,
        model::{Param, Signature},
    },
    types::Type,
};
#[path = "object_local_field_transport.rs"]
mod field;
#[path = "object_change_transport.rs"]
mod change;
struct ParameterMap {
    source: String,
    target: String,
    values: NodeRef,
    transport: construction::ReferenceTypeTransport,
    subjects: Vec<(NodeRef, NodeRef)>,
}
enum Read {
    Projection(usize),
    Field { position: usize, names: [String; 2] },
}
pub(super) struct Output {
    pub transports: Vec<NodeRef>,
    pub status: Decision,
    pub reasons: Vec<Reason>,
    pub evidence: Vec<NodeRef>,
}
fn merge_status(current: Decision, next: Decision) -> Decision {
    if current == Decision::Refuted || next == Decision::Refuted {
        Decision::Refuted
    } else if current == Decision::Undetermined || next == Decision::Undetermined {
        Decision::Undetermined
    } else {
        Decision::Established
    }
}
// guardがある場合だけ全tupleを保持する。各readの反例もこの実割当てを使う。
struct Applicable {
    rows: Vec<Vec<usize>>,
    status: Decision,
    support: Vec<Fact>,
    scope: Scope,
    reasons: Vec<Reason>,
    evidence: Vec<NodeRef>,
}
fn counterexample(
    b: &mut Builder<'_>,
    params: &[Param],
    maps: &[Arc<ParameterMap>],
    row: &[usize],
    left: NodeRef,
    right: NodeRef,
    facts: &[Fact],
) -> Result<NodeRef, ValidationFailure> {
    let mut args = vec![left, right];
    let bindings = params
        .iter()
        .zip(maps)
        .zip(row)
        .map(|((p, map), &i)| {
            let value = map.subjects[i].0;
            args.push(value);
            Json::obj([
                ("name", Json::str(&p.name)),
                ("type", p.ty.wire()),
                ("value", value.wire()),
            ])
        })
        .collect();
    b.push(
        NodeType::Evidence,
        "evidence",
        Json::obj([
            ("kind", Json::str("counterexample")),
            (
                "data",
                Json::obj([
                    ("bindings", Json::Arr(bindings)),
                    ("paths", Json::Arr(vec![])),
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
fn applicable(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    declarations: [&crate::law::model::Declaration; 2],
    maps: &[Arc<ParameterMap>],
    origins: &[NodeRef],
    request: &Request,
    c: &mut Control,
) -> Result<Option<Applicable>, ValidationFailure> {
    let mut signatures = vec![];
    for declaration in declarations {
        let Signature::Local { params, guard, .. } = &declaration.signature else {
            return Err("guardの元宣言がlocalでない".into());
        };
        signatures.push((params, guard));
    }
    if signatures.iter().all(|(_, guard)| guard.is_none()) {
        return Ok(None);
    }
    let mut tuples = vec![vec![]];
    for map in maps {
        let mut next = vec![];
        for row in tuples {
            for i in 0..map.subjects.len() {
                tick(c)?;
                let mut row = row.clone();
                row.push(i);
                next.push(row);
            }
        }
        tuples = next;
    }
    let mut out = Applicable {
        rows: vec![],
        status: Decision::Established,
        support: vec![],
        scope: Scope::default(),
        reasons: vec![],
        evidence: vec![],
    };
    for row in tuples {
        tick(c)?;
        let mut values = [Some(true); 2];
        let mut missing = vec![];
        let mut facts = vec![];
        for side in 0..2 {
            if side == 1 && values[0] != Some(true) {
                break;
            }
            let (params, guard) = signatures[side];
            let Some(id) = guard else {
                continue;
            };
            let mut bindings = vec![];
            for ((p, map), &i) in params.iter().zip(maps).zip(&row) {
                let fact = if side == 0 {
                    &map.transport.source()[i]
                } else {
                    &map.transport.images()[i]
                };
                bindings.push((
                    p.name.clone(),
                    Scalar::Subject {
                        snapshot: fact.snapshot.clone(),
                        subject: fact.subject.clone(),
                        entity: if side == 0 {
                            map.source.clone()
                        } else {
                            map.target.clone()
                        },
                    },
                ));
            }
            let (value, support, scope, absent) =
                super::super::environment::local_read::guard_value(
                    env,
                    *id,
                    &bindings,
                    &declarations[side].reading,
                )?;
            values[side] = value;
            facts.extend(support.iter().cloned());
            out.support.extend(support);
            out.scope.merge(&scope);
            missing.extend(absent);
        }
        if values[0] == Some(false) {
            continue;
        }
        if values.iter().any(Option::is_none) {
            out.status = merge_status(out.status, Decision::Undetermined);
            missing.sort();
            missing.dedup();
            out.reasons.push(Reason {
                kind: if missing.is_empty() {
                    ReasonKind::UnsupportedAlgorithm {
                        question: request.kind,
                        operand_types: vec![Type::Bool],
                        method: "local_guard_applicability".into(),
                    }
                } else {
                    ReasonKind::Missing
                },
                request: request.id.clone(),
                dependencies: origins.to_vec(),
                missing,
                location: Some(crate::issue::Location::Law {
                    span: declarations[if values[0].is_none() { 0 } else { 1 }].span,
                }),
            });
            continue;
        }
        if values[1] == Some(false) {
            out.status = Decision::Refuted;
            let left = b.push(
                NodeType::Value(Type::Bool),
                "binding",
                Scalar::Bool(true).wire(),
                origins.to_vec(),
                Some(Scalar::Bool(true)),
                None,
            )?;
            let right = b.push(
                NodeType::Value(Type::Bool),
                "binding",
                Scalar::Bool(false).wire(),
                origins.to_vec(),
                Some(Scalar::Bool(false)),
                None,
            )?;
            out.evidence.push(counterexample(
                b,
                signatures[0].0,
                maps,
                &row,
                left,
                right,
                &facts,
            )?);
        } else {
            out.rows.push(row);
        }
    }
    out.support.sort();
    out.support.dedup();
    Ok(Some(out))
}

fn field_read(
    inputs: &super::super::input::CheckedInputs,
    mut id: usize,
    parameters: &[Param],
    c: &mut Control,
) -> Result<Option<(usize, String)>, ValidationFailure> {
    loop {
        tick(c)?;
        match &inputs.law().exprs[id].kind {
            ExprKind::Group(inner) => id = *inner,
            ExprKind::Dotted(parts) if parts.len() == 2 => {
                for (position, parameter) in parameters.iter().enumerate() {
                    tick(c)?;
                    if parameter.name == parts[0].name {
                        return Ok(Some((position, parts[1].name.clone())));
                    }
                }
                return Ok(None);
            }
            ExprKind::Field { base, name } => {
                return Ok(read_parameter(inputs, *base, parameters, c)?
                    .map(|position| (position, name.name.clone())));
            }
            _ => return Ok(None),
        }
    }
}

fn read_parameter(
    inputs: &super::super::input::CheckedInputs,
    mut id: usize,
    parameters: &[Param],
    c: &mut Control,
) -> Result<Option<usize>, ValidationFailure> {
    loop {
        tick(c)?;
        match &inputs.law().exprs[id].kind {
            ExprKind::Group(inner) => id = *inner,
            ExprKind::Dotted(parts) if parts.len() == 1 => {
                for (position, parameter) in parameters.iter().enumerate() {
                    tick(c)?;
                    if parts[0].name == parameter.name {
                        return Ok(Some(position));
                    }
                }
                return Ok(None);
            }
            _ => return Ok(None),
        }
    }
}
fn domain(
    b: &mut Builder<'_>,
    ty: &Type,
    dependencies: &[NodeRef],
) -> Result<NodeRef, ValidationFailure> {
    b.push(
        NodeType::Domain,
        "domain",
        Json::obj([("kind", Json::str("type")), ("type", ty.wire())]),
        dependencies.to_vec(),
        None,
        None,
    )
}
fn value_map(
    b: &mut Builder<'_>,
    types: [&Type; 2],
    subjects: &[(NodeRef, NodeRef)],
    declarations: &[(String, String)],
    dependencies: &[NodeRef],
) -> Result<NodeRef, ValidationFailure> {
    let source = domain(b, types[0], dependencies)?;
    let target = domain(b, types[1], dependencies)?;
    let mut args = dependencies.to_vec();
    args.extend([source, target]);
    args.extend(subjects.iter().flat_map(|(a, z)| [*a, *z]));
    b.push(
        NodeType::Construction(T::ValueMap),
        "value_map",
        Json::obj([
            ("source", source.wire()),
            ("target", target.wire()),
            ("source_type", types[0].wire()),
            ("target_type", types[1].wire()),
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
                        .map(|(a, z)| Json::Arr(vec![Json::str(a), Json::str(z)]))
                        .collect(),
                ),
            ),
            ("generators", Json::Arr(vec![])),
        ]),
        args,
        None,
        None,
    )
}
fn reference_map(
    b: &mut Builder<'_>,
    inputs: &super::super::input::CheckedInputs,
    declarations: &construction::DeclarationCorrespondence,
    st: &str,
    tt: &str,
    dependencies: &[NodeRef],
    c: &mut Control,
) -> Result<Arc<ParameterMap>, ValidationFailure> {
    let transport =
        construction::reference_type_transport(inputs, declarations, st, c).map_err(failure)?;
    if transport.target_type() != tt
        || transport
            .failures()
            .iter()
            .any(|f| matches!(f, construction::ReferenceConditionFailure::ImageType { .. }))
    {
        return Err("local参照写像の像型が違う".into());
    }
    let mut subjects = vec![];
    for (s, t) in transport.source().iter().zip(transport.images()) {
        tick(c)?;
        let mut refs = vec![];
        for (fact, entity) in [(s, st), (t, tt)] {
            let scalar = Scalar::Subject {
                snapshot: fact.snapshot.clone(),
                subject: fact.subject.clone(),
                entity: entity.into(),
            };
            refs.push(b.push(
                NodeType::Value(scalar.ty()),
                "binding",
                scalar.wire(),
                dependencies.to_vec(),
                Some(scalar),
                None,
            )?);
        }
        subjects.push((refs[0], refs[1]));
    }
    let values = value_map(
        b,
        [&Type::Ref(st.into()), &Type::Ref(tt.into())],
        &subjects,
        declarations.types(),
        dependencies,
    )?;
    let map = Arc::new(ParameterMap {
        source: st.into(),
        target: tt.into(),
        values,
        transport,
        subjects,
    });
    Ok(map)
}
fn expression(
    b: &mut Builder<'_>,
    inputs: &super::super::input::CheckedInputs,
    id: usize,
    params: &[Param],
    dependencies: &[NodeRef],
) -> Result<NodeRef, ValidationFailure> {
    let ty = inputs
        .law()
        .expr_type(id)
        .ok_or("local readの元型がない")?
        .clone();
    b.push(
        NodeType::Expression(ty),
        "expression",
        Json::obj([
            ("kind", Json::str("source")),
            (
                "location",
                crate::result::location_wire(&crate::issue::Location::Law {
                    span: inputs.law().exprs[id].span,
                }),
            ),
            (
                "parameters",
                Json::Arr(
                    params
                        .iter()
                        .map(|p| Json::obj([("name", Json::str(&p.name)), ("type", p.ty.wire())]))
                        .collect(),
                ),
            ),
            ("bindings", Json::Arr(vec![])),
        ]),
        dependencies.to_vec(),
        None,
        None,
    )
}
pub(super) fn retain(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    inputs: &super::super::input::CheckedInputs,
    declarations: &construction::DeclarationCorrespondence,
    dependencies: &[NodeRef],
    request: &Request,
    c: &mut Control,
) -> Result<Output, ValidationFailure> {
    let mut result = Output {
        transports: vec![],
        status: Decision::Established,
        reasons: vec![],
        evidence: vec![],
    };
    for candidate in declarations.candidates() {
        tick(c)?;
        if candidate.source().kind == "change" {
            let out = change::retain(env, b, inputs, declarations, candidate, dependencies, request, c)?;
            result.transports.extend(out.transports);
            result.status = merge_status(result.status, out.status);
            result.reasons.extend(out.reasons); result.evidence.extend(out.evidence);
            continue;
        }
        if candidate.source().kind != "local" {
            continue;
        }
        let pair = candidate.pair().ok_or("localの対応署名がない")?;
        let source = &inputs.law().declarations[pair.source()];
        let target = &inputs.law().declarations[pair.target()];
        let (
            Signature::Local {
                params: sp,
                guard: sg,
                reads: sr,
            },
            Signature::Local {
                params: tp,
                guard: tg,
                reads: tr,
            },
        ) = (&source.signature, &target.signature)
        else {
            return Err("localの対応宣言がlocalでない".into());
        };
        if sp.len() != tp.len() || sr.len() != tr.len() {
            return Err("参照射影以外のlocal宣言移送は未実装".into());
        }
        let mut reads = vec![];
        for (&s, &t) in sr.iter().zip(tr) {
            if let Some(position) = read_parameter(inputs, s, sp, c)? {
                if read_parameter(inputs, t, tp, c)? != Some(position) {
                    return Err("異なる引数射影のlocal read移送は未実装".into());
                }
                reads.push(Read::Projection(position));
            } else if let (Some((a, source)), Some((z, target))) =
                (field_read(inputs, s, sp, c)?, field_read(inputs, t, tp, c)?)
            {
                if a != z {
                    return Err("異なる引数のfield read移送は未実装".into());
                }
                reads.push(Read::Field {
                    position: a,
                    names: [source, target],
                });
            } else {
                return Err("local readの式移送は未実装".into());
            }
        }
        let mut parameter_maps = vec![];
        let mut type_maps: Vec<Arc<ParameterMap>> = vec![];
        let mut argument_subjects = vec![];
        for (source, target) in sp.iter().zip(tp) {
            tick(c)?;
            let (Type::Ref(st), Type::Ref(tt)) = (&source.ty, &target.ty) else {
                return Err("非参照local引数の移送は未実装".into());
            };
            if let Some(map) = type_maps
                .iter()
                .find(|map| &map.source == st && &map.target == tt)
            {
                parameter_maps.push(map.clone());
                continue;
            }
            let map = reference_map(b, inputs, declarations, st, tt, dependencies, c)?;
            argument_subjects.extend(map.subjects.iter().copied());
            type_maps.push(map.clone());
            parameter_maps.push(map);
        }
        let mut guard_expressions = vec![];
        for (guard, params) in [(*sg, sp), (*tg, tp)] {
            if let Some(id) = guard {
                let r = expression(b, inputs, id, params, dependencies)?;
                guard_expressions.push(r);
            }
        }
        let args = [
            Type::Tuple(sp.iter().map(|p| p.ty.clone()).collect()),
            Type::Tuple(tp.iter().map(|p| p.ty.clone()).collect()),
        ];
        let arguments = value_map(
            b,
            [&args[0], &args[1]],
            &argument_subjects,
            declarations.types(),
            dependencies,
        )?;
        let applicable = applicable(
            b,
            env,
            [source, target],
            &parameter_maps,
            &guard_expressions,
            request,
            c,
        )?;
        let mut clauses = vec![];
        let mut all = dependencies.to_vec();
        all.extend(guard_expressions.iter().copied());
        for ((&s, &t), read) in sr.iter().zip(tr).zip(reads) {
            tick(c)?;
            let se = expression(b, inputs, s, sp, dependencies)?;
            let te = expression(b, inputs, t, tp, dependencies)?;
            let mut comparison = match read {
                Read::Projection(position) => field::Comparison {
                    values: parameter_maps[position].values,
                    status: Decision::Established,
                    arguments: vec![],
                    reasons: vec![],
                    evidence: vec![],
                    support: vec![],
                    scope: Scope::default(),
                },
                Read::Field { position, names } => field::compare(
                    b,
                    env,
                    inputs,
                    [source, target],
                    declarations,
                    &parameter_maps,
                    applicable.as_ref().map(|domain| domain.rows.as_slice()),
                    position,
                    &names,
                    [s, t],
                    [se, te],
                    dependencies,
                    request,
                    c,
                )?,
            };
            if let Some(domain) = &applicable {
                comparison.status = merge_status(comparison.status, domain.status);
                comparison.support.extend(domain.support.iter().cloned());
                comparison.scope.merge(&domain.scope);
                comparison.reasons.extend(domain.reasons.iter().cloned());
                comparison.evidence.extend(domain.evidence.iter().copied());
                comparison.arguments.extend(domain.evidence.iter().copied());
            }
            let values = comparison.values;
            let mut comparison_arguments = comparison.arguments;
            comparison_arguments.extend(guard_expressions.iter().copied());
            let commutes = b.proposition(
                "declaration_transport",
                vec![se, te, arguments, values],
                comparison_arguments,
                comparison.status,
            )?;
            let p = &mut b.parts[commutes.0 - b.base];
            p.support.extend(comparison.support);
            p.support.sort();
            p.support.dedup();
            p.scope.merge(&comparison.scope);
            p.reasons.extend(comparison.reasons.iter().cloned());
            sort_reasons(&mut p.reasons);
            p.evidence.extend(comparison.evidence.iter().copied());
            if let Some(judgment) = p.judgment.as_mut() {
                judgment.reasons = p.reasons.clone();
                judgment.evidence = p.evidence.clone();
            }
            result.status = merge_status(result.status, comparison.status);
            result.reasons.extend(comparison.reasons);
            result.evidence.extend(comparison.evidence);
            p.scope.assignments = true;
            let quantifiers: Vec<_> = sp
                .iter()
                .map(|parameter| Quantifier {
                    kind: crate::law::ast::QuantKind::Forall,
                    name: parameter.name.clone(),
                    ty: parameter.ty.clone(),
                    domain: None,
                    occurrence: parameter.span,
                    context: None,
                })
                .collect();
            p.scope.quantifiers.extend(quantifiers.iter().cloned());
            if let Json::Obj(wire) = &mut p.wire {
                wire.insert(
                    "quantifiers".into(),
                    Json::Arr(quantifiers.iter().map(Quantifier::wire).collect()),
                );
            }
            all.extend([se, te, arguments, values, commutes]);
            clauses.push(Json::obj([
                ("source", se.wire()),
                ("target", te.wire()),
                ("arguments", arguments.wire()),
                ("values", values.wire()),
                ("commutes", commutes.wire()),
            ]));
        }
        result.transports.push(
            b.push(
                NodeType::Construction(T::DeclarationTransport),
                "declaration_transport",
                Json::obj([
                    ("kind", Json::str("local")),
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
                    ("clauses", Json::Arr(clauses)),
                ]),
                all,
                None,
                None,
            )?,
        );
    }
    sort_reasons(&mut result.reasons);
    Ok(result)
}
