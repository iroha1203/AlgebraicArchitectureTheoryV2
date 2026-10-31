//! localの参照・field readを、実参照写像と可換な宣言式として保持する。
use super::*;
use crate::{
    law::{
        ast::ExprKind,
        model::{Param, Signature},
    },
    types::Type,
    observed::environment::numeric_parameters,
};
use std::collections::BTreeSet;
#[path = "object_local_field_transport.rs"]
mod field;
#[path = "object_local_numeric_transport.rs"]
mod numeric_read;
#[path = "object_change_transport.rs"]
mod change;
#[path = "object_relation_transport.rs"]
mod relation;
struct ParameterMap {
    source: String,
    target: String,
    values: NodeRef,
    transport: construction::ReferenceTypeTransport,
    subjects: Vec<(NodeRef, NodeRef)>,
}
// localの各引数位置を保ち、既存の参照写像または有限全域の候補像を読む。
enum LocalParameter {
    // One symbolic coordinate in the finite-row index, never a sampled value.
    Numeric { values: NodeRef },
    Reference(Arc<ParameterMap>),
    Finite {
        transport: super::super::value_transport::FiniteValueTransport,
        values: NodeRef,
        sources: Vec<NodeRef>,
    },
}
impl LocalParameter {
    fn reference(&self) -> Option<&Arc<ParameterMap>> {
        match self {
            Self::Reference(map) => Some(map),
            _ => None,
        }
    }
    fn len(&self) -> usize {
        match self {
            Self::Reference(map) => map.subjects.len(),
            Self::Finite { transport, .. } => transport.source().len(),
            Self::Numeric { .. } => 1,
        }
    }
    fn values(&self) -> NodeRef {
        match self {
            Self::Reference(map) => map.values,
            Self::Finite { values, .. } | Self::Numeric { values } => *values,
        }
    }
    fn source_value(&self, index: usize) -> Result<NodeRef, ValidationFailure> {
        Ok(match self {
            Self::Reference(map) => map.subjects[index].0,
            Self::Finite { sources, .. } => sources[index],
            Self::Numeric { .. } => return Err("symbolic number has no finite source value".into()),
        })
    }
    fn binding(&self, index: usize, side: usize) -> Result<Scalar, ValidationFailure> {
        Ok(match self {
            Self::Reference(map) => {
                let (fact, entity) = if side == 0 {
                    (&map.transport.source()[index], &map.source)
                } else {
                    (&map.transport.images()[index], &map.target)
                };
                Scalar::Subject {
                    snapshot: fact.snapshot.clone(),
                    subject: fact.subject.clone(),
                    entity: entity.clone(),
                }
            }
            Self::Finite { transport, .. } => {
                let values = if side == 0 {
                    transport.source()
                } else {
                    transport.images()
                };
                values[index].scalar().clone()
            }
            Self::Numeric { .. } => return Err("symbolic number has no finite binding".into()),
        })
    }
}
enum ReadValueMap {
    Finite(super::super::value_transport::FiniteValueTransport, NodeRef),
    Structural(NodeRef, bool), // 型全域の値写像と、その恒等性。
}
impl ReadValueMap {
    fn is_identity(&self, c: &mut Control) -> Result<bool, ValidationFailure> {
        match self {
            Self::Structural(_, identity) => Ok(*identity),
            Self::Finite(transport, _) => {
                if transport.source_type() != transport.target_type() {
                    return Ok(false);
                }
                for (source, image) in transport.source().iter().zip(transport.images()) {
                    tick(c)?;
                    if source != image {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    }
    fn values(&self) -> NodeRef {
        match self {
            Self::Finite(_, values) | Self::Structural(values, _) => *values,
        }
    }
}

enum Read {
    Projection(usize),
    Expression,
    Field { position: usize, names: [String; 2] },
}
pub(super) struct Output {
    pub transports: Vec<NodeRef>,
    // 移送の構成条件を反証する元の型付きValue/Expression。read値の反例とは区別する。
    pub failed_arguments: Vec<NodeRef>,
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
    maps: &[LocalParameter],
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
            let value = map.source_value(i)?;
            args.push(value);
            Ok(Json::obj([
                ("name", Json::str(&p.name)),
                ("type", p.ty.wire()),
                ("value", value.wire()),
            ]))
        })
        .collect::<Result<Vec<_>, ValidationFailure>>()?;
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
fn parameter_rows(
    maps: &[LocalParameter],
    c: &mut Control,
) -> Result<Vec<Vec<usize>>, ValidationFailure> {
    let mut tuples = vec![vec![]];
    for map in maps {
        let mut next = vec![];
        for row in tuples {
            for i in 0..map.len() {
                tick(c)?;
                let mut row = row.clone();
                row.push(i);
                next.push(row);
            }
        }
        tuples = next;
    }
    Ok(tuples)
}
fn applicable(
    b: &mut Builder<'_>,
    env: &Environment<'_>,
    declarations: [&crate::law::model::Declaration; 2],
    maps: &[LocalParameter],
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
    let mut out = Applicable {
        rows: vec![],
        status: Decision::Established,
        support: vec![],
        scope: Scope::default(),
        reasons: vec![],
        evidence: vec![],
    };
    for row in parameter_rows(maps, c)? {
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
                bindings.push((p.name.clone(), map.binding(i, side)?));
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
    inputs: &crate::input::CheckedInputs,
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
    inputs: &crate::input::CheckedInputs,
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
    inputs: &crate::input::CheckedInputs,
    declarations: &construction::DeclarationCorrespondence,
    st: &str,
    tt: &str,
    dependencies: &[NodeRef],
    c: &mut Control,
) -> Result<Arc<ParameterMap>, ValidationFailure> {
    checked_reference_map(
        b,
        inputs,
        declarations,
        st,
        tt,
        dependencies,
        &mut vec![],
        c,
    )?
    .ok_or_else(|| "local参照写像の像型が違う".into())
}
fn checked_reference_map(
    b: &mut Builder<'_>,
    inputs: &crate::input::CheckedInputs,
    declarations: &construction::DeclarationCorrespondence,
    st: &str,
    tt: &str,
    dependencies: &[NodeRef],
    failed_arguments: &mut Vec<NodeRef>,
    c: &mut Control,
) -> Result<Option<Arc<ParameterMap>>, ValidationFailure> {
    let transport =
        construction::reference_type_transport(inputs, declarations, st, c).map_err(failure)?;
    if transport.target_type() != tt {
        return Err("local参照写像の終域型が宣言対応と違う".into());
    }
    if let Some(construction::ReferenceConditionFailure::ImageType { source, .. }) = transport
        .failures()
        .iter()
        .find(|f| matches!(f, construction::ReferenceConditionFailure::ImageType { .. }))
    {
        let scalar = Scalar::Subject {
            snapshot: source.snapshot.clone(),
            subject: source.subject.clone(),
            entity: st.into(),
        };
        failed_arguments.push(b.push(
            NodeType::Value(scalar.ty()),
            "binding",
            scalar.wire(),
            dependencies.to_vec(),
            Some(scalar),
            None,
        )?);
        return Ok(None);
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
    Ok(Some(map))
}

fn outside_value(
    b: &mut Builder<'_>,
    transport: &super::super::value_transport::FiniteValueTransport,
    dependencies: &[NodeRef],
) -> Result<Option<NodeRef>, ValidationFailure> {
    let index = transport.failures().iter().find_map(|f| match f {
        super::super::value_transport::FiniteValueConditionFailure::OutsideTarget {
            source,
            ..
        } => Some(*source),
        _ => None,
    });
    index
        .map(|i| {
            let value = transport.source()[i].scalar().clone();
            b.push(
                NodeType::Value(value.ty()),
                "binding",
                value.wire(),
                dependencies.to_vec(),
                Some(value),
                None,
            )
        })
        .transpose()
}
fn value_type_map(
    b: &mut Builder<'_>,
    inputs: &crate::input::CheckedInputs,
    declarations: &construction::DeclarationCorrespondence,
    declaration: &str,
    types: [&Type; 2],
    type_maps: &mut Vec<Arc<ParameterMap>>,
    dependencies: &[NodeRef],
    failed_arguments: &mut Vec<NodeRef>,
    c: &mut Control,
) -> Result<
    Option<(
        NodeRef,
        Vec<(NodeRef, NodeRef)>,
        Vec<(String, String)>,
        bool,
    )>,
    ValidationFailure,
> {
    let mut pending = vec![types[0]];
    let mut references = BTreeSet::new();
    let mut families = BTreeSet::new();
    let mut names = BTreeSet::new();
    let mut map_types = vec![];
    let type_action = declarations.types().iter().cloned().collect();
    while let Some(ty) = pending.pop() {
        tick(c)?;
        match ty {
            Type::Ref(name) => {
                references.insert(name.clone());
            }
            Type::Tuple(items) => pending.extend(items),
            Type::Option(item) | Type::Set(item) | Type::List(item) => pending.push(item),
            Type::Map(a, b) => {
                if !map_types.contains(&ty) {
                    map_types.push(ty);
                }
                pending.extend([a.as_ref(), b.as_ref()]);
            }
            Type::Data(family) => {
                if families.insert(family.clone()) {
                    names.insert(family.clone());
                    for ctor in super::super::data::constructors(inputs.law(), family)? {
                        tick(c)?;
                        names.insert(format!("{family}.{}", ctor.name));
                        // Dataのfamilyとconstructorは固定する。全payload型が同じ
                        // familyの引数型へ戻ることを、空値や未評価の枝でも確認する。
                        for arg in &ctor.arguments {
                            let moved = construction::moved_declaration_type(
                                arg,
                                &type_action,
                                &std::collections::BTreeMap::new(),
                                c,
                            )
                            .map_err(failure)?;
                            if moved != *arg {
                                failed_arguments.extend([
                                    domain(b, arg, dependencies)?,
                                    domain(b, &moved, dependencies)?,
                                ]);
                                return Ok(None);
                            }
                        }
                        pending.extend(&ctor.arguments);
                    }
                }
            }
            Type::Unit | Type::Bool | Type::Fp(_) | Type::Z | Type::Q | Type::Text => {}
            _ => return Err("値写像の型構造が未対応".into()),
        }
    }
    let mut pairs = if references.is_empty() {
        vec![]
    } else {
        declarations.types().to_vec()
    };
    pairs.extend(names.into_iter().map(|n| (n.clone(), n)));
    pairs.sort();
    pairs.dedup();
    let mut subjects = vec![];
    let mut identity = types[0] == types[1];
    for st in references {
        let tt = declarations
            .types()
            .iter()
            .find(|(s, _)| s == &st)
            .map(|(_, t)| t.as_str())
            .unwrap_or(&st);
        let map = if let Some(map) = type_maps
            .iter()
            .find(|map| map.source == st && map.target == tt)
        {
            map.clone()
        } else {
            let Some(map) = checked_reference_map(
                b,
                inputs,
                declarations,
                &st,
                tt,
                dependencies,
                failed_arguments,
                c,
            )?
            else {
                return Ok(None);
            };
            type_maps.push(map.clone());
            map
        };
        identity &= map.source == map.target;
        for (source, image) in map.transport.source().iter().zip(map.transport.images()) {
            tick(c)?;
            identity &= source == image;
        }
        subjects.extend(map.subjects.iter().copied());
    }
    // 有限の全型域は呼出側で検査済み。無限複合ではMap成分を全列挙する。
    if !map_types.is_empty() && !super::super::finite::supported(types[0], inputs.law(), c)? {
        for ty in map_types {
            if let Some(value) = super::super::value_transport::finite_type_domain_failure(
                inputs,
                declarations,
                declaration,
                ty,
                c,
            )
            .map_err(failure)?
            {
                failed_arguments.push(b.push(
                    NodeType::Value(value.ty()),
                    "binding",
                    value.wire(),
                    dependencies.to_vec(),
                    Some(value),
                    None,
                )?);
                return Ok(None);
            }
        }
    }
    let values = value_map(b, types, &subjects, &pairs, dependencies)?;
    Ok(Some((values, subjects, pairs, identity)))
}

fn expression(
    b: &mut Builder<'_>,
    inputs: &crate::input::CheckedInputs,
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
    inputs: &crate::input::CheckedInputs,
    declarations: &construction::DeclarationCorrespondence,
    dependencies: &[NodeRef],
    request: &Request,
    c: &mut Control,
) -> Result<Output, ValidationFailure> {
    let mut result = Output {
        transports: vec![],
        failed_arguments: vec![],
        status: Decision::Established,
        reasons: vec![],
        evidence: vec![],
    };
    let related = relation::retain(env, b, inputs, declarations, dependencies, request, c)?;
    result.transports.extend(related.transports);
    result.failed_arguments.extend(related.failed_arguments);
    result.status = merge_status(result.status, related.status);
    result.reasons.extend(related.reasons);
    result.evidence.extend(related.evidence);
    'declarations: for candidate in declarations.candidates() {
        tick(c)?;
        if candidate.source().kind == "change" {
            let out = change::retain(env, b, inputs, declarations, candidate, dependencies, request, c)?;
            result.transports.extend(out.transports);
            result.failed_arguments.extend(out.failed_arguments);
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
        let unsupported = |method: &str| Reason {
            kind: ReasonKind::UnsupportedAlgorithm {
                question: request.kind,
                operand_types: sp
                    .iter()
                    .map(|p| p.ty.clone())
                    .chain(
                        sr.iter()
                            .filter_map(|id| inputs.law().expr_type(*id).map(|t| t.erase())),
                    )
                    .collect(),
                method: method.into(),
            },
            request: request.id.clone(),
            dependencies: dependencies.to_vec(),
            missing: vec![],
            location: Some(crate::issue::Location::Law { span: source.span }),
        };
        for parameter in sp {
            tick(c)?;
            if !matches!(parameter.ty, Type::Ref(_))
                && numeric_parameters::numeric_width(&parameter.ty).is_none()
                && !super::super::finite::supported(&parameter.ty, inputs.law(), c)?
            {
                result.status = merge_status(result.status, Decision::Undetermined);
                result
                    .reasons
                    .push(unsupported("local_parameter_domain_transport"));
                continue 'declarations;
            }
        }
        let coefficient = sp
            .iter()
            .find_map(|p| numeric_parameters::coefficient_type(&p.ty));
        if coefficient.is_some()
            && sr.iter().zip(tr).any(|(s, t)| {
                let ty = inputs.law().expr_type(*s).map(|t| t.erase());
                ty != inputs.law().expr_type(*t).map(|t| t.erase())
                    || !matches!(ty, Some(Type::Z | Type::Q))
            })
        {
            result.status = merge_status(result.status, Decision::Undetermined);
            result
                .reasons
                .push(unsupported("local_read_coefficient_transport"));
            continue;
        }
        let mut reads = vec![];
        for (&s, &t) in sr.iter().zip(tr) {
            if coefficient.is_some() {
                reads.push(Read::Expression);
                continue;
            }
            let read_type = inputs.law().expr_type(s).map(|ty| ty.erase());
            let expression_read = match &read_type {
                Some(ty) => {
                    super::super::finite::supported(ty, inputs.law(), c)?
                        || (!sp.is_empty()
                            && super::super::environment::local_read::value_type_supported(
                                ty,
                                inputs.law(),
                                c,
                            )?
                            && inputs.law().expr_type(t).map(|ty| ty.erase()) == read_type)
                        || (!sp.is_empty()
                            && super::super::environment::local_read::reference_value_type_supported(
                                ty, inputs.law(), c,
                            )?)
                }
                None => false,
            };
            if let Some(position) = read_parameter(inputs, s, sp, c)? {
                if read_parameter(inputs, t, tp, c)? == Some(position) {
                    reads.push(Read::Projection(position));
                } else if expression_read {
                    reads.push(Read::Expression);
                } else {
                    return Err("異なる引数射影のlocal read移送は未実装".into());
                }
            } else if let (Some((a, source)), Some((z, target))) =
                (field_read(inputs, s, sp, c)?, field_read(inputs, t, tp, c)?)
            {
                if a == z {
                    reads.push(Read::Field {
                        position: a,
                        names: [source, target],
                    });
                } else if expression_read {
                    reads.push(Read::Expression);
                } else {
                    return Err("異なる引数のfield read移送は未実装".into());
                }
            } else if expression_read {
                reads.push(Read::Expression);
            } else {
                return Err("local readの式移送は未実装".into());
            }
        }
        let mut parameter_maps = vec![];
        let mut type_maps: Vec<Arc<ParameterMap>> = vec![];
        let mut argument_subjects = vec![];
        let mut argument_declarations = declarations.types().to_vec();
        for (position, (source, target)) in sp.iter().zip(tp).enumerate() {
            tick(c)?;
            if !matches!(source.ty, Type::Ref(_))
                && super::super::finite::supported(&source.ty, inputs.law(), c)?
            {
                let transport = super::super::value_transport::finite_declaration_value_transport(
                    inputs,
                    declarations,
                    &candidate.source().name,
                    super::super::value_transport::DeclarationValuePosition::Parameter(position),
                    c,
                )
                .map_err(failure)?;
                if let Some(value) = outside_value(b, &transport, dependencies)? {
                    result.failed_arguments.push(value);
                    result.status = Decision::Refuted;
                    continue 'declarations;
                }
                let Some((values, subjects, value_declarations, _)) = value_type_map(
                    b,
                    inputs,
                    declarations,
                    &candidate.source().name,
                    [transport.source_type(), transport.target_type()],
                    &mut type_maps,
                    dependencies,
                    &mut result.failed_arguments,
                    c,
                )? else {
                    result.status = Decision::Refuted;
                    continue 'declarations;
                };
                argument_subjects.extend(subjects);
                let mut sources = vec![];
                for value in transport.source() {
                    tick(c)?;
                    let scalar = value.scalar().clone();
                    sources.push(b.push(
                        NodeType::Value(source.ty.clone()),
                        "binding",
                        scalar.wire(),
                        dependencies.to_vec(),
                        Some(scalar),
                        None,
                    )?);
                }
                argument_declarations.extend(value_declarations);
                parameter_maps.push(LocalParameter::Finite {
                    transport,
                    values,
                    sources,
                });
                continue;
            }
            if numeric_parameters::numeric_width(&source.ty).is_some() && source.ty == target.ty {
                super::super::numeric_transport::numeric_declaration_value_transport(
                    inputs,
                    declarations,
                    &candidate.source().name,
                    super::super::value_transport::DeclarationValuePosition::Parameter(position),
                    c,
                ).map_err(failure)?;
                let values = value_map(b, [&source.ty, &target.ty], &[], &[], dependencies)?;
                parameter_maps.push(LocalParameter::Numeric { values });
                continue;
            }
            let (Type::Ref(st), Type::Ref(tt)) = (&source.ty, &target.ty) else {
                return Err("local argument type has no supported finite value transport".into());
            };
            if let Some(map) = type_maps
                .iter()
                .find(|map| &map.source == st && &map.target == tt)
            {
                parameter_maps.push(LocalParameter::Reference(map.clone()));
                continue;
            }
            let map = reference_map(b, inputs, declarations, st, tt, dependencies, c)?;
            argument_subjects.extend(map.subjects.iter().copied());
            type_maps.push(map.clone());
            parameter_maps.push(LocalParameter::Reference(map));
        }
        let infinite = parameter_maps.iter().any(|p| matches!(p, LocalParameter::Numeric { .. }));
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
        argument_declarations.sort();
        argument_declarations.dedup();
        argument_subjects.sort_by_key(|(a, b)| (a.0, b.0));
        argument_subjects.dedup();
        let arguments = value_map(
            b,
            [&args[0], &args[1]],
            &argument_subjects,
            &argument_declarations,
            dependencies,
        )?;
        // 戻り値の全型域も、guard/readの実評価より先に検査する。
        let mut read_maps = vec![];
        for (index, read) in reads.iter().enumerate() {
            let ty = inputs
                .law()
                .expr_type(sr[index])
                .ok_or("local read型がない")?
                .erase();
            let finite = super::super::finite::supported(&ty, inputs.law(), c)?;
            let structural = !sp.is_empty()
                && super::super::environment::local_read::reference_value_type_supported(&ty, inputs.law(), c)?;
            if !matches!(read, Read::Projection(_)) && (finite || structural) {
                let expected = construction::moved_declaration_type(
                    inputs
                        .law()
                        .expr_type(sr[index])
                        .ok_or("local readの元型がない")?,
                    &declarations.types().iter().cloned().collect(),
                    &pair.parameters().iter().cloned().collect(),
                    c,
                )
                .map_err(failure)?;
                if inputs.law().expr_type(tr[index]) != Some(&expected) {
                    // 型写像を構成できない。評価値の反例ではなく、両原式の型を残す。
                    result.failed_arguments.extend([
                        expression(b, inputs, sr[index], sp, dependencies)?,
                        expression(b, inputs, tr[index], tp, dependencies)?,
                    ]);
                    result.status = Decision::Refuted;
                    continue 'declarations;
                }
                if !finite {
                    let Some((values, _, _, identity)) = value_type_map(
                        b,
                        inputs,
                        declarations,
                        &candidate.source().name,
                        [&ty, &expected.erase()],
                        &mut type_maps,
                        dependencies,
                        &mut result.failed_arguments,
                        c,
                    )? else {
                        result.status = Decision::Refuted;
                        continue 'declarations;
                    };
                    read_maps.push(Some(ReadValueMap::Structural(values, identity)));
                    continue;
                }
                let transport = super::super::value_transport::finite_declaration_value_transport(
                    inputs,
                    declarations,
                    &candidate.source().name,
                    super::super::value_transport::DeclarationValuePosition::LocalRead(index),
                    c,
                )
                .map_err(failure)?;
                if let Some(value) = outside_value(b, &transport, dependencies)? {
                    result.failed_arguments.push(value);
                    result.status = Decision::Refuted;
                    continue 'declarations;
                }
                let Some((values, _, _, _)) = value_type_map(
                    b,
                    inputs,
                    declarations,
                    &candidate.source().name,
                    [transport.source_type(), transport.target_type()],
                    &mut type_maps,
                    dependencies,
                    &mut result.failed_arguments,
                    c,
                )? else {
                    result.status = Decision::Refuted;
                    continue 'declarations;
                };
                read_maps.push(Some(ReadValueMap::Finite(transport, values)));
            } else {
                read_maps.push(None);
            }
        }
        let applicable = if infinite {
            None
        } else {
            applicable(b, env, [source, target], &parameter_maps, &guard_expressions, request, c)?
        };
        let mut clauses = vec![];
        let mut all = dependencies.to_vec();
        all.extend(guard_expressions.iter().copied());
        for (((&s, &t), read), read_map) in sr.iter().zip(tr).zip(reads).zip(&read_maps) {
            tick(c)?;
            let se = expression(b, inputs, s, sp, dependencies)?;
            let te = expression(b, inputs, t, tp, dependencies)?;
            let mut comparison = if infinite {
                let read_type = inputs.law().expr_type(s).ok_or("local read type missing")?.erase();
                let ty = &read_type;
                let values = value_map(b, [ty, ty], &[], &[], dependencies)?;
                numeric_read::compare(
                    b, env, [source, target], &parameter_maps, [s, t], ty, values,
                    &[se, te], request, c,
                )?
            } else { match read {
                Read::Projection(position) => field::Comparison {
                    values: parameter_maps[position].values(),
                    status: Decision::Established,
                    arguments: vec![],
                    reasons: vec![],
                    evidence: vec![],
                    support: vec![],
                    scope: Scope::default(),
                },
                read @ (Read::Expression | Read::Field { .. }) => {
                    let direct = match &read {
                        Read::Field { position, names } => Some((*position, names)),
                        _ => None,
                    };
                    field::compare_expression(
                        b, env, inputs, [source, target], declarations, &parameter_maps,
                        read_map.as_ref(), direct,
                        applicable.as_ref().map(|domain| domain.rows.as_slice()),
                        [s, t], [se, te], dependencies, request, c,
                    )?
                },
            } };
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
