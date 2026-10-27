//! 参照そのものを読むlocalの句を、実参照写像と可換な宣言式として保持する。
use super::*;
use crate::{
    law::{
        ast::ExprKind,
        model::{Param, Signature},
    },
    types::Type,
};

fn identity_read(
    inputs: &super::super::input::CheckedInputs,
    mut id: usize,
    name: &str,
    c: &mut Control,
) -> Result<bool, ValidationFailure> {
    loop {
        tick(c)?;
        match &inputs.law().exprs[id].kind {
            ExprKind::Group(inner) => id = *inner,
            ExprKind::Dotted(parts) => return Ok(parts.len() == 1 && parts[0].name == name),
            _ => return Ok(false),
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
    b: &mut Builder<'_>,
    inputs: &super::super::input::CheckedInputs,
    declarations: &construction::DeclarationCorrespondence,
    dependencies: &[NodeRef],
    c: &mut Control,
) -> Result<Vec<NodeRef>, ValidationFailure> {
    let mut result = vec![];
    for candidate in declarations.candidates() {
        tick(c)?;
        if candidate.source().kind != "local" {
            continue;
        }
        let pair = candidate.pair().ok_or("localの対応署名がない")?;
        let source = &inputs.law().declarations[pair.source()];
        let target = &inputs.law().declarations[pair.target()];
        let (
            Signature::Local {
                params: sp,
                guard: None,
                reads: sr,
            },
            Signature::Local {
                params: tp,
                guard: None,
                reads: tr,
            },
        ) = (&source.signature, &target.signature)
        else {
            return Err("guard付きlocal宣言移送は未実装".into());
        };
        if sp.len() != 1 || tp.len() != 1 || sr.len() != tr.len() {
            return Err("参照射影以外のlocal宣言移送は未実装".into());
        }
        let (Type::Ref(st), Type::Ref(tt)) = (&sp[0].ty, &tp[0].ty) else {
            return Err("非参照local引数の移送は未実装".into());
        };
        for (&s, &t) in sr.iter().zip(tr) {
            if !identity_read(inputs, s, &sp[0].name, c)?
                || !identity_read(inputs, t, &tp[0].name, c)?
            {
                return Err("参照射影以外のlocal read移送は未実装".into());
            }
        }
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
                    entity: entity.clone(),
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
            [&sp[0].ty, &tp[0].ty],
            &subjects,
            declarations.types(),
            dependencies,
        )?;
        let args = [
            Type::Tuple(vec![sp[0].ty.clone()]),
            Type::Tuple(vec![tp[0].ty.clone()]),
        ];
        let arguments = value_map(
            b,
            [&args[0], &args[1]],
            &subjects,
            declarations.types(),
            dependencies,
        )?;
        let mut clauses = vec![];
        let mut all = dependencies.to_vec();
        for (&s, &t) in sr.iter().zip(tr) {
            tick(c)?;
            let se = expression(b, inputs, s, sp, dependencies)?;
            let te = expression(b, inputs, t, tp, dependencies)?;
            // 両句は対応する引数の射影。全source参照の像を両経路で同じ実写像から得る。
            let commutes = b.proposition(
                "declaration_transport",
                vec![se, te, arguments, values],
                vec![],
                Decision::Established,
            )?;
            let p = &mut b.parts[commutes.0 - b.base];
            p.scope.assignments = true;
            let q = Quantifier {
                kind: crate::law::ast::QuantKind::Forall,
                name: sp[0].name.clone(),
                ty: sp[0].ty.clone(),
                domain: None,
                occurrence: sp[0].span,
                context: None,
            };
            p.scope.quantifiers.push(q.clone());
            if let Json::Obj(wire) = &mut p.wire {
                wire.insert("quantifiers".into(), Json::Arr(vec![q.wire()]));
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
        result.push(
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
    Ok(result)
}
