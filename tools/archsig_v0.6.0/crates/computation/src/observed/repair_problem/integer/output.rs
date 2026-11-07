//! 明示的に要求された整数全解・元割当・適用後対象の型付き表示。
use super::*;
#[derive(Debug)]
pub(in crate::observed::repair_problem) struct PublicModel {
    equations: NodeRef,
    certificate: NodeRef,
    visible_module: NodeRef,
    hidden_module: NodeRef,
    image_embedding: Option<NodeRef>,
}
impl PublicModel {
    pub(super) fn inputs(&self) -> Vec<NodeRef> {
        let mut refs = vec![
            self.equations,
            self.certificate,
            self.visible_module,
            self.hidden_module,
        ];
        refs.extend(self.image_embedding);
        refs.sort_by_key(|r| r.0);
        refs.dedup();
        refs
    }
}
pub(super) fn known_public(
    g: &Graph,
    shared: &Arc<Shared>,
    c: &Control,
) -> Result<Option<Arc<PublicModel>>, ValidationFailure> {
    for node in &g.nodes {
        tick(c)?;
        let Some(Payload::Construction(v)) = &node.payload else {
            continue;
        };
        let D::SharedRepair(d) = &v.data else {
            continue;
        };
        if d.index + 1 != d.source.parts.len() {
            continue;
        }
        let Some(state) = d.source.integer() else {
            continue;
        };
        if Arc::ptr_eq(&state.shared, shared)
            && let Some(model) = &state.public_model
        {
            return Ok(Some(model.clone()));
        }
    }
    Ok(None)
}
pub(super) fn publish_model(
    b: &mut Builder<'_>,
    shared: &Shared,
    c: &Control,
) -> Result<Arc<PublicModel>, ValidationFailure> {
    use crate::observed::change_result::linear_result as display;
    let problem = shared.problem.ok_or(internal!("整数問題がない"))?;
    let mut premises = shared.requirements.clone();
    premises.push(problem);
    let (equations, certificate) = display::system(
        b,
        &shared.compiled.linear,
        shared.ring,
        shared.parameter_module,
        &premises,
        c,
    )?;
    let (visible_module, hidden_module, image_embedding) = if let Some(projection) =
        &shared.projection
    {
        let d = shared.compiled.linear.kernel.first().map_or(0, Vec::len);
        let directions = display::module(b, shared.ring, d, "kernel", vec![equations])?;
        let shared_state = display::module(
            b,
            shared.ring,
            projection.shared_rows.len(),
            "free",
            vec![problem],
        )?;
        let image_map = display::map(b, directions, shared_state, projection.coefficients(), d, c)?;
        let part = &mut b.parts[image_map.0 - b.base];
        part.arguments.extend([shared.action, problem, certificate]);
        part.arguments.sort_by_key(|r| r.0);
        part.arguments.dedup();
        let visible = display::module(
            b,
            shared.ring,
            projection.visible(),
            "image",
            vec![image_map],
        )?;
        let hidden = display::module(
            b,
            shared.ring,
            projection.hidden(),
            "kernel",
            vec![image_map],
        )?;
        let embedding = display::map(
            b,
            visible,
            shared_state,
            &projection.action,
            projection.visible(),
            c,
        )?;
        let part = &mut b.parts[embedding.0 - b.base];
        part.arguments.extend([image_map, shared.action, problem]);
        part.arguments.sort_by_key(|r| r.0);
        part.arguments.dedup();
        (visible, hidden, Some(embedding))
    } else {
        let empty = display::module(b, shared.ring, 0, "free", vec![problem])?;
        (empty, empty, None)
    };
    Ok(Arc::new(PublicModel {
        equations,
        certificate,
        visible_module,
        hidden_module,
        image_embedding,
    }))
}
pub(super) fn render_solutions(
    b: &mut Builder<'_>,
    shared: &Shared,
    public: &PublicModel,
    math: &RangeMath,
    range: NodeRef,
    c: &Control,
) -> Result<NodeRef, ValidationFailure> {
    use crate::observed::change_result::linear_result as display;
    let mut dependencies = vec![
        shared.domain,
        shared.problem.ok_or(internal!("整数問題がない"))?,
        range,
        public.certificate,
    ];
    dependencies.extend(&shared.requirements);
    let representation = match math {
        RangeMath::Empty => Json::obj([
            ("kind", Json::str("empty")),
            ("certificate", public.certificate.wire()),
        ]),
        RangeMath::Constrained {
            coefficients,
            rhs,
            fiber,
        } => {
            let mut premises = vec![public.certificate, range];
            premises.extend(public.image_embedding);
            let (equations, certificate) = display::smith(
                b,
                shared.ring,
                public.visible_module,
                coefficients.matrix(),
                rhs,
                fiber,
                &premises,
                c,
            )?;
            dependencies.extend([equations, certificate]);
            if fiber.particular.is_none() {
                Json::obj([
                    ("kind", Json::str("empty")),
                    ("certificate", certificate.wire()),
                ])
            } else {
                let projection = shared
                    .projection
                    .as_ref()
                    .ok_or(internal!("整数共有像がない"))?;
                let original = shared
                    .compiled
                    .linear
                    .particular
                    .as_ref()
                    .ok_or(internal!("元整数fiberの原点がない"))?;
                let point = projection
                    .candidate(
                        original,
                        &shared.compiled.linear.kernel,
                        fiber,
                        &0u32.into(),
                        c,
                    )?
                    .ok_or(internal!("整数原点の復元がない"))?;
                let particular = display::vector(b, shared.parameter_module, &point, c)?;
                let visible = display::module(
                    b,
                    shared.ring,
                    projection.visible() - fiber.decomposition.rank,
                    "kernel",
                    vec![equations],
                )?;
                let directions = display::module(
                    b,
                    shared.ring,
                    projection.free(fiber)?,
                    "direct_sum",
                    vec![visible, public.hidden_module],
                )?;
                let embedding = display::map_generated(
                    b,
                    directions,
                    shared.parameter_module,
                    projection.free(fiber)?,
                    c,
                    |j| projection.kernel_column(&shared.compiled.linear.kernel, fiber, j, c),
                )?;
                dependencies.extend([particular, directions, embedding]);
                Json::obj([
                    ("kind", Json::str("affine")),
                    ("particular", particular.wire()),
                    ("directions", directions.wire()),
                    ("embedding", embedding.wire()),
                ])
            }
        }
    };
    b.push(
        NodeType::Construction(T::SolutionSet),
        "solution_set",
        Json::obj([
            ("domain", shared.domain.wire()),
            ("requirements", refs(&shared.requirements)),
            ("representation", representation),
        ]),
        dependencies,
        None,
    )
}
pub(super) fn assignment_value(
    b: &mut Builder<'_>,
    s: &Shared,
    parameters: &[Z],
    solutions: NodeRef,
) -> Result<NodeRef, ValidationFailure> {
    let origin = Witness::Architecture(s.witness.clone());
    let Signature::Change { params, .. } =
        &origin.inputs().law().declarations()[&s.compiled.change].signature
    else {
        unreachable!()
    };
    let width = params.len() - 1;
    if parameters.len() != width * s.subjects.len() {
        return Err(internal!("整数元Assignmentの幅が違う").into());
    }
    let mut entries = vec![];
    let mut arguments = vec![s.domain, solutions];
    for (i, subject) in s.subjects.iter().enumerate() {
        let values = parameters[i * width..(i + 1) * width]
            .iter()
            .map(|z| change_result::value(b, &Scalar::Z(z.clone())))
            .collect::<Result<Vec<_>, _>>()?;
        arguments.push(*subject);
        arguments.extend(&values);
        entries.push(Json::obj([
            ("subject", subject.wire()),
            ("parameters", refs(&values)),
        ]));
    }
    b.push(
        NodeType::Construction(T::Assignment),
        "assignment",
        Json::obj([("domain", s.domain.wire()), ("entries", Json::Arr(entries))]),
        arguments,
        None,
    )
}
pub(super) fn apply_object(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    s: &Shared,
    selected: NodeRef,
    solutions: NodeRef,
    claim: NodeRef,
    candidate: &change_evaluation::Candidate,
) -> Result<(NodeRef, Vec<NodeRef>), ValidationFailure> {
    let mut checks = vec![b.proposition(
        "solution_member",
        vec![solutions, selected],
        vec![claim],
        Decision::Established,
    )?];
    for law in &s.requirements {
        checks.push(b.proposition(
            "law_holds",
            vec![*law],
            vec![selected, claim],
            Decision::Established,
        )?);
    }
    let Some(Payload::Construction(original)) = &b.g.get(s.base)?.payload else {
        return Err(internal!("整数選択の基準Architectureがない").into());
    };
    let mut wire = original.wire();
    let Json::Obj(fields) = &mut wire else {
        return Err(internal!("基準Architectureがrecordでない").into());
    };
    let Some(Json::Arr(previous)) = fields.get_mut("overrides") else {
        return Err(internal!("基準Architectureのoverrideがない").into());
    };
    let mut arguments = original.arguments();
    let original_count = arguments.len();
    arguments.push(s.base);
    arguments.extend(&checks);
    for (fact, value) in &candidate.update.values {
        tick(&env.control)?;
        let actual = env.indexes.subject(&fact.snapshot, &fact.subject)?;
        let scalar = Scalar::Subject {
            snapshot: fact.snapshot.clone(),
            subject: fact.subject.clone(),
            entity: actual.ty.to_string(),
        };
        let subject = change_result::value(b, &scalar)?;
        let value = change_result::value(b, value)?;
        arguments.extend([subject, value]);
        previous.retain(|row| {
            let Some(row) = super::fields(row) else {
                return true;
            };
            let Some(slot) = row.get("slot").and_then(super::fields) else {
                return true;
            };
            if slot.get("field") != fact.field.as_ref().map(Json::str).as_ref() {
                return true;
            }
            !arguments[..original_count].iter().any(|r| {
                Some(&r.wire()) == slot.get("subject") && b.g.scalar(*r).ok() == Some(&scalar)
            })
        });
        previous.push(Json::obj([
            (
                "slot",
                Json::obj([
                    ("subject", subject.wire()),
                    (
                        "field",
                        Json::str(
                            fact.field
                                .as_deref()
                                .ok_or(internal!("整数更新fieldがない"))?,
                        ),
                    ),
                ]),
            ),
            ("value", value.wire()),
        ]));
    }
    let object = b.push(
        NodeType::Construction(T::Architecture),
        "architecture",
        wire,
        arguments,
        None,
    )?;
    b.parts[object.0 - b.base]
        .scope
        .merge(&candidate.update.scope);
    b.parts[object.0 - b.base]
        .support
        .make_owned()
        .extend(candidate.update.support.iter().cloned());
    b.parts[object.0 - b.base].support.make_owned().sort();
    b.parts[object.0 - b.base].support.make_owned().dedup();
    Ok((object, checks))
}
