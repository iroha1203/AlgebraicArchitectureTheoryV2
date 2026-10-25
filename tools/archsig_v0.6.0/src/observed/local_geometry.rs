//! 固定状態の支持context、交わり、生成coverの有限局所系。
use super::*;
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct Support {
    pub carrier: Vec<Json>,
    pub positions: Vec<Fact>,
    pub visible: Vec<Fact>,
}
impl Support {
    pub(super) fn contains(&self, other: &Self) -> bool {
        other.carrier.iter().all(|v| self.carrier.contains(v))
            && other.positions.iter().all(|v| self.positions.contains(v))
            && other.visible.iter().all(|v| self.visible.contains(v))
    }
    fn intersect(&self, other: &Self) -> Self {
        Self {
            visible: self
                .visible
                .iter()
                .filter(|v| other.visible.contains(v))
                .cloned()
                .collect(),
            carrier: self
                .carrier
                .iter()
                .filter(|v| other.carrier.contains(v))
                .cloned()
                .collect(),
            positions: self
                .positions
                .iter()
                .filter(|v| other.positions.contains(v))
                .cloned()
                .collect(),
        }
    }
}
pub(super) struct Local {
    pub support: Support,
    pub instances: Vec<Json>,
    pub arguments: Vec<NodeRef>,
}
pub(super) struct Built {
    pub system: NodeRef,
    pub adequacy: NodeRef,
    pub point: NodeRef,
    pub semantic: NodeRef,
    pub equation: NodeRef,
    pub states: NodeRef,
    pub patch_count: usize,
}
struct State {
    point: NodeRef,
    semantic: NodeRef,
    equations: NodeRef,
    equation: NodeRef,
    states: NodeRef,
    identity: NodeRef,
    slots: Json,
    subjects: Vec<NodeRef>,
}
fn state(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    target: NodeRef,
    laws: &[NodeRef],
    positions: &[Fact],
    inhabited: bool,
    unit: NodeRef,
    c: &mut Control,
) -> Result<State, ValidationFailure> {
    let mut slot_values = vec![];
    let mut slot_subjects = vec![];
    for position in positions {
        c.checkpoint(super::super::control::Checkpoint::Localize)?;
        let subject = env.subject(&position.snapshot, &position.subject)?;
        let reference = change_result::value(
            b,
            &Scalar::Subject {
                snapshot: position.snapshot.clone(),
                subject: position.subject.clone(),
                entity: subject.ty.clone(),
            },
        )?;
        slot_subjects.push(reference);
        slot_values.push(Json::obj([
            ("subject", reference.wire()),
            (
                "field",
                Json::str(position.field.as_ref().ok_or("固定位置にfieldがない")?),
            ),
        ]));
    }
    let slots = Json::Arr(slot_values);

    let point = domain(b, &Type::Unit, &[unit])?;
    let elements = if inhabited { vec![unit] } else { vec![] };
    let states = domain(b, &Type::Unit, &elements)?;
    let action = state_map(b, point, point, &[(unit, unit)])?;
    let space = b.push(
        NodeType::Construction(T::StateSpace),
        "state_space",
        Json::obj([
            ("base", target.wire()),
            ("slots", Json::Arr(vec![])),
            ("state_type", Type::Unit.wire()),
        ]),
        vec![target],
        None,
        None,
    )?;
    let candidates = b.push(
        NodeType::Construction(T::CandidateSpace),
        "candidate_space",
        Json::obj([
            ("kind", Json::str("identity")),
            ("base", target.wire()),
            ("bindings", Json::Arr(vec![])),
            ("parameters", point.wire()),
            ("states", space.wire()),
            ("action", action.wire()),
            ("instances", Json::Arr(vec![])),
            ("guards", Json::Arr(vec![])),
            ("requirements", refs(laws)),
        ]),
        [target, point, space, action]
            .into_iter()
            .chain(laws.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let representation = Json::obj([("kind", Json::str("finite")), ("values", refs(&elements))]);
    let semantic = b.push(
        NodeType::Construction(T::SolutionSet),
        "solution_set",
        Json::obj([
            ("domain", candidates.wire()),
            ("requirements", refs(laws)),
            ("representation", representation.clone()),
        ]),
        [candidates, states]
            .into_iter()
            .chain(laws.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let equations = b.push(
        NodeType::Construction(T::EquationSpace),
        "equation_space",
        Json::obj([
            ("base", target.wire()),
            ("variables", Json::Arr(vec![])),
            ("fixed", slots.clone()),
            ("parameters", point.wire()),
            ("requirements", refs(laws)),
        ]),
        [target, point]
            .into_iter()
            .chain(laws.iter().copied())
            .chain(slot_subjects.iter().copied())
            .collect(),
        None,
        None,
    )?;
    let equation = b.push(
        NodeType::Construction(T::EquationSolutionSet),
        "equation_solutions",
        Json::obj([
            ("domain", equations.wire()),
            ("representation", representation),
        ]),
        vec![equations, states],
        None,
        None,
    )?;

    let pairs = elements.iter().map(|r| (*r, *r)).collect::<Vec<_>>();
    let identity = state_map(b, states, states, &pairs)?;
    Ok(State {
        point,
        semantic,
        equations,
        equation,
        states,
        identity,
        slots,
        subjects: slot_subjects,
    })
}
#[allow(clippy::too_many_arguments)]
pub(super) fn build(
    env: &Environment<'_>,
    b: &mut Builder<'_>,
    target: NodeRef,
    laws: &[NodeRef],
    truth: &[bool],
    patches: &[Support],
    law_supports: &[Support],
    global: Support,
    readings: &[Json],
    read_supports: &[Support],
    reading_refs: &[NodeRef],
    locals: &[Local],
    local_scope: &Scope,
    c: &mut Control,
) -> Result<Built, ValidationFailure> {
    let mut supports = vec![global];
    let mut patch_indices = vec![];
    for patch in patches {
        let i = if let Some(i) = supports.iter().position(|v| v == patch) {
            i
        } else {
            supports.push(patch.clone());
            supports.len() - 1
        };
        if !patch_indices.contains(&i) {
            patch_indices.push(i);
        }
    }
    let unit = change_result::value(b, &Scalar::Unit)?;
    let mut contexts = vec![];
    let mut states = vec![];
    let mut inhabited = vec![];
    let mut context_index = 0;
    while context_index < supports.len() {
        let support = &supports[context_index];
        c.checkpoint(super::super::control::Checkpoint::Localize)?;
        let selected = law_supports
            .iter()
            .enumerate()
            .filter(|(_, p)| support.contains(p))
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        let context_laws = selected.iter().map(|i| laws[*i]).collect::<Vec<_>>();
        let holds = selected.iter().all(|i| truth[*i]);
        let state = state(
            env,
            b,
            target,
            &context_laws,
            &support.positions,
            holds,
            unit,
            c,
        )?;
        let visible = readings
            .iter()
            .zip(read_supports)
            .enumerate()
            .filter(|(_, (_, s))| support.contains(s))
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        let selected_locals = locals
            .iter()
            .filter(|local| support.contains(&local.support))
            .collect::<Vec<_>>();
        let dependencies = visible
            .iter()
            .flat_map(|i| reading_refs[2 * i..2 * i + 2].iter().copied())
            .chain(
                selected_locals
                    .iter()
                    .flat_map(|local| local.arguments.iter().copied()),
            )
            .collect::<Vec<_>>();
        let local_instances = selected_locals
            .iter()
            .flat_map(|local| local.instances.iter().cloned())
            .collect::<Vec<_>>();
        let context = b.push(
            NodeType::Construction(T::Context),
            "context",
            Json::obj([
                ("base", target.wire()),
                ("locals", Json::Arr(local_instances)),
                ("carrier", Json::Arr(support.carrier.clone())),
                ("dependencies", state.slots.clone()),
                (
                    "readings",
                    Json::Arr(visible.iter().map(|i| readings[*i].clone()).collect()),
                ),
                ("law_coordinates", refs(&context_laws)),
            ]),
            std::iter::once(target)
                .chain(context_laws)
                .chain(dependencies)
                .chain(state.subjects.iter().copied())
                .collect(),
            None,
            None,
        )?;
        b.parts[context.0 - b.base].scope.merge(local_scope);
        contexts.push(context);
        states.push(state);
        inhabited.push(holds);
        // 完成したcontextを先に保持し、引戻し閉包を一つずつ拡張する。
        for j in 0..context_index {
            c.checkpoint(super::super::control::Checkpoint::Localize)?;
            let intersection = supports[context_index].intersect(&supports[j]);
            if !supports.contains(&intersection) {
                supports.push(intersection);
            }
        }
        context_index += 1;
    }
    let mut arrows = BTreeMap::new();
    let mut maps = vec![];
    let mut restrictions = vec![];
    let mut restriction_refs = vec![];
    for (v, small) in supports.iter().enumerate() {
        for (w, big) in supports.iter().enumerate() {
            c.checkpoint(super::super::control::Checkpoint::Localize)?;
            if !big.contains(small) {
                continue;
            }
            // Law座標を支持で閉じたため、成立する大contextから空の小contextへの写像は生じない。
            if inhabited[w] && !inhabited[v] {
                return Err("局所状態の制限が定義できない".into());
            }
            let pairs = if inhabited[w] {
                vec![(unit, unit)]
            } else {
                vec![]
            };
            let restriction = if v == w {
                states[v].identity
            } else {
                state_map(b, states[w].states, states[v].states, &pairs)?
            };
            let images = small
                .carrier
                .iter()
                .map(|value| {
                    big.carrier
                        .iter()
                        .position(|x| x == value)
                        .map(|i| Json::Nat(i as u64))
                        .ok_or_else(|| ValidationFailure::from("contextの包含像がない"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let arrow = b.push(
                NodeType::Construction(T::ContextMap),
                "context_map",
                Json::obj([
                    ("source", contexts[v].wire()),
                    ("target", contexts[w].wire()),
                    ("images", Json::Arr(images)),
                    ("restrictions", refs(&[restriction])),
                ]),
                vec![contexts[v], contexts[w], restriction],
                None,
                None,
            )?;
            arrows.insert((v, w), arrow);
            maps.push(arrow);
            restriction_refs.push(restriction);
            for side in ["equation", "semantic"] {
                restrictions.push(Json::obj([
                    ("side", Json::str(side)),
                    ("arrow", arrow.wire()),
                    ("map", restriction.wire()),
                ]));
            }
        }
    }
    let mut overlaps = vec![];
    for &left in &patch_indices {
        for &right in &patch_indices {
            c.checkpoint(super::super::control::Checkpoint::Localize)?;
            let intersection = supports[left].intersect(&supports[right]);
            let i = supports
                .iter()
                .position(|s| *s == intersection)
                .ok_or("交わりcontextがない")?;
            let lp = arrows[&(i, left)];
            let rp = arrows[&(i, right)];
            overlaps.push(b.push(
                NodeType::Construction(T::Overlap),
                "context",
                Json::obj([
                    ("left", contexts[left].wire()),
                    ("right", contexts[right].wire()),
                    ("context", contexts[i].wire()),
                    ("left_projection", lp.wire()),
                    ("right_projection", rp.wire()),
                ]),
                vec![contexts[left], contexts[right], contexts[i], lp, rp],
                None,
                None,
            )?);
        }
    }
    let adequate = supports[0].carrier.iter().all(|x| {
        patch_indices
            .iter()
            .any(|i| supports[*i].carrier.contains(x))
    }) && supports[0].positions.iter().all(|x| {
        patch_indices
            .iter()
            .any(|i| supports[*i].positions.contains(x))
    }) && law_supports
        .iter()
        .all(|law| patches.iter().any(|patch| patch.contains(law)));
    if !adequate {
        return Err("暗黙支持coverが全体を被覆しない".into());
    }
    let adequacy = b.proposition(
        "cover_adequate",
        contexts.clone(),
        vec![],
        Decision::Established,
    )?;
    let patch_refs = patch_indices
        .iter()
        .map(|i| contexts[*i])
        .collect::<Vec<_>>();
    let cover = b.push(
        NodeType::Construction(T::Cover),
        "cover",
        Json::obj([
            ("base", contexts[0].wire()),
            ("patches", refs(&patch_refs)),
            ("overlaps", refs(&overlaps)),
            ("adequacy", adequacy.wire()),
        ]),
        std::iter::once(contexts[0])
            .chain(patch_refs)
            .chain(overlaps)
            .chain([adequacy])
            .collect(),
        None,
        None,
    )?;
    // 唯一の生成coverを各contextに引き戻すと、真の部分contextでは恒等射を含む。
    // 従って生成位相は各最大篩と、全体上のpatchで生成した篩(およびその上位篩)である。
    // 全体以外はすべてpatch以下なので、上位篩は生成篩自身と最大篩だけ。
    let mut sieves = vec![];
    let mut matching_checks = vec![];
    for w in 0..supports.len() {
        let sources = (0..supports.len())
            .filter(|v| arrows.contains_key(&(*v, w)))
            .collect::<Vec<_>>();
        matching_checks.push((w, sources.clone()));
        sieves.push(Json::obj([
            ("base", contexts[w].wire()),
            (
                "arrows",
                refs(&sources.iter().map(|v| arrows[&(*v, w)]).collect::<Vec<_>>()),
            ),
        ]));
    }
    if !patch_indices.contains(&0) {
        let sources = (0..supports.len())
            .filter(|v| {
                patch_indices
                    .iter()
                    .any(|p| supports[*p].contains(&supports[*v]))
            })
            .collect::<Vec<_>>();
        matching_checks.push((0, sources.clone()));
        sieves.push(Json::obj([
            ("base", contexts[0].wire()),
            (
                "arrows",
                refs(&sources.iter().map(|v| arrows[&(*v, 0)]).collect::<Vec<_>>()),
            ),
        ]));
    }
    let topology = b.push(
        NodeType::Construction(T::Topology),
        "topology",
        Json::obj([
            ("contexts", refs(&contexts)),
            ("maps", refs(&maps)),
            ("generators", refs(&[cover])),
            ("covering_sieves", Json::Arr(sieves)),
        ]),
        contexts
            .iter()
            .chain(&maps)
            .copied()
            .chain([cover])
            .collect(),
        None,
        None,
    )?;
    // 固定状態では各fiberは空または一点。非空な局所状態の制限はすべてUnitを保つので、
    // matchingの有無と全域状態の有無を照合すれば、存在と一意性を別々に検査できる。
    let cover_holds = inhabited[0] == patch_indices.iter().all(|i| inhabited[*i]);
    let topology_holds = matching_checks
        .iter()
        .all(|(w, sources)| inhabited[*w] == sources.iter().all(|i| inhabited[*i]));
    let mut checks = vec![];
    for side in ["equation", "semantic"] {
        for (scope, object, holds) in [
            ("cover", cover, cover_holds),
            ("topology", topology, topology_holds),
        ] {
            let proposition = b.proposition(
                "sheaf_condition",
                std::iter::once(object)
                    .chain(restriction_refs.iter().copied())
                    .collect(),
                vec![],
                if holds {
                    Decision::Established
                } else {
                    Decision::Refuted
                },
            )?;
            checks.push((
                proposition,
                Json::obj([
                    ("scope", Json::str(scope)),
                    ("side", Json::str(side)),
                    ("proposition", proposition.wire()),
                ]),
            ));
        }
    }
    let mut fields = BTreeMap::from([
        ("base".into(), target.wire()),
        ("laws".into(), refs(laws)),
        ("contexts".into(), refs(&contexts)),
        ("maps".into(), refs(&maps)),
        ("cover".into(), cover.wire()),
        ("topology".into(), topology.wire()),
        (
            "semantic_states".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .map(|(context, s)| {
                        Json::obj([
                            ("context", context.wire()),
                            ("parameters", s.semantic.wire()),
                            ("state_image", s.states.wire()),
                            ("action", s.identity.wire()),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "equation_states".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .map(|(context, s)| {
                        Json::obj([
                            ("context", context.wire()),
                            ("space", s.equations.wire()),
                            ("solutions", s.equation.wire()),
                        ])
                    })
                    .collect(),
            ),
        ),
        ("restrictions".into(), Json::Arr(restrictions)),
        (
            "state_comparisons".into(),
            Json::Arr(
                contexts
                    .iter()
                    .zip(&states)
                    .map(|(context, s)| {
                        Json::obj([
                            ("context", context.wire()),
                            ("map", s.identity.wire()),
                            ("conditions", Json::Arr(vec![])),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "sheaf_checks".into(),
            Json::Arr(checks.iter().map(|(_, v)| v.clone()).collect()),
        ),
    ]);
    for name in [
        "coefficients",
        "coefficient_restrictions",
        "actions",
        "presentations",
        "polynomial_inclusions",
        "residual_restrictions",
        "conditions",
    ] {
        fields.insert(name.into(), Json::Arr(vec![]));
    }
    let system = b.push(
        NodeType::Construction(T::LocalSystem),
        "local_system",
        Json::Obj(fields),
        std::iter::once(target)
            .chain(contexts)
            .chain(maps)
            .chain([cover, topology])
            .chain(laws.iter().copied())
            .chain(
                states
                    .iter()
                    .flat_map(|s| [s.semantic, s.states, s.equations, s.equation, s.identity]),
            )
            .chain(checks.iter().map(|(r, _)| *r))
            .chain(restriction_refs)
            .collect(),
        None,
        None,
    )?;
    Ok(Built {
        system,
        adequacy,
        point: states[0].point,
        semantic: states[0].semantic,
        equation: states[0].equation,
        states: states[0].states,
        patch_count: patch_indices.len(),
    })
}
