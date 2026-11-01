//! 有限changeを持つ支持局所系の公開構成と両側のmatching診断。
use super::*;
#[allow(clippy::too_many_arguments)]
pub(super) fn compute(
    env: &Environment<'_>,
    g: &Graph,
    request: &Request,
    target: NodeRef,
    original: &ConstructionValue,
    base: usize,
    witness: Arc<ArchitectureWitness>,
    c: &Control,
) -> Result<Source, ValidationFailure> {
    let assignments = match &original.data {
        D::Change(d) => d.overrides(g)?,
        D::Quotient(d) => d.overrides(g)?,
        _ => vec![],
    }
    .into_iter()
    .map(|(f, _, v)| (f, v))
    .collect::<Vec<_>>();
    let mut fixed = Environment::try_primitive_valuation(env.indexes.inputs, &assignments, c)?
        .ok_or("有限局所系の元Architectureが不適合")?;
    fixed.select_local_object(&witness, c)?;
    let (model, missing) = finite_model::analyze(env, &fixed, g, &witness, request, c)?;
    let Some(model) = model else {
        let using = request
            .arguments
            .iter()
            .find_map(|a| match (&*a.name, &a.value) {
                ("using", Selector::Declaration { name }) => Some(name),
                _ => None,
            })
            .ok_or("欠測した局所change名がない")?;
        let declaration = &env.indexes.inputs.law().declarations()[using];
        let Signature::Change { params, body, .. } = &declaration.signature else {
            return Err("局所changeの署名がない".into());
        };
        let mut b = Builder {
            g,
            base,
            parts: vec![],
        };
        let expression = change_result::source_expression(
            &mut b,
            env,
            *body,
            &[],
            &params
                .iter()
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect::<Vec<_>>(),
        )?;
        b.parts[expression.0 - base].arguments.push(target);
        b.parts[expression.0 - base]
            .scope
            .merge(&g.get(target)?.scope);
        let scope = b.parts[expression.0 - base].scope.clone();
        let reason = Reason {
            kind: ReasonKind::Missing,
            request: request.id.clone(),
            dependencies: vec![expression],
            missing,
            location: Some(Location::Law {
                span: declaration.span,
            }),
        };
        b.parts[expression.0 - base].reasons.push(reason.clone());
        return Ok(Source {
            base,
            parts: b.parts,
            scope_domains: vec![],
            request: request.clone(),
            witness,
            system: None,
            answer: Answer {
                id: request.id.clone(),
                status: Decision::Undetermined,
                outputs: BTreeMap::new(),
                claim: None,
                evidence: vec![],
                scope,
                reasons: vec![reason],
            },
        });
    };
    if model.rational_equations {
        return super::rational_finite::compute_model(
            env, g, request, target, base, witness, fixed, model, c,
        );
    }
    compute_model(env, g, request, target, base, witness, fixed, model, c)
}
fn split_diagram(
    d: Option<integer::Diagram>,
) -> (Option<integer::Diagram>, Option<rational::Diagram>) {
    (d, None)
}
include!("../local_finite_build.rs");
#[allow(clippy::too_many_arguments)]
pub(super) fn diagnose(
    g: &Graph,
    request: &Request,
    target: NodeRef,
    base: usize,
    witness: Arc<ArchitectureWitness>,
    finite: &geometry::Finite,
    laws: &[NodeRef],
    degree: u64,
    c: &Control,
) -> Result<Source, ValidationFailure> {
    let side = request
        .arguments
        .iter()
        .find_map(|a| match (&*a.name, &a.value) {
            ("side", Selector::Enum { value }) => Some(value.as_str()),
            _ => None,
        })
        .ok_or("有限診断のsideがない")?;
    let selected = if side == "equation" {
        finite.equation.as_ref().ok_or("有限の方程式状態がない")?
    } else {
        &finite.semantic
    };
    let mut b = Builder {
        g,
        base,
        parts: vec![],
    };
    let mut matching_values = vec![];
    for value in &selected.matching {
        c.checkpoint(crate::control::Checkpoint::Localize)?;
        matching_values.push((value, change_result::value(&mut b, value)?));
    }
    let matching = domain(
        &mut b,
        &selected.matching_type,
        &matching_values.iter().map(|(_, r)| *r).collect::<Vec<_>>(),
    )?;
    let pairs = selected
        .restriction
        .iter()
        .map(|(r, v)| {
            matching_values
                .iter()
                .find(|(w, _)| *w == v)
                .map(|(_, s)| (*r, *s))
                .ok_or_else(|| ValidationFailure::from("matching像がない"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let restriction = state_map(&mut b, selected.domain, matching, &pairs)?;
    let mut fibers = vec![];
    let mut fiber_refs = vec![];
    for (value, r) in matching_values {
        c.checkpoint(crate::control::Checkpoint::Localize)?;
        let states = selected
            .restriction
            .iter()
            .filter(|(_, v)| v == value)
            .map(|(r, _)| *r)
            .collect::<Vec<_>>();
        let parameters = selected
            .parameters
            .iter()
            .filter(|(s, _)| states.contains(s))
            .flat_map(|(_, p)| p.iter().copied())
            .collect::<Vec<_>>();
        let mut fields = BTreeMap::from([
            ("domain".into(), selected.solution_domain.wire()),
            (
                "representation".into(),
                Json::obj([("kind", Json::str("finite")), ("values", refs(&parameters))]),
            ),
        ]);
        if side == "semantic" {
            fields.insert("requirements".into(), refs(laws));
        }
        let fiber = b.push(
            NodeType::Construction(if side == "semantic" {
                T::SolutionSet
            } else {
                T::EquationSolutionSet
            }),
            if side == "semantic" {
                "solution_set"
            } else {
                "equation_solutions"
            },
            Json::Obj(fields),
            [selected.solution_domain, restriction, r]
                .into_iter()
                .chain(parameters)
                .chain(laws.iter().copied())
                .collect(),
            None,
            None,
        )?;
        fiber_refs.push(fiber);
        fibers.push(Json::obj([
            ("matching", r.wire()),
            ("preimage", fiber.wire()),
        ]));
    }
    let diagnostic = b.push(
        NodeType::Construction(T::Diagnostic),
        "diagnostic",
        Json::obj([
            ("kind", Json::str("finite_matching")),
            ("side", Json::str(side)),
            ("system", target.wire()),
            ("degree", Json::Nat(degree)),
            ("matching", matching.wire()),
            ("global", selected.global.wire()),
            ("restriction", restriction.wire()),
            ("fibers", Json::Arr(fibers)),
            ("conditions", Json::Arr(vec![])),
        ]),
        std::iter::once(target)
            .chain([matching, selected.global, restriction])
            .chain(fiber_refs)
            .collect(),
        None,
        None,
    )?;
    let status = if degree == 0 || !selected.values.is_empty() {
        Decision::Established
    } else {
        Decision::Refuted
    };
    let mut outputs = BTreeMap::from([("diagnostic".into(), diagnostic)]);
    let mut evidence = vec![];
    let claim = if degree == 1 {
        if selected.values.is_empty() {
            evidence.push(
                b.push(
                    NodeType::Evidence,
                    "evidence",
                    Json::obj([
                        ("kind", Json::str("finite_exhaustion")),
                        (
                            "data",
                            Json::obj([
                                ("domain", selected.all.wire()),
                                ("checked", Json::Nat(selected.checked as u64)),
                                ("instances", refs(laws)),
                            ]),
                        ),
                    ]),
                    std::iter::once(selected.all)
                        .chain(laws.iter().copied())
                        .collect(),
                    None,
                    None,
                )?,
            );
        }
        let proposition = b.proposition(
            "inhabited",
            vec![selected.global],
            std::iter::once(diagnostic)
                .chain(evidence.iter().copied())
                .collect(),
            status,
        )?;
        b.parts[proposition.0 - base]
            .judgment
            .as_mut()
            .ok_or("診断の判断がない")?
            .evidence = evidence.clone();
        outputs.insert("proposition".into(), proposition);
        Some(proposition)
    } else {
        None
    };
    let answer = Answer {
        id: request.id.clone(),
        status,
        outputs,
        claim,
        evidence,
        reasons: vec![],
        scope: b.parts[diagnostic.0 - base].scope.clone(),
    };
    Ok(Source {
        base,
        parts: b.parts,
        scope_domains: vec![],
        answer,
        request: request.clone(),
        witness,
        system: None,
    })
}
