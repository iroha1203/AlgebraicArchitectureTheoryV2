//! 元の評価を保持し、少数の合法assignmentからwholeの相違証人を探す。
use super::*;
use crate::observed::call::{CompletionCase, CompletionOrigin};
pub(super) enum ProbeOutcome {
    Pair(Answer),
    Discover {
        roots: Vec<NodeRef>,
        carried: BTreeMap<Fact, Scalar>,
    },
    NoPair,
}
impl Evaluator<'_, '_> {
    pub(super) fn probe_completion_pair(
        &mut self,
        observed: &Answer,
        seed: NodeRef,
        support: &Support,
        scope: &Scope,
        carried: &BTreeMap<Fact, Scalar>,
    ) -> Result<ProbeOutcome, Failure> {
        let Some(&original_root) = observed.outputs.get("evaluation") else {
            return Ok(ProbeOutcome::NoPair);
        };
        if observed.status != Decision::Undetermined
            || !reasons_equal(&observed.reasons, &self.graph.get(original_root)?.reasons)
        {
            return Ok(ProbeOutcome::NoPair);
        }
        let Some(Payload::CompletionSeed {
            fields,
            sources,
            bindings,
            roots,
            ..
        }) = &self.graph.get(seed)?.payload
        else {
            unreachable!();
        };
        let (fields, sources, fixed, roots) = (
            fields.clone(),
            sources.clone(),
            bindings.clone(),
            roots.clone(),
        );
        let proposals = self
            .environment
            .completion_probe_assignments(self.graph, &fields, &roots, carried)?;
        self.completion_observe("completion_probe_proposals", proposals.len());
        if proposals.is_empty() {
            return Ok(ProbeOutcome::NoPair);
        }
        let (params, guard, body, role) = match &self.declaration.signature {
            Signature::View { params, body, .. } => (params.clone(), None, *body, None),
            Signature::Law {
                params,
                guard,
                body,
                role,
            } => (params.clone(), *guard, *body, Some(*role)),
            _ => unreachable!(),
        };
        let caller = self.graph.active;
        // case単体の値を公開回答へ昇格しない。探索中の停止はこの元Answerを保持する。
        self.finish_answer(observed)?;
        let previous = self.verified_observed.replace(observed.clone());
        let retained_reasons = self.reasons.clone();
        let result = (|| -> Result<ProbeOutcome, Failure> {
            let mut known: Vec<(NodeRef, Vec<NodeRef>, NodeRef)> = Vec::new();
            for (ordinal, proposal) in proposals.into_iter().enumerate() {
                self.completion_observe("completion_probe", ordinal);
                self.tick(Checkpoint::FiniteIteration)?;
                if !self
                    .environment
                    .completion_probe_assignment_valid(&fields, &proposal)?
                {
                    continue;
                }
                let values = if fields.len() == 1 {
                    vec![proposal.clone()]
                } else {
                    let Scalar::Tuple(values) = &proposal else {
                        unreachable!();
                    };
                    values.clone()
                };
                let member = self.value(
                    proposal,
                    Rule::Construction("domain"),
                    vec![seed],
                    support.clone(),
                    scope.clone(),
                )?;
                let mut references = Vec::new();
                for (value, source) in values.into_iter().zip(&sources) {
                    references.push(self.value(
                        value,
                        Rule::Construction("domain"),
                        vec![seed, member, *source],
                        support.clone(),
                        scope.clone(),
                    )?);
                }
                let index = self.graph.cases.len();
                self.graph.cases.push(CompletionCase {
                    caller,
                    seed,
                    origin: CompletionOrigin::Assignment,
                    member,
                    values: references.clone(),
                });
                self.completion_reset(crate::observed::call::Context {
                    case: Some(index),
                    ..caller
                });
                let evaluated = if self.is_family(&params) {
                    self.family_answer(&params, guard, body, role)
                } else {
                    self.answer(&params, guard, body, role)
                };
                let mut discovered_roots = Vec::new();
                match &evaluated {
                    Ok(answer) => {
                        discovered_roots.extend(answer.outputs.get("evaluation").copied());
                        discovered_roots.extend(answer.claim);
                        discovered_roots.extend(
                            answer
                                .reasons
                                .iter()
                                .flat_map(|r| r.dependencies.iter().copied()),
                        );
                    }
                    Err(Failure::NotImplemented { .. }) => {
                        discovered_roots.extend(
                            self.reasons
                                .iter()
                                .flat_map(|r| r.dependencies.iter().copied()),
                        );
                        discovered_roots
                            .extend(self.completed.values().map(|value| value.evaluation));
                    }
                    _ => {}
                }
                // 失敗・停止もcaseの返却評価を外側の元回答へ流さない。
                self.completion_reset(caller);
                self.bindings = fixed.clone();
                let known_whole = evaluated
                    .as_ref()
                    .ok()
                    .and_then(|answer| answer.outputs.get("evaluation"))
                    .is_some_and(|r| {
                        matches!(
                            &self.graph.get(*r).ok().and_then(|n| n.payload.as_ref()),
                            Some(Payload::Evaluation { value: Some(_), .. })
                        )
                    });
                if !known_whole
                    && !matches!(&evaluated, Err(Failure::Stop(_) | Failure::Internal(_)))
                {
                    let (new_fields, _, _) = self
                        .environment
                        .completion_assignment_slots(self.graph, &discovered_roots)?;
                    if new_fields.iter().any(|field| !fields.contains(field)) {
                        self.completion_observe("completion_probe_discovered", new_fields.len());
                        let mut next = carried.clone();
                        for (field, reference) in fields.iter().zip(&references) {
                            next.insert(field.clone(), self.graph.scalar(*reference)?.clone());
                        }
                        return Ok(ProbeOutcome::Discover {
                            roots: discovered_roots,
                            carried: next,
                        });
                    }
                }
                let answer = match evaluated {
                    Ok(answer) => answer,
                    Err(Failure::NotImplemented { .. }) => continue,
                    Err(failure) => return Err(failure),
                };
                let Some(&evaluation) = answer.outputs.get("evaluation") else {
                    continue;
                };
                let Some(Payload::Evaluation {
                    value: Some(value), ..
                }) = &self.graph.get(evaluation)?.payload
                else {
                    continue;
                };
                let value = *value;
                self.completion_observe("completion_probe_whole", ordinal);
                self.tick(Checkpoint::FiniteIteration)?;
                for (prior, prior_values, prior_member) in &known {
                    let Some(Payload::Evaluation {
                        value: Some(prior_value),
                        ..
                    }) = &self.graph.get(*prior)?.payload
                    else {
                        unreachable!();
                    };
                    if value_equality::equal(
                        self.graph.scalar(*prior_value)?,
                        self.graph.scalar(value)?,
                        self.environment.indexes.inputs.law(),
                        self.control,
                    )? != Some(false)
                    {
                        continue;
                    }
                    let mut all_scope = scope.clone();
                    let mut all_support = support.clone();
                    let mut reasons = self.graph.get(seed)?.reasons.clone();
                    for reference in [*prior, evaluation] {
                        let node = self.graph.get(reference)?;
                        all_scope.merge(&node.scope);
                        all_support = Support::sum(vec![], [all_support, node.support.clone()]);
                        reasons.extend(node.reasons.iter().cloned());
                    }
                    crate::observed::environment::completion::canonical_reasons(
                        &mut reasons,
                        self.control,
                    )?;
                    self.completion_observe("completion_probe_pair", ordinal);
                    self.tick(Checkpoint::FiniteIteration)?;
                    let pair = self.push(Node {
                        ty: NodeType::Evidence,
                        payload: Some(Payload::CompletionPair {
                            fields: fields.clone(),
                            first: prior_values.clone(),
                            second: references.clone(),
                            first_result: *prior,
                            second_result: evaluation,
                        }),
                        rule: Rule::Construction("evidence"),
                        arguments: [seed, *prior_member, member, *prior, evaluation]
                            .into_iter()
                            .chain(prior_values.iter().copied())
                            .chain(references.iter().copied())
                            .collect(),
                        support: all_support,
                        evidence: vec![],
                        judgment: None,
                        scope: all_scope.clone(),
                        reasons: reasons.clone(),
                    })?;
                    let mut augmented = observed.clone();
                    augmented.evidence.push(pair);
                    augmented.scope.merge(&all_scope);
                    self.finish_answer(&augmented)?;
                    self.verified_observed = Some(augmented.clone());
                    self.completion_observe("completion_probe_committed", ordinal);
                    return Ok(ProbeOutcome::Pair(augmented));
                }
                known.push((evaluation, references, member));
            }
            Ok(ProbeOutcome::NoPair)
        })();
        self.completion_reset(caller);
        self.bindings = fixed;
        self.reasons = retained_reasons;
        if matches!(result, Ok(ProbeOutcome::NoPair)) {
            self.verified_observed = previous;
        }
        result
    }
}
