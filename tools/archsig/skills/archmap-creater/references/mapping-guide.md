# ArchMap Mapping Guide

Use this guide when deciding what repository evidence should become an ArchMap `mapItem`.
ArchMap authoring is evidence mapping, not architecture invention.

## Source Cues To Map Items

| Source cue | Preferred ArchMap reading | Typical `mappingKind` | Typical `targetRef.kind` | Notes |
| --- | --- | --- | --- | --- |
| File, module, namespace, class, service, package | Architecture object candidate | `object` | `air-component` | Preserve component identity. Forget implementation detail such as method count unless it is the measured subject. |
| Static import, explicit dependency, constructor injection, function call used as boundary evidence | Relation candidate | `relation` | `air-relation` | Static evidence alone does not prove semantic dependency or runtime frequency. |
| Doc policy, layer rule, dependency rule, ownership rule | Law or policy boundary | `policyBoundary` | `air-claim` | Use `claimClassification=assumed` unless independently measured by tooling. |
| Test, theorem, contract spec, golden fixture | Semantic evidence or contract observation | `semanticDiagram` or `semanticCommutationClaim` | `semantic-diagram` | Scope to the selected observation. Do not generalize to all executions. |
| Two workflow paths with the same observed result | Commutation candidate | `semanticCommutationClaim` | `semantic-diagram` | Use `equivalence=observational` when the equality is test/spec relative. |
| Workflow paths with different observed results, missing compensation, impossible filler | Obstruction or witness | `nonfillabilityWitness` | `nonfillability-witness` | Preserve the witness and avoid root-cause or incident-causality claims. |
| Component with multiple responsibility regions or reasons to change | Responsibility / SRP review cue | `semanticRole` | `air-claim` | Treat SOLID as local contract-layer evidence, not a universal theorem. |
| Event stream to read model, replay projection, CQRS projection | Event-sourcing semantic diagram | `semanticDiagram` | `semantic-diagram` | Forget event-log completeness unless the log evidence was supplied. |
| Saga branch, rollback path, compensation handler | Compensation or missing compensation cue | `nonfillabilityWitness` or `semanticDiagram` | `nonfillability-witness` or `semantic-diagram` | Keep incident causality out of ArchMap. |
| Runtime trace, production edge, log-derived dependency | Runtime observation candidate | `runtimeObservationCandidate` or `reviewBoundary` | `air-claim` | If trace is unavailable, mark unmeasured and list missing evidence. |
| Framework convention such as route filename, DI registration, ORM relation | Framework boundary | `reviewBoundary` | `air-claim` | Mark framework expansion as unmeasured unless an adapter artifact is supplied. |
| Dynamic plugin loading, reflection, generated code, private registry | Blind spot / unsupported construct | `reviewBoundary` | `air-claim` | Put it in `knownBlindSpots`, coverage, and non-conclusions. |
| PRD command flow, CLI workflow, user operation | SFT operation or workflow input candidate | `operationCandidate` or `workflowCandidate` | `sft-operation-candidate` or `sft-workflow-candidate` | This feeds ArchSig SFT projection; it is not a ForecastCone result. |
| Domain event, state update, migration, lifecycle transition | SFT event / state transition candidate | `eventCandidate`, `stateCandidate`, or `stateTransitionCandidate` | `sft-event-candidate`, `sft-state-candidate`, or `sft-transition-candidate` | Preserve source refs and missing preconditions. |
| Test oracle, acceptance criterion, invariant check | SFT test oracle candidate | `testOracleCandidate` | `sft-test-oracle-candidate` | Use as evidence for operation support, not correctness proof. |

## AAT-Facing Vs SFT-Facing

AAT-facing items preserve architecture structure:

- `object`
- `relation`
- `semanticRole`
- `semanticDiagram`
- `semanticCommutationClaim`
- `nonfillabilityWitness`
- `policyBoundary`
- flatness or exactness boundary cues expressed through `preserves[]`, `targetRef.subjectRef`, or coverage fields

SFT-facing items describe input candidates for deterministic ArchSig SFT artifacts:

- `operationCandidate`
- `workflowCandidate`
- `eventCandidate`
- `stateCandidate`
- `stateTransitionCandidate`
- `testOracleCandidate`
- `runtimeObservationCandidate`
- `proposalForceCandidate`

Do not put `ForecastCone`, `ConsequenceEnvelope`, attractor, basin, quality ranking, forecast correctness, or incident causality in ArchMap. Those are downstream ArchSig/SFT report surfaces.

## Evidence Strength

Use conservative classification:

| Evidence situation | `claimClassification` | `measurementBoundary` | `confidence` |
| --- | --- | --- | --- |
| Direct source file or test evidence was read and cited | `measured` | `measuredNonzero` | `high` or `medium` |
| Policy/doc assumption is supplied but not independently measured | `assumed` | `unmeasured` or `notComparable` | `medium` |
| Runtime/framework/dynamic evidence is named but not supplied | `unmeasured` | `unmeasured` or `unavailable` | `low` |
| Private evidence is referenced but cannot be inspected | `unmeasured` | `private` | `low` |
| Source contradicts another artifact or extraction result | `measured` or `unmeasured` depending on source | matching boundary | `medium` or `low` |
| LLM inference without specific source refs | avoid the item | `unmeasured` if retained as boundary | `low` |

Never use `measuredZero` for unavailable evidence. Use `measuredZero` only when the selected measurement actually observed absence.

## Conflict Categories

Use conflict categories as review cues:

- `missing-static-edge`: semantic relation is claimed but static extractor does not show the edge.
- `unexplained-static-edge`: static edge exists but no ArchMap item explains its semantic role.
- `policy-disagreement`: source evidence disagrees with supplied policy.
- `semantic-runtime-disagreement`: semantic and runtime evidence disagree, or one side is unavailable.

Conflicts are not automatic failures and not automatic repair instructions.

## Authoring Heuristics

- Prefer fewer, well-evidenced map items over broad speculative coverage.
- Use one `mapItem` per preserved structure, not one per paragraph.
- Put global uncertainty in `coverage`, `knownBlindSpots`, and top-level `nonConclusions`.
- Put item-local uncertainty in `missingEvidence` and item-level `nonConclusions`.
- If a source file supports both AAT and SFT readings, create separate items with shared `sourceRefs`.
- If the item is SFT-facing, make the downstream role clear in `preserves[]` and `targetRef.kind`.
- If a theorem or Lean definition is referenced, record it as a candidate or assumption; do not claim proof discharge from JSON validation.
