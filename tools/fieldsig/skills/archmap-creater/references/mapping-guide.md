# ArchMap Observation Guide

Use this guide when deciding what repository evidence should become an ArchMap observation.
ArchMap authoring is source-grounded observation, not architecture invention and not law-relative analysis.

## Source Cues To Observations

| Source cue | Preferred ArchMap reading | Primary field | Notes |
| --- | --- | --- | --- |
| File, module, namespace, class, service, package | Component existence atom observation | `atomObservations[]` | Preserve component identity. Forget implementation detail such as method count unless it is the measured subject. |
| Static import, explicit dependency, constructor injection, function call used as boundary evidence | Relation atom observation | `atomObservations[]` | Static evidence alone does not prove semantic dependency or runtime frequency. |
| Doc policy, layer rule, dependency rule, ownership rule | Policy or selected-universe source observation | `semanticObservations[]` or `observationGaps[]` | Record policy evidence as supplied context. Do not decide lawfulness in ArchMap. |
| Test, theorem, contract spec, golden fixture | Contract or behavior atom / semantic observation | `atomObservations[]`, `semanticObservations[]` | Scope to the selected observation. Do not generalize to all executions. |
| Two workflow paths with the same observed result | Semantic commutation cue | `semanticObservations[]` | Use an observational boundary when equality is test/spec relative. |
| Workflow paths with different observed results, missing compensation, impossible filler | Review concern cue over observed facts | `concernHints[]` | Keep primitive facts in atom observations. The concern hint is not an obstruction circuit and not incident causality. |
| Component with multiple responsibility regions or reasons to change | Responsibility molecule / SRP review cue | `moleculeObservations[]`, `concernHints[]` | Treat responsibility as a molecule over atoms, not a primitive atom. Treat SOLID as local contract-layer evidence, not a universal theorem. |
| Event stream to read model, replay projection, CQRS projection | Event-sourcing semantic observation | `semanticObservations[]` | Forget event-log completeness unless log evidence was supplied. |
| Saga branch, rollback path, compensation handler | Compensation observation or missing-compensation concern | `semanticObservations[]`, `concernHints[]` | Keep incident causality out of ArchMap. |
| Runtime trace, production edge, log-derived dependency | Runtime atom observation | `atomObservations[]` | If trace is unavailable, record an observation gap. |
| Framework convention such as route filename, DI registration, ORM relation | Framework boundary | `observationGaps[]` or low-confidence observation | Mark framework expansion as unmeasured unless an adapter artifact is supplied. |
| Dynamic plugin loading, reflection, generated code, private registry | Blind spot / unsupported construct | `observationGaps[]` | Put it in source universe blind spots and non-conclusions. |
| CLI workflow, observed tool workflow, user operation in repository evidence | SFT handoff hint over observed operation evidence | `semanticObservations[]`, `projectionInfo[]` | This may feed FieldSig after ArchSig analysis. It is not a ForecastCone result. |
| Domain event, state update, migration, lifecycle transition | Event / state transition observation | `atomObservations[]`, `semanticObservations[]`, `projectionInfo[]` | Preserve source refs and missing preconditions. |
| Test oracle, acceptance criterion, invariant check | Test oracle observation | `semanticObservations[]`, `projectionInfo[]` | Use as evidence for later operation support, not correctness proof. |

## AAT-Facing Vs SFT-Facing

AAT-facing observations preserve architecture structure:

- component existence
- relation evidence
- responsibility molecules
- semantic diagrams or commutation cues
- selected policy/source boundary readings

SFT-facing readings should be projection hints over observations:

- operation candidate
- workflow candidate
- event candidate
- state candidate
- state transition candidate
- test oracle candidate
- runtime observation candidate

Do not put `ForecastCone`, `ConsequenceEnvelope`, attractor, basin, quality ranking, forecast correctness, or incident causality in ArchMap. Those are downstream FieldSig report surfaces.

## Evidence Strength

Use conservative status and boundary text:

| Evidence situation | `observationStatus` | `evidenceBoundary` | `confidence` |
| --- | --- | --- | --- |
| Direct source file or test evidence was read and cited | `observed` | `sourceObserved` | `high` or `medium` |
| Policy/doc assumption is supplied but not independently measured | `assumed` | `assumedSource` | `medium` |
| Runtime/framework/dynamic evidence is named but not supplied | `unmeasured` | `unavailable` or `unmeasured` | `low` |
| Private evidence is referenced but cannot be inspected | `unmeasured` | `private` | `low` |
| Source contradicts another artifact or extraction result | `observed` or `unmeasured` depending on source | matching boundary | `medium` or `low` |
| LLM inference without specific source refs | avoid the observation | `unmeasured` if retained as a gap | `low` |

Never use measured absence for unavailable evidence. Use measured absence only when the selected measurement actually observed absence.

## Concern Hints

Use concern hints for source-grounded review cues:

- `missingCompensation`
- `missingRuntimeEvidence`
- `semanticRuntimeDisagreement`
- `policySourceDisagreement`
- `unexplainedStaticRelation`
- `responsibilityOverload`

Concern hints are not automatic failures, not automatic repair instructions, not law violations, and not obstruction circuits. ArchSig constructs law-relative obstruction readings after ArchMap is paired with LawPolicy.

## Authoring Heuristics

- Prefer fewer, well-evidenced observations over broad speculative coverage.
- Use one observation per source-grounded fact or semantic reading.
- Put global uncertainty in `sourceUniverse`, `provenance`, `observationGaps`, and top-level `nonConclusions`.
- Put observation-local uncertainty in `uncertainty`, `evidenceBoundary`, and child-level `nonConclusions`.
- If a source file supports both AAT and SFT readings, create observations first and put SFT reading hints in `projectionInfo[]`.
- If a theorem or Lean definition is referenced, record it as source evidence or a candidate reading; do not claim proof discharge from JSON validation.
- Keep `atomObservations[]`, `moleculeObservations[]`, `semanticObservations[]`, `observationGaps[]`, `projectionInfo[]`, and `concernHints[]` synchronized through refs.
