# ArchMap Prompt Pack

Use this prompt pack with `archsig archmap-generate` or as the instruction source for an external LLM agent.

## Task

Create an `archmap-observation-map-v0` JSON artifact from the supplied bounded source inventory and inspected source evidence.

## Required Boundary

- Treat ArchMap as LLM-authored observation evidence.
- Do not treat ArchMap as architecture ground truth.
- Do not infer facts from sources that were not read or supplied.
- Do not reconstruct private, unavailable, generated, framework-expanded, or runtime evidence.
- Preserve blind spots as `observationGaps[]` or source-universe boundary notes.
- Do not decide architecture lawfulness.
- Do not emit obstruction circuits, zero-curvature claims, Lean proof claims, forecast claims, quality scores, or causal diagnoses.

## Atom Reading

Write `atomObservations[]` only for primitive architectural facts grounded in selected source refs.

Common primitive fact families:

- `existence`: component, module, service, class, package, process, table, queue
- `relation`: import, call, read, write, publish, subscribe, ownership, implementation
- `capability`: command, query, handler, port, interface, storage access
- `state`: field, table column, cache entry, configuration value, event projection
- `effect`: database write, message send, email, payment, event publish, remote call
- `authority`: permission, owner, visibility, policy scope, access path
- `trust`: trust boundary, delegated authority, integration trust
- `contractSpecification`: precondition, postcondition, return shape, invariant, error behavior
- `semantic`: source-supported domain meaning or identity meaning
- `runtimeInteraction`: trace/log-supported runtime edge, message, call, or effect

Do not use `atomObservations[]` for responsibility, law violation, obstruction, forecast, quality, incident causality, or global correctness.

## Observation Surfaces

- Use `moleculeObservations[]` for composed roles such as responsibility over atom refs.
- Use `semanticObservations[]` for source-supported meaning, behavior, workflow, contract reading, or commutation cue.
- Use `observationGaps[]` for unavailable, private, unmeasured, or out-of-scope evidence.
- Use `projectionInfo[]` for downstream AAT or SFT handoff hints only.
- Use `concernHints[]` for review cues only. A concern hint is not an obstruction circuit.
- Use `nonConclusions[]` to state what the artifact does not prove.

## Output Requirements

- Output valid JSON only when asked for the artifact.
- Use `schemaVersion: "archmap-observation-map-v0"`.
- Keep IDs stable and readable.
- Ensure observed claims cite `sourceRefs[]`.
- Ensure source refs resolve to `sourceUniverse.includedRefs[]` when they support observations.
- Keep confidence qualitative: `high`, `medium`, or `low`. Do not read it as probability.
- Prefer a small accurate map over broad speculative coverage.
