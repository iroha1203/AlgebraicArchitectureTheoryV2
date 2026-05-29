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
An atom has no coarse/fine scale. If a candidate summarizes a subsystem, responsibility, workflow, policy reading, or concern, split the primitive facts into atom observations and move the larger reading to `moleculeObservations[]`, `semanticObservations[]`, `observationGaps[]`, or `concernHints[]`.

ASTs, symbol indexes, import graphs, route lists, and framework conventions may guide source navigation. They are not sufficient evidence by themselves. Cite the selected source refs that were actually read and that directly support the architectural fact.

If you use static navigation aids, list them in provenance, uncertainty, or local notes as discovery aids only. Do not cite an AST, route list, or import graph as the sole support for an observed atom unless that artifact itself is the selected source being observed.

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

Before emitting an observed atom:

- Confirm the fact belongs to exactly one atomFamily.
- Confirm the fact is primitive enough that it cannot be usefully split into smaller architectural observations.
- Confirm `sourceRefs[].artifactId` resolves to `sourceUniverse.includedRefs[]`.
- Preserve local uncertainty in `uncertainty[]` and `nonConclusions[]`.
- Move unavailable runtime, private, generated, or unexpanded framework evidence to `observationGaps[]`.

## Observation Surfaces

- Use `moleculeObservations[]` for composed roles such as responsibility over atom refs.
- Use `semanticObservations[]` for source-supported meaning, behavior, workflow, contract reading, or commutation cue.
- Use `observationGaps[]` for unavailable, private, unmeasured, or out-of-scope evidence.
- Use `projectionInfo[]` for downstream AAT or SFT handoff hints only.
- Use `concernHints[]` for review cues only. A concern hint is not an obstruction circuit.
- Use `nonConclusions[]` to state what the artifact does not prove.

Workflow-first reading is allowed for discovery, but the output must not contain coarse workflow atoms. Split primitive source facts into `atomObservations[]`, compose responsibilities in `moleculeObservations[]`, and put workflow or behavior readings in `semanticObservations[]`.

## Parallel Agent Mode

For large codebases, multiple agents may survey separate surfaces such as authority/authentication, state/model, effects/jobs, provider/trust, domain/contracts, runtime/framework, and docs/governance. A surface agent must output candidates, not a final ArchMap. The final integrator decides which candidates are accepted.

Surface-agent candidate packets should include:

- reviewed refs and excluded refs
- navigation aids used, explicitly marked as non-evidence
- candidate primitive atoms with source refs actually read
- candidate molecule or semantic readings only when they reference candidate atoms
- observation gaps for private, unavailable, generated, framework-expanded, or runtime-only evidence
- concern hints as review cues only
- uncertainty and non-conclusions

The integrator must deduplicate by predicate, subject/object refs, and source refs; resolve accepted source refs into `sourceUniverse.includedRefs[]`; lower confidence or create gaps when agents disagree; and keep coarse responsibility, workflow, policy, and concern readings out of `atomObservations[]`.

## Output Requirements

- Output valid JSON only when asked for the artifact.
- Use `schemaVersion: "archmap-observation-map-v0"`.
- Keep IDs stable and readable.
- Ensure observed claims cite `sourceRefs[]`.
- Ensure source refs resolve to `sourceUniverse.includedRefs[]` when they support observations.
- Keep confidence qualitative: `high`, `medium`, or `low`. Do not read it as probability.
- Prefer a small accurate map over broad speculative coverage.
