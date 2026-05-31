# ArchMap Observation Schema Cheatsheet

Use this reference when filling an `archmap-observation-map-v0` document. Prefer the field names listed here.
When the ArchSig source repository is available, fixtures and schema code may be used as additional examples, but they are not required for this skill.

## Top-Level Fields

Required top-level shape:

```json
{
  "schemaVersion": "archmap-observation-map-v0",
  "mapId": "...",
  "architectureId": "...",
  "generatedAt": "2026-05-24T00:00:00Z",
  "generator": {},
  "promptRefs": [],
  "sourceInventoryRef": {},
  "generationBoundary": {},
  "sourceUniverse": {},
  "provenance": {},
  "atomObservations": [],
  "moleculeObservations": [],
  "semanticObservations": [],
  "observationGaps": [],
  "projectionInfo": [],
  "concernHints": [],
  "nonConclusions": []
}
```

## Source Universe

`sourceUniverse` must describe what was selected:

- `root`: repository or source root
- `includedRefs`: files, doc sections, tests, runtime traces, policy files, PR artifacts
- `excludedRefs`: intentionally excluded artifacts
- `unavailableRefs`: relevant artifacts not available
- `privateRefs`: relevant private artifacts not inspected
- `hashes`: optional content hashes for reproducibility
- `knownBlindSpots`: dynamic loading, framework convention expansion, runtime traces, private registries
- `selectionBoundary`: one sentence describing the bounded scope

Use `artifactId` values consistently. Source refs that support observed claims must point back to `sourceUniverse.includedRefs[]`. Use `unavailableRefs[]`, `privateRefs[]`, or `observationGaps[]` for boundary refs that were not inspected.

## Provenance

`provenance` records how the observation map was produced:

- `observer`
- `observationMethod`
- `sourceRoot`
- `observationBoundary`
- `reviewedRefs`
- `excludedReadings`
- `nonConclusions`

Use `excludedReadings` for things intentionally not read, such as lawfulness, obstruction circuits, zero curvature, private policy, runtime traces, or FieldSig forecast evidence.

## Atom Observations

An atom observation records a bounded observation of a primitive architectural fact. It does not certify the canonical Atom itself.
An atom observation should not have coarse/fine scale. If a candidate observation summarizes a workflow, role, subsystem, or policy reading, split it into primitive atoms and move the larger reading to `moleculeObservations[]` or `semanticObservations[]`.

Each `atomObservations[]` entry should include:

- `atomObservationId`
- `atomFamily`: for example `existence`, `relation`, `capability`, `state`, `effect`, `authority`, `trust`, `contractSpecification`, `semantic`, `runtimeInteraction`
- `predicate`
- `subjectRef`
- `objectRefs`
- `sourceRefs`
- `observationStatus`: usually `observed` or `unmeasured`
- `evidenceBoundary`: for example `sourceObserved`, `unmeasured`, `private`, `unavailable`, `outOfScope`
- `confidence`: review priority, not probability
- `uncertainty`
- `projectionRefs`
- `nonConclusions`

Do not use atom families such as `responsibility`, `obstruction`, `lawViolation`, `forecast`, `qualityScore`, or `incidentCausality`. Responsibility is a molecule. Obstruction is law-relative ArchSig analysis, not an ArchMap atom observation.

Atom family intent:

| atomFamily | Intended primitive fact | Required evidence cue |
| --- | --- | --- |
| `existence` | component, module, service, class, package, process, table, queue, route, command object | selected source defines or declares the subject |
| `relation` | import, call, read, write, publish, subscribe, owner edge, implementation edge, dependency edge | selected source shows the edge or explicit dependency |
| `capability` | command, query, handler, port, adapter, processor, serializer, storage access | selected source exposes or dispatches the capability |
| `state` | field, table column, cache entry, config value, status, lifecycle marker, projection | selected source defines, stores, or mutates the state |
| `effect` | DB write, message send, email, payment, event publish, remote call, object storage mutation, queue enqueue | selected source executes or schedules the effect |
| `authority` | permission, owner scope, role gate, visibility boundary, access path, policy scope, admin bypass | selected source checks or establishes authority |
| `trust` | trusted source, token verification, delegated authority, provider/webhook/LLM trust boundary | selected source accepts, verifies, delegates, or constrains trust |
| `contractSpecification` | precondition, postcondition, return shape, error behavior, invariant, idempotency, retry rule | selected source defines validation, behavior, or failure contract |
| `semantic` | bounded domain meaning, identity meaning, ownership meaning, unit meaning, status meaning | selected source names or constrains the meaning |
| `runtimeInteraction` | runtime call, edge, message, effect, or trace/log event | supplied runtime trace or log directly supports it |

Boundary rule:

- `observed` + `sourceObserved` requires inspected source refs.
- `assumed` + `assumedSource` is for supplied policy/doc assumptions, not independent measurement.
- `unmeasured`, `unavailable`, `private`, or `outOfScope` normally belongs in `observationGaps[]`, unless the schema field itself is recording a boundary note.
- Missing runtime evidence, private provider behavior, unexpanded framework convention, or generated code not read is not an observed atom.

## Molecule Observations

Each `moleculeObservations[]` entry should include:

- `moleculeObservationId`
- `moleculeFamily`
- `roleName`
- `atomObservationRefs`
- `sourceRefs`
- `observationStatus`
- `evidenceBoundary`
- `confidence`
- `nonConclusions`

Responsibility is a molecule over atom observations, not a primitive atom.
Use molecule observations for composed roles or patterns whose meaning depends on multiple atom observations. A molecule should reference the atom observations it composes; it should not replace those atoms.

Do not create an atom with `atomFamily: "responsibility"`, `atomFamily: "workflow"`, or `atomFamily: "policy"` to avoid building the molecule/semantic layer.

## Semantic Observations

Semantic observations are source-supported readings over atom and molecule observations. They are not proof of global semantic correctness.

Each `semanticObservations[]` entry should include:

- `semanticObservationId`
- `semanticFamily`: for example `operationMeaning`, `contractBehavior`, `workflow`, `semanticReading`, `commutationCue`
- `subjectRef`
- `predicate`
- `atomObservationRefs`
- `moleculeObservationRefs`
- `sourceRefs`
- `observationStatus`
- `evidenceBoundary`
- `nonConclusions`

Scope semantic observations to the selected source refs. Do not generalize a test, fixture, or doc section into global semantic correctness.
Use semantic observations for workflow meaning, operation meaning, behavior readings, contract readings, policy readings, and commutation cues. Do not use a coarse `semantic` atom when the reading combines multiple primitive facts.

If a semantic observation depends on primitive facts, list their `atomObservationRefs`. If it depends on a composed role, list the relevant `moleculeObservationRefs`.

## Observation Gaps

Each `observationGaps[]` entry should include:

- `gapId`
- `gapKind`
- `subjectRef`
- `evidenceStatus`: `unmeasured`, `unavailable`, `private`, or `outOfScope`
- `reason`
- `expectedAtomFamilies`
- `sourceRefs`
- `nonConclusions`

Do not use `measuredZero` for unavailable evidence. Use measured absence only when the selected measurement actually observed absence.

For Homotopy / Holonomy / Stokes readiness, prefer targeted gap ids and
subjects:

```json
{
  "gapId": "gap:path-rule:<name>:missing-filler",
  "gapKind": "MissingFillerEvidence",
  "subjectRef": "path-rule:<name>",
  "evidenceStatus": "unavailable",
  "reason": "selected contract / test / runtime / policy filler evidence was not supplied",
  "expectedAtomFamilies": ["contractSpecification", "runtimeInteraction"],
  "sourceRefs": [],
  "nonConclusions": ["missing filler evidence is not measured zero"]
}
```

Targeted gaps let ArchSig keep one loop as `blockedByCoverageGap` without
turning unrelated measured loops into holes.

## Projection Info

Each `projectionInfo[]` entry should include:

- `projectionId`
- `projectionFamily`: for example `object`, `relation`, `signatureAxis`, `operationCandidate`, `stateTransitionCandidate`
- `sourceObservationRef`
- `targetSurface`
- `reading`
- `projectionBoundary`
- `nonConclusions`

Projection info is a handoff hint. It is not ArchMap lawfulness, Lean proof, zero curvature, or FieldSig forecast output.

## Concern Hints

Each `concernHints[]` entry should include:

- `concernHintId`
- `concernFamily`
- `subjectRef`
- `atomObservationRefs`
- `moleculeObservationRefs`
- `semanticObservationRefs`
- `sourceRefs`
- `evidenceBoundary`
- `analysisBoundary`
- `nonConclusions`

Concern hints are review cues only. They are not obstruction circuits, not law violations, and not theorem evidence. ArchSig can construct law-relative obstruction readings only after combining ArchMap with LawPolicy.

## Coverage And Boundary Rules

Prefer these observation statuses:

- `observed`: source evidence was inspected and cited.
- `assumed`: supplied doc/policy assumption is used.
- `unmeasured`: relevant evidence was not measured.
- `unavailable`: relevant evidence is named but not available.
- `private`: relevant evidence is private and not inspected.
- `outOfScope`: relevant evidence is intentionally outside the selected universe.

Use confidence as qualitative review priority:

- `high`
- `medium`
- `low`

Do not read confidence as probability.

## Validation Checklist

Before validation:

- every observation id is unique
- source refs resolve to included refs or are clearly boundary refs
- observed claims cite source refs
- missing evidence is not represented as measured zero
- semantic observations have source support
- SFT-facing projection hints are not presented as forecast results
- every atom `projectionRefs[]` entry has a matching `projectionInfo[]` entry
- ACTS / Spectrum requests have lhs/rhs support, witness support, transfer
  support, or targeted missing-support gaps
- Homotopy / Stokes requests have path candidates, endpoint refs, continuation
  evidence, filler evidence, or targeted non-fillability gaps
- residual `blockedByCoverageGap` entries are genuine unavailable/private/out-of-scope evidence, not skipped source reading
- atom observations are source-grounded observations, not certified atoms
- responsibility is represented through molecule observations
- concern hints are not represented as obstruction circuits
- observation gaps are not represented as measured zero
- non-conclusions exist at child and top level

Validate with:

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input <archmap.json> \
  --out .archsig/archmap/validation.json
```

Then, for handoff:

```bash
${ARCHSIG_BIN:-archsig} law-policy --input <law-policy.json> --out .archsig/law-policy/validation.json
${ARCHSIG_BIN:-archsig} archsig-analysis \
  --archmap <archmap.json> \
  --law-policy <law-policy.json> \
  --out .archsig/analysis/packet.json \
  --validation-out .archsig/analysis/validation.json

${ARCHSIG_BIN:-archsig} analyze \
  --archmap <archmap.json> \
  --law-policy <law-policy.json> \
  --out-dir .archsig/analyze
```
