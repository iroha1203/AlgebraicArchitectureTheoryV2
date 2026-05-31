# ArchMap Observation Guide

Use this guide when deciding what repository evidence should become an ArchMap observation.
ArchMap authoring is source-grounded observation, not architecture invention and not law-relative analysis.

## Navigation Aid Boundary

Static analysis artifacts can speed up source selection, but they are not ArchMap observations.

| Artifact | Allowed reading | Not allowed |
| --- | --- | --- |
| AST or symbol index | Candidate source refs to inspect | Atom truth, semantic dependency, or complete coverage |
| Import graph | Candidate relation evidence to read in source | Runtime call frequency, architecture lawfulness, or dependency intent |
| Route list or class/function map | Candidate entrypoints and capabilities to inspect | Permission coverage, effect execution, or workflow correctness |
| Framework registry or convention output | Framework expansion to mark as a blind spot or inspect directly | Observed atoms without reading generated/expanded source |
| Search result set | Bounded survey queue | Source inventory completeness |

After a navigation aid identifies a candidate, read the cited source and record the directly supported primitive fact. If the source is unavailable or outside scope, use `observationGaps[]` or a low-confidence `concernHints[]` review cue.

## Complete-First Authoring Boundary

The user-facing ArchMap authoring workflow is complete-first. Do not ask the
user to first accept a thin static map and then manually grow it until ArchSig
becomes useful. Use partial notes only as internal scratch state while reading
the repository. The handoff artifact should already contain the evidence needed
for the requested ArchSig measurement, plus targeted gaps only for evidence
that is genuinely unavailable, private, or out of scope.

For large repositories, split the reading work across surfaces, then integrate
the result into one bounded ArchMap:

- authority / authentication
- state / model
- effects / jobs
- provider / trust
- domain / contracts
- runtime / framework
- docs / governance

The integrator must turn those surface packets into primitive atoms, molecules,
semantic observations, projection hints, concern hints, and targeted gaps. A
surface packet is not a user-facing reduced ArchMap.

## Source Cues To Observations

| Source cue | Preferred ArchMap reading | Primary field | Notes |
| --- | --- | --- | --- |
| File, module, namespace, class, service, package | Component existence atom observation | `atomObservations[]` | Preserve component identity. Forget implementation detail such as method count unless it is the measured subject. |
| Static import, explicit dependency, constructor injection, function call used as boundary evidence | Relation atom observation | `atomObservations[]` | Static evidence alone does not prove semantic dependency or runtime frequency. |
| Doc policy, layer rule, dependency rule, ownership rule | Policy or selected-universe source observation | `semanticObservations[]` or `observationGaps[]` | Record policy evidence as supplied context. Do not decide lawfulness in ArchMap. |
| Test, theorem, contract spec, golden fixture | Contract or behavior atom / semantic observation | `atomObservations[]`, `semanticObservations[]` | Scope to the selected observation. Do not generalize to all executions. |
| Two workflow paths with the same observed result | Semantic commutation cue | `semanticObservations[]` | Use an observational boundary when equality is test/spec relative. |
| Workflow paths with different observed results, missing compensation, impossible filler | Review concern cue over observed facts | `concernHints[]` | Keep primitive facts in atom observations. The concern hint is not an obstruction circuit and not incident causality. |
| Two operation sequences that should be compared by ArchSig Homotopy | First-class operation square evidence plus primitive operation atoms | `operationSquareEvidence[]`, `atomObservations[]`, `semanticObservations[]`, `projectionInfo[]`, `concernHints[]` | Record `pOperationSequence`, `qOperationSequence`, endpoint object refs, shared endpoint refs, generator candidates, and source refs. Without those refs ArchSig must emit a blocked candidate, not synthesize a continuation operation. |
| State transition relation with source/test/runtime evidence | Transition input for state/effect law evaluation | `operationSquareEvidence[]`, state/effect/runtime `atomObservations[]`, targeted `observationGaps[]` | Preserve from/event/to refs through endpoint/shared endpoint refs, operation sequences, invariant refs, and runtime or test refs. Missing traces/tests block the law axis; do not record measured zero. |
| Effect ordering, replay/idempotency, compensation, or authority requirement | Effect relation input for law evaluation | `operationSquareEvidence[]`, effect/relation/authority/runtime atoms, `concernHints[]`, targeted `observationGaps[]` | Keep ordering, replay/idempotency, compensation/finalization, and authority evidence separate so ArchSig can evaluate each axis instead of reading raw effect Atom presence. |
| Lhs/rhs observations for a selected law diagram | Primitive atoms plus semantic diagram cue | `atomObservations[]`, `semanticObservations[]`, `projectionInfo[]` | Preserve source refs for both sides so ArchSig can compute local curvature inputs. Missing side evidence remains a gap. |
| Contract, test, runtime trace, policy, or source implementation that fills a loop | Filler evidence cue over observed facts | `semanticObservations[]`, `projectionInfo[]` | Record the evidence source and boundary. If absent or private, create an observation gap instead of a measured filler. |
| Missing filler for one path rule or operation square | Targeted non-fillability witness | `observationGaps[]`, `concernHints[]` | Use the path-rule or square ref as `subjectRef` so unrelated loops are not blocked by a global gap. |
| Component with multiple responsibility regions or reasons to change | Responsibility molecule / SRP review cue | `moleculeObservations[]`, `concernHints[]` | Treat responsibility as a molecule over atoms, not a primitive atom. Treat SOLID as local contract-layer evidence, not a universal theorem. |
| Event stream to read model, replay projection, CQRS projection | Event-sourcing semantic observation | `semanticObservations[]` | Forget event-log completeness unless log evidence was supplied. |
| Saga branch, rollback path, compensation handler | Compensation observation or missing-compensation concern | `semanticObservations[]`, `concernHints[]` | Keep incident causality out of ArchMap. |
| Runtime trace, production edge, log-derived dependency | Runtime atom observation | `atomObservations[]` | If trace is unavailable, record an observation gap. |
| Framework convention such as route filename, DI registration, ORM relation | Framework convention boundary | `observationGaps[]` or low-confidence observation | Mark framework expansion as unmeasured unless the expanded evidence was supplied and inspected. |
| Dynamic plugin loading, reflection, generated code, private registry | Blind spot / unsupported construct | `observationGaps[]` | Put it in source universe blind spots and non-conclusions. |
| CLI workflow, observed tool workflow, user operation in repository evidence | SFT handoff hint over observed operation evidence | `semanticObservations[]`, `projectionInfo[]` | This may feed FieldSig after ArchSig analysis. It is not a ForecastCone result. |
| Domain event, state update, migration, lifecycle transition | Event / state transition observation | `atomObservations[]`, `semanticObservations[]`, `projectionInfo[]` | Preserve source refs and missing preconditions. |
| Test oracle, acceptance criterion, invariant check | Test oracle observation | `semanticObservations[]`, `projectionInfo[]` | Use as evidence for later operation support, not correctness proof. |

## Atom Family Extraction Guide

Use this section when deciding whether a source-backed reading belongs in `atomObservations[]`.
Each atom should record one primitive architectural fact. If the candidate combines multiple
facts, split it before writing the atom. If the candidate is still meaningful only as a workflow,
responsibility, policy interpretation, concern, or missing evidence note, use the corresponding
non-atom surface.

| atomFamily | Good atom cue | Not an atom cue | Usually move to |
| --- | --- | --- | --- |
| `existence` | A selected file defines `BillingService`, a route module, a queue name, a DB model, or a command object. | A directory name suggests there is a service, but no file or symbol was read. | `observationGaps[]` if the component is expected but uninspected. |
| `relation` | Source shows `OrderRoute` calling `OrderService.create`, a repository reading a table, or a task publishing to a queue. | Two files share a domain word, or an AST import exists without architectural boundary relevance. | `semanticObservations[]` for larger dependency readings; `observationGaps[]` for unexpanded framework edges. |
| `capability` | A service exposes a command/query, a handler processes a message, a processor supports a MIME type, or an adapter exposes storage access. | The candidate describes the whole end-to-end request workflow. | `moleculeObservations[]` for composed responsibility; `semanticObservations[]` for workflow meaning. |
| `state` | A model field, table column, cache key, enum status, job lifecycle marker, or persisted projection is defined or mutated. | A runtime value is guessed from domain knowledge or not present in selected evidence. | `observationGaps[]` for unavailable runtime state. |
| `effect` | Code commits DB writes, sends email, invokes a provider, publishes an event, mutates object storage, or enqueues work. | A dependency name implies possible I/O but no effecting code path was read. | `observationGaps[]` or `concernHints[]` if review should check effect ordering. |
| `authority` | Code checks workspace role, admin level, owner scope, RLS/session context, signed token, allowlist, or route dependency. | A schema has `user_id` but no access rule, ownership check, or authority boundary was inspected. | `semanticObservations[]` for authority architecture reading; `observationGaps[]` for route audit gaps. |
| `trust` | Source verifies webhook signatures, JWT/JWKS, provider identity, delegated credentials, or treats LLM/provider output as untrusted until validation. | Any external API call is treated as trust evidence without an observed trust decision. | `concernHints[]` for provider trust review cues; `observationGaps[]` for missing provider logs. |
| `contractSpecification` | DTO validation, precondition, postcondition, error mapping, idempotency key, retry rule, invariant, or bounded return shape is visible. | A passing test is generalized into universal correctness. | `semanticObservations[]` for behavior reading; `projectionInfo[]` for downstream handoff. |
| `semantic` | Source names a domain identity, ownership meaning, unit, status meaning, or bounded business term. | A long process narrative combines many atoms and roles. | `semanticObservations[]` for larger meaning/workflow readings. |
| `runtimeInteraction` | Supplied trace or log directly shows runtime call, edge, message, or effect. | Runtime behavior is expected from source code but no trace/log was supplied. | `observationGaps[]`; never measured-zero. |

Anti-patterns:

- Do not create a coarse atom such as "the authentication system owns all tenant access". Split observed role gates, token verification, session/RLS state, and admin bypass facts into atoms, then compose the larger reading as a molecule or semantic observation.
- Do not create an atom only because AST, import graph, or route discovery found a symbol. Use that index to navigate to source evidence, then record the architectural fact supported by the source.
- Do not use atom families such as `responsibility`, `workflow`, `policy`, `obstruction`, `lawViolation`, `forecast`, `qualityScore`, or `incidentCausality`.
- Do not turn an unavailable trace, private secret, unexpanded framework convention, or unreviewed generated file into an observed atom.

## Atom Vs Molecule Vs Semantic

Use this decision boundary after the atomFamily check.

| Question | If yes | If no |
| --- | --- | --- |
| Can the reading be stated as one primitive source-grounded architecture fact? | It may be an `atomObservations[]` entry. | Do not force it into an atom. |
| Does the reading name a role, responsibility, responsibility overload, or pattern over several atoms? | Use `moleculeObservations[]`. | Continue checking. |
| Does the reading describe workflow meaning, operation behavior, contract behavior, policy meaning, or commutation over atoms/molecules? | Use `semanticObservations[]`. | Continue checking. |
| Is the reading a review cue about risk, overload, missing compensation, missing runtime evidence, or disagreement? | Use `concernHints[]`. | Continue checking. |
| Is the required evidence unavailable, private, unmeasured, generated, or out of scope? | Use `observationGaps[]`. | Read more source or discard the candidate. |

Examples:

- `route.users calls UserService.create` is a relation atom.
- `route.users + service.user + create-user contract form user request orchestration` is a responsibility molecule.
- `the route/service/contract group describes create-user behavior` is a semantic observation.
- `the create-user workflow may lack compensation evidence` is a concern hint.
- `runtime DB trace for create-user was not supplied` is an observation gap.

Do not use `semantic` atom as a dumping ground for broad workflow readings. A `semantic` atom is only for primitive source-supported meaning, such as an identity meaning, unit meaning, ownership meaning, or status meaning.

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

## Source Reference And Boundary Requirements

For every `atomObservations[]` entry:

- `sourceRefs[]` must name the source artifacts that were actually read.
- For `observationStatus: "observed"`, each supporting `sourceRefs[].artifactId` should resolve to `sourceUniverse.includedRefs[]`.
- `evidenceBoundary` should say how the evidence was observed, usually `sourceObserved`, `assumedSource`, `unmeasured`, `unavailable`, `private`, or `outOfScope`.
- `confidence` is qualitative review priority, not probability. Use `high` only for direct, local source evidence; use `medium` when the fact spans files or depends on supplied policy; use `low` when retained only as weak evidence.
- `uncertainty[]` should preserve local caveats, such as missing runtime confirmation, framework expansion, sampled coverage, or partial route audit.
- `nonConclusions[]` should prevent promotion to architecture truth, global correctness, lawfulness, or proof discharge.

Move the candidate to `observationGaps[]` when the relevant evidence exists only as a private credential, provider log, runtime trace, generated file, framework expansion, production database row, or unreviewed test suite.

## Spectrum And Homotopy Evidence Patterns

For ACTS / Spectrum readiness, record:

- local lhs/rhs observations as primitive atoms or semantic diagram cues
- witness-support refs for the selected axis
- distance input refs and source-backed transfer-edge cues
- coverage gaps for missing rows, not zero-valued rows

For Homotopy / Holonomy / Stokes readiness, record:

- path-pair candidates as source-backed semantic observations or projection hints
- endpoint object refs through atom / molecule support
- operation sequence and generator-candidate cues when source supports them
- continuation evidence from source, tests, runtime traces, policy, or explicit user evidence
- filler evidence from contracts, tests, runtime traces, source implementation, policy docs, or explicit user evidence
- non-fillability witnesses as targeted `observationGaps[]`

Adding an atom is not enough to make a loop Stokes-ready. ArchSig can read
local curvature only when the ArchMap gives a measured filler boundary and the
selected LawPolicy can compare nonzero holonomy. If filler evidence is missing,
preserve it as a targeted gap so the feedback loop can repair exactly that
blocker.

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
