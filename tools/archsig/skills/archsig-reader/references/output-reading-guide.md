# ArchSig Output Reading Guide

Use this reference when deciding what to read first in an `archsig-analysis-packet-v0`.

## Priority Fields

| Field | Why it matters |
| --- | --- |
| `archMapRef`, `selectedLawPolicyRef` | Identifies the observed source state and selected law universe. |
| `flatnessReading` | States whether selected signature axes are zero/nonzero and which coverage gaps block exactness. |
| `signatureAxes[]` | Gives axis-local support refs, missing evidence, exactness assumptions, and excluded readings. |
| `workflowRiskReadings[]` | Prioritizes molecule-local review pressure such as permission, LLM mediation, state/effect reconciliation, and domain cohesion. |
| `spectralAnalysisReadings[]` | Shows dominant rows/columns and coupling surfaces across workflows, molecules, obstructions, and operation deltas. |
| `transferBridgeReadings[]` | Connects repair transfer axes, molecule overlap paths, bridge edge source refs, review focus, and boundary preparation. |
| `splitReadinessReadings[]` | Shows which molecules are blocked by bridge edges or need boundary preparation before feature extraction or refactoring. |
| `structuralReadingReviewSurface` | Summarizes AAT structural review surfaces across representation, curvature, projection, state algebra, Galois, and split readiness. |
| `currentStateEvolutionBoundary` | Keeps ArchSig current-state analysis separate from FieldSig evolution / PR / diff / forecast analysis. |
| `llmInterpretationPacket` | Gives a compact review index. Use it as a guide, not independent evidence. |

## LawPolicy Boundary

Do not treat LawPolicy as a harmless default. It defines the selected law universe, witness rules, signature axes, exactness assumptions, and coverage requirements. Changing LawPolicy changes what ArchSig can read as obstruction, nonzero axis, flatness pressure, repair candidate, or non-conclusion.

Use a project-specific LawPolicy for real analysis. If only the bundled `default_law_policy.json` is available, use it only as an explicit generic baseline / smoke test and label the result that way. A bundled baseline run can show that the toolchain and packet-reading workflow work; it should not be presented as the repository's intended architecture law analysis.

## Interpreting Status

- `pass` in validation means packet shape and guardrails passed; it is not architecture lawfulness.
- `actionable` means the bounded reading has enough evidence for review action.
- `needsReview` means human/source review is required before conclusions or implementation decisions.
- `blockedByCoverageGap` means missing evidence must be carried as unknown remainder.
- `nonConclusion` means ArchSig explicitly refuses a conclusion on that surface.

## Packet Variant Fallback

Some valid packets do not emit every high-level review surface. If `workflowRiskReadings[]`, `spectralAnalysisReadings[]`, `transferBridgeReadings[]`, or `splitReadinessReadings[]` are empty, do not invent those readings.

Use this fallback order:

1. `flatnessReading`: status, nonzero axes, zero axes, coverage gaps
2. `signatureAxes[]`: values, source refs, missing evidence, coverage status
3. `obstructionCircuits[]`: law refs, witness rules, atom refs, molecule refs, concern refs, missing evidence
4. `repairOperationCandidates[]`: operation kind, preconditions, support refs, transferred obstructions, excluded readings
5. `operationDeltas[]`: decreased axes, transferred obstructions, side-effect axes
6. `boundedJudgements[]` and `llmInterpretationPacket.recommendedHumanReviewFocus`

For source comparison in this variant, build the review queue from nonzero axes, obstruction source refs, repair candidate support refs, and coverage gaps.

## Common Improvement Mapping

| ArchSig pressure | First evidence check | Likely improvement family |
| --- | --- | --- |
| `permissionCoverage` | route-by-route dependency and tenant/workspace scope | policy boundary / permission audit |
| `authorityTrustBoundary` | auth/session/token/provider trust handoffs | authority boundary / trust boundary hardening |
| `stateEffectReconciliation` | commit ownership, retries, idempotency, status finalization | transaction boundary / recovery contract |
| `llmOutputMediation` | prompt context, provider output filtering, persistence gates | anti-corruption layer / output validation |
| `sourceBackedDomainCohesion` | domain identity, source relations, contracts | explicit interface / model relationship audit |
| high molecule overlap | shared atom refs and source refs | split only after boundary preparation |
| nonzero operation transfer | operation delta touches non-target axes | avoid local repair that transfers complexity |

## Source Comparison Checklist

- Resolve packet refs to ArchMap source refs before reading code.
- Confirm whether the source still matches the ArchMap observation.
- Check tests only when tests were part of the ArchMap scope or when the user asks for improvement validation.
- Preserve private/unavailable/runtime gaps; do not infer from missing files.
- When a reading depends on route coverage, runtime traces, provider logs, or model relationships, report the missing evidence explicitly.
- Tie every improvement proposal to a packet field and source ref.

## Report Boundaries

Always include:

- selected LawPolicy
- coverage gaps that block exactness
- whether source comparison was performed
- which source refs were confirmed, stale, missing, or not inspected
- non-conclusions relevant to the user's decision
