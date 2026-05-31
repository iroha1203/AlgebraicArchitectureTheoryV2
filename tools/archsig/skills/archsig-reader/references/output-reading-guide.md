# ArchSig Output Reading Guide

Use this reference when deciding what to read first in an
`archsig-analysis-packet-v0` or `archsig-analysis-summary.json`.

## Analysis Summary Reading Order

When `analysis-summary` is available, read it before raw packet details:

1. `verdict`: the measured conclusion for the supplied ArchMap + LawPolicy.
2. `qualityMeasurement`: counts for nonzero axes, hotspots, recurrent pressure,
   unfilled architectural holes, nonzero holonomy loops, and coverage gaps.
3. `dominantFindings`: compact nonzero axes, hotspots, recurrent pressure,
   architectural holes, nonzero holonomy, workflow risks, and bridge pressure.
4. `actionQueue`: the full compact review queue derived from hotspots, holes,
   nonzero holonomy, nonzero axes, workflow pressure, and bridge pressure.
   Queue entries use `detailRefs`; they do not carry nested support/source/
   witness evidence arrays.
5. `axisSummary`, `workflowRiskSummary`, `architecturalHoleSummary`,
   `bridgeSummary`, and `coverageGapSummary`: compact counts and examples for
   the major surfaces.
6. `detailIndex`: packet sections and `packet:<json-pointer>` refs for reading
   full evidence in `archsig-analysis-packet.json`.
7. `measurementBasis`: input refs, profile refs, validation results, coverage
   gaps, and measured boundaries.
8. `metadata.nonConclusions`: claim-boundary metadata. Keep it available, but
   do not lead the user-facing diagnosis with it.

The report posture is: "for this input model, these conclusions were measured."
Do not turn unmeasured claims into caveats in the main diagnosis.
Use packet detail only after the compact summary identifies which queue item or
finding needs evidence inspection.

When ArchSig output is being read as part of complete ArchMap authoring, the
posture is slightly different: keep the measured conclusion first, then turn
coverage blockers into authoring repair work. `blockedByCoverageGap` should
mean "go find or explicitly bound the missing evidence" unless the evidence is
truly unavailable, private, or out of scope.

## Priority Fields

| Field | Why it matters |
| --- | --- |
| `archMapRef`, `selectedLawPolicyRef` | Identifies the observed source state and selected law universe. |
| `axisSummary` / `detailIndex` | States selected/nonzero axis counts and points to `flatnessReading` / `signatureAxes[]` detail when needed. |
| `workflowRiskSummary` / `actionQueue` | Prioritizes molecule-local review pressure such as permission, LLM mediation, state/effect reconciliation, and domain cohesion, with refs into `workflowRiskReadings[]`. |
| `dominantFindings` / `detailRefs` | Gives compact hotspots, recurrent pressure, architectural holes, nonzero holonomy, workflow risks, and bridge pressure before raw packet inspection. |
| `architectureSpectrumReport` | Packet detail surface for ACTS evidence: top hotspots, bounded mode data, witness clusters, recurrent obstruction entries, coverage gaps, measured boundary, and review focus. |
| `architectureHomotopyReport` | Packet detail surface for Homotopy / Holonomy / Stokes evidence: filled loops, unfilled loops, nonzero holonomy loops, local curvature cells, bounded aggregate readings, coverage gaps, and review focus. |
| `transferBridgeReadings[]` | Packet detail surface for repair transfer axes, molecule overlap paths, bridge edge source refs, review focus, and boundary preparation. |
| `splitReadinessReadings[]` | Shows which molecules are blocked by bridge edges or need boundary preparation before feature extraction or refactoring. |
| `structuralReadingReviewSurface` | Summarizes AAT structural review surfaces across representation, curvature, projection, state algebra, Galois, and split readiness. |
| `currentStateEvolutionBoundary` | Keeps ArchSig current-state analysis separate from FieldSig evolution / PR / diff / forecast analysis. |
| `llmInterpretationPacket` | Gives a compact review index. Use it as a guide, not independent evidence. |

## LawPolicy Boundary

Do not treat LawPolicy as a harmless default. It defines the selected law universe, witness rules, signature axes, exactness assumptions, and coverage requirements. Changing LawPolicy changes what ArchSig can read as obstruction, nonzero axis, flatness pressure, repair candidate, or non-conclusion.

Use a project-specific LawPolicy for real analysis. If only the bundled `default_law_policy.json` is available, use it only as an explicit generic baseline / smoke test and label the result that way. A bundled baseline run can show that the toolchain and packet-reading workflow work; it should not be presented as the repository's intended architecture law analysis.

For ACTS readings, confirm that the selected LawPolicy contains
`spectrumMeasurementProfile`. If it is absent, report that
`ArchitectureSpectrumReport` may be absent and do not infer spectrum hotspots
from generic spectral fields.

For Homotopy / Holonomy / Stokes readings, confirm that the selected LawPolicy
contains `homotopyMeasurementProfile`. If it is absent, report that
`ArchitectureHomotopyReport` may be absent and do not infer loop, filler,
holonomy, or local-curvature readings from generic obstruction fields.

For both reports, read `measurementStatus` and `readingBoundary` before
interpreting values. `measured` means the selected evidence needed by that
record is present. `proxy` means the record is a bounded computational proxy,
such as `rho(T^kappa)` over measured support rows. `unmeasured` and
`blockedByCoverageGap` must stay in the review queue as missing evidence, not
as zero curvature, zero holonomy, or path equality.

## Interpreting Status

- `pass` in validation means packet shape and guardrails passed; it is not architecture lawfulness.
- `actionable` means the bounded reading has enough evidence for review action.
- `needsReview` means human/source review is required before conclusions or implementation decisions.
- `blockedByCoverageGap` means missing evidence must be carried as unknown remainder.
- `nonConclusion` means ArchSig explicitly refuses a conclusion on that surface.

For complete-first authoring, split `blockedByCoverageGap` into:

- repairable blocker: source, docs, tests, runtime trace, policy, or explicit
  user evidence can still be read and added to the ArchMap
- residual blocker: evidence is private, unavailable, or out of scope and must
  remain as a targeted gap with non-conclusions

Do not hand a repairable blocker to the user as if it were an expected manual
workflow step.

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
| `architectureSpectrumReport.topHotspots[]` | hotspot witness refs, support refs, coverage gaps | review current-state hotspot before repair planning |
| `curvatureSupportReadings[].support[]` | lhs/rhs observation refs, local curvature ref, distance inputs, source refs, measurement status | confirm what was actually measured before reading curvature as zero or nonzero |
| `curvatureTransferReadings[].transferOperator` | row/column support refs, sparse entries, transfer edge refs, spectral radius kind | inspect `rho(T^kappa)` as a bounded finite-operator proxy, not empirical amplification |
| `architectureSpectrumReport.recurrentObstructions[]` | transfer edge refs, recurrence kind, cycle weight, witness support | inspect recurrence as bounded current-state diagnostic |
| `architectureSpectrumReport.coverageGaps[]` | missing docs, traces, tests, or source refs | collect evidence before reading absent support as zero |
| `pathPairCandidates[]` and `operationSquareCandidates[]` | operation sequences, endpoint object refs, generator candidate refs | verify the candidate path basis before comparing continuations |
| `pathContinuationTraces[]` | operation sequence, endpoint refs, continuation step refs | trace how `Cont_x(p)` and `Cont_x(q)` were built |
| `axisWiseMonodromyDefects[]` | p/q continuation refs, distance input refs, positive witness boundary, weight | read `mu_x=d_x(Cont_x(p), Cont_x(q))` only when distance inputs are present |
| `designPrincipleReadings[]` | principle-specific witness rule, witness status, evidence refs, source refs, obstruction refs | read principles as invariant / law / obstruction / operation preservation telemetry, not global lint status |
| `architectureHomotopyReport.nonzeroHolonomyLoops[]` | loop refs, compared continuations, selected axes, source refs | inspect path differences as bounded current-state review queues |
| `architectureHomotopyReport.unfilledLoops[]` | missing filler evidence, coverage gaps, next check refs | add or confirm contract/test/runtime/policy filler evidence before concluding |
| `architectureHomotopyReport.topLocalCurvatureCells[]` | filled loop refs and local curvature cell candidates | review local curvature only inside measured fillings, not unfilled holes |
| `architectureHomotopyReport.aggregateReadings[]` | selected measured square refs, positive contributors, zero-weight defects | use as prioritization counts, not quality score or global homology |

## Source Comparison Checklist

- Resolve packet refs to ArchMap source refs before reading code.
- Confirm whether the source still matches the ArchMap observation.
- Check tests only when tests were part of the ArchMap scope or when the user asks for improvement validation.
- Preserve private/unavailable/runtime gaps; do not infer from missing files.
- When a reading depends on route coverage, runtime traces, provider logs, or model relationships, report the missing evidence explicitly.
- Tie every improvement proposal to a packet field and source ref.
- For homotopy reports, resolve loop refs through `loopCandidates[]`,
  `pathPairCandidates[]`, `architecturalHoleReadings[]`,
  `homotopyHolonomyReadings[]`, and `stokesStyleReadings[]` before proposing
  code or policy changes.
- For complete ArchMap authoring, feed those resolved refs back into
  `archmap-creater`: add measured filler evidence when source/test/runtime/
  policy evidence exists, or add a targeted non-fillability gap when it does
  not.

## Metadata / Boundaries

Keep these fields available after the verdict and action queue:

- selected LawPolicy
- coverage gaps that block exactness
- whether source comparison was performed
- which source refs were confirmed, stale, missing, or not inspected
- non-conclusions relevant to the user's decision

For `ArchitectureHomotopyReport`, preserve these as metadata:

- candidate paths and loops are review cues, not path truth
- `mu_x` and AMI are selected-axis measurements over recorded continuation
  evidence, not global homotopy or homology computations
- unfilled loops are architectural holes, not automatic violations
- missing filler evidence is not measured zero
- Stokes-style local curvature requires measured filler evidence; holes carry
  non-fillability witness refs instead
- nonzero holonomy is not future incident prediction or repair-safety evidence
- ArchitectureHomotopyReport is not a single architecture quality score
