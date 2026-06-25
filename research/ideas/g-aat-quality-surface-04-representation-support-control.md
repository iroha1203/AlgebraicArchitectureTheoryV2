---
goal: G-aat-quality-surface-04
cycle: 37
candidate: Representation Support-Control Faithfulness Extraction
candidate_type: target-support
evidence_stage: proved-in-research
score_status: T4 confirmed as support-node
base_score: 42
evidence_multiplier: 2.0
penalty: 0
final_score: 84
target_progress: support-node
---

# Representation Support-Control Faithfulness Extraction

Cycle 37 narrows the Cycle 36 faithfulness obligation to a visible query /
support determinacy certificate.

The new Lean file
`Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryRepresentationSupportControl.lean`
proves that, if the current canonical shadow determines the concrete query
trace shadow, then every post-map on that query is invariant on realized
current-shadow query fibers.  Consequently the canonical current-shadow
reading is faithful for the query post-map, represented observations factor
through the current shadow, and separated post-fibers are ruled out.

It also introduces the canonical support-shadow observation and proves the
exact support-level criterion: the current shadow determines the finite support
trace shadow iff that support-shadow observation is faithful for the canonical
current-shadow reading.

## Lean Surface

- `supportSelfQuerySupportedBy`
- `supportTraceShadowPost`
- `supportTraceShadowFiniteTraceQueryObservation`
- `supportTraceShadowFiniteTraceQueryObservation_observe_eq`
- `supportTraceShadowFiniteTraceQueryObservationRepresentation`
- `postInvariantOnCurrentShadowFibers_of_currentShadowDeterminesTraceQuery`
- `currentShadowSemanticReading_faithfulToQueryPost_of_currentShadowDeterminesTraceQuery`
- `finiteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesTraceQuery`
- `representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesTraceQuery`
- `representedFiniteTraceQueryObservation_currentShadowFactor_of_currentShadowDeterminesTraceQuery`
- `no_queryPostFiberSeparation_of_representedFiniteTraceQueryObservation_currentShadowDeterminesTraceQuery`
- `representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesSupportTraceShadow`
- `currentShadowDeterminesSupportTraceShadow_iff_supportTraceShadowObservation_currentShadowSemanticReading_faithful`
- `nilSupport_representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful`
- `not_boolCompleteSupportTraceShadowObservation_currentShadowSemanticReading_faithful`

## Boundary

This is not a target theorem proof.  `CurrentShadowDeterminesTraceQuery` and
`CurrentShadowDeterminesSupportTraceShadow` remain visible theorem arguments /
concrete certificates.  They are not hidden in the representation package and
are not derived here from arbitrary semantic soundness or representation
adequacy.

Remaining blockers:

- non-circular extraction of query/support determinacy from semantic soundness
  or representation adequacy;
- arbitrary semantic observation factorization;
- T6 `$math-lean-review`.
