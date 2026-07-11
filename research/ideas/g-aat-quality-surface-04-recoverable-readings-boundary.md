---
goal: G-aat-quality-surface-04
cycle: 39
status: picked
candidate: Recoverable Readings Coordinate-Extraction Boundary
candidate_type: target-refinement
evidence_stage: proved-in-research
score_status: T4 confirmed as target-refined
base_score: 44
evidence_multiplier: 2.0
penalty: 0
final_score: 88
target_progress: target-refined
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: uniformly output-decodable query readings to coordinate-extensionality extraction boundary
proof_obligation_delta: Uniformly recoverable query-readings post-maps, raw query-readings observations, and query support-shadow semantic adequacy now expose the exact coordinate-extensionality boundary.
material_premises: QueryReadingsRecoveringPost is a visible theorem argument; arbitrary semantic soundness / representation adequacy is not discharged.
premise_discharge_status: partial refinement only; no generic SemanticSound -> QueryTraceCoordinatesCurrentShadowExtensional theorem.
anti_weakening_verdict: pass as target-refinement; reject if promoted to target theorem completion.
claim_boundary: not target completion; exact support-shadow adequacy and recoverability are completion-sensitive visible premises.
math_lean_review_scope: not run this cycle
lean_files:
  - research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryRepresentationRecoverableReadings.lean
lean_declarations:
  - QueryReadingsRecoveringPost
  - queryTraceReadingsPost
  - queryTraceReadingsPost_recovers
  - queryTraceReadingsFiniteTraceQueryObservation
  - queryTraceReadingsFiniteTraceQueryObservation_observe_eq
  - queryTraceReadingsFiniteTraceQueryObservationRepresentation
  - queryTraceVector_shadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
  - queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
  - finiteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
  - representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
  - queryTraceReadingsObservation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional
  - queryTraceReadingsRepresentation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional
  - queryCoordinateCurrentShadowExtensional_iff_querySupportShadowObservation_exists_semanticReadingAdequacy
  - queryCoordinateCurrentShadowExtensional_of_querySupportShadow_currentShadowFactor
  - no_boolTrueQuerySupportShadow_currentShadowFactor
  - boolTrueConstantFiniteTraceQueryObservation_currentShadowFaithful_not_queryCoordinateCurrentShadowExtensional
  - boolFirstQueryRepresentation_supportFactor_but_no_currentShadowFactor
  - no_boolFirstRepresentedFiniteTraceQueryObservation_semanticReadingAdequacy
  - not_boolTrueTraceQuerySupportShadowObservation_exists_semanticReadingAdequacy
  - nilQuery_queryTraceReadingsObservation_currentShadowSemanticReading_faithful
  - not_boolTrueQueryTraceReadingsObservation_currentShadowSemanticReading_faithful
t3_verification: focused Lean, module build, ResearchLean.AG, ResearchLean, full lake build, axiom audit, placeholder scan, hidden Unicode scan, local path scan, and git diff check passed.
---

# Recoverable Readings Coordinate-Extraction Boundary

Cycle 39 gives a non-circular route from canonical current-shadow reading
faithfulness to query-coordinate extensionality for uniformly output-decodable
post-maps.

The new Lean file
`research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryRepresentationRecoverableReadings.lean`
defines `QueryReadingsRecoveringPost`, a visible decoder premise saying that the
post-map output uniformly recovers the finite query readings.  Under this
premise, current-shadow reading faithfulness forces the query trace vector to
be current-shadow extensional, hence forces
`QueryTraceCoordinatesCurrentShadowExtensional`.

The file also shows that raw query-readings observations and query
support-shadow semantic adequacy are exact boundary tests: they are equivalent
to query-coordinate extensionality, not weaker semantic-soundness facts.

## Lean Surface

- `queryTraceVector_shadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost`
- `queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost`
- `finiteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost`
- `representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost`
- `queryTraceReadingsObservation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional`
- `queryCoordinateCurrentShadowExtensional_iff_querySupportShadowObservation_exists_semanticReadingAdequacy`
- `queryCoordinateCurrentShadowExtensional_of_querySupportShadow_currentShadowFactor`
- `no_boolTrueQuerySupportShadow_currentShadowFactor`
- `boolTrueConstantFiniteTraceQueryObservation_currentShadowFaithful_not_queryCoordinateCurrentShadowExtensional`
- `boolFirstQueryRepresentation_supportFactor_but_no_currentShadowFactor`
- `no_boolFirstRepresentedFiniteTraceQueryObservation_semanticReadingAdequacy`
- `not_boolTrueTraceQuerySupportShadowObservation_exists_semanticReadingAdequacy`

## Boundary

This is a `target-refinement` support node, not target completion.  It does not
claim arbitrary semantic soundness, representation adequacy, or current-shadow
faithfulness implies query-coordinate extensionality.  The decoder premise is a
visible theorem argument, and support-shadow semantic adequacy is proved to be
equivalent to the coordinate boundary rather than hidden as an adequacy field.

Remaining blockers:

- extraction of uniformly recoverable post-map premises from principled
  semantic soundness / representation adequacy;
- arbitrary semantic observation factorization;
- T6 `$math-lean-review`.
