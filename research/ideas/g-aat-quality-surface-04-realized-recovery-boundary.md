---
goal: G-aat-quality-surface-04
cycle: 40
status: picked
candidate: Realized Recovery Coordinate-Extraction Boundary
candidate_type: target-refinement
capability_category: finite-query-representation / realized-recovery / coordinate-extraction / anti-weakening
expected_base_score: 44
expected_evidence_multiplier: 2.0
expected_final_score: 88
evidence_stage: proved-in-research
score_status: T4 confirmed as target-refined
base_score: 44
evidence_multiplier: 2.0
penalty: 0
final_score: 88
score_reason: Axiom-free Lean target-refinement with realized-tower recovery and Bool anti-weakening witnesses; below main descent theorem strength.
goal_advancement: Narrows the coordinate-extraction recovery premise to realized towers and exposes the next semantic soundness / representation adequacy discharge obligation.
rival_advantage: Makes the decoder/recovery condition visible on realized semantic repair towers instead of hiding representation adequacy inside an observation field.
dullness_risk: low; it weakens the decoder domain from arbitrary shadow/readings pairs to realized towers and adds a support-factor/no-current-factor recovery witness.
proof_or_evidence_plan: Completed in Lean; use T2/T3/T3.5/T4 audits and PR review before ledger sync.
planned_theorem_names:
  - QueryReadingsRecoveringPostOnRealizedTowers
  - ObservationRecoversQueryReadings
  - queryReadingsRecoveringPostOnRealizedTowers_of_queryReadingsRecoveringPost
  - queryTraceVector_shadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers
  - queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers
  - finiteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers
  - queryReadingsRecoveringPostOnRealizedTowers_of_observationRecoversQueryReadings
  - representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_observationRecoversQueryReadings
  - representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_shadowExtensional_of_observationRecoversQueryReadings
  - representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowFactor_of_observationRecoversQueryReadings
  - queryTraceReadingsObservation_recoversQueryReadings
  - queryTraceReadingsRepresentation_recoversQueryReadingsOnRealizedTowers
  - not_boolTrueConstantPost_queryReadingsRecoveringPostOnRealizedTowers
  - boolTrueConstantPost_currentShadowFaithful_but_not_queryReadingsRecoveringPostOnRealizedTowers
  - boolFirstQueryRepresentation_supportFactor_no_currentFactor_but_recoversReadings
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: realized-tower query-reading recovery to current-shadow coordinate extraction
target_progress: target-refined
proof_obligation_delta: Cycle 39's uniform all-shadow decoder premise is reduced to a realized-tower recovery premise, and visible represented-observation recovery now transports to coordinate-extensionality extraction.
target_completion_role: support/refinement only; not target completion
material_premises: QueryReadingsRecoveringPostOnRealizedTowers and ObservationRecoversQueryReadings remain visible theorem arguments.
premise_discharge_plan: Future work must derive realized recovery from principled semantic soundness or representation adequacy certificates without baking in current-shadow factorization or query-coordinate extensionality.
anti_weakening_verdict: pass as target-refinement; reject if promoted to target theorem completion.
claim_boundary: target-refinement only; no arbitrary semantic soundness / representation adequacy discharge and no target theorem completion.
statement_strength_audit: conditional extraction theorem is intentionally bounded by visible recovery and faithfulness/factorization premises.
dependency_plan: import Cycle 39 recoverable-readings boundary and reuse Cycle 38 current-shadow coordinate extraction theorems.
origin: G-aat-quality-surface-04-cycle-40
tags: [target-theorem, target-refinement, finite-query, current-shadow, anti-weakening]
created: 2026-06-25
lean: proved-in-research
math_lean_review_scope: not run this cycle
---

# Realized Recovery Coordinate-Extraction Boundary

## Claim

Cycle 40 replaces the stronger Cycle 39 uniform post-map decoder with a
realized-tower decoder.  A post-map only needs to recover query readings on
actual `FiniteSemanticRepairObstructionTower` values.  A visible
`FiniteTraceQueryObservationRepresentation` can then transport an
observation-level decoder to the representing post-map on realized towers, and
current-shadow faithfulness/factorization extracts
`QueryTraceCoordinatesCurrentShadowExtensional`.

This is not a theorem that arbitrary semantic soundness or representation
adequacy implies coordinate extraction.  Recovery remains explicit theorem
data.

## Candidate Type

`target-refinement`

## Dependencies

- GOAL `G-aat-quality-surface-04` target theorem, material premise ledger, and
  anti-weakening rule.
- Cycle 38 current-shadow coordinate obligations.
- Cycle 39 recoverable readings boundary.
- Lean file:
  `Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryRepresentationRealizedRecovery.lean`

## Lean Surface

- `QueryReadingsRecoveringPostOnRealizedTowers`
- `ObservationRecoversQueryReadings`
- `queryReadingsRecoveringPostOnRealizedTowers_of_queryReadingsRecoveringPost`
- `queryTraceVector_shadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers`
- `queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers`
- `finiteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers`
- `queryReadingsRecoveringPostOnRealizedTowers_of_observationRecoversQueryReadings`
- `representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_observationRecoversQueryReadings`
- `representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_shadowExtensional_of_observationRecoversQueryReadings`
- `representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowFactor_of_observationRecoversQueryReadings`
- `queryTraceReadingsObservation_recoversQueryReadings`
- `queryTraceReadingsRepresentation_recoversQueryReadingsOnRealizedTowers`
- `not_boolTrueConstantPost_queryReadingsRecoveringPostOnRealizedTowers`
- `boolTrueConstantPost_currentShadowFaithful_but_not_queryReadingsRecoveringPostOnRealizedTowers`
- `boolFirstQueryRepresentation_supportFactor_no_currentFactor_but_recoversReadings`

## Nontriviality

The realized premise is strictly better aligned with the target boundary than a
decoder for arbitrary unattested `shadow/readings` pairs.  It still avoids the
anti-weakening failure: the decoder is not hidden in representation adequacy,
and the Bool witnesses show that current-shadow faithfulness alone does not
recover readings, while support-shadow factorization plus reading recovery does
not imply current-shadow factorization.

## Mathematical Interest

This separates three notions that could otherwise be conflated:

- current-shadow faithfulness of a represented post-map;
- output-level recovery of the finite query readings on realized towers;
- current-shadow factorization / query-coordinate extensionality.

The separation gives a sharper proof boundary for future semantic faithfulness
or representation adequacy discharge theorems.

## GOAL Advancement

The support node advances the representation-adequacy / semantic-faithfulness
discharge frontier by identifying the exact realized recovery premise needed to
extract current-shadow coordinate extensionality from represented observations.

## Rival Advantage

An ADL analyzer or metric dashboard can expose a finite query result, but it
usually does not distinguish whether the result is recoverable from the
reported observation on realized semantic towers or whether a factorization
premise has been silently assumed.  This Lean package makes that distinction
theorem-level.

## SCORE Expectation

- `score_reason`: base 44, multiplier 2.0 expected.  The contribution is a
  target-boundary refinement with axiom-free Lean evidence and explicit Bool
  obstruction witnesses, but it remains below a main descent theorem.
- `dullness_risk`: low.  It is not a notation-only restatement of Cycle 39
  because it weakens the decoder domain to realized towers and adds a
  support-factor/no-current-factor recovery witness.
- `proof_or_evidence_plan`: completed in Lean; T2/T3/T3.5/T4 audits must
  decide final score and target progress.

## Target Theorem Contribution

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem.
- `target_support_node`: realized-tower query-reading recovery to
  current-shadow coordinate extraction.
- `target_progress`: target-refined.
- `proof_obligation_delta`: Cycle 39's uniform recovery premise is narrowed to
  realized towers; represented observation recovery now transports to
  post-map recovery; Bool witnesses keep the boundary fail-closed.
- `target_completion_role`: support/refinement only.  T6 is not run and target
  completion is not claimed.

## Evidence

Verification already passed for this candidate:

- `lake env lean Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryRepresentationRealizedRecovery.lean`
- `lake build Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryRepresentationRealizedRecovery`
- `lake env lean Formal/AG/Research.lean`
- `lake build Formal.AG.Research`
- `lake build FormalAGResearch`
- `lake build`
- `.tmp/g04_realized_recovery_axioms.lean` axiom audit: 13 reported
  declarations, no axioms.
- placeholder scan, hidden Unicode scan, local path scan, and `git diff --check`
  clean.

## Judge Notes

- rigor: T2 accept.  The candidate is a rigorous support/refinement node; the
  realized recovery and observation recovery premises remain visible.
- proof distance: T2 accept.  Proof distance improves moderately by replacing
  Cycle 39's all-shadow decoder with realized-tower recovery, but semantic
  soundness / representation adequacy discharge remains open.
- premise / anti-weakening: T2 accept.  `QueryReadingsRecoveringPostOnRealizedTowers`
  and `ObservationRecoversQueryReadings` are new visible premises, not hidden
  completion evidence.
- project value: T2 accept with base score 44.
- T3 axiom/formalization quality: pass.  Focused checks, aggregate builds,
  full `lake build`, and the 13-declaration axiom audit passed; the target file
  remains under `Formal/AG/Research`.
- T3.5 sync: initial revise until this card/report synchronization; final
  sync audit should see Cycle 40 report entry, T4 score, and explicit
  visible-undischarged premise status.
- T4 SCORE: confirm, base 44, multiplier 2.0, final 88,
  `target_progress: target-refined`.

## Related

- `research/ideas/g-aat-quality-surface-04-recoverable-readings-boundary.md`
- `Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryRepresentationRecoverableReadings.lean`

## Progress Log

- 2026-06-25: Cycle 40 candidate created after focused Lean, aggregate build,
  full `lake build`, and axiom audit passed.
- 2026-06-25: T2 accepted from rigor, proof-distance, anti-weakening, and
  rival-value lanes; T3 passed axiom and formalization-quality audits; T4
  confirmed +88 as `target-refined`.
