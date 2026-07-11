---
goal: G-aat-quality-surface-04
cycle: 41
status: picked
candidate: Support-Shadow Realized Recovery Discharge
candidate_type: target-support
capability_category: finite-query-representation / support-shadow-recovery / realized-recovery-discharge / anti-weakening
expected_base_score: 48
expected_evidence_multiplier: 2.0
expected_final_score: 96
evidence_stage: proved-in-research
score_status: T4 confirmed as support-node
base_score: 48
evidence_multiplier: 2.0
penalty: 0
final_score: 96
score_reason: Axiom-free Lean support theorem discharging realized recovery for canonical support-shadow observations while preserving current-shadow factorization as a separate obligation.
goal_advancement: Reduces Cycle 40's visible recovery premise for the support-shadow observation class without claiming current-shadow adequacy or target completion.
rival_advantage: Separates query-reading recoverability from descent to current shadow, a distinction finite dashboards and ADL-style local outputs usually conflate.
dullness_risk: low; it constructs an explicit decoder from support-shadow factorization rather than renaming recovery as adequacy.
proof_or_evidence_plan: Completed in Lean; T2/T3/T3.5/T4 audits must confirm score and boundary.
planned_theorem_names:
  - supportTraceShadowObservation_recoversSupportedQueryReadings
  - completeSupportTraceShadowObservation_recoversQueryReadings
  - supportTraceShadowFiniteTraceQueryObservation_recoversQueryReadings
  - supportTraceShadowRepresentation_recoversQueryReadingsOnRealizedTowers
  - boolTrueCompleteSupportTraceShadowObservation_recoversQueryReadings
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite-query realized recovery discharge via support-shadow decoder
target_progress: support-node
proof_obligation_delta: Cycle 40's visible `ObservationRecoversQueryReadings` and `QueryReadingsRecoveringPostOnRealizedTowers` premises are discharged for the canonical support-shadow observation / representation under visible query-support or complete-support certificates.
target_completion_role: support-node only; not target completion
material_premises: `QuerySupportedBy support query` or `FiniteSupportComplete support` remains visible input geometry; current-shadow factorization, semantic-reading faithfulness, and query-coordinate extensionality remain undischarged.
premise_discharge_plan: Later work must still extract current-shadow factorization / semantic-reading adequacy from non-circular semantic soundness or representation adequacy certificates.
anti_weakening_verdict: pass as target-support; reject if support-shadow recovery is promoted to current-shadow adequacy or target theorem completion.
claim_boundary: support-shadow recovery only; no arbitrary semantic soundness / representation adequacy discharge and no target theorem completion.
statement_strength_audit: conditional recovery theorem is bounded by visible support/query certificates and does not assert current-shadow descent.
dependency_plan: import Cycle 40 realized recovery and existing finite support/query admissibility theorems.
origin: G-aat-quality-surface-04-cycle-41
tags: [target-theorem, target-support, finite-query, support-shadow, anti-weakening]
created: 2026-06-25
lean: proved-in-research
math_lean_review_scope: not run this cycle
---

# Support-Shadow Realized Recovery Discharge

## Claim

If a finite query is visibly supported by a finite support list, then the
canonical support trace shadow recovers the query readings on realized semantic
repair towers.  Therefore, for the canonical support-shadow finite-query
representation, the Cycle 40 realized-post recovery premise is discharged by a
concrete decoder.

This does not imply current-shadow factorization, query-coordinate
extensionality, semantic-reading faithfulness, global repair coherence, or
target theorem completion.

## Candidate Type

`target-support`

## Dependencies

- GOAL `G-aat-quality-surface-04` target theorem, material premise ledger, and
  anti-weakening rule.
- Cycle 20 query support / support-shadow factorization.
- Cycle 37 support-shadow finite-query representation.
- Cycle 40 realized recovery transport.
- Lean file:
  `research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryRepresentationSupportRecovery.lean`

## Lean Surface

- `supportTraceShadowObservation_recoversSupportedQueryReadings`
- `completeSupportTraceShadowObservation_recoversQueryReadings`
- `supportTraceShadowFiniteTraceQueryObservation_recoversQueryReadings`
- `supportTraceShadowRepresentation_recoversQueryReadingsOnRealizedTowers`
- `boolTrueCompleteSupportTraceShadowObservation_recoversQueryReadings`

## Nontriviality

The theorem is not a renaming of representation adequacy.  The decoder is
constructed from `queryTraceVector_factors_through_supportTraceShadow` and only
works for query/support certificates that are already visible.  Current-shadow
descent remains separate.

## Mathematical Interest

This identifies a precise intermediate level between raw recovery premises and
current-shadow adequacy:

- support-shadow output can recover supported query readings;
- current-shadow output may still forget those readings;
- semantic/representation adequacy must still prove a non-circular descent or
  factorization condition.

## GOAL Advancement

Cycle 41 reduces the realized recovery proof obligation for the support-shadow
observation class, while preserving the anti-weakening boundary that recovery
is not current-shadow adequacy.

## Rival Advantage

Finite analysis tools can expose local query outputs, but they usually do not
separate "the output contains recoverable support readings" from "the output
descends to the current canonical shadow."  This theorem makes that separation
auditable.

## SCORE Expectation

- `score_reason`: expected base 48, multiplier 2.0.  The theorem discharges a
  visible recovery premise for a canonical support-shadow class, but does not
  discharge current-shadow factorization or representation adequacy.
- `dullness_risk`: low.  It constructs a concrete support-shadow decoder and
  keeps the target proof boundary fail-closed.
- `proof_or_evidence_plan`: completed in Lean; T2/T3/T3.5/T4 audits must
  decide final score and target progress.

## Target Theorem Contribution

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem.
- `target_support_node`: finite-query realized recovery discharge via
  support-shadow decoder.
- `target_progress`: support-node.
- `proof_obligation_delta`: support-shadow observations / representations now
  discharge Cycle 40 realized recovery under visible query-support or
  complete-support certificates.
- `target_completion_role`: support-node only.  T6 is not run and target
  completion is not claimed.

## Evidence

Verification already passed for this candidate:

- `lake env lean research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryRepresentationSupportRecovery.lean`
- `lake build ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryRepresentationSupportRecovery`
- `lake env lean research/lean/ResearchLean.lean`
- `lake build ResearchLean.AG`
- `lake build ResearchLean`
- `lake build`
- `.tmp/g04_support_recovery_axioms.lean` axiom audit: 5 reported declarations,
  no axioms.
- placeholder scan, hidden Unicode scan, local path scan, and `git diff --check`
  clean.

## Judge Notes

- T1 premise-discharge: recommends this support-shadow decoder route as
  `target-support`.
- T1 statement-audit / proof-dag: exact criterion package is useful but can
  remain a later refinement.
- T1 obstruction: Bool recovery/no-current-factor witness remains the
  anti-weakening guard.
- T2: four lanes accepted; `target_progress: support-node`; base score 48.
- T3 axiom/formalization quality: pass.  Focused Lean, aggregate builds, full
  `lake build`, and 5-declaration axiom audit passed.
- T3.5 sync: initial revise until this card/report synchronization; final sync
  should see Cycle 41 score, report entry, and premise status.
- T4 SCORE: confirm, base 48, multiplier 2.0, final 96,
  `target_progress: support-node`.

## Premise Status

- `ObservationRecoversQueryReadings`: discharged for canonical support-shadow
  observations when the query is visibly supported by the support list.
- `QueryReadingsRecoveringPostOnRealizedTowers`: discharged for the canonical
  support-shadow finite-query representation.
- `QuerySupportedBy support query` / `FiniteSupportComplete support`: visible
  input geometry.
- current-shadow factorization, semantic-reading faithfulness,
  query-coordinate extensionality, semantic soundness / representation adequacy:
  not discharged.
- new material premise: none.

## Related

- `research/ideas/g-aat-quality-surface-04-realized-recovery-boundary.md`
- `research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteQueryRepresentationRealizedRecovery.lean`

## Progress Log

- 2026-06-25: Cycle 41 candidate created after focused Lean, aggregate build,
  full `lake build`, and axiom audit passed.
- 2026-06-25: T2 accepted from all lanes; T3 passed axiom and
  formalization-quality audits; T4 confirmed +96 as `support-node`.
