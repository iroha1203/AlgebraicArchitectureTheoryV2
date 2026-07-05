---
goal: G-sft-conway-01
cycle: 36
candidate_type: bridge
evidence_stage: proved-in-research
base_score: 15
evidence_multiplier: 2.0
penalty: 10
final_score: 20
categories:
  - conway-obstruction
  - first-miss-scanner
  - selected-conflict-set
  - no-miss-criterion
---

# First-miss no-miss bridge

## Claim

For the selected reorg/refactor edit shapes, absence of a selected first miss is
equivalent to pointwise absence of selected misses.

## Lean evidence

- `Formal/AG/Research/SFT/ConwayFirstMissNoMissBridge.lean`
- `reorgNoFirstSelectedMiss_iff_noSelectedMiss`
- `refactorNoFirstSelectedMiss_iff_noSelectedMiss`
- `selectedFirstMissNoMissBridgePackage`

## Value

This exposes the direct negative-side bridge between the bounded first-miss
scanner and the pointwise selected miss predicate.  Downstream statements can
refer to a no-first-miss criterion without re-deriving the existential
first-miss completeness equivalence.

## Boundaries

This is selected finite Conway vocabulary.  It is not an arbitrary conflict
enumeration algorithm, a runtime diagnostic procedure, or a general repair
calculus.
