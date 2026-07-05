---
goal: G-sft-conway-01
cycle: 35
candidate_type: criterion
evidence_stage: proved-in-research
base_score: 20
evidence_multiplier: 2.0
penalty: 10
final_score: 30
categories:
  - conway-obstruction
  - first-miss-scanner
  - repair-transition
  - positive-criterion
---

# No-miss repair criterion

## Claim

For the selected reorg/refactor edit shapes, absence of selected first misses,
absence of any selected miss, and selected repair-transition existence coincide.

## Lean evidence

- `Formal/AG/Research/SFT/ConwayNoMissRepairCriterion.lean`
- `reorgNoFirstSelectedMiss_iff_repairTransition`
- `refactorNoFirstSelectedMiss_iff_repairTransition`
- `reorgNoSelectedMiss_iff_repairTransition`
- `refactorNoSelectedMiss_iff_repairTransition`
- `selectedNoMissRepairCriterionPackage`

## Value

This records the positive repair criterion corresponding to Cycle 34's
negative miss criterion.  It gives downstream statements a direct no-miss to
repair-transition theorem rather than requiring them to reason through a
double negation.

## Boundaries

This is selected finite Conway vocabulary and a positive-side bridge theorem.
It is not an arbitrary repair calculus, runtime diagnostic procedure, or
general conflict enumeration result.
