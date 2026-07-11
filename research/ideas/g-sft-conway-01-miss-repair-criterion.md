---
goal: G-sft-conway-01
cycle: 34
candidate_type: criterion
evidence_stage: proved-in-research
base_score: 35
evidence_multiplier: 2.0
penalty: 10
final_score: 60
categories:
  - conway-obstruction
  - first-miss-scanner
  - repair-transition
  - criterion
---

# Miss repair criterion

## Claim

For the selected reorg/refactor edit shapes, existence of a selected first miss
is equivalent to absence of a selected repair-transition record.

Thus the bounded first-miss scanner is complete for the selected
repair-transition existence criterion.

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayMissRepairCriterion.lean`
- `reorgSelectedMiss_exists_iff_noRepairTransition`
- `reorgFirstSelectedMiss_exists_iff_noRepairTransition`
- `canonicalReorgCoverEdit_repairTransition_iff_noFirstMiss`
- `partialReorgMissesDbConflict_firstMiss_iff_noRepairTransition`
- `refactorSelectedMiss_exists_iff_noRepairTransition`
- `refactorFirstSelectedMiss_exists_iff_noRepairTransition`
- `canonicalRefactorOwnershipEdit_repairTransition_iff_noFirstMiss`
- `partialRefactorSupportsOnlyApi_firstMiss_iff_noRepairTransition`
- `selectedMissRepairCriterionPackage`

## Value

This connects the first-miss selector to the selected repair-transition
criterion rather than leaving it as a diagnostic wrapper.  It makes a selected
first miss a complete obstruction to the selected repair-transition record for
both edit families.

## Boundaries

This remains selected finite Conway vocabulary.  It is not an arbitrary repair
calculus, runtime extraction algorithm, or general conflict enumeration result.
