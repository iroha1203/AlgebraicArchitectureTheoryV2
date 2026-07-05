---
goal: G-sft-conway-01
cycle: 28
candidate_type: criterion
evidence_stage: proved-in-research
base_score: 35
evidence_multiplier: 2.0
penalty: 10
final_score: 60
categories:
  - conway-obstruction
  - repair-transition
  - finite-conflict-table
  - communication-support
---

# Repair transition criterion

## Claim

For the selected reorg/refactor edit shapes, finite conflict-table satisfaction
is equivalent to existence of a selected repair-transition record from
`mismatchedAtlas` to the edit's post-edit atlas.

Canonical reorg/refactor edits realize repair-transition records.  The selected
missed-conflict reorg and API-only refactor edits realize no such record.

## Lean evidence

- `Formal/AG/Research/SFT/ConwayRepairTransitionCriterion.lean`
- `ReorgCoverEditRepairTransition`
- `ReorgCoverEdit.repairTransition_nonempty_iff_finiteConflictTable`
- `ReorgCoverEdit.canonicalRepairTransition_nonempty`
- `ReorgCoverEdit.partialMissesDbConflict_noRepairTransition`
- `RefactorOwnershipEditRepairTransition`
- `RefactorOwnershipEdit.repairTransition_nonempty_iff_finiteConflictTable`
- `RefactorOwnershipEdit.canonicalRepairTransition_nonempty`
- `RefactorOwnershipEdit.partialSupportsOnlyApi_noRepairTransition`
- `selectedRepairTransitionCriterionPackage`

## Value

This moves beyond transition record packaging: it proves a criterion for when
an edit realizes a selected repair-transition record.  The same finite table
interface classifies canonical success and selected missed-conflict failure.

## Boundaries

This is still selected finite Conway vocabulary.  It is not an arbitrary repair
calculus, a transition-composition theorem, or a general conflict-set calculus.
