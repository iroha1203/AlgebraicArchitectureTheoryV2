---
goal: G-sft-conway-01
cycle: 26
candidate_type: bridge
evidence_stage: proved-in-research
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
categories:
  - conway-obstruction
  - finite-conflict-table
  - communication-support
  - reorg-refactor-duality
---

# Finite conflict table

## Claim

For the selected two-module Conway vocabulary, the operation-shaped hitting
predicates from Cycle 23 are equivalent to finite conflict tables.  These
tables are also equivalent to existence of Cycle 25 communication-support
assignment data for the post-edit atlas.

The canonical reorg/refactor repairs satisfy their finite tables.  The selected
Cycle 24 missed-conflict reorg and API-only refactor edits fail their finite
tables.

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayFiniteConflictTable.lean`
- `ReorgCoverEditFiniteConflictTable`
- `reorgCoverEditHitsEveryConflict_iff_finiteConflictTable`
- `ReorgCoverEdit.supportAssignment_nonempty_iff_finiteConflictTable`
- `canonicalReorgCoverEdit_finiteConflictTable`
- `partialReorgMissesDbConflict_not_finiteConflictTable`
- `RefactorOwnershipEditFiniteConflictTable`
- `refactorOwnershipEditHitsEveryConflict_iff_finiteConflictTable`
- `RefactorOwnershipEdit.supportAssignment_nonempty_iff_finiteConflictTable`
- `canonicalRefactorOwnershipEdit_finiteConflictTable`
- `partialRefactorSupportsOnlyApi_not_finiteConflictTable`
- `selectedFiniteConflictTablePackage`

## Value

This makes the selected Conway conflict checking surface finite and explicit.
It connects operation criteria, support-assignment existence, positive repairs,
and negative missed-hit witnesses through one table interface.  The result is a
stepping stone toward a general conflict-set hitting predicate, but its current
value is a selected finite table bridge.

## Boundaries

This is not yet a general conflict-set calculus for arbitrary covers.  The
table is specialized to the finite two-module Conway vocabulary and the
Cycle 23 reorg/refactor edit shapes.
