---
goal: G-sft-conway-01
cycle: 29
candidate_type: interface
evidence_stage: proved-in-research
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
categories:
  - conway-obstruction
  - selected-conflict-set
  - repair-transition
  - finite-conflict-table
---

# Selected conflict-set interface

## Claim

For the selected reorg/refactor edit shapes, the hard-coded finite conflict
tables factor through explicit selected table-obligation indices and hitting
predicates.

Selected hitting is equivalent to finite-table satisfaction and to selected
repair-transition record existence.  Canonical repairs hit the selected
obligation sets; selected missed-conflict edits do not.

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwaySelectedConflictSet.lean`
- `ReorgSelectedConflict`
- `ReorgCoverEditHitsSelectedConflictSet`
- `reorgHitsSelectedConflictSet_iff_finiteConflictTable`
- `reorgRepairTransition_nonempty_iff_hitsSelectedConflictSet`
- `canonicalReorgCoverEdit_hitsSelectedConflictSet`
- `partialReorgMissesDbConflict_not_hitsSelectedConflictSet`
- `RefactorSelectedConflict`
- `RefactorOwnershipEditHitsSelectedConflictSet`
- `refactorHitsSelectedConflictSet_iff_finiteConflictTable`
- `refactorRepairTransition_nonempty_iff_hitsSelectedConflictSet`
- `canonicalRefactorOwnershipEdit_hitsSelectedConflictSet`
- `partialRefactorSupportsOnlyApi_not_hitsSelectedConflictSet`
- `selectedConflictSetPackage`

## Value

This moves the selected finite table from conjunction syntax to explicit
table-obligation vocabulary.  It gives later cycles a bounded place to attach
membership, refinement, or conflict-set morphism statements without claiming an
arbitrary conflict enumeration algorithm.

## Boundaries

This is still selected finite Conway vocabulary.  The conflict sets are
hand-selected for the current two-module reorg/refactor edit shapes; this is
not an arbitrary conflict-set calculus or general repair algorithm.
