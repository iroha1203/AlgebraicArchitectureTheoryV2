---
goal: G-sft-conway-01
cycle: 32
candidate_type: selector
evidence_stage: proved-in-research
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
categories:
  - conway-obstruction
  - selected-conflict-set
  - membership
  - miss-selector
---

# Selected conflict membership

## Claim

For the selected reorg/refactor edit shapes, selected hitting is equivalent to
having no pointwise missed selected conflict.

Canonical reorg/refactor edits miss no selected conflicts.  The existing
partial reorg edit misses exactly `platformDb`, and the existing API-only
partial refactor edit misses exactly `db`.

## Lean evidence

- `Formal/AG/Research/SFT/ConwaySelectedConflictMembership.lean`
- `ReorgCoverEditActivatesSelectedConflict`
- `ReorgCoverEditMissesSelectedConflict`
- `reorgHitsSelectedConflictSet_iff_noSelectedMiss`
- `canonicalReorgCoverEdit_noSelectedMiss`
- `partialReorgMissesDbConflict_missesSelectedConflict_iff`
- `partialReorgMissesDbConflict_hasSelectedMiss`
- `RefactorOwnershipEditMissesSelectedConflict`
- `refactorHitsSelectedConflictSet_iff_noSelectedMiss`
- `canonicalRefactorOwnershipEdit_noSelectedMiss`
- `partialRefactorSupportsOnlyApi_missesSelectedConflict_iff`
- `partialRefactorSupportsOnlyApi_hasSelectedMiss`
- `selectedConflictMembershipPackage`

## Value

This moves selected conflict sets from aggregate hitting predicates to
pointwise membership and exact miss selectors.  It gives later refinement or
diagnostic work a precise selected conflict identity instead of only a failed
finite table.

## Boundaries

This is still selected finite Conway vocabulary.  It is not an arbitrary
conflict enumeration algorithm, runtime diagnostic, or general repair calculus.
