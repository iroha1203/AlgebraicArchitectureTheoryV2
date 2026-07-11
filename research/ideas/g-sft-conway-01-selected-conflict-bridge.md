---
goal: G-sft-conway-01
cycle: 30
candidate_type: bridge
evidence_stage: proved-in-research
base_score: 25
evidence_multiplier: 2.0
penalty: 10
final_score: 40
categories:
  - conway-obstruction
  - selected-conflict-set
  - support-assignment
  - repair-transition
---

# Selected conflict bridge

## Claim

For the selected reorg/refactor edit shapes, selected conflict-set hitting is
equivalent to the older operation-shaped hitting predicates, post-edit
support-assignment existence, and selected repair-transition existence.

Selected conflict-set hitting also implies that the post-edit atlas has no
selected Conway obstruction.

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwaySelectedConflictMorphism.lean`
- `reorgHitsSelectedConflictSet_iff_hitsEveryConflict`
- `refactorHitsSelectedConflictSet_iff_hitsEveryConflict`
- `reorgHitsSelectedConflictSet_iff_supportAssignment`
- `refactorHitsSelectedConflictSet_iff_supportAssignment`
- `reorgNoConwayObstruction_of_hitsSelectedConflictSet`
- `refactorNoConwayObstruction_of_hitsSelectedConflictSet`
- `selectedConflictBridgePackage`

## Value

This connects the Cycle 29 selected conflict-set vocabulary back to the
existing operation-shaped hitting, support-assignment, and repair-transition
existence criteria.  It gives later work a single bounded bridge point where
membership, selector preservation, or refinement statements can attach.

## Boundaries

This is a bridge over the selected finite Conway vocabulary.  It is not a
general conflict-set morphism category, arbitrary conflict enumeration
algorithm, repair composition theorem, or empirical organizational claim.
