---
goal: G-sft-conway-01
cycle: 31
candidate_type: witness
evidence_stage: proved-in-research
base_score: 35
evidence_multiplier: 2.0
penalty: 10
final_score: 60
categories:
  - conway-obstruction
  - refactor-failure
  - two-owner-witness
  - obstruction-preserving-transition
---

# Refactor two-owner obstruction witness

## Claim

There is a selected refactor-side failure shape that keeps the all-communication
block but retains split two-owner ownership.  Its post-edit atlas is the
canonical mismatched atlas, so it is not compatible, has no communication
support assignment, and preserves an actual selected Conway obstruction.

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayRefactorTwoOwnerObstruction.lean`
- `RefactorTwoOwnerFailureEdit`
- `refactorKeepsSplitOwnership`
- `refactorKeepsSplitOwnership_postAtlas_eq_mismatchedAtlas`
- `refactorKeepsSplitOwnership_not_compatible`
- `refactorKeepsSplitOwnership_nonzeroConwayObstruction`
- `refactorKeepsSplitOwnership_noCommunicationSupportAssignment`
- `refactorKeepsSplitOwnership_obstructionPreservingTransition`
- `selectedRefactorTwoOwnerObstructionPackage`

## Value

Cycle 24 could only state refactor-side hitting and compatibility failure
because the original refactor edit shape collapsed ownership to one owner.
This adds the missing selected two-owner refactor failure witness and connects
it to the obstruction-preserving transition vocabulary, within the bounded
selected two-module refactor-failure shape.

## Boundaries

This is still a selected finite witness over the canonical two-module Conway
vocabulary.  It does not claim an arbitrary refactor calculus, optimal repair,
general transition composition, or empirical organizational causality.
