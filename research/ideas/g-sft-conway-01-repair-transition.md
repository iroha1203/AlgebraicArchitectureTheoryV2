---
goal: G-sft-conway-01
cycle: 27
candidate_type: transition
evidence_stage: proved-in-research
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
categories:
  - conway-obstruction
  - repair-transition
  - communication-support
  - finite-operation
---

# Repair transition objects

## Claim

For the selected canonical Conway mismatch, both canonical one-sided repairs
can be recorded as before/after transition objects: the before atlas is
`mismatchedAtlas`, the after atlas has support-assignment existence, and the
selected Conway obstruction is absent after the transition.

The selected missed-conflict edits are recorded as transition failures.  The
missed reorg edit lacks a post-edit support assignment and still has an actual
selected Conway obstruction.  The API-only refactor edit lacks post-edit
support-assignment existence without claiming a two-owner obstruction witness for
the single-owner refactor shape.

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayRepairTransition.lean`
- `ConwayRepairTransition`
- `ConwayAssignmentFailedTransition`
- `ConwayObstructionPreservingTransition`
- `CanonicalRepairOperation.repairTransition`
- `CanonicalRepairOperation.repairTransition_before`
- `CanonicalRepairOperation.repairTransition_after`
- `partialReorgMissesDbConflict_assignmentFailedTransition`
- `partialReorgMissesDbConflict_obstructionPreservingTransition`
- `partialRefactorSupportsOnlyApi_assignmentFailedTransition`
- `selectedRepairTransitionPackage`

## Value

This is the first selected before/after transition vocabulary for the Conway
repair thread.  It packages the canonical mismatch, canonical repairs,
support-assignment existence, obstruction elimination, and missed-conflict
failure witnesses.

## Boundaries

This is not an arbitrary repair calculus or optimality theorem.  The transition
objects are selected finite witnesses over the current Conway two-module
vocabulary and Cycle 23 reorg/refactor edit shapes.
