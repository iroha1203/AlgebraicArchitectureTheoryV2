---
goal: G-sft-conway-01
cycle: 25
candidate_type: closure
evidence_stage: proved-in-research
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
categories:
  - conway-obstruction
  - communication-support
  - finite-assignment
  - reorg-refactor-duality
---

# Communication-support assignment bridge

## Claim

For any finite Conway two-cover atlas, communication compatibility is
equivalent to explicit assignment data choosing one ownership block for every
communication block and proving that it supports the whole block.

The canonical mismatch has no such assignment.  Both canonical one-sided
repairs have assignments, compatibility, and no selected Conway obstruction.
The Cycle 24 missed-conflict reorg and API-only refactor edits also have no
assignment.

## Lean evidence

- `Formal/AG/Research/SFT/ConwayCommunicationSupportAssignment.lean`
- `CommunicationSupportAssignment`
- `CommunicationSupportAssignment.toCompatibility`
- `CommunicationSupportAssignment.ofCompatibility`
- `communicationCoverCompatible_iff_supportAssignment`
- `canonicalReorgCoverEdit_supportAssignment`
- `canonicalRefactorOwnershipEdit_supportAssignment`
- `CanonicalRepairOperation.supportAssignment`
- `CanonicalRepairOperation.compatible_of_supportAssignment`
- `mismatchedAtlas_noCommunicationSupportAssignment`
- `partialReorgMissesDbConflict_noCommunicationSupportAssignment`
- `partialRefactorSupportsOnlyApi_noCommunicationSupportAssignment`
- `selectedCommunicationSupportAssignmentPackage`

## Value

This turns the compatible side of the Conway receiver into explicit support
assignment data instead of repeatedly unpacking `forall comm, exists owner`.
It gives the next cycles a stable interface for transition, selector, and
assignment-preservation claims.  Its value is interface closure rather than a
new obstruction phenomenon.

## Boundaries

This is not a canonical assignment theorem.  The compatibility-to-assignment
direction uses choice because compatibility only supplies existence of a
supporting owner for each communication block.  It is not an arbitrary repair
calculus, optimal repair theorem, empirical organizational claim, or sheaf
cohomology statement.
