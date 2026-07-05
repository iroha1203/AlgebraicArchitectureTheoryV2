---
status: implemented
goal: G-sft-conway-01
cycle: 24
candidate_type: obstruction
capability_category:
  - reorg-refactor-duality
  - negative-witness
  - finite-operation
  - conway-obstruction
expected_base_score: 40
expected_evidence_multiplier: 2.0
expected_penalty: 10
expected_final_score: 70
evidence_stage: proved-in-research
rival_advantage: Existing tools can suggest partial repair narratives; this package proves a finite missed-conflict witness for the canonical operation criteria.
genius_potential: no
target_theorem: not-applicable
claim_boundary:
  - canonical finite Conway mismatch only
  - reorg negative witness has actual Conway obstruction
  - refactor negative witness is hitting/compatibility failure only
  - missed-conflict witness is canonical, not arbitrary
  - no arbitrary operation calculus
  - no real organizational causality
---

# G-sft-conway-01 Cycle 24: reorg/refactor negative witnesses

## Candidate

Add finite negative witnesses for the Cycle 23 canonical operation-shaped
criteria.

- `partialReorgMissesDbConflict` leaves the platform communication block
  covering both API and DB.
- It misses `ReorgCoverEditHitsEveryConflict`, is not post-edit compatible,
  and still has a selected Conway obstruction.
- `partialRefactorSupportsOnlyApi` supports API but not DB in the Cycle 23
  single-owner refactor shape.
- It misses `RefactorOwnershipEditHitsEveryConflict` and is not post-edit
  compatible.

## Lean evidence

- `Formal/AG/Research/SFT/ConwayReorgRefactorNegativeWitness.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.partialReorgMissesDbConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_not_hitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_not_compatible`
- `Formal.AG.Research.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_nonzeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi`
- `Formal.AG.Research.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_not_hitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_not_compatible`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedReorgRefactorNegativeWitnessPackage`

## Claim boundary

This is a selected finite negative witness package for the canonical operation
shapes.  The reorg-side partial edit leaves an actual Conway obstruction.  The
refactor-side partial edit is only a hitting/compatibility failure because the
Cycle 23 refactor shape uses a single owner index and cannot witness two
distinct owners.  This does not claim arbitrary operation calculus, optimal
repair, or real organizational causality.
