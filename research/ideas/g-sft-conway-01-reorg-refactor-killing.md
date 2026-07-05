---
status: implemented
goal: G-sft-conway-01
cycle: 23
candidate_type: closure
capability_category:
  - reorg-refactor-duality
  - obstruction-killing
  - finite-operation
  - conway-obstruction
expected_base_score: 50
expected_evidence_multiplier: 2.0
expected_penalty: 10
expected_final_score: 90
evidence_stage: proved-in-research
rival_advantage: Existing org/code tools can suggest reorg or refactor narratives; this package gives Lean-checked finite hitting criteria for the canonical one-sided repairs.
genius_potential: no
target_theorem: not-applicable
claim_boundary:
  - canonical finite Conway mismatch only
  - no real organizational causality
  - no optimal repair theorem
  - no arbitrary-cover naturality
  - no sheaf cohomology claim
---

# G-sft-conway-01 Cycle 23: reorg/refactor obstruction killing

## Candidate

Promote the Cycle 1 repaired examples into finite operation-shaped
compatibility criteria for the canonical mismatch.

- `ReorgCoverEdit` changes the communication cover and keeps split ownership.
- `RefactorOwnershipEdit` keeps all-communication and changes the ownership
  cover.
- Each operation has a concrete canonical `HitsEveryConflict` predicate.
- For each operation type, `HitsEveryConflict` is equivalent to post-edit
  communication compatibility.
- The canonical reorg and refactor edits satisfy their hitting criteria and
  kill the selected Conway obstruction.

## Lean evidence

- `Formal/AG/Research/SFT/ConwayReorgRefactorKilling.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ReorgCoverEdit`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ReorgCoverEditHitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ReorgCoverEdit.postCompatible_iff_hitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ReorgCoverEdit.killsConwayObstruction_of_hitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.canonicalReorgCoverEdit`
- `Formal.AG.Research.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_hitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_killsConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.RefactorOwnershipEdit`
- `Formal.AG.Research.SFT.ConwayTwoTopology.RefactorOwnershipEditHitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.RefactorOwnershipEdit.postCompatible_iff_hitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.RefactorOwnershipEdit.killsConwayObstruction_of_hitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit`
- `Formal.AG.Research.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_hitsEveryConflict`
- `Formal.AG.Research.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_killsConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CanonicalRepairOperation`
- `Formal.AG.Research.SFT.ConwayTwoTopology.canonicalRepairOperation_killsConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedReorgRefactorKillingPackage`

## Claim boundary

This is a selected finite operation-shaped criterion for the canonical Conway
mismatch.
It does not assert real-world organizational causality, an optimal repair
theorem, arbitrary-cover naturality, or a sheaf/cohomology theorem.  The hitting
criteria are finite compatibility criteria for the two canonical one-sided
operation shapes.
