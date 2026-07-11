---
status: implemented
goal: G-sft-conway-01
cycle: 22
candidate_type: bridge-obstruction
capability_category:
  - finite-incidence-receiver
  - conway-obstruction
  - local-global-boundary
  - finite-witness
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
rival_advantage: Existing review, CODEOWNERS, and org-network tools can report owner mismatch; this package records the selected obstruction as a Lean-checked finite owner/fork incidence receiver with a local/global section gap.
genius_potential: no
target_theorem: not-applicable
claim_boundary:
  - selected finite owner/fork incidence receiver only
  - no true sheaf H1 theorem
  - no arbitrary-cover naturality
  - no canonical selector
  - no real organizational causality
---

# G-sft-conway-01 Cycle 22: owner-uniform incidence receiver

## Candidate

Define an independent finite incidence receiver for the owner-uniform Conway
obstruction.

- vertices are owners;
- edges are selected fork indices;
- incidence means that an owner supports the communication block selected by
  a fork edge;
- a global section is one owner incident to every selected fork edge.

The receiver is independent of the Cycle 21 `C0` wrapper: it is not a boundary
generator record.  It is a finite owner/fork incidence graph whose global
sections re-express the existing owner-uniform support criterion and compare it
to the selected Conway class.

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformIncidenceReceiver.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceVertex`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceEdge`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceIncident`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceLocallySupported`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceLocalGlobalGap`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformIncidenceGlobalSection_nonempty_iff_support`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformConwayClass_eq_zero_iff_incidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_incidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_incidenceLocallySupported`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_no_incidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_incidenceLocalGlobalGap`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_conwayClass_nonzero_iff_no_incidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerUniformIncidenceReceiverPackage`

## Claim boundary

This is a selected finite incidence receiver.  It does not assert true sheaf
cohomology, arbitrary-cover naturality, arbitrary-site Cech cohomology,
universal quotient properties, a canonical owner selector, or real-world
organizational causality.  It only fixes the owner/fork incidence data and the
global-section criterion that matches selected owner-uniform support and zero
of the selected Conway class.
