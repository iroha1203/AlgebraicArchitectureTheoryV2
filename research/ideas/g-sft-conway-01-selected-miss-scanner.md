---
goal: G-sft-conway-01
cycle: 33
candidate_type: selector
evidence_stage: proved-in-research
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
categories:
  - conway-obstruction
  - selected-conflict-set
  - first-miss-scanner
  - miss-selector
---

# Selected miss scanner

## Claim

For the selected reorg/refactor edit shapes, bounded first-miss scanner
predicates are sound and complete for selected miss existence.

Canonical reorg/refactor edits have no first miss.  The existing partial reorg
edit has exactly `platformDb` as first miss, and the existing API-only partial
refactor edit has exactly `db` as first miss.

## Lean evidence

- `Formal/AG/Research/SFT/ConwaySelectedMissScanner.lean`
- `ReorgCoverEditFirstSelectedMiss`
- `reorgFirstSelectedMiss_sound`
- `reorgFirstSelectedMiss_exists_iff_hasSelectedMiss`
- `canonicalReorgCoverEdit_noFirstSelectedMiss`
- `partialReorgMissesDbConflict_firstSelectedMiss_iff`
- `RefactorOwnershipEditFirstSelectedMiss`
- `refactorFirstSelectedMiss_sound`
- `refactorFirstSelectedMiss_exists_iff_hasSelectedMiss`
- `canonicalRefactorOwnershipEdit_noFirstSelectedMiss`
- `partialRefactorSupportsOnlyApi_firstSelectedMiss_iff`
- `selectedMissScannerPackage`

## Value

This turns pointwise selected miss membership into a bounded finite scanner
interface with soundness, completeness, and exact first-miss identities for the
selected partial edits.  It is a better bridge toward diagnostic extraction
than a bare existence theorem.

## Boundaries

This is a selected finite scanner over the Conway two-module vocabulary.  It is
not a runtime extraction algorithm, arbitrary conflict enumeration procedure,
or general repair calculus.
