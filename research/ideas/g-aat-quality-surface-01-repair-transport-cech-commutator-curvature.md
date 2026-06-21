---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: profile-curvature / certificate-transport / obstruction / repair-potential / quality-surface / traceability
expected_base_score: 88
expected_evidence_multiplier: 2.0
expected_final_score: 176
evidence_stage: proved-in-research
rival_advantage: ADL and conformance tools can report route/order or refinement mismatches, but they do not usually package a visible-flat repair/transport commutator as protected Cech overlap support with an exact obstruction basis and repair obligation.
origin: research-loop-cycle-67
tags: [quality-surface, handoff, cech, overlap, commutator-curvature, profile-curvature]
created: 2026-06-21
cycle: 67
lean: proved-in-research
---

# Repair-transport Cech commutator curvature of overlap support

## 主張

A selected finite repair-transport Cech commutator cell can be read as Cech
overlap curvature.  The cell has two typed paths: a flat path and a curved
path.  They share the same visible/local commutator projection, but the flat
path has empty generated overlap support while the curved path has an exact
nonempty overlap basis.  The curved path therefore fails global handoff
exactness under local exactness, and component-complete declared repair clears
it exactly when it hits the curvature basis.  The claim is relative to selected
finite source-ref handoff covers, existing finite repair/transport commutator
witnesses, finite `BridgeComponent` vocabulary, and declared component-level
repair predicates.

It does not assert canonical global curvature, runtime repair synthesis,
source extraction completeness, ArchMap correctness, arbitrary route
enumeration, global sheaf completeness, or whole-codebase quality.

## 候補種別

`bridge`

## 依拠

- `Formal/AG/Research/QualitySurface/HandoffCechExactness.lean`
- `Formal/AG/Research/QualitySurface/OverlapObstructionBasis.lean`
- `Formal/AG/Research/QualitySurface/LawfulRepairTransportCommutator.lean`
- `Formal/AG/Research/QualitySurface/FrontierLocalRepairTransportCommutator.lean`
- `Formal/AG/Research/QualitySurface/LossAwareCommutatorAtlas.lean`
- Cycle 62 repair/transport handoff obstruction bridge
- Cycle 65 Cech overlap exactness
- Cycle 66 overlap obstruction basis / repair-transversal duality

## 非自明性

Cycle 62 relates repair/transport endpoint order to handoff obstruction.
Cycle 65-66 package Cech overlap support and selected overlap bases.  This
candidate asks for the common geometry: one typed finite commutator cell whose
two Cech paths share visible/local projection but differ in protected overlap
support.  It is not just another component deletion witness; the theorem must
connect commutator curvature, local-to-global exactness failure, exact overlap
basis, and lossful visible projection in one package.

## 数学的興味

The result reads profile curvature as local-to-global overlap obstruction.
Curvature is not a scalar bend or endpoint mismatch; it is a protected
component-support class carried by the overlap cocycle of a selected finite
commutator cell.

## GOAL への前進

It advances the `profile-curvature`, `certificate-transport`, `obstruction`,
and `repair-potential` frontiers at once.  Quality Surface gains a theorem
showing how repair/transport order can be visible-flat while still carrying a
hidden overlap basis and declared repair obligation.

## ライバルに対する有効性

ADL / conformance checkers can display route/order mismatches or refined
conformance differences.  This theorem package records the protected basis
that a visible-flat commutator hides, and ties it to Cech global exactness and
component-complete declared repair hitting.  That gives AAT a certificate
geometry not reducible to a mismatch list or scalar dashboard.

## SCORE 見込み

- `score_reason`: High bridge value.  The candidate connects prior
  repair/transport commutator evidence with the latest Cech overlap basis
  calculus, creating a profile-curvature reading of protected overlap support.
- `dullness_risk`: Medium.  It would be weak if it merely renamed an existing
  visible commutator witness.  G3 must include a named curvature predicate,
  visible/local projection equality from the same typed cell, protected overlap
  basis discrepancy, and global exactness failure under local exactness.
- `proof_or_evidence_plan`: Define a finite repair-transport Cech commutator
  cell with a flat Cech path and a curved Cech path as fields of the same
  object.  Prove that their visible/local projections agree, while the curved
  path has exact nonempty overlap basis and the flat path has empty generated
  support.  Use Cycle 65 exactness and Cycle 66 basis duality to turn nonempty
  overlap basis into global exactness failure and repair obligation.
- `G2_actual_score_band`: A requested revise with base 80; B accepted base 88;
  C accepted base 90; D accepted base 90.  Revise requirement: choose one
  commutator regime, type the cell, construct flat and curved Cech covers from
  that same cell, and prove support-level basis discrepancy instead of
  juxtaposing unrelated Cycle 62 and Cycle 65-66 facts.
- `G2_after_revise`: A accepted base 84, genius no; B accepted base 88,
  genius no; C accepted base 90, genius no; D accepted base 90, genius no.
- `G3_evidence`: Lean proof in
  `Formal/AG/Research/QualitySurface/RepairTransportCechCommutatorCurvature.lean`.
  `lake env lean Formal/AG/Research/QualitySurface/RepairTransportCechCommutatorCurvature.lean`
  and `lake build FormalAGResearch` passed.  Full `lake build` also passed;
  the only warnings were pre-existing linter warnings in
  `Formal/Arch/Extension/FeatureExtensionExamples.lean`.
- `G3_synced_score_expectation`: expected base lowered to 88 before G4.  The
  post-revise G2 band is A 84 / B 88 / C 90 / D 90, and 88 reflects the
  conservative midpoint while preserving the x2.0 Lean evidence multiplier for
  SCORE audit.

## CS / SWE への帰結

A viewer or report can distinguish "the same visible commutator surface" from
"the same protected repair obligation."  A visible-flat repair/transport
square may still carry a hidden overlap basis that determines which declared
repair support must be touched.

## 証明・根拠の見込み

Lean declarations fixed in G3:

- `RepairTransportCechCommutatorCell`
- `CommutatorCechCurvature`
- `repairTransport_paths_same_visibleLocal`
- `flatPath_overlapBasis_empty`
- `curvedPath_overlapBasis_nonempty`
- `curvedPath_notGlobalExact_of_local`
- `curvedPath_declaredClearance_iff_hitsCurvatureBasis`
- `visibleRepairTransport_not_faithful_to_cechCurvature`
- `repairTransportCechCommutatorCurvature_package`

Evidence summary: the selected cell has `flatPath` and `curvedPath` fields.
The flat path has empty overlap support and an exact empty basis.  The curved
path has an exact nonempty basis
`repairTransportCurvatureBasis = {trace, repairFrontier}`, fails global handoff
exactness under local exactness, and component-complete declared repair clears
it iff the repair support hits that basis.  `CommutatorCechCurvature` itself
includes the repair-clearing iff, so the final package is stated through
`selectedRepairTransportCechCommutatorCell.flatPath` and `.curvedPath`.

G3 axiom summary: `RepairTransportCechCommutatorCell` and
`CommutatorCechCurvature` are axiom-free.  `curvedPath_overlapBasis`,
`curvedPath_overlapBasis_nonempty`, `curvedPath_notGlobalExact_of_local`, and
`curvedPath_declaredClearance_iff_hitsCurvatureBasis` use standard `propext`.
`repairTransport_paths_same_visibleLocal`, `flatPath_overlapBasis_empty`,
`selectedRepairTransportCechCommutator_hasCurvature`,
`visibleRepairTransport_not_faithful_to_cechCurvature`, and
`repairTransportCechCommutatorCurvature_package` use standard `propext` plus
existing `Quot.sound`.  No `sorryAx`, custom `axiom`, `admit`, or `unsafe`
appears.  Independent G3 axiom check passed, and independent Lean
formalization-quality audit passed after the package was revised to use selected
cell fields.

## 追加メタデータ

```text
planned_theorem_names:
  RepairTransportCechCommutatorCell
  CommutatorCechCurvature
  repairTransport_paths_same_visibleLocal
  flatPath_overlapBasis_empty
  curvedPath_overlapBasis_nonempty
  curvedPath_notGlobalExact_of_local
  curvedPath_declaredClearance_iff_hitsCurvatureBasis
  visibleRepairTransport_not_faithful_to_cechCurvature
  repairTransportCechCommutatorCurvature_package
visible_projection:
  local chart exactness plus visible repair/transport commutator surface
protected_structure:
  Cech overlap cocycle support, selected overlap obstruction basis, source-ref handoff component identity, declared repair support
exactness_or_minimality_claim:
  the same typed repair-transport Cech commutator cell supplies both paths; flat path has empty generated overlap support; curved path has exact nonempty basis and fails global exactness under local exactness; component-complete declared repair clearance is equivalent to hitting the curvature basis; the final package is stated through the selected cell fields
nonfaithfulness_or_failure_mode:
  visible/local commutator equality is not faithful to protected Cech overlap curvature or repair obligation
previous_cycle_delta:
  Cycle 65-66 gave overlap exactness and basis duality for selected covers; this cycle connects them to repair/transport Cech commutator curvature.
genius_potential:
  no
genius_target:
  none
genius_support_role:
  none
```

## 審判メモ

- 厳密性:
  - initial revise required: choose repair-transport Cech commutator vocabulary, type the cell, and make flat/curved covers fields of the same object; avoid juxtaposing unrelated witnesses or claiming distinct exact bases on one cover.
  - after revise: accept, base 84, genius no.  G3 must instantiate a non-vacuous concrete cell rather than store desired conclusions as assumptions.
- 研究価値:
  - accept, base 88, genius no. High compression from commutator flatness, Cech local-to-global failure, exact overlap basis, and repair-transversal semantics.
- repo 全体価値:
  - accept, base 90, genius no. Strong AAT/Lean/Research and future projection-rule value.
- ライバル比較:
  - accept, base 90, genius no. Moves rival comparison from visible conformance to protected support/basis/repair-transversal faithfulness.

## 関連

- `research/ideas/g-aat-quality-surface-01-overlap-obstruction-basis-repair-duality.md`
- `research/ideas/g-aat-quality-surface-01-finite-cech-handoff-obstruction-exactness.md`
- `research/ideas/g-aat-quality-surface-01-repair-transport-handoff-obstruction-bridge.md`
- `research/reports/G-aat-quality-surface-01.md`

## 進捗ログ

- 2026-06-21: Cycle 67 G1 候補 pool から作成。
- 2026-06-21: G2 A の revise を受け、`law-refinement / repair-transport` の曖昧さを `repair-transport Cech commutator cell` に絞り、flat / curved paths が同じ typed cell から出る要件を明記。
- 2026-06-21: G2 四審判が accept。G3 で Lean proof を追加し、形式化品質監査の revise を受けて final package を selected cell fields 経由へ修正。G3 axiom check と formalization-quality audit が pass。
