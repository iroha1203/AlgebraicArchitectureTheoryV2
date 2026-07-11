---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: obstruction / minimality / repair-potential / certificate-transport / quality-surface / computability
expected_base_score: 84
expected_evidence_multiplier: 2.0
expected_final_score: 168
evidence_stage: proved-in-research
rival_advantage: ADL / conformance surfaces can show mismatch component sets, but this candidate records non-singleton branch incidence and repair-transversal classes hidden by the same visible union.
origin: G1-cycle69
tags: [quality-surface, cech, overlap-basis, antichain, repair-transversal]
created: 2026-06-21
cycle: 69
genius_potential: no
genius_target: none
genius_support_role: none
---

# Antichain Cech overlap basis and transversal exactness

## 主張

Finite Cech overlap support can be read not only as an exact component basis,
but as a selected antichain of nonempty protected support branches whose union
generates that component basis.  The branch layer is not identified with the
existing component-level `HandoffCechRepairObligation`; it has its own declared
branch-clearance and residual-branch predicates.  A missed selected branch
survives as residual branch support, while in a branch-complete declared repair
regime, clearing every branch is equivalent to the repair support hitting every
selected branch.  Deleting a branch, or replacing a two-branch incidence basis
by another basis with the same visible component-union projection, can change
the repair-transversal class.  Thus non-singleton incidence is protected
Quality Surface data, not merely a visible component bitset.

This is a selected finite theorem package about `BridgeComponent` support
branches grounded by an exact selected Cech overlap component basis.  It does
not assert runtime repair synthesis, canonical global minimality, source
extraction completeness, ArchMap correctness, arbitrary route enumeration,
global sheaf completeness, or whole-codebase quality.

## 候補種別

`unification`: overlap basis exactness, selected branch-deletion failure,
residual branch support, and repair-transversal duality are placed in one
finite antichain calculus.

## 依拠

- `research/lean/ResearchLean/QualitySurface/HandoffRepairTransversal.lean`
- `research/lean/ResearchLean/QualitySurface/HandoffCechExactness.lean`
- `research/lean/ResearchLean/QualitySurface/OverlapObstructionBasis.lean`
- Cycle 64 component-support repair transversal.
- Cycle 66 finite overlap obstruction basis and repair-transversal duality.
- Cycle 68 selected repair-basin exchange obstruction.

## 非自明性

Cycle 66 handles exact overlap bases as predicates on components and repairs
them through `HandoffCechRepairObligation`, a component-level clearance
predicate.  This candidate adds a separate branch layer generated over such an
exact component basis and separates three levels that a visible component
bitset conflates:

1. the union of all components that appear in some branch,
2. the branch incidence relation itself, and
3. the repair supports that hit every branch.

The main nonfaithfulness claim fixes the visible projection to the component
union only: two branch families can have the same visible union while requiring
different protected repair transversals.

## 数学的興味

This imports hypergraph / antichain transversal duality into the Cech overlap
obstruction calculus without claiming a full matroid theory.  It makes repair
necessity depend on incidence, not just on component support membership.

## GOAL への前進

This advances the non-singleton overlap basis frontier and turns repair
potential into a branch-incidence invariant of the Quality Surface.

## ライバルに対する有効性

ADL, architecture conformance checkers, and metric dashboards can surface
component sets or mismatch counts.  They do not usually retain whether the same
component union came from one two-component branch or from two singleton
branches, nor whether the declared repair support hits each branch.  This
candidate makes that loss a Lean-checkable finite theorem.

## SCORE 見込み

- `score_reason`: non-singleton branch incidence plus residual-branch and repair-transversal nonfaithfulness directly addresses the current frontier and gives a new repair-potential invariant, but remains a selected finite branch calculus rather than a global Cech theorem.
- `dullness_risk`: If the result only defines a hypergraph and restates hitting, it is dull.  The Lean evidence must include exact branch generation, branch deletion failure, and same-visible-union / different-transversal witness.
- `proof_or_evidence_plan`: Research-side Lean evidence now defines finite branch predicates grounded by a selected exact overlap component basis, residual branch semantics, `AntichainCechOverlapBasis`, branch transversal, branch-complete plans, selected two-singleton and one-pair bases, drop-branch failure, same union nonfaithfulness, and a theorem package.
- `actual_evidence`: Implemented in `research/lean/ResearchLean/QualitySurface/AntichainOverlapBasisTransversal.lean` and imported by `research/lean/ResearchLean.lean`.

## CS / SWE への帰結

A repair view that only says "components trace and repairFrontier are involved"
may hide whether a single repair action can cover one branch or must satisfy
two separate branch obligations.  This gives a finite criterion for why a
visible component set is insufficient as a repair dashboard.

## Lean evidence

Lean evidence is fixed in
`research/lean/ResearchLean/QualitySurface/AntichainOverlapBasisTransversal.lean`.
The main declarations are:

- `BranchSupport`: a predicate on `BridgeComponent`.
- `BranchNonempty` and `BranchSubsupport`.
- `BranchFamilyUnionGenerates`: branch union generates a selected component basis.
- `AntichainCechOverlapBasis`: an exact selected component overlap basis together with nonempty antichain branches whose union generates it.
- `DeclaredResidualBranchSupport`: if no touched component lies in a selected branch, that branch remains as declared residual support.
- `DeclaredBranchRepairClears`: branch-level clearance, intentionally separate from the existing component-level `HandoffCechRepairObligation`.
- `BranchRepairTransversal`: a repair support hits every selected branch.
- `BranchCompleteRepairPlan`: if a touched component lies in a selected branch, the declared branch is clear.
- `missedBranch_survives_as_residual`: a selected missed branch remains as residual branch support.
- `declaredBranchClearance_iff_hits_antichainOverlapBasis`: branch-complete plans clear all branches iff their support hits every branch.
- `twoSingleton_antichainCechOverlapBasis` and `singlePair_antichainCechOverlapBasis`: selected finite branch bases with the same visible union.
- `dropTraceBranch_breaks_antichainGeneration`: deleting the selected trace branch breaks branch generation.
- `sameVisibleUnion_not_faithful_to_branchTransversal`: the same visible union can carry different protected transversal requirements.
- `antichainOverlapBasisTransversal_package`: exactness, branch residual support, branch deletion, and nonfaithfulness.

Actual declaration names:

- `AntichainCechOverlapBasis`
- `missedBranch_survives_as_residual`
- `declaredBranchClearance_iff_hits_antichainOverlapBasis`
- `twoSingleton_antichainCechOverlapBasis`
- `singlePair_antichainCechOverlapBasis`
- `dropTraceBranch_breaks_antichainGeneration`
- `twoSingleton_singlePair_same_visibleUnion`
- `traceOnly_repairFrontierBranch_residual`
- `traceOnly_not_hits_twoSingletonBranch`
- `traceOnly_branchClearance_singlePair_not_componentCechObligation`
- `sameVisibleUnion_not_faithful_to_branchTransversal`
- `antichainOverlapBasisTransversal_package`

Build evidence:

- `lake env lean research/lean/ResearchLean/QualitySurface/AntichainOverlapBasisTransversal.lean`: pass.
- `lake build ResearchLean`: pass.
- `lake build`: pass, with only pre-existing linter warnings in `Formal/Arch/Extension/FeatureExtensionExamples.lean`.

Axiom audit:

- No axioms: `AntichainCechOverlapBasis`, `missedBranch_survives_as_residual`,
  `declaredBranchClearance_iff_hits_antichainOverlapBasis`,
  `dropTraceBranch_breaks_antichainGeneration`,
  `twoSingleton_singlePair_same_visibleUnion`,
  `traceOnly_repairFrontierBranch_residual`,
  `traceOnly_not_hits_twoSingletonBranch`,
  `sameVisibleUnion_not_faithful_to_branchTransversal`.
- `propext`: `twoSingleton_antichainCechOverlapBasis`,
  `singlePair_antichainCechOverlapBasis`,
  `traceOnly_branchClearance_singlePair_not_componentCechObligation`,
  `antichainOverlapBasisTransversal_package`.
- No `sorryAx`, `Classical.choice`, `Quot.sound`, custom axiom, or `unsafe` in reported declarations.

The remaining `propext` comes through existing selected Cech overlap/refinement
predicate-equality evidence such as `curvedPath_overlapBasis` and
`traceOnlyRepairPlan_fails_refinedBasin`.  The new branch-layer residual,
deletion, and same-visible-union nonfaithfulness witnesses are axiom-free.

## 可視 projection

The visible projection is only the union of components appearing in any branch.
It deliberately forgets branch count and incidence.

## protected_structure

The protected structure is the branch family: whether trace and repairFrontier
appear as two singleton branches or one paired branch changes transversal
requirements.

## exactness_or_minimality_claim

Exactness means the branch union generates the selected exact Cech overlap
component basis and each selected branch is nonempty.  This cycle proves branch
deletion failure for the selected trace branch witness, not global all-branch
indispensability or a matroid minimality theorem.

## nonfaithfulness_or_failure_mode

The same visible union `{trace, repairFrontier}` can have distinct branch
transversal classes: hitting one paired branch differs from hitting two
singleton branches.

## previous_cycle_delta

Cycle 68 showed that a selected trace-only repair plan can clear a coarse basin
and fail a refined basin.  This cycle explains a more structural reason:
branch-level repair obligation can depend on incidence among non-singleton
overlap basis branches, not just on the visible component union or the existing
component-level clearance predicate.

## 審判メモ

- 厳密性: A は初回 `revise`。任意 hypergraph の hitting lemma に落とさず、exact selected Cech overlap component basis への union-generation、residual branch semantics、component-level clearance との非同一性、projection を component-union に固定した nonfaithfulness を Lean evidence に入れるようカードを修正した。
- 厳密性再審判: A は `accept`、base 82、genius no。`AntichainCechOverlapBasis` と component-basis grounding により任意 hypergraph 化から離れたと判定。ただし `BranchCompleteRepairPlan` が tautological に見えないよう、G4 では selected witness と residual branch semantics を重視する。
- 研究価値: B は `accept`、base 88、genius no。
- repo 全体価値: C は `accept`、base 84、genius no。arbitrary hypergraph 化のリスクにより expected base を 84 に下げた。
- ライバル比較: D は `accept`、base 88、genius no。

## G3 監査メモ

- 公理検査: pass。build は pass。報告対象の core branch/residual/nonfaithfulness theorem は axiom-free。Cech component-basis grounding と component-level obligation 分離を含む package は既存 Cech evidence 由来の `propext` のみ。
- Lean 形式化品質監査: pass。`AntichainCechOverlapBasis` は `OverlapObstructionBasis` に grounded されており、same component-union / different branch-transversal class、drop-trace failure、residual branch support、component-level `HandoffCechRepairObligation` との分離を表現している。
- 残る unchecked: global all-branch deletion minimality、global Cech / sheaf completeness、runtime synthesis、whole-codebase quality、external ADL literature comparison。

## 関連

- `g-aat-quality-surface-01-overlap-obstruction-basis.md`
- `g-aat-quality-surface-01-repair-basin-exchange-obstruction.md`

## 進捗ログ

- 2026-06-21: Cycle 69 の picked 候補として作成。G2 へ進める。
- 2026-06-21: G2 A の revise を受け、branch-clearance と component-level `HandoffCechRepairObligation` の分離、residual branch semantics、exact overlap component basis への grounding、visible projection の固定を明記。
- 2026-06-21: Lean evidence を追加し、`lake build ResearchLean` と full `lake build` を通過。G3 公理検査・形式化品質監査はいずれも pass。
