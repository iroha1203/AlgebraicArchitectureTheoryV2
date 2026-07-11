---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: profile-curvature / certificate-transport / repair-potential / obstruction / minimality / quality-surface
expected_base_score: 84
expected_evidence_multiplier: 2.0
expected_final_score: 168
evidence_stage: proved-in-research
rival_advantage: ADL / conformance surfaces can compare repair/refinement views, but this candidate records path-indexed branch exchange obligations hidden by the same visible/local projection and component union.
origin: G1-cycle70
tags: [quality-surface, cech, basis-exchange, repair-refinement, branch-transversal]
created: 2026-06-21
cycle: 70
lean: research/lean/ResearchLean/QualitySurface/CurvatureBasisExchange.lean
genius_potential: no
genius_target: none
genius_support_role: none
---

# Curvature basis exchange for repair/refinement exchange cells

## 主張

In a selected finite repair/refinement exchange cell, the coarse path and
refined path carry exact Cech overlap bases.  The exchange datum is not only
the component union of those bases, but the path-indexed branch obligation:
which branch belongs to the coarse side and which branch belongs to the
refined side.  Under component-complete declared repair, common clearance of
the exchange cell is equivalent to hitting every path-indexed exchange branch.

The selected witness uses the coarse trace basis and the refined
trace / repair-frontier basis.  A visible component-union projection forgets
the path index and cannot distinguish the selected exchange closure from a
coarser paired visible branch.  The trace-only repair support can hit the
paired visible branch, but it misses the refined repair-frontier exchange
branch and therefore fails the protected exchange closure.

This is a selected finite theorem package about Cech overlap bases,
path-indexed branch incidence, and declared repair predicates.  It is not a
global matroid basis-exchange theorem, a canonical atlas-refinement theorem,
runtime repair synthesis, source extraction completeness, ArchMap correctness,
arbitrary route enumeration, global sheaf completeness, or whole-codebase
quality.

## 候補種別

`unification`: Cycle 67 Cech curvature, Cycle 68 repair/refinement exchange,
and Cycle 69 antichain branch-transversal nonfaithfulness are compressed into
one path-indexed basis-exchange calculus.

## 依拠

- `research/lean/ResearchLean/QualitySurface/RepairTransportCechCommutatorCurvature.lean`
- `research/lean/ResearchLean/QualitySurface/RepairBasinExchangeObstruction.lean`
- `research/lean/ResearchLean/QualitySurface/AntichainOverlapBasisTransversal.lean`
- Cycle 67 selected repair/transport Cech commutator curvature.
- Cycle 68 selected repair-basin exchange obstruction.
- Cycle 69 antichain Cech overlap basis and transversal exactness.

## 非自明性

The result is not just the union of two component bases.  The protected data is
a path-indexed branch family.  The refined repair-frontier branch is a distinct
exchange obligation even though the visible component-union projection only
sees `{trace, repairFrontier}`.

This prevents a common collapse: treating a repair/refinement exchange cell as
if the only relevant data were the set of components that appear somewhere in
the cell.  The theorem instead distinguishes visible union, path-indexed
branch incidence, and declared repair transversality.

## 数学的興味

This gives a finite hypergraph-style basis exchange object without claiming a
full matroid theory.  Profile curvature is read as a path-indexed obstruction
in the exchange closure: clearing the exchange requires hitting the branches
that appear on the relevant paths, not merely hitting the coarse visible
component set.

## GOAL への前進

This advances the curvature-basis-exchange frontier and gives the Quality
Surface a reusable finite criterion for repair/refinement exchange cells.

## ライバルに対する有効性

ADL, conformance tools, and dashboards can show two repair/refinement views and
their component sets.  They generally do not provide a theorem-level condition
stating which path-indexed protected branches must be hit for common declared
clearance.  This candidate makes the loss of path-indexed exchange data
Lean-checkable.

## SCORE 見込み

- `score_reason`: the Lean theorem package unifies the last three Cech/repair cycles and directly addresses curvature basis exchange, while staying inside the selected finite boundary.
- `dullness_risk`: controlled.  The Lean statements keep `ExchangeSide × BridgeComponent` in the protected branch type, prove common clearance iff exchange-branch hitting, and prove visible-union nonfaithfulness.
- `proof_or_evidence_plan`: completed in `research/lean/ResearchLean/QualitySurface/CurvatureBasisExchange.lean`.

## Lean evidence

Lean proves:

- `ExchangeSide`: coarse and refined path indices.
- `ExchangeBranchSupport`: a predicate on `(ExchangeSide × BridgeComponent)`.
- `liftBranchToExchangeSide`: lift a branch into one side of the exchange cell.
- `selectedBasisExchangeFamily`: the selected path-indexed coarse trace branch and refined trace / repair-frontier branches.
- `collapsedVisibleExchangeFamily`: a coarser visible branch family with the same component-union projection.
- `ExchangeBranchRepairTransversal`: a declared repair support hits every selected exchange branch.
- `coarseTrace_antichainCechOverlapBasis` and `refinedTwoSingleton_antichainCechOverlapBasis`: coarse and refined path branches are grounded in exact selected Cech overlap bases.
- `selectedBasisExchange_exact`: the side-wise exact branch bases are packaged together.
- `selectedBasisExchangeFamily_sideGrounded`: every selected exchange branch is the side lift of a branch grounded on the coarse or refined exact basis.
- `commonClearance_iff_hits_selectedBasisExchange`: component-complete common clearance iff hitting every selected exchange branch.
- `selected_collapsed_same_visibleUnion`: selected and collapsed families have the same visible component-union projection.
- `traceOnly_hits_collapsedVisibleExchange`: the trace-only plan hits the collapsed visible branch.
- `traceOnly_misses_refinedRepairFrontierExchangeBranch` and `traceOnly_refinedRepairFrontierExchange_residual`: the trace-only plan misses the refined repair-frontier exchange branch, leaving residual exchange-branch support.
- `traceOnly_not_hits_selectedBasisExchange`: the trace-only plan is not a transversal for the selected path-indexed family.
- `traceOnly_fails_commonExchangeClearance`: trace-only support fails common clearance of the selected exchange cell.
- `sameVisibleUnion_not_faithful_to_basisExchange`: visible component union cannot recover path-indexed branch-transversal class.
- `curvatureBasisExchange_package`: exactness, exchange-branch hitting, trace-only failure, and nonfaithfulness.

Local checks:

- `lake env lean research/lean/ResearchLean/QualitySurface/CurvatureBasisExchange.lean`: pass.
- `lake build ResearchLean`: pass.
- `#print axioms`: `selectedBasisExchangeFamily_sideGrounded`, `selected_collapsed_same_visibleUnion`, `traceOnly_hits_collapsedVisibleExchange`, `traceOnly_misses_refinedRepairFrontierExchangeBranch`, `traceOnly_refinedRepairFrontierExchange_residual`, `traceOnly_not_hits_selectedBasisExchange`, and `sameVisibleUnion_not_faithful_to_basisExchange` are axiom-free.  Cech grounding, common-clearance, trace-only common-clearance failure, and the package use only standard `propext` inherited from existing Cech predicate-equality evidence.  No `sorryAx`, custom axiom, `Classical.choice`, `Quot.sound`, or `unsafe` was reported in the new core evidence.

## 可視 projection

The visible projection forgets `ExchangeSide` and remembers only the component
union that appears in some exchange branch.

## protected_structure

The protected structure is the path-indexed exchange branch family: a trace
branch on the coarse side, and trace plus repair-frontier branches on the
refined side.

## exactness_or_minimality_claim

Exactness means that the selected exchange branches are grounded in the exact
coarse and refined Cech overlap bases, and component-complete common clearance
is equivalent to hitting those selected exchange branches.  This cycle does
not claim global least exchange closure or matroid basis exchange.

## nonfaithfulness_or_failure_mode

The selected exchange family and a coarser collapsed visible branch family
have the same visible component union.  The trace-only support hits the
collapsed visible branch but misses the selected refined repair-frontier
exchange branch.

## previous_cycle_delta

Cycle 69 showed fixed-cover visible-union nonfaithfulness for antichain branch
families.  This cycle moves the same phenomenon into the repair/refinement
exchange cell: the forgotten datum is now path-indexed branch incidence.

## 審判メモ

- 厳密性: accept / base 84 / genius no.  Selected finite theorem package として進める。`ExchangeSide × BridgeComponent` が theorem の主対象に残る限り、component union の名前替えではない。
- 研究価値: accept / base 90 / genius no.  Cycle 67 Cech curvature、Cycle 68 repair/refinement exchange、Cycle 69 branch-transversal nonfaithfulness を path-indexed exchange-branch calculus に圧縮する。
- repo 全体価値: accept / base 88 / genius no.  Lean / paper / future projection-rule surface に価値があるが、project-level bridge ではなく phase-continuation theorem package。
- ライバル比較: accept / base 88 / genius no.  ADL / conformance surface が持つ visible views や component sets では決まらない path-indexed branch-transversal class を Lean-checkable にする。
- G3 形式化品質監査: pass.  `ExchangeSide` は protected theorem statements に残り、global matroid exchange、canonical refinement、runtime synthesis、tooling correctness などを主張していない。
- G4 SCORE 監査: confirm / base 84 / multiplier 2.0 / penalty 0 / final +168.  Total は 9330 から 9498 へ進む。G2 全員が genius no のため genius scoring は not-applicable。

## 関連

- `g-aat-quality-surface-01-repair-transport-cech-commutator-curvature.md`
- `g-aat-quality-surface-01-repair-basin-exchange-obstruction.md`
- `g-aat-quality-surface-01-antichain-overlap-basis-transversal-exactness.md`

## 進捗ログ

- 2026-06-21: Cycle 70 の picked 候補として作成。G2 へ進める。
- 2026-06-21: `CurvatureBasisExchange.lean` を追加し、selected finite path-indexed basis-exchange theorem package として Lean 検証済みに同期。
- 2026-06-21: G4 SCORE 監査で final +168 を confirm。
