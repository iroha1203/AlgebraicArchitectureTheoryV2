---
status: picked
goal: G-aat-quality-surface-01
candidate_type: computability
capability_category: computability / repair-potential / certificate-transport / obstruction / quality-surface
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checkers can report visible repair failures, but this candidate computes the selected path-indexed residual branch and deletion/restoration witness inside certificate geometry.
origin: G1-cycle72
tags: [quality-surface, computability, branch-transversal, residual, repair]
created: 2026-06-21
cycle: 72
lean: research/lean/ResearchLean/QualitySurface/BranchTransversalScanKernel.lean
genius_potential: no
genius_target: none
genius_support_role: none
---

# Selector-relative branch-transversal scan kernel

## 主張

For the selected finite repair/refinement exchange family, branch-transversal
clearance can be read by a selector-code scan kernel.  The kernel scans a fixed
ordered list of selected path-indexed branch codes against a declared repair
support, returns an `Option` residual code for the first missed branch when one
exists, and proves that the absence of a residual branch is equivalent to
hitting every selected exchange branch.

The selected trace-only witness has a concrete residual: the refined
repair-frontier exchange branch.  Deleting that canonical residual from the
selected finite family restores trace-only transversality.  This is a
selector-relative finite deletion/restoration theorem, not a global minimality
or canonical repair theorem.

The same visible component-union projection that forgets branch incidence
cannot recover the scan kernel residual.  The theorem package must include a
kernel pair: two visible-equivalent finite readings whose scan residuals differ
because one reading keeps the selected path-indexed branch codes and the other
uses the collapsed visible branch.  The theorem package remains inside finite
AAT certificate geometry: it does not assert runtime repair synthesis, source
extraction completeness, ArchMap correctness, arbitrary route enumeration,
global sheaf completeness, or whole-codebase quality.

## 候補種別

`computability`: Cycle 70/71 の branch-transversal nonfaithfulness を、失敗を計算して返す finite scan kernel に変える。

## 依拠

- `research/lean/ResearchLean/QualitySurface/CurvatureBasisExchange.lean`
- `research/lean/ResearchLean/QualitySurface/NaiveRefinementSupportCounterexample.lean`
- Cycle 70 path-indexed curvature basis exchange.
- Cycle 71 selected branch-reflection failure for naive refinement readings.

## 非自明性

This is not the definition of `ExchangeBranchRepairTransversal` unfolded.  It
also is not just the route-slot scan pattern from Cycles 55/56 copied to a new
type.  The new content is that the scan target is the selected
repair/refinement exchange family, the returned object is a protected
path-indexed branch residual, and the visible component-union projection is
proved unable to recover that residual.  The candidate must expose an ordered
computational object:

1. selector codes that enumerate exactly the selected exchange branches,
2. an ordered `Option` first-missed residual selector over those codes,
3. an empty-residual iff theorem for branch transversality,
4. a concrete trace-only residual, and
5. deletion/restoration for the selected finite family,
6. a visible-equivalent kernel pair with different residual behavior.

The point is to turn the no-go examples into a residual-producing kernel that
can be reused by later projection and refinement transport theorems.

## 数学的興味

The repair obligation becomes a finite obstruction scan rather than a bare
proposition.  Obstruction, residual branch, deletion, restoration, and visible
projection loss are represented in one finite certificate object.

## GOAL への前進

This adds a computability layer to atom-supported quality geometry: selected
repair failure is not only detected but localized to a path-indexed residual
branch.

## ライバルに対する有効性

ADL / conformance tools and metric dashboards can report violated constraints
or component-level failures.  They do not, by default, return the selected
path-indexed branch residual whose deletion/restoration explains the repair
obligation inside certificate geometry.  This candidate makes that residual
Lean-checkable.

## SCORE 見込み

- `score_reason`: computability result that converts Cycle 70/71 projection-loss and branch-reflection failures into a residual-producing finite kernel.  G2 strictness reduced the base from 88 to 80 because the repo already has generic ordered scan machinery; the score is carried by the branch-specific selector enumeration, concrete residual, deletion/restoration, and visible-equivalent kernel pair.
- `dullness_risk`: real.  If the evidence only restates `ExchangeBranchRepairTransversal` or merely ports the earlier route-slot scan API, the score should drop.  The Lean proof must include selector-code enumeration, an `Option` first-missed selector, a concrete trace-only residual, deletion/restoration, and a visible-equivalent kernel pair whose residual behavior differs.
- `proof_or_evidence_plan`: completed in `research/lean/ResearchLean/QualitySurface/BranchTransversalScanKernel.lean`.

## CS / SWE への帰結

This provides the mathematical form of a loss-aware repair diagnostic kernel:
an external surface may display a compact view, but the AAT certificate layer
can name the residual protected branch that blocks repair clearance.  Any
tooling use would remain relative to an ArchMap / evidence contract and is not
claimed here.

## 証明・根拠

Lean will reuse the selected exchange branch family from Cycle 70 and the
trace-only witness from Cycle 71.  The proved statements are:

- `SelectedScanBranch`: finite selector codes for the selected exchange branches.
- `selectedScanBranchFamily_complete`: selector codes enumerate exactly the selected basis-exchange family.
- `firstMissedSelectedBranch?`: ordered residual selector.
- `firstMissedSelectedBranch?_none_iff_transversal`: no residual iff selected branch transversality.
- `traceOnly_firstMissedSelectedBranch`: trace-only residual is the refined repair-frontier branch.
- `dropFirstMissed_restores_traceOnlyTransversal`: deleting the residual restores trace-only transversality.
- `collapsedVisible_firstMissedBranch_traceOnly`: the collapsed visible reading has no residual under trace-only repair.
- `visibleEquivalent_residualKernelPair`: selected and collapsed readings have the same visible union but different scan residual behavior.
- `visibleUnion_not_faithful_to_branchScanKernel`: visible union does not determine the scan residual.
- `branchTransversalScanKernel_package`: theorem package.

## Lean evidence

Lean proves:

- `SelectedScanBranch`: selector codes for the selected path-indexed exchange branches.
- `SelectedScanBranch.branch`: interpretation of selector codes as exchange branches.
- `selectedScanOrder`: the finite selected branch-code order.
- `selectedScanBranchFamily_complete`: selector codes enumerate exactly `selectedBasisExchangeFamily`.
- `selectedScanOrder_covers`: every selector code appears in the selected order.
- `selectedScanBranchHit_iff_exchangeHit`: branch-code hit is equivalent to hitting the interpreted exchange branch.
- `firstMissedSelectedBranch?`: ordered `Option` residual selector.
- `firstMissedSelectedBranch?_some_mem`: returned residual codes are listed.
- `firstMissedSelectedBranch?_some_missed`: returned residual codes are genuinely missed.
- `firstMissedSelectedBranch?_none_iff_listedHits`: no residual iff all listed selector codes are hit.
- `firstMissedSelectedBranch?_none_iff_transversal`: no selected residual iff selected exchange-branch transversality.
- `traceOnly_firstMissedSelectedBranch`: trace-only repair first misses the refined repair-frontier selector code.
- `traceOnly_firstMissedSelectedBranch_residual`: the returned residual is selected and missed.
- `dropFirstMissed_restores_traceOnlyTransversal`: deleting the first missed selected residual restores trace-only transversality for the selected finite family.
- `CollapsedVisibleScanBranch` and `firstMissedCollapsedVisibleBranch?`: collapsed visible reading and its residual selector.
- `collapsedVisible_firstMissedBranch_traceOnly`: trace-only repair has no collapsed-visible residual.
- `visibleEquivalent_residualKernelPair`: selected and collapsed readings have the same visible union but different residual behavior.
- `visibleUnion_not_faithful_to_branchScanKernel`: visible union is not faithful to the branch scan kernel.
- `branchTransversalScanKernel_package`: theorem package.

Local checks:

- `lake env lean research/lean/ResearchLean/QualitySurface/BranchTransversalScanKernel.lean`: pass.
- `lake build ResearchLean`: pass.
- `lake build`: pass, with only the pre-existing `Formal/Arch/Extension/FeatureExtensionExamples.lean` linter warnings.
- `#print axioms`: selector type, branch interpretation, selected order, hit predicates, both scan functions, and concrete residual predicate are axiom-free.  Selector enumeration, list membership / none-iff proofs, trace-only concrete scan result, deletion/restoration, visible-equivalent kernel pair, nonfaithfulness, and the package use only standard `propext`.  No `sorryAx`, custom axiom, `Classical.choice`, `Quot.sound`, or `unsafe` was reported.

## 可視 projection

The visible projection remembers the component union that appears somewhere in
the selected exchange family, but forgets the ordered branch-incidence data
used by the scan kernel.

## protected_structure

The protected structure is the selected path-indexed branch family together
with the ordered selector and repair support.

## exactness_or_minimality_claim

Minimality is only selector-relative: the first missed branch in the selected
ordered list is the canonical residual for that selector, and deleting it
restores trace-only transversality for this selected finite family.  No global
minimal repair set or global canonical order is claimed.

## nonfaithfulness_or_failure_mode

The visible component-union projection cannot recover whether the selected
scan kernel has a residual branch.  Trace-only repair can look adequate after
visible collapse while the protected scan returns the refined repair-frontier
branch.

## previous_cycle_delta

Cycle 70 fixed path-indexed branch exchange and visible-union loss.  Cycle 71
showed that a naive refinement reading can preserve visible union while
missing branch reflection.  This cycle turns the protected failure into a
computable residual selector.

## 審判メモ

- 厳密性: revise / base 76 / genius no。claim boundary は良好だが、既存 Cycle 70/71 と Cycles 55/56 の再包装に見えるリスクがある。selector code、`Option` residual、enumeration exactness、same-visible kernel pair を Lean statement に入れることを要求。
- 研究価値: accept / base 88 / genius no。repair obligation を residual-producing certificate object に上げる点を評価。
- repo 全体価値: accept / base 84 / genius no。future viewer projection rule の足場になるが、既存 scan 系との差分を明記する必要がある。
- ライバル比較: accept / base 88 / genius no。ADL / dashboard 的 failure display ではなく path-indexed residual branch と deletion/restoration を証明対象にする点を評価。
- G2 revise 対応: 候補カードを改訂し、selector-code enumeration、`Option` first-missed residual、visible-equivalent kernel pair、既存 route-slot scan との差分を主張と証明計画へ追加した。
- G2 厳密性再審判: accept / base 80 / genius no。改訂で G3 へ進めるが、既存 ordered scan machinery があるため base 88 ではなく 80 とする。
- G3 公理検査: pass。computational objects and concrete residual predicate are axiom-free; Prop-level list / iff wrappers use only standard `propext`.  No `sorryAx`, custom axiom, `Classical.choice`, `Quot.sound`, or `unsafe`.
- G3 形式化品質監査: pass。generic scan recursion の新規性は限定的だが、exact selector enumeration、selected transversality iff, concrete trace-only residual, deletion/restoration, and visible-equivalent selected/collapsed residual kernel pair が候補主張を十分に表している。
- G4 SCORE 監査: confirm / base 80 / multiplier 2.0 / penalty 0 / final +160。Total は 9634 から 9794 へ進む。G2 全員が genius no のため genius scoring は not-applicable。

## 関連

- `g-aat-quality-surface-01-curvature-basis-exchange.md`
- `g-aat-quality-surface-01-naive-refinement-support-counterexample.md`

## 進捗ログ

- 2026-06-21: Cycle 72 の picked 候補として作成。G2 へ進める。
- 2026-06-21: G2 厳密性 revise を受け、ordered selector code と visible-equivalent residual kernel pair を必須証拠に追加。
- 2026-06-21: `BranchTransversalScanKernel.lean` を追加し、selector-relative branch-transversal scan kernel として Lean 検証済みに同期。
- 2026-06-21: G3 公理検査と形式化品質監査を通過。
- 2026-06-21: G4 SCORE 監査で final +160 を confirm。
