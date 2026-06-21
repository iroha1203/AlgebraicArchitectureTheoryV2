---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: obstruction / invariance / minimality / certificate-transport / quality-surface
expected_base_score: 68
expected_evidence_multiplier: 2.0
expected_final_score: 136
evidence_stage: proved-in-research
rival_advantage: ADL / conformance refinement views can preserve visible component unions while missing whether branch reflection preserved path-indexed repair obligations.
origin: G1-cycle71
tags: [quality-surface, refinement, cech, branch-transversal, counterexample]
created: 2026-06-21
cycle: 71
lean: Formal/AG/Research/QualitySurface/NaiveRefinementSupportCounterexample.lean
genius_potential: no
genius_target: none
genius_support_role: none
---

# Selected branch-reflection failure for naive refinement readings

## 主張

In the selected finite repair/refinement exchange cell, preserving visible
component-union data is not enough to preserve branch-transversal repair
obligations.  A naive refinement reading can keep the coarse trace branch and
pair the refined trace / repair-frontier components into one refined branch.
That reading has the same visible component-union projection as the reflected
selected branch reading, and the trace-only repair support hits the naive
paired reading.  But the reflected selected reading separates the refined
repair-frontier singleton branch, and trace-only repair misses it.

The obstruction is minimal only in the selected finite deletion/restoration
sense: deleting the reflected refined repair-frontier singleton branch restores
trace-only transversality for the selected branch family.  This is not a global
minimality theorem, and it does not claim that the visible union remains
unchanged after deletion.  The point is narrower: visible-union preservation
does not encode the branch-reflection datum needed by repair transversality.

This is a selected finite no-go theorem for a too-weak refinement reading.  It
does not define or prove a positive atlas-refinement transport theorem,
canonical refinement, runtime repair synthesis, source extraction completeness,
ArchMap correctness, arbitrary route enumeration, global sheaf completeness,
or whole-codebase quality.

## 候補種別

`orientation`: before proving a positive refinement-invariant support
transport theorem, this cycle fixes a selected finite failure mode of the
naive visible-union-preserving reading.

## 依拠

- `Formal/AG/Research/QualitySurface/AntichainOverlapBasisTransversal.lean`
- `Formal/AG/Research/QualitySurface/CurvatureBasisExchange.lean`
- Cycle 69 antichain branch-transversal nonfaithfulness.
- Cycle 70 path-indexed curvature basis exchange.

## 非自明性

This is not just another trace-only failure.  The point is to separate three
levels:

1. visible component-union preservation,
2. naive side-indexed paired branch reading, and
3. reflected selected branch reading with the refined repair-frontier singleton
   branch.

The theorem should show that level 1 and even a paired level-2 reading are not
enough for branch-transversal preservation.  The missing datum is exactly the
reflected refined repair-frontier singleton branch.  The refinement language is
therefore represented by a selected finite `branch reflection` reading, not by
a global atlas-refinement morphism.

## 数学的興味

The result turns a prospective refinement theorem into a necessary-hypothesis
problem.  It identifies branch reflection, not visible component support, as
the datum that must be preserved by a future refinement map if
repair-transversal semantics are to be invariant.

## GOAL への前進

This advances the refinement-invariant support frontier by preventing a false
invariance theorem and isolating the minimal protected structure needed for
the positive theorem.

## ライバルに対する有効性

ADL, conformance tools, and dashboards can compare refined views and component
sets.  They do not by themselves prove that refinement preserves the
path-indexed branch-transversal class.  This candidate makes the failure of
that inference Lean-checkable.

## SCORE 見込み

- `score_reason`: moderate orientation value because it prevents a too-weak refinement theorem and isolates branch reflection as the missing hypothesis, while reusing Cycle 70's selected finite setting.
- `dullness_risk`: real.  If it only repeats Cycle 70 trace-only nonfaithfulness, the score should drop.  The Lean evidence must explicitly introduce a selected finite branch-reflection reading, a naive refined-pair reading, and deletion/restoration of the reflected repair-frontier singleton.
- `proof_or_evidence_plan`: completed in `Formal/AG/Research/QualitySurface/NaiveRefinementSupportCounterexample.lean`.

## Lean evidence

Lean proves:

- `naiveRefinedPairExchangeBranch`: a refined-side paired trace / repair-frontier branch.
- `naiveRefinementBranchFamily`: coarse trace plus the naive refined paired branch.
- `reflectedSelectedBranchFamily`: the selected Cycle 70 branch family, read as a selected branch-reflection target.
- `branchReflectedBy`: a selected finite predicate saying a reflected branch is represented by a source branch under the reading.
- `naiveReading_not_reflects_repairFrontierSingleton`: the naive paired reading does not reflect the refined repair-frontier singleton as a separate branch.
- `naiveRefinement_preserves_visibleUnion`: naive and reflected readings have the same visible component union.
- `traceOnly_hits_naiveRefinementBranches`: trace-only support is a transversal for the naive paired reading.
- `traceOnly_not_hits_reflectedSelectedBranches`: trace-only support is not a transversal for the reflected selected reading.
- `reflectedRepairFrontier_minimal_obstruction`: the refined repair-frontier singleton branch is the exact missed branch that breaks transversality.
- `dropRefinedRepairFrontier_restores_traceOnlyTransversal`: deleting that singleton restores trace-only transversality in the selected finite family.
- `selectedBranchReflectionFailure`: visible-union preservation, branch-reflection failure, trace-only separation, and deletion/restoration in one statement.
- `naiveRefinementCounterexample_package`: visible preservation, before/after transversal separation, and minimal obstruction.

Local checks:

- `lake env lean Formal/AG/Research/QualitySurface/NaiveRefinementSupportCounterexample.lean`: pass.
- `lake build FormalAGResearch`: pass.
- `lake build`: pass, with only existing `Formal/Arch/Extension/FeatureExtensionExamples.lean` linter warnings.
- `#print axioms`: all reported declarations are axiom-free.  No `sorryAx`, custom axiom, `propext`, `Classical.choice`, `Quot.sound`, or `unsafe` appears in the reported declarations.

## 可視 projection

The visible projection forgets the difference between a refined paired branch
and the two reflected refined singleton branches, remembering only the
component union.

## protected_structure

The protected structure is branch reflection: refined trace and refined
repair-frontier must remain separate selected branches when the repair
obligation depends on branch transversality.

## exactness_or_minimality_claim

The exactness input is inherited from Cycle 70: selected exchange branches are
grounded in exact coarse and refined Cech overlap bases, and
component-complete common clearance is equivalent to hitting those selected
exchange branches.  This cycle's new selected finite minimality claim is only
deletion/restoration: dropping the reflected repair-frontier singleton restores
trace-only transversality for the selected family.

## nonfaithfulness_or_failure_mode

Naive visible refinement preserves the visible component-union projection, but
it is nonfaithful to the branch-transversal class because it pairs away the
refined repair-frontier singleton obstruction.

## previous_cycle_delta

Cycle 70 showed that a collapsed visible exchange family and the selected
path-indexed family can have the same visible union while differing on
transversality.  This cycle sharpens that into a refinement-invariance no-go:
branch reflection, not visible union preservation, is the missing hypothesis.

## 審判メモ

- 厳密性: G2 で判定する。特に「最小反例」が selected finite deletion/restoration として十分に定式化されているかを確認する。
- 研究価値: G2 で判定する。
- repo 全体価値: G2 で判定する。
- ライバル比較: G2 で判定する。
- G2 revise 対応: 厳密性審判の指摘を受け、global refinement theorem ではなく selected finite branch-reflection failure に縮約し、expected base score を 88 から 68 に下げた。`minimal` は deletion/restoration に限定し、削除後も visible union が同一であるとは主張しない。
- G2: revised card 後、厳密性 accept / base 68 / genius no、研究価値 accept / base 82 / genius no、repo 全体価値 accept / base 84 / genius no、ライバル比較 accept / base 68 / genius no。
- G3 公理検査: pass。報告対象9 theorem はすべて axiom-free。
- G3 形式化品質監査: pass。ただし `branchReflectedBy` は selected finite witness には十分だが、将来の一般 refinement API としては弱い。この cycle では一般 API として扱わない。
- G4 SCORE 監査: confirm / base 68 / multiplier 2.0 / penalty 0 / final +136。Total は 9498 から 9634 へ進む。G2 全員が genius no のため genius scoring は not-applicable。

## 関連

- `g-aat-quality-surface-01-antichain-overlap-basis-transversal-exactness.md`
- `g-aat-quality-surface-01-curvature-basis-exchange.md`

## 進捗ログ

- 2026-06-21: Cycle 71 の picked 候補として作成。G2 へ進める。
- 2026-06-21: G2 A revise を受け、主張境界と SCORE 見込みを保守的に改訂。
- 2026-06-21: `NaiveRefinementSupportCounterexample.lean` を追加し、selected finite branch-reflection failure として Lean 検証済みに同期。
- 2026-06-21: G4 SCORE 監査で final +136 を confirm。
