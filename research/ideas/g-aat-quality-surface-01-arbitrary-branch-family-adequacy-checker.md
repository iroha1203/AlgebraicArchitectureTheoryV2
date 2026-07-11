---
status: picked
goal: G-aat-quality-surface-01
exploration_role: closer / wildcard / unifier
candidate_type: computability
capability_category: computability / certificate-transport / repair-potential / obstruction / invariance / quality-surface
expected_base_score: 84
expected_evidence_multiplier: 2.0
expected_final_score: 168
evidence_stage: proved-in-research
rival_advantage: ADL / dashboard / AI-review readings can show pass/fail rows or visible component unions, but they do not certify that a finite branch-family adequacy checker is sound, complete, and returns a protected missing reflected branch witness.
origin: cycle-75
tags: [quality-surface, finite-branch-family, adequacy-checker, residual-witness, genius-support]
created: 2026-06-22
cycle: 75
lean: proved-in-research
---

# Arbitrary finite branch-family adequacy checker with witness-complete residuals

## 主張

任意の source branch family、target branch family、branch-reflection relation、declared repair support に対して、
supplied finite target order が target family を exact に列挙するという仮定のもとで adequacy checker を定義する。
checker が `none` を返すことは、その finite target order 上の全 branch が source family の branch と support-lift closure によって
covered されることと同値である。加えて target-order completeness により、それは target family 全体の adequacy と同値になる。
`some b` を返す場合は、`b` が target order に属し、target family の branch であり、source 側に reflected support-lift witness を持たない
protected missing branch witness である。

さらに adequacy が通るなら、source branch-transversal repair clearance は target branch-transversal clearance へ transport する。
同じ visible component-union projection を持つ selected / collapsed readings でも、protected adequacy checker は異なる結果を返しうる。

この主張は、exact target-order enumeration、decidable covered predicate、supplied branch-reflection relation、declared component repair support、
selected finite Quality Surface witness に相対化する。
global canonical refinement、runtime repair synthesis、source extraction completeness、ArchMap correctness、global sheaf completeness、whole-codebase quality は主張しない。

## 候補種別

`computability`

## 依拠

- Cycle 70: `CurvatureBasisExchange.lean` の path-indexed exchange branch family。
- Cycle 72: `BranchTransversalScanKernel.lean` の selected residual scan。
- Cycle 73: `BranchReflectionAdequacyKernel.lean` の branch-local support-lift adequacy。
- Cycle 74: `SelectedResidualScanPrefixMinimality.lean` の prefix-exact residual diagnostics。
- tracking Issue #2348 の genius target seed: semantic repair-gluing obstruction theorem。

## 非自明性

Cycle 72-74 は selected scan order と trace-only witness に依存していた。この候補は、target family を exact に列挙する
任意の finite target order と branch-reflection relation を入力にした proof-producing checker へ一般化する。
単なる list scan ではなく、checker の `none` / `some` を adequacy、missing branch witness、
transversality transport に結びつける点が非自明である。

## 数学的興味

finite repair obstruction を、存在命題ではなく executable residual object として読む。`some b` は UI の first failing row ではなく、
supplied target order に相対化された protected branch-reflection failure witness であり、`none` は repair-transversal transport の
十分条件を証明する。この形は、将来の semantic repair-gluing obstruction theorem で必要になる finite adequacy witness engine になる。

## GOAL への前進

arbitrary finite branch family に対する executable adequacy checking を与え、Quality Surface の computability、
certificate-transport、repair-potential、obstruction 軸を一段広げる。Cycle 73 の selected adequacy kernel を、次の
component-level refinement support-lift theorem と semantic repair-gluing obstruction target の support node にする。

## ライバルに対する有効性

ADL / conformance dashboard は component set、view、first failing row、pass/fail summary を表示できる。
しかしこの候補は、finite branch-family checker の soundness / completeness と、failure 時に返る protected missing reflected branch witness を
theorem として固定する。strong rival の AI-review summary でも、branch-reflection relation と support-lift closure を持たなければ、
visible component union から adequacy result を復元できない。

## SCORE 見込み

- `score_reason`: selected residual scan と branch-reflection adequacy を任意有限 branch family の sound / complete checker へ持ち上げる。G2 四審判後、A の厳格値に合わせて base 84 / final 168 見込みへ下げる。
- `dullness_risk`: generic list search の再包装に落ちると低価値。branch reflection relation、support-lift closure、missing protected branch witness、transport theorem、visible projection contrast をすべて Lean statement に含める。
- `proof_or_evidence_plan`: Research 側 Lean ファイルで finite target order、target-order exactness、decidable covered predicate、first uncovered branch checker、none iff listed adequacy、target-order completeness から full adequacy への変換、some witness membership/missingness、adequate transport theorem、selected/collapsed visible nonfaithfulness package を証明する。

## CS / SWE への帰結

refinement / viewer / diagnostic surface が first failure を表示するとき、その failure が protected branch-reflection transport のどの missing witness かを返せる。
逆に `none` の場合は、source repair clearance を target repair clearance へ運べる条件を持つため、可視 pass/fail を repair-transversal semantics へ接続できる。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/ArbitraryBranchFamilyAdequacy.lean` に固定した。

- `TargetOrderEnumerates`
- `ListedTargetCodesCovered`
- `CodeReflectionCovered`
- `BranchFamilyReflectionAdequate`
- `firstUncoveredTargetBranch?`
- `firstUncoveredTargetBranch?_some_mem`
- `firstUncoveredTargetBranch?_some_uncovered`
- `firstUncoveredTargetBranch?_some_witness`
- `firstUncoveredTargetBranch?_none_iff_listedAdequate`
- `listedCoverage_gives_branchFamilyAdequacy`
- `firstUncoveredTargetBranch?_none_iff_adequate`
- `branchFamilyAdequacy_transportsTransversal`
- `selectedTargetOrderEnumerates`
- `collapsedTargetOrderEnumerates`
- `selectedTraceOnlyCoveredByCollapsed_iff_reflection`
- `selected_firstUncoveredTargetBranch`
- `collapsed_firstUncoveredTargetBranch_none`
- `selected_firstUncoveredTargetBranch_witness`
- `visibleUnion_not_faithful_to_arbitraryAdequacyCheck`
- `arbitraryBranchFamilyAdequacyChecker_package`

G3 実績:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/ArbitraryBranchFamilyAdequacy.lean`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: definitions、`listedCoverage_gives_branchFamilyAdequacy`、`branchFamilyAdequacy_transportsTransversal`、`selectedTraceOnlyCoveredByCollapsed_iff_reflection` は axiom-free。`firstUncoveredTargetBranch?_some_*`、list / iff / selected-collapsed witness / package 系 theorem は標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`Quot.sound`、`unsafe` は出ていない。
- `rg -n "\\b(axiom|admit|sorry|unsafe)\\b"` on changed files: no matches。

## 審判メモ

- 厳密性: revise 後 accept。base 84。target-order exactness、decidable coverage、`none iff listed adequacy` と full adequacy 変換を分けたことで、order omission の穴は閉じた。残るリスクは adequacy 定義の tautology 化と visible contrast の再掲化。
- 研究価値: accept。base 90。Cycle 72-74 の scan / adequacy / prefix residual / visible nonfaithfulness を arbitrary finite checker contract に圧縮し、semantic repair-gluing target の support node を作る。
- repo 全体価値: accept。base 86。Lean / paper / future tooling 価値があり、AAT の computability、certificate-transport、repair-potential、projection nonfaithfulness に整合する。
- ライバル比較: accept。base 90。ADL / dashboard / AI-review に対し、pass/fail row ではなく protected missing reflected branch witness と transport theorem を返す点が差分。
- genius: 四審判とも `genius_eligibility: no`。通常 SCORE の genius-support-normal として扱う。

## G4 SCORE 監査結果

- score_verdict: confirm。
- base_score: 84。
- evidence_multiplier: 2.0。
- penalty: 0。
- final_score: 168。
- category: computability / certificate-transport / repair-potential / obstruction / invariance / quality-surface。
- genius_verdict: downgrade-to-normal。四審判すべて `genius_eligibility: no` であり、これは target unlock ではなく support node である。
- total_delta: 10090 -> 10258。active threshold 12000 までは残り 1742。
- research_kiri_contribution: positive support-cycle contribution。phase boundary ではない。

## 追加 required fields

- `mathematical_interest`: finite branch obstruction を executable residual object として正規化し、transport adequacy と結びつける点。
- `goal_advancement`: arbitrary finite branch-family adequacy checking を確立し、semantic repair-gluing obstruction target の support node を作る。
- `planned_theorem_names`: `BranchFamilyReflectionAdequate`, `firstUncoveredTargetBranch?_none_iff_adequate`, `branchFamilyAdequacy_transportsTransversal`, `visibleUnion_not_faithful_to_arbitraryAdequacyCheck`, `arbitraryBranchFamilyAdequacyChecker_package`
- `visible_projection`: collapsed visible component-union / UI-level pass-fail reading。これは protected branch adequacy checker に faithful ではない。
- `protected_structure`: target branch incidence, source-to-target reflection coverage, branch-local support-lift closure, missing reflected branch witness。
- `exactness_or_minimality_claim`: target family を exact に列挙する supplied finite order に相対化した sound / complete adequacy decision。global canonical minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: visible union が同じでも checker result と missing protected branch が異なる。
- `previous_cycle_delta`: Cycle 72 selected scan、Cycle 73 adequacy kernel、Cycle 74 prefix residual theorem を arbitrary finite family へ広げる。
- `rival_stress_test`: 同じ visible union を持つ selected/reflected branch families を入力し、一方は checker pass、他方は missing repair-frontier branch を返す finite case を置く。
- `genius_potential`: no
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: finite adequacy witness engine。semantic repair-gluing theorem の support map の第一ノード。

## 関連

- `research/ideas/g-aat-quality-surface-01-branch-transversal-scan-kernel.md`
- `research/ideas/g-aat-quality-surface-01-branch-reflection-adequacy-kernel.md`
- `research/ideas/g-aat-quality-surface-01-selected-residual-scan-prefix-minimality.md`

## 進捗ログ

- 2026-06-22: G1 四ロールの候補 pool から Cycle 75 通常候補として作成。genius target seed への support role を明記した。
- 2026-06-22: G2 A の revise により、`arbitrary finite branch family` を exact target-order enumeration と decidable coverage に相対化し、checker の `none iff adequacy` が target order omission で破綻しないよう主張を修正した。
- 2026-06-22: G2 四審判が accept。base は A=84, B=90, C=86, D=90。strict base 84 / expected final 168 として picked に更新。
- 2026-06-22: G3 Lean 証拠を `ArbitraryBranchFamilyAdequacy.lean` に固定し、`ResearchLean` が通った。
- 2026-06-22: G3 形式化品質監査の minor caveat を受け、generic `some -> listed ∧ targetFamily ∧ uncovered` を `firstUncoveredTargetBranch?_some_witness` として追加し、package theorem に含めて再ビルドした。
- 2026-06-22: G4 SCORE 監査が confirm。base 84、multiplier 2.0、final +168。genius は通常 SCORE へ downgrade。
