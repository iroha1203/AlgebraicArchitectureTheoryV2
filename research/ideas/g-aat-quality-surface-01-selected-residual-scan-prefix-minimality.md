---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: computability / minimality / obstruction / repair-potential / certificate-transport / quality-surface
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
rival_advantage: ADL / conformance dashboards can show an ordered failure row, but they do not prove that the returned protected branch is prefix-exact, genuinely missed, and the minimal selected deletion that restores branch-transversal repair.
origin: cycle-74
tags: [quality-surface, residual-scan, prefix-exactness, minimality]
created: 2026-06-22
cycle: 74
lean: proved-in-research
---

# Prefix-minimal residual scan theorem for selected branch diagnostics

## 主張

Cycle 72 の selected branch scan に、prefix exactness と selector-relative minimal restoration を追加する。
`firstMissedSelectedBranch?` が residual code を返すとき、その code の前方 prefix はすべて hit 済みであり、
returned code は genuinely missed である。選ばれた trace-only witness では、前方 branch を削除しても
selected transversality は回復せず、returned residual branch を削除したときだけ trace-only transversality が回復する。

この主張は、選ばれた finite selected scan order、path-indexed exchange branch family、trace-only declared support、
collapsed visible reading に相対化する。global canonical repair order、global minimality、runtime repair synthesis、
source extraction completeness、ArchMap correctness、global sheaf completeness、whole-codebase quality は主張しない。

## 候補種別

`closure`

## 依拠

- Cycle 72: `BranchTransversalScanKernel.lean` の selected scan、first missed residual、selected/collapsed visible nonfaithfulness。
- Cycle 73: `BranchReflectionAdequacyKernel.lean` の missing reflected branch と transport adequacy obstruction。

## 非自明性

単なる `some_mem` / `some_missed` の再掲ではなく、returned residual の前方 prefix がすべて hit 済みであること、
そして selected trace-only witness で earlier deletion では restoration せず returned deletion で restoration することを
同じ package にまとめる。これにより residual scan を viewer の first failure 表示ではなく、repair-transversal obstruction の
prefix-minimal certificate として読める。

## 数学的興味

ordered finite branch family に対して、最初の residual は diagnostic order に相対化した境界点である。
前方 prefix は clear 済み、returned branch は missed、returned branch の削除だけが selected trace-only transversality を戻す。
この「prefix exactness + restoration minimality」が、branch scan を単なる list traversal から obstruction certificate に変える。

## GOAL への前進

Quality Surface の computability / repair-potential 軸に、selected residual scan の exact explanation を追加する。
Cycle 72 の residual kernel と Cycle 73 の missing branch obstruction を、phase report で使える prefix-minimal diagnostic theorem として閉じる。

## ライバルに対する有効性

ADL / conformance / dashboard は failure list や first failing row を返せるが、その row が path-indexed branch obligation の
prefix-minimal obstruction であり、前方 branches は hit 済みで、returned protected branch の deletion が restoration になることは
通常 theorem として持たない。この候補は first failure display を AAT 側の証明付き repair-transversal diagnostic に持ち上げる。

## SCORE 見込み

- `score_reason`: Cycle 72/73 の scan / missing branch machineryを prefix exactness と restoration minimality で閉じる。G2 は prefix 性自体が既存 scan recursion に近いと見たため、通常 SCORE の base 60 見込みへ下げる。
- `dullness_risk`: `firstMissedSelectedBranch?_some_mem` や `some_missed` の焼き直しに落ちると低価値。trace-only selected witness で earlier deletion non-restoration と returned deletion restoration を含め、residual の diagnostic 意味を強める。
- `proof_or_evidence_plan`: Research 側 Lean ファイルで prefix-before predicate、generic prefix-hit theorem、trace-only prefix exactness、earlier deletion non-restoration、returned deletion restoration、visible collapsed contrast、package theorem を証明する。

## CS / SWE への帰結

UI や report で first residual marker を出すとき、それが単なる最初に見つかった行ではなく、selected order に相対化した
prefix-exact obstruction certificate であると言える。visible collapsed reading では residual が消えるため、AAT 側で保つべき
protected scan payload の意味も明確になる。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SelectedResidualScanPrefixMinimality.lean` に固定した。

- `selectedPrefixBefore`
- `firstMissedSelectedBranch?_some_prefixHit`
- `traceOnly_firstResidual_prefixExact`
- `dropSelectedScanBranch`
- `refinedRepairFrontier_ne_coarseTraceBranch`
- `refinedRepairFrontier_ne_refinedTraceBranch`
- `traceOnly_dropCoarseTrace_not_restore_selectedTransversal`
- `traceOnly_dropRefinedTrace_not_restore_selectedTransversal`
- `traceOnly_noEarlierDeletionRestoresSelectedTransversal`
- `traceOnly_returnedDeletionRestoresSelectedTransversal`
- `selectedResidualPrefix_visibleContrast`
- `selectedResidualScanPrefixMinimality_package`

## G2 審判結果

- 厳密性: accept。base 60。境界は selected finite scan order と trace-only witness に相対化されている。prefix exactness 自体は recursion に近いため、no-earlier-deletion / returned-deletion restoration が価値の条件。
- 研究価値: accept。base 52。主定理級ではないが、selected residual を prefix-exact obstruction certificate として閉じる診断意味論として有効。
- repo 全体価値: accept。base 64。Lean / paper seed と future viewer projection rule に接続する。
- ライバル比較: accept。base 72。dashboard の first-failing row ではなく、protected residual と deletion/restoration semantics を持つ点で有効。
- genius: 四審判とも `genius_eligibility: no`。

## G3 監査結果

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/SelectedResidualScanPrefixMinimality.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SelectedResidualScanPrefixMinimality`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: `selectedPrefixBefore`, `dropSelectedScanBranch`, branch inequality lemmas、earlier deletion non-restoration、no-earlier-deletion theorem は axiom-free。`firstMissedSelectedBranch?_some_prefixHit`, `traceOnly_firstResidual_prefixExact`, `traceOnly_returnedDeletionRestoresSelectedTransversal`, `selectedResidualPrefix_visibleContrast`, `selectedResidualScanPrefixMinimality_package` は標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`Quot.sound`、`unsafe` なし。
- Lean 形式化品質監査: pass。minimality は selector-relative singleton deletion に限定されており、global minimality は主張していない。`selectedPrefixBefore` は固定 selected order の inductive relation であり、将来の可変 scan order には別途 list-based predicate が必要。

## G4 SCORE 監査結果

- score_verdict: confirm。
- base_score: 60。
- evidence_multiplier: 2.0。
- penalty: 0。
- final_score: 120。
- category: computability / minimality / obstruction / repair-potential / certificate-transport / quality-surface。
- genius_verdict: downgrade-to-normal。四審判すべて `genius_eligibility: no` なので genius scoring は採らない。
- total_delta: 9970 -> 10090。active threshold 10000 に到達する。

## 審判メモ

- 厳密性: prefix exactness が generic recursion の単なる再命名に落ちていないか。selected trace-only witness の restoration minimality が Lean statement に入っているか。
- 研究価値: phase boundary 直前の小補題ではなく、residual scan の diagnostic 意味を強めているか。
- repo 全体価値: report / future viewer projection rule に自然に接続するか。
- ライバル比較: first failing row を返す dashboard との差分が theorem-level prefix/minimality にあるか。

## 追加 required fields

- `mathematical_interest`: ordered finite branch scan の returned residual を prefix-minimal obstruction certificate として読む点。
- `goal_advancement`: residual-producing scan kernel を exact diagnostic theorem へ進める。
- `planned_theorem_names`: `firstMissedSelectedBranch?_some_prefixHit`, `traceOnly_firstResidual_prefixExact`, `traceOnly_noEarlierDeletionRestoresSelectedTransversal`, `traceOnly_returnedDeletionRestoresSelectedTransversal`, `selectedResidualScanPrefixMinimality_package`
- `visible_projection`: collapsed visible scan / visible component-union projection。これは selected prefix residual を復元しない。
- `protected_structure`: selected scan order, path-indexed branch code, prefix hit certificate, first missed residual, deletion/restoration witness。
- `exactness_or_minimality_claim`: selector-relative singleton deletion minimality。returned residual の前方 prefix は exact に hit 済みで、selected trace-only witness では前方 singleton deletion は restoration せず returned singleton deletion が restoration する。global minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: collapsed visible scan は residual none だが、selected protected scan は refined repair-frontier branch を prefix-minimal residual として返す。
- `previous_cycle_delta`: Cycle 72 の selected residual scan と Cycle 73 の missing branch obstruction を、prefix-minimal diagnostic theorem として閉じる。
- `genius_potential`: no
- `genius_target`: none
- `genius_support_role`: none

## 関連

- `research/ideas/g-aat-quality-surface-01-branch-transversal-scan-kernel.md`
- `research/ideas/g-aat-quality-surface-01-branch-reflection-adequacy-kernel.md`

## 進捗ログ

- 2026-06-22: Cycle 74 候補として作成。
- 2026-06-22: G2 四審判は accept。base は A=60, B=52, C=64, D=72。全員 `genius_eligibility: no`。期待値を base 60 / final 120 へ下方修正し、minimality scope を selector-relative singleton deletion に限定。
