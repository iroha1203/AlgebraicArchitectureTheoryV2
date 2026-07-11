---
status: picked
goal: G-aat-quality-surface-01
exploration_role: closer / computability / minimality / obstruction-class support convergence
candidate_type: computability / exactness / genius-support
capability_category: semantic-obstruction / finite-atlas-transition / computability / genius-support
expected_base_score: 72
expected_evidence_multiplier: 2.0
expected_final_score: 144
evidence_stage: proved-in-research
rival_advantage: ADL, static analyzers, dashboards, and AI summaries can report edges or suspected violations, but they do not return a Lean proof-carrying residual transition cut certificate with scanner exactness over a supplied finite atlas edge order.
origin: cycle-90
tags: [quality-surface, semantic-repair, indexed-transport, residual-cut, scanner, genius-support]
created: 2026-06-23
cycle: 90
lean: proved-in-research
planned_report_section: "Cycle 90: Supplied-order residual transition cut scanner exactness"
---

# Supplied-order Residual Transition Cut Scanner Exactness

## 主張

Cycle 89 の finite atlas `ResidualTransitionCut` を、supplied finite edge order 上の scanner exactness へ上げる。
scanner が `some pair` を返すなら、その pair は `ResidualTransitionCut` を復元し、任意の `AtlasResidualTransitionClosed` と `TransitionCoherentAtlasData` を阻む。
scanner が `none` を返すことは listed edge order 上の residual cut 不在と同値であり、edge order が active edge family を cover する場合に限って atlas 上の `ResidualTransitionCut` 不在と同値になる。

この主張は、`none -> transition closure`、canonical/global minimal cut、order-independent minimality、obstruction class、arbitrary sheaf gluing、runtime repair synthesis、source extraction completeness、ArchMap correctness、whole-codebase quality を含まない。

## 候補種別

`computability` / `exactness` / `genius-support`

## 依拠

- Cycle 86: semantic residual finite scanner。
- Cycle 88: residual-present / residual-free edge obstruction。
- Cycle 89: finite semantic atlas residual transition cut certificate。
- open genius target: `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。

## 非自明性

単に Cycle 89 の cut witness を list recursion で包むだけでは弱い。
この候補では、cut pair predicate、finite edge-order scanner、`some -> cut certificate`、`some -> obstruction`、`none <-> listed cut-free`、complete edge-order 下の `none <-> no ResidualTransitionCut`、および supplied order に相対化した prefix-clear witness を一つの theorem package にする。

## 数学的興味

finite atom-supported atlas の semantic residual obstruction を、存在証明だけでなく diagnostic selector として扱えるようにする。
これは H^1 obstruction class そのものではないが、edge-local obstruction を proof-carrying finite detector に変換する support node であり、次の obstruction-class formulation の入力になる。

## GOAL への前進

`finite transition scanner exactness` frontier を閉じ、open genius target の certificate-selector layer を追加する。
Cycle 89 の cut certificate を、finite diagnostic regime が返せる obstruction certificate に変える。

## ライバルに対する有効性

ADL や architecture conformance checker は edge row、violation、constraint failure を示せる。
static analyzer や dashboard は検出結果や severity を返せる。
AI review summary は疑わしい edge を説明できる。
この候補の差分は、選ばれた semantic atom vocabulary と finite atlas skeleton に相対化して、scanner の返り値が Lean の `ResidualTransitionCut` certificate を復元し、その certificate が closure/data を阻む theorem まで持つ点にある。

## SCORE 見込み

- `score_reason`: Cycle 86 scanner pattern と Cycle 89 cut certificate を接続し、supplied finite edge order に対する exact proof-carrying diagnostic にする。新しい obstruction 原理ではないため genius unlock ではなく support cycle とする。
- `dullness_risk`: `some -> cut` だけなら Cycle 89 の thin wrapper になる。`none` exactness、edge-order completeness、prefix-clear witness、selected concrete scanner witness を揃えることで研究 delta を確保する。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/QualitySurface/SemanticResidualTransitionCutScanner.lean` で scanner predicate、finite scanner、some/none exactness、prefix-clear witness、selected frontier-flat scanner theorem、package theorem を証明する。

## CS / SWE への帰結

finite atlas diagnostic で edge row を見せるだけでは不十分である。
診断 surface は、返した edge pair が semantic residual cut certificate を復元し、その certificate が transition closure を阻むことまで保持して初めて、AAT 側の quality geometry に載る。

## 証明・根拠の見込み

Lean 証拠は `research/lean/ResearchLean/QualitySurface/SemanticResidualTransitionCutScanner.lean` に固定した。

- `IsResidualTransitionCutPair`
- `ListedAtlasEdgesComplete`
- `ListedResidualTransitionCutsClear`
- `residualTransitionCut_of_pair`
- `residualTransitionCut_pair_isCut`
- `firstResidualTransitionCut?`
- `firstResidualTransitionCut?_some_mem`
- `firstResidualTransitionCut?_some_pairCut`
- `firstResidualTransitionCut?_some_cut`
- `firstResidualTransitionCut?_some_obstructs_atlasTransitionClosure`
- `firstResidualTransitionCut?_some_obstructs_transitionCoherentData`
- `PrefixBeforeFirstCut`
- `firstResidualTransitionCut?_some_prefixClear`
- `firstResidualTransitionCut?_none_iff_listedCutsClear`
- `firstResidualTransitionCut?_none_iff_noResidualTransitionCut`
- `selectedFrontierFlatScanOrder`
- `selectedFrontierFlatCutPairDecidable`
- `selected_firstResidualTransitionCut`
- `selected_firstResidualTransitionCut_prefixClear`
- `selected_firstResidualTransitionCut_obstructs_transitionClosure`
- `selected_firstResidualTransitionCut_obstructs_transitionCoherentData`
- `semanticResidualTransitionCutScanner_package`

G3 初期実績:

- `lake env lean research/lean/ResearchLean/QualitySurface/SemanticResidualTransitionCutScanner.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SemanticResidualTransitionCutScanner`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: `firstResidualTransitionCut?_some_pairCut`、`firstResidualTransitionCut?_some_obstructs_atlasTransitionClosure`、`firstResidualTransitionCut?_none_iff_noResidualTransitionCut` は標準 `propext` のみ。selected scanner witness と package は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。
- G3 形式化品質監査: pass。`none` は listed cut-free / complete edge-order no-cut に限定され、`none -> transition closure`、absolute minimality、H^1 class、global gluing claim は主張していない。
- G3.5 同期監査の revise に従い、`selectedFrontierFlatScanOrder`、`selectedFrontierFlatCutPairDecidable`、axiom audit、G2 revise 解決、genius support role 同期を追記した。

claim boundary は、finite supplied edge order、decidable cut predicate regime、selected semantic atom vocabulary、finite atlas skeleton、edge-family residual transition closure に留める。
`none` は residual transition cut absence の exactness であり、transition closure の十分条件ではない。

## 審判メモ

- G2 A: accept / base 70 / genius no。`supplied-order first residual transition cut scanner exactness` に寄せる条件つき。
- G2 B: accept / base 72 / genius no。新しい obstruction 原理ではないが finite transition scanner exactness frontier を閉じる。
- G2 C: revise / base 78 after narrowing / genius no。proof-carrying AAT obstruction certificate という rival 差分に限定する。
- G2 D: revise / base 72 / genius no。absolute minimality を避け、prefix no-cut exactness と complete edge-order no-cut theorem に限定する。
- G2 revise 解決: 候補名・本文・Lean theorem は `supplied finite edge order` 相対に限定し、`minimality` は `PrefixBeforeFirstCut` / `prefixClear` のみとした。`none -> transition closure`、global minimal cut、obstruction class、H^1、global gluing、ArchMap correctness、runtime repair synthesis は claim から外した。
- unchecked: 実コード全体の品質、source extraction completeness、canonical semantic ontology、tooling runtime extraction、UI / dashboard correctness、general obstruction class theorem。

## 追加 required fields

- `mathematical_interest`: residual transition cut を finite edge-order diagnostic selector として読む。
- `goal_advancement`: Cycle 89 cut certificate を scanner exactness layer へ上げ、open genius target の detector/certificate support node を作る。
- `planned_theorem_names`: `firstResidualTransitionCut?_some_cut`, `firstResidualTransitionCut?_none_iff_noResidualTransitionCut`, `semanticResidualTransitionCutScanner_package`
- `visible_projection`: listed atlas edge row / dashboard-like edge diagnostic / component-level edge surface。
- `protected_structure`: semantic residual-present source、residual-free target、active edge family、finite edge-order completeness、proof-carrying cut certificate。
- `exactness_or_minimality_claim`: supplied finite edge order に相対した first cut / prefix-clear exactness。complete edge order の下で `none` は `ResidualTransitionCut` 不在と同値。
- `nonfaithfulness_or_failure_mode`: visible edge row や scalar diagnostic は、returned edge が semantic residual cut certificate を持つことを自動では保持しない。
- `previous_cycle_delta`: Cycle 89 の finite atlas cut witness を supplied-order scanner exactness theorem に変換する。
- `rival_stress_test`: rival は edge/violation/witness を示せても、chosen semantic atom vocabulary 上の `some -> ResidualTransitionCut -> closure obstruction` と `none -> no cut` を Lean theorem として保持しない。
- `genius_potential`: support-cycle。1000 点 unlock ではなく、future obstruction-class theorem の input node。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: finite atlas obstruction を proof-carrying diagnostic selector へ変換する certificate-selector layer。
- `genius_support_map_sync`: tracking Issue #2348 の open genius target は `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。今回の result は unlock condition ではなく、target theorem に必要な finite detector / certificate-selector node として同期する。
- `genius_unlock_condition_remaining`: finite obstruction class、coboundary-like equivalence、vanishing/nonvanishing criterion、または local-pass/global-fail classification が未到達。

## 関連

- `research/ideas/g-aat-quality-surface-01-residual-transition-cut-theorem.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-edge-transition-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-indexed-transport.md`
- planned report section: `Cycle 90: Supplied-order residual transition cut scanner exactness`

## 進捗ログ

- 2026-06-23: Cycle 90 G1 で scanner exactness / order-relative prefix-clear 候補を採択。obstruction 1-preclass は次候補として温存。
- 2026-06-23: G2 審判に従い、canonical/global minimality、`none -> closure`、H^1 obstruction class claim を外し、supplied finite edge order 相対の scanner exactness に限定した。
- 2026-06-23: Lean 証拠を `SemanticResidualTransitionCutScanner.lean` に固定し、単体 `lake env lean` が通った。
- 2026-06-23: module build、ResearchLean、G3 公理監査、G3 形式化品質監査が pass。
- 2026-06-23: G3.5 revise に従い、カードに helper declaration、axiom audit、G2 revise 解決、genius support map 同期を追記。
