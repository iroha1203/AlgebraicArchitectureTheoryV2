---
status: picked
goal: G-aat-quality-surface-01
exploration_role: repair-hit scanner exactness / unhit source obstruction detection / genius-support convergence
candidate_type: unhit status-drop repair scanner theorem / mapped target obstruction certificate / all-hit exactness
capability_category: semantic-obstruction / status-drop-scanner / repair-hit-exactness / mapped-target-obstruction / genius-support
expected_base_score: 88
expected_evidence_multiplier: 2.0
expected_final_score: 176
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can list status drops or repair touches, but they do not prove that a finite source scanner is exact for all-hit repair obligations and that scanner hits map to target obstruction.
origin: cycle-104
tags: [quality-surface, semantic-repair, residual-cut, status-drop, scanner, repair-hitting, mapped-obstruction, genius-support]
created: 2026-06-23
cycle: 104
lean: proved-in-research
planned_report_section: "Cycle 104: Source unhit status-drop scanner exactness"
---

# Source Unhit Status-Drop Scanner Exactness

## 主張

source finite edge order 上で、old status drop かつ edge/source/target の三つの repair-hit loci がすべて
unhit である pair を scan する。

scanner が `some pair` を返すなら、その pair は explicit unhit old status drop であり、
mapped status-drop repair transport の下で target status drop、target canonical nonzero、transition closure /
transition-coherent data obstruction を与える。

complete source edge order 上で scanner が `none` を返すなら、すべての old status drops は
`ResidualCutHit` を満たす。逆に all-hit なら scanner は `none` である。

これは finite source-order-relative な repair-hit exactness であり、hit sufficiency、repair synthesis、
global minimality、target-wide order canonicity、vanishing-to-closure、true `H^1` / Cech / coboundary quotient、
status extraction、ArchMap/tooling correctness、runtime/UI correctness、whole-codebase quality は主張しない。

## 候補種別

`unhit status-drop repair scanner theorem` / `mapped target obstruction certificate` / `all-hit exactness`

## 依拠

- Cycle 100: mapped status-drop repair-hitting transport。
- Cycle 101: finite status-drop scanner exactness。
- Cycle 103: generated mapped source-order scanner surface。

## 非自明性

この cycle は target scanner `none` の説明責務ではなく、source 側で repair-hit obligation の未解消 witness を直接 scan する。
`some` は target obstruction certificate へ map され、`none` は complete source order に相対化して all-hit と同値になる。

## 数学的興味

repair-hit necessity を有限探索可能な exact scanner として切り出す。
これは semantic repair-gluing obstruction theorem に向けて、未 hit の old status drop を target obstruction として抽出し、
未検出なら all-hit obligation が成立する、という computational obstruction/explanation layer である。

## GOAL への前進

source certificate geometry 上で repair-hit obligations の failure witness を scan し、それを target obstruction へ transport できる。
quality surface の「green claim」に対し、未 hit witness の存在 / all-hit の二分を Lean theorem として与えた。

## ライバルに対する有効性

ADL、static analyzer、dashboard、AI summary は status drop や repair touch を列挙できる。
しかし、source-complete finite scanner の `none` が all-hit と同値であり、`some` が mapped target obstruction を与えることを証明しない。

## SCORE 見込み

- `score_reason`: repair-hit obligation を直接 finite scanner exactness にし、some/none の両側を target obstruction / all-hit に接続した。
- `dullness_risk`: scanner pattern の再利用に見える危険はある。unhit triple predicate、mapped target obstruction、all-hit exactness を一つの package にまとめて補強した。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/QualitySurface/SemanticResidualUnhitStatusDropScanner.lean` で source unhit scanner exactness と selected witness を証明する。

## CS / SWE への帰結

repair が説明すべき old status drops を finite order で scan し、未 hit なら target obstruction を具体化する。
未検出なら all-hit obligation が成立するため、repair audit の green claim と red witness を同じ scanner surface で扱える。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/QualitySurface/SemanticResidualUnhitStatusDropScanner.lean` に固定した。

- `UnhitMappedOldStatusDropPair`
- `firstUnhitMappedOldStatusDrop?`
- `firstUnhitMappedOldStatusDrop?_some_mem`
- `firstUnhitMappedOldStatusDrop?_some_pair`
- `firstUnhitMappedOldStatusDrop?_some_maps_to_newStatusDrop`
- `firstUnhitMappedOldStatusDrop?_some_mappedCanonicalNonzero`
- `firstUnhitMappedOldStatusDrop?_some_obstructs_mappedTransitionClosure`
- `firstUnhitMappedOldStatusDrop?_some_obstructs_mappedTransitionCoherentData`
- `ListedUnhitMappedOldStatusDropsClear`
- `firstUnhitMappedOldStatusDrop?_none_iff_listedClear`
- `firstUnhitMappedOldStatusDrop?_none_iff_allMappedOldStatusDropsHit`
- `selectedUnhitMappedOldStatusDropPairDecidable`
- `selected_firstUnhitMappedOldStatusDrop`
- `selected_firstUnhitMappedOldStatusDrop_maps_to_extendedStatusDrop`
- `selected_firstUnhitMappedOldStatusDrop_mappedCanonicalNonzero`
- `selected_firstUnhitMappedOldStatusDrop_obstructs_extendedTransitionClosure`
- `selected_firstUnhitMappedOldStatusDrop_obstructs_extendedTransitionCoherentData`
- `selected_firstUnhitMappedOldStatusDrop_none_iff_allHits`
- `semanticResidualUnhitStatusDropScanner_package`

検証実績:

- `lake env lean research/lean/ResearchLean/QualitySurface/SemanticResidualUnhitStatusDropScanner.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SemanticResidualUnhitStatusDropScanner`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: generic theorem family は標準 `propext` のみ。selected witness と package は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。

claim boundary は、finite source edge order、explicit unhit triple predicate、mapped transport、scanner some-to-target-obstruction、
complete source order scanner none-to-all-hit exactness に限定する。
unchecked: hit sufficiency、repair synthesis、global minimality、target-wide order canonicity、vanishing-to-closure、
true H1/cohomology、Cech quotient、coboundary quotient、status extraction、ArchMap correctness、runtime/UI correctness、
whole-codebase quality、arbitrary atlas category/functoriality。

## 審判メモ

- G1: accept。repair-hit obligation そのものを source 側で scan し、`some` を mapped target obstruction、`none` を complete source order 下の all-hit に接続する実用的前進として base 88 / final +176 を推奨。
- G2: accept。rival は status drop と repair touch を列挙できても、`some` to mapped target obstruction certificate と `none iff all-hit` を同じ theorem surface として持たない。score range +172 to +176、提案 +176 は妥当。
- strong genius-support。genius unlock ではなく、finite semantic repair-gluing obstruction theorem へ向けた support-cycle。

## 追加 required fields

- `mathematical_interest`: repair-hit obligation を finite scanner exactness と target obstruction transport に分解する。
- `goal_advancement`: quality surface の unhit witness / all-hit explanation を同じ Lean scanner で扱える。
- `planned_theorem_names`: `firstUnhitMappedOldStatusDrop?_none_iff_allMappedOldStatusDropsHit`, `firstUnhitMappedOldStatusDrop?_some_mappedCanonicalNonzero`, `semanticResidualUnhitStatusDropScanner_package`
- `visible_projection`: source edge order、unhit repair loci、scanner some/none、mapped target obstruction。
- `protected_structure`: explicit unhit triple、status-drop predicate、mapped transport preservation、all-hit exactness。
- `exactness_or_minimality_claim`: complete source order に相対化した some/none exactness。minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: scanner none without complete source order does not certify all-hit。
- `previous_cycle_delta`: Cycle 103 の generated mapped order surface から、source-side unhit repair witness scanner へ進めた。
- `rival_stress_test`: rival は repair touches を表示できても scanner none iff all-hit と some-to-target-obstruction を theorem として出さない。
- `genius_potential`: strong support-cycle。1000 点 unlock ではなく、future finite semantic repair-gluing obstruction theorem の repair-hit scanner layer。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: unhit repair witness と all-hit explanation を finite scanner exactness として提供する。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-status-drop-scanner.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-mapped-status-drop-scanner-order.md`
- planned report section: `Cycle 104: Source unhit status-drop scanner exactness`

## 進捗ログ

- 2026-06-23: Cycle 104 candidate として source unhit status-drop scanner exactness を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualUnhitStatusDropScanner.lean` に固定し、単体
  `lake env lean`、module build、`lake build ResearchLean`、axiom 監査が通った。
