---
status: picked
goal: G-aat-quality-surface-01
candidate_type: computability
capability_category: traceability/repair-potential/computability/quality-surface/certificate-transport
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle21
tags:
  - source-ref
  - repair-trajectory
  - finite-codebase-trace
created: 2026-06-20
---

# Finite codebase trace repair trajectory with exact frontier collapse

## 主張

supplied finite source-ref packet family 上で、missing source-ref locus ちょうどを埋める
pointwise repair action を定義すると、partial packet は repaired packet へ移り、source-ref missing
locus と repair frontier は storage singleton から empty へ collapse する。一方で scalar / verdict /
code-support の visible surface は repair 前後で同一に見えるため、repair progress は protected
source-ref reading を保持する場合にだけ検出できる。

主張は supplied finite packet、declared repair action、source-ref missing locus、exact repair frontier
に相対化する。実コード全体の repair reachability、source extraction completeness、ArchMap correctness、
任意 codebase の repair planning、tooling completeness は結論しない。

## 候補種別

`computability`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/CodebaseTracePacket.lean`
- `research/lean/ResearchLean/AG/QualitySurface/ReadingAdequacy.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SourceRefTupleBridge.lean`
- `CodebaseTracePacket.partialPacket`
- `CodebaseTracePacket.fullPacket`
- `partialTrace_storage_missing_locus`
- `partialTrace_missing_locus_exact_storage`
- `partialTrace_repair_frontier_matches_missingRefs`
- `fullTrace_has_no_missing_sourceRef_locus`
- `surfaceReading_not_faithful_to_codebaseTraceFrontier`
- `sourceRefLocusAware_faithful_to_repairFrontier_of_exact`

## 非自明性

Cycle 9 は full / partial packet の static 分離と exact repair frontier を固定した。この候補は、
その差分を repair action と repair trajectory として読み直し、frontier collapse と visible surface
nonfaithfulness を同じ theorem package に束ねる。

単なる `fullPacket` / `partialPacket` の再掲にしないため、repair action は pointwise law を持つ。
具体的には、pre-state の missing locus ちょうどを repair support とし、missing atom には repaired
token を供給し、non-missing atom の source-ref entry は保存し、code support / scalar / verdict は
保存する。その action を `partialPacket` に適用した post-state について、missing locus empty、
repair frontier empty、visible trajectory nonfaithfulness、protected reading による repair progress
detection を Lean statement として明示する。

## 数学的興味

Quality certificate を静的状態ではなく、protected trace evidence が変化する有限 trajectory として読む。
repair frontier は missing source-ref locus の exact support として計算され、repair action によって
empty frontier へ collapse する。

## GOAL への前進

finite codebase trace example、repair-potential、traceability、computability を接続し、loss-aware
visualization が repair progress を保持するために protected source-ref reading を必要とすることを示す。

## SCORE 見込み

- `score_reason`: G2-B/C は base 65/75 を認めたが、G2-A が static full/partial packet の再掲に落ちる危険を指摘したため、revised candidate は base 60 / final 120 に下げる。
- `dullness_risk`: medium-high。static full/partial packet の再掲に落ちないよう、pointwise repair action、exact fill condition、non-missing source-ref preservation、frontier collapse、trajectory reading nonfaithfulness を required evidence にする。
- `proof_or_evidence_plan`: `CodebaseTraceRepairTrajectory.lean` に `SourceRefRepairAction`、`PreservesNonMissingSourceRefs`、`FillsExactlyMissingSourceRefs`、`repairPacket`、post-state theorem、frontier collapse theorem、visible trajectory nonfaithfulness theorem、protected reading detection theorem、package theorem を置く。

## CS / SWE への帰結

source-ref missing locus を repair action の exact support として読むと、修復前後の visible surface が同じでも、
protected source-ref reading は repair progress を検出できる。これは finite supplied packet の数学的
witness であり、実コード全体の自動修復や tooling completeness は主張しない。

## 証明・根拠

Lean proof は `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceRepairTrajectory.lean` に閉じた。
`research/lean/ResearchLean.lean` はこの Research evidence file を import する。

主要 theorem / declaration:

- `SourceRefRepairAction`
- `PreservesNonMissingSourceRefs`
- `FillsExactlyMissingSourceRefs`
- `repairPacket`
- `storageRepairAction`
- `storageRepairAction_preserves_nonMissingRefs`
- `storageRepairAction_exactly_fills_missingRefs`
- `repairPacket_repairFrontierExact`
- `storageRepairPacket`
- `repairTrajectory_visibleSurface_preserved`
- `repairTrajectory_missingLocus_collapses`
- `repairTrajectory_repairFrontier_collapses`
- `repairTrajectory_repairFrontierExact`
- `repairTrajectory_available_on_support`
- `repairTrajectory_sourceRefMissing_changed`
- `repairTrajectory_repairFrontier_changed`
- `repairTrajectory_protectedReading_detects_progress`
- `repairTrajectory_visibleSurface_not_faithful`
- `codebaseTraceRepairTrajectory_package`

Planned report theorem names match the same declaration set, with
`codebaseTraceRepairTrajectory_package` as the report package theorem. The report is not updated until
G4 confirms or reduces the final SCORE.

固定された内容:

- `SourceRefRepairAction` は repair support、post-state source-ref table、post-state obligation を持つ。
- `PreservesNonMissingSourceRefs` は pre-state で存在した source-ref entry を action が保存する pointwise law である。
- `FillsExactlyMissingSourceRefs` は repair support が pre-state missing locus と一致し、missing atom を実際に埋め、non-missing entry を保存することを bundled にする。
- `repairPacket` は scalar / verdict / code support を保ち、source-ref table と obligation を action から更新し、post-state repair frontier を post-state missing locus として再計算する。
- `storageRepairAction_exactly_fills_missingRefs` は partial packet の storage missing locus ちょうどを埋め、endpoint / worker source-ref entry を保存する。
- `repairTrajectory_missingLocus_collapses` と `repairTrajectory_repairFrontier_collapses` は post-state で missing locus と repair frontier が empty になることを示す。
- `repairTrajectory_visibleSurface_preserved` は repair 前後で visible support surface が同じであることを示す。
- `repairTrajectory_protectedReading_detects_progress` は source-ref-locus-aware reading では repair progress が検出されることを示す。

検証:

- `focused Lean check: ResearchLean/AG/QualitySurface/CodebaseTraceRepairTrajectory.lean`: pass。
- `Research package build`: pass。
- `.tmp/codebase_trace_repair_trajectory_axioms.lean` の `#print axioms`: listed declarations are all
  `does not depend on any axioms`。`sorryAx`、`propext`、`Classical.choice`、`Quot.sound` は出ていない。
- G3 公理検査: pass。
- G3 Lean 形式化品質監査: pass。`repairPacket` は pre packet から visible surface を保存しつつ
  repaired source-ref table で post-state frontier を再計算しており、単なる `fullPacket` relabel ではない。

## 審判メモ

- 厳密性: G2-A は revise、base 60。`repairPacket` が単に `fullPacket` を返すだけの vacuous trajectory にならないよう、pointwise action laws、non-missing token preservation、exact fill、post-state recomputation を required evidence とした。
- 研究価値: G2-B は accept、base 65。static packet witness を repair-potential trajectory へ変換する価値はあるが、新しい codebase trace example そのものではないため base 80 は高すぎる。
- repo 全体価値: G2-C は accept、base 75。Research / Lean / paper seed / future tooling explanatory surface として有効。ただし tooling completeness や実コード修復可能性に読ませないこと。

## 関連

- `research/ideas/g-aat-quality-surface-01-source-ref-packet.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-tuple-bridge.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-packet-transport.md`
- `research/reports/G-aat-quality-surface-01.md`

## 進捗ログ

- 2026-06-20: Cycle 21 candidate card 作成。
- 2026-06-20: G2-A revise を反映し、pointwise repair-action law、non-missing source-ref preservation、exact fill、post-state recomputation を required evidence に追加し、base 60 / final 120 に下げた。
- 2026-06-20: G2-A 再審判 accept。`CodebaseTraceRepairTrajectory.lean` を追加し、単体 Lean、`ResearchLean`、axiom harness、G3 公理検査、G3 Lean 形式化品質監査を通した。
