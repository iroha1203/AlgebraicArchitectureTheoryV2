---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: traceability, quality-surface, certificate-transport, repair-potential, ridge-fold
expected_base_score: 75
expected_evidence_multiplier: 2.0
expected_final_score: 150
evidence_stage: proved-in-research
origin: G1-quality-surface-cycle-6
tags: [quality-surface, trace-locus, missing-trace, repair-frontier, scalar-collapse]
created: 2026-06-20
cycle: 6
lean: research/lean/ResearchLean/QualitySurface/TraceLocus.lean
---

# Finite trace-locus certificate grid

## 主張

有限 support 上で、同じ visible scalar reading、同じ selected verdict、同じ selected support を持つ二つの
certificate を構成する。一方は selected support 全体で trace token を持ち、もう一方は selected support 内の
database atom に trace token を欠く。

この差分は scalar / verdict / support からは復元できないが、missing trace locus と repair frontier では
区別される。従って Quality Surface の traceability surface は、単に「trace missing がある」という state label
だけでなく、support 内のどこが traced で、どこが missing で、どの repair frontier が強制されるかを保持する必要がある。

## 候補種別

`bridge`

## 依拠

- `research/goals/G-aat-quality-surface-01.md` の `G-aat-quality-surface-01`
- cycle 4 の `research/lean/ResearchLean/QualitySurface/TraceTransport.lean`
- cycle 5 の `research/lean/ResearchLean/QualitySurface/StateSeparation.lean`

## 非自明性

cycle 5 は trace-missing を zero-looking state から分離した。この候補はさらに、同じ selected support の内部を
available trace locus と missing trace locus に分解する。trace missing を単一ラベルにせず、support atom ごとの
partial trace field と repair frontier へ落とす点が新しい。

## 数学的興味

Quality Surface の traceability は、global な traced / missing verdict ではなく、support 上の locus decomposition
として読むべきである。同じ scalar fiber と selected support fiber の中でも、missing locus が違えば repair frontier は
変わる。これは trace-aware certificate geometry の局所性を有限例として固定する。

## GOAL への前進

traceability、repair-potential、ridge-fold、multi-axis signature の frontier を進める。cycle 4 の trace transport と
cycle 5 の state separation を、support 内の missing locus / repair frontier という drill-down surface へ接続する。

## SCORE 見込み

- `score_reason`: 同じ visible surface と selected support の下で、full trace coverage と partial trace gap が
  分かれることを Lean で示し、missing trace locus と exact repair frontier が scalar / verdict / support projection から
  復元できないことを証明する。
- `dullness_risk`: 単なる `Option` の missing 例だけでは弱い。`TraceAvailableOn` / `TraceMissingOn` との接続、
  locus partition、repair frontier coverage、projection nonfaithfulness を theorem として固定する。
- `proof_or_evidence_plan`: finite support atom `{api, database, queue}` を置き、full trace certificate と partial trace
  certificate を構成する。`TraceAvailableLocus`、`TraceMissingLocus`、`RepairCoversMissingTrace` を定義し、
  partition、full availability、partial missing、repair coverage、exact frontier、surface/support nonfaithfulness を証明する。

## CS / SWE への帰結

同じ score / verdict / selected support を表示していても、trace token が欠けている atom が一つあるだけで次の作業は変わる。
Quality Surface viewer / report は support-level trace locus と repair frontier を drill-down できる形で保持する必要がある。

## 証明・根拠の見込み

Lean では `TraceLocusCertificate` に visible scalar、verdict、selected support、trace field、repair frontier、obligation を持たせる。
`trace_locus_partition`、`trace_available_missing_disjoint`、`fullTrace_available_on_support`、
`partialTrace_missing_on_support`、`partialTrace_missing_locus_exact_database`、
`partialTrace_repair_covers_missing`、`partialTrace_repair_frontier_matches_missing_locus`、
`surfaceSupport_not_faithful_to_missing_locus`、`surfaceSupport_not_faithful_to_repair_frontier`、
`same_surface_support_but_trace_locus_diff` を証明する。

## 審判メモ

- 厳密性: G2-A revise 後、repair frontier が missing trace locus と exactly 一致する theorem と、
  repair frontier 自体の nonfaithfulness theorem を追加した。
- 研究価値: cycle 4 の trace transport と cycle 5 の trace-missing state separation を、support 内の
  trace locus / repair frontier 分解へ進める。
- repo 全体価値: Research sandbox の Lean 証拠と future viewer / paper seed として採用する。

## 関連

- `Trace-natural certificate transport bridge`
- `Measured-zero / unmeasured / trace-missing separation`
- `Trace curvature detector`

## 進捗ログ

- 2026-06-20: cycle 6 の G1 候補として作成。
- 2026-06-20: `TraceLocus.lean` を追加し、`lake env lean research/lean/ResearchLean/QualitySurface/TraceLocus.lean` と
  `lake build ResearchLean` の通過を確認。
- 2026-06-20: G2-A / G3 revise を受け、repair frontier exactness と repair frontier nonfaithfulness を追加し、
  主要 theorem の axiom 依存がないことを確認。
