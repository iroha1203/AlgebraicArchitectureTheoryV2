---
status: picked
goal: G-aat-quality-surface-01
candidate_type: computability
capability_category: traceability, profile-curvature, certificate-transport, repair-potential, ridge-fold
expected_base_score: 85
expected_evidence_multiplier: 2.0
expected_final_score: 170
evidence_stage: proved-in-research
origin: G1-quality-surface-cycle-7
tags: [quality-surface, trace-curvature, trace-locus, profile-square, repair-frontier]
created: 2026-06-20
cycle: 7
lean: Formal/AG/Research/QualitySurface/TraceCurvature.lean
---

# Trace-curvature detector

## 主張

有限 profile square において、lower-left の trace certificate から upper-right へ向かう二つの path を構成する。
二つの path は upper-right で同じ visible scalar reading、同じ selected verdict、同じ selected support を持つ。
しかし、law-then-cover path は trace complete のままで、cover-then-law path は database atom に trace gap を持ち、
その missing trace locus に対応する exact repair frontier を要求する。

従って Quality Surface の traceability は、頂点の scalar / verdict / support だけではなく、
profile change に沿う path-ordered trace locus / repair frontier の coherence を見なければならない。

## 候補種別

`computability`

## 依拠

- `research/GOALS.md` の `G-aat-quality-surface-01`
- cycle 3 の `Formal/AG/Research/QualitySurface/ProfileCurvature.lean`
- cycle 4 の `Formal/AG/Research/QualitySurface/TraceTransport.lean`
- cycle 6 の `Formal/AG/Research/QualitySurface/TraceLocus.lean`

## 非自明性

cycle 3 は profile square 上の support / repair curvature を示し、cycle 6 は同じ surface / support の下に trace locus
と repair frontier が隠れることを示した。この候補はそれらを統合し、profile square の path ordering が trace locus と
repair frontier の曲率として現れる finite detector を固定する。

## 数学的興味

Quality Surface の trace geometry は、support locus の静的 drill-down だけでなく、profile change の path coherence
としても読む必要がある。同じ upper-right surface に到達しても、path-ordered certificate transport が trace locus を
保つか欠くかで、repair frontier が変わる。

## GOAL への前進

traceability、profile-curvature、certificate transport、repair-potential、ridge-fold を同時に進める。
当時の active threshold 1000 に向けた cycle 7 として、cycle 3 / 4 / 6 の成果を trace-curvature detector に統合する。

## SCORE 見込み

- `score_reason`: 同じ upper-right scalar / verdict / support の下で、path ordering によって trace completeness と
  trace-missing exact repair frontier が分岐することを Lean で示し、visible surface が trace locus coherence と
  repair frontier に faithful でないことを証明する。
- `dullness_risk`: 単に二つの fields を置くだけでは弱い。typed profile square、two path composites、
  `TraceAvailableOn` / `TraceMissingOn`、exact repair frontier、trace-locus faithfulness 否定を theorem として固定する。
- `proof_or_evidence_plan`: `TraceProfile` square と typed `EdgeTransport` を置き、law-then-cover と cover-then-law の
  upper-right certificate を構成する。scalar/verdict/support の一致、law path の trace availability、cover path の
  missing trace、database repair frontier、trace locus / repair frontier nonfaithfulness、`TraceCurvatureCell` を証明する。

## CS / SWE への帰結

同じ final support と score に見える品質面でも、変更の順序によって trace evidence の欠落と repair frontier が変わる。
Quality Surface viewer / report は、最終点の値だけでなく path-ordered trace coherence を見せる必要がある。

## 証明・根拠の見込み

Lean では `TraceSquareCertificate`、typed `EdgeTransport`、`lawThenCover`、`coverThenLaw` を定義する。
`same_scalar_after_trace_paths`、`same_verdict_after_trace_paths`、`same_support_after_trace_paths`、
`lawThenCover_trace_available`、`coverThenLaw_trace_missing`、`coverThenLaw_repair_frontier_matches_missing_locus`、
`trace_square_not_faithful_to_trace_locus`、`trace_square_not_faithful_to_repair_frontier`、
`trace_curvature_cell` を証明する。

## 審判メモ

- 厳密性: typed profile square、two path composites、trace availability / missing、exact repair frontier、
  trace locus / repair frontier nonfaithfulness を Lean で固定した。
- 研究価値: cycle 3 の path-ordered profile curvature と cycle 6 の trace locus / exact repair frontier を、
  trace-curvature detector として統合する。
- repo 全体価値: Research sandbox の Lean 証拠、paper seed、future viewer の path-coherence 説明として採用する。

## 関連

- `Finite square cell profile-curvature detector`
- `Trace-natural certificate transport bridge`
- `Finite trace-locus certificate grid`

## 進捗ログ

- 2026-06-20: cycle 7 の G1 候補として作成。
- 2026-06-20: `TraceCurvature.lean` を追加し、`lake env lean Formal/AG/Research/QualitySurface/TraceCurvature.lean` と
  `lake build FormalAGResearch` の通過を確認。
- 2026-06-20: G2-A の補強提案を受け、repair frontier 側の faithfulness 否定も追加し、
  主要 theorem の axiom 依存がないことを確認。
