---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: certificate-transport / obstruction / traceability / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / architecture conformance checker can report route or view failures, but this result turns the selected repair/transport criterion into a finite law-deletion matrix that explains which visible, obligation, table, and action-naturalness laws are independently needed for source-ref exact visualization.
origin: G-aat-quality-surface-01-cycle42
tags: [quality-surface, repair-transport, exact-visualization, minimality]
created: 2026-06-21
cycle: 42
lean: proved-in-research
---

# Exact-visualization criterion and four-law selected minimality matrix

## 主張

`SourceRefExactVisualization` は、packet-induced tuple view 上で `TupleVisibleVisualizationEquivalent` と protected `RouteDefectSupportEmpty` の同時成立と同値である。さらに selected finite repair/transport square において、visible law、obligation law、transport table law、action naturality はそれぞれ独立に削れるが、各 deletion cell は異なる protected / visible defect を生み、source-ref exact visualization を阻害する。

## 候補種別

`unification`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/SourceRefExactVisualization.lean`
- `research/lean/ResearchLean/AG/QualitySurface/LawfulRepairTransportCommutator.lean`
- `research/lean/ResearchLean/AG/QualitySurface/TransportTableLawRouteLocalization.lean`
- `research/lean/ResearchLean/AG/QualitySurface/VisibleLawDeletionProtectedZero.lean`
- `research/lean/ResearchLean/AG/QualitySurface/RouteDefectSupport.lean`

## 非自明性

Cycle 24 の exactness criterion、Cycle 37 の table-law deletion、Cycle 39 の visible-law deletion を単に並べるのではなく、新規に obligation-law deletion cell と action-naturality deletion cell を追加し、四つの law が selected commutator exactness に対して別々の失敗 mode を持つことを同じ theorem package に束ねる。

## 数学的興味

lawful repair/transport square の条件を、十分条件としての便利な仮定ではなく、selected finite witness 上で削ると何が壊れるかを表す minimality matrix として読める。visible failure、obligation holonomy、table defect、action mismatch が同じ `RouteDefectSupport` / exact visualization criterion の中で比較可能になる。

## GOAL への前進

この候補は `certificate-transport`、`obstruction`、`traceability`、`quality-surface` を前進させ、Quality Surface の lawful repair/transport criterion minimality frontier を埋める。

## ライバルに対する有効性

ADL / conformance checker は route mismatch や view failure を検出できるが、visible law、obligation law、table law、action naturality のどれを削るとどの protected component が exact visualization を壊すかを、finite certificate geometry の law-deletion matrix として返すわけではない。この結果はその差分を Lean 証拠として固定する。

## SCORE 見込み

- `score_reason`: lawful criterion minimality matrix frontier に対応し、既存 two-cell witness に obligation/action cells を足して四 law を比較できる。ただし exactness criterion は既存同値の合成でもあるため、G2 厳密性審判に従い base 70 に下げる。Lean proof が sorry-free で通れば multiplier 2.0。
- `dullness_risk`: 既存 witness の再包装だけなら低価値。新規 obligation/action deletion cells と `exactVisualization_iff_visible_emptyRouteSupport` を同時に入れることで回避する。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/AG/QualitySurface/ExactVisualizationCriterionMinimality.lean` に selected packet updates、stale transported action、route support defects、four-law matrix package を証明する。

## CS / SWE への帰結

loss-aware quality view で、見た目の flatness と protected exactness を分けるだけでなく、どの commutator law が失敗したかを drill-down する根拠になる。これは UI / tooling claim ではなく、finite certificate surface の theorem として読む。

## 証明・根拠の見込み

Lean file: `research/lean/ResearchLean/AG/QualitySurface/ExactVisualizationCriterionMinimality.lean`

Planned / proved declarations:

- `exactVisualization_requires_visible_and_emptyRouteSupport`
- `visible_and_emptyRouteSupport_suffices_exactVisualization`
- `exactVisualization_iff_visible_emptyRouteSupport`
- `obligationLawDeletion_cell`
- `actionNaturalityDeletion_cell`
- `fourLawSelectedMinimalityMatrix`
- `exactVisualizationCriterionMinimality_package`

Verification:

- `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/ExactVisualizationCriterionMinimality.lean`: pass
- `cd research/lean && lake build ResearchLean`: pass
- `#print axioms` for the reported declarations: no axioms
- `sorryAx`: none
- Formal boundary: `research/lean/ResearchLean` only; `Formal/AG` proper is imported but not edited.

## 審判メモ

- 厳密性: `accept`、base 70。exactness criterion は既存同値の合成に近いが、新規 obligation/action deletion cells は rename ではない。selected finite witness として書くこと。
- 研究価値: `accept`、base 80。Cycle 24/37/39/38 の exactness、route support、deletion cell を一つの criterion package に束ねる。
- repo 全体価値: `accept`、base 75。paper seed 強化として価値あり。ただし global minimality や tooling 実装済み capability として言い過ぎない。
- ライバル比較: `accept`、base 80。ADL / conformance checker との差分として、law deletion ごとの visible/protected defect localization を theorem-level で固定する。

## 関連

- Cycle 37: `Transport table-law deletion localizes the selected route defect`
- Cycle 39: `Visible-law deletion separates protected zero holonomy from source-ref exact visualization`
- Cycle 41: `Minimal internal excursion support family hitting theorem`

## 進捗ログ

- 2026-06-21: Cycle 42 候補として作成。Lean 単体チェックは `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/ExactVisualizationCriterionMinimality.lean` で pass。
- 2026-06-21: G2 四審判は全員 `accept`。厳密性審判に従い expected score を base 70 / final 140 へ下げ、obligation deletion cell に action naturality 保存を明記。
- 2026-06-21: G3 公理検査は pass。reported declarations はすべて no axioms / no `sorryAx`。形式化品質監査も pass。
- 2026-06-21: G3.5 sync audit は `synced`。G4 SCORE audit は `confirm`、base 70、multiplier 2.0、penalty 0、final 140。`research/reports/G-aat-quality-surface-01.md` Cycle 42 と total SCORE 5250 を更新。
