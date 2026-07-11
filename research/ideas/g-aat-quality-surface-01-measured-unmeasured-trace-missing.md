---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: traceability, quality-surface, multi-axis-signature, computability, ridge-fold
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
origin: G1-quality-surface-cycle-5
tags: [quality-surface, measured-zero, unmeasured, trace-missing, scalar-collapse]
created: 2026-06-20
cycle: 5
lean: research/lean/ResearchLean/AG/QualitySurface/StateSeparation.lean
---

# Measured-zero / unmeasured / trace-missing separation

## 主張

有限 certificate calculus において、同じ visible scalar reading `0` と同じ selected verdict を持つ三つの
certificate 状態を構成する。

1. `measured-zero`: selected predicate は測定され、actual measurement として zero certificate を持つ。
2. `unmeasured`: selected profile / certificate selector の対象外で、actual measurement を持たない。
3. `trace-missing`: selected support は存在し、actual measurement はあるが、partial trace field 上で利用可能な trace token が欠けている。

visible scalar `0` は actual measurement ではなく lossful display convention として定義する。
これら三状態は scalar reading と verdict では区別できないが、actual measurement、selector state、
selected support、trace status、repair / explanation obligation によって分離される。従って scalar reading /
verdict projection は certificate state に faithful ではない。

## 候補種別

`orientation`

## 依拠

- `research/goals/G-aat-quality-surface-01.md` の `G-aat-quality-surface-01`
- `docs/note/aat_quality_surface.md` の measured zero / unmeasured 区別、trace field、reading fold
- cycle 2 の `research/lean/ResearchLean/AG/QualitySurface/ScalarCollapse.lean`
- cycle 4 の `research/lean/ResearchLean/AG/QualitySurface/TraceTransport.lean`

## 非自明性

単なる enum の場合分けではなく、同じ scalar fiber と同じ verdict の下で、測定済みゼロ、未測定、trace 欠落が
異なる構造的条件と obligation を持つことを固定する。`unmeasured` は zero certificate ではなく selector outside
として扱い、`trace-missing` は selected support と partial trace field の欠落として扱う。visible zero は
certificate geometry の state を復元せず、Quality Surface の穴、空白、ゼロ高さ、trace 欠落を同じ数値に潰してしまう。

## 数学的興味

cycle 2 は scalar reading が support / repair frontier に faithful でないことを示した。cycle 4 は support
transport と trace transport を分離した。この候補はその合流点として、zero-looking surface が実際には
measurement-state stratification を持つことを finite witness として固定する。

## GOAL への前進

loss-aware visualization、traceability、multi-axis signature、ridge-fold のカテゴリを増やす。Quality Surface の
visible scalar layer の下に、測定状態・trace 状態・obligation 状態を保持する必要を示す。

## SCORE 見込み

- `score_reason`: 三つの state を同じ scalar/verdict fiber 内で分離し、unmeasured が actual zero ではないこと、
  trace-missing が selected support と partial trace field に戻ること、trace-missing 専用の faithfulness 否定
  theorem まで Lean で固定し、loss-aware visualization と finite trace frontier を前進させる。
- `dullness_risk`: `Option Nat` や enum の場合分けだけでは弱い。certificate tuple に visible scalar、
  actual measurement、selector state、selected support、trace status、repair/explanation obligation を持たせ、
  projection nonfaithfulness と state distinctness を theorem として示す。
- `proof_or_evidence_plan`: finite `QualityCertificate` を三つ置き、tuple から `visibleScalarReading`、`verdict`、
  `actualMeasurement?`、`selectorState`、`selectedSupport?`、`traceStatus`、`obligation` を読む。
  三つが scalar/verdict で一致すること、`unmeasured` は `actualMeasurement? = none` であること、
  `trace-missing` は selected support と `TraceTransport.TraceMissingOn` で定義された missing trace を持つこと、
  protected components では互いに異なること、`ScalarVerdictFaithfulToState` と
  `ScalarVerdictFaithfulToTraceMissing` が成り立たないことを証明する。

## CS / SWE への帰結

UI で同じ `0` や同じ acceptable verdict に見える場合でも、測定済みゼロ、未測定、trace 欠落では次に取る行動が異なる。
Quality Surface は zero value だけでなく、state / trace / obligation を drill-down 可能な certificate として保持する必要がある。

## 証明・根拠の見込み

Lean では `MeasurementState`、`SelectorState`、`TraceStatus`、`ObligationKind` を有限型として定義する。
`measuredZeroCert`、`unmeasuredCert`、`traceMissingCert` はすべて visible scalar reading `0` と selected verdict
`acceptable` を持つ。一方で、`actualMeasurement?`、selector state、selected support、trace status、obligation は異なる。
`measuredZero_has_actual_zero`、`unmeasured_has_no_actual_measurement`、
`traceMissing_has_selected_support_and_missing_trace`、`SelectedTraceMissing`、
`zeroLooking_certificates_state_separated`、`state_components_pairwise_distinct`、
`scalarVerdict_not_faithful_to_certificateState`、
`scalarVerdict_not_faithful_to_selectedTraceMissing` を証明する。

## 審判メモ

- 厳密性: G2 revise 後、trace-missing を `TraceTransport.TraceMissingOn` による導出条件として
  `ScalarVerdictFaithfulToTraceMissing` の反例に直接参加させた。
- 研究価値: cycle 2 の scalar collapse と cycle 4 の trace transport を、zero-looking surface の
  measurement-state stratification へ接続する。
- repo 全体価値: Research sandbox の Lean 証拠と paper seed として採用する。

## 関連

- `Scalar-collapse separation by support antichains`
- `Trace-natural certificate transport bridge`
- `finite trace-locus certificate grid`

## 進捗ログ

- 2026-06-20: cycle 5 の G1 候補生成から審判対象として作成。
- 2026-06-20: G2 revise を受け、visible scalar を actual measurement から分離し、`unmeasured` を
  selector outside / no actual measurement、`trace-missing` を selected support + partial trace field failure として明示。
- 2026-06-20: `SelectedTraceMissing` と `ScalarVerdictFaithfulToTraceMissing` を追加し、trace-missing が
  scalar/verdict projection から復元できないことを Lean で証明。
