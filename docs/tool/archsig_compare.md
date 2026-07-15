# ArchSig compare report guide

`archsig compare` は 2 つの `archsig analyze` run directory を読み、record 水準の差分を出力する。
`--refinement <refinement-comparison/v0.5.3>` を供給した場合は、coarse / fine の
`complexFingerprint` がそれぞれ base / head run の正規化有限複体 fingerprint
(`inputDigests.siteCoverDigest.sha256`)と一致することを検査してから、class-zero reading を追加する。
この fingerprint 検査により、site cover が異なる coarse→fine run でも refinement 経路を受理できる。
不一致は `COMPARISON_DATA_CONTRACT_VIOLATION` で fail-closed とする。
fingerprint 不一致かつ refinement 不在の場合は `profileConclusionCode: TWO_PROFILES_REPORTED_SEPARATELY` を記録する。

SAGA の run 内 H¹ comparison は `RepairPlan.comparison.h1ComparisonData` が所有する。
explicit comparison では `cochainMap.degreeZero` / `degreeOne` / `degreeTwo.basisMap` と
`degreeTwo.zeroImage` の有限写像表を validator が再計算し、適合条件を満たす場合だけ
analyze の転送 invariant が立つ。
compare の run-pair 記録はこの run 内写像を自動生成しない。

SAGA の run 内 comparison は、source の `saga.residual-class` が未計測なら
`silence_by_design`、reason `residual_class_prerequisite_not_measured` と
不足している入力slot (`complex.tripleOverlaps`, `coefficient`,
`trueSheafCertificate`, `gluingData`) を案内する `whatNext` を記録する。この前提未供給は比較違反として扱わない。source class が計測済みの場合だけ、有限 map の適合検査または target class の zero predicate の検査へ進む。

`h1-comparison-transfer` は `ag.saga-comparison` evaluator が所有する computed invariant であり、`contract` を必須とする。contract は `incidenceBridgeKind`、`h1ComparisonDataKind`、`normalizedComplexFingerprint`（文字列）と、`classPrerequisite`、`targetClassComputed`、`contractChecked`（真偽値）の6フィールドを持ち、未知フィールドや別 evaluator への付け替えは受理しない。
不一致になった場合だけ `COMPARISON_DATA_CONTRACT_VIOLATION` を記録する。

## Inputs and outputs

Input run directory must contain:

- `archsig-run-manifest.json`
- `normalized-archmap.json`
- `archsig-measurement-packet.json`

Command:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- compare \
  --base-run .tmp/base-run \
  --head-run .tmp/head-run \
  --out-dir .tmp/archsig-compare
```

Outputs:

- `archmap-diff.json` with schema `archmap-diff/v0.5.3`
- `archsig-comparison-report.json` with schema `archsig-comparison-report/v0.5.3`

## Comparability

`identical` requires matching ArchMap digest, LawPolicy, law-surface, and
MeasurementProfile component fingerprints, plus tool version.
`verdict-row` requires matching LawPolicy, law-surface, and MeasurementProfile component fingerprints, site cover
digest, and tool version. A policy-bundle component change is therefore
explicitly recorded as `not-comparable`.
Other pairs are `not-comparable`; the report records both independent run conclusions and emits a typed boundary.

When a checked refinement artifact binds both run site-cover fingerprints, `classTransport.recordComparability`
may remain `not-comparable` while the separate refinement reading is established.

Cover or context changes are boundary data. They are not architecture degradation claims.
For gate policy, affected transitions are classified as `other_transition` and map through the policy key `other`.

## Record-level conclusion codes

Current conclusion codes are:

- `NO_NEW_MEASURED_OBSTRUCTION_RECORDED`
- `MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE`
- `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE`
- `RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA`

`VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR` belongs to the `refactor-morphism/v0.5.3`
analytic reading. Refinement compare uses the dedicated
`CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT` token only for coarse-zero →
fine-zero. Both nonzero and zero/nonzero pairs remain `not_computed` with a
boundary statement; they do not establish class transport.

## Non-claims

- compare does not transport nonzero cohomology classes or obstruction identity across runs; its dedicated refinement reading is limited to the checked class-zero predicate.
- compare does not decide whether a code change caused a verdict change.
- compare does not turn raw ArchMap differences into FieldSig evolution claims.
