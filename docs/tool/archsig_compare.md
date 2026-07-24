# ArchSig compare report guide

`archsig compare` は 2 つの `archsig analyze` run directory を読み、record 水準の差分を出力する。
`--refinement <refinement-comparison/v0.5.4>` を供給した場合は、coarse / fine の
`complexFingerprint` がそれぞれ base / head run の正規化有限複体 fingerprint
(`inputDigests.siteCoverDigest.sha256`)と一致することを検査してから、class-zero reading を追加する。
この fingerprint 検査により、site cover が異なる coarse→fine run でも refinement 経路を受理できる。
不一致は `COMPARISON_DATA_CONTRACT_VIOLATION` で fail-closed とする。
fingerprint 不一致かつ refinement 不在の場合は `profileConclusionCode: TWO_PROFILES_REPORTED_SEPARATELY` を記録する。

SAGA の run 内 H¹ comparison は `RepairPlan.comparison.h1ComparisonData` が所有する。
`kind: "explicit"` では `cochainMap.degreeZero` / `degreeOne` / `degreeTwo.basisMap` と
`degreeTwo.zeroImage` の有限写像表を validator が再計算する。
`kind: "presentation-generated"` では各 chart / overlap / triple cell の semantic generators、
repair relation 行列、equation quotient presentation、`generatorMap` と restriction 行列を入力し、
F₂ 上で `im(R)=ker(χ̃)`、`im(χ̃)=Q_E`、restriction naturality を検査する。これにより
local `Φ` と `κ⁰ / κ¹ / κ²` を導出し、`κ¹D_sem⁰=D_E⁰κ⁰` と
`κ²D_sem¹=D_E¹κ¹` を有限 cell incidence で確認する。presentation は independently authored な
`equationLiftAtlas`（chart ごとの local lift と overlap ごとの transition difference）も持ち、
ArchSig はそこから `r_E` を導出する。`κ¹(r_sem)=r_E+δ⁰h` は equation relation を含む商上で
解き、解があるときだけ computed quotient-atlas witness `h` を出力する。同じ商上で target cocycle と
target `Z¹/B¹` class を再計算する。semantic presentation 側でも `r_sem` の cocycle と
`Z¹/B¹` class を計算するため、nonempty triple がない selected `C²=0` complex でも、有限presentation
そのものから source / target H¹ transfer を確立できる。
どちらの kind でも適合条件を満たす場合だけ analyze の転送 invariant が立つ。
compare の run-pair 記録はこの run 内写像を自動生成しない。

SAGA の run 内 comparison で `kind: "explicit"` を選ぶ場合は、source の
`saga.residual-class` が未計測なら `silence_by_design`、reason
`residual_class_prerequisite_not_measured` と、不足している入力slot
(`complex.tripleOverlaps`, `coefficient`, `trueSheafCertificate`, `gluingData`) を案内する
`whatNext` を記録する。この前提未供給は比較違反として扱わない。source class が計測済みの場合だけ、有限 map の適合検査または target class の zero predicate の検査へ進む。

`kind: "presentation-generated"` では `saga.residual-class` を入力前提にせず、上記の
finite presentation 検査から semantic presentation の source `Z¹/B¹` class を計算する。
その計算に必要な presentation、restriction maps、または `equationLiftAtlas` が不成立なら同じ
`silence_by_design` と reason を記録し、それらの補充を `whatNext` に示す。4-cycle のように
selected `C²=0` で triple overlap が空でも、presentation による source / target class と
quotient-atlas witness が計算できれば、この経路は `established` になりうる。

`h1-comparison-transfer` は `ag.saga-comparison` evaluator が所有する computed invariant であり、`contract` を必須とする。contract は `incidenceBridgeKind`、`h1ComparisonDataKind`、`normalizedComplexFingerprint`（文字列）と、`classPrerequisite`、`targetClassComputed`、`contractChecked`（真偽値）の6フィールドを持ち、未知フィールドや別 evaluator への付け替えは受理しない。presentation-generated 経路が established のときは `SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS` を出力し、explicit 経路の `SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA` と区別する。
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

- `archmap-diff.json` with schema `archmap-diff/v0.5.4`
- `archsig-comparison-report.json` with schema `archsig-comparison-report/v0.5.4`

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

`VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR` belongs to the `refactor-morphism/v0.5.4`
analytic reading. Refinement compare uses the dedicated
`CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT` token only for coarse-zero →
fine-zero. Both nonzero and zero/nonzero pairs remain `not_computed` with a
boundary statement; they do not establish class transport.

ArchViewがgate reportを表示する場合も、compare reportからdecisionを再計算しない。
`archsig-gate-report/v0.5.4`はArchSigの`gate`が生成した第二入力として、対応するmeasurement
packet digestとともに供給する。

## Non-claims

- compare does not transport nonzero cohomology classes or obstruction identity across runs; its dedicated refinement reading is limited to the checked class-zero predicate.
- compare does not decide whether a code change caused a verdict change.
- compare does not turn raw ArchMap differences into FieldSig evolution claims.
