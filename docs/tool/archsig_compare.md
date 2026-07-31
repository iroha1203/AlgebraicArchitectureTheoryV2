# ArchSig compare report guide

`archsig compare` は 2 つの `archsig analyze` run directory を読み、record 水準の差分を出力する。
選択された MeasurementProfile の `siteRef` / `coverRef` と、両 run の normalized ArchMap を使い、
fine cover の各 context が coarse cover の一つへ identity または `restrictsTo` 経路で到達することを導出する。
各 fine context の到達先が一意に定まる場合だけ、class-zero reading を追加する。
site / cover の選択が異なる、cover が存在しない、context が到達しない、または複数の coarse context へ到達する場合は、
`classTransport.status: not_computed` と named reason を記録する。

SAGA の run 対の読みは、supplied comparison data ではなく **導出 residualDifferenceReading** が担う
(#3822 で `RepairPlan.comparison` slot と `saga-comparison:h1-transfer` invariant は沈黙した)。
`compare` は base / head 両 run の `saga-descent:residual-derivation`(観測 sectionValue 比較から
導出された overlap ごとの F₂ 値と provenance)を読み、comparability ゲート
(level が identical / verdict-row、両 derivation の coverRef / mappedCoverRef / lawSurfaceRef /
charts 相等、overlap 鍵集合一致)の下で delta = value_base XOR value_head を作り、
スカラー系 δ⁰h = delta の可解性を計算して `residualDifferenceReading` block を出力する:

- `status: difference_in_B1` — residual の差が `B¹` に入り、`witnessChartAssignment` に
  `δ⁰h = delta` の witness `h` を記録
- `status: difference_not_in_B1` — residual の差が選択複体の `B¹` に入らない
- `status: no_residual_change` — delta が空
- `status: not_computed` / `silence_by_design` — 複体・provenance 不一致、または derivation 未記録

この block は 2 run の residual 差に対する `B¹` 所属の有限計算である
(theoremRef: part10/2.3)。修理成功の読みは、repaired 側 run の零 residual
(`REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`)と gate が担う。v0.5.7 はこの一系統の語彙を
triple 宣言の有無にかかわらず使う。入力は両 run に記録済みの導出 residual であり、
新しい authored data や供給 slot は追加しない。

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
- `archsig-comparison-report.json` with schema `archsig-comparison-report/v0.5.7`

## Comparability

`identical` requires matching ArchMap digest, LawPolicy, law-surface, and
MeasurementProfile component fingerprints, optional RepairPlan digest, plus tool version.
`verdict-row` requires matching LawPolicy, law-surface, and MeasurementProfile component fingerprints, site cover
digest, and tool version. RepairPlan digest differences are emitted as
`sameRepairPlanDigest: false` with a `repair_plan_changed_between_runs` record, while preserving
the record-level comparison. A policy-bundle component change is therefore explicitly recorded as
`not-comparable`.
Other pairs are `not-comparable`; the report records both independent run conclusions and emits a typed boundary.

Each measurement run manifest records the canonical digests of its normalized ArchMap and measurement packet.
`compare` verifies both digests and each artifact's run contract (`runId`, tool version, input digests,
component fingerprints) against the manifest before computing an ArchMap diff or verdict transition.

When the derived context relation is established, `classTransport.recordComparability` may remain
`not-comparable` while the separate class-zero reading is established.

Cover or context changes are boundary data. They are not architecture degradation claims.
For gate policy, affected transitions are classified as `other_transition` and map through the policy key `other`.

## Record-level conclusion codes

Current conclusion codes are:

- `NO_NEW_MEASURED_OBSTRUCTION_RECORDED`
- `MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE`
- `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE`
- `RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA`

The derived coarse-to-fine reading uses the dedicated
`CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT` token only for coarse-zero →
fine-zero. Both nonzero and zero/nonzero pairs remain `not_computed` with a
boundary statement; they do not establish class transport.

ArchViewがgate reportを表示する場合も、compare reportからdecisionを再計算しない。
`archsig-gate-report/v0.5.4`はArchSigの`gate`が生成した第二入力として、対応するmeasurement
packet digestとともに供給する。

## Non-claims

- compare does not transport nonzero cohomology classes or obstruction identity across runs; its dedicated reading is limited to the derived class-zero predicate.
- compare does not decide whether a code change caused a verdict change.
- compare does not turn raw ArchMap differences into FieldSig evolution claims.
