# ArchSig compare report guide

`archsig compare` は 2 つの `archsig analyze` run directory を読み、record 水準の差分を出力する。
`--refinement <refinement-comparison/v0.5.2>` を供給した場合に限り、検査済み粗→細データの下で class-zero preservation reading を追加する。
fingerprint 不一致かつ refinement 不在の場合は `profileConclusionCode: TWO_PROFILES_REPORTED_SEPARATELY` を記録する。

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

- `archmap-diff.json` with schema `archmap-diff/v0.5.2`
- `archsig-comparison-report.json` with schema `archsig-comparison-report/v0.5.2`

## Comparability

`identical` requires matching ArchMap digest, LawPolicy, law-surface, and
MeasurementProfile component fingerprints, plus tool version.
`verdict-row` requires matching LawPolicy, law-surface, and MeasurementProfile component fingerprints, site cover
digest, and tool version. A policy-bundle component change is therefore
explicitly recorded as `not-comparable`.
Other pairs are `not-comparable`; the report records both independent run conclusions and emits a typed boundary.

Cover or context changes are boundary data. They are not architecture degradation claims.
For gate policy, affected transitions are classified as `other_transition` and map through the policy key `other`.

## Record-level conclusion codes

Current conclusion codes are:

- `NO_NEW_MEASURED_OBSTRUCTION_RECORDED`
- `MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE`
- `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE`
- `RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA`

Names that imply transport or causality without the corresponding supplied
artifact, including `ZERO_PRESERVED...`,
`..._INTRODUCED_BY_CHANGE`, and `..._CLEARED_BY_CHANGE`, are outside this artifact contract.

## Non-claims

- compare does not transport cohomology classes or obstruction identity across runs.
- compare does not decide whether a code change caused a verdict change.
- compare does not turn raw ArchMap differences into FieldSig evolution claims.
