# Sig0 extractor

Lean status: `empirical hypothesis` / tooling output.

`sig0-extractor` は Lean module import graph から Architecture Signature v0 の入力 JSON を作る最小 CLI である。Lean の証明器ではなく、repository checkout から測定用データを作る外部 tooling として扱う。

## Usage

fixture を使った最小再現例は次である。

```bash
cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- \
  --root tools/sig0-extractor/tests/fixtures/minimal \
  --policy tools/sig0-extractor/tests/fixtures/minimal/policy_measured_zero.json \
  --runtime-edges tools/sig0-extractor/tests/fixtures/minimal/runtime_edges.json \
  --out .lake/sig0-fixture.json
```

代表的な出力 contract は次の形になる。

```json
{
  "schemaVersion": "sig0-extractor-v0",
  "componentKind": "lean-module",
  "policies": {
    "policyId": "minimal-measured-zero",
    "schemaVersion": "signature-policy-v0"
  },
  "metricStatus": {
    "boundaryViolationCount": {
      "measured": true,
      "source": "policy:minimal-measured-zero"
    },
    "runtimePropagation": {
      "measured": true,
      "source": "runtime-edge-projection-v0"
    }
  },
  "runtimeDependencyGraph": {
    "projectionRule": "runtime-edge-projection-v0",
    "edgeKind": "runtime"
  }
}
```

policy を渡さない場合、`boundaryViolationCount` と
`abstractionViolationCount` の値は placeholder の `0` になるが、
`metricStatus.<axis>.measured = false` なので違反なしとは読まない。
runtime edge evidence を渡さない場合も、dataset 側の `runtimePropagation` は
未評価の `null` として残る。

```bash
cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- \
  --root . \
  --policy signature-policy.json \
  --runtime-edges runtime-edges.json \
  --out .lake/sig0.json
```

`--policy` を省略すると boundary / abstraction policy は未評価の placeholder として
出力される。`--out` を省略すると JSON は stdout に出力される。
`--runtime-edges` を指定すると runtime edge evidence を読み、metadata を保持したまま
0/1 `RuntimeDependencyGraph` projection を出力する。省略した場合、
`runtimePropagation` は未評価の欠損値として dataset 側に残る。

既存 Sig0 JSON から `ComponentUniverse` 境界に対応する validation report を生成する場合は
次を使う。

```bash
cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- validate \
  --input .lake/sig0.json \
  --out .lake/sig0-validation.json \
  --universe-mode local-only
```

`validate` は source file を再 scan せず、入力 JSON の `components`, `edges`,
`metricStatus` から duplicate-free component list, local edge closure, external target,
synthetic module root target, policy metric status を検査する。`Foo.Main -> Foo` のような
root module import target は component list へ自動補完せず、`local-only` universe 外の
synthetic target として warning にする。report は tooling-side evidence であり、
`ComponentUniverse` の Lean witness そのものではない。

fixture 出力を検証する例:

```bash
cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- validate \
  --input .lake/sig0-fixture.json \
  --out .lake/sig0-fixture-validation.json \
  --universe-mode local-only
```

pass する場合の要点は次である。

```json
{
  "schemaVersion": "component-universe-validation-report-v0",
  "summary": {
    "result": "pass",
    "failedCheckCount": 0,
    "notMeasuredCheckCount": 0
  }
}
```

repository root を測定する場合、`.git`, `.lake`, `.elan`, `target`, root 直下の
`tools` は scan 対象から除外する。これは extractor 自身の fixture や build artifact
を Lean module import graph に混ぜないための v0 の実装仕様である。

## Output

出力 schema は `schemaVersion: "sig0-extractor-v0"` の単一 JSON document である。

- `components`: Lean source file から得た module component。
- `edges`: `source depends on target` の import edge。これは `ArchGraph.edge source target` に対応する。
- `signature`: import graph から計算した `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk` と、policy 評価に基づく violation count。
- `metricStatus`: 各 signature 軸が測定済みか、placeholder 欠損値かを記録する。
- `policyViolations`: policy 評価で検出した unique dependency edge 単位の evidence。違反がなければ省略される。
- `runtimeEdgeEvidence`: `--runtime-edges` で入力した runtime edge metadata。`label`, `failureMode`, `timeoutBudget`, `retryPolicy`, `circuitBreakerCoverage`, `confidence`, `evidenceLocation` を保持する。
- `runtimeDependencyGraph`: runtime evidence が 1 件以上ある component pair を 0/1 edge に落とした projection。未指定なら省略される。

この CLI は `ComponentUniverse` の完全な witness を生成したとは主張しない。duplicate-free component list, edge closure, coverage などの証明付き universe は Lean 側の別責務として扱う。

validation report の出力 schema は
`schemaVersion: "component-universe-validation-report-v0"` の単一 JSON document である。
`summary.result` は `pass`, `warn`, `fail` のいずれかで、`fail` の場合だけ CLI の終了コードは
`1` になる。入力 JSON を読めない、または report を生成できない場合の終了コードは `2` である。

PR 前後の Signature と PR metadata を empirical dataset v0 record に結合する場合は
次を使う。

main branch の週次 scan や任意期間 diff のために repository revision ごとの Signature を
蓄積する場合は、`docs/design/signature_snapshot_store_schema.md` の
`signature-snapshot-store-v0` を使う。snapshot store は PR metadata や signed delta を
持たず、`repository`, `revision`, `scan.scannedAt`, extractor version, `policy.policyId`,
`signature`, `metricStatus`, `validationSummary` を保持する。`validationSummary.result`
が `fail` の snapshot は主要 diff から除外し、`metricStatus.measured = false` の軸は
placeholder 0 でも risk 0 として扱わない。

GitHub API の PR detail / files / reviews JSON から `pr-metadata.json` を生成する場合は
次を使う。

```bash
cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- pr-metadata \
  --pull-request github-pr.json \
  --files github-pr-files.json \
  --reviews github-pr-reviews.json \
  --out pr-metadata.json
```

`--pull-request` は GitHub REST `pulls/{number}` の JSON を想定する。
`--files` は pull request files API の配列を想定し、`.lean` file path から
`changedComponents` を `Formal/Arch/A.lean -> Formal.Arch.A` の規則で抽出する。
`--reviews` を省略した場合、`reviewRoundCount` は `0` になり、
`firstReviewLatencyHours` と `approvalLatencyHours` は `null` になる。
approval review がない場合も `approvalLatencyHours` は `null` であり、0 時間とは扱わない。
`mergeLatencyHours` は `merged_at` がない場合に `null` になる。
author が GitHub Bot type または `[bot]` / `-bot` login の場合、
`pullRequest.isBotGenerated = true` として保持する。
GraphQL reviewThreads JSON を別途持つ場合は `--review-threads` で渡せる。

```bash
cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- dataset \
  --before .lake/sig0-base.json \
  --after .lake/sig0-head.json \
  --pr-metadata pr-metadata.json \
  --after-role head \
  --out .lake/empirical-dataset-v0.json
```

`--after-role` は `head` または `merge` を指定する。`merge` を指定する場合は
PR metadata の `pullRequest.mergeCommit` が必須である。

`pr-metadata.json` は `repository`, `pullRequest`, `prMetrics` を持つ JSON document
で、`issueIncidentLinks` と `analysisMetadata` は省略できる。dataset 出力は
`schemaVersion: "empirical-signature-dataset-v0"` の単一 record である。
`deltaSignatureSigned` は before / after の両方で `metricStatus.measured = true`
かつ値が `null` でない軸だけを符号付き差分として出す。policy 未指定の
`boundaryViolationCount` のような placeholder 0 は `null` delta として保持する。
runtime edge evidence がない Sig0 JSON では `runtimePropagation` は `null` のままで、
測定済み 0 とは扱わない。

fixture metadata を使った dataset 生成例:

```bash
cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- \
  --root tools/sig0-extractor/tests/fixtures/minimal \
  --out .lake/sig0-before.json

cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- \
  --root tools/sig0-extractor/tests/fixtures/minimal \
  --policy tools/sig0-extractor/tests/fixtures/minimal/policy_measured_zero.json \
  --runtime-edges tools/sig0-extractor/tests/fixtures/minimal/runtime_edges.json \
  --out .lake/sig0-after.json

cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- dataset \
  --before .lake/sig0-before.json \
  --after .lake/sig0-after.json \
  --pr-metadata tools/sig0-extractor/tests/fixtures/minimal/pr_metadata.json \
  --after-role head \
  --out .lake/empirical-dataset-v0.json
```

この例では before 側の policy / runtime graph が未評価なので、after 側が測定済みでも
次のように delta は `null` になる。

```json
{
  "deltaSignatureSigned": {
    "boundaryViolationCount": null,
    "runtimePropagation": null
  },
  "metricDeltaStatus": {
    "boundaryViolationCount": {
      "comparable": false,
      "beforeMeasured": false,
      "afterMeasured": true
    }
  },
  "analysisMetadata": {
    "runtimeMetrics": {
      "runtimeGraphMeasured": true,
      "runtimeEdgeEvidenceCount": 2
    }
  }
}
```

workflow 単位の `RelationComplexityObservation` を候補 evidence JSON から生成する場合は
次を使う。

```bash
cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- relation-complexity \
  --input relation-complexity-candidates.json \
  --out relation-complexity-observation.json
```

入力 schema は `schemaVersion: "relation-complexity-candidates/v0"` で、
`repository`, `revision`, `measurementUniverse`, `workflow`,
`evidenceCandidates` を持つ。出力 schema は
`schemaVersion: "relation-complexity-observation/v0"` である。
`relation-complexity-rules/v0` は `constraints`, `compensations`,
`projections`, `failureTransitions`, `idempotencyRequirements` の tag を数え、
同じ evidence item 内の同一 tag は 1 回だけ数える。`application-owned` と
`application-configured` は counting candidate とし、`framework-generated` や
未対応 framework の候補は `excludedEvidence` に理由を残す。

fixture の代表出力では `constraints = 1`, `compensations = 1`,
`failureTransitions = 1` なので、`relationComplexity = 3` になる。

## Test and CI

ローカル検証は次で行う。

```bash
cargo test --manifest-path tools/sig0-extractor/Cargo.toml
```

CI では GitHub Actions の `sig0-extractor cargo test` job が同じコマンドを実行する。
Lean theorem ではなく tooling contract の再現性を確認するため、fixtures と CLI test で
policy, runtime edge projection, relation complexity, dataset conversion を通す。
