# Sig0 extractor

Lean status: `empirical hypothesis` / tooling output.

`sig0-extractor` は Lean module import graph から Architecture Signature v0 の入力 JSON を作る最小 CLI である。Lean の証明器ではなく、repository checkout から測定用データを作る外部 tooling として扱う。

## Usage

```bash
cargo run --manifest-path tools/sig0-extractor/Cargo.toml -- \
  --root . \
  --policy signature-policy.json \
  --out .lake/sig0.json
```

`--policy` を省略すると boundary / abstraction policy は未評価の placeholder として
出力される。`--out` を省略すると JSON は stdout に出力される。

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
policy metric status を検査する。report は tooling-side evidence であり、
`ComponentUniverse` の Lean witness そのものではない。

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

この CLI は `ComponentUniverse` の完全な witness を生成したとは主張しない。duplicate-free component list, edge closure, coverage などの証明付き universe は Lean 側の別責務として扱う。

validation report の出力 schema は
`schemaVersion: "component-universe-validation-report-v0"` の単一 JSON document である。
`summary.result` は `pass`, `warn`, `fail` のいずれかで、`fail` の場合だけ CLI の終了コードは
`1` になる。入力 JSON を読めない、または report を生成できない場合の終了コードは `2` である。

PR 前後の Signature と PR metadata を empirical dataset v0 record に結合する場合は
次を使う。

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
