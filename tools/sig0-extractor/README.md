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

repository root を測定する場合、`.git`, `.lake`, `.elan`, `target`, root 直下の
`tools` は scan 対象から除外する。これは extractor 自身の fixture や build artifact
を Lean module import graph に混ぜないための v0 の実装仕様である。

## Output

出力 schema は `schemaVersion: "sig0-extractor-v0"` の単一 JSON document である。

- `components`: Lean source file から得た module component。
- `edges`: `source depends on target` の import edge。これは `ArchGraph.edge source target` に対応する。
- `signature`: import graph から計算した `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk` と、policy 評価に基づく violation count。
- `metricStatus`: `boundaryViolationCount` / `abstractionViolationCount` が測定済みか、placeholder 欠損値かを記録する。
- `policyViolations`: policy 評価で検出した unique dependency edge 単位の evidence。違反がなければ省略される。

この CLI は `ComponentUniverse` の完全な witness を生成したとは主張しない。duplicate-free component list, edge closure, coverage などの証明付き universe は Lean 側の別責務として扱う。
