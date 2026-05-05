# ArchSig

`archsig` は repository checkout から Architecture Signature 用の JSON artifact を作る
CLI である。Lean の証明器ではなく、CI や AI agent が読むための architecture telemetry
generator として扱う。

現在の scan は Lean module import graph と Python import graph に対応する。出力は JSON
artifact として固定し、validation、diff、AIR、Feature Extension Report、policy decision、
PR comment、dataset generation などの後段 command に渡せる。

## できること

- Lean `import` / Python `import` graph から component と dependency edge を抽出する。
- `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk` などの構造 metric を計算する。
- policy JSON がある場合、boundary / abstraction violation を測る。
- runtime edge evidence JSON がある場合、runtime dependency projection を出す。
- Sig0 output を validation し、revision snapshot と before / after diff を作る。
- PR metadata、AIR、theorem precondition check、Feature Extension Report、policy decision、
  PR comment summary を生成する。
- 実証研究用 dataset と B10 operational feedback artifact を JSON として出力する。

詳細な command と artifact は次に分けている。

- [Command Guide](docs/commands.md)
- [Artifacts And Boundaries](docs/artifacts-and-boundaries.md)
- [Operational Feedback](docs/operational-feedback.md)

## 最短手順

fixture で scan する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --root tools/archsig/tests/fixtures/minimal \
  --policy tools/archsig/tests/fixtures/minimal/policy_measured_zero.json \
  --runtime-edges tools/archsig/tests/fixtures/minimal/runtime_edges.json \
  --out .lake/sig0-fixture.json
```

validation report を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- validate \
  --input .lake/sig0-fixture.json \
  --out .lake/sig0-fixture-validation.json \
  --universe-mode local-only
```

repository root を scan する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --root . \
  --out .lake/sig0.json
```

Python repository を scan する場合は `--language python` を指定する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --language python \
  --root path/to/repository \
  --source-root src \
  --package-root src \
  --out .lake/python-sig0.json
```

`--out` を省略すると JSON は stdout に出る。

## PR / CI フロー

PR / CI 診断では、基本的に次の順で artifact を作る。

```text
scan
  -> validate
  -> snapshot
  -> signature-diff
  -> air
  -> theorem-check
  -> feature-report
  -> policy-decision
  -> pr-comment
```

通常の PR review で最初に読むのは次でよい。

| 出力 | 用途 |
| --- | --- |
| `signature-diff-report-v0` | before / after の悪化軸、改善軸、未評価軸、evidence diff、PR attribution candidate。 |
| `feature-extension-report-v0` | split status、witness、coverage gap、theorem precondition checks。 |
| `policy-decision-report-v0` | organization policy に基づく pass / warn / fail / advisory decision。 |
| `pr-comment-summary-v0` | GitHub Checks / PR comment 向け Markdown summary。 |

[Signature diff report workflow](../../.github/workflows/signature-diff.yml) は、PR / push /
schedule / manual run で Sig0、validation、snapshot、`signature-diff-report-v0` を作り、
workflow summary と artifact を保存する。

## 読み方の要点

`archsig` は測定済み 0 と未評価を分ける。

- `metricStatus.<axis>.measured = true`: 測定済み。
- `metricStatus.<axis>.measured = false`: 未評価。signature 値が placeholder 0 でも risk 0 と読まない。
- optional axis の `null`: 未評価、またはこの入力では比較不能。
- `deltaSignatureSigned.<axis> = null`: before / after のどちらかが未評価、または値が `null`。

AI agent や CI job は `signature` の値だけで判断せず、`metricStatus`,
`metricDeltaStatus`, `unmeasuredAxes`, `nonConclusions` を併読する。

## できないこと

現状では、次は行わない。

- 任意 repository から完全な architecture model を抽出する。
- security vulnerability や一般的な code smell を診断する。
- runtime dependency や incident / repair cost を外部 system から自動収集する。
- metric と incident / rollback / MTTR の因果関係を証明する。
- Lean theorem proof、extractor completeness、architecture lawfulness を tooling output だけで結論する。

## Test

ローカル検証は次で行う。

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
```

ローカルの rustc incremental cache が壊れている場合は、次で再実行する。

```bash
CARGO_INCREMENTAL=0 cargo test --manifest-path tools/archsig/Cargo.toml
```

CI では GitHub Actions の `archsig cargo test` job が同じ test suite を実行する。
