# ArchSig

`archsig` は repository checkout から Architecture Signature 用の JSON artifact を作る
CLI である。Lean の証明器ではなく、CI や AI agent が読むための architecture telemetry
generator として扱う。

現在の scan は Lean module import graph と Python import graph に対応する。出力は JSON
artifact として固定し、validation、diff、AIR、Feature Extension Report、policy decision、
PR comment、dataset generation などの後段 command に渡せる。

## Product surface

ArchSig は単一の command ではなく、次の surface に分けて読む。

| Surface | 現在使えるもの | Remaining gaps |
| --- | --- | --- |
| ArchSig Core | Lean / Python import graph scan、Sig0、validation、snapshot、signature diff。policy JSON と runtime edge evidence は明示入力として扱える。 | call graph、data dependency、dynamic import、plugin loading、framework convention は adapter boundary。extractor output は完全な `ComponentUniverse` ではない。 |
| ArchSig Review | AIR、AIR validation、theorem precondition check、Feature Extension Report、policy decision、PR comment summary、baseline suppression。 | organization ごとの policy calibration、review practice との tuning、任意 invariant の自動判定は未完成。tool output は Lean theorem ではない。 |
| ArchSig SFT | Markdown PRD / Spec / Issue / AI proposal、GitHub Issue JSON、AI proposal JSON から `ArtifactDescriptor`、`OperationSupportEstimate`、`ForecastConeSkeleton`、`ConsequenceEnvelope`、validation report を生成する bounded pipeline。 | real dataset calibration、framework semantics adapter は remaining gaps。`ForecastCone` は point prediction ではなく、`ConsequenceEnvelope` は report projection である。 |
| ArchSig Operational | PR history dataset、feature extension dataset、outcome linkage、B10 daily ledger、calibration review、team threshold、ownership boundary、repair adoption、incident correlation、hypothesis refresh artifacts。 | 実 dataset での calibration、incident / rollback / MTTR との運用接続、confounder 管理、private data boundary の組織別設計が残る。correlation は因果 theorem ではない。 |

## できること

- Lean `import` / Python `import` graph から component と dependency edge を抽出する。
- `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk` などの構造 metric を計算する。
- policy JSON がある場合、boundary / abstraction violation を測る。
- runtime edge evidence JSON がある場合、runtime dependency projection を出す。
- Sig0 output を validation し、revision snapshot と before / after diff を作る。
- PR metadata、AIR、theorem precondition check、Feature Extension Report、policy decision、
  PR comment summary を生成する。
- 実証研究用 dataset、B10 operational feedback artifact、B12 SFT forecasting MVP の
  descriptor / support estimate / cone / envelope / calibration hook を JSON として出力する。

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
| `artifact-descriptor-v0` | PRD / Spec / Issue / AI proposal を SFT forecasting MVP の入力境界へ正規化する。 |
| `operation-support-estimate-v0` | `artifact-descriptor-v0` から候補 operation family、policy constraints、known forbidden support、unknown remainder を保持する。 |
| `forecast-cone-skeleton-v0` | finite support と bounded horizon に相対化した path class candidates と forecast boundary を保持する。 |
| `consequence-envelope-report-v0` | signature axis、obstruction candidate、missing boundary、review / CI recommendation を report projection にまとめる。 |
| `forecast-calibration-hook-v0` | forecast item refs と B10 / B11 の observed artifact refs を対応付ける。 |

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
