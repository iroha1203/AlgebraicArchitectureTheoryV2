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
| ArchSig Review | AIR、ArchMap supplied JSON validation、ArchMap-to-AIR projection、AIR validation、theorem precondition check、Feature Extension Report、architecture-policy、law violation report、policy decision、PR comment summary、baseline suppression、PR quality analysis。 | organization ごとの policy calibration、review practice との tuning、任意 invariant の自動判定。tool output は Lean theorem や merge approval ではない。 |
| ArchSig SFT | Markdown PRD / Spec / Issue / AI proposal、GitHub Issue JSON、AI proposal JSON から `ArtifactDescriptor`、`OperationSupportEstimate`、`ForecastConeSkeleton`、`ConsequenceEnvelope`、validation report を生成する bounded pipeline。PRD v3 では `IntentMap`、`AlignmentMap`、`intent-forecast` を使って planning forecast を作る。 | real dataset calibration、framework semantics adapter は remaining gaps。`ForecastCone` は point prediction ではなく、`ConsequenceEnvelope` は report projection である。 |
| ArchSig Operational | PR history dataset、feature extension dataset、outcome linkage、B10 daily ledger、calibration review、team threshold、ownership boundary、repair adoption、incident correlation、hypothesis refresh artifacts。 | 実 dataset での calibration、incident / rollback / MTTR との運用接続、confounder 管理、private data boundary の組織別設計が残る。correlation は因果 theorem ではない。 |

## できること

- Lean `import` / Python `import` graph から component と dependency edge を抽出する。
- `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk` などの構造 metric を計算する。
- policy JSON がある場合、boundary / abstraction violation を測る。
- architecture-policy JSON がある場合、Layered Architecture の deterministic violation と SRP review cue boundary を分ける。
- runtime edge evidence JSON がある場合、runtime dependency projection を出す。
- Sig0 output を validation し、revision snapshot と before / after diff を作る。
- PR metadata、AIR、theorem precondition check、Feature Extension Report、policy decision、
  PR comment summary を生成する。
- supplied JSON の `archmap-v0` を validation report に変換し、AIR へ loss-aware に投影する。
- 実証研究用 dataset、B10 operational feedback artifact、B12 SFT forecasting MVP の
  descriptor / support estimate / cone / envelope / calibration hook を JSON として出力する。
- PRD / Epic / Spec の意図を `intentmap-v0` として保持し、`intent-archmap-alignment-v0`
  から operation support、ForecastCone、ConsequenceEnvelope を deterministic に生成する。
- PR diff / repository evidence から作られた ArchMap 系 artifact を、merge approval ではない
  PR quality review cue として読む `pr-quality-analysis-report-v0` を出力する。
- Codex skill として、ArchMap 作成、IntentMap 作成、PR / CI 分析、Epic / PRD forecast の作業手順を AI agent に渡せる。

詳細な command と artifact は次に分けている。

- [Command Guide](docs/commands.md)
- [Artifacts And Boundaries](docs/artifacts-and-boundaries.md)
- [Operational Feedback](docs/operational-feedback.md)

## Codex Skills

`tools/archsig/skills/` には、ArchSig / ArchMap を Codex から扱うための skill bundle を置く。
これらは ArchSig source repository に依存せず、built `archsig` binary と skill bundle だけで動ける
ことを目標にしている。実行時は `archsig` が `PATH` にあるか、`ARCHSIG_BIN=/path/to/archsig`
で明示されている前提で読む。

| Skill | 用途 |
| --- | --- |
| [`archmap-creater`](skills/archmap-creater/SKILL.md) | repository evidence から bounded `archmap-v0` を作成し、validation まで進める。IntentMap は扱わない。 |
| [`intentmap-creater`](skills/intentmap-creater/SKILL.md) | Epic / PRD / Spec / Issue / proposal から bounded `intentmap-v0` を作成し、missing decision と ambiguous intent を保持して validation まで進める。 |
| [`arch-pr-analyzer`](skills/arch-pr-analyzer/SKILL.md) | PR / CI の architecture artifact を読み、architecture risk、review cue、evidence gap、次の PR review action を分析する。planning forecast は扱わない。 |
| [`arch-intent-forecaster`](skills/arch-intent-forecaster/SKILL.md) | IntentMap x ArchMap alignment から planning forecast artifact を読み、bounded evolution pressure、missing decision、planning action を分析する。PR merge review は扱わない。 |

skill は AI native な操作面であり、tool output を Lean proof、forecast correctness、incident causality、
global architecture truth として読まない。生成 artifact は標準では `.archsig/` 以下に置く。

## 最短手順

生成 artifact は標準では `.archsig/` 以下に置く。`.archsig/` は作業用出力ディレクトリであり、
canonical fixture や regression test 用 artifact は `tools/archsig/tests/fixtures/` に置く。

fixture で scan する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --root tools/archsig/tests/fixtures/minimal \
  --policy tools/archsig/tests/fixtures/minimal/policy_measured_zero.json \
  --runtime-edges tools/archsig/tests/fixtures/minimal/runtime_edges.json \
  --out .archsig/signature/sig0-fixture.json
```

validation report を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- validate \
  --input .archsig/signature/sig0-fixture.json \
  --out .archsig/signature/sig0-fixture-validation.json \
  --universe-mode local-only
```

repository root を scan する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --root . \
  --out .archsig/signature/sig0.json
```

Python repository を scan する場合は `--language python` を指定する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --language python \
  --root path/to/repository \
  --source-root src \
  --package-root src \
  --out .archsig/signature/python-sig0.json
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

semantic evidence を supplied ArchMap から流す場合は、次の経路も使える。

```text
archmap-v0
  -> archmap
  -> air-from-archmap
  -> validate-air
  -> theorem-check
  -> feature-report
```

通常の PR review で最初に読むのは次でよい。

| 出力 | 用途 |
| --- | --- |
| `signature-diff-report-v0` | before / after の悪化軸、改善軸、未評価軸、evidence diff、PR attribution candidate。 |
| `feature-extension-report-v0` | split status、witness、coverage gap、theorem precondition checks。 |
| `archmap-validation-report-v0` | supplied ArchMap の source refs、claim boundary、semantic coverage、conflict、formal promotion guardrail。 |
| `architecture-policy-v0` | project-local adopted laws、layer selectors、exceptions、SRP taxonomy。 |
| `law-violation-report-v0` | Layered deterministic violation、allowed exception、unmeasured selector、SRP review cue。 |
| `policy-decision-report-v0` | organization policy に基づく pass / warn / fail / advisory decision。 |
| `pr-comment-summary-v0` | GitHub Checks / PR comment 向け Markdown summary。 |
| `pr-quality-analysis-report-v0` | ArchMap / AIR / theorem-check / feature-report / policy-decision 由来の PR review cue。merge 可否は自動判定しない。 |
| `intentmap-v0` | PRD / Epic / Spec の requirement、operation、workflow、state transition、acceptance、non-goal、ambiguity、missing decision を source refs とともに保持する。 |
| `intent-archmap-alignment-v0` | IntentMap item と ArchMap item の対応、unaligned / unsupported / ambiguous intent、missing evidence を保持する。 |
| `artifact-descriptor-v0` | PRD / Spec / Issue / AI proposal を SFT forecasting MVP の入力境界へ正規化する。 |
| `operation-support-estimate-v0` | `artifact-descriptor-v0` または `intent-archmap-alignment-v0` から候補 operation family、policy constraints、known forbidden support、unknown remainder を保持する。 |
| `forecast-cone-skeleton-v0` | finite support と bounded horizon に相対化した path class candidates と forecast boundary を保持する。 |
| `consequence-envelope-report-v0` | signature axis、obstruction candidate、missing boundary、review / CI recommendation を report projection にまとめる。 |
| `forecast-calibration-hook-v0` | forecast item refs と B10 / B11 の observed artifact refs を対応付ける。 |
| `intent-calibration-record-v0` | IntentMap item、forecast item、observed implementation artifact、missing decision status、forecast usefulness feedback を対応付ける。 |

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
- LLM / agent から `archmap-v0` を自動生成する。
- metric と incident / rollback / MTTR の因果関係を証明する。
- Lean theorem proof、extractor completeness、architecture lawfulness を tooling output だけで結論する。
- SRP cue を deterministic tool violation として結論する。

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
