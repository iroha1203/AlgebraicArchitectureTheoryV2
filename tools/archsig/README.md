# ArchSig

Lean status: `empirical hypothesis` / tooling output.

`archsig` は repository checkout から Architecture Signature 用の JSON artifact を作る CLI である。
Lean の証明器ではなく、CI や AI agent が読むための architecture telemetry generator として扱う。

現状の自動 scan は Lean module import graph に対応する。出力 schema は JSON で固定し、
後段の `validate`, `snapshot`, `signature-diff`, `air`, `dataset` は JSON artifact を入力にして動く。

## 何ができるか

- Lean source の `import` から component / dependency edge を抽出する。
- `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk` を計算する。
- policy JSON がある場合、`boundaryViolationCount` と `abstractionViolationCount` を測る。
- runtime edge evidence JSON がある場合、0/1 `RuntimeDependencyGraph` projection を作る。
- Sig0 output が測定 universe として扱えるか validation report を作る。
- revision ごとの snapshot を作り、before / after の signature diff を出す。
- GitHub PR JSON から PR metadata を作り、dataset や diff attribution に使う。
- relation complexity candidate JSON から workflow-level observation を作る。
- Sig0 / validation / diff / PR metadata を AIR v0 に正規化する。
- AIR claim に対して static theorem package v0 の前提充足状況を検査する。
- synthesis constraint artifact v0 の候補境界と no-solution certificate 境界を検査する。

## 標準フロー

PR / CI 診断では、基本的に次の順で artifact を作る。

```text
scan
  -> validate
  -> snapshot
  -> signature-diff
  -> air
  -> theorem-check
  -> feature-report
  -> AI agent / CI job が feature report と diff report を読む
```

単一 revision の状態だけを見たい場合は `scan` と `validate` まででよい。
before / after の悪化軸や evidence diff を見たい場合は `snapshot` と `signature-diff` まで作る。

## 出力の読み方

AI / CI が最初に読むべき成果物は次である。

| 出力 | schemaVersion | 用途 |
| --- | --- | --- |
| Sig0 output | `archsig-sig0-v0` | 単一 revision の component、edge、signature、metric status。 |
| Validation report | `component-universe-validation-report-v0` | Sig0 output の duplicate、edge closure、policy status などの検査結果。 |
| Snapshot | `signature-snapshot-store-v0` | repository revision ごとの保存用 signature record。 |
| Diff report | `signature-diff-report-v0` | before / after の悪化軸、改善軸、未評価軸、evidence diff、PR attribution candidate。 |
| AIR | `aat-air-v0` | Signature artifact layer を claim / evidence / coverage / extension boundary へ正規化した中間表現。 |
| AIR validation report | `aat-air-validation-report-v0` | AIR の dangling refs、claim boundary、measured evidence traceability の検査結果。 |
| Theorem precondition check report | `theorem-precondition-check-report-v0` | static theorem package v0 の registry と、AIR claim が `FORMAL_PROVED` へ昇格できるかの検査結果。 |
| Feature Extension Report | `feature-extension-report-v0` | AIR から生成する PR review 用 static report。split status、witness、coverage gap、theorem precondition checks を併読する。 |
| Synthesis constraint validation report | `synthesis-constraint-validation-report-v0` | synthesis constraint artifact の constraint / candidate refs、assumption boundary、solver no-candidate と valid no-solution certificate の分離を検査する。 |
| Dataset record | `empirical-signature-dataset-v0` | PR metadata と before / after signature を結合した実証研究用 record。 |

通常の PR / CI 診断では、最終的に `feature-extension-report-v0` と
`signature-diff-report-v0` を読む。

この CLI では、測定済み 0 と未評価を分ける。

- `metricStatus.<axis>.measured = true`: 測定済み。
- `metricStatus.<axis>.measured = false`: 未評価。signature 値が placeholder 0 でも risk 0 と読まない。
- optional axis の `null`: 未評価、またはこの入力では比較不能。
- `deltaSignatureSigned.<axis> = null`: before / after のどちらかが未評価、または値が `null`。

AI agent は `signature` の値だけで判断せず、必ず `metricStatus`, `metricDeltaStatus`,
`unmeasuredAxes` を併読する。

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

`--out` を省略すると JSON は stdout に出る。

## Scan する

基本形:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- \
  --root . \
  --policy signature-policy.json \
  --runtime-edges runtime-edges.json \
  --out .lake/sig0.json
```

`--policy` と `--runtime-edges` は任意である。

`--policy` を省略すると `boundaryViolationCount` と `abstractionViolationCount` は placeholder の
`0` になる。ただし `metricStatus.<axis>.measured = false` なので、違反なしとは読まない。

`--runtime-edges` を省略すると `runtimePropagation` は未評価として扱う。
runtime evidence を渡した場合、metadata を保持したまま 0/1 `RuntimeDependencyGraph` projection を出す。
この CLI が直接出す `runtimePropagation` は dependency edge の向きに沿う exposure radius である。
incident root cause からの blast radius は reverse reachability 由来の analysis metric として別に扱う。

repository root を測定する場合、`.git`, `.lake`, `.elan`, `target`, root 直下の `tools` は scan 対象から除外する。
`lakefile.lean` は build configuration metadata として扱い、component universe から除外する。
multi-project repository を project 単位で測る場合は、各 subproject root を `--root` に指定して別々に実行する。

代表的な Sig0 output:

```json
{
  "schemaVersion": "archsig-sig0-v0",
  "componentKind": "lean-module",
  "components": [
    { "id": "Formal", "path": "Formal.lean" }
  ],
  "edges": [
    {
      "source": "Formal",
      "target": "Formal.Arch.A",
      "kind": "import",
      "evidence": "import Formal.Arch.A"
    }
  ],
  "signature": {
    "hasCycle": 0,
    "sccMaxSize": 1,
    "maxDepth": 2,
    "fanoutRisk": 3,
    "boundaryViolationCount": 0,
    "abstractionViolationCount": 0
  },
  "metricStatus": {
    "boundaryViolationCount": {
      "measured": true,
      "source": "policy:minimal-measured-zero"
    }
  }
}
```

## Validate する

既存 Sig0 JSON を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- validate \
  --input .lake/sig0.json \
  --out .lake/sig0-validation.json \
  --universe-mode local-only
```

`validate` は source file を再 scan しない。入力 JSON の `components`, `edges`, `metricStatus` から
duplicate-free component list, local edge closure, external target, synthetic module root target,
policy metric status を検査する。

`Foo.Main -> Foo` のような root module import target は component list へ自動補完せず、
`local-only` universe 外の synthetic target として warning にする。

pass する場合の要点:

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

`summary.result` は `pass`, `warn`, `fail` のいずれかである。
`fail` の場合だけ CLI の終了コードは `1` になる。
入力 JSON を読めない、または report を生成できない場合の終了コードは `2` である。

## Snapshot / Diff を作る

CI や週次 scan では、まず Sig0 output と validation report から snapshot を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- snapshot \
  --input .lake/signature-current/sig0.json \
  --validation-report .lake/signature-current/validation.json \
  --repo-owner example \
  --repo-name service \
  --revision-sha "$(git rev-parse HEAD)" \
  --revision-ref "$(git rev-parse --abbrev-ref HEAD)" \
  --revision-branch main \
  --scanned-at "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --policy-path signature-policy.json \
  --extractor-output-path .lake/signature-current/sig0.json \
  --tag ci \
  --out .lake/signature-current/snapshot.json
```

before / after の snapshot から diff report を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- signature-diff \
  --before-snapshot .lake/signature-previous/snapshot.json \
  --after-snapshot .lake/signature-current/snapshot.json \
  --before-sig0 .lake/signature-previous/sig0.json \
  --after-sig0 .lake/signature-current/sig0.json \
  --pr-metadata .lake/pr-metadata-123.json \
  --out .lake/signature-current/diff-report.json
```

`signature-diff` は `diff` alias でも呼び出せる。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- diff \
  --before .lake/signature-previous/snapshot.json \
  --after .lake/signature-current/snapshot.json \
  --out .lake/signature-current/diff-report.json
```

diff report は次を持つ。

- `comparisonStatus`: primary diff として扱えるか。
- `deltaSignatureSigned`: after - before の符号付き差分。
- `worsenedAxes`: risk が増えた軸。
- `improvedAxes`: risk が減った軸。
- `unchangedAxes`: 変化しなかった軸。
- `unmeasuredAxes`: 未評価または比較不能な軸と理由。
- `evidenceDiff`: component / edge / policy violation の追加削除。
- `attribution`: PR metadata に基づく原因候補。因果証明ではなく調査開始点である。

代表的な diff report 抜粋:

```json
{
  "schemaVersion": "signature-diff-report-v0",
  "comparisonStatus": {
    "primaryDiffEligible": true,
    "reasons": []
  },
  "worsenedAxes": [
    {
      "axis": "fanoutRisk",
      "before": 3,
      "after": 5,
      "delta": 2
    }
  ],
  "unmeasuredAxes": [
    {
      "axis": "runtimePropagation",
      "reason": "runtime dependency graph not provided",
      "beforeMeasured": false,
      "afterMeasured": false
    }
  ]
}
```

`validationSummary.result = fail` または `not_run` の snapshot、extractor / rule set / policy が一致しない比較は
`comparisonStatus.primaryDiffEligible = false` になる。

## AIR を作る

Sig0 output、validation report、diff report、PR metadata を AIR v0 に正規化する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- air \
  --sig0 .lake/signature-current/sig0.json \
  --validation .lake/signature-current/validation.json \
  --diff .lake/signature-current/diff-report.json \
  --pr-metadata .lake/pr-metadata-123.json \
  --law-policy signature-policy.json \
  --out .lake/signature-current/air.json
```

AIR では `static_edges` / `runtime_edges` を出さず、`relations` を canonical representation として使う。
各 signature axis は `measurementBoundary` に `measuredZero`, `measuredNonzero`, `unmeasured` を持つため、
測定済み 0 と未測定の placeholder 0 を分けて読める。

AIR の参照整合性を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- validate-air \
  --input .lake/signature-current/air.json \
  --out .lake/signature-current/air-validation.json
```

`validate-air` は dangling component / artifact / evidence / claim refs、coverage universe refs、
claim classification と `measurementBoundary` の不整合を検出する。
`claimClassification = measured` の claim に `evidenceRefs` がない場合は通常 warning とし、
CI で fail にしたい場合は `--strict-measured-evidence` を付ける。

canonical AIR fixture は `tools/archsig/tests/fixtures/air` に置く。

- `good_extension.json`
- `hidden_interaction.json`
- `policy_violation.json`
- `unmeasured_runtime_semantic.json`

## Theorem Precondition Check を作る

AIR v0 の claim を static theorem package v0 registry に照合する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- theorem-check \
  --air .lake/signature-current/air.json \
  --out .lake/signature-current/theorem-check.json
```

初期 registry は static theorem package に限定し、Lean 側 entrypoint として
`SelectedStaticSplitExtension` を持つ。参照できる theorem refs は
`SelectedStaticSplitExtension`, `CoreEdgesPreserved`,
`DeclaredInterfaceFactorization`, `NoNewForbiddenStaticEdge`,
`EmbeddingPolicyPreserved` である。

`claimLevel = formal`, `claimClassification = proved`, registry 登録済み theorem refs、
かつ `missingPreconditions = []` の claim だけを `FORMAL_PROVED` として表示する。
tooling の `measured` claim は `MEASURED_WITNESS` のまま残し、formal proof claim へ
昇格しない。missing preconditions が残る formal/proved claim は
`BLOCKED_FORMAL_CLAIM` として表示する。

## Feature Extension Report を作る

AIR v0 から PR review 用の static Feature Extension Report v0 を生成する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- feature-report \
  --air .lake/signature-current/air.json \
  --out .lake/signature-current/feature-report.json
```

`feature-report` は static / policy 層の測定済み evidence だけを根拠に
`splitStatus` を `split`, `non_split`, `unknown`, `unmeasured` へ分類する。
runtime / semantic 層が未測定の場合は `coverageGaps` と `nonConclusions` に
`UNMEASURED` として残し、static split の根拠にはしない。
Feature Extension Report には `theoremPreconditionSummary` と
`theoremPreconditionChecks` も含まれるため、`MEASURED` witness と `FORMAL_PROVED`
claim の境界を report 内で確認できる。

## Synthesis Constraints を検査する

synthesis constraint artifact v0 は、constraint refs、candidate refs、required /
coverage / exactness assumptions、unsupported constructs、non-conclusions を明示する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- synthesis-constraints \
  --input tools/archsig/tests/fixtures/minimal/synthesis_constraints_candidate.json \
  --out .lake/signature-current/synthesis-constraints.json
```

候補が返った場合は `SynthesisSoundnessPackage.candidate_satisfies` などの
soundness package refs と前提境界を併読する。solver が candidate を返さないことは
valid no-solution certificate ではないため、`noSolutionBoundary` と
`nonConclusions` で solver completeness を主張しないことを固定する。

## PR Metadata / Dataset を作る

GitHub API の PR detail / files / reviews JSON から `pr-metadata.json` を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- pr-metadata \
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
GraphQL reviewThreads JSON を別途持つ場合は `--review-threads` で渡せる。

before / after の Sig0 output と PR metadata から empirical dataset record を作る。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- dataset \
  --before .lake/sig0-base.json \
  --after .lake/sig0-head.json \
  --pr-metadata pr-metadata.json \
  --after-role head \
  --out .lake/empirical-dataset-v0.json
```

`--after-role` は `head` または `merge` を指定する。
`merge` を指定する場合は PR metadata の `pullRequest.mergeCommit` が必須である。

dataset 出力は `schemaVersion: "empirical-signature-dataset-v0"` の単一 record である。
`deltaSignatureSigned` は before / after の両方で測定済み、かつ値が `null` でない軸だけを
符号付き差分として出す。policy 未指定の `boundaryViolationCount` のような placeholder 0 は
`null` delta として保持する。

## Relation Complexity

workflow 単位の `RelationComplexityObservation` を candidate evidence JSON から生成する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- relation-complexity \
  --input relation-complexity-candidates.json \
  --out relation-complexity-observation.json
```

入力 schema は `schemaVersion: "relation-complexity-candidates/v0"` で、
`repository`, `revision`, `measurementUniverse`, `workflow`, `evidenceCandidates` を持つ。
出力 schema は `schemaVersion: "relation-complexity-observation/v0"` である。

`relation-complexity-rules/v0` は次の tag を数える。

- `constraints`
- `compensations`
- `projections`
- `failureTransitions`
- `idempotencyRequirements`

同じ evidence item 内の同一 tag は 1 回だけ数える。
`application-owned` と `application-configured` は counting candidate とし、
`framework-generated` や未対応 framework の候補は `excludedEvidence` に理由を残す。

## 現状で可能な診断

単一 revision の構造診断:

| 診断 | 主に見る parameter / field | 高い、または増えた場合に言えること | 注意 |
| --- | --- | --- | --- |
| 静的依存の循環検出 | `signature.hasCycle`, `signature.sccMaxSize`, `sccExcessSize` | import graph に循環がある。`sccMaxSize` が大きいほど、相互到達できる component 群が大きく、分解可能性のリスクが高い。 | `hasCycle = 0` は scan 対象内の import graph で循環が見つからないという意味。runtime dependency や動的依存の非循環性までは言わない。 |
| SCC リスク | `sccMaxSize`, `sccExcessSize`, `weightedSccRisk` | 大きい SCC は一部変更が同じ SCC 内へ波及しやすい候補になる。`sccExcessSize` は singleton SCC を 0 risk として正規化した値。 | `weightedSccRisk` は重み入力がある場合だけ測れる。重みの意味は policy / empirical 側で決める。 |
| 依存深度 | `maxDepth` | 依存 chain が深い。変更や理解のために辿る階層が長い可能性がある。 | 現状は bounded max depth。循環リスクは `hasCycle` / SCC 軸で別に読む。 |
| fanout / 依存集中 | `fanoutRisk`, `maxFanout` | `fanoutRisk` が増えると測定対象内の依存辺総数が増えたことを示す。`maxFanout` が高い component は多くの依存先を持つ局所的な結合点候補。 | fanout 増加は常に悪ではない。新機能追加や module 追加でも増えるため、差分 edge と PR context を併読する。 |
| 到達 cone / 変更波及候補 | `reachableConeSize` | ある component から到達できる依存先集合が大きい。変更理解や影響確認の範囲が広がる候補。 | edge 方向は `source depends on target`。障害源から影響を受ける側の blast radius とは向きが違う。 |
| boundary violation | `boundaryViolationCount`, `policyViolations[]` | policy で禁止した境界越え依存がある。増えた場合、意図した layer / domain boundary が破られている候補。 | policy 未指定なら placeholder 0 でも `metricStatus.boundaryViolationCount.measured = false`。違反なしとは読まない。 |
| abstraction violation | `abstractionViolationCount`, `policyViolations[]` | 抽象化 rule に反する直接依存がある。DIP / abstraction boundary の破れ候補。 | 現状の CLI は policy-based な tooling evidence。Lean の `ProjectionSound` witness そのものではない。 |
| runtime exposure | `runtimePropagation`, `runtimeDependencyGraph`, `runtimeEdgeEvidence[]` | runtime evidence 上で、依存辺の向きに沿った exposure radius が大きい。実行時依存の連鎖が広い候補。 | runtime edge evidence を渡した場合だけ測定済み。incident root cause からの blast radius は reverse reachability 由来の別 metric として扱う。 |
| relation complexity | `relationComplexity`, `counts.*`, `excludedEvidence[]` | workflow に制約、補償、projection、失敗遷移、冪等性要求が多い。状態遷移設計や運用リスクのレビュー対象候補。 | candidate evidence からの observation。実 repository での完全自動抽出や品質相関はまだ empirical hypothesis。 |

before / after の差分診断:

| 診断 | 主に見る parameter / field | 高い、または増えた場合に言えること | 注意 |
| --- | --- | --- | --- |
| before / after 差分 | `worsenedAxes`, `improvedAxes`, `unchangedAxes`, `deltaSignatureSigned` | どの signature axis が悪化、改善、維持されたかを判断できる。 | `deltaSignatureSigned` の正値は risk 増加、負値は risk 減少。未評価軸は `null`。 |
| 未評価 / 比較不能軸 | `metricStatus`, `metricDeltaStatus`, `unmeasuredAxes` | 測定されていない、または before / after で比較できない軸を識別できる。 | AI agent は signature 値だけで判断せず、未評価理由を必ず併読する。 |
| evidence diff | `evidenceDiff.componentDelta`, `evidenceDiff.edgeDelta`, `evidenceDiff.policyViolationDelta` | 追加 / 削除された component、dependency edge、policy violation を確認できる。悪化軸の具体的な調査入口になる。 | `--before-sig0` / `--after-sig0` を diff に渡した場合に raw evidence diff が有効になる。 |
| PR attribution candidate | `attribution.candidates[]` | changed components、edge diff、policy violation diff から、どの PR が悪化軸に関係しそうかを候補として出せる。 | 因果証明ではない。confidence は調査優先度であり、最終判断ではない。 |

現状では、セキュリティ脆弱性診断、一般的な code smell 診断、runtime dependency の自動抽出、
incident / repair cost との統計的相関判定、自然言語の修正提案は行わない。

## GitHub Actions

[Signature diff report workflow](../../.github/workflows/signature-diff.yml) は、PR / push / schedule /
manual run で次を実行する。

1. before / after ref を解決する。
2. Sig0 output を作る。
3. validation report を作る。
4. snapshot を作る。
5. `signature-diff-report-v0` を作る。
6. workflow summary と artifact を保存する。

PR では GitHub API から PR metadata を生成し、diff report の attribution candidate に含める。
policy / runtime evidence を渡していない軸は `unmeasuredAxes` に理由を残し、
placeholder 0 を risk 0 として扱わない。

## Test

ローカル検証は次で行う。

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
```

CI では GitHub Actions の `archsig cargo test` job が同じコマンドを実行する。
unit tests は実装 module の近くに置き、parse / graph / extraction / validation / dataset /
theorem precondition / relation complexity の局所的な不変条件を検証する。
`tests/fixtures/minimal` と `tests/fixtures/air` は representative fixture として、Sig0、
policy violation、runtime dependency graph、dataset、snapshot diff、AIR、feature report、
theorem precondition、relation complexity の回帰確認に使う。
`tests/cli.rs` は CLI と JSON schemaVersion / contract の integration test として維持する。
