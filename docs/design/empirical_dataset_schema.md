# empirical dataset v0 schema

Lean status: `empirical hypothesis` / dataset schema.

この文書は Issue [#108](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/108)
の設計メモである。目的は、Signature v1 core / extension output と PR metadata を
結合し、`docs/design/empirical_protocol.md` の H1 から H4 を検証できる最小 dataset
record を固定することである。

ここで定義する dataset は Lean theorem の対象ではない。Lean 側は有限 universe 上の
構造的事実を証明し、dataset は extractor / GitHub metadata / issue or incident
metadata を結合した実証研究用の観測表として扱う。

## record 粒度

最小単位は PR 単位の record である。1 record は、1 つの repository の 1 つの PR について、
base commit と head または merge commit の Signature、PR metadata、関連 issue /
incident metadata、未評価 metric の状態を保持する。

```text
EmpiricalSignatureDatasetV0 =
  schemaVersion: "empirical-signature-dataset-v0"
  repository: RepositoryRef
  pullRequest: PullRequestRef
  signatureBefore: SignatureSnapshot
  signatureAfter: SignatureSnapshot
  deltaSignatureSigned: NullableSignatureIntVector
  metricDeltaStatus: MetricDeltaStatus
  prMetrics: PullRequestMetrics
  issueIncidentLinks: List IssueIncidentLink
  analysisMetadata: AnalysisMetadata
```

`signatureBefore` は PR base commit、`signatureAfter` は PR head commit または merge
commit で計算する。どちらを使ったかは `analysisMetadata.signatureAfterCommitRole`
に記録する。head と merge commit の両方を計算し、値が異なる場合は追加 record を作る
のではなく、差分を `analysisMetadata.alternateSignatureAfter` に残す。

## SignatureSnapshot

`SignatureSnapshot` は extractor output の Signature 値と、その値の測定状態を同時に
保持する。

```text
SignatureSnapshot =
  commit: GitCommitRef
  extractor:
    name: String
    version: String
    ruleSetVersion: String
    policyVersion: String | null
  signature: ArchitectureSignatureV1DatasetShape
  metricStatus: MetricStatus
```

`ArchitectureSignatureV1DatasetShape` は Lean 側の `ArchitectureSignatureV1Core` と
`ArchitectureSignatureV1` を dataset 用に flatten した形で保持する。v0 互換軸は
必須、extension axis は測定できない場合に `null` を許す。

| field | 型 | 扱い |
| --- | --- | --- |
| `hasCycle` | integer >= 0 | v0 互換軸。0/1 indicator として扱う。 |
| `sccMaxSize` | integer >= 0 | v0 互換軸。 |
| `maxDepth` | integer >= 0 | v0 互換軸。 |
| `fanoutRisk` | integer >= 0 | v0 互換軸。Sig0 extractor では `totalFanout` 相当。 |
| `boundaryViolationCount` | integer >= 0 | v0 互換軸。policy 未指定の 0 は placeholder。 |
| `abstractionViolationCount` | integer >= 0 | v0 互換軸。policy 未指定の 0 は placeholder。 |
| `sccExcessSize` | integer >= 0 | v1 core axis。 |
| `maxFanout` | integer >= 0 | v1 core axis。 |
| `reachableConeSize` | integer >= 0 | v1 core axis。 |
| `weightedSccRisk` | integer >= 0 or null | optional extension axis。 |
| `projectionSoundnessViolation` | integer >= 0 or null | optional extension axis。 |
| `lspViolationCount` | integer >= 0 or null | optional extension axis。 |
| `nilpotencyIndex` | integer >= 0 or null | optional extension axis。`null` は未評価または非 DAG / 未成立。 |
| `runtimePropagation` | integer >= 0 or null | optional extension axis。 |
| `relationComplexity` | integer >= 0 or null | empirical extension axis。 |
| `empiricalChangeCost` | integer >= 0 or null | 目的変数側の補助軸。通常は PR / issue metadata から別列で読む。 |

`null` は risk 0 ではない。Lean 側の `Option Nat.none`、および extractor output の
`metricStatus.<axis>.measured = false` と同じく、未評価または当該 rule set では解釈
できない値を表す。

## MetricStatus

`MetricStatus` は `ArchitectureSignatureV1DatasetShape` の全軸について entry を持つ。
entry がない軸を `measured = true` と推定しない。過去の extractor output で entry が
欠けている場合は、dataset への取り込み時に `measured = false` とし、理由を
`legacy data without metricStatus entry` のように明示する。

```text
MetricStatus.<axis> =
  measured: Bool
  reason: String | null
  source: String | null
```

`measured = false` の軸では、対応する `signature.<axis>` が 0 でも違反なしや risk 0 と
解釈しない。optional extension axis で `signature.<axis> = null` の場合も、
`metricStatus.<axis>.measured = false` と理由を記録する。

## signed delta

`deltaSignatureSigned` は before / after の差分を `Int` として保持する。改善による負の
値を 0 に丸めない。

```text
NullableSignatureIntVector =
  hasCycle: Int | null
  sccMaxSize: Int | null
  maxDepth: Int | null
  fanoutRisk: Int | null
  boundaryViolationCount: Int | null
  abstractionViolationCount: Int | null
  sccExcessSize: Int | null
  maxFanout: Int | null
  reachableConeSize: Int | null
  weightedSccRisk: Int | null
  projectionSoundnessViolation: Int | null
  lspViolationCount: Int | null
  nilpotencyIndex: Int | null
  runtimePropagation: Int | null
  relationComplexity: Int | null
```

各軸の delta は次で決める。

- before / after の両方で `metricStatus.<axis>.measured = true` なら
  `after.signature.<axis> - before.signature.<axis>` を入れる。
- before / after のどちらかが `measured = false`、または optional extension axis が
  `null` の場合、delta は `null` にする。
- `hasCycle` は `0` または `1` の risk indicator として扱い、delta は `-1`, `0`, `1`,
  `null` のいずれかにする。
- `nilpotencyIndex = null` は risk 0 ではないため、片側が `null` の場合も delta は
  `null` にする。

`metricDeltaStatus.<axis>` には delta が使えるかどうかを明示する。

| field | 型 | 意味 |
| --- | --- | --- |
| `comparable` | boolean | before / after の差分を主要分析に使えるか。 |
| `reason` | string | `comparable = false` の理由。 |
| `beforeMeasured` | boolean | before 側が測定済みか。 |
| `afterMeasured` | boolean | after 側が測定済みか。 |

`deltaSignatureSigned.<axis> = 0` と `deltaSignatureSigned.<axis> = null` は区別する。
前者は測定済みで変化なし、後者は欠損または比較不能である。

## PR metadata

`PullRequestRef` と `PullRequestMetrics` は、分析で交絡要因として使う列を含む。

```text
PullRequestRef =
  number: Nat
  author: String
  createdAt: Timestamp
  mergedAt: Timestamp | null
  baseCommit: String
  headCommit: String
  mergeCommit: String | null
  labels: List String
  isBotGenerated: Bool

PullRequestMetrics =
  changedFiles: Nat
  changedLinesAdded: Nat
  changedLinesDeleted: Nat
  changedComponents: List String
  reviewCommentCount: Nat
  reviewThreadCount: Nat
  reviewRoundCount: Nat
  firstReviewLatencyHours: Number | null
  approvalLatencyHours: Number | null
  mergeLatencyHours: Number | null
```

PR size、review policy、bot-generated PR は Signature との関係を歪めやすいため、
除外条件としてだけでなく、pilot dataset の列として必ず保持する。

## issue / incident links

Issue / incident metadata は目的変数または stratification に使う。PR と issue の対応は
完全とは限らないため、複数 link を許す。

```text
IssueIncidentLink =
  kind: "issue" | "incident"
  id: String
  url: String | null
  severity: String | null
  labels: List String
  openedAt: Timestamp | null
  closedAt: Timestamp | null
  affectedComponents: List String
  rollback: Bool | null
  reopened: Bool | null
```

障害修正コストを分析する場合は、incident link と hotfix PR を別 record として重複計上
しないように、`analysisMetadata.primaryCostRecord` を 1 つだけ指定する。

## relationComplexity

`relationComplexity` は単一スコアだけで評価しない。dataset では派生合計値とは別に、
構成要素ベクトルを `analysisMetadata.relationComplexityComponents` に保持する。

```text
RelationComplexityComponents =
  constraints: Nat
  compensations: Nat
  projections: Nat
  failureTransitions: Nat
  idempotencyRequirements: Nat
```

H4 では、`relationComplexity` の合計値だけでなく、構成要素別の説明変数を使える形で
保存する。

## JSON fragment

次は欠損値規約を示す抜粋である。実 dataset では `metricStatus` と
`metricDeltaStatus` に全軸の entry を置く。

```json
{
  "schemaVersion": "empirical-signature-dataset-v0",
  "repository": {
    "owner": "example",
    "name": "service",
    "defaultBranch": "main"
  },
  "pullRequest": {
    "number": 42,
    "author": "alice",
    "createdAt": "2026-04-01T00:00:00Z",
    "mergedAt": "2026-04-02T00:00:00Z",
    "baseCommit": "base",
    "headCommit": "head",
    "mergeCommit": "merge",
    "labels": ["feature"],
    "isBotGenerated": false
  },
  "signatureBefore": {
    "commit": {"sha": "base", "role": "base"},
    "extractor": {
      "name": "sig0-extractor",
      "version": "0.1.0",
      "ruleSetVersion": "sig0-v0",
      "policyVersion": null
    },
    "signature": {
      "hasCycle": 0,
      "sccMaxSize": 1,
      "maxDepth": 3,
      "fanoutRisk": 12,
      "boundaryViolationCount": 0,
      "abstractionViolationCount": 0,
      "sccExcessSize": 0,
      "maxFanout": 4,
      "reachableConeSize": 7,
      "weightedSccRisk": null,
      "projectionSoundnessViolation": null,
      "lspViolationCount": null,
      "nilpotencyIndex": null,
      "runtimePropagation": null,
      "relationComplexity": null,
      "empiricalChangeCost": null
    },
    "metricStatus": {
      "boundaryViolationCount": {
        "measured": false,
        "reason": "policy file not provided"
      }
    }
  },
  "signatureAfter": {
    "commit": {"sha": "merge", "role": "merge"},
    "extractor": {
      "name": "sig0-extractor",
      "version": "0.1.0",
      "ruleSetVersion": "sig0-v0",
      "policyVersion": null
    },
    "signature": {
      "hasCycle": 0,
      "sccMaxSize": 1,
      "maxDepth": 4,
      "fanoutRisk": 14,
      "boundaryViolationCount": 0,
      "abstractionViolationCount": 0,
      "sccExcessSize": 0,
      "maxFanout": 5,
      "reachableConeSize": 9,
      "weightedSccRisk": null,
      "projectionSoundnessViolation": null,
      "lspViolationCount": null,
      "nilpotencyIndex": null,
      "runtimePropagation": null,
      "relationComplexity": null,
      "empiricalChangeCost": null
    },
    "metricStatus": {
      "boundaryViolationCount": {
        "measured": false,
        "reason": "policy file not provided"
      }
    }
  },
  "deltaSignatureSigned": {
    "hasCycle": 0,
    "sccMaxSize": 0,
    "maxDepth": 1,
    "fanoutRisk": 2,
    "boundaryViolationCount": null,
    "abstractionViolationCount": null,
    "sccExcessSize": 0,
    "maxFanout": 1,
    "reachableConeSize": 2,
    "weightedSccRisk": null,
    "projectionSoundnessViolation": null,
    "lspViolationCount": null,
    "nilpotencyIndex": null,
    "runtimePropagation": null,
    "relationComplexity": null
  },
  "metricDeltaStatus": {
    "boundaryViolationCount": {
      "comparable": false,
      "reason": "policy file not provided before and after",
      "beforeMeasured": false,
      "afterMeasured": false
    }
  },
  "prMetrics": {
    "changedFiles": 5,
    "changedLinesAdded": 120,
    "changedLinesDeleted": 20,
    "changedComponents": ["Service.A", "Service.B"],
    "reviewCommentCount": 3,
    "reviewThreadCount": 2,
    "reviewRoundCount": 1,
    "firstReviewLatencyHours": 4.5,
    "approvalLatencyHours": 12.0,
    "mergeLatencyHours": 24.0
  },
  "issueIncidentLinks": [],
  "analysisMetadata": {
    "signatureAfterCommitRole": "merge",
    "excludedFromPrimaryAnalysis": false,
    "exclusionReasons": [],
    "primaryCostRecord": null,
    "relationComplexityComponents": null
  }
}
```

この例では `boundaryViolationCount` の値は before / after とも 0 だが、
`metricStatus.measured = false` なので delta は `null` である。したがって、境界違反が
存在しない PR として H4 に投入してはならない。

## H1 から H4 への対応

| 仮説 | 主要説明変数 | 目的変数 / metadata | 必須の比較可能条件 |
| --- | --- | --- | --- |
| H1 | `deltaSignatureSigned.maxDepth`, `deltaSignatureSigned.reachableConeSize` | `changedFiles`, `changedComponents` | 対象軸の `metricDeltaStatus.comparable = true` |
| H2 | `signatureBefore.hasCycle`, `signatureBefore.sccMaxSize`, `signatureBefore.sccExcessSize` | issue / incident close time, hotfix scope | cycle / SCC 軸が before 側で測定済み |
| H3 | `deltaSignatureSigned.fanoutRisk`, `signatureBefore.maxFanout` | review comments, review rounds, approval latency | fanout 軸が before / after で測定済み |
| H4 | `boundaryViolationCount`, `relationComplexity` and its components | future co-change, incident count, repair time | policy と relation rule set が測定済み |

欠損率が高い軸は risk 0 として補完しない。pilot では、欠損率を仮説ごとに報告し、
必要なら exploratory analysis と primary analysis を分ける。
