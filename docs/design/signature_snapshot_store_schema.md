# Signature snapshot store schema

Lean status: `empirical hypothesis` / tooling schema.

この文書は Issue [#157](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/157)
の設計メモである。目的は、weekly scan や任意期間比較に使う Architecture Signature
snapshot store の最小 record schema を固定することである。

ここで定義する store は Lean theorem の対象ではない。Lean 側は有限 universe 上の
構造的事実を証明し、snapshot store は extractor output、policy metadata、
validation summary、未評価軸を repository revision ごとに蓄積する tooling-side
evidence として扱う。

## record 粒度

最小単位は repository revision 単位の snapshot record である。1 record は、1 つの
repository の 1 revision について、scan 時刻、extractor version、policy id、
Architecture Signature、metric status、validation summary を保持する。

```text
SignatureSnapshotStoreRecordV0 =
  schemaVersion: "signature-snapshot-store-v0"
  repository: RepositoryRef
  revision: RepositoryRevisionRef
  scan: ScanMetadata
  extractor: ExtractorMetadata
  policy: PolicyMetadata
  signature: ArchitectureSignatureV1DatasetShape
  metricStatus: MetricStatus
  validationSummary: ValidationSummary
  artifacts: SnapshotArtifacts
  analysisMetadata: SnapshotAnalysisMetadata
```

PR 単位の before / after 比較ではなく、main branch の継続監視、週次 scan、
任意期間の diff、extractor / policy upgrade の影響確認に使う。

## Top-level fields

| field | 型 | 必須 | 意味 |
| --- | --- | --- | --- |
| `schemaVersion` | string | yes | v0 では `signature-snapshot-store-v0` 固定。 |
| `repository` | `RepositoryRef` | yes | repository の stable identity。 |
| `revision` | `RepositoryRevisionRef` | yes | 測定対象 revision。 |
| `scan` | `ScanMetadata` | yes | scan の実行時刻と実行環境 metadata。 |
| `extractor` | `ExtractorMetadata` | yes | extractor / rule set の version。 |
| `policy` | `PolicyMetadata` | yes | boundary / abstraction / runtime policy の identity。 |
| `signature` | `ArchitectureSignatureV1DatasetShape` | yes | 多軸 Signature 値。 |
| `metricStatus` | `MetricStatus` | yes | 各 axis の測定状態。 |
| `validationSummary` | `ValidationSummary` | yes | validation report の集計。 |
| `artifacts` | `SnapshotArtifacts` | no | raw extractor output や validation report への参照。 |
| `analysisMetadata` | `SnapshotAnalysisMetadata` | no | 除外理由、tag、補助 metadata。 |

`signature` は単一スコアではなく、多軸診断として保持する。derived total score を
top-level field として追加しない。

## Repository and revision

```text
RepositoryRef =
  owner: String
  name: String
  defaultBranch: String
  remoteUrl: String | null

RepositoryRevisionRef =
  sha: String
  ref: String | null
  branch: String | null
  committedAt: Timestamp | null
  parentShas: List String
```

`sha` は必須で、branch name だけを stable key として使わない。週次 scan で同じ
`sha` を再測定した場合も、extractor version や policy id が異なれば別 record として
保持する。

## Scan metadata

```text
ScanMetadata =
  scannedAt: Timestamp
  scannerId: String | null
  trigger: "manual" | "scheduled" | "ci" | "backfill"
  root: String | null
```

`scannedAt` は repository commit time ではなく測定実行時刻である。期間比較では
`revision.committedAt` と `scan.scannedAt` を混同しない。

## Extractor and policy metadata

```text
ExtractorMetadata =
  name: String
  version: String
  ruleSetVersion: String
  inputSchemaVersion: String

PolicyMetadata =
  policyId: String | null
  schemaVersion: String | null
  version: String | null
  sourcePath: String | null
  contentHash: String | null
```

主要 diff では、原則として `extractor.name`, `extractor.version`,
`extractor.ruleSetVersion`, `policy.policyId`, `policy.version` が一致する snapshot 同士を
比較する。これらが異なる比較は、tooling / policy upgrade の影響を含むため、主要分析
ではなく migration check または sensitivity analysis として扱う。

policy が未指定の場合も `policy` object は省略せず、`policyId = null` と
`metricStatus.<axis>.measured = false` の理由を残す。

## Signature and metric status

`signature` は
[empirical dataset v0 schema](empirical_dataset_schema.md) の
`ArchitectureSignatureV1DatasetShape` と同じ shape を使う。

`metricStatus` は全 axis について entry を持つ。

```text
MetricStatus.<axis> =
  measured: Bool
  reason: String | null
  source: String | null
```

測定済み 0 と未評価は必ず分ける。

- `metricStatus.<axis>.measured = true` かつ `signature.<axis> = 0` は、測定済みの
  risk 0 または violation 0 を表す。
- `metricStatus.<axis>.measured = false` の場合、`signature.<axis>` が 0 でも risk 0
  と解釈しない。
- optional extension axis の未評価値は `signature.<axis> = null` かつ
  `metricStatus.<axis>.measured = false` とする。

## Validation summary

snapshot record は validation report 全体を埋め込まず、主要分析で必要な summary を
保持する。詳細は artifact として参照する。

```text
ValidationSummary =
  schemaVersion: "component-universe-validation-report-v0" | null
  result: "pass" | "warn" | "fail" | "not_run"
  universeMode: "local-only" | "closed-with-external" | null
  failedCheckCount: Nat | null
  warningCheckCount: Nat | null
  notMeasuredCheckCount: Nat | null
  reportPath: String | null
```

`validationSummary.result = "fail"` の snapshot は、主要 diff から除外する。
`warn` の snapshot は主要 diff に含められるが、warning 種別を stratification または
sensitivity analysis に使えるように report 参照を残す。`not_run` は validation が
未実施であることを表し、主要 diff では原則除外する。

## Artifacts

```text
SnapshotArtifacts =
  extractorOutputPath: String | null
  validationReportPath: String | null
  policyPath: String | null
```

artifact path は store の読者が raw evidence を追跡するための参照であり、Lean witness
そのものではない。外部 object storage を使う場合は path の代わりに URI を入れてよい。

## Analysis metadata

```text
SnapshotAnalysisMetadata =
  excludedFromPrimaryDiff: Bool
  exclusionReasons: List String
  tags: List String
  notes: String | null
```

`excludedFromPrimaryDiff = true` の代表例は次である。

- `validationSummary.result = "fail"`。
- `validationSummary.result = "not_run"`。
- 比較対象と extractor version または policy id が一致しない。
- 必須 axis の `metricStatus.<axis>.measured = false`。

## Empirical dataset v0 との責務分担

snapshot store は revision ごとの測定事実を蓄積する。PR metadata、review latency、
issue / incident link、before / after の signed delta は保持しない。

[empirical dataset v0 schema](empirical_dataset_schema.md) は、PR 単位の
`signatureBefore`, `signatureAfter`, `deltaSignatureSigned`, `metricDeltaStatus`,
`prMetrics`, `issueIncidentLinks` を保持する分析用 record である。dataset builder は
snapshot store から before / after revision の snapshot を読むことができるが、delta は
dataset 側で計算し、片側でも未測定の axis は `null` にする。

この分離により、週次監視用の長期 store と PR / incident 分析用 dataset を混同せず、
measured 0 と unmeasured `null` の規約を両方で維持できる。

## JSON fragment

```json
{
  "schemaVersion": "signature-snapshot-store-v0",
  "repository": {
    "owner": "example",
    "name": "service",
    "defaultBranch": "main",
    "remoteUrl": "https://github.com/example/service"
  },
  "revision": {
    "sha": "abc123",
    "ref": "refs/heads/main",
    "branch": "main",
    "committedAt": "2026-04-25T00:00:00Z",
    "parentShas": ["parent123"]
  },
  "scan": {
    "scannedAt": "2026-04-26T00:00:00Z",
    "scannerId": "weekly-signature-scan",
    "trigger": "scheduled",
    "root": "."
  },
  "extractor": {
    "name": "sig0-extractor",
    "version": "0.1.0",
    "ruleSetVersion": "sig0-v0",
    "inputSchemaVersion": "sig0-extractor-v0"
  },
  "policy": {
    "policyId": "service-boundary-v0",
    "schemaVersion": "signature-policy-v0",
    "version": "2026-04-01",
    "sourcePath": "signature-policy.json",
    "contentHash": "sha256:..."
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
      "measured": true,
      "reason": null,
      "source": "policy:service-boundary-v0"
    },
    "runtimePropagation": {
      "measured": false,
      "reason": "runtime edge evidence not provided",
      "source": null
    }
  },
  "validationSummary": {
    "schemaVersion": "component-universe-validation-report-v0",
    "result": "warn",
    "universeMode": "local-only",
    "failedCheckCount": 0,
    "warningCheckCount": 1,
    "notMeasuredCheckCount": 1,
    "reportPath": ".lake/sig0-validation.json"
  },
  "artifacts": {
    "extractorOutputPath": ".lake/sig0.json",
    "validationReportPath": ".lake/sig0-validation.json",
    "policyPath": "signature-policy.json"
  },
  "analysisMetadata": {
    "excludedFromPrimaryDiff": false,
    "exclusionReasons": [],
    "tags": ["weekly"],
    "notes": null
  }
}
```

この例では `boundaryViolationCount = 0` は測定済み 0 である。一方、
`runtimePropagation = null` は未評価であり、runtime risk 0 ではない。
