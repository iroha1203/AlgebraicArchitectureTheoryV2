# PR history dataset v0 schema

Lean status: `empirical hypothesis` / tooling validation.

この文書は Phase B6 の PR history dataset の最小 schema を固定する。目的は GitHub PR
metadata と ArchSig artifact refs を PR 単位で安定して保存し、後続の feature extension
dataset や incident / rollback / review outcome linkage に渡すことである。

この dataset は Lean theorem の対象ではない。architecture lawfulness、設計原則の成立、
または outcome への因果効果を PR metadata だけから結論しない。

## record 粒度

最小単位は 1 repository の 1 PR である。

```text
PrHistoryDatasetV0 =
  schemaVersion: "pr-history-dataset-v0"
  repository: RepositoryRef
  records: List PrHistoryRecordV0
  analysisMetadata: PrHistoryAnalysisMetadata

PrHistoryRecordV0 =
  pullRequest: PullRequestRef
  changedFileSummary: ChangedFileSummary
  reviewMetadata: ReviewMetadata
  artifactRefs: PrHistoryArtifactRefs
```

`RepositoryRef` と `PullRequestRef` は `empirical-signature-dataset-v0` と同じ形を使う。
これにより、PR history record は before / after Signature dataset と同じ PR key で
join できる。

## changed file summary

```text
ChangedFileSummary =
  changedFiles: Nat
  additions: Nat
  deletions: Nat
  changedComponents: List String
  files: List ChangedFileEntry

ChangedFileEntry =
  path: String
  additions: Nat | null
  deletions: Nat | null
  status: String | null
```

`changedComponents` は Lean module path を component id へ写した列である。非 Lean file は
`files` には残すが、component id へは推定しない。

## review metadata

```text
ReviewMetadata =
  reviewCommentCount: Nat
  reviewThreadCount: Nat
  reviewRoundCount: Nat
  reviewerCount: Nat
  reviewers: List String
  reviewStates: List String
  firstReviewLatencyHours: Number | null
  approvalLatencyHours: Number | null
  mergeLatencyHours: Number | null
```

reviewer count と latency は review cost の候補列であり、Signature axis の theorem claim
ではない。GitHub API の欠損や provider 差分がある場合、未取得値は `null` または 0 件と
して明示する。

## artifact refs

```text
PrHistoryArtifactRefs =
  signatureArtifacts: List PrHistoryArtifactRef
  featureExtensionReports: List PrHistoryArtifactRef

PrHistoryArtifactRef =
  kind: String
  path: String
  commitRole: String | null
  schemaVersion: String | null
```

`signatureArtifacts` は `archsig-sig0-v0` などの Signature artifact を指す。
`featureExtensionReports` は `feature-extension-report-v0` を指す。artifact は参照として
保持し、存在・妥当性・claim boundary の検査は artifact 生成側または後続 dataset builder
で扱う。

## non-conclusions

`analysisMetadata.nonConclusions` は少なくとも次を含む。

- architecture lawfulness を結論しない。
- Lean theorem claim を確立しない。
- PR metadata だけから outcome への因果効果を推定しない。
