# Outcome linkage dataset v0 schema

Lean status: `empirical hypothesis` / tooling validation.

この文書は Phase B6 の incident / rollback / review outcome linkage schema を固定する。
目的は `feature-extension-dataset-v0` の obstruction profile と、review cost、
follow-up fix、rollback、incident scope、MTTR などの outcome 観測を PR 単位で join し、
H1-H3 の correlation analysis input に渡すことである。

この dataset は Lean theorem の対象ではない。obstruction witness と outcome の対応は
causal proof ではなく、明示的な measurement boundary を持つ観測列である。

## record 粒度

最小単位は 1 repository の 1 PR と 1 outcome observation の対応である。

```text
OutcomeLinkageDatasetV0 =
  schemaVersion: "outcome-linkage-dataset-v0"
  repository: RepositoryRef
  records: List OutcomeLinkageDatasetRecordV0
  analysisMetadata: OutcomeLinkageAnalysisMetadata

OutcomeLinkageDatasetRecordV0 =
  pullRequest: PullRequestRef
  featureDatasetRecordRef: OutcomeFeatureDatasetRecordRef
  changedComponents: List String
  splitStatus: "split" | "non_split" | "unmeasured"
  claimClassification: String
  obstructionWitnessTaxonomy: List FeatureExtensionObstructionTaxon
  outcomeObservation: OutcomeObservationV0
  correlationInputs: OutcomeCorrelationInputs
  nonConclusions: List String
```

join key は repository と PR number である。Feature Extension Report artifact path と
architecture id は `featureDatasetRecordRef` に残す。

## outcome observation

```text
OutcomeObservationV0 =
  prNumber: Nat
  reviewCost: ReviewCostOutcome
  followUpFixCount: OutcomeMetric Nat
  rollback: OutcomeMetric Bool
  incidentAffectedComponentCount: OutcomeMetric Nat
  mttrHours: OutcomeMetric Float
  traceability: OutcomeTraceabilityRefs
  nonConclusions: List String

OutcomeMetric T =
  boundary: "measured" | "unavailable" | "private" | String
  value: T | null
  reason: String | null
  sourceRefs: List String
  nonConclusions: List String
```

`value = null` は、未観測・非公開・集計不能を表す。`null` や missing record を
measured-zero evidence として扱わない。

## traceability

```text
OutcomeTraceabilityRefs =
  prRefs: List OutcomeExternalRef
  issueRefs: List OutcomeExternalRef
  incidentRefs: List OutcomeExternalRef
  artifactRefs: List PrHistoryArtifactRef
  missingOrPrivateData: List String
  nonConclusions: List String
```

PR / issue / incident ref は traceability のために保存する。private incident、redacted
timeline、missing issue link は non-conclusion として残し、障害や rollback がなかったという
結論には変換しない。

## CLI

`archsig outcome-linkage-dataset` は Feature Extension dataset と outcome observation input を
join して dataset を生成する。

```bash
archsig outcome-linkage-dataset \
  --feature-dataset feature-extension-dataset.json \
  --outcome outcome-observations.json \
  --out outcome-linkage-dataset.json
```

## non-conclusions

`analysisMetadata.nonConclusions` は少なくとも次を含む。

- obstruction profile から outcome への因果効果を推定しない。
- runtime / semantic / extractor completeness を確立しない。
- Architecture Signature を単一スコアの品質 ranking として扱わない。
- missing / private outcome data を measured-zero evidence として扱わない。
