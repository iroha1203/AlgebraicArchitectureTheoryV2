# Feature extension dataset v0 schema

Lean status: `empirical hypothesis` / tooling validation.

この文書は Phase B6 の feature extension dataset の最小 schema を固定する。目的は
`pr-history-dataset-v0` と `feature-extension-report-v0`、必要に応じて
`theorem-precondition-check-report-v0` を PR 単位で join し、H1-H5 の correlation
analysis に渡せる観測列を作ることである。

この dataset は Lean theorem の対象ではない。Feature Extension Report の分類、obstruction
witness、coverage gap、repair suggestion は outcome の原因として証明されたものではなく、
review cost、follow-up fix、rollback、incident scope などと後続で照合する入力である。

## record 粒度

最小単位は 1 repository の 1 PR と 1 Feature Extension Report の対応である。

```text
FeatureExtensionDatasetV0 =
  schemaVersion: "feature-extension-dataset-v0"
  repository: RepositoryRef
  records: List FeatureExtensionDatasetRecordV0
  analysisMetadata: FeatureExtensionDatasetAnalysisMetadata

FeatureExtensionDatasetRecordV0 =
  pullRequest: PullRequestRef
  prHistoryRecordRef: FeatureExtensionPrHistoryRecordRef
  changedComponents: List String
  featureReportRef: PrHistoryArtifactRef
  architectureId: String
  feature: AirFeature
  splitStatus: "split" | "non_split" | "unmeasured"
  claimClassification: String
  obstructionWitnessTaxonomy: List FeatureExtensionObstructionTaxon
  coverageGaps: List FeatureExtensionDatasetCoverageGap
  repairSuggestionAdoptionCandidates: List FeatureExtensionRepairSuggestionAdoptionCandidate
  theoremPreconditionBoundary: FeatureExtensionTheoremPreconditionBoundary
  artifactRefs: FeatureExtensionDatasetArtifactRefs
  nonConclusions: List String
```

`PullRequestRef`、`RepositoryRef`、`PrHistoryArtifactRef` は PR history dataset と同じ形を
使う。join key は repository、PR number、Feature Extension Report artifact path である。

## obstruction witness taxonomy

```text
FeatureExtensionObstructionTaxon =
  kind: String
  layer: String
  claimLevel: String
  claimClassification: String
  measurementBoundary: String
  witnessCount: Nat
  witnessRefs: List String
  components: List String
```

`kind` は Feature Extension Report の witness kind を保持する。これは taxonomy column であり、
obstruction witness が outcome を引き起こしたという causal proof ではない。

## coverage gaps

```text
FeatureExtensionDatasetCoverageGap =
  layer: String
  measurementBoundary: String
  unmeasuredAxes: List String
  unsupportedConstructs: List String
  nonConclusions: List String
```

coverage gap は missing / private / unsupported data の boundary を明示する。gap があることも、
witness がないことも、measured-zero evidence として扱わない。

## repair suggestion adoption candidates

```text
FeatureExtensionRepairSuggestionAdoptionCandidate =
  suggestionId: String
  repairRuleId: String | null
  targetWitnessKind: String
  proposedOperation: String
  sourceWitnessRefs: List String
  sourceCoverageGapRefs: List String
  adoptionStatus: "candidate"
  requiredPreconditions: List String
  traceability: List String
  nonConclusions: List String
```

repair suggestion は後続研究で「提案された修正が採用されたか」を追跡する候補列である。
採用、成功、全 obstruction removal、global flatness preservation、empirical cost 改善は
この dataset だけから結論しない。

## theorem precondition boundary

```text
FeatureExtensionTheoremPreconditionBoundary =
  summary: TheoremPreconditionCheckSummary
  missingPreconditions: List String
  blockedClaimRefs: List String
  measuredWitnessCount: Nat
  formalProvedClaimCount: Nat
  nonConclusions: List String
```

theorem precondition は Feature Extension Report に埋め込まれた summary / checks、または
明示された theorem check report から得る。これは formal claim と measured witness の境界を
dataset に残すための列であり、新しい Lean proof ではない。

## CLI

`archsig feature-extension-dataset` は PR history dataset と Feature Extension Report を
join して dataset を生成する。

```bash
archsig feature-extension-dataset \
  --pr-history pr-history.json \
  --feature-report feature-extension-report.json \
  --theorem-check-report theorem-check.json \
  --out feature-extension-dataset.json
```

`--theorem-check-report` は省略できる。省略時は Feature Extension Report 内の theorem
precondition summary / checks を使う。

## non-conclusions

`analysisMetadata.nonConclusions` は少なくとも次を含む。

- architecture lawfulness を結論しない。
- Lean theorem claim を確立しない。
- Feature Extension Report の分類から outcome への因果効果を推定しない。
- missing / private artifact を measured-zero evidence として扱わない。
