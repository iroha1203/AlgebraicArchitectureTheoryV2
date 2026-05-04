# B6 empirical hypothesis evaluation plan

Lean status: `empirical hypothesis` / research validation.

この文書は Phase B6 の `pr-history-dataset-v0`、`feature-extension-dataset-v0`、
`outcome-linkage-dataset-v0` を接続し、Feature Extension Report / Architecture Signature /
obstruction profile と開発 outcome の対応を評価するための最小計画を固定する。

ここで扱う H1-H5 は `docs/aat_v2_tooling_design.md` の Phase B6 仮説である。
`docs/design/empirical_protocol.md` の Signature pilot 用 `H1a` / `H1b` / `H2` ...
とは別の番号体系として読む。

この評価は Lean theorem ではない。dataset は correlation analysis input であり、
Feature Extension Report の分類、obstruction witness、runtime exposure、review outcome
から、architecture lawfulness、causal proof、extractor completeness、または単一スコアの
品質 ranking を直接結論しない。

## 入力 dataset

Phase B6 の最小入力は次の三層である。

| dataset | schema | 役割 |
| --- | --- | --- |
| PR history | [PR history dataset v0 schema](pr_history_dataset_schema.md) | PR metadata、changed file summary、review metadata、Signature / Feature Extension Report artifact refs を保持する。 |
| Feature extension | [Feature extension dataset v0 schema](feature_extension_dataset_schema.md) | PR history と Feature Extension Report / theorem precondition boundary を join し、split status、obstruction witness taxonomy、coverage gaps、repair suggestion candidates を保持する。 |
| Outcome linkage | [Outcome linkage dataset v0 schema](outcome_linkage_dataset_schema.md) | Feature extension dataset と review / follow-up / rollback / incident outcome を boundary 付きで join する。 |

三つの dataset は repository、PR number、artifact path、schema version を join key として使う。
claim taxonomy、measurement boundary、non-conclusions は Feature Extension Report から
outcome linkage まで落とさず保持する。

## H1-H5 対応表

| ID | 仮説 | dataset column | report metric | evaluation query |
| --- | --- | --- | --- | --- |
| H1 | `non_split` feature extension は review cost や follow-up fix の増加と相関する。 | `FeatureExtensionDatasetRecordV0.splitStatus`, `obstructionWitnessTaxonomy`, `OutcomeObservationV0.reviewCost`, `followUpFixCount` | split group 別の review comment count、review round count、approval latency、follow-up fix count | `splitStatus = "non_split"` の PR と `split` の PR を、changed files / changed components / reviewer count で stratify して比較する。 |
| H2 | hidden interaction witness は semantic defect や rollback と相関する。 | `obstructionWitnessTaxonomy.kind`, `claimClassification`, `rollback`, `followUpFixCount`, `traceability.issueRefs`, `traceability.incidentRefs` | hidden interaction witness count、rollback rate、follow-up defect issue count | hidden / semantic witness を持つ PR と持たない PR の rollback / follow-up fix 分布を見る。semantic evidence が unmeasured の record は別 bucket にする。 |
| H3 | runtime exposure witness は incident scope や MTTR と相関する。 | runtime-related `obstructionWitnessTaxonomy`, `incidentAffectedComponentCount`, `mttrHours`, `traceability.incidentRefs` | measured runtime witness count、affected component count、MTTR、runtime data missing rate | runtime measurement boundary が `measured` の record だけで exposure witness と incident scope / MTTR の分布を比較する。runtime data unavailable は risk 0 として補完しない。 |
| H4 | split extension と判定された PR は後続変更で再利用・置換・移行しやすい。 | `splitStatus`, `repairSuggestionAdoptionCandidates`, PR history observation window, future PR / issue refs | future co-change count、migration / replacement PR count、repair suggestion adoption candidate follow-up count | merge 後 30 / 90 / 180 日の観測窓で、split PR の feature area が再利用・置換・移行された回数を見る。観測窓が不足する PR は not evaluated とする。 |
| H5 | Feature Extension Report は architecture review の合意形成を速める。 | `artifactRefs.featureExtensionReports`, `reviewMetadata.reviewCommentCount`, `reviewThreadCount`, `reviewRoundCount`, `firstReviewLatencyHours`, `approvalLatencyHours` | report-present group の approval latency、review rounds、architecture discussion thread count proxy | Feature Extension Report artifact がある PR とない PR、または導入前後の PR segment を比較する。PR size と reviewer count を stratification に残す。 |

H5 の「合意形成」は主観評価ではなく、測定可能な review outcome として扱う。最小 proxy は
approval latency、review round count、review thread count、architecture-related label /
thread count である。review policy や team process が期間中に変わった場合は、同じ segment
内でだけ比較する。

## summary artifact

Phase B6 の評価結果を tooling output として保存する場合、最小 summary は次の形にする。
これは schema candidate であり、現時点では Lean theorem や CI gate ではない。

```text
B6EmpiricalEvaluationSummaryV0 =
  schemaVersion: "b6-empirical-evaluation-summary-v0"
  repository: RepositoryRef
  inputDatasets:
    prHistory: ArtifactRef
    featureExtension: ArtifactRef
    outcomeLinkage: ArtifactRef
  hypothesisResults: List B6HypothesisResult
  measurementBoundary: B6MeasurementBoundary
  nonConclusions: List String

B6HypothesisResult =
  id: "H1" | "H2" | "H3" | "H4" | "H5"
  tier: "primary" | "exploratory" | "not_evaluated"
  inputRecordCount: Nat
  excludedRecordCount: Nat
  exclusionReasons: List String
  explanatoryColumns: List String
  outcomeColumns: List String
  descriptiveStatistics: List String
  effectSizeSummary: String | null
  limitations: List String
  nonConclusions: List String
```

`effectSizeSummary` は exploratory note 用の記述であり、p-value だけを成果として扱わない。
pilot size が小さい場合は、順位相関、分布差、外れ値、欠損率を主に報告する。

## 共通除外条件

- bot-only PR、formatting-only PR、vendored code だけの PR は primary analysis から外す。
- Feature Extension Report または outcome artifact が missing / private の場合、その理由を
  `nonConclusions` と `exclusionReasons` に残す。
- `unmeasured`、`unavailable`、`private`、`null` を measured zero として補完しない。
- schema version、extractor version、policy version が比較不能な record は sensitivity
  analysis に回す。
- review policy、incident policy、repository ownership が大きく変わった期間を混ぜない。

## non-conclusions

- Feature Extension Report の分類から causal effect を主張しない。
- obstruction witness と outcome の対応を Lean theorem として読まない。
- extractor が完全な `ComponentUniverse` を生成したとは主張しない。
- Architecture Signature を単一スコアの品質 ranking として扱わない。
- report-present PR の review latency が短い場合でも、Feature Extension Report 単独の効果とは
  結論しない。
