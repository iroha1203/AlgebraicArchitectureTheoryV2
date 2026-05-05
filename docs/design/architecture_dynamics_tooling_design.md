# Architecture Dynamics tooling 設計

Lean status: `empirical hypothesis` / `tooling validation`.

この文書は [Architecture Signature Dynamics 設計](architecture_signature_dynamics.md) を
tool 側へ落とすための設計である。数学側の中心命題は、`codebase as field`、
architecture-induced operation distribution、signature trajectory、Observed / Latent /
Dissipated force、dissipation / control である。tool 側の目的は、この理論を観測、記録、
推定、比較、review feedback に使える artifact set へ分解することである。

tool は Architecture Dynamics を証明しない。tool が行うのは、architecture field の現在値、
operation proposal、accepted transition、rejected / modified force、signature trajectory、
control input を測定境界つきで保存し、AAT の仮説検証と PR review に使える形へ変換することである。

## Tooling thesis

Architecture Dynamics tooling の中心は次の閉ループを artifact として記録することである。

```text
current architecture field
  -> operation proposals
  -> accepted / rejected transitions
  -> observed / latent / dissipated force
  -> signature trajectory
  -> updated architecture field
```

この閉ループを測定するため、tooling layer は次を分ける。

| 対象 | artifact | 主な用途 |
| --- | --- | --- |
| current architecture field | `architecture-field-snapshot-v0` | codebase が future operation distribution をどう誘導するかを記録する。 |
| operation proposal | `operation-proposal-log-v0` | AI / human / automation が提案した変更候補と prompt / requirement / context を記録する。 |
| accepted PR force | `pr-force-report-v0` | before / after Signature delta と Feature Extension Report context を PR 単位で記録する。 |
| rejected / modified force | `force-dissipation-ledger-v0` | review / CI / policy によって拒否・修正・減衰された raw force を記録する。 |
| trajectory | `signature-trajectory-report-v0` | selected window の Signature trajectory と drift / stability signal を記録する。 |
| dynamics metrics | `architecture-dynamics-metrics-report-v0` | trajectory, force, field, control, AI dynamics の指標を集計する。 |
| control input | `development-control-input-log-v0` | requirement, design boundary, prompt, review / CI policy の変化を記録する。 |

これらは既存の `archsig-sig0-v0`、`feature-extension-report-v0`、
`pr-history-dataset-v0`、`architecture-drift-ledger-v0`、`outcome-linkage-dataset-v0` を
置き換えない。Dynamics tooling は、それらを source artifact として参照し、force / field /
trajectory の読みへ統合する上位 layer である。

## Implementation spine

最初の実装単位は、Architecture Dynamics 全体を一度に測ることではない。最初に固めるべき
artifact は次の三つである。

```text
pr-force-report-v0
signature-trajectory-report-v0
architecture-dynamics-metrics-report-v0
```

この三つがあると、AAT Dynamics はすぐに読める。

- `pr-force-report-v0` は、各 PR が Signature 空間へ加えた `ObservedForce` を示す。
- `signature-trajectory-report-v0` は、一定 window で Signature trajectory がどちらへ流れたかを示す。
- `architecture-dynamics-metrics-report-v0` は、何が測定済みで、何が推定で、何が
  `unmeasured` / `unavailable` / `notComparable` かを明示する。

`architecture-field-snapshot-v0`、`operation-proposal-log-v0`、
`force-dissipation-ledger-v0`、`development-control-input-log-v0` は次段階の artifact とする。
これらは理論上重要だが、proposal completeness、raw force estimation、organization metadata の
収集境界が難しいため、最初の skeleton / validator の主戦場にはしない。

## Common measurement contract

Architecture Dynamics tooling の価値は、値そのものだけでなく、その値の測定状態を壊さず
伝搬することにある。すべての dynamics artifact は、共通の measurement contract を持つ。

```text
DynamicsMeasuredValue A =
  value: A | null
  status: MeasurementStatus
  confidence: ConfidenceLevel | null
  sourceRefs: List ArtifactRef
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String

MeasurementStatus =
  measured
  estimated
  derived
  advisory
  unmeasured
  unavailable
  private
  notComparable
  outOfScope
```

`MeasurementStatus` の読みは次である。

| status | 意味 |
| --- | --- |
| `measured` | source artifact から明示的に測定された値。 |
| `estimated` | proposal、metadata、heuristic、model から推定された値。 |
| `derived` | 測定済み source から deterministic に計算された派生値。 |
| `advisory` | review 補助 signal。formal claim や measured value ではない。 |
| `unmeasured` | 測定対象だが測定されていない。0 と読まない。 |
| `unavailable` | source が取得できない。0 と読まない。 |
| `private` | evidence が非公開。0 と読まない。 |
| `notComparable` | extractor / policy / schema / window 差分により比較不能。 |
| `outOfScope` | 当該 artifact の測定対象外。 |

`MeasurementBoundary` は少なくとも次を保持する。

```text
MeasurementBoundary =
  measuredLayer: String
  measuredAxes: List String
  sourceArtifactRefs: List ArtifactRef
  extractorVersion: String | null
  policyVersion: String | null
  schemaVersion: String | null
  aggregationWindow: AggregationWindow | null
  selectedRegionRefs: List String
  assumptions: List String
  unsupportedConstructs: List String
  missingEvidence: List MissingEvidence
  nonConclusions: List String
```

Validation は、`measured` / `estimated` / `derived` / `advisory` を混同してはならない。
特に `unmeasured`、`unavailable`、`private`、`notComparable` は measured zero ではない。

## Stochastic / empirical bridge

Architecture Signature Dynamics の stochastic / empirical bridge は、Lean theorem、
tooling validation、empirical validation の三つを分けるための artifact boundary である。
tool は finite universe と join key を検査するが、operation distribution の完全性や
AI patch 成功条件を証明しない。

初期 schema は次の五つに分ける。

| schema | 役割 | source / join |
| --- | --- | --- |
| `finite-weighted-operation-distribution-v0` | selected finite operation universe と重みを記録する。 | `operation-proposal-log-v0`, `pr-history-dataset-v0`, manual annotation |
| `signature-dynamics-simulation-protocol-v0` | initial state、operation distribution、control policy、bounded horizon、observation を固定する。 | field snapshot, distribution, Signature snapshot store |
| `architecture-dynamics-metrics-report-v0` | trajectory / force / attractor candidate / AI sensitivity signal を measurement status つきで集計する。 | PR force report, trajectory report, distribution |
| `ai-patch-sensitivity-protocol-v0` | AI 由来 proposal / accepted transition が selected bad-axis measure や safe region に与える変化を測る。 | proposal log, PR force report, dissipation ledger |
| `vibe-coding-hypothesis-v0` | task class、architecture region、control policy、outcome linkage を束ねて empirical hypothesis を管理する。 | outcome linkage dataset, trajectory report, review metadata |

`finite-weighted-operation-distribution-v0` は、operation id、operation kind、applicability
boundary、weight、weight status、source refs、normalization status、missing evidence、
non-conclusions を持つ。weight は `measured` / `estimated` / `advisory` / `unmeasured`
を区別し、正規化済みであっても実際の future operation distribution の完全復元とは読まない。

`signature-dynamics-simulation-protocol-v0` は、selected finite state list、operation
distribution ref、transition semantics ref、control policy ref、bounded horizon、
seed / deterministic replay metadata、signature observation ref、comparison baseline refs を
持つ。validation は、参照 artifact の schema version と measurement boundary が比較可能かを
検査する。finite simulation の結果は global attractor / basin claim ではない。

`ai-patch-sensitivity-protocol-v0` では、AI provenance は source metadata としてだけ扱う。
AI 由来であることから high risk / low risk、lawfulness、theorem precondition discharge を
結論しない。selected bad-axis nonincrease を主張する場合は、Lean 側の explicit damping
assumption または tooling-side policy evidence への参照を必須にする。

`vibe-coding-hypothesis-v0` は empirical hypothesis ledger であり、success criteria、
task class、control policy、trajectory / outcome refs、confounder notes、retained /
rejected status、non-conclusions を保持する。これは case study や pilot の入口であり、
Vibe coding の一般的成功 / 失敗を theorem claim にしない。

## Artifact overview

### architecture-field-snapshot-v0

`architecture-field-snapshot-v0` は、ある repository revision が future operation
distribution をどのように誘導しうるかを記録する field snapshot である。

```text
ArchitectureFieldSnapshotV0 =
  schemaVersion: "architecture-field-snapshot-v0"
  repository: RepositoryRef
  revision: RepositoryRevisionRef
  signatureSnapshotRef: ArtifactRef
  fieldSignals: FieldSignals
  canonicalExamples: List CanonicalExampleSignal
  localGrammarSignals: LocalGrammarSignals
  policyContext: PolicyContext
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

`fieldSignals` は、boundary strength、module ownership、responsibility concentration、
effect routing、test observability、known debt wells、generated-code quarantine などを
保持する。初期段階ではすべてを自動抽出できなくてよい。測定済み、未測定、manual annotation、
private evidence を分ける。

この artifact は `ArchitectureSignature` と同じではない。Signature は多軸診断値であり、
field snapshot は future operation distribution を誘導する context signal を記録する。

Non-conclusions:

- field snapshot は future patch distribution を完全に予測しない。
- canonical example の存在だけで seed attractor の強さを証明しない。
- unmeasured local grammar signal を risk 0 と読まない。

### operation-proposal-log-v0

`operation-proposal-log-v0` は、accepted される前の operation proposal を記録する。
AI agent、human developer、automation の提案を同じ claim taxonomy で扱い、作者種別で
基準を変えない。

```text
OperationProposalLogV0 =
  schemaVersion: "operation-proposal-log-v0"
  repository: RepositoryRef
  proposals: List OperationProposalRecord
  analysisMetadata: ProposalAnalysisMetadata

OperationProposalRecord =
  proposalId: String
  sourceKind: "human" | "ai_agent" | "automation" | "unknown"
  sourceRef: String | null
  requirementRefs: List ArtifactRef
  promptRefs: List ArtifactRef
  baseRevision: RepositoryRevisionRef
  proposedRevision: RepositoryRevisionRef | null
  proposedOperationKind: String | null
  proposalStatus: "proposed" | "accepted" | "rejected" | "modified" | "superseded"
  artifactRefs: ProposalArtifactRefs
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

この artifact により、accepted PR だけでなく、review / CI で落ちた raw force も後から
推定できる。`sourceKind = ai_agent` は provenance であり、formal claim promotion ではない。

Non-conclusions:

- proposal log は operation distribution の完全標本ではない。
- missing rejected proposal は accepted proposal と同じではない。
- AI 由来であることだけで high risk / low risk を結論しない。

### pr-force-report-v0

`pr-force-report-v0` は、accepted transition の `ObservedForce` を PR 単位で記録する。
既存の empirical dataset v0 の `deltaSignatureSigned`、Feature Extension Report、PR history
metadata を join する report である。

```text
PrForceReportV0 =
  schemaVersion: "pr-force-report-v0"
  pullRequest: PullRequestRef
  signatureBeforeRef: ArtifactRef
  signatureAfterRef: ArtifactRef
  deltaSignatureSigned: NullableSignatureIntVector
  observedForce: ObservedForceVector
  forceDecomposition: ForceDecomposition
  featureExtensionReportRefs: List ArtifactRef
  theoremPreconditionRefs: List ArtifactRef
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

`forceDecomposition` は feature / repair / boundary / coupling / type / test / debt /
stabilizing の候補成分を持つ。初期段階では、明示 evidence がある成分だけを
`measured` とし、heuristic classification は `advisory` に留める。

Non-conclusions:

- PR force は単一スコアではない。
- observed force は rejected raw force を含まない。
- force decomposition は theorem claim ではない。
- measured delta は unmeasured semantic / runtime axis を zero と読まない。

### force-dissipation-ledger-v0

`force-dissipation-ledger-v0` は、raw proposal force が review / CI / type / policy によって
どう拒否・修正・減衰されたかを記録する。これは `DissipatedForce` の tooling entrypoint である。

```text
ForceDissipationLedgerV0 =
  schemaVersion: "force-dissipation-ledger-v0"
  repository: RepositoryRef
  window: AggregationWindow
  entries: List DissipationEntry
  analysisMetadata: DissipationAnalysisMetadata

DissipationEntry =
  proposalRef: ArtifactRef
  acceptedPrRef: ArtifactRef | null
  rawForceEstimate: NullableForceVector
  acceptedForceRef: ArtifactRef | null
  dissipatedForceEstimate: NullableForceVector
  dissipationMechanisms: List DissipationMechanism
  evidenceRefs: List ArtifactRef
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

`dissipationMechanisms` は review change request、CI failure、type error、policy fail、
architecture rule violation、manual redesign などを保持する。

Non-conclusions:

- rejected proposal の raw force は常に計算できるとは限らない。
- dissipation estimate は review / CI の因果効果の証明ではない。
- CI failure count だけで dissipation capacity を結論しない。

### signature-trajectory-report-v0

`signature-trajectory-report-v0` は、selected window の Signature trajectory を保存する。
input は Signature snapshot store、PR force report、drift ledger、policy / extractor metadata である。

```text
SignatureTrajectoryReportV0 =
  schemaVersion: "signature-trajectory-report-v0"
  repository: RepositoryRef
  window: AggregationWindow
  trajectoryPoints: List SignatureTrajectoryPoint
  forceRefs: List ArtifactRef
  driftSignals: DriftSignals
  stabilitySignals: StabilitySignals
  selectedRegions: List SelectedSignatureRegion
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

`selectedRegions` は safe region、bad region、debt well、attractor candidate を
明示する。attractor / basin 語彙は、初期段階では必ず finite observed trajectory、
selected region、bounded operation window に相対化する。

Non-conclusions:

- trajectory report は global attractor を証明しない。
- selected window 外の behavior を結論しない。
- extractor / policy version 差分がある trajectory は sensitivity metadata を必要とする。

### architecture-dynamics-metrics-report-v0

`architecture-dynamics-metrics-report-v0` は、Architecture Dynamics 用の定量指標を集計する。

```text
ArchitectureDynamicsMetricsReportV0 =
  schemaVersion: "architecture-dynamics-metrics-report-v0"
  repository: RepositoryRef
  window: AggregationWindow
  sourceRefs: DynamicsSourceRefs
  trajectoryMetrics: TrajectoryMetrics
  forceMetrics: ForceMetrics
  fieldControlMetrics: FieldControlMetrics
  aiDynamicsMetrics: AiDynamicsMetrics
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

初期指標:

| group | metrics |
| --- | --- |
| trajectory | `TrajectoryDriftRate`, `TrajectoryStability`, `InvariantDecayRate`, `SignatureVolatility`, `PhaseShiftSignal` |
| force | `ObservedForce`, `LatentForceEstimate`, `DissipatedForceEstimate`, `NetPRForce`, `DebtForceAccumulation`, `StabilizingForceRatio`, `MergeOrderSensitivity` |
| field / control | `DissipationCapacity`, `ConstraintSaturation`, `FeedbackDelayInstability`, `DesignFieldStrength`, `IndirectForceLeverage` |
| AI dynamics | `OperationDistributionShift`, `AIPatchLyapunov`, `PromptBasinBias`, `SeedAttractorStrength`, `AISafetyMargin` |

各 metric は `value`, `status`, `sourceRefs`, `confidence`, `measurementBoundary`,
`nonConclusions` を持つ。推定値と測定値を同じ confidence で扱わない。

### development-control-input-log-v0

`development-control-input-log-v0` は、operation distribution を変えうる control input の
変化を記録する。

```text
DevelopmentControlInputLogV0 =
  schemaVersion: "development-control-input-log-v0"
  repository: RepositoryRef
  records: List ControlInputRecord
  analysisMetadata: ControlInputAnalysisMetadata

ControlInputRecord =
  controlInputId: String
  kind: "requirement" | "design_boundary" | "prompt_policy" | "review_policy" |
        "ci_policy" | "type_policy" | "organization_policy" | "unknown"
  effectiveWindow: AggregationWindow
  artifactRefs: List ArtifactRef
  expectedDistributionEffect: String | null
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

この artifact は組織判断そのものを形式化するものではない。組織判断や prompt / policy の変化が
architecture transition distribution に与えた可能性を、後続の metrics report が検証できる形で
参照可能にする。

## Development field tooling bridge

Development Field Theory の tooling layer は、組織判断を直接 theorem claim にせず、
architecture transition distribution への作用を artifact として記録する。初期 schema は
次の四つに分ける。

| schema | 役割 | source / join |
| --- | --- | --- |
| `indirect-force-leverage-dataset-v0` | requirement、design boundary、prompt、policy などの indirect control input と、後続 force / trajectory / outcome signal を join する。 | `development-control-input-log-v0`, PR force report, trajectory report, outcome linkage |
| `design-field-strength-report-v0` | architecture field snapshot が future operation distribution をどの方向へ誘導したかを selected signal で読む。 | field snapshot, operation proposal log, PR force report |
| `organization-damping-capacity-protocol-v0` | review / CI / type / policy / ownership が raw force を rejection / projection / modification / delay した境界を記録する。 | proposal log, force dissipation ledger, policy decision report |
| `ai-agent-team-dynamics-protocol-v0` | 複数 agent / human / automation の proposal、merge order sensitivity、prompt basin bias、dissipation demand を測る。 | proposal log, merge sensitivity refs, trajectory report |

### indirect-force-leverage-dataset-v0

```text
IndirectForceLeverageDatasetV0 =
  schemaVersion: "indirect-force-leverage-dataset-v0"
  repository: RepositoryRef
  records: List IndirectForceLeverageRecord
  analysisMetadata: DevelopmentFieldAnalysisMetadata

IndirectForceLeverageRecord =
  controlInputRef: ArtifactRef
  fieldKind: "demand" | "requirement" | "design" | "operation" |
             "dissipation" | "observation" | "unknown"
  beforeWindow: AggregationWindow
  afterWindow: AggregationWindow
  operationDistributionRefs: List ArtifactRef
  prForceReportRefs: List ArtifactRef
  trajectoryReportRefs: List ArtifactRef
  outcomeLinkageRefs: List ArtifactRef
  estimatedEffect: DynamicsMeasuredValue String
  confounderNotes: List String
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

この dataset は causal proof ではない。同じ selected window、比較可能な schema version、
比較可能な measurement boundary に相対化した empirical signal として扱う。

### design-field-strength-report-v0

```text
DesignFieldStrengthReportV0 =
  schemaVersion: "design-field-strength-report-v0"
  repository: RepositoryRef
  architectureFieldSnapshotRef: ArtifactRef
  selectedRegionRefs: List String
  fieldSignalScores: List DynamicsMeasuredValue FieldSignalScore
  distributionShiftRefs: List ArtifactRef
  seedAttractorSignals: List DynamicsMeasuredValue String
  badForceLocalizationSignals: List DynamicsMeasuredValue String
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

`DesignFieldStrengthReportV0` は design field の真値を返さない。canonical example、
boundary strength、ownership、local grammar、test observability などの selected signal を
operation proposal / accepted transition と join し、future operation distribution の
完全予測ではなく bounded signal として出す。

### organization-damping-capacity-protocol-v0

```text
OrganizationDampingCapacityProtocolV0 =
  schemaVersion: "organization-damping-capacity-protocol-v0"
  repository: RepositoryRef
  controlPolicyRefs: List ArtifactRef
  proposalLogRefs: List ArtifactRef
  dissipationLedgerRefs: List ArtifactRef
  acceptedTrajectoryRefs: List ArtifactRef
  selectedInvariantRefs: List String
  badAxisRefs: List String
  boundedWindow: AggregationWindow
  dampingAssumptions: List String
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

この protocol は Lean 側の explicit damping assumption を tooling / empirical evidence へ
接続する入口である。review、CI、type checker、policy、ownership が存在するだけで、
safe-region preservation や bad-axis nonincrease が証明されたとは読まない。

### ai-agent-team-dynamics-protocol-v0

```text
AIAgentTeamDynamicsProtocolV0 =
  schemaVersion: "ai-agent-team-dynamics-protocol-v0"
  repository: RepositoryRef
  agentPolicyRefs: List ArtifactRef
  promptRefs: List ArtifactRef
  proposalLogRefs: List ArtifactRef
  mergeOrderSensitivityRefs: List ArtifactRef
  dissipationLedgerRefs: List ArtifactRef
  trajectoryReportRefs: List ArtifactRef
  selectedTaskClass: String
  selectedArchitectureRegion: String
  measurementBoundary: MeasurementBoundary
  nonConclusions: List String
```

AI provenance は source metadata であり、risk claim や theorem claim ではない。この protocol は
agent team の proposal diversity、merge order sensitivity、prompt basin bias、dissipation demand
を selected finite window 上で測る。

## CLI surface

初期 CLI は既存 `archsig` に次を追加する想定にする。

```bash
archsig pr-force-report \
  --empirical-dataset empirical-signature-dataset.json \
  --pr-history pr-history-dataset.json \
  --feature-report feature-report.json \
  --out pr-force-report.json

archsig signature-trajectory-report \
  --signature-snapshots signature-snapshot-store.json \
  --pr-force-reports pr-force-report.json \
  --drift-ledger architecture-drift-ledger.json \
  --out signature-trajectory-report.json

archsig architecture-dynamics-metrics \
  --trajectory signature-trajectory-report.json \
  --force-reports pr-force-report.json \
  --out architecture-dynamics-metrics-report.json
```

CLI は段階的に実装してよい。最初は schema fixture と validation だけを固定し、推定指標は
`unmeasured` / `unavailable` として出す。

次段階 CLI は、proposal、field、dissipation、control input の evidence が揃ってから追加する。

```bash
archsig architecture-field-snapshot \
  --signature-snapshot signature-snapshot.json \
  --feature-report feature-report.json \
  --policy organization-policy.json \
  --out architecture-field-snapshot.json

archsig operation-proposal-log \
  --pr-history pr-history-dataset.json \
  --generated-change-metadata generated-change.json \
  --out operation-proposal-log.json

archsig force-dissipation-ledger \
  --operation-proposals operation-proposal-log.json \
  --policy-decisions policy-decision-report.json \
  --ci-results ci-results.json \
  --out force-dissipation-ledger.json
```

Development field artifacts は、上の次段階 artifact が揃った後に追加する。

```bash
archsig indirect-force-leverage-dataset \
  --control-inputs development-control-input-log.json \
  --force-reports pr-force-report.json \
  --trajectory signature-trajectory-report.json \
  --out indirect-force-leverage-dataset.json

archsig design-field-strength-report \
  --field-snapshot architecture-field-snapshot.json \
  --operation-proposals operation-proposal-log.json \
  --force-reports pr-force-report.json \
  --out design-field-strength-report.json

archsig organization-damping-capacity-protocol \
  --proposals operation-proposal-log.json \
  --dissipation force-dissipation-ledger.json \
  --trajectory signature-trajectory-report.json \
  --out organization-damping-capacity-protocol.json

archsig ai-agent-team-dynamics-protocol \
  --operation-proposals operation-proposal-log.json \
  --trajectory signature-trajectory-report.json \
  --out ai-agent-team-dynamics-protocol.json
```

## Existing artifact connections

| 既存 artifact | Dynamics tooling での役割 |
| --- | --- |
| `archsig-sig0-v0` / Signature snapshot store | field snapshot と trajectory point の source。 |
| `empirical-signature-dataset-v0` | PR force の before / after delta source。 |
| `pr-history-dataset-v0` | PR identity、review metadata、artifact join key。 |
| `feature-extension-report-v0` | PR force の theorem precondition / obstruction context。 |
| `policy-decision-report-v0` | dissipation mechanism と accepted / rejected boundary。 |
| `baseline-suppression-report-v0` | accepted risk と suppression workflow。 |
| `architecture-drift-ledger-v0` | trajectory drift signal。 |
| `outcome-linkage-dataset-v0` | force / trajectory と incident / rollback / review outcome の empirical join。 |
| `report-outcome-daily-ledger-v0` | long-running operational feedback。 |
| `hypothesis-refresh-cycle-v0` | ASD metrics の仮説更新 cycle。 |

## Validation rules

最低限の validation は次である。

- `schemaVersion` が catalog または experimental catalog に存在する。
- source artifact refs が解決できるか、missing / private / unavailable として明示される。
- measured zero、unmeasured、unavailable、out of scope を区別する。
- `MeasurementStatus` が `measured` / `estimated` / `derived` / `advisory` /
  `unmeasured` / `unavailable` / `private` / `notComparable` / `outOfScope` のいずれかである。
- metric value が `null` の場合、`measured` または `derived` として出さない。
- `estimated` metric は confidence、source refs、assumption、non-conclusion を持つ。
- `ObservedForce`、`LatentForceEstimate`、`DissipatedForceEstimate` を混同しない。
- accepted transition と rejected proposal を同じ force class として集計しない。
- AI provenance を risk claim や theorem claim に変換しない。
- attractor / basin / Lyapunov-like metric は finite observed trajectory、selected region、
  bounded operation window を明示する。
- finite weighted operation distribution は selected universe、weight status、source refs、
  normalization status、missing evidence を明示する。
- simulation protocol は bounded horizon、transition semantics、control policy、
  observation boundary、comparison baseline を固定する。
- Vibe coding success condition は empirical hypothesis として扱い、formal / tooling claim に
  昇格しない。
- indirect force leverage は causal proof ではなく、selected window と比較可能な boundary に
  相対化した empirical signal として扱う。
- design field strength は真値ではなく、selected field signal と operation distribution refs の
  bounded report として扱う。
- organization damping capacity は policy の存在だけでなく、proposal / dissipation / trajectory
  evidence への refs と missing evidence を持つ。
- AI agent team dynamics は AI provenance を theorem claim や risk claim に変換しない。
- extractor / policy / schema version が異なる比較は sensitivity analysis または migration
  boundary を必要とする。
- formal claim promotion は theorem precondition checker の明示 precondition なしに通さない。

## Non-conclusions

Architecture Dynamics tooling は次を結論しない。

- architecture lawfulness。
- Lean theorem claim。
- AI patch distribution の完全復元。
- operation proposal log の完全性。
- PR force と incident / rollback / MTTR の因果関係。
- organization policy の正しさ。
- design field strength の真値。
- indirect force leverage の因果効果。
- organization-level damping capacity の十分性。
- AI agent team の lawfulness や incident reduction。
- finite selected window からの global attractor claim。
- unmeasured axis や private evidence の measured-zero 化。

## 最初の実装単位

最初の tooling Issue として自然なのは、実指標計算ではなく schema fixture と validator である。

初期 scope:

- `pr-force-report-v0` skeleton。
- `signature-trajectory-report-v0` skeleton。
- `architecture-dynamics-metrics-report-v0` skeleton。
- 共通 `DynamicsMeasuredValue` / `MeasurementStatus` / `MeasurementBoundary` validation。
- canonical minimal fixtures。
- `archsig architecture-dynamics-metrics --fixture` で non-conclusions と unmeasured metrics を出す。

次段階で `operation-proposal-log-v0` と `force-dissipation-ledger-v0` を追加し、
Observed / Latent / Dissipated force を分けた PR Force Report へ進む。
Development field artifacts はさらにその後の段階とし、indirect force leverage、design field
strength、organization damping capacity、AI agent team dynamics を empirical / tooling boundary
つきで扱う。
