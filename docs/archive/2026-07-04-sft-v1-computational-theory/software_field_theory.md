# Software Field Theory: A Computational Theory of Field-Shaped Software Evolution（ソフトウェアの場の理論）

Software Field Theory (SFT) は、field-shaped software evolution の計算理論である。
SFT は、要求、artifact、実践、ツール、AI agent、レビュー、CI/CD、運用 feedback、
lifecycle decision が、コードベースの到達可能なアーキテクチャ未来をどう変えるかを扱う。

SFT の看板主張は次である。

```text
SFT は、ソフトウェア進化を計算可能な対象にする。
```

ソフトウェア進化は単なるコード変更列ではない。
artifact、実践、agent、governance mechanism、feedback loop が、何が自然な変更に見えるか、
何が許されるか、何が観測されるか、何が制御可能かを作り替える
field-shaped computation である。

```text
ソフトウェア進化は場によって形作られる:

artifact
  + practices
  + agents
  + governance
  + operational feedback
  + lifecycle pressure
  -> operation support
  -> selection policy
  -> observation boundary
  -> governance intervention
  -> reachable architectural futures
```

bounded transition-system core は、SFT 全体ではない。
それは、この広い場の理論のうち、計算可能・検証可能な発明核である。

```text
AAT は Atom から代数幾何的 architecture を構成する。
ArchSig は選ばれた architecture evidence を測定する。
SFT はソフトウェア進化を計算可能にする。
```

SFT が `field`、`force`、`dissipation`、`attractor`、`basin` と呼ぶものは物理量ではない。
これらは development context、artifact-mediated change、proposal accounting、
stable region、reachable preimage として明示された場合に限って、計算対象になる。

## Part I. The New Object（新しい対象）

### 1. Software Evolution as a Computable Object（計算可能な対象としてのソフトウェア進化）

SFT が導入する新しい対象は、ソフトウェア進化そのものである。
従来の tooling は、多くの場合、すでに起きた code state、PR diff、test result、
static dependency を観測する。
SFT はさらに一歩進めて、次を計算対象にする。

```text
reachable architectural futures of a codebase
```

ここでいう future は未来予言ではない。
選択された field model、operation support、policy、observation boundary、
governance intervention、horizon に相対化された到達可能領域である。

SFT における `computable` は、実際のソフトウェア進化が完全に決定可能であることを意味しない。
明示された field model、observation boundary、operation support、policy、horizon の下で、
選択された問いを有限または bounded な問題へ落とせることを意味する。

```text
SFT における computable :=
  明示された modeling boundary の下で表現できる
  + 選択された horizon / universe / observation axes により有界化される
  + 次のような計算問題へ落とせる:
      reachability
      support inference
      cone generation
      safety preservation
      proposal accounting
      feedback update
      calibration
```

SFT の中心命題は次である。

```text
ソフトウェア進化は、単なるコード変更列ではない。
artifact、実践、agent、governance system、feedback loop が、
operation space と観測可能な architecture future を作り替える
field-shaped computation である。
```

SFT はこの命題を、説明、測定、計算、governance の四つの層で扱う。

```text
Theory / 理論:
  software evolution を field-shaped computation として定義する。

Measurement / 測定:
  AAT / ArchSig により architecture object、signature、obstruction、
  theorem boundary、field estimate を観測可能にする。

Computation / 計算:
  operation support、policy、ForecastCone、ConsequenceEnvelope、
  support safety、feedback update を計算対象にする。

Governance / 統治:
  review、CI、type checker、AI policy、runtime feedback を、
  codebase future を変える governance intervention system として扱う。
```

### 2. Codebase as Field Memory（場の記憶としてのコードベース）

コードベースは単なる実装成果物ではない。
過去の要求、設計判断、レビュー規則、incident、workaround、migration、組織境界、
tooling practice が沈着した記憶である。
同時に、未来の開発可能性を制約する媒体である。

```text
Codebase as Field Memory :=
  implementation state
  + sedimented requirements
  + design decisions
  + review and CI history
  + incidents and repairs
  + migrations and workarounds
  + ownership boundaries
  + tooling practices
  + latent default paths
```

同じ module graph でも、field memory が違えば次に自然に選ばれる operation は変わる。
古い workaround、暗黙の ownership、過去の incident、AI agent が学習しやすい local pattern は、
未来の operation support と selection policy を変える。

SFT は、コードベースを静的な graph としてだけでなく、過去の field action が沈着した
development memory として扱う。

### 3. Development Fields（開発場）

`DevelopmentField` は、コードベースと、そのコードベースを変化させる artifact、practice、
agent、governance、feedback、lifecycle pressure の組である。

```text
DevelopmentField :=
  codebase
  + requirements and specs
  + issues and planning artifacts
  + design practices
  + developers and AI agents
  + review systems
  + CI / type / test systems
  + runtime observations
  + incident and postmortem records
  + lifecycle and migration pressure
```

SFT は人間の意図や組織文化を完全モデル化しない。
それらが operation support、selection policy、observation boundary、governance intervention、
feedback update に現れる範囲で扱う。

したがって、広い field theory と computable core は対立しない。
広い field は SFT の射程であり、computable core はその中で計算可能な断面である。

広い `DevelopmentField` を完全に `SoftwareField` へ変換することは主張しない。
SFT は modeling boundary を選び、その境界内で partial な `SoftwareFieldEstimate` を構成する。

```text
model_B : DevelopmentField -> Partial SoftwareFieldEstimate

ModelingBoundary B :=
  selected artifacts
  + selected codebase region
  + selected architecture universe
  + selected observation axes
  + selected governance records
  + selected time horizon
  + unavailable evidence
  + non-conclusions

SoftwareFieldEstimate :=
  modeling boundary
  + extracted SoftwareField
  + evidence status
  + unknown / unmodeled remainder
```

tooling 側では、この境界を
[`tools/fieldsig/docs/artifacts-and-boundaries.md`](../../tools/fieldsig/docs/artifacts-and-boundaries.md)
で管理する。そこでは PRD / Issue / PR / review / CI / incident / ownership trace を
observed、derived、unavailable、private、unknown、notComparable に分ける。
これにより、SFT は開発場全体の完全モデル化を避けつつ、明示境界内の計算可能な断面を扱う。

### 4. Architecture Futures and Signature Trajectories（アーキテクチャ未来と署名軌道）

SFT は endpoint だけを見ない。
safe endpoint から safe trajectory は従わない。
net signature delta が 0 でも、途中で unsafe excursion が起きることがある。

```text
ArchitectureFuture :=
  field path
  + architecture projection path
  + observed signature trajectory
  + obstruction witness candidates
  + forecast boundary

SignatureTrajectory :=
  observed signature record_0
  -> observed signature record_1
  -> ...
  -> observed signature record_n
```

`ArchitectureFuture` は確定未来ではない。
選択された field model と horizon の下での reachable future である。
SFT の重要な問いは、artifact や governance がこの reachable future をどう広げ、狭め、
どの default path を作るかである。

#### Running Example Preview: Coupon PRD（実行例の予告: クーポン PRD）

曖昧な coupon PRD は、単に feature request を追加するだけではない。
それは checkout / payment 領域で、複数の path を自然に見せる field action である。

```text
Coupon PRD may expose:
  lawful DiscountPolicy insertion path
  + PaymentAdapter shortcut path
  + UI-only discount drift path
  + rounding semantic obstruction path
```

以降では、この例を artifact、operation support、ConsequenceEnvelope、review governance、
feedback update へ展開する running example として使う。

## Part II. The Algebraic and Observational Basis（代数的・観測的基盤）

### 5. AAT: Local Algebra of Software Architecture（ソフトウェアアーキテクチャの局所代数）

SFT は AAT の上に載る。
ただし、AAT は SFT のための理論ではない。
依存方向は片方向である。

```text
AAT は SFT に依存しない。
SFT は AAT に依存する。
```

AAT は Atom から architecture object、AAT site、sheaf、law algebra、
obstruction ideal sheaf、lawful locus を構成する。
SFT はその局所的な AAT claim を、architecture projection、local transition law、
observable coordinate、admissibility boundary として使う。

対応関係の詳細は [AAT / SFT Interface](aat_interface.md) に置く。
ここでは最小対応だけを再掲する。

| SFT 側の役割 | AAT 側 |
| --- | --- |
| architecture projection | `ArchitectureObject` |
| local transition law | `ArchitectureOperation` |
| protected constraint | `InvariantFamily` |
| defect / repair target / boundary axis | `ObstructionWitness` |
| partial observation coordinate | ArchSig measurement packet / selected coordinate |
| admissibility boundary | theorem boundary / non-conclusions |
| local path skeleton | `ArchitecturePath` |

SFT は AAT theorem を empirical prediction に変換しない。
AAT theorem は、SFT reachability / safety schema の local premise として使う。

### 6. ArchSig: Measuring Selected Architecture Evidence

ArchSig は、実 artifact と codebase から供給された ArchMap observation と selected
LawPolicy を読み、AAT 語彙による law-relative analysis packet を作る観測・分析層である。
SFT field estimate、ForecastCone、ConsequenceEnvelope、calibration、governance、
operational feedback は FieldSig 側の責務であり、ArchSig から theorem として従うものではない。

```text
source artifacts
  -> ArchMap observation map
  -> LawPolicy
  -> ArchSig analysis packet
  -> FieldSig SFT input boundary
```

この境界で ArchMap、LawPolicy、ArchSig、FieldSig の責務を分ける。LLM-authored ArchMap は
source artifact から `atomObservations`、`moleculeObservations`、`semanticObservations`、
`observationGaps`、`projectionInfo`、`concernHints` を記録する law-independent な
Atom observation map である。ArchMap の主語は homomorphism ではなく Atom observation であり、
Atom、AAT、lawfulness、zero curvature、obstruction circuit、repair conclusion を生成しない。

ArchSig は ArchMap と selected LawPolicy から molecule readings、law-relative obstruction
circuits、signature axes、flatness reading、repair operation candidates、coverage gaps、
evidence boundaries、non-conclusions を含む `archsig-analysis-packet/v1` を作る。これは
bounded architecture-evidence state / FieldSig handoff であり、FieldSig が SFT 側で operation support、
ForecastCone、ConsequenceEnvelope、calibration、governance、operational feedback へ投影する。
shared source refs は cross-reference であって、AAT projection から SFT calculation が
theorem として従うことを意味しない。

ArchSig は、単一スコアではなく多軸診断を返す。
未測定 axis を 0 と読まない。
signature delta は、両側で測定済みで、axis ごとの比較順序が定義されている場合に限って
比較する。

```text
ObservedSignatureRecord :=
  measured selected coordinates
  + unmeasured axes
  + out-of-scope axes
  + evidence boundary
  + measurement non-conclusions

SignatureDelta(S_before, S_after)
  は、比較可能な測定済み axis に対してのみ定義される
```

SFT へ渡す ArchSig output は、FieldSig が読む input boundary として扱う。

```text
ArchSigAnalysisPacketAsSFTInput :=
  molecule_readings
  + law_relative_obstruction_circuits
  + signature_axes
  + flatness_reading
  + repair_operation_candidates
  + coverage_gaps
  + evidence_boundaries
  + missing_evidence
  + excluded_readings
  + non_conclusions

FieldSigProjection :=
  operation_support_estimate
  + comparable_signature_axes
  + unknown_remainder
  + forecast_boundary
  + governance_boundary
```

### 7. Claim Boundaries（主張境界）

SFT が大きな理論として信用されるためには、claim level discipline が必要である。
SFT の主張は、どの観測、どの model、どの calibration に基づくかを明示する。

```text
主張レベル 0:
  概念的・診断的な解釈

主張レベル 1:
  trace に基づく field diagnosis

主張レベル 2:
  set-valued な形式定理 schema

主張レベル 3:
  確率的 / transition-kernel model

主張レベル 4:
  dataset により calibration された経験的 forecast

主張レベル 5:
  実運用された closed-loop governance system
```

例:

```text
良い spec は `ForecastCone` を狭める。
  support inclusion と step simulation が定義されていれば Level 2。
  過去の PR / review / CI outcome で calibration されていれば Level 4。

AI proposal は shortcut を増やす。
  trace で観測されていれば Level 1。
  dataset で calibration されていれば Level 4。

組織 field が architecture drift を生む。
  Level 1 または Level 4。
  無制限の定理ではない。
```

## Part III. The SFT Core（SFT の中核）

### 8. SoftwareField and Architecture Projection（SoftwareField とアーキテクチャ射影）

`SoftwareField` は、development field のうち、計算可能な断面として扱う state である。
field state 自体は AAT の `ArchitectureObject` ではない。
AAT 側の object は、field から取り出される architecture projection である。

```text
arch : SoftwareField -> ArchitectureObject

SoftwareField :=
  contextual dynamic state
  + arch projection
  + observed signature record
  + history
  + operation support
  + operation policy
  + constraint environment
  + observation model
  + governance intervention model
  + exogenous artifact inputs
```

SFT の計算可能な核は次である。

```text
ComputableCore :=
  SoftwareField
  + arch projection
  + ArtifactMediatedChange
  + OperationSupport
  + OperationPolicy
  + StepRelation
  + ObservationRecord
  + GovernanceIntervention
  + ForecastCone
  + FieldUpdate
```

これは SFT 全体ではない。
これは、SFT を単なる比喩にしないための theorem-bearing fragment である。

### 9. Artifact-Mediated Change（artifact を介した変化）

正式な計算概念は `ArtifactMediatedChange` または `ArtifactAction` である。
`Force` は、その field-level reading を指す非公式名として残す。

```text
ArtifactAction a :=
  alpha_a : FieldSpace -> Set FieldSpaceUpdateHypothesis

FieldSpaceUpdateHypothesis :=
  明示された interpretation boundary の下で、
  後続 SoftwareField を構成または制約するための candidate update descriptor

applyUpdate :
  FieldSpace -> FieldSpaceUpdateHypothesis -> FieldSpace

DeterministicArtifactAction :=
  special case where alpha_a(F) is singleton
```

artifact は、field を一意に次の field へ写すとは限らない。
PRD、Spec、Issue、AI proposal は、複数の解釈、複数の candidate update、
複数の path class を生みうる。
SFT で扱う action は、source artifact、target field components、action boundary、
composition boundary、observable boundary、non-conclusions を持つ。

```text
RawArtifactAction :=
  source artifact
  + target field components
  + interpretation boundary
  + candidate field updates
  + action boundary
  + composition boundary
  + observable boundary
  + non-conclusions

ForceDescriptor :=
  action class
  + target architecture regions
  + candidate operation support families
  + affected policy / constraint / governance / observation components
  + uncertainty boundary

ForecastedEffect :=
  forecast boundary
  + expected comparable signature axes
  + expected axis delta ranges
  + candidate obstruction witness families
  + unknown / unmodeled remainder

ObservedEffect :=
  observed transition
  + before / after observed signature records
  + comparable measured axis delta
  + unexpected obstruction witnesses
  + review / CI / runtime outcome
```

`ForecastedEffect` は forecast の出力であり、`RawArtifactAction` の定義には含めない。
これにより、action を使って forecast するのに action 自体が forecast を含む、という循環を避ける。

### 10. Operation Support, Policy, and Selection（操作 support・policy・選択）

SFT の核心は、どの operation が正しいかだけではなく、
どの operation が自然、可能、低コスト、選択されやすいものとして field に現れるかを問う点にある。

```text
SupportedOperation :=
  operation
  + applicable theorem boundary
  + precondition evidence
  + expected witness mapping
  + non-conclusions

OperationSupport(F)
  = admissible operation set after constraints / governance interventions

OperationPolicy(F)
  = preorder, cost, or selection relation on that support
```

確率に進まない最小 core では、次のいずれかを使う。

```text
PolicyAsPreorder:
  op1 <=_F op2
    := op1 is no harder / no less natural than op2 in field F

PolicyAsCost:
  cost_F(op) : OrderedCost

PolicyAsSelection:
  Selected(F, op)
```

確率的 semantics を採用する場合に限り、`mu_F : Distribution SupportedOperation` を追加する。

### 11. Attractor Engineering as Support and Policy Shaping（support / policy shaping としてのアトラクターエンジニアリング）

`Attractor Engineering` は、SFT の中で興味を引く看板語として残す。
ただし、formal core では物理的な attractor を仮定しない。
SFT における attractor engineering は、良い architecture future へ向かう operation が
自然、低コスト、観測可能、反復可能になるように、operation support と operation policy を設計することを指す。

```text
AttractorEngineering(F, R) :=
  target region R
  + support shaping
  + policy shaping
  + governance intervention
  + observation boundary
  + feedback update rule
```

良い field とは、単に悪い proposal を review / CI で止める場ではない。
良い operation が局所的に見つけやすく、模倣しやすく、低摩擦で、
悪い shortcut が unsupported、high-cost、observable、review-mediated になる場である。

したがって、attractor engineering の計算可能な読みは次である。

```text
support shaping:
  future operation support を変える

policy shaping:
  lawful path の cost を下げ、shortcut path の cost を上げる

observation shaping:
  bad basin へ向かう drift を witness として見えるようにする

feedback shaping:
  review / CI / incident outcome を posterior field に保存する
```

`Attractor` と `Basin` は、安定性、再帰性、または policy / probability semantics が
明示された場合に限って強い意味を持つ。
集合論的 core では、これらは `StableRegion`、`ReachablePreimage`、
`ForecastCone`、`SupportSafety`、`ProposalAccounting` へ分解して扱う。

この節の役割は、実務上の直感を失わずに、SFT の formal boundary へ接続することである。

### 12. ForecastCone and ConsequenceEnvelope（予測円錐と帰結包絡）

`ForecastCone` は formal object である。
horizon `h` と operation support `U` に相対化された reachable field path set として読む。
この core は集合値の到達可能性だけを扱い、確率、calibration、または実コード上の
抽出完全性を前提にしない。

```text
FieldPath :=
  finite sequence in FieldSpace

ReachableFieldPath(F, U, h, p)
  = p starts at F
  + length(p) <= h
  + 隣接する各組 F_i -> F_{i+1} について、
      exists op in U(F_i) such that StepRelation(F_i, op, F_{i+1})

StepRelation(F, op, F')
  = 選択された theorem boundary と field model の下で、
    operation op が F から F' への transition を実現できる

ForecastCone(F, U, h) :=
  { p : FieldPath | ReachableFieldPath(F, U, h, p) }
```

Lean formalization へ移す場合の最小語彙は、次の順で分離する。

```text
SoftwareField:
  field state carrier

OperationSupport:
  Field -> Set Operation

Horizon:
  Nat

StepRelation:
  Field -> Operation -> Field -> Prop

ReachableFieldPath:
  start field
  + bounded path
  + every adjacent pair is witnessed by supported step

ForecastCone:
  bounded reachable path set
```

この分離により、support の制約、step relation の simulation、horizon の単調性を
それぞれ別 theorem schema として扱える。
最初の formal target は、`ForecastCone` 自体の豊かな semantics ではなく、
support inclusion と step simulation から cone projection が従うという片方向 theorem である。

artifact action 付きの cone は、formal core の `ForecastCone(F, U, h)` から派生させる。
set-valued action の場合は、candidate update ごとに cone を生成し、その族を envelope へまとめる。

```text
u in alpha_a(F)
F_u := applyUpdate(F, u)
U_u := U(F_u)

ForecastConeFamilyAfterAction(F, a, h) :=
  { ForecastCone(F_u, U_u, h) | u in alpha_a(F) }
```

`ConsequenceEnvelope`（帰結包絡）は、実務・診断・tooling 側の提示形式である。
選択された field model と observation boundary の下で、一つ以上の `ForecastCone` を
解釈可能な report としてまとめる。

```text
ConsequenceEnvelope :=
  selected ForecastCones
  + reachable path classes
  + affected architecture regions
  + comparable signature axes
  + expected axis delta ranges
  + obstruction witness candidates
  + missing invariants / boundaries
  + review / CI / issue decomposition recommendations
  + forecast boundary
  + unknown / unmodeled remainder
```

より形式的には、`ConsequenceEnvelope` は cone family からの loss-aware report
projection として読む。

```text
ConeFamily :=
  nonempty selected set of ForecastCone(F_i, U_i, h_i)

EnvelopeProjection(ConeFamily, ObservationBoundary) :=
  path classes visible through the boundary
  + affected region refs obtained from observed path endpoints / supports
  + comparable signature axes under the selected measurement universe
  + axis delta ranges for comparable axes
  + obstruction candidates witnessed inside the observed projection
  + missing boundary / theorem boundary items
  + non-conclusions inherited from all selected cones
  + unknown remainder not discharged by the projection
```

この projection は全情報を保存しない。path の個数、probability weight、unobserved
field coordinates、support の完全性、calibrated correctness は、明示された
boundary に入っていない限り envelope へ昇格しない。
したがって soundness boundary は片方向である。

```text
ForecastCone family
  -> ConsequenceEnvelope report projection

ConsequenceEnvelope report
  -/-> unique ForecastCone family
  -/-> causal correctness
  -/-> calibrated point prediction
```

`unknown / unmodeled remainder` と `forecast non-conclusions` は projection の副産物ではなく、
保持すべき構成要素である。ある cone に unknown support、unmeasured axis、missing theorem
boundary が残るなら、envelope はそれを missing / theorem boundary item として残す。
複数 cone をまとめる場合も、unknown remainder は相殺されない。

理論家には `ForecastCone`、実務家には `ConsequenceEnvelope`、tooling には simulator output を返す。
FieldSig の `forecast-cone-skeleton-v0` は、この formal core の有限 support refs、
bounded horizon、path class candidates、forecast boundary、unknown remainder を保持する
review artifact である。これは `ForecastCone(F, U, h)` の Lean theorem witness ではなく、
probability、causal correctness、global safety、または calibration 済み予測を結論しない。
FieldSig の `consequence-envelope-report-v0` は、`forecast-cone-skeleton-v0` から
affected regions、comparable axes、axis delta ranges、obstruction candidates、missing
boundary / theorem boundary、review recommendation を生成する report projection である。
Lean 側では `Formal/Arch/Evolution/SFTEnvelope.lean` が、この片方向 boundary を
`ConeFamily`、`ObservationBoundary`、`ConsequenceEnvelope`、`EnvelopeProjection` として
record-level に切り出す。これは formal core の `EnvelopeProjection` に対応する tooling
artifact だが、Lean theorem witness ではなく、projection 元の cone family の一意復元、
probability、causal proof、forecast correctness を結論しない。

### 13. Observation Boundaries and Governance Interventions（観測境界と governance intervention）

SFT の forecast は、何が観測され、何が観測されないかに強く依存する。
そのため、observation boundary は core concept である。

```text
Observation :=
  obs : FieldSpace -> ObservedSignatureRecord

ObservationBoundary :=
  measured axes
  + unavailable evidence
  + private evidence
  + extractor version
  + non-conclusions
```

governance intervention は、operation support、policy、observation、feedback update を変える
governance mechanism である。

```text
GovernanceIntervention :=
  support transformation
  + policy transformation
  + observation enrichment
  + feedback update
  + escalation / deferral rule

RestrictiveIntervention:
  removes unsafe support

RedirectiveIntervention:
  raises shortcut cost and lowers lawful path cost

InstrumentingIntervention:
  adds observation axes, tests, or runtime checks

EscalatingIntervention:
  converts proposal into review / design / incident record

LearningIntervention:
  updates field memory after observed outcome
```

review、CI、type checker、architecture rules、AI policy、runtime guard は、SFT では
governance intervention として扱われる。

### 14. Field Update and Closed-Loop Feedback（場の更新と閉ループ feedback）

SFT は予測だけでなく、予測と観測の差分で field model を更新する closed-loop theory である。

```text
FieldUpdate :=
  prior field
  + ForecastCone / ConsequenceEnvelope
  + observed PR signature delta
  + unexpected obstruction witnesses
  + review / CI outcome
  + runtime feedback
  -> posterior field
```

`FieldUpdate` は、自動的な予測精度向上を主張しない。
従うのは、指定された update rule の下で forecast error、missing evidence、
unexpected witness、policy drift、non-conclusions が posterior field に保存されることである。

Lean 側では `Formal/Arch/Evolution/SFTFieldUpdate.lean` が、この record-preservation
boundary を `ForecastRecord` / `ObservedOutcome` / `PosteriorFieldRecord` /
`FieldUpdate.UpdateSound` として切り出す。これは feedback preservation の anchor であり、
accuracy improvement、calibration、governance effectiveness の theorem ではない。

```text
UpdateSound(update)
  = observed delta / unexpected witness / review outcome
    are recorded in the posterior field
```

## Part IV. Principles and Theorems（原理と定理）

### 15. ForecastCone Narrowing（予測円錐の縮小）

Claim Level:

```text
set-valued support semantics と step simulation の下では L2。
transition-kernel semantics の下では L3。
dataset calibration 後に限り L4。
```

仕様 artifact が feature direction を保ちながら、選択された obstruction witness family を排除する
健全な制約を追加するなら、その witness family に関する `ForecastCone` は縮小する。

```text
sound constraint addition
  + 意図された feature direction が保存される
  + 選択された witness family が排除される
  -> その witness family に関して ForecastCone が縮小する
```

集合論的 core では、最初の theorem schema は support inclusion と step simulation である。
Lean core ではまず same `Field` / `Operation` 上の identity-field projection として証明している。
一般の対応関係 `~` をまたぐ simulation は、この schema の将来の拡張として扱う。

```text
PointwiseSupportInclusion(U2, U1)
  = 到達可能で対応する field F2 ~ F1 すべてについて:
      U2(F2) subset U1(F1)

StepSimulation(U2, U1, ~)
  = F2 からの任意の U2-step は F1 からの U1-step で simulation でき、
    次の field も ~ によって対応し続ける

PointwiseSupportInclusion(U2, U1)
  + StepSimulation(U2, U1, ~)
  + F2 ~ F1
  -> ForecastCone(F2, U2, h) は ForecastCone(F1, U1, h) へ射影される
```

selected witness family に関する narrowing は、global risk reduction ではない。
別の witness family へ complexity が転送されることがある。

Proof sketch（証明 sketch）:

```text
horizon h に関する帰納法で示す。

h = 0:
  対応する field は仮定により関係 ~ を満たす。

h + 1:
  F2 からの任意の U2-step を取る。
  StepSimulation により、F1 から対応する U1-step が得られる。
  後続 field も ~ によって対応し続ける。
  残りの horizon に帰納法の仮定を適用する。
```

### 16. Support Safety（support 安全性）

Claim Level:

```text
選択された safe region の下の accepted trajectory について L2。
global future safety は主張しない。
未測定 axis については主張しない。
```

safe region は operation の集合ではなく、signature / state 側の領域である。
support safety は、support 内の各 operation が selected safe region を保存することとして読む。

```text
SupportOperationsPreserveSafeRegion(U, O, R)
  = U から選択されたすべての operation は、
    観測 O の下で safe region R を保存する step だけを実現する

StateInSafeRegion(O, R, F)
  + accepted step はすべて U から選択される
  + SupportOperationsPreserveSafeRegion(U, O, R)
  -> accepted trajectory は R に留まる
```

これは明示された accepted trajectory と selected safe region に相対化された主張である。
global future safety は従わない。

Lean status:
`Formal/Arch/Evolution/SFTSupportSafety.lean` は、finite kernel を SFT の
`OperationSupport`、operation semantics を primitive transition witness 付き
`StepRelation` として読み、realized supported script から `ForecastCone` witness と
selected safe-region preservation を得る theorem package を持つ。accepted-step evidence は
record に残すが、support preservation の導出には使わない。

SFT Lean surface 全体の docs-facing entrypoint は
`Formal/Arch/Evolution/SFTTheoremPackages.lean` である。この entrypoint は
`SoftwareField`、`ForecastCone`、cone projection、artifact action、policy / governance、
reachability、support safety、`FieldUpdate`、`ConsequenceEnvelope`、AAT / ArchSig boundary、
counterexample package の代表 declaration と non-conclusion boundary を束ねる metadata であり、
calibration、global future safety を theorem claim に昇格しない。

Atom foundation との接続では、SFT は `AATCoreLocalAlgebraForSFT` と
`AATCoreTransition` を通じて `AATCore system` の transition を読む。
`AATCorePremisedConsequenceEnvelope` と `FieldSigAATCoreTransitionAnalysis` は
この transition を envelope / FieldSig analysis input として保持するが、AAT を
再定義せず、forecast correctness や global future safety を結論しない。

### 17. Proposal Accounting and Review Mediation（proposal accounting と review mediation）

Claim Level:

```text
review / CI / incident trace に基づく場合は L1。
coverage と overlap policy が明示定義されている場合は L2。
rejection / rework / deferral category が calibration されている場合は L4。
```

`Dissipation` は正式な保存則ではない。
正式語は `ProposalAccounting` または `ReviewMediation` である。

```text
ProposalAccounting(raw_proposal_universe)
  proposal pressure を次へ分類する:
    accepted
    rejected
    delayed
    unresolved
    coordination_record
    runtime_pressure_estimate
    unaccounted_remainder
  明示された coverage / overlap policy の下で行う。
```

review、CI、type checker、architecture rules は、単に proposal を止めるのではなく、
accepted、rejected、delayed、unresolved、rework、runtime pressure の record を作る。
SFT はこの mediation を、field update と governance design の入力として扱う。

### 18. Feedback Boundary Update（feedback による境界更新）

Claim Level:

```text
観測 outcome が記録されている場合は L1。
record preservation としての update soundness については L2。
forecast quality が dataset 上で calibration されている場合に限り L4。
```

forecast と観測された transition / signature delta / obstruction witness の差分を使うと、
posterior field は forecast error、missing evidence、unexpected witness、policy drift、
non-conclusions をより明示的に記録する。

```text
forecast
  + observed transition
  + forecast error
  -> boundary-aware posterior field
```

これは自動的な accuracy improvement theorem ではない。
次の forecast は、狭くなる場合も、広がる場合も、境界が再分類される場合もある。
update rule、dataset boundary、observation quality、policy drift が明示されている場合の
closed-loop boundary update schema である。

### 19. Stable Regions and Recurrent Development Paths（安定領域と反復的開発 path）

Claim Level:

```text
set-valued semantics の下での MayReach / MustReach / StableRegion は L2。
transition-kernel semantics の下での recurrent / likely reachability は L3。
trace による calibration 後に限り L4。
```

`Attractor` と `Basin` は、追加 semantics を必要とする語である。
集合論的 core では、まず may reachability、must reachability、stable region を分ける。

```text
MayReach_h(F, U, A)
  = F から出発する U-accepted path のうち、
    h step 以内に region A へ到達するものが存在する

MustReach_h(F, U, A)
  = F から出発するすべての U-accepted path が、
    h step 以内に region A へ到達する

StableRegion(U, A)
  = A 内の field からのすべての U-accepted step は A 内に留まる

ReachablePreimage_h(U, A)
  = { F | MayReach_h(F, U, A) }
```

`Attractor` と呼ぶには、少なくとも安定性、再帰性、または policy / probability semantics が必要である。
実務的には、`DefaultPath`、`RecurrentPattern`、`StableRegion` として扱う方が安全である。

## Part V. Computing Systems Built from SFT（SFT から作る計算システム）

### 20. SFT Computational Problems（SFT の計算問題）

SFT は概念だけでなく、計算問題の族を定義する。

```text
1. Field Reconstruction Problem
   artifact trace, codebase, review, CI, incident records から
   SoftwareField の近似を構成する。

2. Operation Support Inference Problem
   現在の field で、どの operation family が自然・可能・危険・低コストかを推定する。

3. ConsequenceEnvelope Generation Problem
   PRD / Spec / Issue / AI proposal から、
   reachable path classes, affected signature axes,
   possible obstruction witnesses, missing invariants を生成する。

4. Cone Narrowing Problem
   意図した feature direction を保ちつつ、
   selected witness family を除外する spec / issue / review constraint を合成する。

5. Support Safety Checking Problem
   selected safe region を保存する operation support / governance intervention になっているかを調べる。

6. Feedback Update Problem
   forecast と observed PR / review / CI / incident outcome の差分から
   posterior field model を更新する。

7. AI Proposal Governance Problem
   AI agent が生成する proposal support を bounded field model 内に収める。

8. Lifecycle Decision Problem
   repair / migration / contraction / end-of-life のどれを選ぶべきかを、
   architecture signature, operation cost, runtime risk, field capacity から診断する。
```

この章により、SFT は説明フレームではなく、計算機科学の問題設定になる。

代表的な問題は、次のように input、output、soundness boundary、claim level を明示する。

```text
問題:
  Field Reconstruction

入力:
  DevelopmentField D
  + modeling boundary B
  + artifact / review / CI / incident traces

出力:
  SoftwareFieldEstimate F_hat

Soundness boundary / 健全性境界:
  F_hat は、B の下で選択された evidence、利用できない evidence、
  unknown / unmodeled remainder を記録する。
  complete reconstruction ではなく、trace source と evidence category を保持する。

Claim Level:
  trace に基づく reconstruction として L1。
  held-out trace に対する validation 後に限り L4。
```

```text
問題:
  ConsequenceEnvelope Generation

入力:
  SoftwareFieldEstimate F_hat
  + artifact a
  + observation boundary O
  + operation support extractor U
  + horizon h

出力:
  ConsequenceEnvelope E

Soundness boundary / 健全性境界:
  report された各 path class は、選択された model の下で
  少なくとも一つの reachable path に支えられる。
  そうでない場合は heuristic / empirical と明示する。

Claim Level:
  set-valued reachability が定義されていれば L2。
  path class と axis delta が calibration されていれば L4。
```

```text
問題:
  Cone Narrowing

入力:
  target artifact direction
  + selected witness family W
  + support extractors U1, U2
  + step simulation relation

出力:
  選択された boundary の下で intended feature direction を保存しつつ、
  W を排除する constraint / spec / review intervention

Soundness boundary / 健全性境界:
  narrowing は W、selected support、selected horizon に相対化される。
  global risk reduction は従わない。

Claim Level:
  support inclusion と step simulation の下では L2。
  calibration がある場合に限り L4。
```

```text
問題:
  AI Proposal Governance

入力:
  AI proposal stream
  + prompt / policy boundary
  + SoftwareFieldEstimate F_hat
  + theorem boundary
  + review / CI traces

出力:
  bounded proposal support
  + shortcut witness report
  + review / CI intervention
  + posterior field update

Soundness boundary / 健全性境界:
  選択された boundary 内の proposal を governance する。
  一般的な AI safety は証明しない。

Claim Level:
  trace に基づく場合は L1。
  形式的な support restriction については L2。
  benchmark-calibrated shortcut detection については L4。
```

### 21. PRD-to-ConsequenceEnvelope Simulator（PRD から ConsequenceEnvelope への simulator）

simulator は SFT の応用ではない。
SFT を計算可能な理論にする実現形である。

```text
PRD / Spec / Issue / AI Proposal
  -> ArtifactDescriptor
  -> OperationSupport
  -> ForecastCone / ConsequenceEnvelope
  -> 期待される Signature Axis
  -> Obstruction Witness Candidate
  -> Missing Invariant / Boundary Report（不足 invariant / boundary の report）
  -> Review / CI / Issue Decomposition Recommendation
  -> 実際の PR / Review / CI / Incident outcome による Calibration
```

これは `PRD-to-PR predictor` ではない。
未来の一点予測ではなく、bounded ConsequenceEnvelope を生成する。

成熟度は段階的に分ける。

| level | 読み | 最小出力 |
| --- | --- | --- |
| 0 | explanatory metaphor | field / force という説明だけ。 |
| 1 | action classification | PRD action class / descriptor。 |
| 2 | support generation | candidate operation support。 |
| 3 | cone generation | bounded ForecastCone / path classes。 |
| 4 | ConsequenceEnvelope | signature axes / obstruction witnesses / missing boundary。 |
| 5 | weighting | path class weight / probability / unknown remainder。 |
| 6 | calibration | actual Issue / PR / review / CI outcome との照合と field update。 |

SFT が計算理論として成立する最低ラインは level 3 である。
実務ツールとしての価値は level 4 から強くなり、予測理論としての主張は level 5 以降、
科学的な検証可能性は level 6 の calibration に依存する。

level 6 の最小 protocol は `tools/fieldsig/docs/artifacts-and-boundaries.md` で管理する。
そこでは forecast item refs と observed PR / review / CI / outcome refs を held-out trace として
対応付け、review mediation と AI shortcut detection を別 benchmark として評価する。
calibration がない段階の `ConsequenceEnvelope` は、bounded review artifact であり、
forecast correctness、probability weighting、causal proof、global risk reduction を結論しない。

### 22. AI-Agent Governance under SFT（SFT における AI agent governance）

SFT は AI-mediated software evolution の基礎理論である。
AI coding agent の安全性は、モデル性能だけでは決まらない。
その proposal がどの field で生成され、governance intervention を受け、観測され、
feedback update されるかによって決まる。

```text
AI agent :=
  artifact interpreter
  + code proposal generator
  + local pattern amplifier
  + shortcut generator
  + review load shifter
  + hidden assumption reproducer
  + field participant
```

SFT は AI agent の一般的安全性を証明しない。
AI agent が生成する operation support を bound し、AAT theorem boundary と SFT forecast boundary の中で
review / CI feedback により制御する枠組みを与える。
最小 protocol は `tools/fieldsig/docs/artifacts-and-boundaries.md` で管理する。
そこでは prompt / policy boundary、allowed operation support、shortcut witness、
review / CI mediation、posterior field update を分け、AI policy compliance を
architecture lawfulness に昇格しない。

```text
AI Proposal Governance :=
  prompt / policy boundary
  + allowed operation support
  + theorem boundary
  + review / CI feedback
  + observed shortcut / witness report
  + field update
```

allowed operation support は、選択された boundary の下で reviewer が評価する
bounded candidate set である。shortcut witness は、その candidate set とは別に、
forbidden edge、missing invariant、runtime boundary、theorem boundary、review load などの
危険な低コスト path を report する。どちらも AI model capability evaluation や
forecast correctness の証明ではなく、後続の review / CI / incident trace と照合される
empirical input である。

### 23. Review / CI / Type Systems as Governance Interventions（governance intervention としての review・CI・type system）

review、CI、type system、architecture rule、runtime guard は、単なる quality gate ではない。
それらは future operation support と selection policy を変える governance intervention system である。

```text
GovernanceSystem :=
  review rule
  + CI / test / type checker
  + architecture rule
  + ownership boundary
  + runtime guard
  + feedback update rule
```

良い governance は、unsafe shortcut を単に拒否するだけではなく、
lawful path を低コスト化し、missing invariant を発見し、field memory へ反映する。

### 24. Lifecycle, Migration, End-of-Life, and Benchmarks（lifecycle・migration・end-of-life・benchmark）

software field は生成と成長だけでなく、老朽化、migration、縮約、削除、終焉を含む。

```text
LifecycleTrajectory :=
  birth
  + growth
  + stabilization
  + drift
  + repair / migration
  + contraction
  + end-of-life
```

End-of-life は失敗ではなく、lifecycle governance / field reconfiguration decision の一種である。
修復コスト、migration path、runtime risk、organizational capacity for repair / migration、
ConsequenceEnvelope の広がりを見て、repair、migration、deletion のどれを選ぶかを扱う。
この判断は project management recommendation ではなく、選択された観測境界の下で
architecture future と field capacity の変化を比較する bounded decision model である。

```text
LifecycleDecisionModel :=
  current LifecycleTrajectory
  + ArchSig measurement trajectory
  + ConsequenceEnvelope family
  + runtime / incident risk boundary
  + ownership / staffing boundary
  + selected intervention set
  + non-conclusions

SelectedIntervention :=
  repair | migration | contraction | deletion
```

比較軸は intervention ごとに異なる。

| intervention | 読み | 主な比較軸 |
| --- | --- | --- |
| repair | 既存 field を保ち、局所的な support / invariant を補う。 | repair adoption、missing invariant、runtime regression risk、ownership capacity。 |
| migration | old field から new field へ support と memory を写す。 | projection mismatch、dual-run cost、consumer compatibility、rollback path。 |
| contraction | support できない surface を縮小し、field capacity を再配分する。 | removed operation family、affected user / runtime boundary、simplified signature axes。 |
| deletion | field component または subsystem を lifecycle から外す。 | dependent operation loss、data / API retirement boundary、incident avoidance、unknown remainder。 |

`ConsequenceEnvelope` は各 intervention の affected regions、signature axes、obstruction
witness candidates、missing boundary を比較可能にする report projection である。
field capacity は、available operation support、ownership / staffing boundary、runtime
guard、migration support の組として読む。したがって、envelope が広いことは直ちに削除を
意味しないし、repair cost が低いことは future trajectory safety を意味しない。

SFT は benchmark と calibration を必要とする。

```text
SFT Benchmark Suite :=
  PRD-to-Issue Benchmark
  + Issue-to-PR Signature Benchmark
  + Review Mediation Benchmark
  + Incident Feedback Benchmark
  + AI Shortcut Benchmark
  + Lifecycle Decision Benchmark
```

benchmark があって初めて、SFT は経験科学としても評価可能になる。

## Part VI. Case Studies（ケーススタディ）

### 25. Coupon PRD（クーポン PRD）

Coupon PRD は、SFT の running example として使う。
対象領域を checkout / payment に固定し、feature addition の artifact action として読む。

```text
Input artifact:
  Coupon PRD

RawArtifactAction:
  source artifact = PRD
  target field components = requirement context, constraints, operation support
  target architecture regions = Checkout / Payment
  action boundary = coupon feature addition only
  non-conclusions = pricing strategy, marketing success, fraud model
```

PRD が「クーポンを適用できるようにする」とだけ述べ、丸め順序、payment state boundary、
discount policy の所有境界を明示しない場合、descriptor は複数の operation family を含む。

```text
ForceDescriptor candidates:
  add DiscountPolicy under Checkout
  + patch PaymentAdapter
  + create CouponRepository dependency
  + add UI-only discount flag

Missing invariants:
  rounding order
  discount composition law
  payment authorization boundary
  refund / cancellation semantics
```

この段階の ConsequenceEnvelope は、少なくとも次の path classes を持つ。

```text
ConsequenceEnvelope:
  lawful policy insertion path
  + hidden PaymentAdapter dependency path
  + rounding semantic obstruction path
  + UI-only discount drift path
  + unknown / unmodeled remainder
```

仕様が boundary と invariant を明示すると、support と policy は lawful path に寄る。
この narrowing は global risk reduction ではなく、selected witness family に関する
bounded claim である。

### 26. Migration（移行）

migration は、old-new projection mismatch と partial migration risk を伴う field transformation である。

```text
MigrationEnvelope :=
  bridge path
  + dual-run path
  + replacement path
  + rollback path
  + old-new projection mismatch
  + partial migration risk
  + consumer compatibility boundary
```

SFT は migration を単なる置換作業ではなく、field memory と operation support の再配置として扱う。

### 27. Incident Response（incident response）

incident response は、runtime observation が field update を強制する case である。

```text
IncidentFeedback :=
  incident observation
  + root-cause witness classification
  + missing invariant discovery
  + review / CI governance update
  + runtime observation update
  + forecast boundary revision
```

incident 後の修正が局所的に通っても、future trajectory safety は従わない。
SFT は incident を missing invariant / observation boundary / governance intervention の発見機会として扱う。

### 28. AI-Generated Shortcut（AI が生成する shortcut）

AI-generated proposal は、local pattern を増幅し、field 内で低コストに見える shortcut を生成しうる。
SFT の観点では、これは model quality だけでなく field support と policy の問題である。

```text
AIShortcutCase :=
  prompt boundary
  + generated operation support
  + selected shortcut path
  + missed theorem boundary
  + review / CI mediation
  + observed obstruction witness
  + posterior field update
```

AI proposal は、AAT theorem boundary と SFT ConsequenceEnvelope の両方に照らして評価する。

### 29. End-of-Life Decision（end-of-life 判断）

end-of-life は、成長の失敗ではなく、lifecycle governance / field reconfiguration の選択肢である。

```text
EndOfLifeDecision :=
  current architecture signature
  + repair cost
  + migration support
  + contraction boundary
  + runtime risk
  + ownership / staffing boundary
  + ConsequenceEnvelope
  + non-conclusions
```

SFT は market success や human intention を予測しない。
扱うのは、repair、migration、contraction、deletion が architecture future と field capacity に
与える影響である。
decision artifact は、選択肢を rank する automated recommendation ではなく、selected inputs、
excluded inputs、known missing evidence、non-conclusions を明示して reviewer / governance
discussion に渡す bounded report である。

## Part VII. Non-Conclusions and Research Program（非主張と研究プログラム）

### 30. Positioning（位置づけ）

SFT は、既存の software engineering framework の単なる言い換えではない。

```text
SFT は次のいずれでもない:
  static architecture metric
  software process model
  DevOps maturity model
  単なる socio-technical metaphor
  technical debt taxonomy
  AI coding benchmark
  formal verification の置き換え
```

SFT の独自性は、ソフトウェア進化そのものを計算対象にする点にある。
artifact と feedback は operation support を変え、governance は selection policy を変え、
observation boundary は signature trajectory を定め、ConsequenceEnvelope は
到達可能な architecture future を記述する。

```text
SFT の違いは、ソフトウェア進化そのものを計算対象として扱う点にある:
  artifact と feedback は operation support を作り替える。
  governance は selection policy を変える。
  observation は signature trajectory を定める。
  ConsequenceEnvelope は到達可能な architecture future を記述する。
```

### 31. What SFT Does Not Claim（SFT が主張しないこと）

SFT は次を主張しない。

```text
将来のソフトウェア挙動が機械的に決定される。
すべての organizational effect が形式モデル化できる。
ForecastCone が calibration なしに empirical prediction になる。
AAT theorem から future trajectory safety が従う。
observed measurement delta から causal artifact action が一意に同定できる。
AI policy compliance から architecture lawfulness が従う。
cone narrowing から global risk reduction が従う。
unmeasured axis が安全である。
ArchSig extraction が ground truth architecture object である。
human intention や market success が予測できる。
```

SFT は大きな理論であるが、万能理論ではない。
大きな射程を持つからこそ、claim boundary と non-conclusions を前面に置く。

### 32. Open Problems in the Computational Theory of Software Evolution（ソフトウェア進化の計算理論における未解決問題）

SFT の研究プログラムは、次の open problems を持つ。

```text
1. Lean formalization of ForecastCone and support simulation.
2. Formal relation between ConsequenceEnvelope and one or more ForecastCones.
3. Trace-grounded reconstruction of SoftwareField.
4. Calibration of PRD-to-ConsequenceEnvelope simulators.
5. Benchmark design for review mediation and AI shortcut detection.
6. Integration of AAT theorem boundaries with practical review systems.
7. Empirical study of codebase as field memory.
8. Governance design for AI-mediated software evolution.
9. Lifecycle and end-of-life decision models.
10. Deployed closed-loop SFT workbench.
```

SFT の最終的な到達点は、次の tool ecosystem である。

```text
SFT Workbench

入力:
  PRD
  design memo
  issue plan
  existing codebase
  architecture signature
  review / CI history
  incident history
  AI agent policy

出力:
  ConsequenceEnvelope
  affected architecture signature axes
  likely obstruction witness families
  missing invariant / boundary report
  risky default paths
  recommended issue decomposition
  recommended review / CI governance interventions
  AI proposal governance constraints
  expected feedback / calibration plan
```

SFT は開発者を置き換えるものではない。
ソフトウェア進化を、観測し、計算し、統治できる対象として見えるようにする。

最小の deployed closed-loop workbench は、単一の自動判断器ではなく、既存の
FieldSig artifact と operational feedback artifact を review cycle に束ねる
bounded workflow である。

```text
PRD / design memo / issue plan / AI proposal
  + existing codebase / ArchSig measurement snapshot
  + review / CI / PR / incident / ownership trace
  + AI agent policy
  -> ArtifactDescriptor
  -> OperationSupportEstimate
  -> ForecastConeSkeleton family
  -> ConsequenceEnvelope report
  -> AI proposal governance / lifecycle decision surface
  -> review / CI / issue decomposition intervention
  -> observed PR / review / CI / outcome refs
  -> ForecastCalibrationHook + B10 operational feedback
  -> field update note / hypothesis refresh input
```

最小 artifact flow は、次の責務を分ける。

| layer | 入力 | 出力 | 境界 |
| --- | --- | --- | --- |
| input normalization | PRD、Issue、AI proposal、source refs | `ArtifactDescriptor` | source refs と missing evidence を保存する。 |
| forecast construction | descriptor、policy constraints、bounded horizon | `OperationSupportEstimate`、`ForecastConeSkeleton` | finite support と unknown remainder を保存する。 |
| review projection | cone family、signature axes、theorem boundary | `ConsequenceEnvelope` | reviewer-facing report であり、causal forecast ではない。 |
| governance projection | AI policy、review / CI mediation refs | AI proposal governance / lifecycle decision surface | allowed / forbidden / unknown support を分ける。 |
| feedback join | observed PR / review / CI / outcome refs、B10 artifact | `ForecastCalibrationHook`、calibration review、hypothesis refresh input | observation linkage であり、forecast correctness の証明ではない。 |

依存関係は次の通りである。

- B12 / B13 SFT forecasting が `ConsequenceEnvelope` までの bounded forecast artifact を作る。
- future adapters は GitHub Issue JSON、AI proposal JSON、framework semantics、runtime / incident
  trace を supplied evidence として正規化する。
- B10 operational feedback は observed outcome、calibration review、threshold、ownership、
  repair adoption、incident correlation、hypothesis refresh を保存する。
- calibration hook は forecast item refs と observed refs を対応付け、benchmark protocol へ渡す。
- deployed workbench はこれらを一つの review cycle に束ねるが、実組織 deployment、
  automatic governance correctness、または causal theorem を追加しない。

phase plan は次の最小順序で進める。

| phase | 目的 | 次に必要なもの |
| --- | --- | --- |
| W0 artifact inventory | 既存 B10 / B12 / B13 / governance artifact と missing adapter を一覧化する。 | workbench run manifest の設計。 |
| W1 offline bundle | 1 件の PRD / Issue / AI proposal と既存 trace refs から workbench bundle を手動生成する。 | artifact refs、excluded inputs、non-conclusions の manifest 化。 |
| W2 review-loop dry run | generated envelope と governance projection を review / CI checklist に接続する。 | reviewer decision と CI outcome refs の収集。 |
| W3 calibration join | forecast items と observed refs を `ForecastCalibrationHook` / B10 artifact に接続する。 | held-out / prospective benchmark set。 |
| W4 deployed pilot | selected repository で scheduler と policy threshold を運用する。 | 組織別 calibration と incident / rollback / MTTR との継続照合。 |

W4 でも、workbench は forecast correctness、global risk reduction、AI safety、
automatic governance correctness、または real organization outcome の因果説明を結論しない。
その主張には、別途 calibration dataset、confounder 管理、prospective validation が必要である。
