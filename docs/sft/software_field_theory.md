# Software Field Theory: A Computational Theory of Field-Shaped Software Evolution

Software Field Theory (SFT) は、field-shaped software evolution の計算理論である。
SFT は、要求、artifact、実践、ツール、AI agent、レビュー、CI/CD、運用 feedback、
lifecycle decision が、コードベースの到達可能なアーキテクチャ未来をどう変えるかを扱う。

SFT の看板主張は次である。

```text
SFT turns software evolution into a computable object.
```

日本語では、SFT はソフトウェア進化を計算可能な対象にする理論である。
ソフトウェア進化は単なるコード変更列ではない。
artifact、実践、agent、governance mechanism、feedback loop が、何が自然な変更に見えるか、
何が許されるか、何が観測されるか、何が制御可能かを作り替える
field-shaped computation である。

```text
Software evolution is field-shaped:

artifacts
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
AAT makes architecture locally algebraic.
ArchSig makes architecture observable.
SFT makes software evolution computable.
```

SFT が `field`、`force`、`dissipation`、`attractor`、`basin` と呼ぶものは物理量ではない。
これらは development context、artifact-mediated change、proposal accounting、
stable region、reachable preimage として明示された場合に限って、計算対象になる。

## Part I. The New Object

### 1. Software Evolution as a Computable Object

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
Computable in SFT :=
  representable under explicit modeling boundary
  + bounded by selected horizon / universe / observation axes
  + reducible to selected computational questions:
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
Software evolution is not merely a sequence of code changes.
It is a field-shaped computation in which artifacts, practices, agents,
governance systems, and feedback loops reshape the operation space and
observable architectural futures of a codebase.
```

SFT はこの命題を、説明、測定、計算、governance の四つの層で扱う。

```text
Theory:
  software evolution を field-shaped computation として定義する。

Measurement:
  AAT / ArchSig により architecture object、signature、obstruction、
  theorem boundary、field estimate を観測可能にする。

Computation:
  operation support、policy、forecast cone、consequence envelope、
  support safety、feedback update を計算対象にする。

Governance:
  review、CI、type checker、AI policy、runtime feedback を、
  codebase future を変える governance intervention system として扱う。
```

### 2. Codebase as Field Memory

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

### 3. Development Fields

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

これにより、SFT は開発場全体の完全モデル化を避けつつ、明示境界内の計算可能な断面を扱う。

### 4. Architecture Futures and Signature Trajectories

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

#### Running Example Preview: Coupon PRD

曖昧な coupon PRD は、単に feature request を追加するだけではない。
それは checkout / payment 領域で、複数の path を自然に見せる field action である。

```text
Coupon PRD may expose:
  lawful DiscountPolicy insertion path
  + PaymentAdapter shortcut path
  + UI-only discount drift path
  + rounding semantic obstruction path
```

以降では、この例を artifact、operation support、consequence envelope、review governance、
feedback update へ展開する running example として使う。

## Part II. The Algebraic and Observational Basis

### 5. AAT: Local Algebra of Software Architecture

SFT は AAT の上に載る。
ただし、AAT は SFT のための理論ではない。
依存方向は片方向である。

```text
AAT does not depend on SFT.
SFT depends on AAT.
```

AAT はアーキテクチャを局所代数にする。
SFT はその局所代数を、architecture projection、local transition law、observable coordinate、
admissibility boundary として使う。

対応関係の詳細は [AAT / SFT Interface](aat_interface.md) に置く。
ここでは最小対応だけを再掲する。

| SFT 側の役割 | AAT 側 |
| --- | --- |
| architecture projection | `ArchitectureObject` |
| local transition law | `ArchitectureOperation` |
| protected constraint | `InvariantFamily` |
| defect / repair target / boundary axis | `ObstructionWitness` |
| partial observation coordinate | `ArchitectureSignature` |
| admissibility boundary | theorem boundary / non-conclusions |
| local path skeleton | `ArchitecturePath` |

SFT は AAT theorem を empirical prediction に変換しない。
AAT theorem は、SFT reachability / safety schema の local premise として使う。

### 6. ArchSig: Observing Architecture Signatures and Obstruction Witnesses

ArchSig は、実 artifact と codebase を AAT observables および SFT field estimates へ写す
観測層である。

```text
real artifacts
  -> ArchSig
  -> AAT observables
  -> SFT field estimates
```

ArchSig は、単一スコアではなく多軸診断を返す。
未測定 axis を 0 と読まない。
signature delta は、両側で測定済みで、axis ごとの比較順序が定義されている場合に限って
比較する。

```text
ObservedSignatureRecord :=
  measured ArchitectureSignature axes
  + unmeasured axes
  + out-of-scope axes
  + evidence boundary
  + measurement non-conclusions

SignatureDelta(S_before, S_after)
  is defined only for comparable measured axes
```

SFT へ渡す ArchSig output は、次のような report として扱う。

```text
ArchSigSFTReport :=
  action_class_candidates
  + target_architecture_regions
  + candidate_operation_families
  + comparable_signature_axes
  + expected_axis_delta_ranges
  + selected_obstruction_witness_families
  + missing_invariants
  + theorem_boundary_items
  + forecast_boundary
  + unknown_unmodeled_remainder
  + claim_level
```

### 7. Claim Boundaries

SFT が大きな理論として信用されるためには、claim level discipline が必要である。
SFT の主張は、どの観測、どの model、どの calibration に基づくかを明示する。

```text
Claim Level 0:
  conceptual / diagnostic interpretation

Claim Level 1:
  trace-grounded field diagnosis

Claim Level 2:
  set-valued formal theorem schema

Claim Level 3:
  probabilistic / transition-kernel model

Claim Level 4:
  dataset-calibrated empirical forecast

Claim Level 5:
  deployed closed-loop governance system
```

例:

```text
良い spec は forecast cone を狭める。
  Level 2, if support inclusion and step simulation are defined.
  Level 4, if calibrated on historical PR / review / CI outcomes.

AI proposal は shortcut を増やす。
  Level 1, if observed in trace.
  Level 4, if dataset-calibrated.

組織 field が architecture drift を生む。
  Level 1 or Level 4.
  It is not an unbounded theorem.
```

## Part III. The SFT Core

### 8. SoftwareField and Architecture Projection

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

### 9. Artifact-Mediated Change

正式な計算概念は `ArtifactMediatedChange` または `ArtifactAction` である。
`Force` は、その field-level reading を指す非公式名として残す。

```text
ArtifactAction a :=
  alpha_a : FieldSpace -> Set FieldSpaceUpdateHypothesis

FieldSpaceUpdateHypothesis :=
  candidate update descriptor sufficient to construct or constrain
  a successor SoftwareField under an explicit interpretation boundary

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

### 10. Operation Support, Policy, and Selection

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

### 11. Forecast Cones and Consequence Envelopes

`ForecastCone` は formal object である。
horizon `h` と operation support `U` に相対化された reachable field path set として読む。

```text
FieldPath :=
  path in FieldSpace

ReachableFieldPath(F, U, h, p)
  = p starts at F
  + length(p) <= h
  + for every adjacent pair F_i -> F_{i+1},
      exists op in U(F_i) such that StepRelation(F_i, op, F_{i+1})

StepRelation(F, op, F')
  = operation op can realize a transition from F to F'
    under the selected theorem boundary and field model

ForecastCone(F, U, h) :=
  { p : FieldPath | ReachableFieldPath(F, U, h, p) }
```

artifact action 付きの cone は、formal core の `ForecastCone(F, U, h)` から派生させる。
set-valued action の場合は、candidate update ごとに cone を生成し、その族を envelope へまとめる。

```text
u in alpha_a(F)
F_u := applyUpdate(F, u)
U_u := U(F_u)

ForecastConeFamilyAfterAction(F, a, h) :=
  { ForecastCone(F_u, U_u, h) | u in alpha_a(F) }
```

`ConsequenceEnvelope` は、実務・診断・tooling 側の提示形式である。
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

理論家には `ForecastCone`、実務家には `ConsequenceEnvelope`、tooling には simulator output を返す。

### 12. Observation Boundaries and Governance Interventions

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

### 13. Field Update and Closed-Loop Feedback

SFT は予報だけでなく、予報と観測の差分で field model を更新する closed-loop theory である。

```text
FieldUpdate :=
  prior field
  + forecast cone / consequence envelope
  + observed PR signature delta
  + unexpected obstruction witnesses
  + review / CI outcome
  + runtime feedback
  -> posterior field
```

`FieldUpdate` は、自動的な予測精度向上を主張しない。
従うのは、指定された update rule の下で forecast error、missing evidence、
unexpected witness、policy drift、non-conclusions が posterior field に保存されることである。

```text
UpdateSound(update)
  = observed delta / unexpected witness / review outcome
    are recorded in the posterior field
```

## Part IV. Principles and Theorems

### 14. Forecast Cone Narrowing

Claim Level:

```text
L2 under set-valued support semantics and step simulation.
L3 under transition-kernel semantics.
L4 only after dataset calibration.
```

仕様 artifact が feature direction を保ちながら、選択された obstruction witness family を排除する
健全な制約を追加するなら、その witness family に関する forecast cone は縮小する。

```text
sound constraint addition
  + intended feature direction preserved
  + selected witness family excluded
  -> forecast cone narrows with respect to that witness family
```

集合論的 core では、最初の theorem schema は support inclusion と step simulation である。

```text
PointwiseSupportInclusion(U2, U1)
  = for all reachable paired fields F2 ~ F1:
      U2(F2) subset U1(F1)

StepSimulation(U2, U1, ~)
  = every U2-step from F2 can be simulated by a U1-step from F1
    and the next fields remain related by ~

PointwiseSupportInclusion(U2, U1)
  + StepSimulation(U2, U1, ~)
  + F2 ~ F1
  -> ForecastCone(F2, U2, h) projects into ForecastCone(F1, U1, h)
```

selected witness family に関する narrowing は、global risk reduction ではない。
別の witness family へ complexity が転送されることがある。

Proof sketch:

```text
By induction on horizon h.

h = 0:
  the paired fields are related by assumption.

h + 1:
  take any U2-step from F2.
  StepSimulation gives a matching U1-step from F1.
  The successor fields remain related by ~.
  Apply the induction hypothesis to the remaining horizon.
```

### 15. Support Safety

Claim Level:

```text
L2 for accepted trajectories under selected safe region.
No claim about global future safety.
No claim about unmeasured axes.
```

safe region は operation の集合ではなく、signature / state 側の領域である。
support safety は、support 内の各 operation が selected safe region を保存することとして読む。

```text
SupportOperationsPreserveSafeRegion(U, O, R)
  = every operation selected from U realizes only steps
    that preserve safe region R under observation O

StateInSafeRegion(O, R, F)
  + every accepted step is selected from U
  + SupportOperationsPreserveSafeRegion(U, O, R)
  -> accepted trajectory stays in R
```

これは明示された accepted trajectory と selected safe region に相対化された主張である。
global future safety は従わない。

### 16. Proposal Accounting and Review Mediation

Claim Level:

```text
L1 when grounded in review / CI / incident traces.
L2 when coverage and overlap policy are explicitly defined.
L4 when rejection / rework / deferral categories are calibrated.
```

`Dissipation` は正式な保存則ではない。
正式語は `ProposalAccounting` または `ReviewMediation` である。

```text
ProposalAccounting(raw_proposal_universe)
  classifies proposal pressure into
    accepted
    rejected
    delayed
    unresolved
    coordination_record
    runtime_pressure_estimate
    unaccounted_remainder
  under an explicit coverage / overlap policy
```

review、CI、type checker、architecture rules は、単に proposal を止めるのではなく、
accepted、rejected、delayed、unresolved、rework、runtime pressure の record を作る。
SFT はこの mediation を、field update と governance design の入力として扱う。

### 17. Feedback Boundary Update

Claim Level:

```text
L1 when observed outcomes are recorded.
L2 for update soundness as record preservation.
L4 only if forecast quality is calibrated over a dataset.
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

### 18. Stable Regions and Recurrent Development Paths

Claim Level:

```text
L2 for MayReach / MustReach / StableRegion under set-valued semantics.
L3 for recurrent or likely reachability under transition-kernel semantics.
L4 only after calibration against traces.
```

`Attractor` と `Basin` は、追加 semantics を必要とする語である。
集合論的 core では、まず may reachability、must reachability、stable region を分ける。

```text
MayReach_h(F, U, A)
  = some U-accepted path from F reaches region A within h steps

MustReach_h(F, U, A)
  = every U-accepted path from F reaches region A within h steps

StableRegion(U, A)
  = every U-accepted step from a field in A stays in A

ReachablePreimage_h(U, A)
  = { F | MayReach_h(F, U, A) }
```

`Attractor` と呼ぶには、少なくとも安定性、再帰性、または policy / probability semantics が必要である。
実務的には、`DefaultPath`、`RecurrentPattern`、`StableRegion` として扱う方が安全である。

## Part V. Computing Systems Built from SFT

### 19. SFT Computational Problems

SFT は概念だけでなく、計算問題の族を定義する。

```text
1. Field Reconstruction Problem
   artifact trace, codebase, review, CI, incident records から
   SoftwareField の近似を構成する。

2. Operation Support Inference Problem
   現在の field で、どの operation family が自然・可能・危険・低コストかを推定する。

3. Consequence Envelope Generation Problem
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
Problem:
  Field Reconstruction

Input:
  DevelopmentField D
  + modeling boundary B
  + artifact / review / CI / incident traces

Output:
  SoftwareFieldEstimate F_hat

Soundness boundary:
  F_hat records selected evidence, unavailable evidence,
  and unknown / unmodeled remainder under B.

Claim Level:
  L1 as trace-grounded reconstruction.
  L4 only after validation against held-out traces.
```

```text
Problem:
  Consequence Envelope Generation

Input:
  SoftwareFieldEstimate F_hat
  + artifact a
  + observation boundary O
  + operation support extractor U
  + horizon h

Output:
  ConsequenceEnvelope E

Soundness boundary:
  every reported path class is supported by at least one reachable path
  under the selected model, or explicitly marked heuristic / empirical.

Claim Level:
  L2 if set-valued reachability is defined.
  L4 if path classes and axis deltas are calibrated.
```

```text
Problem:
  Cone Narrowing

Input:
  target artifact direction
  + selected witness family W
  + support extractors U1, U2
  + step simulation relation

Output:
  constraint / spec / review intervention that excludes W
  while preserving intended feature direction under the selected boundary

Soundness boundary:
  narrowing is relative to W, selected support, and selected horizon.
  It does not imply global risk reduction.

Claim Level:
  L2 under support inclusion and step simulation.
  L4 only with calibration.
```

```text
Problem:
  AI Proposal Governance

Input:
  AI proposal stream
  + prompt / policy boundary
  + SoftwareFieldEstimate F_hat
  + theorem boundary
  + review / CI traces

Output:
  bounded proposal support
  + shortcut witness report
  + review / CI intervention
  + posterior field update

Soundness boundary:
  governs proposals within selected boundaries.
  It does not prove general AI safety.

Claim Level:
  L1 when trace-grounded.
  L2 for formal support restrictions.
  L4 for benchmark-calibrated shortcut detection.
```

### 20. PRD-to-ConsequenceEnvelope Simulator

simulator は SFT の応用ではない。
SFT を計算可能な理論にする実現形である。

```text
PRD / Spec / Issue / AI Proposal
  -> ArtifactDescriptor
  -> OperationSupport
  -> ForecastCone / ConsequenceEnvelope
  -> Expected Signature Axes
  -> Obstruction Witness Candidates
  -> Missing Invariant / Boundary Report
  -> Review / CI / Issue Decomposition Recommendation
  -> Calibration by actual PR / Review / CI / Incident outcomes
```

これは `PRD-to-PR predictor` ではない。
未来の一点予測ではなく、bounded consequence envelope を生成する。

成熟度は段階的に分ける。

| level | 読み | 最小出力 |
| --- | --- | --- |
| 0 | explanatory metaphor | field / force という説明だけ。 |
| 1 | action classification | PRD action class / descriptor。 |
| 2 | support generation | candidate operation support。 |
| 3 | cone generation | bounded forecast cone / path classes。 |
| 4 | consequence envelope | signature axes / obstruction witnesses / missing boundary。 |
| 5 | weighting | path class weight / probability / unknown remainder。 |
| 6 | calibration | actual Issue / PR / review / CI outcome との照合と field update。 |

SFT が計算理論として成立する最低ラインは level 3 である。
実務ツールとしての価値は level 4 から強くなり、予測理論としての主張は level 5 以降、
科学的な検証可能性は level 6 の calibration に依存する。

### 21. AI-Agent Governance under SFT

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

```text
AI Proposal Governance :=
  prompt / policy boundary
  + allowed operation support
  + theorem boundary
  + review / CI feedback
  + observed shortcut / witness report
  + field update
```

### 22. Review / CI / Type Systems as Governance Interventions

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

### 23. Lifecycle, Migration, End-of-Life, and Benchmarks

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
consequence envelope の広がりを見て、repair、migration、deletion のどれを選ぶかを扱う。

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

## Part VI. Case Studies

### 24. Coupon PRD

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

この段階の consequence envelope は、少なくとも次の path classes を持つ。

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

### 25. Migration

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

### 26. Incident Response

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

### 27. AI-Generated Shortcut

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

AI proposal は、AAT theorem boundary と SFT consequence envelope の両方に照らして評価する。

### 28. End-of-Life Decision

end-of-life は、成長の失敗ではなく、lifecycle governance / field reconfiguration の選択肢である。

```text
EndOfLifeDecision :=
  current architecture signature
  + repair cost
  + migration support
  + runtime risk
  + ownership / staffing boundary
  + consequence envelope
  + non-conclusions
```

SFT は market success や human intention を予測しない。
扱うのは、repair、migration、contraction、deletion が architecture future と field capacity に
与える影響である。

## Part VII. Non-Conclusions and Research Program

### 29. Positioning

SFT は、既存の software engineering framework の単なる言い換えではない。

```text
SFT is not:
  a static architecture metric,
  a software process model,
  a DevOps maturity model,
  a socio-technical metaphor,
  a technical debt taxonomy,
  an AI coding benchmark,
  or a replacement for formal verification.
```

SFT の独自性は、ソフトウェア進化そのものを計算対象にする点にある。
artifact と feedback は operation support を変え、governance は selection policy を変え、
observation boundary は signature trajectory を定め、consequence envelope は
到達可能な architecture future を記述する。

```text
SFT differs by treating software evolution itself as the computable object:
  artifacts and feedback reshape operation support,
  governance changes selection policy,
  observations define signature trajectories,
  and consequence envelopes describe reachable architectural futures.
```

### 30. What SFT Does Not Claim

SFT は次を主張しない。

```text
future software behavior is mechanically determined.
every organizational effect is formally modelable.
forecast cones are empirical predictions without calibration.
AAT theorem implies future trajectory safety.
observed signature delta uniquely identifies causal artifact action.
AI policy compliance implies architecture lawfulness.
cone narrowing implies global risk reduction.
unmeasured axes are safe.
ArchSig extraction is ground truth architecture object.
human intention or market success can be predicted.
```

SFT は大きな理論であるが、万能理論ではない。
大きな射程を持つからこそ、claim boundary と non-conclusions を前面に置く。

### 31. Open Problems in the Computational Theory of Software Evolution

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

Input:
  PRD
  design memo
  issue plan
  existing codebase
  architecture signature
  review / CI history
  incident history
  AI agent policy

Output:
  consequence envelope
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
開発ツールが何を見られるかを変える。
