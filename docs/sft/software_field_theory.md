# Software Field Theory ソフトウェアの場の理論

SFT は、ソフトウェア進化を場の力学として扱う理論である。
AAT はソフトウェアアーキテクチャの局所代数として独立に成立し、
SFT はその局所代数を state space、observable coordinate、local law として使う。

```text
SFT studies software evolution as:

software field
  + artifact-induced forces
  + operation support / policies
  + signature trajectories
  + dissipation
  + feedback control
```

SFT が `field`、`force`、`dissipation`、`basin` と呼ぶものは、
物理量ではない。
これらは bounded transition system 上の state、artifact action、filter / accounting record、
reachable region として定義される場合に限って、力学として扱う。

```text
SFT dynamics core :=
  field state
  + artifact action
  + operation support / policy
  + accepted transition
  + observation
  + control filter
  + reachable path set
  + field update
```

SFT の主題は、要求、仕様、Issue、PR、組織、AI、運用が architecture state に加える
force、誘導する trajectory、散逸する obstruction、制御に使われる feedback である。
ここでいう field はコードベースに限らない。
PdM、PO、アーキテクト、エンジニア、AI agent、レビュー、CI/CD、運用 feedback を含む
開発組織全体が、operation support / policy と signature trajectory を形作る。

直感的には、曖昧な coupon PRD は checkout と payment へ feature force をかける。
このとき `DiscountPolicy`、丸め規則、payment state boundary が仕様にないなら、
forecast cone は `PaymentAdapter -> CouponRepository` のような危険な trajectory を含みうる。
仕様がそれらの境界と不変量を明示すれば、cone は狭まり、operation support / policy は
より lawful な path へ寄る。

## 1. AAT との関係

SFT は AAT の上に載る。ただし、AAT は SFT のための理論ではない。
依存方向は片方向である。

```text
AAT does not depend on SFT.
SFT depends on AAT.
```

対応関係の詳細は [AAT / SFT Interface](aat_interface.md) に置く。
ここでは最小対応だけを再掲する。

| SFT 側 | AAT 側 |
| --- | --- |
| field state | `ArchitectureObject` |
| local transition | `ArchitectureOperation` |
| preserved constraint | `InvariantFamily` |
| local resistance / defect | `ObstructionWitness` |
| observable coordinate | `ArchitectureSignature` |
| admissibility boundary | theorem boundary / non-conclusions |
| local path skeleton | `ArchitecturePath` |

SFT は AAT theorem を empirical prediction へ変換しない。
AAT の局所主張を、field model の観測量、制約、制御入力として使う。

## 2. Software Field

`SoftwareField` は、architecture state と、その state から次にどの operation が選ばれやすいかを
決める文脈を合わせた対象である。

```text
SoftwareField :=
  architecture state
  + architecture signature
  + history
  + operation support
  + requirement context
  + design constraints
  + review / CI constraints
  + organization policy
  + AI agent policy
  + runtime feedback
```

SFT の最小 formal core は、まず確率を入れず、bounded transition system として置く。

```text
SoftwareField_t :=
  X_t  : ArchitectureObject
  sig_t : ArchitectureSignature
  H_t  : History
  U_t  : admissible operation support
  π_t  : operation policy / preference
  C_t  : constraint environment
  O_t  : observation model
  R_t  : review / CI / control filter
  E_t  : exogenous artifact inputs
```

集合論的 core では、`U_t` は選択可能な operation の support、
`π_t` は support 上の policy / preference である。
確率的 semantics を採用する場合に限り、分布 `μ_t : OperationDistribution` を追加する。

力学としての最小構造は次である。

```text
FieldSpace :=
  set of SoftwareField states

ArtifactAction a :=
  α_a : FieldSpace -> FieldSpace

SupportExtractor :=
  U : FieldSpace -> Set ArchitectureOperation

PolicyExtractor :=
  π : FieldSpace -> OperationPolicy

Step :=
  step : FieldSpace -> ArchitectureOperation -> Option FieldSpace

Observation :=
  obs : FieldSpace -> ArchitectureSignature

ControlFilter :=
  R : FieldSpace -> FieldSpace
```

artifact action を force として扱うには、任意の endomorphism ではなく、
少なくとも作用の境界を持つ必要がある。

```text
ArtifactActionFamily :=
  identity action
  + composition of actions
  + projection to support / policy / constraint / filter / observation changes
  + observable delta boundary
  + non-conclusions
```

PRD、Spec、Issue、Review、CI、Incident は、直接 theorem になるのではなく、
`ArtifactAction`、`ControlFilter`、`Observation`、`FieldUpdate` のどれとして読むかを
明示したときに SFT の対象になる。

基本遷移は次の形で読む。

```text
E_t + field context
  -> shaped operation support U'_t
  -> accepted operation a_t
  -> X_{t+1}
  -> sig_{t+1}
  -> SoftwareField_{t+1}
```

確率分布、entropy、stochastic dominance、Markov kernel は、この集合論的 core の後に載せる
追加 semantics である。
最初の SFT theorem は、operation support、transition relation、signature observation、
forecast cone を集合として扱う。

同じ `ArchitectureObject` でも、field が異なれば次の operation support / policy は異なる。
同じ module graph でも、レビュー規則、所有境界、既存 canonical pattern、テスト粒度、
AI prompt、incident history が違えば、将来選ばれやすい操作は変わる。

```text
field_t
  -> operation support U_t
  -> operation policy π_t
  -> accepted / rejected transitions
  -> signature_t+1
  -> field_t+1
```

この式は決定論ではない。SFT が扱うのは、field が operation support / policy と
signature trajectory をどのように形作るかである。

## 3. Force

`Force` は、field を別の field へ写す artifact-induced action である。
要求、仕様、Issue、PR、レビュー、CI、incident、組織判断、AI prompt は、すべて force の発生源になりうる。

最小 semantics では、force は field action として読む。

```text
force_a : FieldSpace -> FieldSpace
```

ただし、任意の `FieldSpace -> FieldSpace` を force と呼ぶのではない。
SFT で扱う force は、source artifact、作用する field 成分、観測可能な delta、
合成境界、non-conclusions を持つ artifact action である。

その射影として、support、policy、constraint、filter、observation model が変わる。

```text
support-shaping force:
  U(force_a F) differs from U(F)

policy-shaping force:
  π(force_a F) differs from π(F)

constraint-shaping force:
  C(force_a F) differs from C(F)

filter-shaping force:
  R(force_a F) differs from R(F)

observation-shaping force:
  O(force_a F) differs from O(F)
```

たとえば spec clause は constraint と support を変え、Issue 分割は support を局所化し、
review policy は filter を変え、incident は observation model や law universe update pressure を生む。
確率的 semantics を採用する場合は、force が `μ_t` をどう変えるかを追加で読む。

```text
ArtifactForce :=
  source artifact
  + target field region
  + candidate operation support
  + expected signature delta
  + expected obstruction pressure
  + uncertainty boundary
```

force は一種類ではない。

```text
feature force
deletion force
migration force
repair force
coupling force
boundary force
invariant force
effect force
debt force
refactor force
replacement force
incident response force
end-of-life force
```

良い artifact は、feature force と stabilizing force を同時に持つ。
悪い artifact は、feature force を出しながら、hidden interaction、ambiguity、coupling、
effect leakage へ力を散らす。

## 4. Force Taxonomy

SFT では force を観測可能性と artifact の役割で分ける。

| force class | 読み | 主な evidence |
| --- | --- | --- |
| `ObservedForce` | accepted transition の before / after signature delta として観測できる force。 | PR before / after signature、drift ledger、Feature Extension Report。 |
| `LatentForce` | 要求、設計、prompt、組織判断、既存 local grammar が operation support / policy に与える見えない作用。 | requirement metadata、design boundary、prompt / agent policy、PR proposal support / policy、case study。 |
| `DissipatedForce` | review / CI / type / policy により拒否、修正、減衰された raw force。 | rejected PR、CI failure、review-requested changes、policy decision report。 |

AAT に近いのは accepted transition と selected signature delta である。
latent force と dissipated force は、原則として tooling / empirical dataset で推定する。

artifact の粒度では、次の下位型を区別する。

```text
RequirementForce :=
  feature direction
  + value pressure
  + ambiguity boundary
  + force class

SpecForce :=
  invariant channel
  + interface constraints
  + observation model

IssueForce :=
  operation support restriction
  + locality boundary

PRForce :=
  realized transition
  + actual signature delta

ReviewForce :=
  rejection / projection / repair / damping

IncidentForce :=
  runtime obstruction pressure
  + law universe update pressure
```

PRD、Spec、Issue、PR、Review、Incident はすべて force の source になりうるが、
同じ種類の force ではない。PRD は方向と曖昧さを持ち、Spec は constraint channel を作り、
Issue は operation support を狭め、PR は realized transition を観測させる。

PRD の force class は、forecast cone の初期形を決める。
新機能追加、削除、migration、repair、incident response、end-of-life は、
同じ PRD artifact でも異なる operation support template と obstruction template を持つ。

```text
PRDForceClass :=
  feature_addition
  + feature_deletion
  + migration
  + replacement
  + repair
  + refactor
  + compliance
  + incident_response
  + performance_scaling
  + observability
  + deprecation
  + end_of_life
```

## 5. Operation Support, Policy, Distribution

`OperationDistribution` は、確率的 semantics を採用したときに、
ある field で次に選ばれうる operation の分布として現れる。
集合論的 core では、support と policy を分けて扱う。

```text
OperationSupport(field)
  = admissible operation set after constraints / filters

OperationPolicy(field)
  = preference / selection rule on that support

OperationDistribution(field)
  = optional probabilistic semantics over that support
```

SFT では、「どの operation が正しいか」だけでなく、
「どの operation が選ばれやすい field になっているか」を問う。
同じ lawful operation が存在しても、それが選ばれにくく、unlawful shortcut が選ばれやすいなら、
field は悪い basin へ落ちやすい。

```text
bad field:
  lawful path exists
  + unlawful shortcut is easier

good field:
  lawful path exists
  + lawful path is locally natural
  + unlawful shortcut is filtered or expensive
```

## 6. Signature Trajectory

`SignatureTrajectory` は、field の遷移に沿って観測される signature の列である。

```text
SignatureTrajectory :=
  signature_0
  -> signature_1
  -> ...
  -> signature_n
```

SFT は endpoint だけを見ない。
safe endpoint から safe trajectory は従わない。
net signature delta が 0 でも、途中で unsafe excursion が起きることがある。

```text
endpoint safe
  does not imply
path safe

net delta = 0
  does not imply
no excursion
```

この区別は、AAT の selected theorem boundary と SFT の trajectory-level safety を混同しないために重要である。

## 7. Forecast Cone

`ForecastCone` は、現在の field と artifact force から到達しうる field path の集合または分布である。
最小 core では、horizon `h` と operation support `U` に相対化された reachable field path set として読む。
SFT の path は文脈付きの field path であり、AAT の `ArchitecturePath` へは projection して読む。

```text
FieldPath :=
  path in FieldSpace

ProjectArchitecturePath :=
  FieldPath -> ArchitecturePath

ReachableFieldPath(F, U, h, p)
  = p starts at F
  + length(p) <= h
  + every step uses an operation in U(current field)
  + every step follows step(current field, operation)

ForecastCone(F, U, h) :=
  { p : FieldPath | ReachableFieldPath(F, U, h, p) }
```

分布付き forecast cone は、この path set に probability / preference / cost を載せた拡張である。

```text
ForecastCone(field, force) :=
  possible FieldPath distribution
  + projected ArchitecturePath distribution
  + expected signature delta
  + obstruction risk distribution
  + uncertainty boundary
  + non-conclusion boundary
```

forecast は theorem ではない。
AAT の theorem boundary、signature axes、witness families、historical dataset、
review / CI policy に相対化された bounded prediction である。

`ForecastBoundary` は、forecast が何に相対化されているかを明示する。

```text
ForecastBoundary :=
  selected architecture universe
  + selected artifact set
  + historical prior / dataset boundary
  + operation support boundary
  + signature axes used
  + organization / review policy assumptions
  + unavailable / private evidence
  + non-conclusions
```

したがって forecast cone は未来予言ではなく、
universe、artifact、prior、policy、unavailable evidence を明示した bounded model である。

Spec は forecast cone を狭める force-shaping artifact として読む。
良い spec clause は、operation support を狭め、lawful path を明確にし、
hidden interaction や ambiguity へ流れる力を減らす。

## 8. Fundamental Principles

SFT の主張は、Lean theorem ではなく、bounded field model 上の principle / theorem schema として置く。
各 principle は `ForecastBoundary`、選択された signature axes、witness families、
artifact set、operation support に相対化される。
各 principle は、採用する semantics によって claim level が変わる。

```text
set-valued support semantics:
  formal theorem schema

transition-kernel semantics:
  probabilistic theorem schema

dataset-calibrated semantics:
  empirical hypothesis

incomplete observation:
  control heuristic with non-conclusions
```

SFT の主張が単なる説明を越えるのは、次の形に落ちる場合である。

```text
defined state space
  + defined artifact action / control
  + defined support extractor
  + defined step relation
  + defined observation
  -> reachability / inclusion / preservation theorem
```

これに落ちない主張は、SFT 内では heuristic、tooling claim、または empirical hypothesis として扱う。

### 8.1 Forecast Cone Narrowing Principle

仕様 artifact が feature 方向を保ちながら、選択された obstruction witness family を排除する
健全な制約を追加するなら、その witness family に関する forecast cone は縮小する。

```text
sound constraint addition
  + intended feature direction preserved
  + selected witness family excluded
  -> forecast cone narrows with respect to that witness family
```

集合論的 core では、最初の theorem schema は support inclusion である。
ただし、これは固定された step semantics と compatible な field update の下でのみ成立する。
初期 field で `U2(F) ⊆ U1(F)` でも、1 step 後の update が support を広げるなら
cone inclusion は従わない。

```text
PointwiseSupportInclusion(U2, U1)
  = for all reachable paired fields F2 ~ F1:
      U2(F2) ⊆ U1(F1)

StepSimulation(U2, U1, ~)
  = every U2-step from F2 can be simulated by a U1-step from F1
    and the next fields remain related by ~

PointwiseSupportInclusion(U2, U1)
  + StepSimulation(U2, U1, ~)
  + F2 ~ F1
  -> ForecastCone(F2, U2, h) projects into ForecastCone(F1, U1, h)
```

同一 field、同一 step relation、support が state update によって予期せず広がらない特殊ケースでは、
これは単純な `U2(F) ⊆ U1(F)` からの cone inclusion として読める。

selected witness family に関する narrowing は、global risk reduction ではない。
ある witness family を除外しても、別の witness family へ complexity が転送されることがある。

これは SFT の看板原理である。
良い PRD / Spec / Issue は、単に作業を増やす artifact ではなく、
将来の architecture trajectory の cone を狭める force-shaping artifact である。

### 8.2 Support Safety Principle

safe region は operation の集合ではなく、signature / state 側の領域である。
したがって support safety は「operation support が safe region の中にある」ことではなく、
support 内の各 operation が selected safe region を保存することとして読む。

```text
SupportOperationsPreserveSafeRegion(U, O, R)
  = every operation selected from U realizes only steps
    that preserve safe region R under observation O

StateInSafeRegion(O, R, F)
  + every accepted step is selected from U
  + SupportOperationsPreserveSafeRegion(U, O, R)
  -> accepted trajectory stays in R
```

support-restricting filters compose.

```text
U(R1(F)) ⊆ U(F)
  + U(R2(R1(F))) ⊆ U(R1(F))
  ->
  U(R2(R1(F))) ⊆ U(F)
```

ただし、これは明示された accepted trajectory と selected safe region に相対化された主張である。
global / future trajectory safety は従わない。
未測定軸、private evidence、future force は `ForecastBoundary` の non-conclusions に残る。

### 8.3 Dissipation Boundary Principle

raw force が review、CI、type、policy によって拒否、射影、修正されるとき、
その力は消えるのではなく、accepted transition、rejected transition、ambiguity、
coordination cost、runtime pressure のどこかへ分配される。

```text
raw force
  -> accepted transition
   + rejected / delayed transition
   + ambiguity / coordination cost
   + runtime pressure
```

ここでいう dissipation は、物理的な保存量を仮定する概念ではない。
拒否または変更された operation pressure が、どの observable record に現れるかを記録する
accounting schema である。

```text
DissipationRecord :=
  raw proposal support / policy
  + accepted support / policy
  + rejected operation log
  + delayed operation log
  + unresolved demand
  + coordination / ambiguity record
  + runtime pressure estimate
  + unaccounted remainder
  + coverage boundary
```

theorem schema として使うには、記録対象が raw proposal を被覆すること、
各分類が互いにどう重なりうるか、unaccounted remainder をどう残すかを明示する。
SFT は、dissipation を単なる失敗ではなく、force がどの軸へ移ったかを
coverage boundary 付きで追跡する対象として扱う。

### 8.4 Feedback Refinement Principle

forecast と観測された transition / signature delta / obstruction witness の差分を使って
field model を更新すれば、同じ artifact class に対する次の forecast boundary は精緻化される。

```text
forecast
  + observed transition
  + forecast error
  -> refined field model
```

これは自動的な精度向上を主張しない。
update rule、dataset boundary、observation quality、policy drift が明示されている場合の
closed-loop refinement schema である。

## 9. Issue と PR

Issue は、artifact force を bounded operation support へ分解する単位である。

```text
IssueOperationSupport :=
  allowed operation family
  + target invariant
  + expected witness impact
  + theorem boundary
  + non-conclusions
```

PR は、予測された force が実際にどの transition になったかを観測する点である。

```text
PRSignatureDelta :=
  actual architecture operation
  + before signature
  + after signature
  + expected / actual delta comparison
  + unexpected obstruction witnesses
```

PR が局所的に通ることから、trajectory 全体が安全であることは従わない。
SFT は single-step correctness と trajectory-level safety を分ける。

## 10. Dissipation と Control

review、CI、type checker、architecture rules、theorem boundary checker は、raw force を
拒否、射影、減衰、修正する control / dissipation field である。

```text
raw operation support / policy
  -> review / CI / type / policy
  -> accepted operation support / policy
```

`Dissipation` は、force が intended feature へ使われず、obstruction、ambiguity、coupling、
coordination cost へ流れる現象でもある。

```text
Dissipation :=
  feature force lost to obstruction
  + ambiguity growth
  + coupling growth
  + review / CI rejection
  + runtime incident pressure
```

damping が十分なら bad-axis measure は非増加または減少する、という形の主張は明示前提を必要とする。
operation が accepted されたという事実だけから bad-axis nonincrease は従わない。

力学として扱う場合、control は field endomorphism または filter として読む。

```text
control R : FieldSpace -> FieldSpace

support-restricting control:
  U(R(F)) ⊆ U(F)

boundary-preserving control:
  SupportOperationsPreserveSafeRegion(U, O, B)
    -> SupportOperationsPreserveSafeRegion(U_R, O, B)
  where U_R(F) := U(R(F))
```

dissipation record は、raw support / proposal が accepted、rejected、delayed、unresolved へ
どう分配されたかを記録する。
これは保存則ではなく、明示された partition / accounting boundary の下での記録である。

```text
DissipationAccounting :=
  raw proposal universe
  + accepted / rejected / delayed / unresolved classes
  + overlap policy
  + coverage proof or coverage boundary
  + unaccounted remainder
```

## 11. Field Update

SFT は予報だけでなく、予報と観測の差分で field model を更新する closed-loop theory である。

```text
FieldUpdate :=
  prior field
  + forecast cone
  + observed PR signature delta
  + unexpected obstruction witnesses
  + review / CI outcome
  + runtime feedback
  -> posterior field
```

incident 後の postmortem は、field update の重要な特殊形である。

```text
PostmortemUpdate :=
  incident observation
  + root-cause witness classification
  + missing invariant discovery
  + review / CI filter update
  + runtime observation update
  + forecast boundary revision
```

基本ループは次である。

```text
forecast
  -> transition
  -> observation
  -> update
  -> next forecast
```

`FieldUpdate` は、過去の forecast が外れた理由を消去しない。
forecast boundary、missing evidence、unexpected witness、organization / review policy drift を
posterior field の一部として残す。

field update を theorem schema として扱う場合は、posterior が prior より何を精緻化したかを
preorder として明示する。

```text
FieldRefinement(F_post, F_prior)
  = F_post preserves recorded forecast errors
  + F_post records added evidence
  + F_post refines selected support / policy / observation boundary
  + F_post keeps non-conclusions or explicitly discharges them

UpdateSound(update)
  = observed delta / unexpected witness / review outcome
    are recorded in the posterior field
```

自動的な予測精度向上はここから従わない。
従うのは、指定された update rule の下で loss / correction record が posterior に保存されることだけである。

## 12. Attractor Engineering

attractor は、反復操作により trajectory が滞留しやすい signature 領域である。
basin は、その attractor へ落ちやすい初期 configuration の集合である。

```text
Attractor :=
  recurrent signature region
  + stability condition
  + observation boundary

Basin :=
  initial configurations that reach the attractor region
```

bounded reachability として読む場合、basin は horizon と support に相対化される。

```text
Reach_h(F, U, A)
  = field F から support U を用いて h step 以内に region A へ到達可能

Basin_h(A)
  = { F | Reach_h(F, U_F, A) }

ProbabilisticBasin_{h,p}(A)
  = { F | Pr[reach A within h] >= p }
```

確率付き basin は追加 semantics であり、集合論的 core では `Reach_h` と `Basin_h` を使う。

Attractor Engineering は、悪い operation を外から止めるだけではなく、
良い operation が自然に選ばれやすい field を作る制御である。

```text
support shaping :=
  remove bad operation
  + add good operation
  + make lawful path easier
  + make unlawful shortcut harder
```

refactoring は、その時点の構造整理だけでなく、未来の operation support / policy を変える
field transformation として読む。

## 13. Organization Field

開発組織は architecture state に force を注入する multi-agent field として読む。

```text
Demand field
  -> Requirement field
  -> Design field
  -> Agent / developer operation field
  -> Review / CI dissipation field
  -> Architecture Signature trajectory
```

| field | 発生源 | SFT 上の作用 |
| --- | --- | --- |
| demand field | PdM、顧客価値、KPI、ロードマップ | feature force の方向と頻度を決める。 |
| requirement field | PO、要件、acceptance criteria、優先順位 | operation script の粒度、順序、局所性を変える。 |
| design field | architect、境界、canonical pattern、非目標 | future PR force の流路を作り、bad force を局所化する。 |
| operation field | developer、AI agent、automation | 実際の architecture transition を生成する。 |
| dissipation field | review、CI、type checker、architecture rules | raw force を減衰、射影、拒否、修正する。 |
| observation field | Signature、Feature Extension Report、drift ledger | trajectory を観測し、制御入力へ戻す。 |

組織判断そのものを Lean theorem 化しない。
組織判断が architecture transition support / policy に与える作用を観測対象にする。
SFT は人間の意図や組織文化そのものを完全モデル化しない。
組織上の意思決定は、operation support、constraints、filters、observed signature trajectory に
現れた範囲で扱う。

## 14. AI-driven Development

AI agent は、field の上で operation を生成する制御対象 / 操作生成器である。

```text
AI agent operation :=
  proposal support / policy
  + prompt / policy boundary
  + allowed operation support
  + theorem boundary
  + review / CI feedback
```

AI の安全性は、生成速度ではなく operation support と feedback control の問題として扱う。
AI agent が提案する operation が、AAT の theorem boundary と SFT の forecast / control boundary の中に
留まるかを観測する。
SFT は AI agent の一般的安全性を証明しない。
AI agent が生成する operation support を bound し、観測し、review / CI feedback で制御する枠組みを与える。

## 15. Lifecycle と End of Life

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

End-of-life は失敗ではなく、field control の一種である。
修復コスト、migration path、runtime risk、organization damping capacity、forecast cone の広がりを見て、
repair、migration、deletion のどれを選ぶかを扱う。

## 16. SFT Simulator

SFT が比喩を越えて力学として成立しているかは、
bounded simulator を構成できるかで検査できる。
シミュレーターは未来の PR を一点予測するものではなく、
PRD や Spec が field に注入する force を forecast cone として展開する。

```text
PRD-to-ForecastCone simulator :=
  input PRD
  + current field state
  + force class classifier
  + operation support templates
  + obstruction witness templates
  + field transition / projection model
  + forecast boundary
  -> reachable path classes
   + expected signature delta range
   + likely obstruction witnesses
   + missing invariant / boundary report
   + unknown / unmodeled remainder
```

これは `PRD-to-PR predictor` ではない。
SFT の simulator は、点予測ではなく台風の予報円のような reachable region / distribution を返す。
確率や重みは optional semantics であり、historical prior と calibration boundary がない限り
empirical prediction とは呼ばない。

```text
structural forecast:
  reachable path classes
  + selected obstruction families
  + cone-narrowing constraints

weighted forecast:
  structural forecast
  + ordinal weights or probabilities
  + unknown / unmodeled remainder

calibrated forecast:
  weighted forecast
  + historical prior
  + prediction-vs-actual calibration record
```

シミュレーターの成熟度は段階的に分ける。

| level | 読み | 最小出力 |
| --- | --- | --- |
| 0 | explanatory metaphor | force / basin という説明だけ。 |
| 1 | force classification | PRD force class。 |
| 2 | support generation | candidate operation support。 |
| 3 | cone generation | bounded forecast cone / path classes。 |
| 4 | signature estimation | expected signature delta / obstruction witnesses。 |
| 5 | weighting | path class weight / probability / unknown remainder。 |
| 6 | calibration | actual Issue / PR / review / CI outcome との照合と field update。 |

SFT が力学として成立する最低ラインは level 3 である。
実務ツールとしての価値は level 4 から強くなり、予測理論としての主張は level 5 以降、
科学的な検証可能性は level 6 の calibration に依存する。

PRD force class は cone の形を変える。

```text
feature addition:
  extension / integration / policy insertion paths
  + hidden interaction / boundary / semantic risk

feature deletion:
  contraction / dependency removal / consumer migration paths
  + compatibility / orphan dependency / runtime consumer risk

migration:
  bridge / dual-run / replacement / rollback paths
  + old-new projection mismatch / partial migration risk

incident response:
  guard / fallback / protection / observation update paths
  + complexity transfer / missing law universe risk
```

初期 MVP は、確率分布を急がず、force class、candidate operation support、
forecast cone、expected signature delta range、missing invariant / boundary を返す。
`unknown / unmodeled` を明示することは、SFT の forecast boundary の一部である。

### Natural-language Force Extraction

PRD や設計メモは自然言語 artifact であり、そのままでは SFT の formal input ではない。
そのため simulator 実装では、自然言語 artifact を `ForceVector` 候補へ変換する
extraction layer が必要になる。
この extraction layer は、人間の設計レビュー、rule-based parser、LLM、
またはそれらの hybrid として実装できる。
LLM は実装選択肢の一つであり、SFT の数学的構成要素や theorem engine ではない。

自然言語 PRD、設計メモ、過去 Issue / PR から、structured force vector candidate を
抽出する front-end として tooling を使う場合、流れは次の形になる。

```text
PRD text
  + repo context
  + architecture signature
  + historical Issue / PR memory
  -> ForceExtractor
  -> ForceVector candidates
  -> schema / boundary validation
  -> SFT ForecastCone simulator
```

extractor が担うのは、自然言語 artifact を SFT の入力へ写す前処理である。

```text
ForceExtractor :=
  force class candidates
  + target field region candidates
  + operation support candidates
  + expected signature delta candidates
  + obstruction witness candidates
  + missing invariant / boundary candidates
  + uncertainty boundary
```

`ForceVector` は dense embedding だけではなく、SFT が読める構造化成分を持つ。

```text
ForceVector :=
  force class weights
  + target region weights
  + operation family weights
  + obstruction axis weights
  + missing invariant set
  + unknown / unmodeled remainder
```

LLM confidence は calibration 済み確率ではない。
初期段階では ordinal weight または candidate score として扱い、
actual Issue / PR / review / CI outcome と照合して初めて calibrated forecast に近づく。

```text
LLM confidence
  != calibrated probability

CalibratedForceVector :=
  ExtractedForceVector
  + historical prior
  + prediction-vs-actual calibration record
```

tooling を使う場合は、抽出境界を必ず記録する。

```text
ForceExtractionBoundary :=
  extractor type / version
  + prompt version, if applicable
  + model version, if applicable
  + retrieved context boundary
  + unavailable private evidence
  + unsupported inference list
  + non-conclusions
```

したがって、extracted output から path safety、global risk reduction、
causal force identification は従わない。
extractor は候補を出し、SFT は support / cone / boundary を管理し、
AAT / ArchSig は signature / witness / invariant を管理する。

## 17. ArchSig の位置づけ

ArchSig は、AAT 的観測量を抽出し、SFT 的予測・制御に渡す計測層である。
AAT / SFT / ArchSig の claim boundary は [AAT / SFT Interface](aat_interface.md) に従う。

```text
ArchSig :=
  AAT signature / witness / theorem-boundary extractor
  + SFT force / forecast / trajectory analyzer
```

AAT 側:

```text
codebase / PR
  -> component universe
  -> signature axes
  -> obstruction witnesses
  -> theorem boundary status
  -> non-conclusions
```

SFT 側:

```text
PRD / Spec / Issue / PR / Review / Incident
  -> force analysis
  -> forecast cone
  -> expected signature delta
  -> obstruction risk distribution
  -> force-shaping recommendation
  -> feedback update
```

ArchSig は、PR 後に危険を見る tool から、PRD 時点で architecture trajectory を予報する
tool へ拡張される。
ただし、claim level は段階的に分ける。

```text
Stage 1:
  PR / codebase から AAT signature と obstruction witness を抽出する

Stage 2:
  PR before / after から signature delta を測る

Stage 3:
  Issue / Spec から expected operation support を推定する

Stage 4:
  PRD から forecast boundary と missing invariant を構成する

Stage 5:
  historical prior と calibration がある範囲で forecast cone を推定する
```

初期 MVP は、未来予測そのものよりも、signature diff、selected obstruction witness report、
theorem boundary / non-conclusions report、missing invariant / missing boundary detector に置く。
PRD forecast は、calibration と dataset boundary がない限り empirical prediction として扱わない。

## 18. 非目標

SFT は次を主張しない。

```text
forecast cone が未来を決定する。
same signature から same future operation support が従う。
safe endpoint から safe trajectory が従う。
accepted step から bad-axis nonincrease が無条件に従う。
organization policy から incident reduction が Lean theorem として従う。
AI agent policy から architecture lawfulness が無条件に従う。
empirical correlation が因果証明である。
observed signature delta から causal force が一意に同定できる。
human intention や market success を予測できる。
ArchSig extraction が ground truth architecture object である。
```

SFT の役割は、AAT の局所代数を観測量と制約として使い、ソフトウェア進化の大域的な場を
予測・制御・検証可能な研究対象へ分解することである。
