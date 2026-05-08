# Software Field Theory ソフトウェアの場の理論

SFT は、ソフトウェア進化を場の力学として扱う理論である。
AAT はソフトウェアアーキテクチャの局所代数として独立に成立し、
SFT はその局所代数を state space、observable coordinate、local law として使う。

```text
SFT studies software evolution as:

software field
  + artifact-induced forces
  + operation distributions
  + signature trajectories
  + dissipation
  + feedback control
```

SFT の主題は、要求、仕様、Issue、PR、組織、AI、運用が architecture state に加える
force、誘導する trajectory、散逸する obstruction、制御に使われる feedback である。
ここでいう field はコードベースに限らない。
PdM、PO、アーキテクト、エンジニア、AI agent、レビュー、CI/CD、運用 feedback を含む
開発組織全体が、operation distribution と signature trajectory を形作る。

直感的には、曖昧な coupon PRD は checkout と payment へ feature force をかける。
このとき `DiscountPolicy`、丸め規則、payment state boundary が仕様にないなら、
forecast cone は `PaymentAdapter -> CouponRepository` のような危険な trajectory を含みうる。
仕様がそれらの境界と不変量を明示すれば、cone は狭まり、operation distribution は
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
  P_t  : operation policy / preference
  C_t  : constraint environment
  O_t  : observation model
  R_t  : review / CI / control filter
  E_t  : exogenous artifact inputs
```

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

同じ `ArchitectureObject` でも、field が異なれば次の operation distribution は異なる。
同じ module graph でも、レビュー規則、所有境界、既存 canonical pattern、テスト粒度、
AI prompt、incident history が違えば、将来選ばれやすい操作は変わる。

```text
field_t
  -> operation distribution_t
  -> accepted / rejected transitions
  -> signature_t+1
  -> field_t+1
```

この式は決定論ではない。SFT が扱うのは、field が operation distribution と signature trajectory を
どのように形作るかである。

## 3. Force

`Force` は、field 上の operation distribution を偏らせる作用である。
要求、仕様、Issue、PR、レビュー、CI、incident、組織判断、AI prompt は、すべて force の発生源になりうる。

最小 semantics では、force は operation support を変える写像として読む。

```text
force : OperationSupport -> OperationSupport
```

たとえば spec clause は unsafe operation を除外し、Issue 分割は support を局所化し、
review policy は accepted support を filter する。
確率的 semantics を採用する場合は、force を分布や preference を変える作用として読む。

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
repair force
coupling force
boundary force
invariant force
effect force
debt force
refactor force
deletion force
```

良い artifact は、feature force と stabilizing force を同時に持つ。
悪い artifact は、feature force を出しながら、hidden interaction、ambiguity、coupling、
effect leakage へ力を散らす。

## 4. Force Taxonomy

SFT では force を観測可能性と artifact の役割で分ける。

| force class | 読み | 主な evidence |
| --- | --- | --- |
| `ObservedForce` | accepted transition の before / after signature delta として観測できる force。 | PR before / after signature、drift ledger、Feature Extension Report。 |
| `LatentForce` | 要求、設計、prompt、組織判断、既存 local grammar が operation distribution に与える見えない作用。 | requirement metadata、design boundary、prompt / agent policy、PR proposal distribution、case study。 |
| `DissipatedForce` | review / CI / type / policy により拒否、修正、減衰された raw force。 | rejected PR、CI failure、review-requested changes、policy decision report。 |

AAT に近いのは accepted transition と selected signature delta である。
latent force と dissipated force は、原則として tooling / empirical dataset で推定する。

artifact の粒度では、次の下位型を区別する。

```text
RequirementForce :=
  feature direction
  + value pressure
  + ambiguity boundary

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

## 5. Operation Distribution

`OperationDistribution` は、ある field で次に選ばれうる operation の分布または support である。

```text
OperationDistribution(field) :=
  operation support
  + likelihood / preference
  + admissibility boundary
  + review / CI filter
  + agent / developer policy
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

`ForecastCone` は、現在の field と artifact force から到達しうる architecture path の集合または分布である。
最小 core では、horizon `h` と operation support `U` に相対化された reachable path set として読む。

```text
ForecastCone(F, U, h) :=
  paths reachable from field F
  using operations in support U
  within horizon h
```

分布付き forecast cone は、この path set に probability / preference / cost を載せた拡張である。

```text
ForecastCone(field, force) :=
  possible ArchitecturePath distribution
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

```text
U2 ⊆ U1
  -> ForecastCone(F, U2, h) ⊆ ForecastCone(F, U1, h)
```

selected witness family に関する narrowing は、global risk reduction ではない。
ある witness family を除外しても、別の witness family へ complexity が転送されることがある。

これは SFT の看板原理である。
良い PRD / Spec / Issue は、単に作業を増やす artifact ではなく、
将来の architecture trajectory の cone を狭める force-shaping artifact である。

### 8.2 Support Safety Principle

operation support が selected safe region の中に閉じており、review / CI filter がその境界を
保持するなら、accepted transition はその boundary に相対化された unsafe operation を含まない。

```text
operation support within safe region
  + boundary-preserving filter
  -> accepted support excludes selected unsafe operations
```

ただし、support safety から trajectory safety 全体は従わない。
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
  raw proposal support / distribution
  + accepted support / distribution
  + rejected operation log
  + unresolved demand
  + coordination / ambiguity record
  + runtime pressure estimate
```

SFT は、dissipation を単なる失敗ではなく、force がどの軸へ移ったかを追跡する対象として扱う。

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
raw operation distribution
  -> review / CI / type / policy
  -> accepted operation distribution
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

Attractor Engineering は、悪い operation を外から止めるだけではなく、
良い operation が自然に選ばれやすい field を作る制御である。

```text
support shaping :=
  remove bad operation
  + add good operation
  + make lawful path easier
  + make unlawful shortcut harder
```

refactoring は、その時点の構造整理だけでなく、未来の operation distribution を変える
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
組織判断が architecture transition distribution に与える作用を観測対象にする。
SFT は人間の意図や組織文化そのものを完全モデル化しない。
組織上の意思決定は、operation support、constraints、filters、observed signature trajectory に
現れた範囲で扱う。

## 14. AI-driven Development

AI agent は、field の上で operation を生成する制御対象 / 操作生成器である。

```text
AI agent operation :=
  proposal distribution
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

## 16. ArchSig の位置づけ

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

## 17. 非目標

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
