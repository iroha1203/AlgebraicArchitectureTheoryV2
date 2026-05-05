# Architecture Signature Dynamics 設計

Lean status: `defined only` / `future proof obligation` / `empirical hypothesis`.

この文書は、AAT の既存語彙の上にカオスゲーム的ソフトウェア進化を建築し、
システム開発全体を場の力学として扱うための設計を固定する。目的は、
`ArchitectureEvolution` と `ArchitectureSignature` を土台に、反復変更、PR force、
operation distribution、attractor / basin、dissipation、control input、organizational
force field を一つの Architecture Signature Dynamics として整理することである。

この文書は `docs/memo/aat_chaos_game_dynamics.md` の研究メモを、現在の AAT v2 の
語彙へ接続する設計メモである。ここでの狙いは、カオスゲーム理論を単なる比喩として
借りることではない。AAT が持つ状態、操作、不変量、obstruction、Signature、proof
obligation、measurement boundary の上に反復写像系を載せることで、コード、PR、AI agent、
review、CI、要求、要件、設計、組織判断を同じ場の力学として扱う理論を作る。

## AAT の立場

AAT は「何が正しい設計か」を直接決める理論ではない。

AAT は、ある設計、分割、operation、review policy、CI policy、prompt、組織判断を選んだとき、
どの invariant が保存され、どの obstruction が現れ、どの Architecture Signature axis が
変化し、どの future operation distribution が誘導されるかを扱う。

したがって、Architecture Signature Dynamics は正しさの理論ではなく、構造的帰結の理論である。
AAT は未来を選ばない。AAT は、選択が未来の architecture transition をどう曲げるかを観測する。

## 大きな主張

AAT は static architecture diagnosis だけでは完結しない。AAT がカオスゲーム理論を
取り込むことで、architecture は「現在の構造」から「未来の変更分布を曲げる場」へ拡張される。
この拡張により、AAT はソフトウェア部品の代数だけでなく、システム開発全体の力学を扱う理論になる。

中心命題は次である。

```text
software development =
  repeated architecture-changing operations
  under a field induced by codebase, requirements, agents, review, CI, and organization

software quality =
  stability and direction of the induced Architecture Signature trajectory
```

この見方では、コード品質は snapshot の静的な良し悪しだけではない。コードベースは未来の
patch distribution を誘導する場であり、PR はその場に加えられる force であり、review / CI /
type system は force を減衰・射影・拒否する dissipation system である。PdM、PO、
architect は、要求、要件、設計境界を通じて operation distribution を変える indirect force を
注入する。

したがって、AAT の対象は次のように広がる。

```text
code structure
  -> architecture operation
  -> PR force
  -> signature trajectory
  -> development field
  -> AI-driven / organization-driven software evolution
```

この拡張の価値は三つある。

- 開発全体を、状態空間、操作族、観測、反復、制御入力、散逸系からなる場の力学として説明できる。
- AI 駆動開発を、単なる生成速度の向上ではなく、operation distribution shift として仮説化できる。
- PR force、trajectory stability、dissipation capacity、basin fragility などの定量指標を導ける。

## Core Thesis

Architecture Signature Dynamics の中心仮説は、architecture state が future operation
distribution を誘導し、その operation distribution の反復が signature trajectory を形成し、
review / CI / type / design policy がその trajectory を制御する、という閉ループである。

```text
current architecture field
  -> operation distribution
  -> accepted / rejected transitions
  -> signature trajectory
  -> future architecture field
```

この閉ループが AAT Dynamics の重力中心である。PR force、dissipation、attractor / basin、
AI patch distribution、organizational force field は、すべてこの閉ループの部品として読む。

特に重要なのは `codebase as field` である。AI agent や開発者は、真空中で patch を生成しない。
既存コード、命名、責務境界、canonical example、テスト粒度、レビュー規則、CI、要件文脈が、
どの operation を自然に選びやすいかを変える。したがって、architecture は単なる構造ではなく、
未来の operation distribution を曲げる場である。

この場は、変更後の architecture によって再び更新される。

```text
C_t
  -> P(operation | C_t, control_t)
  -> C_{t+1}
  -> P(operation | C_{t+1}, control_{t+1})
```

ここで `control_t` は prompt、review policy、CI policy、type system、architecture rule、
requirements、design boundary、organization policy を含む。AAT はこれらの control input
そのものを自然言語として完全形式化するのではなく、それらが architecture transition
distribution に与える作用を観測対象にする。

## 中心設計

Architecture Signature Dynamics の最小核は次である。

```text
architecture state
  -> architecture operation / transition
  -> architecture evolution path
  -> signature observation
  -> signed signature delta
  -> signature trajectory
```

AAT 既存語彙では、これは次の対応になる。

| Dynamics 側 | AAT 側 |
| --- | --- |
| state space | `State` parameter, finite `ComponentUniverse`, `ArchitectureLawModel` |
| primitive step | `ArchitectureTransition`, `ArchitectureOperation` |
| repeated step | `ArchitectureEvolution`, `ArchitecturePath` |
| observation | `ArchitectureSignatureV1`, `AnalyticRepresentation` |
| force | before / after signature の signed delta |
| trajectory | evolution path に沿った signature sequence |
| safe region | selected invariant / selected required axes zero / policy-specified region |
| drift | selected signature axis または witness profile の悪化方向 delta |
| damping | review / CI / type / policy による accepted-step predicate または projection |
| attractor candidate | finite observed trajectory が滞留する selected signature region |
| basin candidate | selected initial states が同じ attractor candidate へ到達する領域 |

重要なのは、カオスゲーム理論を直接 `AI` や `PR` の話として始めないことである。
AAT 上ではまず、有限または bounded な状態空間、操作列、観測写像、観測値の差分を作る。
その上で、操作選択分布を入れたものを stochastic patch dynamics として扱う。

ただし、最終的な射程は Lean core に閉じない。Lean core は、場の力学を支える骨格である。
その外側に tooling、dataset、simulation、case study を置くことで、AI agent や開発組織までを
同じ理論の上で測定・比較・制御する。

## Force Taxonomy

`force` は一つの概念に見えるが、AAT Dynamics では観測可能性に応じて三層に分ける。

| force class | 定義方向 | 主な evidence |
| --- | --- | --- |
| `ObservedForce` | 実際に accepted された transition の before / after signature delta。 | PR before / after Signature、drift ledger、Feature Extension Report。 |
| `LatentForce` | 要求、設計、prompt、組織判断、既存 local grammar が operation distribution に与える見えない作用。 | requirement metadata、design boundary、prompt / agent policy、PR proposal distribution、case study。 |
| `DissipatedForce` | review / CI / type / policy によって拒否、修正、減衰された raw force。 | rejected PR、CI failure、review-requested changes、policy decision report。 |

この分解により、PR force は測定可能な `ObservedForce`、design field や requirement field は
推定対象の `LatentForce`、review / CI / policy は `DissipatedForce` として扱える。
AAT の theorem は主に observed transition と accepted-step predicate を扱い、latent force と
dissipated force は tooling / empirical dataset で推定する。

## Development Field Dynamics

Architecture Signature Dynamics では、開発組織を architecture state に force を注入する
multi-agent field として読む。

```text
Demand field
  -> Requirement field
  -> Design field
  -> Agent / developer operation field
  -> Review / CI dissipation field
  -> Architecture Signature trajectory
```

各場の意味は次である。

| field | 発生源 | AAT 上の作用 |
| --- | --- | --- |
| demand field | PdM、顧客価値、KPI、ロードマップ | feature force の方向と頻度を決める。 |
| requirement field | PO、要件、acceptance criteria、優先順位 | operation script の粒度、順序、局所性を変える。 |
| design field | architect、境界、canonical pattern、非目標 | future PR force の流路を作り、bad force を局所化する。 |
| operation field | developer、AI agent、automation | 実際の architecture transition を生成する。 |
| dissipation field | review、CI、type checker、architecture rules | raw force を減衰、射影、拒否、修正する。 |
| observation field | Signature、Feature Extension Report、drift ledger | trajectory を観測し、制御入力へ戻す。 |

これらは architecture の外側にあるノイズではない。AAT は組織判断そのものを完全形式化する
理論ではないが、組織判断が architecture transition distribution に与える作用を観測対象にする。
この節度を保つことで、AAT はコード構造だけでなく開発系全体を扱いながら、測定可能性を失わない。

この構成では、開発は単なる作業列ではなく feedback system である。

```text
observe trajectory
  -> adjust policy / prompt / design / requirement
  -> change operation distribution
  -> change future trajectory
```

AAT はこの feedback system に、証明可能な核と測定可能な軸を与える。

## 層分け

### Layer 1: Formal dynamics kernel

Lean core に置ける最小層である。ここでは AI、GitHub、組織、レビュー遅延は扱わない。

候補 schema:

```text
SignatureObservation State Sig =
  observe : State -> Sig

SignatureTrajectory plan =
  states and observed signatures along an ArchitectureEvolution

SignatureForce Sig Delta =
  delta : Sig -> Sig -> Delta

NetSignatureForce =
  fold / sum of per-step deltas
```

この層で欲しい theorem:

| theorem 候補 | 読み |
| --- | --- |
| endpoint observation theorem | trajectory の最後の観測は evolution target の signature である。 |
| telescoping theorem | additive signature vector では、各 step delta の和が initial と final の差に一致する。 |
| invariant-closed trajectory theorem | safe region が全 step で閉じていれば、trajectory は safe region から出ない。 |
| accepted-step preservation theorem | accepted step predicate が selected invariant preservation を含むなら、accepted evolution は invariant を保存する。 |
| finite eventual periodicity | 有限状態空間上の deterministic self-map 反復は eventually periodic になる。 |
| commutative merge-order theorem | 2 step が観測上可換なら merge order sensitivity は 0 になる。 |
| non-commutativity counterexample | local step がそれぞれ lawful でも、順序により final signature が変わりうる。 |

この層の non-conclusions:

- AI patch 分布を結論しない。
- 実 PR の品質、incident、review cost との相関を結論しない。
- `ArchitectureSignature` を単一スコアとして読まない。
- unmeasured axis を measured zero と読まない。
- local correctness から global invariant preservation を自動導出しない。

### Layer 2: Deterministic dynamics over selected operations

次に、操作族を固定して反復写像として読む。

```text
F : State -> State
sigma : State -> Signature
trajectory t = sigma (F^t X0)
```

または、操作族を持つ。

```text
op : OperationId -> State -> State
script : List OperationId
```

この層ではカオスゲームの「複数写像の反復」を、AAT の operation family として読む。
確率はまだ入れない。Lean では finite operation script や bounded path を対象にし、
`ArchitecturePath` / `ArchitectureEvolution` と接続する。

主な概念:

| 概念 | 設計上の扱い |
| --- | --- |
| operation family | selected `ArchitectureOperationKind` または concrete operation script。 |
| repeated operation | `ArchitectureEvolution` として表す。 |
| signature trajectory | `observe` を path に沿って map したもの。 |
| attractor candidate | finite trajectory 上で再訪問または滞留する selected region。 |
| basin candidate | finite initial-state list に相対化した到達分類。 |
| escape cost | bad region から safe region へ出る selected repair / refactor script の長さまたは重み。 |

ここでの attractor / basin は、無限位相空間上の強い定理ではなく、
有限 simulation universe や selected state list に相対化した候補として扱う。
これは守りではなく、理論を測定可能に保つための足場である。`attractor`、`basin`、
`Lyapunov-like` は、少なくとも初期段階では `finite observed trajectory`、
`selected region`、`bounded operation script` に相対化して定義する。

### Layer 3: Stochastic patch dynamics

ここで operation distribution を導入する。

```text
P(operation | current architecture context, prompt, agent policy, review policy)
```

AAT では、これは theorem ではなく empirical / simulation layer の入力である。
ただし、抽象 schema としては次のように切れる。

```text
OperationDistribution State Op =
  support : State -> List Op
  weight : State -> Op -> Weight
```

Lean 化する場合も、初期段階では確率測度の一般論ではなく、
有限 support と重み、または nondeterministic transition relation から始めるのがよい。
AI patch 分布そのものは dataset / simulation / tooling で推定する。

この層で扱う仮説:

| 仮説 | status |
| --- | --- |
| AI は operation selection distribution を変える | `empirical hypothesis` |
| codebase as prompt は future patch distribution を誘導する | `empirical hypothesis` |
| canonical example は seed attractor として働く | `empirical hypothesis` |
| review / CI は bad force を減衰する | Lean では accepted predicate、実効容量は empirical |
| throughput が dissipation capacity を超えると drift が増える | `empirical hypothesis` |

AI 駆動開発に関する中心仮説は、AI がコードを書くこと自体ではなく、現在の architecture
context に条件づけられた operation distribution を変えることである。

```text
P_human(operation | C_t, requirement, organization)
P_AI(operation | C_t, prompt, agent policy, context window, review policy)
```

この差分が、AI-driven architecture dynamics の主対象である。AI が強いほど必ず良い
trajectory になるのではなく、AI が参加する場の design field と dissipation field が
十分に強いとき、AI は良い attractor を増幅しうる。逆に、場が悪い場合、AI は既存の
bad local grammar を高頻度で再生産し、debt basin を深くしうる。

したがって、AAT が立てる AI 駆動開発の問いは次になる。

- この codebase は AI patch distribution をどの basin へ誘導するか。
- prompt / review / CI / architecture rule は operation distribution をどれだけ変えるか。
- AI throughput は dissipation capacity を超えていないか。
- AI agent team の merge order sensitivity はどれだけ高いか。
- canonical examples は seed attractor として良い force を生んでいるか。

### Layer 4: PR Force Model

PR は AAT 上では、状態遷移と観測差分の組である。

```text
PRForce(PR) =
  sigma(after(PR)) - sigma(before(PR))
```

既存 dataset では `EmpiricalSignatureDatasetV0.deltaSignatureSigned` がこの入口になる。
PR history dataset、Feature Extension Report、outcome linkage dataset は、
PR force と review / incident / rollback / repair outcome を join する empirical input である。

PR Force Model の設計境界:

| 項目 | 扱い |
| --- | --- |
| per-axis signed delta | dataset / tooling schema、将来 Lean の generic delta theorem と接続。 |
| observed force | accepted PR の before / after signature delta として測る。 |
| latent force | requirement / design / prompt / codebase field が operation distribution へ与えた作用として推定する。 |
| dissipated force | rejected / modified / CI-failed raw force と accepted force の差分として扱う。 |
| force decomposition | feature / repair / coupling / boundary / type / test / debt は report 上の分類候補。 |
| net force | 一定期間の signed delta の集計。telescoping 可能な軸では formal theorem 候補。 |
| projection / damping | policy accepted predicate、review required predicate、CI decision report として扱う。 |
| debt force | selected bad-signature region へ近づく delta として定義する。単一スコア化しない。 |

注意点として、PR force は物理的な力ではなく、AAT の観測空間上の signed delta である。
この定義により、比喩ではなく測定可能な対象になる。

### Layer 5: Organizational force field

PdM、PO、architect、review policy、CI policy は、operation distribution または
accepted-step predicate を変える外部入力として扱う。

```text
upstream decision
  -> operation distribution / script selection
  -> PR force distribution
  -> signature trajectory
```

これは AAT の射程の外側ではなく、AAT を開発系の数学へ拡張する中心部分である。
AAT は組織判断そのものを形式化するのではない。組織判断が architecture transition
distribution に与える作用を観測対象にする。要求品質、要件分割、設計境界、review latency、
CI feedback delay は socio-technical variable であり、dataset と case study によって測定する。

組織判断は、コードに直接現れないから重要でないのではない。むしろ、後続する多数の PR の
operation distribution を曲げるため、高い leverage を持つ。AAT ではこれを
`IndirectForceLeverage` や `DesignFieldStrength` のような指標に落とす。

## カオスゲーム理論との接続

カオスゲーム理論側の基本形を、AAT では次のように読む。

```text
X_{t+1} = f_{i_t}(X_t)
i_t ~ P(. | X_t, control_t)
Y_t = sigma(X_t)
```

対応:

| カオスゲーム側 | AAT 側 |
| --- | --- |
| `X_t` | architecture state |
| `f_i` | architecture operation / transition |
| `i_t` | selected operation / PR / patch |
| operation probability | AI / developer / review / CI による operation distribution |
| `Y_t` | Architecture Signature observation |
| attractor | selected signature region or recurrent state set |
| basin | selected initial states that reach the region |
| Lyapunov-like sensitivity | 近い初期状態または近い operation script の signature distance amplification |
| control input | prompt, review policy, CI, type checker, architecture rules |

この接続の設計方針:

- AAT core は、状態、操作、観測、不変量、証明境界を与える。
- Dynamics layer は、操作の反復と signature trajectory を扱う。
- Stochastic layer は、operation distribution を扱うが、まず有限 support に限定する。
- Empirical layer は、AI patch、PR、review、incident、組織判断を観測する。

## 定量指標の導出

Architecture Signature Dynamics から導くべき指標は、現在値の metric だけではない。
重要なのは、未来変更に対する場の性質を測ることである。

### Signature trajectory metrics

| 指標 | 定義方向 | 意味 |
| --- | --- | --- |
| `TrajectoryDriftRate` | 時間または PR 数あたりの bad-axis signed delta | architecture が悪い signature 領域へ流れる速度。 |
| `TrajectoryStability` | selected safe region からの逸脱頻度と復帰時間 | 小変更後に良い領域へ戻る力。 |
| `InvariantDecayRate` | selected invariant violation の増加率 | local correctness 反復による global invariant 劣化。 |
| `SignatureVolatility` | delta vector の分散または振幅 | trajectory が安定か散乱しているか。 |
| `PhaseShiftSignal` | ある PR 前後での delta norm / axis jump | sudden phase shift の検出候補。 |

### PR force metrics

| 指標 | 定義方向 | 意味 |
| --- | --- | --- |
| `PRForceVector` | before / after signature の signed delta | PR が signature 空間へ加える多軸 force。 |
| `ObservedForce` | accepted transition の signed signature delta | 実際に architecture field を更新した測定可能な force。 |
| `LatentForceEstimate` | proposal distribution / requirement / design metadata からの推定 | acceptance 前に場へかかっていた見えない force。 |
| `DissipatedForceEstimate` | rejected / modified raw force と accepted force の差分 | review / CI / policy がどれだけ force を削ったか。 |
| `NetPRForce` | window 内の PR force 集計 | 一定期間の開発がどの方向へ architecture を押したか。 |
| `DebtForceAccumulation` | bad region へ近づく小 delta の累積 | 小さな負債 force の長期蓄積。 |
| `StabilizingForceRatio` | feature force に対する repair / test / boundary 改善 force | 機能追加が安定化を伴っているか。 |
| `MergeOrderSensitivity` | PR 適用順序による final signature 差 | 並列 PR / AI agent team の干渉度。 |

### Field and control metrics

| 指標 | 定義方向 | 意味 |
| --- | --- | --- |
| `DissipationCapacity` | review / CI / type / policy が bad force を減衰した量 | raw patch 流量を受け止める能力。 |
| `ConstraintSaturation` | raw PR throughput と dissipation capacity の比 | 制約系が飽和しているか。 |
| `FeedbackDelayInstability` | patch 生成から feedback までの遅延と drift の関係 | 遅い feedback が不安定化を増やす度合い。 |
| `DesignFieldStrength` | boundary / canonical pattern / non-goal が PR force を整流する度合い | architecture design が future patch を導く力。 |
| `IndirectForceLeverage` | 上流判断が後続 PR force 分布へ与える影響倍率 | PdM / PO / architect 判断の波及力。 |

### AI dynamics metrics

| 指標 | 定義方向 | 意味 |
| --- | --- | --- |
| `OperationDistributionShift` | human-only と AI-assisted の operation 分布差 | AI 導入で選ばれる変更操作がどう変わるか。 |
| `AIPatchLyapunov` | 近い初期状態からの signature distance 増幅率 | AI 反復が小差を吸収するか増幅するか。 |
| `PromptBasinBias` | prompt / agent policy ごとの到達 basin 分布 | prompt がどの attractor へ誘導するか。 |
| `SeedAttractorStrength` | canonical example に類似する patch の増加度 | 良い例 / 悪い例が future patch を引き寄せる力。 |
| `AISafetyMargin` | invariant decay が始まる throughput / policy 境界 | AI patch 反復に対する余裕。 |

これらの指標は、AAT の多軸 Signature を前提にする。単一の品質スコアを作るのではなく、
trajectory、force、field、control、AI distribution の各軸を分けることで、開発系のどこが
不安定化しているかを診断する。

## 定理候補のロードマップ

### Phase D1: trajectory と force の形式核

最初に Lean 化する候補:

- `SignatureObservation`
- `SignatureTrajectory`
- `SignatureDelta`
- `NetSignatureDelta`
- endpoint / telescoping theorem
- safe-region preservation theorem

この段階では、`ArchitectureSignatureV1` に直結しすぎず、まず抽象 `Sig` と `Delta` で
証明する。その後、`ArchitectureSignatureV1Axis` ごとの `Option Nat` / dataset 側の
`Int` delta に接続する。

### Phase D2: merge order sensitivity

候補:

- two-step observation commutativity
- `MergeOrderSensitivity`
- commutative case の zero theorem
- non-commutative counterexample

これは PR 並列生成、patch interference、AI agent team 評価の形式的入口になる。

### Phase D3: finite attractor / basin candidate

候補:

- finite deterministic iteration
- recurrent state / recurrent signature region
- eventually periodic theorem
- finite basin classification schema
- safe attractor / bad attractor predicate

ここでも、強い global attractor theorem ではなく、有限 universe と selected region に
相対化する。

### Phase D4: damping / control

候補:

- accepted-step predicate
- rejected-step non-conclusion
- projection-like report semantics
- accepted evolution preserves selected invariant
- bad-axis nonincrease under explicit damping assumption

Review / CI / type checker の実効容量は empirical だが、accepted step が満たすべき
predicate は Lean theorem の前提として扱える。

### Phase D5: stochastic / empirical bridge

候補:

- finite weighted operation distribution schema
- simulation protocol
- PR force report schema
- AI patch Lyapunov-like sensitivity protocol
- Vibe coding success condition hypotheses

ここは Lean proof と tooling validation と empirical validation を混同しない。

### Phase D6: development field theory

候補:

- demand / requirement / design / operation / dissipation / observation field schema
- indirect force leverage dataset schema
- design field strength report
- organization-level damping capacity protocol
- AI agent team dynamics protocol

この段階で、AAT は個別コードベース診断から、開発組織全体の trajectory governance へ
射程を広げる。

## 既存文書との関係

| 既存文書 / API | 接続 |
| --- | --- |
| `ArchitectureEvolution` | signature trajectory の path substrate。 |
| `ArchitecturePath` | operation sequence と path theorem の generic substrate。 |
| `ArchitectureSignatureV1` | 観測空間。multi-axis diagnosis として扱う。 |
| `AnalyticRepresentation` | signature を analytic domain として読む bridge。 |
| `EmpiricalSignatureDatasetV0` | before / after signature と signed delta の dataset 入口。 |
| `PrHistoryDatasetV0` | PR force と GitHub metadata の join key。 |
| `FeatureExtensionReport` | PR force の theorem precondition / obstruction witness context。 |
| `OutcomeLinkageDatasetV0` | PR force と review / incident / rollback outcome の empirical join。 |
| `architecture-drift-ledger-v0` | 時系列 drift の tooling artifact。 |

## Non-conclusions

Architecture Signature Dynamics は、次を主張しない。

- AI が常に architecture を悪化させる、または改善する。
- Vibe coding が一般に成功する、または失敗する。
- PR force の単一スコアでコード品質を順位付けできる。
- measured signature delta が全 semantic / runtime drift を捕捉する。
- operation distribution をコードだけから完全復元できる。
- review / CI policy の存在だけで dissipation capacity が十分である。
- finite simulation 上の attractor candidate が実コードベース全体の global attractor である。
- unmeasured axis、private evidence、unsupported construct を zero と読める。

## 最初の実装単位

最初の Issue / PR として自然なのは、Lean core ではなくこの設計文書を source of truth にし、
次に小さな Lean module を作ることである。

候補 module:

```text
Formal/Arch/Evolution/SignatureDynamics.lean
```

最初の Lean API 候補:

```text
SignatureObservation
SignatureTrajectory
SignatureDelta
NetSignatureDelta
trajectory_endpoint_observation
netSignatureDelta_telescopes
trajectory_preserves_safeRegion
```

この module は `ArchitectureEvolution` と `ArchitecturePath` に依存してよいが、
AI patch distribution、GitHub PR、dataset schema には依存しない。dataset / PR Force Report は
後続の tooling / empirical layer で接続する。
