# Attractor Engineering

Lean status: `future proof obligation` / `tooling validation` / `empirical hypothesis`.

この文書は、[Architecture Signature Dynamics 設計](architecture_signature_dynamics.md) の上に
`Attractor Engineering` という設計語彙を置くためのメモである。

Attractor Engineering は、AI agent を外から harness / guardrail で押さえつける考え方ではない。
AAT + Dynamics では、architecture を future operation distribution を曲げる field と見る。
そのため設計対象は agent 単体ではなく、codebase、boundary、operation vocabulary、
canonical examples、tests、type system、review feedback、measurement boundary が作る
architecture field 全体である。

## Definition

Attractor Engineering は次のように定義する。

```text
Attractor Engineering is the bounded, measurement-aware design of
architecture fields, operation vocabularies, feedback and damping structures,
seed examples, and observation boundaries so that repeated human / AI
architecture-changing operations are more likely, more locally natural,
and lower-cost to follow trajectories toward selected safe or productive
signature regions, while bad attractor basins are made smaller, shallower,
more observable, or easier to escape.
```

日本語では次のように読む。

```text
Attractor Engineering とは、人間や AI による反復的な
architecture-changing operation が、選択された safe / productive な
signature region へ向かう軌道を自然に取りやすくなるように、
architecture field、operation vocabulary、canonical examples、
feedback / damping structure、measurement boundary を設計することである。

ただし、その主張は常に selected universe、bounded horizon、
selected signature axes、measurement boundary に相対化される。
```

ここでの「自然に」は比喩ではなく、AAT では次のような観測可能な作用として扱う。

```text
natural guidance =
  support mass を良い operation family へ寄せる
  + bad operation の local convenience を下げる
  + good operation の local discoverability / copyability を上げる
  + safe basin への return cost を下げる
  + bad basin への entry support / basin mass / boundary fragility を下げる
  + unmeasured axis を visible にする
```

短く言うと、Attractor Engineering は禁止の理論ではなく、操作分布の幾何を設計する理論である。

## Difference from Guardrails

Attractor Engineering は harness / guardrail / policy enforcement と重なる部分を持つが、
主語が異なる。

| 概念 | 主な作用 | Attractor Engineering との差分 |
| --- | --- | --- |
| guardrail | 危険な出力や操作を止める。 | guardrail は出たものを止める。Attractor Engineering はそもそも良い操作が出やすい field を作る。 |
| harness | agent を外側から囲い、評価・制限する。 | harness は wrapper である。Attractor Engineering は codebase / boundary / examples / tests / ownership が作る内在的 field を設計する。 |
| policy enforcement | rule 違反を検出・拒否する。 | policy は forbidden set を定める。Attractor Engineering は operation distribution、basin、return time、escape cost を設計する。 |
| review gate | merge 前に accepted / rejected を決める。 | review gate は damping system の一部である。Attractor Engineering は review 前の proposal distribution まで設計対象にする。 |
| platform engineering | paved road を提供する。 | 良い実装経路を提供する点では近い。AAT ではそれを signature trajectory / basin mass / support risk として測る。 |
| architecture governance | 原則・標準・境界を維持する。 | governance は規範寄りである。Attractor Engineering は、その規範が future operation distribution をどう曲げたかを見る。 |

対比を一文で書くと次のようになる。

```text
guardrail / harness:
  bad operation を外から止める。

Attractor Engineering:
  bad operation が自然な局所最適にならない field を作る。
```

したがって、Attractor Engineering は `DampingControlSchema` だけではない。
Damping は出てきた raw force を減衰・射影・拒否・修正する。
Attractor Engineering は、出てくる前の operation support、local grammar、seed examples、
boundary affordance を変える。

```text
DampingControlSchema:
  raw force -> accepted / rejected / projected force

Attractor Engineering:
  architecture field -> raw force distribution itself
```

## AAT Dynamics Mapping

Attractor Engineering は、AAT の中では Architecture Signature Dynamics の design / control
layer として扱う。

対応は次の通りである。

| AAT / Dynamics 語彙 | Attractor Engineering での意味 |
| --- | --- |
| `ArchitectureField` | operation distribution を曲げる現在の構造・境界・例・テスト・ownership・policy context。Lean core というより docs / tooling 側の field snapshot。 |
| `FiniteOperationKernel` | state ごとの有限 operation support。Attractor Engineering の最小 formal handle。 |
| `OperationTransitionSemantics` | operation id がどの primitive transition を実現するかの関係。 |
| `SignatureObservation` | field の結果を signature 空間へ写す観測写像。 |
| `SignatureTrajectory` | operation 反復で得られる observed path。 |
| `AttractorCandidate` | finite observed trajectory の suffix が selected region に滞留する bounded witness。 |
| `BasinCandidate` | selected initial states が selected attractor candidate に到達する bounded classification。 |
| `DampingControlSchema` | review / CI / type checker / policy を accepted-step predicate として扱う schema。 |
| `gapMetrics` | endpoint / axis-wise / measured には安全に見えるが、path / cross-axis / future support / unmeasured axis で危険な差分を測る metric group。 |
| `SupportRiskMass` | support 内にある unsafe / unproved / unmeasured operation の重み。 |
| `BasinFragility` | 近傍 perturbation や operation support 変更で basin classification が反転する度合い。 |
| `SeedAttractorStrength` | canonical examples が future patch distribution を引き寄せる強さ。 |
| `DesignFieldStrength` | design boundary / examples / ownership / tests / non-goals が proposal distribution を整流する強さ。 |

Attractor Engineering の最小図式は次である。

```text
ArchitectureField F_t
  induces
FiniteOperationKernel K_t : State -> finite support Op

K_t + Semantics + Control
  induces
ArchitectureEvolution path

SignatureObservation sigma
  maps path to
SignatureTrajectory

Attractor / Basin layer
  classifies
selected suffix / selected initial states
```

この図式は global theorem ではない。selected finite universe、selected operation support、
bounded horizon、selected observation、measurement boundary に相対化して扱う。

## Formal Core

Lean に直接入れる最小核は、巨大な `ArchitectureField` 定義ではなく、既存の
`SignatureDynamics` API を読み替える薄い package でよい。

候補 schema:

```text
AttractorEngineeringSupportPackage =
  State
  Op
  Sig
  observation : SignatureObservation State Sig
  kernel : FiniteOperationKernel State Op
  semantics : OperationTransitionSemantics State Op
  targetRegion : SafeRegion Sig
  supportPreserves :
    kernel.SupportOperationsPreserveSafeRegion semantics observation targetRegion
  coverageAssumptions
  measurementBoundary
  nonConclusions
```

この package の意味は、selected support 内で自然に選ばれうる operation が、selected target
region を保存するように field を整えた、という bounded claim である。

## Bounded Theorem Candidates

### Support-Closed Safe Trajectory

operation support に入っている全 operation が selected safe region を保存するなら、その support
から選ばれた bounded script の signature trajectory は safe region から出ない。

```text
kernel.SupportOperationsPreserveSafeRegion sem O R
script.RealizesEvolution sem plan
kernel.ScriptUsesSupport script.operations plan
StateInSafeRegion O R X
------------------------------------------------
SignatureTrajectoryInSafeRegion R (SignatureTrajectory O plan)
```

Lean status: existing theorem を Attractor Engineering 語彙で読み替える wrapper 候補。

Attractor Engineering 的な読みは、良い field とは、少なくとも bounded universe 内では
自然に選ばれる operation support が safe-preserving family に閉じている状態である。

### Support Shaping Avoids Bad Region

bad region の補集合を selected safe region として扱い、support operations がそれを保存するなら、
bounded script は bad region に入らない。

```text
AvoidsBad Bad := fun sig => not (Bad sig)

StateInSafeRegion O (AvoidsBad Bad) X
kernel.SupportOperationsPreserveSafeRegion sem O (AvoidsBad Bad)
script.RealizesEvolution sem plan
kernel.ScriptUsesSupport script.operations plan
------------------------------------------------
SignatureTrajectoryInSafeRegion (AvoidsBad Bad) (SignatureTrajectory O plan)
```

Lean status: future wrapper theorem。実質的には support-closed safe trajectory の特殊化である。

### Same Signature, Different Future Field

現在の signature が同じでも、architecture field / operation kernel が違えば future trajectory は
変わりうる。

```text
exists X Y,
  O.observe X = O.observe Y
  and kernel1.support X != kernel2.support Y
```

さらに transition semantics と script を与えると、同じ current signature から異なる future
signature trajectory が生じる counterexample にできる。

Lean status: future counterexample。

この theorem は Attractor Engineering の必要性を示す。current signature snapshot だけでは、
future operation distribution を誘導する field は決まらない。

### Accepted Preservation Is Not Support Preservation

accepted step が safe region を保存することと、operation support 自体が safe-preserving である
ことは違う。guardrail が unsafe operations を reject していても、field には unsafe support が
残っていることがある。

```text
control.acceptedPreservesInvariant
and exists X op,
  kernel.Supports X op
  and not (sem.OperationPreservesSafeRegion O R op)
```

Lean status: future counterexample。

この theorem は、guardrail 成功と Attractor Engineering 成功を分離する。

### Constructive Damping Finite Return

accepted operation が bad-axis を非増加にするだけでは弱い。一定 block ごとに strict decrease が
あるなら、有限時間で safe region に戻る。

```text
bad : Sig -> Nat

assumption:
  every block of length k with bad > 0 contains
  an accepted step that strictly decreases bad

conclusion:
  bad sigma_0 = B
  implies exists n <= k * B, bad sigma_n = 0
```

Lean status: future proof obligation。

これは `DampingControlSchema.BadAxisDampingAssumption` を strict / fair block へ拡張する候補である。
tooling / empirical layer では、この strict damping assumption がどれだけ support されるかを測る。

### Observability Expansion Shock

新しい signature axis を追加すると、コードを変えていなくても bad-axis が visible になることがある。
これは architecture degradation ではなく、measurement boundary の拡張である。

```text
coarseSafe (coarseObserve X)
and not refinedSafe (refinedObserve X)
```

Lean status: future counterexample / existing measured-axis boundary theorem の読み替え。

Attractor Engineering metrics は unmeasured basin risk を zero と読んではいけない。

## Tooling Metrics

Attractor Engineering の tooling は、[Architecture Dynamics tooling 設計](architecture_dynamics_tooling_design.md)
の `architecture-dynamics-metrics-report-v0` に `attractorEngineering` slice を追加する形から始める。

候補 artifact:

```text
AttractorEngineeringReportV0 =
  repository
  window
  selectedRegions
  architectureFieldSnapshotRefs
  operationDistributionRefs
  trajectoryReportRefs
  attractorCandidates
  basinCandidates
  designFieldStrength
  seedAttractorStrength
  supportRiskMass
  basinBoundaryFragility
  trajectoryReturnTime
  badAttractorEscapeCost
  observabilityDebt
  measurementBoundary
  nonConclusions
```

初期段階では独立 artifact にせず、`architecture-dynamics-metrics-report-v0` の section として
出してよい。

| Metric | 定義方向 | claim level |
| --- | --- | --- |
| `DesignFieldStrength` | boundary、canonical examples、ownership、tests、non-goals が operation proposal を good family へ寄せる強さ。 | tooling / empirical |
| `SeedAttractorStrength` | canonical example に似た safe patch が増える度合い。 | empirical |
| `SupportRiskMass` | support ops のうち unsafe / unproved / unmeasured な operation の重み。 | tooling / empirical |
| `GoodAttractorBasinMass` | selected initial states / weighted states のうち good attractor candidate に到達する割合。 | simulation / empirical |
| `BadAttractorBasinMass` | bad attractor candidate に到達する selected initial-state mass。 | simulation / empirical |
| `BasinBoundaryFragility` | 1-step / k-step perturbation で basin label が変わる割合。 | simulation / tooling |
| `TrajectoryReturnTime` | safe region 逸脱後、何 PR / step で戻るか。 | tooling |
| `BadAttractorEscapeCost` | bad region から safe region へ戻る最短 repair / refactor script cost。 | Lean lower bound / tooling search |
| `FieldAlignmentScore` | observed / latent force が target region 方向に向いている度合い。 | tooling / empirical |
| `DefaultOperationBias` | 何も指示しないと選ばれやすい operation family の偏り。 | empirical |
| `GoodPathDiscoverability` | safe operation script が templates / examples / docs / APIs から見つけやすい度合い。 | tooling / empirical |
| `AttractorCaptureRate` | proposals / accepted PRs が selected good basin に入る割合。 | tooling / empirical |
| `NoncommutativeInterferencePressure` | proposal pair の期待 merge-order sensitivity。 | tooling / simulation |
| `ObservabilityDebt` | required axis のうち unmeasured / private / unavailable の mass。 | tooling |
| `FieldShapingDelta` | field update 前後の `SupportRiskMass`, `GoodBasinMass`, `SeedAttractorStrength` の差。 | empirical |

中心 metric は `SupportRiskMass` である。

```text
SupportRiskMass(C) =
  sum over op in support(C) of weight(op) * risk(op, C)
```

ただし `risk(op, C)` は単純な 0/1 ではなく、少なくとも次の状態を区別する。

```text
safe-preserving proved
safe-preserving measured
safe-preserving estimated
unsafe witness measured
unmeasured
notComparable
outOfScope
```

これにより、AAT の「測れていないものを zero と読まない」原則を守る。

## Empirical Hypotheses

Attractor Engineering は、かなりの部分が empirical hypothesis である。
証明できるのは bounded finite universe 上の support / trajectory / basin theorem であって、
実コードベース全体の成功や incident reduction は Lean theorem ではない。

### Design Field Strength Hypothesis

```text
DesignFieldStrength が高い architecture region では、
human / AI proposal distribution が good operation family に偏り、
SupportRiskMass が低くなる。
```

### Seed Attractor Hypothesis

```text
curated canonical examples を追加すると、
類似 task に対する proposal distribution が
safe-preserving operation vocabulary へシフトする。
```

### Basin Fragility Predicts Drift

```text
BasinBoundaryFragility が高い region では、
小さな PR / prompt / requirement perturbation により
signature trajectory が bad basin へ分岐しやすい。
```

### Damping Alone Is Insufficient

```text
review / CI の rejection が強くても、
unsafe operation support が大きい architecture field では、
raw bad force inflow が増え続け、ConstraintSaturation が上がる。
```

### Refactoring as Basin Reshaping

```text
良い refactoring は現在の signature を改善するだけでなく、
future operation distribution を変え、
GoodAttractorBasinMass を増やし、
BadAttractorEscapeCost を下げる。
```

### Same Signature, Different Field Hypothesis

```text
同じ Architecture Signature を持つ二つの region でも、
canonical examples、ownership、tests、local grammar が違えば、
future operation distribution と signature trajectory は異なる。
```

## Vibe Coding Readiness

Vibe Coding を AAT + Attractor Engineering で見るなら、成功条件は AI agent の能力や
harness の強さだけではない。高 throughput の proposal generation が、良い basin に落ちるよう
設計された architecture field に注入されるかが重要である。

短い定式化:

```text
Vibe Coding succeeds when high-throughput proposal generation is injected
into an architecture field whose natural operation distribution,
canonical examples, feedback loops, and measurement boundaries
pull repeated patches toward selected productive basins faster than
bad-axis force can accumulate.
```

日本語では次のように読む。

```text
Vibe Coding が成立するのは、高速な proposal generation が、
悪い局所文法を増幅するのではなく、良い basin に落ちるよう設計された
architecture field に注入される場合である。
```

multi-axis readiness としては次を観測する。

```text
VibeCodingReadiness(C, TaskClass, H) depends on:
  DesignFieldStrength(C)
  SeedAttractorStrength(C)
  SupportRiskMass(C)
  GoodAttractorBasinMass(C, H)
  BasinBoundaryFragility(C, H)
  TrajectoryReturnTime(C)
  DampingToThroughputMargin(C)
  ObservabilityDebt(C)
```

単一スコア化は避ける。dashboard では multi-axis readiness として出す。

## Maturity Model

Attractor Engineering の maturity は、次の段階で扱う。

| Level | 名前 | 状態 |
| --- | --- | --- |
| AE-0 | Unobserved field | signature trajectory も proposal distribution も見えていない。 |
| AE-1 | Trajectory observed | PR force / signature trajectory は測れている。 |
| AE-2 | Support visible | finite operation support / proposal log が一部見えている。 |
| AE-3 | Basin candidate visible | bounded simulation / observed trajectory で attractor / basin candidate が見える。 |
| AE-4 | Damping calibrated | review / CI / type / policy の dissipated force が測れている。 |
| AE-5 | Field shaping validated | canonical examples / boundary / non-goals が operation distribution を変えた evidence がある。 |
| AE-6 | Closed-loop attractor engineering | field update -> distribution shift -> trajectory improvement -> feedback update の loop が artifact として回っている。 |

## Non-Conclusions

Attractor Engineering は次を結論しない。

- 実コードベース全体の global attractor が分かった。
- finite simulation の basin candidate が現実の全 trajectory を代表する。
- AI patch distribution を完全に測定できた。
- review / CI / type checker が存在するので十分な dissipation capacity がある。
- `DesignFieldStrength` が真の因果効果として測れた。
- selected safe region が全 semantic / runtime / organizational risk を覆っている。
- unmeasured axis は zero である。
- Vibe Coding が一般に成功する、または失敗する。
- AI provenance だけで high risk / low risk が言える。
- Attractor Engineering maturity が incident reduction を theorem として保証する。

## First Implementation Slice

最初に入れる単位は docs / Lean / tooling を分ける。

### docs

この文書を source of truth とし、`Architecture Signature Dynamics 設計` と
`Architecture Dynamics tooling 設計` から参照する。

### Lean

最初から大きな `ArchitectureField` を入れない。候補は次である。

```text
Formal/Arch/Evolution/AttractorEngineering.lean
```

初期内容は、既存 `SignatureDynamics.lean` の theorem を Attractor Engineering 語彙で束ねる
wrapper package とする。

優先候補:

- `supportPackage_preserves_targetTrajectory`
- `sameSignature_differentKernel_counterexample`
- `acceptedPreservation_not_supportPreservation_counterexample`

### tooling

最初は `architecture-dynamics-metrics-report-v0` に `attractorEngineering` section を追加する。

```text
attractorEngineering =
  selectedRegions
  attractorCandidates
  basinCandidates
  supportRiskMass
  designFieldStrength
  seedAttractorStrength
  basinBoundaryFragility
  trajectoryReturnTime
  observabilityDebt
  measurementBoundary
  nonConclusions
```

validator の最初の仕事は、数値の正しさよりも、`unmeasured` / `unavailable` / `private` /
`notComparable` を 0 と読ませないことである。

## Research Message

Attractor Engineering の最も強いメッセージは次である。

```text
The safest AI coding environment is not necessarily the one with
the strongest external harness.

It is the one whose architecture field makes good operations
locally natural, copyable, observable, and low-friction,
while making bad attractor basins shallow, visible, and hard to enter.
```

日本語では次のように読む。

```text
最も安全な AI coding 環境とは、外部ハーネスが最も強い環境ではない。
良い operation が局所的に自然で、模倣しやすく、観測可能で、低摩擦であり、
悪い attractor basin が浅く、見えやすく、入りにくい architecture field を持つ環境である。
```
