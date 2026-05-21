# SFT Roadmap 残タスク実装指示書（実装前履歴）

この文書は、`Formal/Arch/Evolution/SFTDescent.lean` に binary local-to-global gluing core
を実装する前の作業指示・履歴である。現在の実装状態の source of truth は
`Formal/Arch/Evolution/SFTDescent.lean`, `docs/aat/lean_theorem_index.md`,
`docs/aat/proof_obligations.md`, `docs/sft/sft_theorem_roadmap_and_research_vision.md` を見る。

実装後の現在状態では、`glueCompatibleBinaryClockedConeFamily` と
`BinaryDescentAssumptions.ofStepGluing` が追加され、compatible local cone family から
global cone point への path gluing は `BinaryClockedStepGluingData` から構成される。
さらに `BinaryProjectionGluingLaws` と
`BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws` により、endpoint-level の
projection/glue laws から selected inverse laws を構成できる。strict path-level inverse
laws は今後の proof obligation として残る。

## 実装前の現在地

以下は実装前スナップショットであり、現在の Lean 実装状態を直接表すものではない。
当時の Lean 実装は、SFT theorem roadmap の土台としてかなり進んでいた。

完了済み:

```text
ClockedForecastCone core
  - exact clock: length = horizon
  - bounded clock: length <= horizon
  - ForecastCone から idle padding で exact ClockedForecastCone へ bridge

BinaryFieldCover
  - restrictLeft / restrictRight
  - interface compatibility
  - glue
  - global_ext

BinarySFTModel
  - global/local/interface support
  - global-to-local support projection
  - global-to-local step projection
  - global clocked path projection
  - global ClockedConePoint -> CompatibleBinaryClockedConeFamily

Binary descent surface
  - ConeEquivalence with equivalence-relation laws
  - BinaryDescentAssumptions
  - forecastCone_descent_binary

Other roadmap surfaces
  - Descent obstruction package
  - MinimalEnvelope quotient
  - Governance guard basis theorem
  - Closed-loop finite-rank fixed point theorem
  - Artifact Yoneda separating probe theorem
  - Agentic confluence normal-form surface
  - FundamentalModularityConclusion / Package
```

まだ残っている中心課題:

```text
compatible local cone family -> global cone point
```

現在これは:

```lean
BinaryDescentAssumptions.glueLocalFamily
```

として仮定されている。

次の目標は、これを可能な限り具体的な cover / support / step gluing assumption から構成すること。

---

## 最重要ゴール

最初の大きな未完部分はこれ。

```text
Local-to-Global Clocked Path Gluing
```

最終的には次を作る。

```lean
def glueCompatibleBinaryClockedConeFamily
  (glueData : BinaryClockedStepGluingData model)
  (family : CompatibleBinaryClockedConeFamily model source horizon)
  : ClockedConePoint model.globalSupport model.globalRelation source horizon
```

そしてこれを使って、

```lean
def BinaryDescentAssumptions.ofStepGluing
  (glueData : BinaryClockedStepGluingData model)
  ...
  : BinaryDescentAssumptions model source horizon
```

を作る。

これにより、

```lean
forecastCone_descent_binary
```

が、`glueLocalFamily` を丸ごと仮定する状態から、より細かい step-level gluing assumptions から構成される状態へ進む。

---

## Phase 1: local tick pair を定義する

追加先:

```text
Formal/Arch/Evolution/SFTDescent.lean
```

または大きくなりすぎるなら:

```text
Formal/Arch/Evolution/SFTDescentGluing.lean
```

定義する。

```lean
structure CompatibleLocalClockedStep
    {Global Left Right Interface : Type _}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG OperationL OperationR OperationI : Type _}
    (model : BinarySFTModel cover OperationG OperationL OperationR OperationI)
    {left₀ left₁ : Left}
    {right₀ right₁ : Right} where
  leftStep :
    ClockedFieldStep model.leftSupport model.leftRelation left₀ left₁
  rightStep :
    ClockedFieldStep model.rightSupport model.rightRelation right₀ right₁
  sourceCompatible :
    cover.compatible left₀ right₀
  targetCompatible :
    cover.compatible left₁ right₁
  interfaceStepAgreement : Prop
  nonConclusions : Prop
```

目的:

```text
left/right の 1 tick が同じ global tick の局所像として読める条件を表す。
```

注意:

- `interfaceStepAgreement` は最初 `Prop` でよい。
- 後で interface path projection equality に強める。
- active/idle の4ケースを無理に最初から分解しない。

---

## Phase 2: local tick pair から global tick を作る gluing data

定義する。

```lean
structure BinaryClockedStepGluingData
    {Global Left Right Interface : Type _}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG OperationL OperationR OperationI : Type _}
    (model : BinarySFTModel cover OperationG OperationL OperationR OperationI) where

  glueStep :
    ∀ {left₀ left₁ : Left} {right₀ right₁ : Right},
      CompatibleLocalClockedStep model
        (left₀ := left₀) (left₁ := left₁)
        (right₀ := right₀) (right₁ := right₁) ->
        ClockedFieldStep model.globalSupport model.globalRelation
          (cover.glue left₀ right₀ ‹cover.compatible left₀ right₀›)
          (cover.glue left₁ right₁ ‹cover.compatible left₁ right₁›)

  left_projection_law : Prop
  right_projection_law : Prop
  idle_left_law : Prop
  idle_right_law : Prop
  active_active_boundary : Prop
  active_idle_boundary : Prop
  idle_active_boundary : Prop
  idle_idle_boundary : Prop
  nonConclusions : Prop
```

Lean では `‹...›` が使いにくいので、実際には source/target compatibility を明示引数にする。

推奨形:

```lean
glueStep :
  ∀ {left₀ left₁ : Left} {right₀ right₁ : Right}
    (hSource : cover.compatible left₀ right₀)
    (hTarget : cover.compatible left₁ right₁),
    CompatibleLocalClockedStep model
      (left₀ := left₀) (left₁ := left₁)
      (right₀ := right₀) (right₁ := right₁) ->
      ClockedFieldStep model.globalSupport model.globalRelation
        (cover.glue left₀ right₀ hSource)
        (cover.glue left₁ right₁ hTarget)
```

最初は projection laws を `Prop` field にしてよい。
次段階で theorem-bearing にする。

---

## Phase 3: local path pair を tickwise に zip する

`CompatibleBinaryClockedConeFamily` は left/right path を持つ。

必要なのは、同じ horizon の exact clock path なので、left/right path を tick ごとに対応させること。

定義候補:

```lean
structure CompatibleLocalClockedPath
    (model : BinarySFTModel cover OperationG OperationL OperationR OperationI)
    (source : Global) (horizon : Nat) where
  family : CompatibleBinaryClockedConeFamily model source horizon
  tickwiseCompatible : Prop
```

ただし、これでは path induction ができない。

よりよい形:

```lean
inductive CompatibleLocalClockedPath :
    {left₀ left₁ : Left} ->
    {right₀ right₁ : Right} ->
    ClockedFieldPath model.leftSupport model.leftRelation left₀ left₁ ->
    ClockedFieldPath model.rightSupport model.rightRelation right₀ right₁ ->
    Prop
  | nil :
      cover.compatible left₀ right₀ ->
      CompatibleLocalClockedPath
        (ArchitecturePath.nil left₀)
        (ArchitecturePath.nil right₀)
  | cons :
      CompatibleLocalClockedStep model localStepPair ->
      CompatibleLocalClockedPath leftRest rightRest ->
      CompatibleLocalClockedPath
        (ArchitecturePath.cons leftStep leftRest)
        (ArchitecturePath.cons rightStep rightRest)
```

この inductive が本命。

証明する。

```lean
compatibleLocalClockedPath_left_length_eq_right_length :
  CompatibleLocalClockedPath leftPath rightPath ->
    ArchitecturePath.length leftPath = ArchitecturePath.length rightPath
```

ただし exact cone から両方 `horizon` なので、長さ一致は補助的。

---

## Phase 4: local compatible path を global path へ glue する

`CompatibleLocalClockedPath` に induction して global path を作る。

```lean
def glueCompatibleLocalClockedPath
  (glueData : BinaryClockedStepGluingData model) :
  CompatibleLocalClockedPath model leftPath rightPath ->
    ClockedFieldPath model.globalSupport model.globalRelation
      (cover.glue leftSource rightSource hSource)
      (cover.glue leftTarget rightTarget hTarget)
```

nil case:

```lean
ArchitecturePath.nil (cover.glue left₀ right₀ hCompat)
```

cons case:

```lean
ArchitecturePath.cons
  (glueData.glueStep ...)
  (glueCompatibleLocalClockedPath rest)
```

証明する。

```lean
glueCompatibleLocalClockedPath_length :
  length gluedPath = length leftPath
```

または

```lean
length gluedPath = horizon
```

family から使うなら後者でよい。

---

## Phase 5: CompatibleBinaryClockedConeFamily に tickwise witness を入れる

現在:

```lean
tickwiseInterfaceAgreement : Prop
```

これを弱すぎるまま使うと glue できない。

変更案:

```lean
tickwiseCompatible :
  CompatibleLocalClockedPath model leftPath rightPath
```

移行が大きければ、追加 field にする。

```lean
tickwiseCompatible :
  Prop
```

から

```lean
tickwisePath :
  CompatibleLocalClockedPath model leftPath rightPath
```

へ強める。

推奨:

```lean
structure CompatibleBinaryClockedConeFamily ... where
  ...
  tickwisePath :
    CompatibleLocalClockedPath model leftPath rightPath
  nonConclusions : Prop
```

`projectGlobalConePointToBinaryFamily` で tickwisePath を作るには、global path の projection から left/right の compatible path を作る必要がある。

そのため次も必要。

```lean
projectedClockedPaths_tickwiseCompatible :
  ∀ globalPath,
    CompatibleLocalClockedPath model
      (projectClockedPathLeft model globalPath)
      (projectClockedPathRight model globalPath)
```

これは global path induction で証明する。

---

## Phase 6: global path projection から tickwise compatibility を証明する

定義:

```lean
projectClockedStepPairCompatible :
  ∀ globalStep,
    CompatibleLocalClockedStep model
      (projectClockedStepLeft model globalStep)
      (projectClockedStepRight model globalStep)
```

idle case は簡単。

active case では interface agreement が必要。
`BinarySFTModel` に追加する。

```lean
global_step_projects_interface :
  ∀ {g₀ g₁ op},
    model.globalSupport.Supports g₀ op ->
    model.globalRelation.Realizes g₀ op g₁ ->
      interface agreement between projected left/right steps
```

最初は:

```lean
projected_step_interface_agreement : Prop
```

でもよいが、`CompatibleLocalClockedStep` を作る theorem には具体的な証拠が必要。

現実的な第一段階:

`CompatibleLocalClockedStep.interfaceStepAgreement` が `Prop` なら、`BinarySFTModel` に

```lean
projected_active_step_interface_agreement :
  ∀ {g₀ g₁ op}
    (hSupport : ...)
    (hRealizes : ...),
      PropForProjectedStep ...
```

を置く。

あるいは簡潔に:

```lean
projected_clocked_step_compatible :
  ∀ {g₀ g₁}
    (step : ClockedFieldStep model.globalSupport model.globalRelation g₀ g₁),
      ProjectedLocalClockedStepCompatible model step
```

を field として持たせる。

---

## Phase 7: glueLocalFamily を構成する

ここでようやく:

```lean
def glueCompatibleBinaryClockedConeFamily
  (glueData : BinaryClockedStepGluingData model)
  (family : CompatibleBinaryClockedConeFamily model source horizon)
  : ClockedConePoint model.globalSupport model.globalRelation source horizon
```

を実装する。

target:

```lean
cover.glue family.leftTarget family.rightTarget family.compatibleTarget
```

path:

```lean
glueCompatibleLocalClockedPath glueData family.tickwisePath
```

coneMember:

```lean
ClockedForecastCone
```

証明:

```lean
length gluedPath = horizon
```

これは

```text
length gluedPath = length family.leftPath
length family.leftPath = horizon
```

で出す。

---

## Phase 8: BinaryDescentAssumptions.ofStepGluing を作る

```lean
def BinaryDescentAssumptions.ofStepGluing
  (glueData : BinaryClockedStepGluingData model)
  (equivData : BinaryProjectionGluingEquivalenceLaws model glueData source horizon)
  : BinaryDescentAssumptions model source horizon
```

`equivData` は以下を持つ。

```lean
structure BinaryProjectionGluingEquivalenceLaws ... where
  globalConePointEquivalent : ...
  localFamilyEquivalent : ...
  global_refl : ...
  global_symm : ...
  global_trans : ...
  local_refl : ...
  local_symm : ...
  local_trans : ...
  projected_glued_related : ...
  glued_projected_related : ...
```

ここでも inverse laws はまだ assumption でよい。
ただし `glueLocalFamily` 自体は concrete に構成される。

これが重要な進歩。

---

## Phase 9: strict equality 版を検討する

selected equivalence 版が通った後、条件が強い場合だけ strict equality 版を作る。

```lean
structure StrictBinaryDescentAssumptions extends BinaryDescentAssumptions ... where
  projected_glued_eq :
    ∀ point,
      glueLocalFamily (projectGlobalConePointToBinaryFamily model point) = point
  glued_projected_eq :
    ∀ family,
      projectGlobalConePointToBinaryFamily model (glueLocalFamily family) = family
```

定理:

```lean
forecastCone_descent_binary_strict :
  StrictBinaryDescentAssumptions model source horizon ->
    BidirectionalEquivalence
      (ClockedConePoint ...)
      (CompatibleBinaryClockedConeFamily ...)
```

これは後回しでよい。

---

## Phase 10: docs の「最終形」表現を調整する

現時点で「最終形」と言い切らない。

使う表現:

```text
substantive binary descent surface
selected-equivalence descent theorem
local-to-global gluing still boundary-explicit
```

`glueCompatibleBinaryClockedConeFamily` が実装されたら:

```text
local-to-global path gluing is now constructed from step gluing data
```

と書ける。

ただし inverse law が assumption なら、

```text
inverse laws remain selected equivalence assumptions
```

と明記する。

---

## Phase 11: finite cover へ進む前の gate

finite cover へ進む前に、binary 版で次が揃っていること。

```text
1. exact ClockedForecastCone
2. BinaryFieldCover
3. global-to-local path projection
4. projected paths are tickwise compatible
5. compatible local paths glue to global path
6. compatible local family glues to global cone point
7. selected equivalence descent theorem
8. no-lift / local-identification obstruction predicates
```

この gate を満たすまで finite cover / Cech には進まない。

---

## Phase 12: finite cover / Cech は binary 後

binary が安定したら追加。

```text
Formal/Arch/Evolution/SFTFiniteCover.lean
Formal/Arch/Evolution/SFTCechCone.lean
```

定義:

```lean
FiniteFieldCover
CechSimplex
LocalConeOnSimplex
CompatibleFiniteClockedConeFamily
```

最初の theorem:

```lean
finiteCover_descent_of_binary_tree_descent
```

つまり finite cover を binary gluing tree に分解できる場合に descent を得る。

一般 limit は後回し。

---

## Phase 13: Fundamental Modularity Theorem の本当の次段階

今の `FundamentalModularityTheoremPackage.ofTheoremFamily` は conservative constructor。

次は依存をもっと具体化する。

```lean
structure FundamentalModularityInputs where
  binaryDescent :
    ∀ source horizon,
      BinaryDescentAssumptions.ofStepGluing ...
  obstructionClassifier :
    ...
  minimalEnvelope :
    ...
  governanceSynthesis :
    ...
  closedLoop :
    ...
```

そして:

```lean
theorem fundamental_modularity_from_binary_descent_inputs :
  FundamentalModularityInputs ... ->
    FundamentalModularityConclusion
```

この theorem では、少なくとも `modularityAsDescent` は `SFTModuleBoundary model` から出す。

```lean
modularityAsDescent := SFTModuleBoundary model
```

現状のように arbitrary Prop を渡すだけにしない。

---

## Phase 14: 次の PR の成功条件

次の PR で最低限ほしい成果:

```text
CompatibleLocalClockedStep
CompatibleLocalClockedPath
projectedClockedPaths_tickwiseCompatible
BinaryClockedStepGluingData
glueCompatibleLocalClockedPath
glueCompatibleBinaryClockedConeFamily
BinaryDescentAssumptions.ofStepGluing
```

これが入れば、かなり本物に近づく。

---

## PR 前チェック

必ず実行。

```bash
lake build
git diff --check
rg -n '\b(axiom|admit|sorry|unsafe)\b' Formal
rg -nP '[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}\x{FEFF}]' Formal docs
```

docs 更新:

```text
docs/aat/lean_theorem_index.md
docs/aat/proof_obligations.md
docs/sft/sft_theorem_roadmap_and_research_vision.md
docs/sft/sft_theorem_roadmap_update_lean.md
```

---

## 判定基準

まだ「全大定理証明済み」とは言わない。

次の状態になったら、

```text
ForecastCone Descent Theorem の binary local-to-global core が実装された
```

と言ってよい。

```lean
glueCompatibleBinaryClockedConeFamily :
  BinaryClockedStepGluingData model ->
  CompatibleBinaryClockedConeFamily model source horizon ->
  ClockedConePoint model.globalSupport model.globalRelation source horizon
```

かつ

```lean
BinaryDescentAssumptions.ofStepGluing :
  BinaryClockedStepGluingData model ->
  BinaryProjectionGluingEquivalenceLaws ... ->
  BinaryDescentAssumptions model source horizon
```

が存在すること。

「Fundamental Modularity Theorem が実質証明された」と言うには、さらに:

```text
SFTModuleBoundary が binary descent inputs から出る
obstruction theorem が actual descent map failure に接続される
minimal envelope が quotient theorem として使われる
governance synthesis が support transformation と接続される
closed-loop theorem が finite-height / well-founded proof に接続される
```

が必要。
```
