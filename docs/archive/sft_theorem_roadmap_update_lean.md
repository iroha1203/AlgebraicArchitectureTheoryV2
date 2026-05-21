# SFT Theorem Roadmap 最終形実装指示書

## 目的

現在の `Formal/Arch/Evolution/SFTTheoremRoadmap.lean` は、SFT theorem roadmap を Lean 上で安全に受け止めるための theorem-package surface である。

次の段階では、roadmap の最終形へ進める。

目標は、`descentEquiv` や `fundamental_modularity` を package field として仮定するだけでなく、明示された前提群から主要 theorem witness を構成することである。

特に最初の主目標は次である。

```text
ForecastCone Descent Theorem

cover compatibility
+ support restriction
+ step projection
+ idle/stutter alignment
+ interface glue
+ inverse laws
--------------------------------
ClockedForecastCone_h(G)
  ≃
CompatibleLocalConeFamily_h(C)
```

この binary descent が通った後、finite cover、obstruction、minimal envelope、governance、fixed point、Fundamental Modularity Theorem へ進む。

## 絶対制約

- `axiom`, `admit`, `sorry`, `unsafe` を導入しない。
- 証明できない主張を theorem stub として置かない。
- 遠い主張は `structure ... where` の明示前提として持つ。
- theorem 名が実際の証明内容より強く見えないようにする。
- docs では `proved accessor` と `proved substantive theorem` を必ず区別する。
- `ForecastCone` は bounded finite path membership であり、予測精度・確率・因果証明ではない。
- `ClockedForecastCone` は exact shared-clock path model として扱う。
- `BoundedClockedForecastCone` と `ClockedForecastCone` を混同しない。

## 現在地

現在あるもの:

```text
Formal/Arch/Evolution/SFTTheoremRoadmap.lean
```

主な内容:

```text
ClockedFieldStep
ClockedFieldPath
ClockedForecastCone              -- length = horizon
BoundedClockedForecastCone       -- length <= horizon
clockedForecastCone_of_forecastCone
ClockedForecastConeDescentPackage
BinaryForecastConeDescentPackage
ModularityRepresentationPackage
DescentObstructionPackage
...
FundamentalModularityTheoremPackage
```

これは theorem-package surface である。

未完の中心:

```text
descentEquiv を前提として持つ
```

から

```text
descentEquiv を cover / restriction / gluing assumptions から構成する
```

へ進むこと。

## Phase 1: Clocked Cone Core を独立 module 化する

作成:

```text
Formal/Arch/Evolution/SFTClockedCone.lean
```

移動または再構成する定義:

```text
ClockedFieldStep
ClockedFieldPath
ExactClockedFieldPath
BoundedClockedFieldPath
ClockedForecastCone
BoundedClockedForecastCone
clockedFieldPathOfFieldPath
idleClockedFieldPath
paddedClockedFieldPathOfFieldPath
ClockedConePoint
```

証明する theorem:

```text
ClockedForecastCone.length_eq_horizon
ClockedForecastCone.length_le_horizon
ClockedForecastCone.nil_mem
ClockedForecastCone.idle_mem_one

BoundedClockedForecastCone.of_clockedForecastCone
BoundedClockedForecastCone.nil_mem
BoundedClockedForecastCone.monotone_horizon
BoundedClockedForecastCone.idle_mem

clockedFieldPathOfFieldPath_length
idleClockedFieldPath_length
paddedClockedFieldPathOfFieldPath_length

boundedClockedForecastCone_of_forecastCone
clockedForecastCone_of_forecastCone

ClockedConePoint.length_eq_horizon
ClockedConePoint.length_le_horizon
ClockedConePoint.ofForecastCone
```

注意:

`ClockedForecastCone` は exact clock に固定する。

```lean
ArchitecturePath.length path = horizon
```

`<= horizon` は必ず `BoundedClockedForecastCone` に分離する。

## Phase 2: Binary Field Cover を定義する

作成:

```text
Formal/Arch/Evolution/SFTFieldCover.lean
```

最初は一般 finite cover ではなく binary cover に集中する。

定義候補:

```lean
structure BinaryFieldCover (Global Left Right Interface : Type _) where
  restrictLeft  : Global -> Left
  restrictRight : Global -> Right
  leftInterface : Left -> Interface
  rightInterface : Right -> Interface
  compatible : Left -> Right -> Prop
  glue : (l : Left) -> (r : Right) -> compatible l r -> Global

  glue_left :
    forall l r h, restrictLeft (glue l r h) = l
  glue_right :
    forall l r h, restrictRight (glue l r h) = r
  compatible_iff_interface :
    forall l r, compatible l r <-> leftInterface l = rightInterface r
  glue_unique :
    forall g l r h,
      restrictLeft g = l ->
      restrictRight g = r ->
      g = glue l r h
```

必要に応じて `glue_unique` は強すぎる可能性がある。
dependent equality が重い場合は、まず weaker version を使う。

```lean
global_ext :
  forall g₁ g₂,
    restrictLeft g₁ = restrictLeft g₂ ->
    restrictRight g₁ = restrictRight g₂ ->
      g₁ = g₂
```

優先は `global_ext`。

## Phase 3: Support / Relation restriction を定義する

作成:

```text
Formal/Arch/Evolution/SFTDescent.lean
```

binary cover 上で、global support / relation と local support / relation の関係を明示する。

定義候補:

```lean
structure BinarySFTModel
    (cover : BinaryFieldCover Global Left Right Interface)
    (OperationG OperationL OperationR OperationI : Type _) where
  globalSupport : OperationSupport Global OperationG
  globalRelation : StepRelation Global OperationG

  leftSupport : OperationSupport Left OperationL
  leftRelation : StepRelation Left OperationL

  rightSupport : OperationSupport Right OperationR
  rightRelation : StepRelation Right OperationR

  interfaceSupport : OperationSupport Interface OperationI
  interfaceRelation : StepRelation Interface OperationI

  projectLeftOp : OperationG -> OperationL
  projectRightOp : OperationG -> OperationR
  projectInterfaceLeftOp : OperationL -> OperationI
  projectInterfaceRightOp : OperationR -> OperationI

  -- operation compatibility
  projected_ops_compatible : Prop

  -- support projection
  global_support_projects_left : Prop
  global_support_projects_right : Prop

  -- step projection
  global_step_projects_left : Prop
  global_step_projects_right : Prop

  -- local step gluing
  compatible_local_steps_glue : Prop

  -- idle/stutter compatibility
  idle_projects : Prop
  idle_glues : Prop

  -- boundaries
  supportBoundary : Prop
  stepBoundary : Prop
  policyBoundary : Prop
  observationBoundary : Prop
  nonConclusions : Prop
```

ただし、`Prop` field のままでは substantive theorem にならない。
次の段階で theorem-bearing predicate に分解する。

具体化する predicate:

```lean
GlobalSupportProjectsLeft
GlobalSupportProjectsRight
GlobalStepProjectsLeft
GlobalStepProjectsRight
CompatibleLocalStepsGlue
IdleStepProjects
IdleStepGlues
```

例:

```lean
def GlobalStepProjectsLeft (...) : Prop :=
  forall {g₀ g₁ : Global} {op : OperationG},
    globalSupport.Supports g₀ op ->
    globalRelation.Realizes g₀ op g₁ ->
      leftRelation.Realizes
        (cover.restrictLeft g₀)
        (projectLeftOp op)
        (cover.restrictLeft g₁)
```

support も同様。

```lean
def GlobalSupportProjectsLeft (...) : Prop :=
  forall g op,
    globalSupport.Supports g op ->
      leftSupport.Supports (cover.restrictLeft g) (projectLeftOp op)
```

## Phase 4: Global clocked path を local clocked path へ射影する

実装する関数:

```lean
projectClockedStepLeft
projectClockedStepRight
projectClockedPathLeft
projectClockedPathRight
```

active step の場合:

```text
global active step
  -> local active step
```

idle step の場合:

```text
global idle step
  -> local idle step
```

証明する theorem:

```lean
projectClockedPathLeft_length
projectClockedPathRight_length
projectClockedForecastCone_left
projectClockedForecastCone_right
```

期待形:

```lean
theorem projectClockedForecastCone_left
  (hCone : ClockedForecastCone globalSupport globalRelation source h target path)
  : ClockedForecastCone leftSupport leftRelation
      (cover.restrictLeft source) h (cover.restrictLeft target)
      (projectClockedPathLeft path)
```

ここで exact horizon が効く。

```lean
ArchitecturePath.length (projectClockedPathLeft path)
=
ArchitecturePath.length path
=
h
```

## Phase 5: CompatibleLocalConeFamily を concrete に定義する

binary 版:

```lean
structure CompatibleBinaryClockedConeFamily (...) where
  leftTarget : Left
  rightTarget : Right
  compatibleTarget : cover.compatible leftTarget rightTarget

  leftPath :
    ClockedFieldPath leftSupport leftRelation
      (cover.restrictLeft source) leftTarget
  rightPath :
    ClockedFieldPath rightSupport rightRelation
      (cover.restrictRight source) rightTarget

  leftCone :
    ClockedForecastCone leftSupport leftRelation
      (cover.restrictLeft source) h leftTarget leftPath
  rightCone :
    ClockedForecastCone rightSupport rightRelation
      (cover.restrictRight source) h rightTarget rightPath

  interfaceEndpointAgreement :
    cover.leftInterface leftTarget = cover.rightInterface rightTarget
  tickwisePath :
    CompatibleLocalClockedPath model leftPath rightPath
```

`interfaceEndpointAgreement` は endpoint 境界を記録し、`tickwisePath` は local left/right
clocked paths が tick ごとに対応していることを記録する。

理想形:

```lean
projectLeftPathToInterface leftPath
=
projectRightPathToInterface rightPath
```

ただし dependent path equality が重いなら、まず endpoint agreement と tickwise compatibility を分ける。

```lean
interfaceEndpointAgreement
tickwisePath
```

## Phase 6: local compatible family を global path へ glue する

関数:

```lean
glueClockedStep
glueClockedPath
```

必要な前提:

```text
left step and right step have compatible interface effect
```

tick ごとの場合分け:

```text
left active, right active -> global active
left active, right idle   -> global active or allowed global step
left idle, right active   -> global active or allowed global step
left idle, right idle     -> global idle
```

ここが最難関。

最初は無理に operation を構成しない。
`CompatibleLocalStepsGlue` に global step witness を返す関数を持たせる。

```lean
structure CompatibleLocalStepGlue (...) where
  glues :
    forall localStepPair,
      TickwiseCompatible localStepPair ->
        exists globalStep,
          projects_to_left globalStep localStepPair.left
          and projects_to_right globalStep localStepPair.right
```

その後:

```lean
glueClockedPath :
  CompatibleBinaryClockedConeFamily ... ->
    ClockedConePoint globalSupport globalRelation source h
```

証明:

```lean
glueClockedPath_length
glueClockedPath_coneMember
```

## Phase 7: Binary ForecastCone Descent を構成する

構成する equivalence:

```lean
forecastCone_descent_binary :
  BinaryDescentAssumptions cover model source h ->
    BidirectionalEquivalence
      (ClockedConePoint globalSupport globalRelation source h)
      (CompatibleBinaryClockedConeFamily cover model source h)
```

`toFun`:

```text
global cone point
  -> project left/right paths
  -> prove local cone membership
  -> prove compatibility
```

`invFun`:

```text
compatible local family
  -> glue target
  -> glue path
  -> prove global cone membership
```

inverse law:

```lean
left_inv :
  forall globalPoint,
    invFun (toFun globalPoint) = globalPoint

right_inv :
  forall localFamily,
    toFun (invFun localFamily) = localFamily
```

ここは dependent equality が重い。
最初は `BidirectionalEquivalence` より弱い setoid equivalence を導入してよい。

候補:

```lean
structure ConeEquivalence (A B : Type _) where
  toFun : A -> B
  invFun : B -> A
  leftRelated : A -> A -> Prop
  rightRelated : B -> B -> Prop
  left_refl : forall a, leftRelated a a
  left_symm : forall {a b}, leftRelated a b -> leftRelated b a
  left_trans : forall {a b c}, leftRelated a b -> leftRelated b c -> leftRelated a c
  right_refl : forall b, rightRelated b b
  right_symm : forall {a b}, rightRelated a b -> rightRelated b a
  right_trans : forall {a b c}, rightRelated a b -> rightRelated b c -> rightRelated a c
  left_related : forall a, leftRelated (invFun (toFun a)) a
  right_related : forall b, rightRelated (toFun (invFun b)) b
```

その場合、docs には strict equality ではなく selected equivalence と書く。

## Phase 8: Descent package field を実 theorem で埋める

既存:

```lean
ClockedForecastConeDescentPackage
BinaryForecastConeDescentPackage
```

に対して、constructor theorem を追加する。

```lean
def BinaryForecastConeDescentPackage.ofAssumptions
  (assumptions : BinaryDescentAssumptions ...)
  : BinaryForecastConeDescentPackage ...
```

または theorem:

```lean
theorem binaryForecastConeDescentPackage_of_assumptions :
  BinaryDescentAssumptions cover model source h ->
    Nonempty (BinaryForecastConeDescentPackage ...)
```

この時点で初めて、package field ではなく、前提群から descent witness が構成される。

## Phase 9: Modularity Representation を実質化する

今は:

```lean
moduleBoundary ↔ forecastConeDescentForAll
```

を package field として持っている。

次は定義として固定する。

```lean
def SFTModuleBoundary cover model : Prop :=
  forall source h,
    Nonempty (BinaryForecastConeDescentPackage cover model source h)
```

または finite cover 版:

```lean
def SFTModuleBoundary cover model : Prop :=
  forall source h,
    ForecastConeDescent cover model source h
```

証明:

```lean
theorem moduleBoundary_iff_forecastConeDescent :
  SFTModuleBoundary cover model
    ↔
  forall source h, ForecastConeDescent cover model source h
```

これは定義展開に近いが、以後の theorem で使う入口になる。

## Phase 10: Descent Obstruction を binary descent failure に接続する

現在:

```lean
DescentObstructionPackage
```

は classifier を field として持つ。

次は actual failure を定義する。

```lean
def LocalFamilyDoesNotLift
def GlobalPathsLocallyIdentified
```

そして theorem:

```lean
theorem obstruction_of_no_lift
theorem obstruction_of_local_identification
```

ただし classifier completeness は前提でよい。

```lean
ClassifierComplete classifier ->
LocalFamilyDoesNotLift family ->
exists obstruction, ...
```

ここでは "tooling が完全" とは言わない。

## Phase 11: Minimal ConsequenceEnvelope を quotient で実装する

現在は factorization が package field。

次は setoid を作る。

```lean
def PathIndistinguishableFor Q p q :=
  forall decision, Q p decision <-> Q q decision
```

証明:

```lean
refl
symm
trans
```

作る:

```lean
def ReviewSetoid Q : Setoid ConePath
def MinimalEnvelope Q := Quot (ReviewSetoid Q)
```

証明:

```lean
minimalEnvelope_sound
minimalEnvelope_exact
minimalEnvelope_factors
```

注意:

factor theorem には `otherProjection` が setoid を respect する前提が必要。

```lean
EnvelopeRespectsDecisionEquivalence Q otherProjection
```

## Phase 12: Governance Synthesis を support transformation に接続する

現在は guard family と intervention の equivalence が package field。

次は既存の

```lean
GovernanceIntervention
SupportTransformation
PointwiseSupportInclusion
ForecastConeProjection
```

に接続する。

定義:

```lean
BadPathExcludedBySupportTransformation
DesiredPathPreservedBySupportTransformation
GuardInducesSupportRestriction
```

証明:

```lean
restrictive_governance_excludes_bad
restrictive_governance_preserves_desired
governance_synthesis_of_guard_basis_complete
```

## Phase 13: Closed-loop Fixed Point を order-theoretic にする

現在は fixed point 到達を package field。

次は finite height または well-founded refinement を入れる。

```lean
FieldEstimateRefinement
StrictRefinement
NoInfiniteStrictRefinement
BoundaryExpansionRequired
```

証明方針:

```text
if update keeps strictly refining without fixed point,
then infinite descending/ascending chain arises
contradiction by well-foundedness
```

または有限 universe で始める。

```lean
FiniteRefinementHeight
```

定理:

```lean
closedLoopCalibration_fixedPoint_or_boundary_of_finiteHeight
```

## Phase 14: Artifact Yoneda を separating probes theorem にする

full Yoneda は後回し。

先に:

```lean
ArtifactResponsesEquivalent
SFTSeparatingProbeFamily
SFTFieldEquivalence
```

を定義し、

```lean
artifact_yoneda_of_separating_probes
```

を証明する。

この theorem は実質的には separating family の定義展開でよい。
ただし docs には "Yoneda-shaped separating probe theorem" と書く。

## Phase 15: Agentic Confluence を rewriting と接続する

定義:

```lean
ProposalStep
Reaches
Terminates
LocalConfluent
UniqueNormalForm
FairInterleaving
```

最初は Newman lemma を一般化しすぎない。
finite proposal graph または well-founded relation に限定する。

証明:

```lean
local_unique_normal_form_of_terminating_confluent
agentic_confluence_of_local_normal_forms_and_descent
```

descent との接続は Phase 7 の binary descent theorem を使う。

## Phase 16: Fundamental Modularity Theorem を再構成する

現在:

```lean
FundamentalModularityTheoremPackage
```

は各成分を field として持つ。

最終形では、個別 theorem を束ねる constructor を作る。

```lean
def FundamentalModularityTheoremPackage.ofTheoremFamily
  (descent : ...)
  (obstruction : ...)
  (minimalEnvelope : ...)
  (governance : ...)
  (fixedPoint : ...)
  : FundamentalModularityTheoremPackage
```

そして theorem:

```lean
theorem fundamental_modularity_of_theorem_family :
  ForecastConeDescent ...
  -> DescentObstructionComplete ...
  -> MinimalEnvelopeTheorem ...
  -> GovernanceSynthesisTheorem ...
  -> ClosedLoopFixedPointTheorem ...
  -> FundamentalModularityConclusion ...
```

結論は強くしすぎない。

```lean
structure FundamentalModularityConclusion where
  modularityAsDescent : Prop
  technicalDebtAsObstruction : Prop
  reviewAsMinimalEnvelope : Prop
  governanceAsObstructionCutting : Prop
  learningAsBoundaryExplicitFixedPoint : Prop
  computablyGoverned : Prop
  typedBoundaryFailureWitness : Prop
  governed_or_failure : computablyGoverned ∨ typedBoundaryFailureWitness
  nonConclusions : Prop
```

## 推奨 Issue 分解

1. `SFTClockedCone.lean` へ clocked cone core を分離する
2. `BinaryFieldCover` と `global_ext` を追加する
3. support / relation projection predicate を追加する
4. global clocked path projection theorem を証明する
5. `CompatibleBinaryClockedConeFamily` を定義する
6. local clocked path glue API を定義する
7. `forecastCone_descent_binary` を selected equivalence で証明する
8. `BinaryForecastConeDescentPackage.ofAssumptions` を追加する
9. `SFTModuleBoundary` を descent で定義し、representation theorem を整理する
10. descent obstruction を actual no-lift / local-identification failure に接続する
11. minimal envelope を quotient/setoid で実装する
12. governance synthesis を support transformation に接続する
13. closed-loop fixed point を finite height / well-founded refinement で証明する
14. artifact Yoneda を separating probe theorem として実装する
15. agentic confluence を rewriting normal form と接続する
16. Fundamental Modularity package を theorem family から構成する

## 追補: Binary local-to-global gluing core

`Formal/Arch/Evolution/SFTDescent.lean` の binary descent surface は、local-to-global
glue function 全体を丸ごと仮定する段階から一歩進み、次の concrete core を持つ。

```text
CompatibleLocalClockedStep
CompatibleLocalClockedPath
BinarySFTModel.projectedClockedPaths_tickwiseCompatible
BinaryClockedStepGluingData
BinaryClockedStepGluingData.glueCompatibleLocalClockedPath
glueCompatibleBinaryClockedConeFamily
BinaryProjectionGluingLaws
BinaryProjectionGluingEquivalenceLaws
BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws
BinaryDescentAssumptions.ofStepGluing
BinaryDescentAssumptions.ofEndpointLaws
forecastCone_descent_binary_of_endpoint_laws
```

これにより、compatible local cone family から global cone point への path gluing は
`BinaryClockedStepGluingData` から構成される。まだ無条件の global descent ではない。
projection/gluing inverse laws は endpoint-level の `BinaryProjectionGluingLaws` から
selected equivalence assumptions として構成できる。ただし strict path-level inverse laws は
future proof obligation として残る。

## PR 前チェック

Lean 変更を含む PR では必ず実行する。

```bash
lake build
git diff --check
rg -n '\b(axiom|admit|sorry|unsafe)\b' Formal
rg -nP '[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}\x{FEFF}]' Formal docs
```

docs 更新も必須。

```text
Formal.lean
Formal/Arch/Evolution/SFTTheoremPackages.lean
docs/aat/lean_theorem_index.md
docs/aat/proof_obligations.md
docs/sft/sft_theorem_roadmap_and_research_vision.md
```

## 成功条件

第一の成功条件:

```text
Binary cover 上で、
前提群から ClockedForecastCone descent equivalence を構成できる。
```

Lean 上では次があること。

```lean
forecastCone_descent_binary :
  BinaryDescentAssumptions cover model source h ->
    ConeEquivalence
      (ClockedConePoint globalSupport globalRelation source h)
      (CompatibleBinaryClockedConeFamily cover model source h)
```

または strict equality で可能なら:

```lean
forecastCone_descent_binary :
  BinaryDescentAssumptions cover model source h ->
    BidirectionalEquivalence
      (ClockedConePoint globalSupport globalRelation source h)
      (CompatibleBinaryClockedConeFamily cover model source h)
```

最終成功条件:

```text
FundamentalModularityTheoremPackage が、
単なる field bundle ではなく、
ForecastCone descent / obstruction / envelope / governance / fixed point theorem family
から構成される。
```

この状態になって初めて、

```text
SFT roadmap の最終形に近づいた
```

と言える。
```
