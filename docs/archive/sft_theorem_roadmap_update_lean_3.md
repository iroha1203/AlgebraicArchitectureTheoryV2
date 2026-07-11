# SFT Roadmap 残タスク実装指示書 3

実装状態: この指示書の endpoint-level inverse-law constructor は
`Formal/Arch/Evolution/SFTDescent.lean` に実装済みである。現在の source of truth は
`BinaryProjectionGluingLaws`, `GlobalConePointTargetEquivalent`,
`LocalFamilyTargetEquivalent`, `BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws`,
`BinaryDescentAssumptions.ofEndpointLaws`,
`forecastCone_descent_binary_of_endpoint_laws`,
`binaryForecastConeDescentPackage_of_endpoint_laws` である。

## 目的

現在の Lean 実装は、ForecastCone Descent Theorem の binary local-to-global core まで到達している。

すでにあるもの:

- `ClockedForecastCone`
- `BoundedClockedForecastCone`
- `BinaryFieldCover`
- `BinarySFTModel`
- `CompatibleLocalClockedStep`
- `CompatibleLocalClockedPath`
- `BinaryClockedStepGluingData`
- `glueCompatibleBinaryClockedConeFamily`
- `BinaryProjectionGluingEquivalenceLaws`
- `BinaryDescentAssumptions.ofStepGluing`
- `forecastCone_descent_binary`
- `SFTTheoremRoadmap.*` theorem-package surfaces
- `FundamentalModularityTheoremPackage.ofTheoremFamily`

この指示書 3 の目的は、次の段階へ進むこと。

```text
selected inverse laws を、具体的な projection / glue laws から導出する
```

つまり、`BinaryProjectionGluingEquivalenceLaws` を単なる assumption として渡す状態から、より細かい cover / step gluing law から構成できる状態へ進める。

---

## 現在の claim boundary

まだ次のようには言わない。

```text
Fundamental Modularity Theorem is fully proved.
All SFT roadmap theorems are complete.
ForecastCone descent holds unconditionally.
```

正しい現在地は:

```text
The binary local-to-global path gluing core is implemented.
The selected descent equivalence is constructed under explicit inverse-law assumptions.
The roadmap theorem family is available as theorem-package surfaces.
```

この指示書 3 で狙う改善後の表現は:

```text
The binary descent inverse laws are derived from explicit projection/gluing laws.
```

ただし、まだ finite cover / Cech cover / full fundamental theorem completion ではない。

---

## Phase 1: projection/glue law structure を分離する

追加先:

```text
Formal/Arch/Evolution/SFTDescent.lean
```

大きくなりすぎる場合は新規ファイルに分ける。

```text
Formal/Arch/Evolution/SFTDescentInverseLaws.lean
```

作る structure:

```lean
structure BinaryProjectionGluingLaws
    {Global Left Right Interface : Type _}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG OperationL OperationR OperationI : Type _}
    {model : BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model) where
  left_project_glued_step :
    ∀ {left₀ left₁ : Left} {right₀ right₁ : Right}
      (hSource : cover.compatible left₀ right₀)
      (hTarget : cover.compatible left₁ right₁)
      (stepPair :
        CompatibleLocalClockedStep model
          (left₀ := left₀) (left₁ := left₁)
          (right₀ := right₀) (right₁ := right₁)),
      model.projectClockedStepLeft
        (glueData.glueStep hSource hTarget stepPair) =
        cast
          (by
            simp [cover.glue_left])
          stepPair.leftStep

  right_project_glued_step :
    ∀ {left₀ left₁ : Left} {right₀ right₁ : Right}
      (hSource : cover.compatible left₀ right₀)
      (hTarget : cover.compatible left₁ right₁)
      (stepPair :
        CompatibleLocalClockedStep model
          (left₀ := left₀) (left₁ := left₁)
          (right₀ := right₀) (right₁ := right₁)),
      model.projectClockedStepRight
        (glueData.glueStep hSource hTarget stepPair) =
        cast
          (by
            simp [cover.glue_right])
          stepPair.rightStep

  projected_glued_endpoint_left :
    ∀ family,
      (projectGlobalConePointToBinaryFamily model
        (glueCompatibleBinaryClockedConeFamily glueData family)).leftTarget =
        family.leftTarget

  projected_glued_endpoint_right :
    ∀ family,
      (projectGlobalConePointToBinaryFamily model
        (glueCompatibleBinaryClockedConeFamily glueData family)).rightTarget =
        family.rightTarget

  global_glued_projected_target :
    ∀ point,
      (glueCompatibleBinaryClockedConeFamily glueData
        (projectGlobalConePointToBinaryFamily model point)).target =
        point.target

  lawBoundary : Prop
  nonConclusions : Prop
```

注意:

- 上の `cast` はそのまま通らない可能性が高い。
- まずは exact statement を Lean に合わせて弱めてよい。
- 重要なのは「step-level projection law」「endpoint law」「global target recovery law」を分離すること。
- dependent equality が重い場合は、最初は path equality ではなく endpoint equality だけでよい。

---

## Phase 2: endpoint-based equivalence を定義する

dependent path equality をいきなり狙わない。

まず、global cone point の同値は target equality にする。

```lean
def GlobalConePointTargetEquivalent
    (p q : ClockedConePoint model.globalSupport model.globalRelation source horizon) : Prop :=
  p.target = q.target
```

local family の同値も endpoint equality にする。

```lean
def LocalFamilyTargetEquivalent
    (p q : CompatibleBinaryClockedConeFamily model source horizon) : Prop :=
  p.leftTarget = q.leftTarget ∧ p.rightTarget = q.rightTarget
```

証明する:

```lean
theorem globalConePointTargetEquivalent_refl : ...
theorem globalConePointTargetEquivalent_symm : ...
theorem globalConePointTargetEquivalent_trans : ...

theorem localFamilyTargetEquivalent_refl : ...
theorem localFamilyTargetEquivalent_symm : ...
theorem localFamilyTargetEquivalent_trans : ...
```

これにより、`ConeEquivalence` の relatedness を concrete な同値関係にできる。

---

## Phase 3: projection after glue を endpoint 同値で証明する

目標:

```lean
theorem projected_glued_target_related
    (laws : BinaryProjectionGluingLaws glueData)
    (family : CompatibleBinaryClockedConeFamily model source horizon) :
    LocalFamilyTargetEquivalent
      (projectGlobalConePointToBinaryFamily model
        (glueCompatibleBinaryClockedConeFamily glueData family))
      family
```

基本方針:

- left target は `cover.glue_left` から出す。
- right target は `cover.glue_right` から出す。
- path equality はまだ不要。
- tickwise path が完全に戻ることは後続タスクに残してよい。

---

## Phase 4: glue after projection を endpoint 同値で証明する

目標:

```lean
theorem glued_projected_target_related
    (laws : BinaryProjectionGluingLaws glueData)
    (point : ClockedConePoint model.globalSupport model.globalRelation source horizon) :
    GlobalConePointTargetEquivalent
      (glueCompatibleBinaryClockedConeFamily glueData
        (projectGlobalConePointToBinaryFamily model point))
      point
```

基本方針:

- projected family の target は `cover.restrictLeft point.target` と `cover.restrictRight point.target`。
- glued target は `cover.glue ... (cover.global_compatible point.target)`。
- `cover.glue_restricts_eq point.target` を使う。

これはかなり通しやすいはず。

---

## Phase 5: BinaryProjectionGluingEquivalenceLaws を concrete に構成する

目標:

```lean
def BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData)
    (source : Global) (horizon : Nat) :
    BinaryProjectionGluingEquivalenceLaws glueData source horizon
```

中身:

```lean
globalConePointEquivalent := GlobalConePointTargetEquivalent
localFamilyEquivalent := LocalFamilyTargetEquivalent

globalConePointEquivalent_refl := ...
globalConePointEquivalent_symm := ...
globalConePointEquivalent_trans := ...

localFamilyEquivalent_refl := ...
localFamilyEquivalent_symm := ...
localFamilyEquivalent_trans := ...

projected_glued_related := glued_projected_target_related laws
glued_projected_related := projected_glued_target_related laws
interfaceGlueBoundary := laws.lawBoundary
inverseLawBoundary := laws.lawBoundary
nonConclusions := laws.nonConclusions
```

注意:

名前の向きに注意する。

既存の `BinaryProjectionGluingEquivalenceLaws` では:

```lean
projected_glued_related :
  ∀ point,
    globalConePointEquivalent
      (glueCompatibleBinaryClockedConeFamily glueData
        (projectGlobalConePointToBinaryFamily model point))
      point

glued_projected_related :
  ∀ family,
    localFamilyEquivalent
      (projectGlobalConePointToBinaryFamily model
        (glueCompatibleBinaryClockedConeFamily glueData family))
      family
```

なので、実装時に theorem 名と field 名を逆にしない。

---

## Phase 6: BinaryDescentAssumptions.ofEndpointLaws を作る

目標:

```lean
def BinaryDescentAssumptions.ofEndpointLaws
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData)
    (source : Global) (horizon : Nat) :
    BinaryDescentAssumptions model source horizon :=
  BinaryDescentAssumptions.ofStepGluing
    glueData
    (BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws
      glueData laws source horizon)
```

これで、外から `BinaryProjectionGluingEquivalenceLaws` を直接渡す必要が減る。

---

## Phase 7: forecastCone_descent_binary の concrete constructor を追加する

目標:

```lean
def forecastCone_descent_binary_of_endpoint_laws
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat} :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation source horizon)
      (CompatibleBinaryClockedConeFamily model source horizon) :=
  forecastCone_descent_binary
    (BinaryDescentAssumptions.ofEndpointLaws
      glueData laws source horizon)
```

これにより、レビュー時の読みがかなり改善する。

今まで:

```text
descent equivalence from selected assumptions
```

改善後:

```text
descent equivalence from step gluing data and endpoint projection/glue laws
```

---

## Phase 8: theorem package surface を更新する

更新先:

```text
Formal/Arch/Evolution/SFTTheoremRoadmap.lean
Formal/Arch/Evolution/SFTTheoremPackages.lean
```

追加候補:

```lean
structure BinaryForecastConeDescentEndpointLawPackage where
  glueData : BinaryClockedStepGluingData model
  laws : BinaryProjectionGluingLaws glueData
  descent :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation source horizon)
      (CompatibleBinaryClockedConeFamily model source horizon)
  boundary : Prop
  nonConclusions : Prop
```

または薄く:

```lean
theorem binaryForecastConeDescent_of_endpoint_laws
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData) :
    Nonempty (BinarySelectedForecastConeDescentPackage model source horizon)
```

この段階では、既存 API を壊さず追加にする。

---

## Phase 9: docs を更新する

更新先:

```text
Formal/
Formal/
docs/sft/sft_theorem_roadmap_and_research_vision.md
docs/sft/sft_theorem_roadmap_update_lean_2.md
```

書いてよい表現:

```text
Binary descent inverse laws can now be instantiated by endpoint projection/glue laws.
```

```text
The selected equivalence is endpoint-based; dependent path equality and strict path reconstruction remain future proof obligations.
```

まだ書かない表現:

```text
Full ForecastCone descent is unconditional.
```

```text
All inverse laws are definitional equalities.
```

```text
Fundamental Modularity Theorem is fully proved.
```

---

## Phase 10: proof obligation を明示する

`Formal/` に残すべき future proof obligation:

```text
Strict path-level projection/glue inverse laws
Finite-cover / Cech-cover descent
Cohomological obstruction interpretation
Governance synthesis integrated with actual obstruction cutting
Closed-loop calibration over concrete finite-height refinement order
Fundamental Modularity theorem over one integrated SFT model
```

Lean 側にも必要なら boundary field として残す。

```lean
strictPathInverseLawBoundary : Prop
finiteCoverBoundary : Prop
cohomologyBoundary : Prop
governanceIntegrationBoundary : Prop
closedLoopIntegrationBoundary : Prop
fundamentalIntegrationBoundary : Prop
```

---

## 成功条件

この指示書 3 が完了したと言える条件:

1. `BinaryProjectionGluingLaws` が追加される。
2. global cone point の endpoint equivalence が定義される。
3. compatible local family の endpoint equivalence が定義される。
4. 両方の equivalence relation law が証明される。
5. projection-after-glue が endpoint equivalence で証明される。
6. glue-after-projection が endpoint equivalence で証明される。
7. `BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws` が実装される。
8. `BinaryDescentAssumptions.ofEndpointLaws` が実装される。
9. `forecastCone_descent_binary_of_endpoint_laws` が実装される。
10. theorem index / proof obligations / roadmap docs が更新される。
11. `lake build` が通る。
12. `git diff --check` が通る。
13. Lean source に `axiom`, `admit`, `sorry`, `unsafe` がない。

---

## 完了後に言えること

完了後は、次のように言える。

```text
ForecastCone Descent の binary selected equivalence は、
step-level gluing data と endpoint-level projection/glue laws から構成できる。
```

ただし、まだ次は言わない。

```text
Fundamental Modularity Theorem is fully proved.
```

より正確には:

```text
The binary descent equivalence has moved from arbitrary selected inverse-law assumptions
to endpoint-level inverse laws derived from explicit projection/glue law data.
Strict path-level inverse laws, finite-cover descent, and full fundamental integration remain open.
```
```
