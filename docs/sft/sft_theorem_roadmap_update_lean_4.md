# SFT Roadmap 残タスク実装指示書 4

## 目的

現在の Lean 実装は、ForecastCone Descent の binary endpoint-law constructor まで到達している。

すでにあるもの:

- `ClockedForecastCone`
- `BinaryFieldCover`
- `BinarySFTModel`
- `CompatibleLocalClockedStep`
- `CompatibleLocalClockedPath`
- `BinaryClockedStepGluingData`
- `glueCompatibleBinaryClockedConeFamily`
- `GlobalConePointTargetEquivalent`
- `LocalFamilyTargetEquivalent`
- `BinaryProjectionGluingLaws`
- `BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws`
- `BinaryDescentAssumptions.ofEndpointLaws`
- `forecastCone_descent_binary_of_endpoint_laws`
- `binaryForecastConeDescentPackage_of_endpoint_laws`

この指示書 4 の目的は、次へ進むこと。

```text
endpoint equality で止まっている inverse laws を、strict path-level inverse laws へ持ち上げる
```

ただし、いきなり dependent path equality の完全一致を狙わない。まずは path-level setoid または selected path equivalence を定義し、その上で projection/glue の往復が同値になることを証明する。

---

## 現在の claim boundary

まだ次のようには言わない。

```text
ForecastCone descent holds by strict dependent path equality.
Finite-cover descent is proved.
Fundamental Modularity Theorem is fully proved.
```

現在言えること:

```text
Binary ForecastCone descent has a selected equivalence constructor from step-level gluing data and endpoint-level projection/glue laws.
```

この指示書 4 の完了後に言いたいこと:

```text
Binary ForecastCone descent also has strict path-level inverse laws, relative to an explicit selected path equivalence.
```

---

## Phase 1: path-level equivalence を定義する

追加先:

```text
Formal/Arch/Evolution/SFTDescent.lean
```

大きくなりすぎる場合:

```text
Formal/Arch/Evolution/SFTDescentPathLaws.lean
```

まず、global cone point の path-level equivalence を定義する。

```lean
def GlobalConePointPathEquivalent
    (p q : ClockedConePoint model.globalSupport model.globalRelation source horizon) : Prop :=
  p.target = q.target ∧
    HEq p.path q.path
```

ただし `HEq` が扱いにくい場合は、最初は selected relation として structure に持たせる。

```lean
structure GlobalConePointPathEquivalenceData
    {Global Left Right Interface : Type _}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG OperationL OperationR OperationI : Type _}
    (model : BinarySFTModel cover OperationG OperationL OperationR OperationI)
    (source : Global) (horizon : Nat) where
  related :
    ClockedConePoint model.globalSupport model.globalRelation source horizon ->
    ClockedConePoint model.globalSupport model.globalRelation source horizon ->
      Prop
  refl : ∀ p, related p p
  symm : ∀ {p q}, related p q -> related q p
  trans : ∀ {p q r}, related p q -> related q r -> related p r
  impliesEndpoint :
    ∀ {p q}, related p q -> p.target = q.target
  nonConclusions : Prop
```

同様に local family 側も作る。

```lean
structure LocalFamilyPathEquivalenceData
    {Global Left Right Interface : Type _}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG OperationL OperationR OperationI : Type _}
    (model : BinarySFTModel cover OperationG OperationL OperationR OperationI)
    (source : Global) (horizon : Nat) where
  related :
    CompatibleBinaryClockedConeFamily model source horizon ->
    CompatibleBinaryClockedConeFamily model source horizon ->
      Prop
  refl : ∀ f, related f f
  symm : ∀ {f g}, related f g -> related g f
  trans : ∀ {f g h}, related f g -> related g h -> related f h
  impliesEndpoint :
    ∀ {f g}, related f g ->
      f.leftTarget = g.leftTarget ∧ f.rightTarget = g.rightTarget
  nonConclusions : Prop
```

設計方針:

- 最初から definitional equality を要求しない。
- endpoint equality は path equivalence の consequence として出す。
- 将来 `HEq` や transport-normalized equality に強められるようにしておく。

---

## Phase 2: strict path projection/glue law data を追加する

`BinaryProjectionGluingLaws` は endpoint law までを担っている。

その上位として、path-level laws を追加する。

```lean
structure BinaryProjectionGluingPathLaws
    {Global Left Right Interface : Type _}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG OperationL OperationR OperationI : Type _}
    {model : BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (endpointLaws : BinaryProjectionGluingLaws glueData)
    (source : Global) (horizon : Nat) where
  globalPathEquiv :
    GlobalConePointPathEquivalenceData model source horizon
  localPathEquiv :
    LocalFamilyPathEquivalenceData model source horizon
  glue_project_after_projection_path :
    ∀ point,
      globalPathEquiv.related
        (glueCompatibleBinaryClockedConeFamily glueData
          (projectGlobalConePointToBinaryFamily model point))
        point
  project_after_glue_path :
    ∀ family,
      localPathEquiv.related
        (projectGlobalConePointToBinaryFamily model
          (glueCompatibleBinaryClockedConeFamily glueData family))
        family
  strictPathLawBoundary : Prop
  nonConclusions : Prop
```

名前は長くなってもよい。ここは claim boundary を誤読させない方が重要。

---

## Phase 3: endpoint laws への forgetful map を作る

path-level laws があれば endpoint-level laws も得られる、という bridge を作る。

目標:

```lean
def BinaryProjectionGluingPathLaws.toEndpointLaws
    (pathLaws : BinaryProjectionGluingPathLaws glueData endpointLaws source horizon) :
    BinaryProjectionGluingLaws glueData
```

ただし、既存の `BinaryProjectionGluingLaws` は全 `source` / `horizon` に対して endpoint law を要求している可能性がある。

この場合は無理に `toEndpointLaws` を作らず、次のどちらかにする。

1. `BinaryProjectionGluingPathLaws` も全 source / horizon に量化する。
2. `BinaryProjectionGluingPathLawsAt` のような source / horizon 固定版を作り、既存 API へ渡すときだけ必要な形に合わせる。

推奨:

```lean
structure BinaryProjectionGluingPathLaws
    ...
    (glueData : BinaryClockedStepGluingData model) where
  endpointLaws : BinaryProjectionGluingLaws glueData
  globalPathEquiv :
    ∀ source horizon,
      GlobalConePointPathEquivalenceData model source horizon
  localPathEquiv :
    ∀ source horizon,
      LocalFamilyPathEquivalenceData model source horizon
  glue_project_after_projection_path :
    ∀ {source horizon}
      (point : ClockedConePoint model.globalSupport model.globalRelation source horizon),
      (globalPathEquiv source horizon).related
        (glueCompatibleBinaryClockedConeFamily glueData
          (projectGlobalConePointToBinaryFamily model point))
        point
  project_after_glue_path :
    ∀ {source horizon}
      (family : CompatibleBinaryClockedConeFamily model source horizon),
      (localPathEquiv source horizon).related
        (projectGlobalConePointToBinaryFamily model
          (glueCompatibleBinaryClockedConeFamily glueData family))
        family
  strictPathLawBoundary : Prop
  nonConclusions : Prop
```

この shape の方が既存の `BinaryProjectionGluingLaws` と合わせやすい。

---

## Phase 4: path-level ConeEquivalence constructor を追加する

endpoint equivalence 版:

```lean
forecastCone_descent_binary_of_endpoint_laws
```

に対応する path equivalence 版を作る。

```lean
def forecastCone_descent_binary_of_path_laws
    (glueData : BinaryClockedStepGluingData model)
    (pathLaws : BinaryProjectionGluingPathLaws glueData)
    {source : Global} {horizon : Nat} :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation source horizon)
      (CompatibleBinaryClockedConeFamily model source horizon)
```

このとき:

- `leftRelated` は `(pathLaws.globalPathEquiv source horizon).related`
- `rightRelated` は `(pathLaws.localPathEquiv source horizon).related`
- `left_refl` / `symm` / `trans` は path equivalence data から出す
- `right_refl` / `symm` / `trans` も同様
- `left_related` は `glue_project_after_projection_path`
- `right_related` は `project_after_glue_path`
- `equivalenceBoundary` は endpoint boundary と strict path law boundary を両方含む

---

## Phase 5: selected package constructor を追加する

既存:

```lean
BinarySelectedForecastConeDescentPackage.ofEndpointLaws
```

新規:

```lean
def BinarySelectedForecastConeDescentPackage.ofPathLaws
    (glueData : BinaryClockedStepGluingData model)
    (pathLaws : BinaryProjectionGluingPathLaws glueData)
    {source : Global} {horizon : Nat} :
    BinarySelectedForecastConeDescentPackage model source horizon
```

`packageBoundary` には必ず次を含める。

```lean
pathLaws.endpointLaws.lawBoundary
pathLaws.endpointLaws.left_project_glued_step_law
pathLaws.endpointLaws.right_project_glued_step_law
pathLaws.endpointLaws.strictPathInverseLawBoundary
pathLaws.strictPathLawBoundary
```

ここで boundary を落とさないこと。

---

## Phase 6: roadmap-facing theorem を追加する

追加先:

```text
Formal/Arch/Evolution/SFTTheoremRoadmap.lean
```

候補:

```lean
theorem binaryForecastConeDescent_of_path_laws
    (glueData : BinaryClockedStepGluingData model)
    (pathLaws : BinaryProjectionGluingPathLaws glueData)
    {source : Global} {horizon : Nat} :
    Nonempty (BinarySelectedForecastConeDescentPackage model source horizon)
```

説明文には必ず書く。

```text
This is still binary descent.
This is still selected path equivalence.
This is not finite-cover descent.
This is not full Fundamental Modularity Theorem.
```

---

## Phase 7: docs を更新する

更新先:

```text
docs/aat/lean_theorem_index.md
docs/aat/proof_obligations.md
docs/sft/sft_theorem_roadmap_and_research_vision.md
docs/sft/sft_theorem_roadmap_update_lean_4.md
```

書いてよい表現:

```text
Binary ForecastCone descent now has selected path-level inverse laws.
```

```text
The path-level inverse laws are relative to explicit selected path equivalence data.
```

まだ書かない表現:

```text
Strict definitional equality of all projected/glued paths is proved.
```

```text
Finite-cover descent is proved.
```

```text
Fundamental Modularity Theorem is fully proved.
```

---

## Phase 8: proof obligation を更新する

指示書 4 完了後に残る future proof obligation:

```text
Finite-cover / Cech-cover descent
Cohomological obstruction interpretation
Actual descent failure to obstruction classifier bridge
Governance synthesis integrated with actual obstruction cutting
Closed-loop calibration over concrete finite-height refinement order
Fundamental Modularity theorem over one integrated SFT model
```

`strict path-level projection/glue inverse laws` は、完了した場合には future から外す。ただし、もし selected path equivalence に留まるなら次を残す。

```text
Definitional path equality or transport-normalized path equality remains future work.
```

---

## 成功条件

この指示書 4 が完了したと言える条件:

1. `GlobalConePointPathEquivalenceData` が追加される。
2. `LocalFamilyPathEquivalenceData` が追加される。
3. `BinaryProjectionGluingPathLaws` が追加される。
4. path equivalence の refl / symm / trans が `ConeEquivalence` に渡される。
5. glue after projection が global path equivalence で証明される。
6. projection after glue が local path equivalence で証明される。
7. `forecastCone_descent_binary_of_path_laws` が追加される。
8. `BinarySelectedForecastConeDescentPackage.ofPathLaws` が追加される。
9. roadmap-facing accessor theorem が追加される。
10. theorem index / proof obligations / roadmap docs が更新される。
11. `lake build` が通る。
12. `git diff --check` が通る。
13. Lean source に `axiom`, `admit`, `sorry`, `unsafe` がない。
14. docs が「大定理完全証明済み」と書いていない。

---

## 完了後に言えること

完了後は、次のように言える。

```text
Binary ForecastCone descent has a selected path-level inverse-law constructor.
```

より正確には:

```text
The binary descent equivalence can be constructed from step-level gluing data,
endpoint projection/glue laws, and selected path-level inverse laws.
```

まだ次は言わない。

```text
Fundamental Modularity Theorem is fully proved.
```

次の指示書 5 では、finite cover / Cech descent へ進む。

---

## 実装後ステータス

この指示書 4 の Lean 実装は `Formal/Arch/Evolution/SFTDescent.lean` と
`Formal/Arch/Evolution/SFTTheoremRoadmap.lean` に反映済み。

追加された surface:

- `GlobalConePointPathEquivalenceData`
- `LocalFamilyPathEquivalenceData`
- `BinaryProjectionGluingPathLaws`
- `BinaryProjectionGluingPathLaws.toEndpointLaws`
- `BinaryProjectionGluingPathLaws.glue_project_after_projection_endpoint`
- `BinaryProjectionGluingPathLaws.project_after_glue_endpoint`
- `forecastCone_descent_binary_of_path_laws`
- `BinarySelectedForecastConeDescentPackage.ofPathLaws`
- `binaryForecastConeDescentPackage_of_path_laws`
- `SFTTheoremRoadmap.binaryForecastConeDescent_of_path_laws`

言えること:

```text
Binary ForecastCone descent has a selected path-level inverse-law constructor.
```

より正確には、binary descent equivalence は step-level gluing data、endpoint
projection/glue laws、explicit selected path-level inverse laws から構成できる。

まだ言わないこと:

```text
Strict definitional equality of all projected/glued paths is proved.
Finite-cover descent is proved.
Fundamental Modularity Theorem is fully proved.
```

残る future proof obligation:

- definitional path equality or transport-normalized path equality
- finite-cover / Cech-cover descent
- cohomological obstruction interpretation
- actual descent failure to obstruction classifier bridge
- governance synthesis integrated with actual obstruction cutting
- closed-loop calibration over concrete finite-height refinement order
- Fundamental Modularity theorem over one integrated SFT model
