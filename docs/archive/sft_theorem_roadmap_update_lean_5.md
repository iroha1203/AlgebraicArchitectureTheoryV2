# SFT Roadmap 残タスク実装指示書 5

## 目的

現在の Lean 実装は、binary cover 上の ForecastCone descent について次の段階まで到達している。

- binary local-to-global path gluing
- endpoint-level inverse-law constructor
- selected path-level inverse-law constructor
- roadmap-facing binary descent accessors

この指示書 5 の目的は、次へ進むこと。

```text
binary cover から finite cover / Cech-style descent skeleton へ拡張する
```

ただし、いきなり一般 category-theoretic limit や sheaf cohomology を導入しない。まずは finite index、finite overlap、compatible local family、selected descent constructor を concrete API として置く。

---

## 現在の claim boundary

まだ次のようには言わない。

```text
Full Cech descent is proved.
All finite covers satisfy ForecastCone descent.
Cone cohomology theorem is fully proved.
Fundamental Modularity Theorem is fully proved.
```

現在言えること:

```text
Binary ForecastCone descent has endpoint-level and selected path-level inverse-law constructors.
```

この指示書 5 の完了後に言いたいこと:

```text
Finite-cover ForecastCone descent has a concrete Cech-style skeleton and selected finite-cover descent package.
```

---

## Phase 1: finite cover skeleton を定義する

追加先:

```text
Formal/Arch/Evolution/SFTFiniteCover.lean
```

または最初は既存ファイルに置く場合:

```text
Formal/Arch/Evolution/SFTDescent.lean
```

推奨は新規ファイル。

```lean
import Formal.Arch.Evolution.SFTDescent

namespace Formal.Arch

structure FiniteFieldCover
    (Global : Type u) (Index : Type v)
    (Local : Index -> Type w) where
  indices : List Index
  mem_indices : Index -> Prop
  restrict : (i : Index) -> Global -> Local i
  coversGlobal : Prop
  finiteBoundary : Prop
  nonConclusions : Prop
```

注意:

- `indices : List Index` は concrete finite witness として使う。
- `mem_indices` は list membership にしてもよいが、最初は selected predicate でよい。
- local type が index dependent になると実装が重くなる場合は、まず同一 local carrier 版にしてよい。

軽量版:

```lean
structure UniformFiniteFieldCover
    (Global : Type u) (Index : Type v) (Local : Type w) where
  indices : List Index
  restrict : Index -> Global -> Local
  coversGlobal : Prop
  finiteBoundary : Prop
  nonConclusions : Prop
```

最初の実装では `UniformFiniteFieldCover` を推奨する。

---

## Phase 2: finite overlap / Cech simplex を定義する

最初に必要なのは 0-simplex と 1-simplex。

```lean
structure Cech0Simplex
    (cover : UniformFiniteFieldCover Global Index Local) where
  i : Index
  i_mem : i ∈ cover.indices

structure Cech1Simplex
    (cover : UniformFiniteFieldCover Global Index Local) where
  i : Index
  j : Index
  i_mem : i ∈ cover.indices
  j_mem : j ∈ cover.indices
  overlapNonempty : Prop
```

triple overlap は後で cohomology theorem へ接続するために入れる。

```lean
structure Cech2Simplex
    (cover : UniformFiniteFieldCover Global Index Local) where
  i : Index
  j : Index
  k : Index
  i_mem : i ∈ cover.indices
  j_mem : j ∈ cover.indices
  k_mem : k ∈ cover.indices
  tripleOverlapNonempty : Prop
```

ここではまだ topological cover ではない。software field の selected finite cover skeleton として読む。

---

## Phase 3: finite local cone family を定義する

binary 版の `CompatibleBinaryClockedConeFamily` に対応する finite 版を作る。

```lean
structure FiniteLocalClockedConeFamily
    (cover : UniformFiniteFieldCover Global Index Local)
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  localTarget :
    (i : Index) -> i ∈ cover.indices -> Local
  localPath :
    (i : Index) -> (h : i ∈ cover.indices) ->
      ClockedFieldPath model.localSupport model.localRelation
        (cover.restrict i source) (localTarget i h)
  localCone :
    (i : Index) -> (h : i ∈ cover.indices) ->
      ClockedForecastCone model.localSupport model.localRelation
        (cover.restrict i source) horizon
        (localTarget i h) (localPath i h)
  pairwiseCompatible : Prop
  nonConclusions : Prop
```

依存型が重い場合は、まず local target/path を opaque package としてよい。

```lean
structure FiniteLocalConeDatum where
  index : Index
  index_mem : index ∈ cover.indices
  target : Local
  path : ClockedFieldPath ...
  coneMember : ClockedForecastCone ...
```

そして:

```lean
structure FiniteLocalClockedConeFamily where
  data : List FiniteLocalConeDatum
  coversIndices : Prop
  pairwiseCompatible : Prop
  nonConclusions : Prop
```

最初は list-based package の方が実装しやすい。

---

## Phase 4: finite SFT model を定義する

binary の `BinarySFTModel` に対応する finite 版を作る。

```lean
structure FiniteSFTModel
    (cover : UniformFiniteFieldCover Global Index Local)
    (OperationG : Type u) (OperationL : Type v) where
  globalSupport : OperationSupport Global OperationG
  globalRelation : StepRelation Global OperationG
  localSupport : OperationSupport Local OperationL
  localRelation : StepRelation Local OperationL
  projectLocalOp : Index -> OperationG -> OperationL
  global_support_projects_local :
    ∀ i g op,
      i ∈ cover.indices ->
      globalSupport.Supports g op ->
        localSupport.Supports (cover.restrict i g) (projectLocalOp i op)
  global_step_projects_local :
    ∀ i {g₀ g₁ : Global} {op : OperationG},
      i ∈ cover.indices ->
      globalSupport.Supports g₀ op ->
      globalRelation.Realizes g₀ op g₁ ->
        localRelation.Realizes
          (cover.restrict i g₀)
          (projectLocalOp i op)
          (cover.restrict i g₁)
  supportBoundary : Prop
  stepBoundary : Prop
  nonConclusions : Prop
```

最初は uniform local support / relation でよい。dependent local type は後で一般化する。

---

## Phase 5: global cone point を finite local family へ射影する

binary の:

```lean
projectGlobalConePointToBinaryFamily
```

に対応する finite 版を作る。

```lean
def projectGlobalConePointToFiniteFamily
    (model : FiniteSFTModel cover OperationG OperationL)
    (point : ClockedConePoint model.globalSupport model.globalRelation source horizon) :
    FiniteLocalClockedConeFamily cover model source horizon
```

必要な補題:

```lean
def projectClockedStepLocal
def projectClockedPathLocal
theorem projectClockedPathLocal_length
theorem projectClockedForecastCone_local
```

binary 版の `projectClockedStepLeft` / `projectClockedPathLeft` / `projectClockedForecastCone_left` を一般化する。

---

## Phase 6: finite local-to-global gluing data を定義する

finite cover では、local family から global cone point を作る gluing data を明示前提にする。

```lean
structure FiniteClockedGluingData
    (model : FiniteSFTModel cover OperationG OperationL) where
  glueFamily :
    ∀ {source horizon},
      FiniteLocalClockedConeFamily cover model source horizon ->
        ClockedConePoint model.globalSupport model.globalRelation source horizon
  projection_glue_boundary : Prop
  local_compatibility_boundary : Prop
  finite_cover_boundary : Prop
  nonConclusions : Prop
```

この段階では、`glueFamily` を完全構成しなくてよい。

重要なのは:

- binary descent の `glueCompatibleBinaryClockedConeFamily` は構成済み。
- finite cover では、まず selected gluing data と finite compatibility law を置く。
- 後続で binary cover の iterated gluing から構成する。

---

## Phase 7: finite-cover relatedness を定義する

endpoint / path law と同じ方針で、finite cover 用の selected equivalence data を置く。

```lean
structure FiniteGlobalConeEquivalenceData
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  related :
    ClockedConePoint model.globalSupport model.globalRelation source horizon ->
    ClockedConePoint model.globalSupport model.globalRelation source horizon ->
      Prop
  refl : ∀ p, related p p
  symm : ∀ {p q}, related p q -> related q p
  trans : ∀ {p q r}, related p q -> related q r -> related p r
  nonConclusions : Prop
```

local family 側:

```lean
structure FiniteLocalFamilyEquivalenceData
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  related :
    FiniteLocalClockedConeFamily cover model source horizon ->
    FiniteLocalClockedConeFamily cover model source horizon ->
      Prop
  refl : ∀ f, related f f
  symm : ∀ {f g}, related f g -> related g f
  trans : ∀ {f g h}, related f g -> related g h -> related f h
  nonConclusions : Prop
```

---

## Phase 8: finite descent laws を定義する

```lean
structure FiniteProjectionGluingLaws
    (model : FiniteSFTModel cover OperationG OperationL)
    (glueData : FiniteClockedGluingData model) where
  globalEquiv :
    ∀ source horizon,
      FiniteGlobalConeEquivalenceData model source horizon
  localEquiv :
    ∀ source horizon,
      FiniteLocalFamilyEquivalenceData model source horizon
  glue_project_after_projection :
    ∀ {source horizon}
      (point : ClockedConePoint model.globalSupport model.globalRelation source horizon),
      (globalEquiv source horizon).related
        (glueData.glueFamily
          (projectGlobalConePointToFiniteFamily model point))
        point
  project_after_glue :
    ∀ {source horizon}
      (family : FiniteLocalClockedConeFamily cover model source horizon),
      (localEquiv source horizon).related
        (projectGlobalConePointToFiniteFamily model
          (glueData.glueFamily family))
        family
  cechCompatibilityBoundary : Prop
  finiteDescentBoundary : Prop
  nonConclusions : Prop
```

この structure が finite-cover descent の中心になる。

---

## Phase 9: finite ForecastCone descent constructor を追加する

binary の:

```lean
forecastCone_descent_binary_of_path_laws
```

に対応して:

```lean
def forecastCone_descent_finite_of_laws
    (glueData : FiniteClockedGluingData model)
    (laws : FiniteProjectionGluingLaws model glueData)
    {source : Global} {horizon : Nat} :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation source horizon)
      (FiniteLocalClockedConeFamily cover model source horizon)
```

`ConeEquivalence` の中身:

- `toFun := projectGlobalConePointToFiniteFamily model`
- `invFun := glueData.glueFamily`
- `leftRelated := (laws.globalEquiv source horizon).related`
- `rightRelated := (laws.localEquiv source horizon).related`
- inverse laws は `laws.glue_project_after_projection` と `laws.project_after_glue`
- boundary は `cechCompatibilityBoundary ∧ finiteDescentBoundary`

---

## Phase 10: selected finite descent package を追加する

```lean
structure FiniteSelectedForecastConeDescentPackage
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  descentEquivalence :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation source horizon)
      (FiniteLocalClockedConeFamily cover model source horizon)
  packageBoundary : Prop
  nonConclusions : Prop
```

constructor:

```lean
def FiniteSelectedForecastConeDescentPackage.ofLaws
    (glueData : FiniteClockedGluingData model)
    (laws : FiniteProjectionGluingLaws model glueData)
    {source : Global} {horizon : Nat} :
    FiniteSelectedForecastConeDescentPackage model source horizon
```

---

## Phase 11: binary cover との bridge を作る

finite cover skeleton が入ったら、binary cover が finite cover の特殊例であることを示す。

最初は完全 bridge でなくてよい。

```lean
def finiteCoverOfBinaryCover
    (cover : BinaryFieldCover Global Left Right Interface) :
    UniformFiniteFieldCover Global Bool (Sum Left Right)
```

または local carrier を揃えるのが難しい場合:

```lean
structure BinaryAsFiniteCoverPackage where
  finiteCover : Type
  binaryToFiniteBoundary : Prop
  nonConclusions : Prop
```

目標:

```lean
theorem binary_descent_as_finite_descent
    ... :
    Nonempty (FiniteSelectedForecastConeDescentPackage ...)
```

この bridge は後続でもよい。指示書 5 の最低限成功条件には含めない。

---

## Phase 12: Cech cohomology package と接続する

既存の `SFTTheoremRoadmap.ConeCohomologyPackage` は abstract package surface。

指示書 5 では、次の接続 predicate だけ置く。

```lean
structure FiniteCechDescentCohomologyBridge
    (model : FiniteSFTModel cover OperationG OperationL) where
  H1Vanishes : Prop
  allCompatibleLocalFuturesGlue : Prop
  h1_vanishes_iff_finiteDescent :
    H1Vanishes ↔ allCompatibleLocalFuturesGlue
  bridgeBoundary : Prop
  nonConclusions : Prop
```

まだ実 cochain complex を完全実装しない。

この段階では:

```text
Cech-style descent skeleton exists
```

まで。

---

## Phase 13: roadmap-facing theorem を追加する

追加先:

```text
Formal/Arch/Evolution/SFTTheoremRoadmap.lean
```

候補:

```lean
theorem finiteForecastConeDescent_of_laws
    (glueData : FiniteClockedGluingData model)
    (laws : FiniteProjectionGluingLaws model glueData)
    {source : Global} {horizon : Nat} :
    Nonempty (FiniteSelectedForecastConeDescentPackage model source horizon)
```

docstring に必ず書く。

```text
This is finite-cover selected descent.
It is not a proof that every finite cover satisfies descent.
It is not full Cech cohomology.
It is not the Fundamental Modularity Theorem.
```

---

## Phase 14: public entrypoint を更新する

更新先:

```text
Formal/Arch/Evolution/SFTTheoremPackages.lean
Formal.lean
```

新規ファイルを作るなら:

```lean
import Formal.Arch.Evolution.SFTFiniteCover
```

representative declarations に追加:

```text
UniformFiniteFieldCover
Cech0Simplex
Cech1Simplex
FiniteSFTModel
FiniteLocalClockedConeFamily
FiniteClockedGluingData
FiniteProjectionGluingLaws
forecastCone_descent_finite_of_laws
FiniteSelectedForecastConeDescentPackage.ofLaws
SFTTheoremRoadmap.finiteForecastConeDescent_of_laws
```

---

## Phase 15: docs を更新する

更新先:

```text
Formal/
Formal/
docs/sft/sft_theorem_roadmap_and_research_vision.md
docs/sft/sft_theorem_roadmap_update_lean_5.md
```

書いてよい表現:

```text
Finite-cover ForecastCone descent has a selected Cech-style skeleton.
```

```text
The finite descent constructor is relative to explicit finite gluing and compatibility laws.
```

まだ書かない表現:

```text
All finite covers satisfy descent.
```

```text
Cech cohomology is fully implemented.
```

```text
Fundamental Modularity Theorem is fully proved.
```

---

## 成功条件

この指示書 5 が完了したと言える条件:

1. `UniformFiniteFieldCover` または `FiniteFieldCover` が追加される。
2. `Cech0Simplex`, `Cech1Simplex`, 必要なら `Cech2Simplex` が追加される。
3. `FiniteSFTModel` が追加される。
4. `FiniteLocalClockedConeFamily` が追加される。
5. global cone point から finite local family への projection が実装される。
6. `FiniteClockedGluingData` が追加される。
7. `FiniteProjectionGluingLaws` が追加される。
8. `forecastCone_descent_finite_of_laws` が追加される。
9. `FiniteSelectedForecastConeDescentPackage.ofLaws` が追加される。
10. roadmap-facing accessor theorem が追加される。
11. theorem index / proof obligations / roadmap docs が更新される。
12. `lake build` が通る。
13. `git diff --check` が通る。
14. Lean source に `axiom`, `admit`, `sorry`, `unsafe` がない。
15. docs が finite cover descent を無条件定理として書いていない。

---

## 完了後に言えること

完了後は、次のように言える。

```text
ForecastCone descent has a finite-cover Cech-style selected descent skeleton.
```

より正確には:

```text
Finite-cover descent can be represented as a selected ConeEquivalence from
global clocked cone points to compatible finite local cone families, under
explicit finite gluing and Cech-compatibility laws.
```

まだ次は言わない。

```text
Cech cohomology theorem is fully proved.
Fundamental Modularity Theorem is fully proved.
```

次の指示書 6 では、finite descent failure を obstruction / cohomology / governance cutting と接続する。

---

## 実装後ステータス

この指示書 5 の Lean 実装は `Formal/Arch/Evolution/SFTFiniteCover.lean`,
`Formal/Arch/Evolution/SFTTheoremRoadmap.lean`, `Formal/Arch/Evolution/SFTTheoremPackages.lean`,
`Formal.lean` に反映済み。

追加された surface:

- `UniformFiniteFieldCover`
- `Cech0Simplex`
- `Cech1Simplex`
- `Cech2Simplex`
- `FiniteSFTModel`
- `FiniteSFTModel.projectClockedStepLocal`
- `FiniteSFTModel.projectClockedPathLocal`
- `FiniteSFTModel.projectClockedPathLocal_length`
- `FiniteSFTModel.projectClockedForecastCone_local`
- `FiniteLocalConeDatum`
- `FiniteLocalClockedConeFamily`
- `projectGlobalConePointToFiniteFamily`
- `FiniteClockedGluingData`
- `FiniteGlobalConeEquivalenceData`
- `FiniteLocalFamilyEquivalenceData`
- `FiniteProjectionGluingLaws`
- `forecastCone_descent_finite_of_laws`
- `FiniteSelectedForecastConeDescentPackage`
- `FiniteSelectedForecastConeDescentPackage.ofLaws`
- `finiteForecastConeDescentPackage_of_laws`
- `finiteCoverOfBinaryCover`
- `BinaryAsFiniteCoverPackage`
- `FiniteCechDescentCohomologyBridge`
- `SFTTheoremRoadmap.finiteForecastConeDescent_of_laws`

言えること:

```text
ForecastCone descent has a finite-cover Cech-style selected descent skeleton.
```

より正確には、finite-cover descent は global clocked cone point から compatible finite local
cone family への selected `ConeEquivalence` として、explicit finite gluing と
Cech-style compatibility laws の下で表現できる。

まだ言わないこと:

```text
All finite covers satisfy descent.
Cech cohomology theorem is fully proved.
Fundamental Modularity Theorem is fully proved.
```

残る future proof obligation:

- definitional path equality or transport-normalized path equality
- all finite covers satisfying descent
- full Cech cohomology theorem / concrete cochain complex
- actual descent failure to obstruction classifier bridge
- governance synthesis integrated with actual obstruction cutting
- closed-loop calibration over concrete finite-height refinement order
- Fundamental Modularity theorem over one integrated SFT model
