import Formal.Arch.Evolution.SFTDescent

/-!
Finite-cover SFT descent skeleton over exact clocked cones.

This module extends the binary descent surface to a concrete finite-cover,
Cech-style skeleton.  It intentionally stops at selected finite gluing and
compatibility laws: it does not assert that every finite cover satisfies
descent, and it does not implement full Cech cohomology.
-/

namespace Formal.Arch

universe u v w x y

/--
A uniform finite field cover with one local carrier.

`indices` is the concrete finite witness.  The cover and non-conclusion fields
remain selected boundary propositions rather than topological completeness
theorems.
-/
structure UniformFiniteFieldCover
    (Global : Type u) (Index : Type v) (Local : Type w) where
  indices : List Index
  restrict : Index -> Global -> Local
  coversGlobal : Prop
  finiteBoundary : Prop
  nonConclusions : Prop

namespace UniformFiniteFieldCover

/-- The selected finite cover records its global coverage boundary. -/
def RecordsCoverage
    {Global : Type u} {Index : Type v} {Local : Type w}
    (cover : UniformFiniteFieldCover Global Index Local) : Prop :=
  cover.coversGlobal

/-- The selected finite cover records its finite-witness boundary. -/
def RecordsFiniteBoundary
    {Global : Type u} {Index : Type v} {Local : Type w}
    (cover : UniformFiniteFieldCover Global Index Local) : Prop :=
  cover.finiteBoundary

/-- Finite-cover non-conclusions remain explicit. -/
def RecordsNonConclusions
    {Global : Type u} {Index : Type v} {Local : Type w}
    (cover : UniformFiniteFieldCover Global Index Local) : Prop :=
  cover.nonConclusions

end UniformFiniteFieldCover

/-- A selected 0-simplex of the finite Cech nerve skeleton. -/
structure Cech0Simplex
    {Global : Type u} {Index : Type v} {Local : Type w}
    (cover : UniformFiniteFieldCover Global Index Local) where
  i : Index
  i_mem : i ∈ cover.indices

/-- A selected 1-simplex / overlap of the finite Cech nerve skeleton. -/
structure Cech1Simplex
    {Global : Type u} {Index : Type v} {Local : Type w}
    (cover : UniformFiniteFieldCover Global Index Local) where
  i : Index
  j : Index
  i_mem : i ∈ cover.indices
  j_mem : j ∈ cover.indices
  overlapNonempty : Prop

/-- A selected 2-simplex / triple overlap of the finite Cech nerve skeleton. -/
structure Cech2Simplex
    {Global : Type u} {Index : Type v} {Local : Type w}
    (cover : UniformFiniteFieldCover Global Index Local) where
  i : Index
  j : Index
  k : Index
  i_mem : i ∈ cover.indices
  j_mem : j ∈ cover.indices
  k_mem : k ∈ cover.indices
  tripleOverlapNonempty : Prop

/--
Finite-cover SFT model with uniform local support and relation.

The projection laws are theorem-bearing fields for each selected cover index.
-/
structure FiniteSFTModel
    {Global : Type u} {Index : Type v} {Local : Type w}
    (cover : UniformFiniteFieldCover Global Index Local)
    (OperationG : Type x) (OperationL : Type y) where
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

namespace FiniteSFTModel

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}

/-- Project one global clocked step to the selected local index. -/
def projectClockedStepLocal
    (model : FiniteSFTModel cover OperationG OperationL)
    (i : Index) (hIndex : i ∈ cover.indices) :
    {g₀ g₁ : Global} ->
      ClockedFieldStep model.globalSupport model.globalRelation g₀ g₁ ->
        ClockedFieldStep model.localSupport model.localRelation
          (cover.restrict i g₀) (cover.restrict i g₁)
  | _, _, ClockedFieldStep.active step =>
      ClockedFieldStep.active
        { operation := model.projectLocalOp i step.operation
          supported :=
            model.global_support_projects_local
              i _ step.operation hIndex step.supported
          realizes :=
            model.global_step_projects_local
              i hIndex step.supported step.realizes }
  | g, _, ClockedFieldStep.idle _ =>
      ClockedFieldStep.idle (cover.restrict i g)

/-- Project a global clocked path to the selected local index. -/
def projectClockedPathLocal
    (model : FiniteSFTModel cover OperationG OperationL)
    (i : Index) (hIndex : i ∈ cover.indices) :
    {g₀ g₁ : Global} ->
      ClockedFieldPath model.globalSupport model.globalRelation g₀ g₁ ->
        ClockedFieldPath model.localSupport model.localRelation
          (cover.restrict i g₀) (cover.restrict i g₁)
  | _, _, ArchitecturePath.nil g => ArchitecturePath.nil (cover.restrict i g)
  | _, _, ArchitecturePath.cons step rest =>
      ArchitecturePath.cons
        (projectClockedStepLocal model i hIndex step)
        (projectClockedPathLocal model i hIndex rest)

/-- Local projection preserves the exact number of clock ticks. -/
@[simp] theorem projectClockedPathLocal_length
    (model : FiniteSFTModel cover OperationG OperationL)
    (i : Index) (hIndex : i ∈ cover.indices) :
    {g₀ g₁ : Global} ->
      (path :
        ClockedFieldPath model.globalSupport model.globalRelation g₀ g₁) ->
        ArchitecturePath.length
            (projectClockedPathLocal model i hIndex path) =
          ArchitecturePath.length path
  | _, _, ArchitecturePath.nil _ => rfl
  | _, _, ArchitecturePath.cons _ rest => by
      simp [projectClockedPathLocal, ArchitecturePath.length,
        projectClockedPathLocal_length model i hIndex rest]

/-- Exact global clocked cone membership projects to local exact membership. -/
theorem projectClockedForecastCone_local
    (model : FiniteSFTModel cover OperationG OperationL)
    (i : Index) (hIndex : i ∈ cover.indices)
    {source target : Global} {horizon : Nat}
    {path :
      ClockedFieldPath model.globalSupport model.globalRelation source target}
    (hCone :
      ClockedForecastCone model.globalSupport model.globalRelation
        source horizon target path) :
    ClockedForecastCone model.localSupport model.localRelation
      (cover.restrict i source) horizon (cover.restrict i target)
      (projectClockedPathLocal model i hIndex path) := by
  simpa [ClockedForecastCone, ExactClockedFieldPath] using hCone

end FiniteSFTModel

/-- One local exact cone datum at a selected finite cover index. -/
structure FiniteLocalConeDatum
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  index : Index
  index_mem : index ∈ cover.indices
  target : Local
  path :
    ClockedFieldPath model.localSupport model.localRelation
      (cover.restrict index source) target
  coneMember :
    ClockedForecastCone model.localSupport model.localRelation
      (cover.restrict index source) horizon target path
  nonConclusions : Prop

/--
Finite compatible local cone family.

The function fields provide one local exact cone point for each selected index.
The compatibility predicate is intentionally selected and Cech-style rather
than a fully implemented cochain condition.
-/
structure FiniteLocalClockedConeFamily
    {Global : Type u} {Index : Type v} {Local : Type w}
    (cover : UniformFiniteFieldCover Global Index Local)
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  localTarget :
    (i : Index) -> i ∈ cover.indices -> Local
  localPath :
    (i : Index) -> (hIndex : i ∈ cover.indices) ->
      ClockedFieldPath model.localSupport model.localRelation
        (cover.restrict i source) (localTarget i hIndex)
  localCone :
    (i : Index) -> (hIndex : i ∈ cover.indices) ->
      ClockedForecastCone model.localSupport model.localRelation
        (cover.restrict i source) horizon
        (localTarget i hIndex) (localPath i hIndex)
  data : List (FiniteLocalConeDatum model source horizon)
  coversIndices : Prop
  pairwiseCompatible : Prop
  cechCompatibilityBoundary : Prop
  nonConclusions : Prop

namespace FiniteLocalClockedConeFamily

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}
variable {model : FiniteSFTModel cover OperationG OperationL}
variable {source : Global} {horizon : Nat}

/-- A finite local family exposes exact clock length at every selected index. -/
theorem local_length_eq_horizon
    (family : FiniteLocalClockedConeFamily cover model source horizon)
    (i : Index) (hIndex : i ∈ cover.indices) :
    ArchitecturePath.length (family.localPath i hIndex) = horizon :=
  ClockedForecastCone.length_eq_horizon (family.localCone i hIndex)

end FiniteLocalClockedConeFamily

/-- Project a global cone point to its finite local cone family. -/
def projectGlobalConePointToFiniteFamily
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    {source : Global} {horizon : Nat}
    (point :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon) :
    FiniteLocalClockedConeFamily cover model source horizon where
  localTarget := fun i _hIndex => cover.restrict i point.target
  localPath := fun i hIndex =>
    model.projectClockedPathLocal i hIndex point.path
  localCone := fun i hIndex =>
    model.projectClockedForecastCone_local i hIndex point.coneMember
  data := []
  coversIndices := True
  pairwiseCompatible := True
  cechCompatibilityBoundary := cover.finiteBoundary
  nonConclusions := cover.nonConclusions ∧ model.nonConclusions

/--
Selected finite local-to-global gluing data.

At this stage the global cone point is supplied by explicit finite gluing data.
Future work can construct it from iterated binary gluing.
-/
structure FiniteClockedGluingData
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL) where
  glueFamily :
    ∀ {source : Global} {horizon : Nat},
      FiniteLocalClockedConeFamily cover model source horizon ->
        ClockedConePoint model.globalSupport model.globalRelation
          source horizon
  projection_glue_boundary : Prop
  local_compatibility_boundary : Prop
  finite_cover_boundary : Prop
  nonConclusions : Prop

/-- Selected equivalence data for global cone points in finite descent. -/
structure FiniteGlobalConeEquivalenceData
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  related :
    ClockedConePoint model.globalSupport model.globalRelation source horizon ->
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon ->
        Prop
  refl : ∀ point, related point point
  symm : ∀ {left right}, related left right -> related right left
  trans :
    ∀ {left middle right},
      related left middle -> related middle right -> related left right
  nonConclusions : Prop

/-- Selected equivalence data for finite compatible local cone families. -/
structure FiniteLocalFamilyEquivalenceData
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  related :
    FiniteLocalClockedConeFamily cover model source horizon ->
      FiniteLocalClockedConeFamily cover model source horizon ->
        Prop
  refl : ∀ family, related family family
  symm : ∀ {left right}, related left right -> related right left
  trans :
    ∀ {left middle right},
      related left middle -> related middle right -> related left right
  nonConclusions : Prop

/-- Selected finite projection/gluing laws for Cech-style descent. -/
structure FiniteProjectionGluingLaws
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    (glueData : FiniteClockedGluingData model) where
  globalEquiv :
    ∀ (source : Global) (horizon : Nat),
      FiniteGlobalConeEquivalenceData model source horizon
  localEquiv :
    ∀ (source : Global) (horizon : Nat),
      FiniteLocalFamilyEquivalenceData model source horizon
  glue_project_after_projection :
    ∀ {source : Global} {horizon : Nat}
      (point :
        ClockedConePoint model.globalSupport model.globalRelation
          source horizon),
      (globalEquiv source horizon).related
        (glueData.glueFamily
          (projectGlobalConePointToFiniteFamily model point))
        point
  project_after_glue :
    ∀ {source : Global} {horizon : Nat}
      (family : FiniteLocalClockedConeFamily cover model source horizon),
      (localEquiv source horizon).related
        (projectGlobalConePointToFiniteFamily model
          (glueData.glueFamily family))
        family
  cechCompatibilityBoundary : Prop
  finiteDescentBoundary : Prop
  nonConclusions : Prop

/--
Finite-cover ForecastCone descent from selected finite gluing and Cech-style
compatibility laws.
-/
def forecastCone_descent_finite_of_laws
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    (glueData : FiniteClockedGluingData model)
    (laws : FiniteProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat} :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation
        source horizon)
      (FiniteLocalClockedConeFamily cover model source horizon) where
  toFun := projectGlobalConePointToFiniteFamily model
  invFun := glueData.glueFamily
  leftRelated := (laws.globalEquiv source horizon).related
  rightRelated := (laws.localEquiv source horizon).related
  left_refl := (laws.globalEquiv source horizon).refl
  left_symm := (laws.globalEquiv source horizon).symm
  left_trans := (laws.globalEquiv source horizon).trans
  right_refl := (laws.localEquiv source horizon).refl
  right_symm := (laws.localEquiv source horizon).symm
  right_trans := (laws.localEquiv source horizon).trans
  left_related := laws.glue_project_after_projection
  right_related := laws.project_after_glue
  equivalenceBoundary :=
    laws.cechCompatibilityBoundary ∧ laws.finiteDescentBoundary
  nonConclusions :=
    glueData.nonConclusions ∧ laws.nonConclusions

/-- A selected package wrapping finite-cover ForecastCone descent. -/
structure FiniteSelectedForecastConeDescentPackage
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  descentEquivalence :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation
        source horizon)
      (FiniteLocalClockedConeFamily cover model source horizon)
  packageBoundary : Prop
  nonConclusions : Prop

namespace FiniteSelectedForecastConeDescentPackage

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}
variable {model : FiniteSFTModel cover OperationG OperationL}

/-- Build the selected finite-cover descent package from explicit laws. -/
def ofLaws
    (glueData : FiniteClockedGluingData model)
    (laws : FiniteProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat} :
    FiniteSelectedForecastConeDescentPackage model source horizon where
  descentEquivalence :=
    forecastCone_descent_finite_of_laws glueData laws
  packageBoundary :=
    laws.cechCompatibilityBoundary ∧ laws.finiteDescentBoundary ∧
      glueData.projection_glue_boundary ∧
        glueData.local_compatibility_boundary ∧
          glueData.finite_cover_boundary
  nonConclusions :=
    glueData.nonConclusions ∧ laws.nonConclusions

end FiniteSelectedForecastConeDescentPackage

/-- Existence wrapper for selected finite-cover descent under explicit laws. -/
theorem finiteForecastConeDescentPackage_of_laws
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    (glueData : FiniteClockedGluingData model)
    (laws : FiniteProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat} :
    Nonempty (FiniteSelectedForecastConeDescentPackage model source horizon) :=
  ⟨FiniteSelectedForecastConeDescentPackage.ofLaws glueData laws⟩

/--
A binary cover can be read as a two-index finite cover skeleton with a sum
local carrier.

This is only a cover-level bridge.  It does not transport binary descent laws
into finite descent laws by itself.
-/
def finiteCoverOfBinaryCover
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    (cover : BinaryFieldCover Global Left Right Interface) :
    UniformFiniteFieldCover Global Bool (Sum Left Right) where
  indices := [false, true]
  restrict := fun side global =>
    if side then
      Sum.inr (cover.restrictRight global)
    else
      Sum.inl (cover.restrictLeft global)
  coversGlobal := cover.coverBoundary
  finiteBoundary := True
  nonConclusions := cover.nonConclusions

/-- Boundary package for reading a binary cover as a finite-cover skeleton. -/
structure BinaryAsFiniteCoverPackage
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    (cover : BinaryFieldCover Global Left Right Interface) where
  finiteCover : UniformFiniteFieldCover Global Bool (Sum Left Right)
  binaryToFiniteBoundary : Prop
  nonConclusions : Prop

/-- Package the cover-level binary-as-finite bridge. -/
def binaryAsFiniteCoverPackage
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    (cover : BinaryFieldCover Global Left Right Interface) :
  BinaryAsFiniteCoverPackage cover where
  finiteCover := finiteCoverOfBinaryCover cover
  binaryToFiniteBoundary := cover.coverBoundary
  nonConclusions := cover.nonConclusions

/--
Bridge predicate connecting the finite Cech skeleton to the existing abstract
cohomology package surface.
-/
structure FiniteCechDescentCohomologyBridge
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL) where
  H1Vanishes : Prop
  allCompatibleLocalFuturesGlue : Prop
  h1_vanishes_iff_finiteDescent :
    H1Vanishes ↔ allCompatibleLocalFuturesGlue
  bridgeBoundary : Prop
  nonConclusions : Prop

namespace FiniteCechDescentCohomologyBridge

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}
variable {model : FiniteSFTModel cover OperationG OperationL}

/-- The bridge exposes the selected forward cohomology-to-descent reading. -/
theorem finiteDescent_of_h1_vanishes
    (bridge : FiniteCechDescentCohomologyBridge model)
    (h : bridge.H1Vanishes) :
    bridge.allCompatibleLocalFuturesGlue :=
  bridge.h1_vanishes_iff_finiteDescent.mp h

/-- The bridge exposes the selected reverse descent-to-cohomology reading. -/
theorem h1_vanishes_of_finiteDescent
    (bridge : FiniteCechDescentCohomologyBridge model)
    (h : bridge.allCompatibleLocalFuturesGlue) :
    bridge.H1Vanishes :=
  bridge.h1_vanishes_iff_finiteDescent.mpr h

end FiniteCechDescentCohomologyBridge

end Formal.Arch
