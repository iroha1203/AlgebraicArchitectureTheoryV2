import Formal.Arch.Evolution.SFTFiniteExactModel

/-!
Concrete finite Cech cochain vocabulary for selected SFT cones.

This module connects the existing finite-cover simplex skeleton to concrete
cone-valued 0/1-cochains, cocycle predicates, and coboundary witnesses.  It is
not a full cohomology theorem and does not prove `H1 = 0 -> finite descent`.
-/

namespace Formal.Arch

universe u v w x y

/--
Concrete 0-cochain of selected local exact cones over the finite Cech
0-simplices.
-/
structure CechCone0
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  localTarget : Cech0Simplex cover -> Local
  localPath :
    (simplex : Cech0Simplex cover) ->
      ClockedFieldPath model.localSupport model.localRelation
        (cover.restrict simplex.i source) (localTarget simplex)
  localCone :
    (simplex : Cech0Simplex cover) ->
      ClockedForecastCone model.localSupport model.localRelation
        (cover.restrict simplex.i source) horizon
        (localTarget simplex) (localPath simplex)
  zeroBoundary : Prop
  nonConclusions : Prop

namespace CechCone0

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}
variable {model : FiniteSFTModel cover OperationG OperationL}
variable {source : Global} {horizon : Nat}

/-- Build a 0-cochain from an existing compatible finite local family. -/
def ofFiniteLocalFamily
    (family : FiniteLocalClockedConeFamily cover model source horizon) :
    CechCone0 model source horizon where
  localTarget := fun simplex =>
    family.localTarget simplex.i simplex.i_mem
  localPath := fun simplex =>
    family.localPath simplex.i simplex.i_mem
  localCone := fun simplex =>
    family.localCone simplex.i simplex.i_mem
  zeroBoundary := family.coversIndices
  nonConclusions := family.nonConclusions

/-- Build a 0-cochain by projecting a global cone point to every 0-simplex. -/
def ofGlobalConePoint
    (point :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon) :
    CechCone0 model source horizon where
  localTarget := fun simplex => cover.restrict simplex.i point.target
  localPath := fun simplex =>
    model.projectClockedPathLocal simplex.i simplex.i_mem point.path
  localCone := fun simplex =>
    model.projectClockedForecastCone_local
      simplex.i simplex.i_mem point.coneMember
  zeroBoundary := cover.coversGlobal
  nonConclusions := cover.nonConclusions ∧ model.nonConclusions

/-- Every local path in a 0-cochain has the selected exact horizon. -/
theorem local_length_eq_horizon
    (cochain : CechCone0 model source horizon)
    (simplex : Cech0Simplex cover) :
    ArchitecturePath.length (cochain.localPath simplex) = horizon :=
  ClockedForecastCone.length_eq_horizon (cochain.localCone simplex)

end CechCone0

/--
Concrete 1-cochain / overlap compatibility data over finite Cech 1-simplices.

The coefficient object remains the selected local cone family; the overlap
comparison itself is a boundary predicate because later issues provide the
cohomology theorem.
-/
structure CechCone1
    {Global : Type u} {Index : Type v} {Local : Type w}
    (cover : UniformFiniteFieldCover Global Index Local)
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  overlapCompatible : Cech1Simplex cover -> Prop
  overlapBoundary : Cech1Simplex cover -> Prop
  oneBoundary : Prop
  nonConclusions : Prop

namespace CechCone1

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}
variable {model : FiniteSFTModel cover OperationG OperationL}
variable {source : Global} {horizon : Nat}

/-- Build a 1-cochain boundary surface from an existing finite local family. -/
def ofFiniteLocalFamily
    (family : FiniteLocalClockedConeFamily cover model source horizon) :
    CechCone1 cover model source horizon where
  overlapCompatible := fun _simplex => family.pairwiseCompatible
  overlapBoundary := fun simplex => simplex.overlapNonempty
  oneBoundary := family.cechCompatibilityBoundary
  nonConclusions := family.nonConclusions

end CechCone1

/-- A concrete Cech cone cocycle is overlap compatibility on every 1-simplex. -/
def IsCechConeCocycle
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (_zero : CechCone0 model source horizon)
    (one : CechCone1 cover model source horizon) : Prop :=
  (∀ simplex : Cech1Simplex cover, one.overlapCompatible simplex) ∧
    one.oneBoundary

/--
Concrete coboundary witness: a global cone point whose selected local
projections agree with the 0-cochain targets.
-/
structure CechConeCoboundary
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (zero : CechCone0 model source horizon) where
  globalPoint :
    ClockedConePoint model.globalSupport model.globalRelation
      source horizon
  target_agrees :
    ∀ simplex : Cech0Simplex cover,
      zero.localTarget simplex = cover.restrict simplex.i globalPoint.target
  coboundaryBoundary : Prop
  nonConclusions : Prop

/-- Predicate form for a selected Cech cone coboundary. -/
def IsCechConeCoboundary
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (zero : CechCone0 model source horizon) : Prop :=
  Nonempty (CechConeCoboundary zero)

namespace CechConeCoboundary

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}
variable {model : FiniteSFTModel cover OperationG OperationL}
variable {source : Global} {horizon : Nat}

/-- A projected global cone point is a selected coboundary witness. -/
def ofGlobalConePoint
    (point :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon) :
    CechConeCoboundary (CechCone0.ofGlobalConePoint point) where
  globalPoint := point
  target_agrees := fun _simplex => rfl
  coboundaryBoundary := cover.coversGlobal
  nonConclusions := cover.nonConclusions ∧ model.nonConclusions

/-- Projecting a global cone point gives the predicate form of coboundary. -/
theorem isCoboundary_of_globalConePoint
    (point :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon) :
    IsCechConeCoboundary (CechCone0.ofGlobalConePoint point) :=
  ⟨ofGlobalConePoint point⟩

end CechConeCoboundary

/-- Existing finite local family compatibility gives a concrete cocycle predicate. -/
theorem cechConeCocycle_of_finiteLocalFamily
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (family : FiniteLocalClockedConeFamily cover model source horizon)
    (hCompatible : family.pairwiseCompatible)
    (hBoundary : family.cechCompatibilityBoundary) :
    IsCechConeCocycle
      (CechCone0.ofFiniteLocalFamily family)
      (CechCone1.ofFiniteLocalFamily family) :=
  ⟨fun _simplex => hCompatible, hBoundary⟩

end Formal.Arch
