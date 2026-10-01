import ResearchLean.AG.RelativeRepairComposition.OriginalRangeQuotient
import ResearchLean.AG.RelativeRepairComposition.CoverCohomology

/-!
# The original H2 inside the full all-column quotient

The quotient by d1 retains every original face value. Its induced d2 kernel,
rather than the whole quotient, is the original full second cohomology.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace OriginalRangeCohomology
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)] (P : ClosedRegion K)
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
/-- Decide membership in the full original edge region by its universal predicate. -/
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original vertex region by its universal predicate. -/
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original face region by its universal predicate. -/
local instance allFacesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).faces) :=
  fun _ => isTrue trivial
local notation "d1P" => differential1 M hlinear ClosedRegion.all P
local notation "d2bar" => OriginalRangeQuotient.inducedD2 (k := k) M P hlinear

/-- An original cycle maps to its unchanged face representative modulo full d1. -/
noncomputable def cycleMap : CoverCohomology.Z2 M P ClosedRegion.all →+
    LinearMap.ker d2bar where
  toFun z := ⟨(LinearMap.range d1P).mkQ z.1,by
    change differential2 M hlinear ClosedRegion.all P z.1 = 0
    rw [differential2_eq]; exact z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Boundaries vanish by the same original whole edge differential. -/
theorem cycleMap_boundary (h : RelativeCover.C1 M ClosedRegion.all P) :
    cycleMap (k := k) M P hlinear (CoverCohomology.boundary2 M P ClosedRegion.all h) = 0 := by
  apply Subtype.ext
  change (LinearMap.range d1P).mkQ (RelativeCover.d1 M ClosedRegion.all P h) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ⟨h,differential1_eq M hlinear ClosedRegion.all P h⟩

/-- Descend the full cycle map through exactly the original boundary subgroup. -/
noncomputable def classMap : CoverCohomology.H2 M P ClosedRegion.all →+
    LinearMap.ker d2bar :=
  QuotientAddGroup.lift (CoverCohomology.boundary2 M P ClosedRegion.all).range
    (cycleMap (k := k) M P hlinear) (by
      rintro _ ⟨h,rfl⟩; exact cycleMap_boundary (k := k) M P hlinear h)

/-- Every cycle class keeps its complete original face representative. -/
theorem classMap_value (z : CoverCohomology.Z2 M P ClosedRegion.all) :
    (classMap (k := k) M P hlinear (QuotientAddGroup.mk z)).1 =
      (LinearMap.range d1P).mkQ z.1 := rfl

/-- The cycle class map is injective because its zero representatives are original boundaries. -/
theorem classMap_injective : Function.Injective (classMap (k := k) M P hlinear) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective
    (CoverCohomology.boundary2 M P ClosedRegion.all).range x
  have hz := congrArg Subtype.val hx
  change (LinearMap.range d1P).mkQ z.1 = 0 at hz
  obtain ⟨h,hh⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  exact (CoverCohomology.h2_eq_zero_iff M P ClosedRegion.all z).mpr
    ⟨h,Subtype.ext ((differential1_eq M hlinear ClosedRegion.all P h).symm.trans hh)⟩

/-- Every induced-d2 cycle has a full original face cocycle representative. -/
theorem classMap_surjective : Function.Surjective (classMap (k := k) M P hlinear) := by
  intro x
  obtain ⟨c,hc⟩ := (LinearMap.range d1P).mkQ_surjective x.1
  have hz : RelativeCover.d2 M ClosedRegion.all P c = 0 := by
    rw [← differential2_eq (k := k) M hlinear ClosedRegion.all P]
    change d2bar ((LinearMap.range d1P).mkQ c) = 0
    rw [hc]; exact x.2
  refine ⟨QuotientAddGroup.mk (⟨c,hz⟩ : CoverCohomology.Z2 M P ClosedRegion.all),?_⟩
  exact Subtype.ext hc

/-- Original full H2 is exactly the induced original d2 kernel in CP2/im d1. -/
noncomputable def equivalence : CoverCohomology.H2 M P ClosedRegion.all ≃+
    LinearMap.ker d2bar :=
  AddEquiv.ofBijective (classMap (k := k) M P hlinear)
    ⟨classMap_injective (k := k) M P hlinear,classMap_surjective (k := k) M P hlinear⟩

/-- The cohomology equivalence preserves every original cocycle value modulo full d1. -/
theorem equivalence_value (z : CoverCohomology.Z2 M P ClosedRegion.all) :
    (equivalence (k := k) M P hlinear (QuotientAddGroup.mk z)).1 =
      (LinearMap.range d1P).mkQ z.1 := rfl

end OriginalRangeCohomology
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
