import ResearchLean.AG.RelativeRepairComposition.OriginalRangeCohomology
import ResearchLean.AG.RelativeRepairComposition.CoverNativeCohomology

/-! # Original-K H2 classes in the original all-column quotient -/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace OriginalNativeRangeCohomology
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)] (P : ClosedRegion K)
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
local instance allFacesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).faces) :=
  fun _ => isTrue trivial

/-- The original-K class map uses the accepted full original-cell homology isomorphism. -/
noncomputable def classMap : RelativeComplex.H2 M P ∅ ∅ →+
    LinearMap.ker (OriginalRangeQuotient.inducedD2 (k := k) M P hlinear) :=
  (OriginalRangeCohomology.classMap (k := k) M P hlinear).comp
    (OriginalCohomology.familySecondIso M P).inv.hom

/-- Every original-K full cocycle has the same original-index cocycle. -/
noncomputable def familyCycle (c : RelativeComplex.Z2 M P) :
    CoverCohomology.Z2 M P ClosedRegion.all :=
  ⟨(RelativeCover.original2 M P).symm c.1,by
    apply (RelativeCover.original3 M P).injective
    rw [map_zero,RelativeCover.original_supported_d2,
      AddEquiv.apply_symm_apply]
    exact c.2⟩

/-- Returning to original K preserves the complete full face cocycle. -/
theorem familyCycle_eq (c : RelativeComplex.Z2 M P) :
    OriginalCohomology.familyCycle2 M P (familyCycle M P c) = c := by
  apply Subtype.ext
  exact (RelativeCover.original2 M P).apply_symm_apply c.1

/-- The original-K class maps to exactly the same whole face representative modulo original d1. -/
theorem classMap_value (c : RelativeComplex.Z2 M P) :
    (classMap (k := k) M P hlinear (QuotientAddGroup.mk c)).1 =
      (LinearMap.range (differential1 M hlinear ClosedRegion.all P)).mkQ
        ((RelativeCover.original2 M P).symm c.1) := by
  have hc := OriginalCohomology.family_h2_class M P (familyCycle M P c)
  rw [familyCycle_eq] at hc
  rw [← hc]
  change (OriginalRangeCohomology.classMap (k := k) M P hlinear
    ((OriginalCohomology.familySecondIso M P).inv
      ((OriginalCohomology.familySecondIso M P).hom
        (QuotientAddGroup.mk (familyCycle M P c))))).1 = _
  rw [Iso.hom_inv_id_apply]
  rfl

/-- The original-K class comparison is bijective onto the original induced-d2 kernel. -/
theorem classMap_bijective : Function.Bijective (classMap (k := k) M P hlinear) := by
  constructor
  · intro x y hxy
    have h := OriginalRangeCohomology.classMap_injective (k := k) M P hlinear hxy
    have hh := congrArg (OriginalCohomology.familySecondIso M P).hom h
    simpa only [Iso.inv_hom_id_apply] using hh
  · intro y
    obtain ⟨x,hx⟩ := OriginalRangeCohomology.classMap_surjective (k := k) M P hlinear y
    refine ⟨(OriginalCohomology.familySecondIso M P).hom x,?_⟩
    change OriginalRangeCohomology.classMap (k := k) M P hlinear
      ((OriginalCohomology.familySecondIso M P).inv
        ((OriginalCohomology.familySecondIso M P).hom x)) = y
    rw [Iso.hom_inv_id_apply]; exact hx

/-- Original-K full H2 is equivalent to the same induced-d2 kernel. -/
noncomputable def equivalence : RelativeComplex.H2 M P ∅ ∅ ≃+
    LinearMap.ker (OriginalRangeQuotient.inducedD2 (k := k) M P hlinear) :=
  AddEquiv.ofBijective (classMap (k := k) M P hlinear) (classMap_bijective (k := k) M P hlinear)

end OriginalNativeRangeCohomology
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
