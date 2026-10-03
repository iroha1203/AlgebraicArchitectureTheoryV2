import ResearchLean.AG.RelativeRepairComposition.W5RelativeCoefficients
import ResearchLean.AG.RelativeRepairComposition.CoverNativeCohomology

/-! # The entire original W5 relative H2 and its actual defect class

The map reads the difference of both full original face coordinates. Its
kernel is the entire original d1 boundary range, so the resulting equivalence
covers the whole quotient and the same original-K cohomology class.
-/
namespace AAT.AG.RelativeRepairComposition.W5RelativeObstruction
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open W5AffineInput W5Regions W5AuthoredOperations W5OriginalDifferentials W5RelativeCoefficients
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (b₁ b₂ : ZMod 2)
local notation "T" => originalTower b₁ b₂
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower b₁ b₂))
local notation "Z" => CoverCohomology.Z2 M fixedRegion ClosedRegion.all
local notation "H" => CoverCohomology.H2 M fixedRegion ClosedRegion.all
/-- All original authored three-cell conditions are discharged on the specified empty family. -/
theorem original_syzygy (s : geometry.ThreeCell) : AuthoredSyzygy (T).toTower.toTransportData 1
    (geometry.threeLeft s) (geometry.threeRight s) := s.elim
/-- Any entire relative face family is an original two-cycle. -/
noncomputable def cycleOfFace (a : RelativeCover.C2 M ClosedRegion.all fixedRegion) : Z :=
  ⟨a,W5RelativeCoefficients.d2_zero b₁ b₂ ClosedRegion.all a⟩
/-- Read first minus second full original face coordinates, retaining the actual defect sign. -/
noncomputable def reading : Z →+ ZMod 2 where
  toFun z := faceCoordinates b₁ b₂ ClosedRegion.all z.1 ⟨false,Set.mem_univ _⟩ -
    faceCoordinates b₁ b₂ ClosedRegion.all z.1 ⟨true,Set.mem_univ _⟩
  map_zero' := by simp
  map_add' a c := by
    change faceCoordinates b₁ b₂ ClosedRegion.all (a.1 + c.1) ⟨false,Set.mem_univ _⟩ -
      faceCoordinates b₁ b₂ ClosedRegion.all (a.1 + c.1) ⟨true,Set.mem_univ _⟩ = _
    simp only [map_add,Pi.add_apply]
    abel
/-- The reading acts on all original cycle representatives. -/
theorem reading_value (z : Z) : reading b₁ b₂ z =
    faceCoordinates b₁ b₂ ClosedRegion.all z.1 ⟨false,Set.mem_univ _⟩ -
      faceCoordinates b₁ b₂ ClosedRegion.all z.1 ⟨true,Set.mem_univ _⟩ := rfl
/-- Every full F2 value is attained by a complete original relative two-cycle. -/
theorem reading_surjective : Function.Surjective (reading b₁ b₂) := by
  intro u
  refine ⟨cycleOfFace b₁ b₂ ((faceCoordinates b₁ b₂ ClosedRegion.all).symm
    (fun f => if (f.1 : Bool) = true then 0 else u)),?_⟩
  rw [reading_value]
  change (faceCoordinates b₁ b₂ ClosedRegion.all) ((faceCoordinates b₁ b₂ ClosedRegion.all).symm _) _ -
    (faceCoordinates b₁ b₂ ClosedRegion.all) ((faceCoordinates b₁ b₂ ClosedRegion.all).symm _) _ = _
  rw [AddEquiv.apply_symm_apply]
  simp
/-- The actual full original boundary range is precisely the diagonal kernel of the reading. -/
theorem boundary_range_eq_kernel : (CoverCohomology.boundary2 M fixedRegion ClosedRegion.all).range =
    (reading b₁ b₂).ker := by
  apply le_antisymm
  · rintro z ⟨a,rfl⟩
    change reading b₁ b₂ (CoverCohomology.boundary2 M fixedRegion ClosedRegion.all a) = 0
    rw [reading_value]
    change faceCoordinates b₁ b₂ ClosedRegion.all (RelativeCover.d1 M ClosedRegion.all fixedRegion a) _ -
      faceCoordinates b₁ b₂ ClosedRegion.all (RelativeCover.d1 M ClosedRegion.all fixedRegion a) _ = _
    rw [W5RelativeCoefficients.d1_value b₁ b₂ ClosedRegion.all (Set.mem_univ _) a,
      W5RelativeCoefficients.d1_value b₁ b₂ ClosedRegion.all (Set.mem_univ _) a,sub_self]
  · intro z hz
    have he : faceCoordinates b₁ b₂ ClosedRegion.all z.1 ⟨false,Set.mem_univ _⟩ =
        faceCoordinates b₁ b₂ ClosedRegion.all z.1 ⟨true,Set.mem_univ _⟩ := sub_eq_zero.mp hz
    refine ⟨cochain b₁ b₂ ClosedRegion.all
      (faceCoordinates b₁ b₂ ClosedRegion.all z.1 ⟨false,Set.mem_univ _⟩),?_⟩
    apply Subtype.ext
    apply (faceCoordinates b₁ b₂ ClosedRegion.all).injective
    funext f
    change faceCoordinates b₁ b₂ ClosedRegion.all
      (RelativeCover.d1 M ClosedRegion.all fixedRegion (cochain b₁ b₂ ClosedRegion.all _)) f = _
    rw [cochain_d1_value]
    rcases f with ⟨f,hf⟩
    cases f
    · rfl
    · exact he
/-- The whole original relative H2 quotient is the entire F2 space, with both inverses. -/
noncomputable def h2Coordinate : H ≃+ ZMod 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq (boundary_range_eq_kernel b₁ b₂)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (reading b₁ b₂) (reading_surjective b₁ b₂))
/-- The complete H2 equivalence keeps every full original cycle representative reading. -/
theorem h2Coordinate_class (z : Z) : h2Coordinate b₁ b₂ (QuotientAddGroup.mk z) = reading b₁ b₂ z := rfl
/-- The whole original-K relative H2 has the same both-inverse F2 coordinate. -/
noncomputable def originalH2Coordinate : RelativeComplex.H2 M fixedRegion ∅ ∅ ≃+ ZMod 2 :=
  (AddEquiv.ofBijective (OriginalCohomology.familySecondIso M fixedRegion).inv.hom
    ⟨(AddCommGrpCat.mono_iff_injective _).mp inferInstance,
      (AddCommGrpCat.epi_iff_surjective _).mp inferInstance⟩).trans (h2Coordinate b₁ b₂)
/-- The original actual defect defines the same full relative cycle before taking a class. -/
noncomputable def actualCycle : Z := cycleOfFace b₁ b₂ (actualDefect b₁ b₂)
/-- The original native cycle is precisely the independently generated actual defect cocycle. -/
theorem actualCycle_original : OriginalCohomology.familyCycle2 M fixedRegion (actualCycle b₁ b₂) =
    ActualRelative.obstructionCocycle T fixedRegion (fixed_faces b₁ b₂) (original_syzygy b₁ b₂) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl
/-- The actual original obstruction class has the same full representative in the whole H2. -/
theorem actual_class_comparison :
    (OriginalCohomology.familySecondIso M fixedRegion).hom (QuotientAddGroup.mk (actualCycle b₁ b₂)) =
      ActualRelative.obstructionClass T fixedRegion ∅ ∅ (fixed_faces b₁ b₂) (original_syzygy b₁ b₂) := by
  rw [OriginalCohomology.family_h2_class,actualCycle_original]
  rfl
/-- The entire original actual obstruction evaluates to b2-b1, including its original positive class sign. -/
theorem actual_obstruction_value : originalH2Coordinate b₁ b₂
    (ActualRelative.obstructionClass T fixedRegion ∅ ∅ (fixed_faces b₁ b₂) (original_syzygy b₁ b₂)) = b₂ - b₁ := by
  rw [← actual_class_comparison]
  change h2Coordinate b₁ b₂ ((OriginalCohomology.familySecondIso M fixedRegion).inv
    ((OriginalCohomology.familySecondIso M fixedRegion).hom (QuotientAddGroup.mk (actualCycle b₁ b₂)))) = _
  rw [Iso.hom_inv_id_apply,h2Coordinate_class,reading_value]
  change faceCoordinates b₁ b₂ ClosedRegion.all (actualDefect b₁ b₂) _ -
    faceCoordinates b₁ b₂ ClosedRegion.all (actualDefect b₁ b₂) _ = _
  rw [actualDefect_value,actualDefect_value]
  change -b₁ - -b₂ = _
  abel

end AAT.AG.RelativeRepairComposition.W5RelativeObstruction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5RelativeObstruction
