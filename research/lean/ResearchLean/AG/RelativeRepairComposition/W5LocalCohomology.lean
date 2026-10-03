import ResearchLean.AG.RelativeRepairComposition.W5RelativeCoefficients

/-! # Entire relative local cohomology of the original W5 patches

Each original patch has its one full authored face. Its entire degree-one
family maps bijectively to the whole face family. The full local H1 and H2
therefore vanish with the same physical P and original differentials.
-/
namespace AAT.AG.RelativeRepairComposition.W5LocalCohomology
open CategoryTheory TransportCoherence AbelianLiftingObstruction
open W5AffineInput W5Regions W5RelativeCoefficients
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (b₁ b₂ : ZMod 2)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower b₁ b₂))
/-- Every original indexed patch keeps its same shared edge. -/
theorem region_shared (side : Bool) : name edgeE ∈ (region side).edges := by
  rw [region_edges]
  exact Or.inl rfl
/-- Every selected original face on the indexed patch is its specified face. -/
theorem region_face (side : Bool) (f : (region side).faces) : f.1 = side := by
  cases side
  · exact f.2
  · exact f.2
/-- The whole patch differential has zero kernel, read on its original authored face. -/
theorem local_cycle_zero (side : Bool) (z : CoverCohomology.Z1 M fixedRegion (region side)) : z = 0 := by
  have hv : edgeCoordinates b₁ b₂ (region side) (region_shared side) z.1 = 0 := by
    calc
      _ = faceCoordinates b₁ b₂ (region side)
          (RelativeCover.d1 M (region side) fixedRegion z.1) ⟨side,face_in_region side⟩ :=
        (W5RelativeCoefficients.d1_value b₁ b₂ (region side) (region_shared side) z.1 _).symm
      _ = 0 := by rw [z.2,map_zero]; rfl
  apply Subtype.ext
  exact (edgeCoordinates b₁ b₂ (region side) (region_shared side)).map_eq_zero_iff.mp hv
/-- All classes of the complete original local H1 vanish. -/
theorem local_h1_zero (side : Bool) (h : CoverCohomology.H1 M fixedRegion (region side)) : h = 0 := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective
    (CoverCohomology.boundary1 M fixedRegion (region side)).range h
  change (QuotientAddGroup.mk' (CoverCohomology.boundary1 M fixedRegion (region side)).range) z = 0
  rw [local_cycle_zero b₁ b₂ side z,map_zero]
/-- Every full original local face family has a restored original relative shared-edge preimage. -/
theorem local_d1_surjective (side : Bool) :
    Function.Surjective (RelativeCover.d1 M (region side) fixedRegion) := by
  intro c
  refine ⟨cochain b₁ b₂ (region side)
    (faceCoordinates b₁ b₂ (region side) c ⟨side,face_in_region side⟩),?_⟩
  apply (faceCoordinates b₁ b₂ (region side)).injective
  funext f
  rw [cochain_d1_value]
  exact congrArg (faceCoordinates b₁ b₂ (region side) c) (Subtype.ext (region_face side f).symm)
/-- All classes of the complete original local H2 vanish by the original surjective d1. -/
theorem local_h2_zero (side : Bool) (h : CoverCohomology.H2 M fixedRegion (region side)) : h = 0 := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective
    (CoverCohomology.boundary2 M fixedRegion (region side)).range h
  apply (CoverCohomology.h2_eq_zero_iff M fixedRegion (region side) z).mpr
  obtain ⟨a,ha⟩ := local_d1_surjective b₁ b₂ side z.1
  exact ⟨a,Subtype.ext ha⟩

end AAT.AG.RelativeRepairComposition.W5LocalCohomology
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5LocalCohomology
