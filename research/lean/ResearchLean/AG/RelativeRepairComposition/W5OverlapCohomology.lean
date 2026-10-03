import ResearchLean.AG.RelativeRepairComposition.W5LocalCohomology
import ResearchLean.AG.RelativeRepairComposition.CoverObstructionKernel

/-! # Entire W5 overlap H1 and the prescribed sum-of-images quotient

The overlap retains the original shared edge and both fixed endpoints, with
no face. Its full H1 is F2; both full original local H1 restriction images
vanish. Omega is the entire prescribed quotient, with inverse coordinates.
-/
namespace AAT.AG.RelativeRepairComposition.W5OverlapCohomology
open CategoryTheory TransportCoherence AbelianLiftingObstruction
open W5AffineInput W5Regions W5RelativeCoefficients W5LocalCohomology
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (b₁ b₂ : ZMod 2)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower b₁ b₂))
local notation "Z" => CoverCohomology.Z1 M fixedRegion overlap
local notation "H" => CoverCohomology.H1 M fixedRegion overlap
/-- The original overlap retains its same full shared-edge coefficient. -/
theorem overlap_shared : name edgeE ∈ overlap.edges := by rw [overlap_edges]; rfl
/-- The original overlap has no selected face, so its whole first differential vanishes. -/
theorem overlap_d1_zero (a : RelativeCover.C1 M overlap fixedRegion) :
    RelativeCover.d1 M overlap fixedRegion a = 0 := by
  apply Subtype.ext
  funext f
  have hf : f.1 ∈ (∅ : Set geometry.TwoCell) := by simpa only [overlap_faces] using f.2
  exact hf.elim
/-- All original overlap cycles and F2 have both inverse full-cochain coordinates. -/
noncomputable def cycleCoordinate : Z ≃+ ZMod 2 where
  toFun z := edgeCoordinates b₁ b₂ overlap overlap_shared z.1
  invFun u := ⟨cochain b₁ b₂ overlap u,overlap_d1_zero b₁ b₂ _⟩
  left_inv z := Subtype.ext (cochain_reconstruct b₁ b₂ overlap overlap_shared z.1)
  right_inv u := (edgeCoordinates b₁ b₂ overlap overlap_shared).apply_symm_apply u
  map_add' z w := (edgeCoordinates b₁ b₂ overlap overlap_shared).map_add z.1 w.1
/-- Every whole original overlap boundary vanishes because its actual source vertex family is zero. -/
theorem boundary_range_bot : (CoverCohomology.boundary1 M fixedRegion overlap).range = ⊥ := by
  apply le_antisymm
  · rintro z ⟨a,rfl⟩
    apply AddSubgroup.mem_bot.mpr
    rw [vertex_zero b₁ b₂ overlap a,map_zero]
  · exact bot_le
/-- The entire original overlap H1 quotient is F2, with both inverse coordinates. -/
noncomputable def h1Coordinate : H ≃+ ZMod 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq (boundary_range_bot b₁ b₂)).trans
    ((QuotientAddGroup.quotientBot).trans (cycleCoordinate b₁ b₂))
/-- Every whole original H1 representative retains the original shared-edge cycle value. -/
theorem h1Coordinate_class (z : Z) :
    h1Coordinate b₁ b₂ (QuotientAddGroup.mk z) = edgeCoordinates b₁ b₂ overlap overlap_shared z.1 := rfl
/-- The denominator is exactly both full local restriction images, and that sum is zero. -/
theorem localImages_bot : CoverObstruction.localImages M fixedRegion leftRegion rightRegion = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a,ha,b,hb,hab⟩ := AddSubgroup.mem_sup.mp hx
    obtain ⟨u,rfl⟩ := ha
    obtain ⟨v,rfl⟩ := hb
    rw [local_h1_zero b₁ b₂ false u,local_h1_zero b₁ b₂ true v,map_zero,map_zero,zero_add] at hab
    exact AddSubgroup.mem_bot.mpr hab.symm
  · exact bot_le
/-- The entire prescribed original integration quotient is F2, with both inverses. -/
noncomputable def omegaCoordinate : CoverObstruction.Omega M fixedRegion leftRegion rightRegion ≃+ ZMod 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq (localImages_bot b₁ b₂)).trans
    ((QuotientAddGroup.quotientBot).trans (h1Coordinate b₁ b₂))
/-- The quotient coordinate retains every full original overlap H1 class. -/
theorem omegaCoordinate_class (h : H) :
    omegaCoordinate b₁ b₂ (QuotientAddGroup.mk h) = h1Coordinate b₁ b₂ h := rfl
/-- Both full original H2 restrictions vanish on every entire original-K class. -/
theorem restriction_zero (x : RelativeComplex.H2 M fixedRegion ∅ ∅) :
    CoverObstructionKernel.restriction M fixedRegion leftRegion rightRegion x = 0 := by
  apply Prod.ext
  · exact local_h2_zero b₁ b₂ false _
  · exact local_h2_zero b₁ b₂ true _
/-- The whole original H2 restriction kernel equals the full original H2. -/
noncomputable def restrictionKernelEquiv :
    (CoverObstructionKernel.restriction M fixedRegion leftRegion rightRegion).ker ≃+
      RelativeComplex.H2 M fixedRegion ∅ ∅ :=
  AddEquiv.ofBijective (AddSubgroup.subtype _) ⟨Subtype.val_injective,
    fun x => ⟨⟨x,restriction_zero b₁ b₂ x⟩,rfl⟩⟩
/-- The same generic B kernel equivalence covers the full original relative H2. -/
noncomputable def omegaOriginalH2Equiv :
    CoverObstruction.Omega M fixedRegion leftRegion rightRegion ≃+ RelativeComplex.H2 M fixedRegion ∅ ∅ :=
  (CoverObstructionKernel.omegaKernelEquiv M fixedRegion leftRegion rightRegion regions_cover).trans
    (restrictionKernelEquiv b₁ b₂)

end AAT.AG.RelativeRepairComposition.W5OverlapCohomology
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5OverlapCohomology
