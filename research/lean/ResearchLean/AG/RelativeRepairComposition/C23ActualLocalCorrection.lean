import ResearchLean.AG.RelativeRepairComposition.C23GeneratedStrictParameters

/-!
# Same whole affine W4 across every independent strict permission range

## Implementation notes

The original full affine tower, authored baa face, original candidate b,
fixed vertex region, full translation kernels and designated factors are the
same input. Both independently generated strict families use their complete
cover. Every parameter and every fresh value is restored to original actual
operations; forbidding b rejects every independently generated repair.
-/
namespace AAT.AG.RelativeRepairComposition.C23ActualLocalCorrection
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine Subdivision C17SubdivisionInput
open C20SubdivisionCoverRegression C21LocalSubdivisionRegression C22GeneratedSubdivisionRegression
open C23GeneratedStrictParameters
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules
attribute [local instance] C22GeneratedSubdivisionRegression.edgeDecidableEq C22GeneratedSubdivisionRegression.faceDecidableEq C22GeneratedSubdivisionRegression.allVerticesDecidable C22GeneratedSubdivisionRegression.allEdgesDecidable C22GeneratedSubdivisionRegression.allFacesDecidable C22GeneratedSubdivisionRegression.regionsVerticesDecidable C22GeneratedSubdivisionRegression.regionsEdgesDecidable C22GeneratedSubdivisionRegression.regionsFacesDecidable C22GeneratedSubdivisionRegression.fixedEdgesDecidable C22GeneratedSubdivisionRegression.fixedFacesDecidable

/-- All complete local correction values equal the same actual full restoration for every permitted range. -/
theorem actual_local_correction (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S)
    (h r : ZMod 3) (e : (expandedRegion geometry chosen ClosedRegion.all).edges) :
    (newLocalSolution h r).1.1 e = splitTower.solutionCorrection (newActual S hs h r).1 e.1 := by
  rcases e with ⟨e,he⟩
  obtain ⟨n,rfl⟩ := (edgeNameEquiv geometry chosen).symm.surjective e
  cases n with
  | inl e =>
    exact (newLocal_retained h r ⟨e.1,trivial⟩ e.2).trans
      (expandSupported_old originalTower chosen factors (fixedEdgesForRange fixedRegion.edges {candidate} S)
        (oldActual S hs h) (middleCoefficient.symm r) e.1 e.2).symm
  | inr b =>
    cases b
    · apply middleCoefficient.injective
      exact (newLocal_first_coordinate h r).trans (restore_first_coordinate (oldRepairEquiv.symm h) r).symm
    · apply middleCoefficient.injective
      have hv := restore_second_coordinate (oldRepairEquiv.symm h) r
      rw [← old_parameter_correction,Equiv.apply_symm_apply] at hv
      exact (newLocal_second_coordinate h r).trans hv.symm

end AAT.AG.RelativeRepairComposition.C23ActualLocalCorrection
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C23ActualLocalCorrection
