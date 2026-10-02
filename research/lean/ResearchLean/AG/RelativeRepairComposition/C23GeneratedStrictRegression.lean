import ResearchLean.AG.RelativeRepairComposition.C23ActualLocalCorrection
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedLocalCorrectionBridge

/-!
# Same whole affine W4 across every independent strict permission range

## Implementation notes

The original full affine tower, authored baa face, original candidate b,
fixed vertex region, full translation kernels and designated factors are the
same input. Both independently generated strict families use their complete
cover. Every parameter and every fresh value is restored to original actual
operations; forbidding b rejects every independently generated repair.
-/
namespace AAT.AG.RelativeRepairComposition.C23GeneratedStrictRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine Subdivision C17SubdivisionInput
open C20SubdivisionCoverRegression C21LocalSubdivisionRegression C22GeneratedSubdivisionRegression
open C23GeneratedStrictParameters
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules
attribute [local instance] C22GeneratedSubdivisionRegression.edgeDecidableEq C22GeneratedSubdivisionRegression.faceDecidableEq C22GeneratedSubdivisionRegression.allVerticesDecidable C22GeneratedSubdivisionRegression.allEdgesDecidable C22GeneratedSubdivisionRegression.allFacesDecidable C22GeneratedSubdivisionRegression.regionsVerticesDecidable C22GeneratedSubdivisionRegression.regionsEdgesDecidable C22GeneratedSubdivisionRegression.regionsFacesDecidable C22GeneratedSubdivisionRegression.fixedEdgesDecidable C22GeneratedSubdivisionRegression.fixedFacesDecidable

-- Reuse the accepted predecessor's proof arguments in the same complete affine types.
attribute [local instance] C22GeneratedSubdivisionRegression.bases._proof_1
attribute [local instance] C22GeneratedSubdivisionRegression.oldExtraction._proof_1

/-- The complete local correction bridge supplies the equality at its own independently generated types. -/
noncomputable def generated_owner_equality (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :=
  eq_of_heq (GeneratedLocalCorrectionBridge.component_heq_of_rhs_eq originalTower chosen factors bases regions fixedRegion {candidate}
    false chosen_private C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
    C19SubdivisionRangeRegression.fixed_faces enumRegions regions_cover S (newActual S hs h r) false
    actualRHS owner_rhs (newLocalSolution h r) (C23ActualLocalCorrection.actual_local_correction S hs h r))

/-- The full generated owner component unfolds to its independent global restoration. -/
theorem owner_extraction_value (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    (newGenerated S hs h r).1 false =
      (GeneratedCoverRestoration.newObjectEquiv originalTower chosen factors bases regions fixedRegion {candidate}
        false chosen_private C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
        C19SubdivisionRangeRegression.fixed_faces enumRegions regions_cover S (newActual S hs h r)).1 false := rfl

/-- The same local generator is precisely the accepted C22 complete generated output. -/
theorem owner_local_generation_value (h r : ZMod 3) :
    GeneratedRelations.newGeneratedEquiv originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
      (value := actualRHS) (newLocalSolution h r) = C22GeneratedSubdivisionRegression.newGenerated h r := rfl


/-- Full global generation keeps exactly the same independently generated local new output for all h and r. -/
theorem new_owner_component (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    (newGenerated S hs h r).1 false = C22GeneratedSubdivisionRegression.newGenerated h r :=
  (owner_extraction_value S hs h r).trans
    ((generated_owner_equality S hs h r).trans (owner_local_generation_value h r))

/-- The full global new generated owner comparison is the same independent C22 local comparison for every parameter. -/
theorem new_owner_comparison (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    C22GeneratedSubdivisionRegression.interfaceComparison ((newGenerated S hs h r).1 false) =
      (C22GeneratedSubdivisionRegression.oldGenerated h,supplement r) :=
  (congrArg C22GeneratedSubdivisionRegression.interfaceComparison (new_owner_component S hs h r)).trans
    (C22GeneratedSubdivisionRegression.generated_coordinates h r)

/-- The whole generated owner still exposes the forced nonzero full public candidate b. -/
theorem generated_public_one (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    ((newGenerated S hs h r).1 false).1.1 C22GeneratedSubdivisionRegression.newPublicIndex = 1 :=
  (congrArg (fun y => y.1.1 C22GeneratedSubdivisionRegression.newPublicIndex)
    (new_owner_component S hs h r)).trans (C22GeneratedSubdivisionRegression.new_generated_public _)
end AAT.AG.RelativeRepairComposition.C23GeneratedStrictRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C23GeneratedStrictRegression
