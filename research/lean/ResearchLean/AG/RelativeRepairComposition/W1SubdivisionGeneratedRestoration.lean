import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedActualNative

/-!
# Every complete actual W1 repair and every native generated label is restored

The independent new generator is compared with every independently specified
actual new repair, at every local original new edge. Both object inverse laws
hold on the whole sets. Its groupoid equivalence retains every full supported
vertex label rather than quotienting labels or restricting to restored objects.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedRestoration
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1SubdivisionInput W1SubdivisionGeneratedInterfaces
attribute [local instance] Classical.propDecidable
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules
attribute [local instance] Subdivision.GeneratedCoverAction.freshComm
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
variable (x y : ZMod 3)
local notation "T" => W1AffineInput.originalTower true x y
local notation "F" => factors x y
local notation "Bn" => bases true x y
local notation "fixed" S => Subdivision.oldEdgeSet geometry chosen (fixedEdges S)

/-- Every entire actual new repair is recovered after independent generated extraction. -/
theorem actual_restore (S : Set (EdgeName (K := geometry)))
    (R : SupportedRepair (splitTower x y) (fixed S)) :
    (actualObjectEquiv x y S).symm (actualObjectEquiv x y S R) = R :=
  (actualObjectEquiv x y S).symm_apply_apply R

/-- Every independent full new generated object is recovered after actual repair restoration. -/
theorem generated_restore (S : Set (EdgeName (K := geometry)))
    (g : Subdivision.GeneratedStrictObjects.NewObjects (T) chosen (F) (Bn) regions fixedRegion candidates
      true chosen_private (original_linear true x y) enumK enumEdges enumFaces (values x y) (candidates \ S)) :
    actualObjectEquiv x y S ((actualObjectEquiv x y S).symm g) = g :=
  (actualObjectEquiv x y S).apply_symm_apply g

/-- Every original complete local new edge correction is retained by independent generated restoration. -/
theorem extracted_correction (S : Set (EdgeName (K := geometry)))
    (R : SupportedRepair (splitTower x y) (fixed S)) (j : Bool)
    (e : (Subdivision.expandedRegion geometry chosen (regions j)).edges) :
    ((newExtraction x y j).symm ((actualObjectEquiv x y S R).1 j)).1.1 e =
      (splitTower x y).solutionCorrection R.1 e.1 :=
  Subdivision.GeneratedCoverRestoration.new_forward_edge_value (T) chosen (F) (Bn) regions fixedRegion candidates
    true chosen_private (original_linear true x y) enumK enumEdges enumFaces (fixed_faces true x y)
    enumRegions indexed_cover S R j e

/-- The whole actual new native groupoid is equivalent to the independently generated strict groupoid for all original permission sets. -/
noncomputable def actualNativeEquivalence (S : Set (EdgeName (K := geometry))) :=
  Subdivision.GeneratedActualNative.equivalence (T) chosen (F) (Bn) regions fixedRegion candidates
    true chosen_private (original_linear true x y) enumK enumEdges enumFaces (fixed_faces true x y)
    enumRegions indexed_cover S

end AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedRestoration
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedRestoration
