import ResearchLean.AG.RelativeRepairComposition.W2LocalInterfaces
import ResearchLean.AG.RelativeRepairComposition.W2EmptyGroupoids
import ResearchLean.AG.RelativeRepairComposition.SupportedNativeEquation
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverAction

/-!
# Full actual W2 repairs and independently generated strict interfaces

The two local generators use the original two-edge affine tower, its actual
defect, and the full candidate/public partition derived from its cover.
Every permission set is imposed on those same generated public values. Complete
actual operations and complete native label arrows are restored in both directions.
-/
namespace AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2ActualRepairs W2FiniteCoefficients

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (S : Set (EdgeName (K := geometry)))
local notation "T" => originalTower
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)
local notation "delta" => actualDefect

/-- All independently generated local public relations, all private kernels and literal shared original values for S. -/
abbrev Objects := GeneratedStrictCover.Objects (M) (bases) fixedRegion regions candidates
  (original_linear) (delta) enumK enumEdges enumFaces S

/-- The complete generated strict groupoid retains every original compatible vertex label. -/
abbrev Groupoid := GeneratedCoverAction.Groupoid (M) (bases) fixedRegion regions candidates
  (original_linear) (delta) enumK enumEdges enumFaces S

/-- The independent original actual full affine repair set has exact generated strict coordinates with both inverses. -/
noncomputable def actualObjectEquiv : RealRepairs S ≃ Objects S :=
  (NativeAffine.repairEquivalence geometry (reference) (reference)
    comparison (linear_faces) (fixedEdges S)).symm.trans
    ((SupportedNativeEquation.repairEquiv (T) fixedRegion candidates S (fixed_faces)).trans
      ((StrictCoverRestoration.objectEquiv (M) fixedRegion regions candidates S (delta) enumRegions indexed_cover).trans
        (GeneratedStrictCover.objectEquiv (M) (bases) fixedRegion regions candidates
          (original_linear) (delta) enumK enumEdges enumFaces S)))

/-- The whole original native groupoid and the complete generated strict groupoid have mutually inverse equivalence functors. -/
noncomputable def nativeEquivalence : NativeCategory S ≌ Groupoid S :=
  (SupportedNativeEquation.equivalence (T) fixedRegion candidates S (fixed_faces)).trans
    ((StrictCoverRestoration.equivalence (M) fixedRegion regions candidates S (delta) enumRegions indexed_cover).trans
      (GeneratedCoverAction.equivalence (M) (bases) fixedRegion regions candidates
        (original_linear) (delta) enumK enumEdges enumFaces S))

/-- Every complete independent actual affine object and all its original affine gauge arrows have the same strict generated groupoid. -/
noncomputable def actualEquivalence :
    NativeAffine.Groupoid geometry (reference) (reference)
      comparison (linear_faces) fixedRegion.vertices (fixedEdges S) ≌ Groupoid S :=
  (wholeAffineEquivalence S).symm.trans (nativeEquivalence S)

/-- Restoring generated coordinates after extracting an independent actual repair retains the entire actual repair. -/
theorem restore_extract (R : RealRepairs S) :
    (actualObjectEquiv S).symm (actualObjectEquiv S R) = R :=
  (actualObjectEquiv S).symm_apply_apply R

/-- Extracting after restoration retains all independent generated public and private values. -/
theorem extract_restore (g : Objects S) :
    actualObjectEquiv S ((actualObjectEquiv S).symm g) = g :=
  (actualObjectEquiv S).apply_symm_apply g

/-- Every restored original operation agrees at its own original full affine edge. -/
theorem restore_operation (R : RealRepairs S) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    ((actualObjectEquiv S).symm (actualObjectEquiv S R)).operation e = R.operation e := by
  rw [restore_extract]

/-- The complete strictly generated empty-permission category restores the actual point, including every arrow. -/
noncomputable def emptyPointEquivalence : Groupoid ∅ ≌ W2EmptyGroupoids.Point :=
  (actualEquivalence ∅).symm.trans W2EmptyGroupoids.globalPointEquivalence

/-- Every empty-permission generated object restores both unchanged original affine operations. -/
theorem empty_restored_operation (g : Objects ∅) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    ((actualObjectEquiv ∅).symm g).operation e = reference e :=
  empty_operation ((actualObjectEquiv ∅).symm g) e

end AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2StrictGeneratedCover
