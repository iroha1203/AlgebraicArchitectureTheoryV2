import ResearchLean.AG.RelativeRepairComposition.W1LocalInterfaces
import ResearchLean.AG.RelativeRepairComposition.W1NativeLabels
import ResearchLean.AG.RelativeRepairComposition.SupportedNativeEquation
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverAction

/-!
# Full actual W1 repairs and independently generated strict interfaces

The two local generators use the original six-edge affine tower, its actual
defect, and exactly the private/public partition already derived from its cover.
Every permission set is imposed on those same generated public values. Complete
actual operations and complete native label arrows are restored in both directions.
-/
namespace AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1ActualRepairs W1FiniteCoefficients
open W1RelativeCoefficients W1IndexedCover W1NativeLabels
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3) (S : Set (EdgeName (K := geometry)))
local notation "T" => originalTower true x y
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)
local notation "delta" => actualDefect true x y

/-- All independently generated local public relations, all private kernels and literal shared original values for S. -/
abbrev Objects := GeneratedStrictCover.Objects (M) (bases true x y) fixedRegion regions candidates
  (original_linear true x y) (delta) enumK enumEdges enumFaces S

/-- The complete generated strict groupoid retains every original compatible vertex label. -/
abbrev Groupoid := GeneratedCoverAction.Groupoid (M) (bases true x y) fixedRegion regions candidates
  (original_linear true x y) (delta) enumK enumEdges enumFaces S

/-- The independent original actual full affine repair set has exact generated strict coordinates with both inverses. -/
noncomputable def actualObjectEquiv : RealRepairs true x y S ≃ Objects x y S :=
  (NativeAffine.repairEquivalence geometry (reference true x y) (reference true x y)
    comparison (linear_faces true x y) (fixedEdges S)).symm.trans
    ((SupportedNativeEquation.repairEquiv (T) fixedRegion candidates S (fixed_faces true x y)).trans
      ((StrictCoverRestoration.objectEquiv (M) fixedRegion regions candidates S (delta) enumRegions indexed_cover).trans
        (GeneratedStrictCover.objectEquiv (M) (bases true x y) fixedRegion regions candidates
          (original_linear true x y) (delta) enumK enumEdges enumFaces S)))

/-- The whole original native groupoid and the complete generated strict groupoid have mutually inverse equivalence functors. -/
noncomputable def nativeEquivalence : NativeCategory true x y S ≌ Groupoid x y S :=
  (SupportedNativeEquation.equivalence (T) fixedRegion candidates S (fixed_faces true x y)).trans
    ((StrictCoverRestoration.equivalence (M) fixedRegion regions candidates S (delta) enumRegions indexed_cover).trans
      (GeneratedCoverAction.equivalence (M) (bases true x y) fixedRegion regions candidates
        (original_linear true x y) (delta) enumK enumEdges enumFaces S))

/-- Every complete independent actual affine object and all its original affine gauge arrows have the same strict generated groupoid. -/
noncomputable def actualEquivalence :
    NativeAffine.Groupoid geometry (reference true x y) (reference true x y)
      comparison (linear_faces true x y) fixedRegion.vertices (fixedEdges S) ≌ Groupoid x y S :=
  (wholeAffineEquivalence true x y S).symm.trans (nativeEquivalence x y S)

/-- Restoring generated coordinates after extracting an independent actual repair retains the entire actual repair. -/
theorem restore_extract (R : RealRepairs true x y S) :
    (actualObjectEquiv x y S).symm (actualObjectEquiv x y S R) = R :=
  (actualObjectEquiv x y S).symm_apply_apply R

/-- Extracting after restoration retains all independent generated public and private values. -/
theorem extract_restore (g : Objects x y S) :
    actualObjectEquiv x y S ((actualObjectEquiv x y S).symm g) = g :=
  (actualObjectEquiv x y S).apply_symm_apply g

/-- Every restored original operation agrees at its own original full affine edge. -/
theorem restore_operation (R : RealRepairs true x y S) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    ((actualObjectEquiv x y S).symm (actualObjectEquiv x y S R)).operation e = R.operation e := by
  rw [restore_extract]

/-- The independently generated strict predicate is feasible exactly when the original actual laws and permission masks admit full parameters. -/
theorem generated_feasible_iff : Nonempty (Objects x y S) ↔
    Nonempty {p : Parameters // Equations true x y p ∧ Allowed S p} :=
  (actualObjectEquiv x y S).nonempty_congr.symm.trans (actualParametersEquiv true x y S).nonempty_congr

end AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1StrictGeneratedCover
