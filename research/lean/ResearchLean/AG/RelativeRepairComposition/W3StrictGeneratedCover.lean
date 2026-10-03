import ResearchLean.AG.RelativeRepairComposition.W3LocalInterfaces
import ResearchLean.AG.RelativeRepairComposition.W3EmptyGroupoids
import ResearchLean.AG.RelativeRepairComposition.SupportedNativeEquation
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverAction

/-! # Independent actual W3 repairs and the complete generated strict cover

The local matrices, elimination, sections and public relations come from
the same complete original affine input before S. Every permission uses
literal shared original values, retaining all operations and full labels.
-/
namespace AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs W3FiniteCoefficients
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (sheared : Bool) (S : Set (EdgeName (K := geometry)))
local notation "T" => originalTower sheared
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)
local notation "delta" => actualDefect sheared

/-- All independently generated full local public relations and literal shared values under S. -/
abbrev Objects := GeneratedStrictCover.Objects (M) (bases sheared) fixedRegion regions candidates
  (original_linear sheared) (delta) enumK enumEdges enumFaces S

/-- The whole generated strict groupoid retains every compatible original vertex label. -/
abbrev Groupoid := GeneratedCoverAction.Groupoid (M) (bases sheared) fixedRegion regions candidates
  (original_linear sheared) (delta) enumK enumEdges enumFaces S

/-- Every independent full actual repair and every generated strict object have both inverse coordinates. -/
noncomputable def actualObjectEquiv : RealRepairs sheared S ≃ Objects sheared S :=
  (NativeAffine.repairEquivalence geometry (reference sheared) (reference sheared)
    comparison (linear_faces sheared) (fixedEdges S)).symm.trans
    ((SupportedNativeEquation.repairEquiv (T) fixedRegion candidates S (fixed_faces sheared)).trans
      ((StrictCoverRestoration.objectEquiv (M) fixedRegion regions candidates S (delta) enumRegions indexed_cover).trans
        (GeneratedStrictCover.objectEquiv (M) (bases sheared) fixedRegion regions candidates
          (original_linear sheared) (delta) enumK enumEdges enumFaces S)))

/-- The original whole native groupoid has the same entire generated strict groupoid. -/
noncomputable def nativeEquivalence : NativeCategory sheared S ≌ Groupoid sheared S :=
  (SupportedNativeEquation.equivalence (T) fixedRegion candidates S (fixed_faces sheared)).trans
    ((StrictCoverRestoration.equivalence (M) fixedRegion regions candidates S (delta) enumRegions indexed_cover).trans
      (GeneratedCoverAction.equivalence (M) (bases sheared) fixedRegion regions candidates
        (original_linear sheared) (delta) enumK enumEdges enumFaces S))

/-- The same independently authored actual operations and every full gauge arrow have complete strict coordinates. -/
noncomputable def actualEquivalence : ActualCategory sheared S ≌ Groupoid sheared S :=
  (wholeAffineEquivalence sheared S).symm.trans (nativeEquivalence sheared S)

/-- Strict extraction and restoration return each entire independent actual repair. -/
theorem restore_extract (R : RealRepairs sheared S) :
    (actualObjectEquiv sheared S).symm (actualObjectEquiv sheared S R) = R :=
  (actualObjectEquiv sheared S).symm_apply_apply R

/-- Actual restoration and strict extraction return every generated public and private value. -/
theorem extract_restore (g : Objects sheared S) :
    actualObjectEquiv sheared S ((actualObjectEquiv sheared S).symm g) = g :=
  (actualObjectEquiv sheared S).apply_symm_apply g

/-- Every full original affine edge operation is restored at its own original typed edge. -/
theorem restore_operation (R : RealRepairs sheared S) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    ((actualObjectEquiv sheared S).symm (actualObjectEquiv sheared S R)).operation e = R.operation e := by
  rw [restore_extract]

/-- Empty-permission strict generation restores the full original fixed-vector groupoid. -/
noncomputable def emptyEquivalence : Groupoid sheared ∅ ≌ W3EmptyGroupoids.BFixed sheared :=
  (actualEquivalence sheared ∅).symm.trans (W3EmptyGroupoids.globalEquivalence sheared)

/-- Every empty-permission generated object restores both unchanged original full affine operations. -/
theorem empty_restored_operation (g : Objects sheared ∅) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    ((actualObjectEquiv sheared ∅).symm g).operation e = reference sheared e :=
  congrArg (fun R : RealRepairs sheared ∅ => R.operation e)
    (empty_unique sheared ((actualObjectEquiv sheared ∅).symm g))

end AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3StrictGeneratedCover
