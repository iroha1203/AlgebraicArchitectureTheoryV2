import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionInput
import ResearchLean.AG.RelativeRepairComposition.W1GeneratedRelations
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedInterfaces
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedGroupoidEquivalence
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedCoverRestoration

/-!
# Full independently generated W1 local and strict interfaces after subdivision

Both generators read their own complete actual matrices, bases and enumerations.
The chosen internal edge is proved private to V. Every full original public
value, private kernel value, fresh value and native strict label is retained,
for all original candidate permissions and the same actual signed defects.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1SubdivisionInput
attribute [local instance] Classical.propDecidable
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules
attribute [local instance] Subdivision.GeneratedCoverAction.freshComm
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3)
local notation "T" => W1AffineInput.originalTower true x y
local notation "F" => factors x y
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (T))
local notation "B" => bases true x y
local notation "rhs" j => -CoverEquation.defect (M) fixedRegion
  (ActualEquation.defectFamily (T) fixedRegion (fixed_faces true x y)) (regions j)

/-- Each original local rhs comes from the actual full original reference defect. -/
noncomputable def values (j : Bool) := (rhs j)

/-- The independently generated full original local extraction is computed before any permission set. -/
noncomputable def oldExtraction (j : Bool) :=
  FiniteNative.generatedRelativeEquiv (M) (B) (regions j) fixedRegion
    (ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j)
    (original_linear true x y) (values x y j) enumK enumEdges enumFaces

/-- The full new extraction independently uses its actual new matrices and complete original-cell substitution. -/
noncomputable def newExtraction (j : Bool) :=
  Subdivision.GeneratedRelations.newGeneratedEquiv (T) chosen (F) (B) regions fixedRegion candidates
    true chosen_private j (original_linear true x y) enumK enumEdges enumFaces
    (value := values x y j)

/-- Every independently generated local new interface compares with the full old interface and its entire allowed fresh kernel. -/
noncomputable def comparison (j : Bool) :=
  Subdivision.GeneratedInterfaces.objectsEquiv (T) chosen (F) (B) regions fixedRegion candidates
    true chosen_private j (original_linear true x y) enumK enumEdges enumFaces
    (value := values x y j)

/-- Every actual new local solution is recovered by its independently generated section. -/
theorem local_restore (j : Bool)
    (h : FiniteNative.RelativeEquation (splitTower x y).toTower.localCoefficients
      (Subdivision.expandedRegion geometry chosen (regions j))
      (Subdivision.expandedRegion geometry chosen fixedRegion)
      ((Subdivision.local2Equiv (T) chosen (F) (regions j) fixedRegion).symm (values x y j))) :
    (newExtraction x y j).symm (newExtraction x y j h) = h :=
  (newExtraction x y j).symm_apply_apply h

/-- Independent new public relations have exactly the same membership after the full original public-coordinate comparison. -/
theorem public_relation_iff (j : Bool)
    (z : FiniteNative.ZIndex (splitTower x y).toTower.localCoefficients
      (Subdivision.FiniteBases.expandedBases (T) chosen (F) (B))
      (Subdivision.expandedRegion geometry chosen (regions j))
      (Subdivision.expandedRegion geometry chosen fixedRegion)
      (ClosedRegion.privateAlwaysEdges (fun l => Subdivision.expandedRegion geometry chosen (regions l))
        (Subdivision.expandedRegion geometry chosen fixedRegion)
        (Subdivision.oldEdgeSet geometry chosen candidates) j) → ZMod 3) :
    z ∈ Subdivision.GeneratedRelations.newRelation (T) chosen (F) (B) regions fixedRegion candidates
      true chosen_private j (original_linear true x y) enumK enumEdges enumFaces (value := values x y j) ↔
    Subdivision.GeneratedPublic.publicCoordinateEquiv (T) chosen (F) (B) regions fixedRegion candidates
      true chosen_private j z ∈
      FiniteNative.generatedRelation (M) (B) (regions j) fixedRegion
        (ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j) (original_linear true x y)
        (values x y j) enumK enumEdges enumFaces :=
  Subdivision.GeneratedRelations.relation_iff (T) chosen (F) (B) regions fixedRegion candidates
    true chosen_private j (original_linear true x y) enumK enumEdges enumFaces (values x y j) z

/-- The complete independently generated strict native groupoids compare for every original permission range. -/
noncomputable def strictEquivalence (S : Set (EdgeName (K := geometry))) :=
  Subdivision.GeneratedGroupoidEquivalence.equivalence (T) chosen (F) (B) regions fixedRegion candidates
    true chosen_private (original_linear true x y) enumK enumEdges enumFaces S (values x y)

/-- Every complete actual new repair is equivalent to its independently generated whole strict object, with all private and fresh values retained. -/
noncomputable def actualObjectEquiv (S : Set (EdgeName (K := geometry))) :=
  Subdivision.GeneratedCoverRestoration.newObjectEquiv (T) chosen (F) (B) regions fixedRegion candidates
    true chosen_private (original_linear true x y) enumK enumEdges enumFaces (fixed_faces true x y)
    enumRegions indexed_cover S

end AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionGeneratedInterfaces
