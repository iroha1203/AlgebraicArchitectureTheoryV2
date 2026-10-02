import ResearchLean.AG.RelativeRepairComposition.C23GeneratedStrictRegression

/-!
# Full native fresh W4 arrows on every generated strict permission range

The same complete independent generated families restore every original h
and fresh r. Every original vertex stays fixed; every actual fresh label t
remains as a full native arrow and acts by r ↦ r+t.
-/
namespace AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine Subdivision C17SubdivisionInput
open C20SubdivisionCoverRegression C21LocalSubdivisionRegression C23GeneratedStrictRegression
open C22GeneratedSubdivisionRegression (bases enumK enumEdges enumFaces)
open C23GeneratedStrictParameters
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules
attribute [local instance] C22GeneratedSubdivisionRegression.edgeDecidableEq C22GeneratedSubdivisionRegression.faceDecidableEq C22GeneratedSubdivisionRegression.allVerticesDecidable C22GeneratedSubdivisionRegression.allEdgesDecidable C22GeneratedSubdivisionRegression.allFacesDecidable C22GeneratedSubdivisionRegression.regionsVerticesDecidable C22GeneratedSubdivisionRegression.regionsEdgesDecidable C22GeneratedSubdivisionRegression.regionsFacesDecidable C22GeneratedSubdivisionRegression.fixedEdgesDecidable C22GeneratedSubdivisionRegression.fixedFacesDecidable
attribute [local instance] C22GeneratedSubdivisionRegression.bases._proof_1
attribute [local instance] C22GeneratedSubdivisionRegression.oldExtraction._proof_1
local notation "values" => (fun j => -CoverEquation.defect originalTower.toTower.localCoefficients fixedRegion
  (ActualEquation.defectFamily originalTower fixedRegion C19SubdivisionRangeRegression.fixed_faces) (regions j))

/-- Full actual restoration of every global generated output recovers the same independent new repair. -/
theorem actual_restore (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    (newExtraction S).symm (newGenerated S hs h r) = newActual S hs h r :=
  (newExtraction S).symm_apply_apply _

/-- Current full global generation restores precisely r on the original actual first factor. -/
theorem actual_first_coordinate (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    middleCoefficient (splitTower.solutionCorrection
      ((newExtraction S).symm (newGenerated S hs h r)).1 (firstEdgeName geometry chosen)) = r := by
  rw [actual_restore]
  exact restore_first_coordinate (oldRepairEquiv.symm h) r

/-- Current full global generation restores precisely h+r on the original actual second factor. -/
theorem actual_second_coordinate (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    middleCoefficient (splitTower.solutionCorrection
      ((newExtraction S).symm (newGenerated S hs h r)).1 (secondEdgeName geometry chosen)) = h+r := by
  rw [actual_restore]
  have hv := restore_second_coordinate (oldRepairEquiv.symm h) r
  rw [← old_parameter_correction,Equiv.apply_symm_apply] at hv
  exact hv

set_option maxRecDepth 32768 in
/-- The same two factor coordinates appear directly in each independent generated owner restoration. -/
theorem generated_factor_coordinates (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    middleCoefficient ((C22GeneratedSubdivisionRegression.newExtraction.symm ((newGenerated S hs h r).1 false)).1.1
      ⟨firstEdgeName geometry chosen,trivial⟩) = r ∧
    middleCoefficient ((C22GeneratedSubdivisionRegression.newExtraction.symm ((newGenerated S hs h r).1 false)).1.1
      ⟨secondEdgeName geometry chosen,trivial⟩) = h+r := by
  constructor
  · exact (congrArg (fun y => middleCoefficient
      ((C22GeneratedSubdivisionRegression.newExtraction.symm y).1.1
        ⟨firstEdgeName geometry chosen,trivial⟩)) (new_owner_component S hs h r)).trans
      (C22GeneratedSubdivisionRegression.generated_first_coordinate h r)
  · exact (congrArg (fun y => middleCoefficient
      ((C22GeneratedSubdivisionRegression.newExtraction.symm y).1.1
        ⟨secondEdgeName geometry chosen,trivial⟩)) (new_owner_component S hs h r)).trans
      (C22GeneratedSubdivisionRegression.generated_second_coordinate h r)

local notation "Mo" => originalTower.toTower.localCoefficients
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower splitTower))
local notation "Un" => (fun j => expandedRegion geometry chosen (regions j))
local notation "Pn" => expandedRegion geometry chosen fixedRegion
local notation "Cn" => oldEdgeSet geometry chosen (Set.singleton candidate)
attribute [local instance] GeneratedCoverAction.freshComm

/-- Each original strict label is zero because the same original vertex is physically fixed. -/
theorem old_label_zero (S : Set (EdgeName (K := geometry)))
    (b : StrictSupportedCover.Labels Mo fixedRegion regions {candidate} S) : b = 0 := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  apply Subtype.ext
  funext v
  exact (b.1 j).1.2 v trivial

/-- Every actual fresh displacement is an independent full strict label in every permission range. -/
noncomputable def freshLabel (S : Set (EdgeName (K := geometry))) (t : ZMod 3) :
    StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet geometry chosen S) :=
  (GeneratedCoverLabels.equivalence originalTower chosen factors regions fixedRegion {candidate} S false chosen_private).symm
    (0,middleCoefficient.symm t)

/-- Full fresh label comparison retains all t, with the entire original label zero. -/
theorem fresh_label_comparison (S : Set (EdgeName (K := geometry))) (t : ZMod 3) :
    GeneratedCoverLabels.equivalence originalTower chosen factors regions fixedRegion {candidate} S false chosen_private
      (freshLabel S t) = (0,middleCoefficient.symm t) :=
  (GeneratedCoverLabels.equivalence originalTower chosen factors regions fixedRegion {candidate} S false chosen_private).apply_symm_apply _

/-- Every full independent new strict label is exactly its entire native fresh displacement. -/
theorem fresh_labels_complete (S : Set (EdgeName (K := geometry)))
    (b : StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet geometry chosen S)) :
    b = freshLabel S (middleCoefficient
      (GeneratedCoverLabels.equivalence originalTower chosen factors regions fixedRegion {candidate} S false chosen_private b).2) := by
  apply (GeneratedCoverLabels.equivalence originalTower chosen factors regions fixedRegion {candidate} S false chosen_private).injective
  rw [fresh_label_comparison]
  apply Prod.ext
  · exact old_label_zero S _
  · exact (middleCoefficient.symm_apply_apply _).symm

set_option maxRecDepth 32768 in
/-- Every native fresh displacement acts on every independent global generated repair by r↦r+t. -/
theorem native_fresh_action (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r t : ZMod 3) :
    Multiplicative.ofAdd (freshLabel S t) • newGenerated S hs h r = newGenerated S hs h (r+t) := by
  apply (comparison S).injective
  have hv := GeneratedCoverAction.objects_equivariant originalTower chosen factors bases regions fixedRegion {candidate}
    false chosen_private C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces S values
    (Multiplicative.ofAdd (freshLabel S t)) (newGenerated S hs h r)
  change comparison S (Multiplicative.ofAdd (freshLabel S t) • newGenerated S hs h r) =
    Multiplicative.ofAdd (GeneratedCoverLabels.equivalence originalTower chosen factors regions fixedRegion {candidate} S false chosen_private
      (freshLabel S t)) • comparison S (newGenerated S hs h r) at hv
  calc
    comparison S (Multiplicative.ofAdd (freshLabel S t) • newGenerated S hs h r) =
        Multiplicative.ofAdd (GeneratedCoverLabels.equivalence originalTower chosen factors regions fixedRegion {candidate} S false chosen_private
          (freshLabel S t)) • comparison S (newGenerated S hs h r) := hv
    _ = Multiplicative.ofAdd (0,middleCoefficient.symm t) • (oldGenerated S hs h,middleCoefficient.symm r) :=
      congrArg₂ (fun b y => b • y) (congrArg Multiplicative.ofAdd (fresh_label_comparison S t))
        (compared_parameters S hs h r)
    _ = ((0 : StrictSupportedCover.Labels Mo fixedRegion regions {candidate} S) +ᵥ oldGenerated S hs h,middleCoefficient.symm r + middleCoefficient.symm t) :=
      SupplementalAction.product_action_value _ _
    _ = (oldGenerated S hs h,middleCoefficient.symm (r+t)) :=
      Prod.ext (zero_vadd (StrictSupportedCover.Labels Mo fixedRegion regions {candidate} S) _)
        (middleCoefficient.symm.map_add r t).symm
    _ = comparison S (newGenerated S hs h (r+t)) := (compared_parameters S hs h (r+t)).symm

set_option maxRecDepth 32768 in
/-- Every full new native label preserves h and acts by its entire actual fresh displacement. -/
theorem native_label_action (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S)
    (h r : ZMod 3) (b : StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet geometry chosen S)) :
    Multiplicative.ofAdd b • newGenerated S hs h r =
      newGenerated S hs h (r + middleCoefficient
        (GeneratedCoverLabels.equivalence originalTower chosen factors regions fixedRegion {candidate} S false chosen_private b).2) := by
  calc
    Multiplicative.ofAdd b • newGenerated S hs h r =
        Multiplicative.ofAdd (freshLabel S (middleCoefficient
          (GeneratedCoverLabels.equivalence originalTower chosen factors regions fixedRegion {candidate} S false chosen_private b).2)) •
          newGenerated S hs h r := congrArg (fun label => Multiplicative.ofAdd label • newGenerated S hs h r) (fresh_labels_complete S b)
    _ = _ := native_fresh_action S hs h r _

/-- The complete independent generated action category in every original permission range. -/
noncomputable def rangeGroupoid (S : Set (EdgeName (K := geometry))) :=
  ActionCategory
    (Multiplicative (StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet geometry chosen S)))
    (GeneratedStrictObjects.NewObjects originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
      values ({candidate} \ S))

/-- The complete native action category uses the standard category of elements structure. -/
noncomputable instance rangeGroupoidCategory (S : Set (EdgeName (K := geometry))) :
    Category (rangeGroupoid S) := CategoryTheory.instCategoryActionCategory _ _

/-- The canonical object of the full action category retains the entire independently generated family. -/
noncomputable def generatedObj (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    rangeGroupoid S := ⟨(),newGenerated S hs h r⟩

/-- Every fresh displacement is retained as a complete native arrow between the corresponding full generated repairs. -/
noncomputable def freshArrow (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r t : ZMod 3) :
    (generatedObj S hs h r) ⟶ (generatedObj S hs h (r+t)) :=
  ⟨Multiplicative.ofAdd (freshLabel S t),native_fresh_action S hs h r t⟩

end AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C23GeneratedStrictNativeRegression
