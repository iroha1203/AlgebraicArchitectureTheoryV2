import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedActualNative
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedNativeRanges
import ResearchLean.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression

/-!
# Same whole affine W4 across every independent strict permission range

## Implementation notes

The original full affine tower, authored baa face, original candidate b,
fixed vertex region, full translation kernels and designated factors are the
same input. Both independently generated strict families use their complete
cover. Every parameter and every fresh value is restored to original actual
operations; forbidding b rejects every independently generated repair.
-/
namespace AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine Subdivision C17SubdivisionInput
open C20SubdivisionCoverRegression C21LocalSubdivisionRegression C22GeneratedSubdivisionRegression
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules
attribute [local instance] C22GeneratedSubdivisionRegression.edgeDecidableEq C22GeneratedSubdivisionRegression.faceDecidableEq C22GeneratedSubdivisionRegression.allVerticesDecidable C22GeneratedSubdivisionRegression.allEdgesDecidable C22GeneratedSubdivisionRegression.allFacesDecidable C22GeneratedSubdivisionRegression.regionsVerticesDecidable C22GeneratedSubdivisionRegression.regionsEdgesDecidable C22GeneratedSubdivisionRegression.regionsFacesDecidable C22GeneratedSubdivisionRegression.fixedEdgesDecidable C22GeneratedSubdivisionRegression.fixedFacesDecidable

/-- The same two original closed members are enumerated before any permission or repair parameter. -/
def enumRegions : FiniteElimination.Enumeration Bool := ⟨[false,true],by intro j; cases j <;> simp⟩

local notation "M" => originalTower.toTower.localCoefficients
local notation "values" => (fun j => -CoverEquation.defect M fixedRegion
  (ActualEquation.defectFamily originalTower fixedRegion C19SubdivisionRangeRegression.fixed_faces) (regions j))

/-- The owner's actual right-hand side is the same full authored baa signed defect. -/
theorem owner_rhs : values false = actualRHS := rfl

/-- The independent complete old strict generator is instantiated once for every permission range. -/
noncomputable def oldExtraction (S : Set (EdgeName (K := geometry))) :=
  GeneratedCoverRestoration.oldObjectEquiv originalTower bases regions fixedRegion {candidate}
    C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces C19SubdivisionRangeRegression.fixed_faces
    enumRegions regions_cover S

/-- The independent complete new strict generator is instantiated once for every original permission range. -/
noncomputable def newExtraction (S : Set (EdgeName (K := geometry))) :=
  GeneratedCoverRestoration.newObjectEquiv originalTower chosen factors bases regions fixedRegion {candidate}
    false chosen_private C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces C19SubdivisionRangeRegression.fixed_faces
    enumRegions regions_cover S

/-- Both independently instantiated full strict generators use the generic full comparison for every S. -/
noncomputable def comparison (S : Set (EdgeName (K := geometry))) :=
  GeneratedStrictObjects.rangeObjectsEquiv originalTower chosen factors bases regions fixedRegion {candidate}
    false chosen_private C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces S values

/-- Every parameter supplies the actual original repair precisely when the same public b is allowed. -/
noncomputable def oldActual (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h : ZMod 3) :
    SupportedRepair originalTower (fixedEdgesForRange fixedRegion.edges {candidate} S) :=
  ⟨(oldRepairEquiv.symm h).1,by
    rintro e (hp | ⟨he,hn⟩)
    · exact hp.elim
    · have heq : e = candidate := he
      exact False.elim (hn (heq.symm ▸ hs))⟩

/-- Every original repair parameter and every entire fresh-kernel value restore an actual supported new repair. -/
noncomputable def newActual (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :=
  expandSupported originalTower chosen factors (fixedEdgesForRange fixedRegion.edges {candidate} S)
    (oldActual S hs h) (middleCoefficient.symm r)

/-- Full old generated outputs retain every independent original actual repair parameter. -/
noncomputable def oldGenerated (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h : ZMod 3) :=
  oldExtraction S (oldActual S hs h)

/-- Full new generated outputs retain every original parameter and every actual fresh value. -/
noncomputable def newGenerated (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :=
  newExtraction S (newActual S hs h r)

/-- The full strict generated comparison reads exactly all original h and all fresh r. -/
theorem compared_parameters (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    comparison S (newGenerated S hs h r) = (oldGenerated S hs h,middleCoefficient.symm r) := by
  unfold newGenerated newExtraction newActual comparison oldGenerated oldExtraction
  rw [← GeneratedActualComparison.comparison_actual_restore,Equiv.apply_symm_apply]

/-- The old independently generated strict family exists exactly when the authored candidate b is allowed. -/
theorem old_nonempty_iff (S : Set (EdgeName (K := geometry))) :
    Nonempty (GeneratedStrictObjects.OldObjects originalTower bases regions fixedRegion {candidate}
      C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces values ({candidate} \ S)) ↔ candidate ∈ S := by
  constructor
  · rintro ⟨y⟩
    by_contra hn
    let R := (oldExtraction S).symm y
    exact forbidden_old_no_repair ⟨⟨R.1,by
      intro e he
      exact R.2 e (Or.inr ⟨he,fun hs => hn (by have heq : e = candidate := he; exact heq ▸ hs)⟩)⟩⟩
  · intro hs
    exact ⟨oldGenerated S hs 0⟩

/-- The independent new full strict family exists for exactly the same candidate permissions. -/
theorem new_nonempty_iff (S : Set (EdgeName (K := geometry))) :
    Nonempty (GeneratedStrictObjects.NewObjects originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces values ({candidate} \ S)) ↔ candidate ∈ S := by
  constructor
  · rintro ⟨y⟩
    exact (old_nonempty_iff S).mp ⟨(comparison S y).1⟩
  · intro hs
    exact ⟨newGenerated S hs 0 0⟩

/-- Allowing the same b leaves the entire independent old actual repair set unchanged. -/
noncomputable def oldActualEquiv (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) :
    SupportedRepair originalTower (fixedEdgesForRange fixedRegion.edges {candidate} S) ≃ ZMod 3 :=
  (show SupportedRepair originalTower (fixedEdgesForRange fixedRegion.edges {candidate} S) ≃ OldRepairs from
    { toFun R := ⟨R.1,by intro e he; exact he.elim⟩
      invFun R := ⟨R.1,by
        rintro e (hp | ⟨he,hn⟩)
        · exact hp.elim
        · have heq : e = candidate := he
          exact False.elim (hn (heq.symm ▸ hs))⟩
      left_inv _ := rfl
      right_inv _ := rfl }).trans oldRepairEquiv

/-- All independent old generated strict objects are precisely the full original h parameters. -/
noncomputable def oldGeneratedEquiv (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) :=
  (oldExtraction S).symm.trans (oldActualEquiv S hs)

/-- All independent new generated strict objects are precisely all full (h,r) parameters. -/
noncomputable def newGeneratedEquiv (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) :=
  (comparison S).trans (Equiv.prodCongr (oldGeneratedEquiv S hs) middleCoefficient.toEquiv)

/-- Every original h is recovered by the full independent old generated classification. -/
theorem old_parameters_value (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h : ZMod 3) :
    oldGeneratedEquiv S hs (oldGenerated S hs h) = h := by
  change oldActualEquiv S hs ((oldExtraction S).symm (oldExtraction S (oldActual S hs h))) = h
  rw [Equiv.symm_apply_apply]
  exact oldRepairEquiv.apply_symm_apply h

/-- Every full pair is recovered by the independent new generated classification. -/
theorem new_parameters_value (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h r : ZMod 3) :
    newGeneratedEquiv S hs (newGenerated S hs h r) = (h,r) := by
  change (oldGeneratedEquiv S hs (comparison S (newGenerated S hs h r)).1,
    middleCoefficient (comparison S (newGenerated S hs h r)).2) = (h,r)
  rw [compared_parameters,old_parameters_value,AddEquiv.apply_symm_apply]

/-- The same allowed W4 has all three independent original generated strict objects. -/
theorem old_generated_count (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) :
    Nat.card (GeneratedStrictObjects.OldObjects originalTower bases regions fixedRegion {candidate}
      C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces values ({candidate} \ S)) = 3 := by
  rw [Nat.card_congr (oldGeneratedEquiv S hs),Nat.card_eq_fintype_card,ZMod.card]

/-- The same allowed W4 has all nine independent new generated strict objects. -/
theorem new_generated_count (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) :
    Nat.card (GeneratedStrictObjects.NewObjects originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces values ({candidate} \ S)) = 9 := by
  rw [Nat.card_congr (newGeneratedEquiv S hs),Nat.card_prod,Nat.card_eq_fintype_card,ZMod.card]

/-- The full global old generated owner component is the same independently generated C22 local output. -/
theorem old_owner_component (S : Set (EdgeName (K := geometry))) (hs : candidate ∈ S) (h : ZMod 3) :
    (oldGenerated S hs h).1 false = C22GeneratedSubdivisionRegression.oldGenerated h := by
  apply C22GeneratedSubdivisionRegression.oldExtraction.symm.injective
  apply Subtype.ext
  apply Subtype.ext
  funext e
  have hv := RelativeActualGeneratedCover.forward_edge_value originalTower bases fixedRegion regions {candidate}
    C19SubdivisionRangeRegression.original_linear C19SubdivisionRangeRegression.fixed_faces enumK enumEdges enumFaces
    enumRegions regions_cover S (oldActual S hs h) false e
  exact hv.trans (by
    change originalTower.solutionCorrection (oldRepairEquiv.symm h).1 e.1 =
      (C22GeneratedSubdivisionRegression.oldExtraction.symm
        (C22GeneratedSubdivisionRegression.oldExtraction (oldLocalSolution h))).1.1 e
    rw [Equiv.symm_apply_apply]
    rfl)

end AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C23GeneratedStrictParameters
