import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalEquations
import ResearchLean.AG.RelativeRepairComposition.C20SubdivisionCoverRegression

/-!
# The same W4 tests all local corrections, labels and the excluded supplement

## Implementation notes

The old solution is obtained from the independent whole affine repair family,
then its actual correction is restricted to the complete member. Every old
parameter and every first-factor value is restored by the general local map.
The second member is the original fixed vertex region: it has zero supplement
and explicitly rejects the same nonzero full fresh coefficient.
-/
namespace AAT.AG.RelativeRepairComposition.C21LocalSubdivisionRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine Subdivision C17SubdivisionInput

/-- The entire fresh coefficient is available in the complete original member. -/
noncomputable def supplement (r : ZMod 3) : localSupplement originalTower chosen factors ClosedRegion.all :=
  ⟨middleCoefficient.symm r,localSupplement_full originalTower chosen factors ClosedRegion.all trivial _⟩

/-- The independently defined full original repair supplies every old local correction value. -/
noncomputable def oldLocal (h : ZMod 3) :
    RelativeCover.C1 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion :=
  ⟨fun e => originalTower.solutionCorrection (oldRepairEquiv.symm h).1 e.1,
    fun _ hf => hf.elim⟩

/-- The same actual signed face defect supplies the local right-hand side. -/
noncomputable def actualRHS :
    RelativeCover.C2 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion :=
  ⟨fun f => -(originalTower.toTower.defect f.1),fun _ hf => hf.elim⟩

/-- Every independently generated actual old repair solves the same original local equation. -/
theorem oldLocal_equation (h : ZMod 3) :
    RelativeCover.d1 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion (oldLocal h) =
      actualRHS := by
  apply Subtype.ext
  have he : Family.extend
      (fun e : EdgeName (K := geometry) => originalTower.toTower.localCoefficients.A e.2.1)
      ClosedRegion.all.edges (oldLocal h).1 = originalTower.solutionCorrection (oldRepairEquiv.symm h).1 := by
    funext e
    exact Family.extend_on
      (fun e : EdgeName (K := geometry) => originalTower.toTower.localCoefficients.A e.2.1)
      ClosedRegion.all.edges (oldLocal h).1 e trivial
  funext f
  change d1 originalTower.toTower.localCoefficients (Family.extend _ ClosedRegion.all.edges (oldLocal h).1)
    f.1 = -(originalTower.toTower.defect f.1)
  rw [he]
  exact congrFun (originalTower.solutionCorrection_d1 (oldRepairEquiv.symm h).1) f.1

/-- The independent old local equation solution retains its full actual repair provenance. -/
noncomputable def oldLocalSolution (h : ZMod 3) :
    {c : RelativeCover.C1 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion //
      RelativeCover.d1 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion c = actualRHS} :=
  ⟨oldLocal h,oldLocal_equation h⟩

/-- Every old parameter and every fresh value generate a full new local equation solution. -/
noncomputable def newLocalSolution (h r : ZMod 3) :=
  (localEquationEquiv originalTower chosen factors ClosedRegion.all fixedRegion
    (by exact not_false) actualRHS).symm (oldLocalSolution h,supplement r)

/-- All local equation coordinates recover the independently supplied old correction and fresh value. -/
theorem newLocal_coordinates (h r : ZMod 3) :
    local1Equiv originalTower chosen factors ClosedRegion.all fixedRegion (by exact not_false)
      (newLocalSolution h r).1 = (oldLocal h,supplement r) :=
  localEquationEquiv_inverse_coordinates originalTower chosen factors ClosedRegion.all fixedRegion
    (by exact not_false) actualRHS (oldLocalSolution h) (supplement r)

/-- The first local factor really retains every r in the whole actual kernel. -/
theorem newLocal_first_coordinate (h r : ZMod 3) :
    middleCoefficient ((newLocalSolution h r).1.1 ⟨firstEdgeName geometry chosen,trivial⟩) = r := by
  change middleCoefficient (((local1Equiv originalTower chosen factors ClosedRegion.all fixedRegion
    (by exact not_false)).symm (oldLocal h,supplement r)).1
      ⟨firstEdgeName geometry chosen,trivial⟩) = r
  rw [local1Equiv_inverse_first]
  exact middleCoefficient.apply_symm_apply r

/-- The same old local chosen correction has precisely its independent full repair parameter. -/
theorem oldLocal_chosen_coordinate (h : ZMod 3) :
    middleCoefficient ((oldLocal h).1 ⟨chosen,trivial⟩) = h := by
  change middleCoefficient (originalTower.solutionCorrection (oldRepairEquiv.symm h).1 chosen) = h
  rw [← old_parameter_correction,Equiv.apply_symm_apply]

set_option maxHeartbeats 2000000 in
/-- The second local factor has h+r, retaining both independent full parameters. -/
theorem newLocal_second_coordinate (h r : ZMod 3) :
    middleCoefficient ((newLocalSolution h r).1.1 ⟨secondEdgeName geometry chosen,trivial⟩) = h+r := by
  change middleCoefficient (((local1Equiv originalTower chosen factors ClosedRegion.all fixedRegion
    (by exact not_false)).symm (oldLocal h,supplement r)).1
      ⟨secondEdgeName geometry chosen,trivial⟩) = h+r
  have hh := local1Equiv_inverse_second originalTower chosen factors ClosedRegion.all fixedRegion
    (by exact not_false) (oldLocal h) (supplement r) trivial
  have hv := congrArg middleCoefficient hh
  dsimp only at hv
  rw [map_sub,oldLocal_chosen_coordinate] at hv
  change middleCoefficient (((local1Equiv originalTower chosen factors ClosedRegion.all fixedRegion
    (by exact not_false)).symm (oldLocal h,supplement r)).1
      ⟨secondEdgeName geometry chosen,trivial⟩) = h -
    middleCoefficient (rho2Add originalTower chosen factors (middleCoefficient.symm r)) at hv
  rw [rho2_coordinate,AddEquiv.apply_symm_apply,sub_neg_eq_add] at hv
  exact hv

/-- All retained original local values, including b, keep their independent actual correction. -/
theorem newLocal_retained (h r : ZMod 3) (e : ClosedRegion.all.edges) (he : e.1 ≠ chosen) :
    (newLocalSolution h r).1.1 ⟨oldEdgeName geometry chosen e.1 he,e.2⟩ = (oldLocal h).1 e :=
  local1Equiv_inverse_old originalTower chosen factors ClosedRegion.all fixedRegion
    (by exact not_false) (oldLocal h) (supplement r) e he

/-- The same full authored face has its actual signed coordinate one after subdivision. -/
theorem local_actual_rhs_coordinate :
    middleCoefficient (-splitTower.toTower.defect ()) = (1 : ZMod 3) := by
  rw [map_neg,C18SubdivisionRegression.new_defect_coordinate,neg_neg]

/-- Every restored full local solution satisfies the actual signed defect equation on every original face. -/
theorem newLocal_actual_equation (h r : ZMod 3) :
    ∀ f : ClosedRegion.all.faces,
      (RelativeCover.d1 splitTower.toTower.localCoefficients
        (expandedRegion geometry chosen ClosedRegion.all) (expandedRegion geometry chosen fixedRegion)
        (newLocalSolution h r).1).1 f = -(splitTower.toTower.defect f.1) := by
  apply (local_actual_equation_iff originalTower chosen factors ClosedRegion.all fixedRegion
    (by exact not_false) (newLocalSolution h r).1).mpr
  rw [newLocal_coordinates]
  intro f
  exact congrArg (fun c : RelativeCover.C2 originalTower.toTower.localCoefficients
    ClosedRegion.all fixedRegion => c.1 f) (oldLocal_equation h)

/-- All old relative vertex labels are zero in this same W4 fixed-vertex input. -/
theorem old_label_zero
    (b : RelativeCover.C0 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion) : b = 0 := by
  apply Subtype.ext
  funext v
  exact b.2 v trivial

/-- A full arbitrary displacement generates its actual new local vertex label. -/
noncomputable def localFreshLabel (r : ZMod 3) :=
  (local0Equiv originalTower chosen factors ClosedRegion.all fixedRegion (by exact not_false)).symm
    (0,supplement r)

/-- The full new label has old coordinate zero and the entire prescribed displacement. -/
theorem localFreshLabel_coordinates (r : ZMod 3) :
    local0Equiv originalTower chosen factors ClosedRegion.all fixedRegion (by exact not_false)
      (localFreshLabel r) = (0,supplement r) :=
  (local0Equiv originalTower chosen factors ClosedRegion.all fixedRegion
    (by exact not_false)).apply_symm_apply _

/-- The same independent local differential keeps the full nonzero or zero displacement. -/
theorem localFreshLabel_d0 (r : ZMod 3) :
    local1Equiv originalTower chosen factors ClosedRegion.all fixedRegion (by exact not_false)
      (RelativeCover.d0 splitTower.toTower.localCoefficients
        (expandedRegion geometry chosen ClosedRegion.all) (expandedRegion geometry chosen fixedRegion)
        (localFreshLabel r)) = (0,supplement r) := by
  rw [local_d0,localFreshLabel_coordinates,map_zero]

/-- The first actual differential value of the local label is the full prescribed r. -/
theorem localFreshLabel_first_coordinate (r : ZMod 3) :
    middleCoefficient ((RelativeCover.d0 splitTower.toTower.localCoefficients
      (expandedRegion geometry chosen ClosedRegion.all) (expandedRegion geometry chosen fixedRegion)
      (localFreshLabel r)).1 ⟨firstEdgeName geometry chosen,trivial⟩) = r := by
  have hv := congrArg (fun x => x.2.1) (localFreshLabel_d0 r)
  dsimp only at hv
  rw [local1Equiv_first,Family.extend_on
    (fun e : EdgeName (K := presentation geometry chosen) => splitTower.toTower.localCoefficients.A e.2.1)
    (expandedRegion geometry chosen ClosedRegion.all).edges _ (firstEdgeName geometry chosen) trivial] at hv
  exact (congrArg middleCoefficient hv).trans (middleCoefficient.apply_symm_apply r)

/-- Every relative local label has zero supplement in the fixed vertex member. -/
theorem excluded_label_supplement
    (b : RelativeCover.C0 splitTower.toTower.localCoefficients
      (expandedRegion geometry chosen fixedRegion) (expandedRegion geometry chosen fixedRegion)) :
    (local0Equiv originalTower chosen factors fixedRegion fixedRegion (by exact not_false) b).2.1 = 0 :=
  localSupplement_zero originalTower chosen factors fixedRegion (by exact not_false) _

/-- Every local correction has zero supplement in the chosen-excluding fixed member. -/
theorem excluded_correction_supplement
    (h : RelativeCover.C1 splitTower.toTower.localCoefficients
      (expandedRegion geometry chosen fixedRegion) (expandedRegion geometry chosen fixedRegion)) :
    (local1Equiv originalTower chosen factors fixedRegion fixedRegion (by exact not_false) h).2.1 = 0 :=
  localSupplement_zero originalTower chosen factors fixedRegion (by exact not_false) _

/-- The same actual nonzero fresh kernel element is rejected by the excluded supplement. -/
theorem excluded_nonzero_rejected :
    C18SubdivisionRegression.freshOne ∉ localSupplement originalTower chosen factors fixedRegion := by
  intro h
  exact C18SubdivisionRegression.freshOne_ne_zero
    (localSupplement_zero originalTower chosen factors fixedRegion (by exact not_false)
      ⟨C18SubdivisionRegression.freshOne,h⟩)

end AAT.AG.RelativeRepairComposition.C21LocalSubdivisionRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C21LocalSubdivisionRegression
