import ResearchLean.AG.RelativeRepairComposition.C17SplitRepairCounts
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCorrection

/-! # W4's actual whole-kernel collapse and all first-factor restorations -/
namespace AAT.AG.RelativeRepairComposition.C17SubdivisionInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction NativeAffine
local notation "π" => projection (k := ZMod 3) (A := ZMod 3)
local notation "p₀" => GroupExtension.projection π
local notation "q₀" => GroupExtension.terminal (ZMod 3 ≃ₗ[ZMod 3] ZMod 3)

/-- The whole actual intermediate kernel inclusion evaluates precisely its original translation coordinate. -/
theorem middle_inclusion (a : Additive (Kernel p₀ q₀ factors.middle)) :
    FiberAut.hom (kernelInclusion p₀ q₀ factors.middle (Additive.toMul a)) =
      translation (k := ZMod 3) (middleCoefficient a) :=
  NativeAffine.coefficient_inclusion geometry reference reference comparison linear_faces () a

/-- The original full correction coordinate is the independent original repaired a value at zero. -/
theorem old_parameter_correction (R : OldRepairs) :
    oldRepairEquiv R = middleCoefficient (originalTower.solutionCorrection R.1 chosen) := by
  have hv := congrArg (fun g : Op => g 0)
    (NativeAffine.native_repair_correction_value geometry reference reference comparison linear_faces ∅ R
      (i := ()) (j := ()) false)
  change ((NativeAffine.repairEquivalence geometry reference reference comparison linear_faces ∅) R).operation
    (i := ()) (j := ()) false 0 = middleCoefficient (originalTower.solutionCorrection R.1 chosen)
  simpa only [reference,if_neg Bool.false_ne_true,AffineEquiv.coe_mul,Function.comp_apply,
    translation_apply,flip_apply,neg_zero,add_zero] using hv

/-- The specified second factor has the full negation linear transport. -/
theorem second_linear (x : ZMod 3) : second.linear x = -x := by
  have hm : π second = π flip := by simp [second,map_mul,projection_translation]
  change (π second) x = -x
  rw [hm]
  rfl

set_option maxHeartbeats 2000000 in
/-- The full actual second-factor kernel transport sends every translation coordinate to its negative. -/
theorem rho2_coordinate (a : Additive (Kernel p₀ q₀ factors.middle)) :
    middleCoefficient (Subdivision.rho2Add originalTower chosen factors a) = -middleCoefficient a := by
  have ht := GroupExtension.transport_hom π second (Additive.toMul a)
  change FiberAut.hom (kernelInclusion p₀ q₀ factors.middle
      (Additive.toMul (Subdivision.rho2Add originalTower chosen factors a))) =
    second * FiberAut.hom (kernelInclusion p₀ q₀ factors.middle (Additive.toMul a)) * second⁻¹ at ht
  rw [middle_inclusion,middle_inclusion,conjugation_translation] at ht
  have he := congrArg (fun g : Op => g 0) ht
  simpa only [translation_apply,add_zero,second_linear] using he

/-- On the entire actual new correction family, the old a correction is exactly v-u. -/
theorem collapse_coordinate (h : C1 splitTower.toTower.localCoefficients) :
    middleCoefficient (Subdivision.collapseCorrection originalTower chosen factors h chosen) =
      middleCoefficient (h (Subdivision.secondEdgeName geometry chosen)) -
        middleCoefficient (h (Subdivision.firstEdgeName geometry chosen)) := by
  rw [Subdivision.collapseCorrection_chosen]
  let v : Additive (Kernel p₀ q₀ factors.middle) := h (Subdivision.secondEdgeName geometry chosen)
  let u : Additive (Kernel p₀ q₀ factors.middle) := h (Subdivision.firstEdgeName geometry chosen)
  let b : Additive (Kernel p₀ q₀ factors.middle) := Subdivision.rho2Add originalTower chosen factors u
  change middleCoefficient (v + b) = _
  rw [map_add]
  change middleCoefficient v + middleCoefficient (Subdivision.rho2Add originalTower chosen factors u) = _
  simpa only [sub_eq_add_neg] using
    congrArg (fun z : ZMod 3 => middleCoefficient v + z) (rho2_coordinate u)

/-- Arbitrary full first-factor restoration really has coordinate r. -/
theorem restore_first_coordinate (R : OldRepairs) (r : ZMod 3) :
    middleCoefficient (splitTower.solutionCorrection
      (Subdivision.expandSupported originalTower chosen factors ∅ R (middleCoefficient.symm r)).1
        (Subdivision.firstEdgeName geometry chosen)) = r := by
  rw [Subdivision.expandSupported_correction]
  change middleCoefficient (Subdivision.expandCorrection originalTower chosen factors
    (originalTower.solutionCorrection R.1) (middleCoefficient.symm r)
      (Subdivision.firstEdgeName geometry chosen)) = r
  rw [Subdivision.expandCorrection_first,AddEquiv.apply_symm_apply]

/-- Every old full correction h and every full r restore the second-factor correction h+r. -/
theorem restore_second_coordinate (R : OldRepairs) (r : ZMod 3) :
    middleCoefficient (splitTower.solutionCorrection
      (Subdivision.expandSupported originalTower chosen factors ∅ R (middleCoefficient.symm r)).1
        (Subdivision.secondEdgeName geometry chosen)) =
      middleCoefficient (originalTower.solutionCorrection R.1 chosen) + r := by
  rw [Subdivision.expandSupported_correction]
  change middleCoefficient (Subdivision.expandCorrection originalTower chosen factors
    (originalTower.solutionCorrection R.1) (middleCoefficient.symm r)
      (Subdivision.secondEdgeName geometry chosen)) = _
  rw [Subdivision.expandCorrection_second]
  let c : Additive (Kernel p₀ q₀ factors.middle) := originalTower.solutionCorrection R.1 chosen
  let b : Additive (Kernel p₀ q₀ factors.middle) :=
    Subdivision.rho2Add originalTower chosen factors (middleCoefficient.symm r)
  change middleCoefficient (c - b) = _
  rw [map_sub]
  change middleCoefficient c - middleCoefficient
    (Subdivision.rho2Add originalTower chosen factors (middleCoefficient.symm r)) = _
  have he := congrArg (fun z : ZMod 3 => middleCoefficient c - z)
    (rho2_coordinate (middleCoefficient.symm r))
  simpa only [AddEquiv.apply_symm_apply,sub_neg_eq_add] using he

/-- Every independent original parameter h and every r restore the complete pair (u,v)=(r,h+r). -/
theorem restore_pair_coordinates (h r : ZMod 3) :
    middleCoefficient (splitTower.solutionCorrection
      (splitRepairEquiv.symm (h,r)).1 (Subdivision.firstEdgeName geometry chosen)) = r ∧
    middleCoefficient (splitTower.solutionCorrection
      (splitRepairEquiv.symm (h,r)).1 (Subdivision.secondEdgeName geometry chosen)) = h + r := by
  rw [all_split_restorations]
  constructor
  · exact restore_first_coordinate (oldRepairEquiv.symm h) r
  · rw [restore_second_coordinate,← old_parameter_correction,Equiv.apply_symm_apply]

end AAT.AG.RelativeRepairComposition.C17SubdivisionInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C17SubdivisionInput
