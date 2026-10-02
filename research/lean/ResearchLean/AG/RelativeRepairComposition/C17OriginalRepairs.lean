import ResearchLean.AG.RelativeRepairComposition.C17SubdivisionInput
import Mathlib.Tactic.LinearCombination

/-! # W4's entire independent original affine repair family
## Implementation notes

RealRepairs are defined independently by affine linear parts and the actual face equation. Evaluation at zero is proved to parametrize all operations, before transport to the generic native repair type. Defining repairs to be a chosen coordinate family would lose the reverse classification direction.
-/
namespace AAT.AG.RelativeRepairComposition.C17SubdivisionInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction NativeAffine
attribute [local instance] Classical.propDecidable

/-- All independent actual original repairs when the original candidate b is allowed. -/
abbrev RealRepairs := NativeAffine.Repair geometry reference comparison ∅
/-- Every arbitrary original repaired operation is determined by its fixed linear part and full value at zero. -/
theorem operation_value (R : RealRepairs) {i j : geometry.Vertex} (e : geometry.Edge i j) (x : ZMod 3) :
    R.operation e x = (if (e : Bool) = true then x else -x) + R.operation e 0 := by
  rw [NativeAffine.operation_apply,R.linear]
  cases e
  · simp only [reference,if_neg Bool.false_ne_true]
    change (-x) + _ = (-x) + _
    rfl
  · simp only [reference]
    rfl

/-- The actual whole authored face forces b to translate by precisely one. -/
theorem candidate_value_one (R : RealRepairs) : R.operation (i := ()) (j := ()) true 0 = 1 := by
  have h := congrArg (fun g : Op => g 0) (R.face ())
  change ((translation (k := ZMod 3) (-1) *
    ((1 : Op) * R.operation (i := ()) (j := ()) false * R.operation (i := ()) (j := ()) false *
      R.operation (i := ()) (j := ()) true)) : Op) 0 = (1 : Op) 0 at h
  simp only [AffineEquiv.coe_mul,Function.comp_apply,translation_apply,
    AffineEquiv.coe_one,id_eq] at h
  rw [operation_value R (i := ()) (j := ()) false
    (R.operation (i := ()) (j := ()) false (R.operation (i := ()) (j := ()) true 0)),
    operation_value R (i := ()) (j := ()) false (R.operation (i := ()) (j := ()) true 0)] at h
  simp only [if_neg Bool.false_ne_true] at h
  linear_combination h

/-- The original repair parameter records the full actual a-translation. -/
def repairParameter (R : RealRepairs) : ZMod 3 := R.operation (i := ()) (j := ()) false 0
/-- W4's actual repaired a is -x+h and its actual repaired b is x+1 for every vector. -/
theorem all_original_operations (R : RealRepairs) {i j : geometry.Vertex}
    (e : geometry.Edge i j) (x : ZMod 3) :
    R.operation e x = if (e : Bool) = true then x + 1 else -x + repairParameter R := by
  cases i
  cases j
  cases e
  · simpa only [Bool.false_eq_true,if_neg Bool.false_ne_true] using operation_value R false x
  · rw [if_pos rfl]
    have hx := operation_value R (i := ()) (j := ()) true x
    rw [if_pos rfl,candidate_value_one R] at hx
    exact hx

/-- Every full original translation parameter generates actual repaired operations. -/
noncomputable def repairedOperations (h : ZMod 3) : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => if (e : Bool) = true then translation (k := ZMod 3) 1 else translation (k := ZMod 3) h * flip
/-- Every parameter defines an independent actual repair, using the actual full face word. -/
noncomputable def actualRepair (h : ZMod 3) : RealRepairs where
  operation := repairedOperations h
  linear := by
    intro i j e
    change projection (repairedOperations h e) = projection (reference e)
    cases e <;> simp [repairedOperations,reference,map_mul,projection_translation]
  face := by
    intro f
    ext x
    simp only [geometry,comparison,GroupExtension.pathValue,repairedOperations,
      if_true,if_neg Bool.false_ne_true,AffineEquiv.coe_mul,Function.comp_apply,
      AffineEquiv.coe_one,id_eq,translation_apply,flip_apply]
    abel
  fixed_value := by intro e he; exact he.elim

/-- Actual repair reconstruction recovers every original full parameter. -/
theorem actualRepair_parameter (h : ZMod 3) : repairParameter (actualRepair h) = h := by
  simp [repairParameter,actualRepair,repairedOperations,AffineEquiv.coe_mul,flip_apply]
/-- Every independently supplied actual repair is reconstructed on every original full operation. -/
theorem parameter_actualRepair (R : RealRepairs) : actualRepair (repairParameter R) = R := by
  apply NativeAffine.Repair.ext
  intro i j e
  ext x
  rw [all_original_operations R e x]
  cases e <;> simp [actualRepair,repairedOperations,AffineEquiv.coe_mul,Function.comp_apply,flip_apply,add_comm]
/-- The entire independent original actual repair set has precisely the three full F3 parameters. -/
noncomputable def realRepairEquiv : RealRepairs ≃ ZMod 3 where
  toFun := repairParameter
  invFun := actualRepair
  left_inv := parameter_actualRepair
  right_inv := actualRepair_parameter

/-- The native original repair set uses the same original affine tower with candidate b allowed. -/
abbrev OldRepairs := SupportedRepair originalTower ∅
/-- The entire actual native original repair set is precisely F3. -/
noncomputable def oldRepairEquiv : OldRepairs ≃ ZMod 3 :=
  (NativeAffine.repairEquivalence geometry reference reference comparison linear_faces ∅).trans realRepairEquiv

end AAT.AG.RelativeRepairComposition.C17SubdivisionInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C17SubdivisionInput
