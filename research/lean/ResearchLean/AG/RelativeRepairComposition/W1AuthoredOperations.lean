import ResearchLean.AG.RelativeRepairComposition.W1AffineInput
import Mathlib.Tactic.Abel

/-!
# W1 equations from the original actual affine words

## Implementation notes

The operation family is defined before imposing either Law. Its translations
are arbitrary on the four original nonfixed edges; rx and ry remain the given
actual input operations. The theorems below evaluate the whole affine maps,
so the equations are derived from the authored temporal paths rather than
supplied as a repair certificate. Independent repairs remain NativeAffine.Repair.
-/
namespace AAT.AG.RelativeRepairComposition.W1AuthoredOperations
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput

/-- The four arbitrary original translation corrections retain u,h,z,v and zero on physical rx,ry. -/
def correctionValue (u h z v : ZMod 3) (e : Fin 6) : ZMod 3 :=
  if e = edgeE then u else if e = edgeA then h else if e = edgeB then z
  else if e = edgeC then v else 0

/-- Arbitrary corrected actual affine operations on the same six original names, before either face Law is imposed. -/
noncomputable def operation (negative : Bool) (x y u h z v : ZMod 3) :
    ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => translation (k := ZMod 3) (correctionValue u h z v (e : Fin 6)) * reference negative x y e

/-- The same original linear a evaluates as negation or identity on every point. -/
theorem linearA_apply (negative : Bool) (t : ZMod 3) :
    linearA negative t = if negative then -t else t := by
  cases negative <;> simp [linearA, flip_apply]

/-- Original e's actual operation is its full arbitrary translation. -/
theorem operation_e_apply (negative : Bool) (x y u h z v t : ZMod 3) :
    operation negative x y u h z v (i := ()) (j := ()) edgeE t = t + u := by
  simp [geometry, operation, correctionValue, reference, edgeE, edgeA, edgeRx, edgeRy, add_comm]

/-- Original a keeps the specified linear component and its full private correction h. -/
theorem operation_a_apply (negative : Bool) (x y u h z v t : ZMod 3) :
    operation negative x y u h z v (i := ()) (j := ()) edgeA t = linearA negative t + h := by
  simp [geometry, operation, correctionValue, reference, edgeE, edgeA, AffineEquiv.coe_mul, Function.comp_apply, add_comm]

/-- Original candidate b has the full correction z, on the same candidate name. -/
theorem operation_b_apply (negative : Bool) (x y u h z v t : ZMod 3) :
    operation negative x y u h z v (i := ()) (j := ()) edgeB t = t + z := by
  simp [geometry, operation, correctionValue, reference, edgeE, edgeA, edgeB, edgeRx, edgeRy, add_comm]

/-- Original candidate c has the full correction v, without changing any other original operation. -/
theorem operation_c_apply (negative : Bool) (x y u h z v t : ZMod 3) :
    operation negative x y u h z v (i := ()) (j := ()) edgeC t = t + v := by
  simp [geometry, operation, correctionValue, reference, edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy, add_comm]

/-- The physically fixed rx actual operation remains the given input translation. -/
theorem operation_rx_apply (negative : Bool) (x y u h z v t : ZMod 3) :
    operation negative x y u h z v (i := ()) (j := ()) edgeRx t = t + x := by
  simp [geometry, operation, correctionValue, reference, edgeE, edgeA, edgeB, edgeC, edgeRx, AffineEquiv.coe_mul, Function.comp_apply, add_comm]

/-- The physically fixed ry actual operation remains the given input translation. -/
theorem operation_ry_apply (negative : Bool) (x y u h z v t : ZMod 3) :
    operation negative x y u h z v (i := ()) (j := ()) edgeRy t = t + y := by
  simp [geometry, operation, correctionValue, reference, edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy, AffineEquiv.coe_mul, Function.comp_apply, add_comm]

/-- Evaluating the complete first authored left word derives u+z from actual composition. -/
theorem first_left_apply (negative : Bool) (x y u h z v t : ZMod 3) :
    GroupExtension.pathValue geometry (operation negative x y u h z v) (geometry.twoLeft false) t =
      t + (u + z) := by
  change operation negative x y u h z v (i := ()) (j := ()) edgeE (operation negative x y u h z v (i := ()) (j := ()) edgeB t) = _
  rw [operation_e_apply, operation_b_apply]
  abel

/-- Both original right paths keep the same actual physical input operations. -/
theorem right_apply (negative : Bool) (x y u h z v t : ZMod 3) (f : geometry.TwoCell) :
    GroupExtension.pathValue geometry (operation negative x y u h z v) (geometry.twoRight f) t =
      t + (if (f : Bool) = true then y else x) := by
  cases f
  · change operation negative x y u h z v (i := ()) (j := ()) edgeRx t = _
    exact operation_rx_apply negative x y u h z v t
  · change operation negative x y u h z v (i := ()) (j := ()) edgeRy t = _
    exact operation_ry_apply negative x y u h z v t

/-- The negative holonomy transports b's z with a minus sign while both actual h terms cancel. -/
theorem second_negative_apply (x y u h z v t : ZMod 3) :
    GroupExtension.pathValue geometry (operation true x y u h z v) (geometry.twoLeft true) t =
      t + (u - z + v) := by
  change operation true x y u h z v (i := ()) (j := ()) edgeE
    (operation true x y u h z v (i := ()) (j := ()) edgeA
      (operation true x y u h z v (i := ()) (j := ()) edgeB
        (operation true x y u h z v (i := ()) (j := ()) edgeA (operation true x y u h z v (i := ()) (j := ()) edgeC t)))) = _
  rw [operation_e_apply, operation_a_apply, operation_b_apply, operation_a_apply, operation_c_apply]
  change -(-(t + v) + h + z) + h + u = t + (u - z + v)
  abel

/-- Changing only a's original linear part to identity retains both h terms on the same authored word. -/
theorem second_identity_apply (x y u h z v t : ZMod 3) :
    GroupExtension.pathValue geometry (operation false x y u h z v) (geometry.twoLeft true) t =
      t + (u + 2 * h + z + v) := by
  change operation false x y u h z v (i := ()) (j := ()) edgeE
    (operation false x y u h z v (i := ()) (j := ()) edgeA
      (operation false x y u h z v (i := ()) (j := ()) edgeB
        (operation false x y u h z v (i := ()) (j := ()) edgeA (operation false x y u h z v (i := ()) (j := ()) edgeC t)))) = _
  rw [operation_e_apply, operation_a_apply, operation_b_apply, operation_a_apply, operation_c_apply]
  change ((t + v + h) + z) + h + u = t + (u + 2 * h + z + v)
  simp only [two_mul]
  abel

/-- The entire actual first Law is equivalent to the derived scalar equation, in both directions. -/
theorem first_law_iff (negative : Bool) (x y u h z v : ZMod 3) :
    GroupExtension.pathValue geometry (operation negative x y u h z v) (geometry.twoLeft false) =
      GroupExtension.pathValue geometry (operation negative x y u h z v) (geometry.twoRight false) ↔
        u + z = x := by
  constructor
  · intro hword
    have hzero := congrArg (fun g : Op => g 0) hword
    simpa only [first_left_apply, right_apply, Bool.false_eq_true, ite_false, zero_add] using hzero
  · intro heq
    ext t
    rw [first_left_apply, right_apply]
    simpa only [Bool.false_eq_true, ite_false] using congrArg (t + ·) heq

/-- The entire actual negative-holonomy second Law is equivalent to u-z+v=y, without assuming repairability. -/
theorem second_negative_law_iff (x y u h z v : ZMod 3) :
    GroupExtension.pathValue geometry (operation true x y u h z v) (geometry.twoLeft true) =
      GroupExtension.pathValue geometry (operation true x y u h z v) (geometry.twoRight true) ↔
        u - z + v = y := by
  constructor
  · intro hword
    have hzero := congrArg (fun g : Op => g 0) hword
    simpa only [second_negative_apply, right_apply, zero_add] using hzero
  · intro heq
    ext t
    rw [second_negative_apply, right_apply]
    simpa only [] using congrArg (t + ·) heq

/-- The entire actual identity-holonomy second Law derives the two surviving h corrections on the same geometry. -/
theorem second_identity_law_iff (x y u h z v : ZMod 3) :
    GroupExtension.pathValue geometry (operation false x y u h z v) (geometry.twoLeft true) =
      GroupExtension.pathValue geometry (operation false x y u h z v) (geometry.twoRight true) ↔
        u + 2 * h + z + v = y := by
  constructor
  · intro hword
    have hzero := congrArg (fun g : Op => g 0) hword
    simpa only [second_identity_apply, right_apply, zero_add] using hzero
  · intro heq
    ext t
    rw [second_identity_apply, right_apply]
    simpa only [] using congrArg (t + ·) heq

end AAT.AG.RelativeRepairComposition.W1AuthoredOperations
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1AuthoredOperations
