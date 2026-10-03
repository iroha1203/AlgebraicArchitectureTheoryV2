import ResearchLean.AG.RelativeRepairComposition.W3AffineInput

/-!
# W3's actual full operation family and original loop evaluation

The two translation corrections are arbitrary vectors before any permission
or gauge quotient is imposed. The original loop is the actual composition f e.
-/
namespace AAT.AG.RelativeRepairComposition.W3AuthoredOperations
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput

/-- Both entire correction vectors on the original edge names. -/
def correctionValue (u v : A) (e : Fin 2) : A := if e = edgeE then u else v

/-- Arbitrary full corrected operations on both original typed edges. -/
def operation (sheared : Bool) (u v : A) :
    ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => translation (k := ZMod 3) (correctionValue u v e.1) * reference sheared e

/-- Every original reference fixes the actual zero vector. -/
theorem reference_zero (sheared : Bool) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    reference sheared e 0 = 0 := by
  unfold reference
  split
  · exact (linearAction sheared).map_zero
  · rfl

/-- Each original actual reference agrees with its full linear part on every vector. -/
theorem reference_apply (sheared : Bool) {i j : geometry.Vertex} (e : geometry.Edge i j)
    (x : A) : reference sheared e x = (reference sheared e).linear x := by
  rw [NativeAffine.operation_apply, reference_zero, add_zero]

/-- Original e's actual operation keeps the entire arbitrary u. -/
theorem operation_e_apply (sheared : Bool) (u v x : A) :
    operation sheared u v (name edgeE).2.2 x = x + u := by
  change (translation (k := ZMod 3) u * reference sheared (name edgeE).2.2) x = _
  rw [reference_e]
  exact add_comm u x

/-- Original f's actual operation keeps the specified full T and arbitrary v. -/
theorem operation_f_apply (sheared : Bool) (u v x : A) :
    operation sheared u v (name edgeF).2.2 x = linearAction sheared x + v := by
  change (translation (k := ZMod 3) v * reference sheared (name edgeF).2.2) x = _
  rw [reference_f]
  exact add_comm v (linearAction sheared x)

/-- Correcting the original edge preserves its entire actual linear component. -/
theorem operation_linear (sheared : Bool) (u v : A)
    {i j : geometry.Vertex} (e : geometry.Edge i j) :
    (operation sheared u v e).linear = (reference sheared e).linear := by
  change projection (operation sheared u v e) = projection (reference sheared e)
  rw [operation, map_mul, projection_translation, one_mul]

/-- The original full path traverses e then f. -/
def loopPath : geometry.Path vertexS vertexS :=
  .cons (name edgeE).2.2 (.cons (name edgeF).2.2 (.nil vertexS))

/-- The loop coordinate is derived from the two actual corrections. -/
def loopValue (sheared : Bool) (u v : A) : A := v + linearAction sheared u

/-- Actual original composition evaluates to T x plus v+T u on all vectors. -/
theorem loop_apply (sheared : Bool) (u v x : A) :
    GroupExtension.pathValue geometry (operation sheared u v) loopPath x =
      linearAction sheared x + loopValue sheared u v := by
  change operation sheared u v (name edgeF).2.2
    (operation sheared u v (name edgeE).2.2 x) = _
  rw [operation_e_apply, operation_f_apply, map_add]
  unfold loopValue
  abel

/-- Every original corrected operation at zero recovers precisely its original correction vector. -/
theorem operation_zero (sheared : Bool) (u v : A)
    {i j : geometry.Vertex} (e : geometry.Edge i j) :
    operation sheared u v e 0 = correctionValue u v e.1 := by
  change translation (k := ZMod 3) (correctionValue u v e.1) (reference sheared e 0) = _
  rw [reference_zero]
  exact add_zero _

end AAT.AG.RelativeRepairComposition.W3AuthoredOperations
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3AuthoredOperations
