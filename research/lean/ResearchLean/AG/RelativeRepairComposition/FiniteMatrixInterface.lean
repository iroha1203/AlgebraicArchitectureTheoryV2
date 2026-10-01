import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteElimination
import ResearchLean.AG.RelativeRepairComposition.LinearInterface
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Generated finite sections applied to complete linear interfaces

## Implementation notes

Every section law needed by the generic interface is proved here from the
finite algorithm on D. Neither a section nor a solution is an input field.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteMatrixInterface
open FiniteElimination
universe uk ui
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {m n : Type ui} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (enumK : Enumeration k) (enumM : Enumeration m) (enumN : Enumeration n)
variable (D : Matrix m n k)

/-- Generate a linear section once from the finite original differential. -/
def linearSection : (m → k) →ₗ[k] (n → k) :=
  Matrix.toLin' (rectangularSection enumK enumN enumM D)

/-- The generated section has the complete image right-inverse law. -/
theorem section_regular (x : n → k) : Matrix.toLin' D (linearSection enumK enumM enumN D (Matrix.toLin' D x)) =
    Matrix.toLin' D x := by
  simp only [linearSection,Matrix.toLin'_apply,Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc,rectangularSection_regular enumK enumN enumM D]

end AAT.AG.RelativeRepairComposition.FiniteMatrixInterface

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
