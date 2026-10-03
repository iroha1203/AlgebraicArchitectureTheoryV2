import ResearchLean.AG.RepairObservationDuality.FiberSufficiency
import ResearchLean.AG.RelativeRepairComposition.FiniteMatrixInterface

/-!
# G-131 D: finite symbolic sections and fully evaluated correction answers

## Implementation notes

The G-130 finite elimination generates a section from the same whole
matrix before RHS values are acquired. The returned option is a complete
vector. No solvability or preselected section is an algorithm input.
-/
namespace AAT.AG.RepairObservationDuality.FiniteMatrixSolver
open RelativeRepairComposition
universe uk ui
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {m n : Type ui} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumM : FiniteElimination.Enumeration m) (enumN : FiniteElimination.Enumeration n)
variable (D : Matrix m n k)

/-- D's full differential is the given finite matrix, with every original coordinate retained. -/
def differential : (n → k) →ₗ[k] (m → k) := Matrix.toLin' D

omit [Fintype k] [DecidableEq k] [Fintype m] [DecidableEq m] in
/-- Every differential value is the actual known matrix multiplication. -/
theorem differential_apply (x : n → k) : differential D x = D.mulVec x := rfl

/-- D's symbolic image section is generated once from G-130's finite elimination. -/
def generatedSection : (m → k) →ₗ[k] (n → k) := FiniteMatrixInterface.linearSection enumK enumM enumN D

/-- The generated section reproduces the whole original differential image. -/
theorem section_regular (x : n → k) :
    differential D (generatedSection enumK enumM enumN D (differential D x)) = differential D x :=
  FiniteMatrixInterface.section_regular enumK enumM enumN D x

/-- D's full numerical answer is either a computed vector or definite impossibility. -/
def solve (r : m → k) : Option (n → k) :=
  let x := generatedSection enumK enumM enumN D r
  if differential D x = r then some x else none

/-- Every successful finite answer is its actual section vector and satisfies the original equation. -/
theorem solve_some_iff (r : m → k) (x : n → k) :
    solve enumK enumM enumN D r = some x ↔
      x = generatedSection enumK enumM enumN D r ∧ differential D x = r := by
  simp only [solve]
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun he => ⟨he.symm, he ▸ h⟩,fun hx => hx.1.symm⟩
  · simp only [false_iff, not_and]
    intro he hx
    exact h (he ▸ hx)

/-- The finite failure answer is exactly nonexistence of a full correction. -/
theorem solve_none_iff (r : m → k) :
    solve enumK enumM enumN D r = none ↔ ¬ ∃ x, differential D x = r := by
  simp only [solve]
  split_ifs with h
  · simp only [false_iff]
    exact not_not.mpr ⟨_,h⟩
  · simp only [true_iff]
    rintro ⟨x,hx⟩
    apply h
    rw [← hx, section_regular]

/-- D's generated numerical solver returns a valid complete output for every acquired RHS. -/
theorem solve_valid {V : Type*} (rhs : V → (m → k)) (v : V) :
    ValidOutput (differential D) rhs v (solve enumK enumM enumN D (rhs v)) := by
  cases he : solve enumK enumM enumN D (rhs v) with
  | none =>
      rw [validOutput_none_iff]
      exact (solve_none_iff enumK enumM enumN D (rhs v)).mp he
  | some x =>
      rw [validOutput_some_iff]
      exact ((solve_some_iff enumK enumM enumN D (rhs v) x).mp he).2

/-- D's symbolic decision direction is an executable representative of the same residual class. -/
def residual : (m → k) →ₗ[k] (m → k) :=
  LinearInterface.projection (differential D) (generatedSection enumK enumM enumN D)

/-- Residual zero is exactly solvability of the same whole matrix equation. -/
theorem residual_zero_iff (r : m → k) :
    residual enumK enumM enumN D r = 0 ↔ ∃ x, differential D x = r :=
  LinearInterface.projection_eq_zero_iff (differential D) (generatedSection enumK enumM enumN D)
    (section_regular enumK enumM enumN D) r

/-- D's executable residual and the native cokernel have exactly the same pullback kernel. -/
theorem residual_comp_ker {V : Type*} [AddCommGroup V] [Module k V]
    (B : V →ₗ[k] (m → k)) :
    LinearMap.ker ((residual enumK enumM enumN D).comp B) =
      LinearMap.ker ((LinearMap.range (differential D)).mkQ.comp B) := by
  ext v
  change residual enumK enumM enumN D (B v) = 0 ↔
    (LinearMap.range (differential D)).mkQ (B v) = 0
  exact (residual_zero_iff enumK enumM enumN D (B v)).trans
    (Submodule.Quotient.mk_eq_zero (LinearMap.range (differential D))).symm

end AAT.AG.RepairObservationDuality.FiniteMatrixSolver
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FiniteMatrixSolver
