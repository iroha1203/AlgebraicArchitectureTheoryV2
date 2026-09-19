import ResearchLean.AG.LocalSemanticReconstruction.IndependentPolynomialPointTransport
import Mathlib.Algebra.Ring.Prod
import Formal.Util.AssertStandardAxioms

/-!
# Noninjective coefficient and missing-monomial controls

Implementation notes: projection from the product ring kills a nonzero
coefficient and must remain accepted by the raw point criterion. Conversely,
a target monomial absent from the source support must be rejected. These
controls exercise the reason every exponent pair is tested, rather than
checking only the source polynomial's nonzero support.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentPolynomialPointTransport.Controls

noncomputable section

open IndependentPolynomialExpressions

/-- A single coordinate with its identity correspondence. -/
def coordinate (c d : Unit) : Bool := decide (c = d)

/-- The directed coefficient graph is projection onto the first integer factor. -/
def coefficient (a : ℤ × ℤ) (b : ℤ) : Bool := decide (a.1 = b)

/-- The coefficient graph sends two distinct source values to zero. -/
theorem distinct_coefficients_share_image :
    coefficient (0, 0) 0 = true ∧ coefficient (0, 1) 0 = true ∧ ((0, 0) : ℤ × ℤ) ≠ (0, 1) := by
  norm_num [coefficient]

/-- A nonzero coefficient annihilated by the directed map is admitted by all primitive polynomial points. -/
theorem annihilated_coefficient_admitted : PointLaws coordinate coefficient
    (sparseEquiv (MvPolynomial.C ((0, 1) : ℤ × ℤ) * MvPolynomial.X () : MvPolynomial Unit (ℤ × ℤ)))
    (sparseEquiv (0 : MvPolynomial Unit ℤ)) := by
  apply (points_iff_rename_map (Equiv.refl Unit) (RingHom.fst ℤ ℤ) coordinate coefficient
    (fun c d => by simp [coordinate]) (fun a b => by simp [coefficient]) _ _).2
  simp

/-- An extra target monomial is rejected even when the source polynomial has empty support. -/
theorem extra_target_monomial_rejected : ¬ PointLaws coordinate coefficient
    (sparseEquiv (0 : MvPolynomial Unit (ℤ × ℤ)))
    (sparseEquiv (MvPolynomial.X () : MvPolynomial Unit ℤ)) := by
  intro hp
  have he := (points_iff_rename_map (Equiv.refl Unit) (RingHom.fst ℤ ℤ) coordinate coefficient
    (fun c d => by simp [coordinate]) (fun a b => by simp [coefficient]) _ _).1 hp
  have hz : (0 : MvPolynomial Unit ℤ) = MvPolynomial.X () := by simpa using he
  exact MvPolynomial.X_ne_zero () hz.symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentPolynomialPointTransport.Controls

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentPolynomialPointTransport.Controls
