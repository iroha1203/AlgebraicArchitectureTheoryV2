import Formal.SHIGURE.Part2.Quantities.Representation
import Mathlib.Algebra.Polynomial.Laurent

/-!
# A quantity and its inverse

Example 5.7 gives the Laurent polynomial algebra by imposing the one written
equation on a pair of point quantities.
-/

universe u

noncomputable section

namespace SHIGURE.Quantities

variable (k : Type u) [CommRing k] {sig : Signature.{u}} (A : Structure sig)

/-- The two point quantities and the written condition that their product is one. -/
def inversePresentation : Presentation k A where
  Quantity := ULift.{u} Bool
  Domain _ := PUnit
  Law := PUnit
  Input _ := PUnit
  left _ _ := .mul (.quantity ⟨⟨false⟩, PUnit.unit⟩) (.quantity ⟨⟨true⟩, PUnit.unit⟩)
  right _ _ := .scalar 1

variable {R : Type u} [CommRing R] [Algebra k R]

/-- A unit and its inverse give values to the two quantities. -/
def inverseModel (x : Rˣ) : (inversePresentation k A).Model R :=
  ⟨fun j _ => if j.down then ↑x⁻¹ else ↑x, by
    intro _ _
    change (↑x : R) * ↑x⁻¹ = algebraMap k R 1
    rw [map_one, Units.mul_inv]⟩

/-- The written equation makes the first value a unit with the second value as inverse. -/
def unitOfInverseModel (q : (inversePresentation k A).Model R) : Rˣ :=
  Units.mkOfMulEqOne (q.val ⟨false⟩ PUnit.unit) (q.val ⟨true⟩ PUnit.unit) (by
    have h : q.val ⟨false⟩ PUnit.unit * q.val ⟨true⟩ PUnit.unit = algebraMap k R 1 :=
      q.property PUnit.unit PUnit.unit
    simpa only [map_one] using h)

/-- The exponent-one Laurent monomial and its inverse are the universal values. -/
private def laurentUnit : (LaurentPolynomial k)ˣ :=
  Units.mkOfMulEqOne (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)) (by
    rw [← LaurentPolynomial.T_add]
    exact LaurentPolynomial.T_zero)

/-- The Law algebra of the inverse presentation is the Laurent polynomial algebra. -/
def inverseLawAlgebraEquiv : (inversePresentation k A).LawAlgebra ≃ₐ[k] LaurentPolynomial k := by
  let P := inversePresentation k A
  let q := inverseModel k A (laurentUnit k)
  let f := P.modelAlgHomEquiv q
  let x := unitOfInverseModel k A P.universalModel
  let g : LaurentPolynomial k →ₐ[k] P.LawAlgebra :=
    ⟨LaurentPolynomial.eval₂ (algebraMap k P.LawAlgebra) x, LaurentPolynomial.eval₂_C _ _⟩
  have hx : g (LaurentPolynomial.T 1) = P.universalModel.val ⟨false⟩ PUnit.unit := by
    change LaurentPolynomial.eval₂ (algebraMap k P.LawAlgebra) x (LaurentPolynomial.T 1) = _
    rw [LaurentPolynomial.eval₂_T]
    simp only [zpow_one]
    rfl
  have hy : g (LaurentPolynomial.T (-1)) = P.universalModel.val ⟨true⟩ PUnit.unit := by
    change LaurentPolynomial.eval₂ (algebraMap k P.LawAlgebra) x (LaurentPolynomial.T (-1)) = _
    rw [LaurentPolynomial.eval₂_T]
    simp only [zpow_neg, zpow_one]
    rfl
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k))
    apply Polynomial.ringHom_ext
    · intro a
      change f (g (Polynomial.toLaurent (Polynomial.C a))) = Polynomial.toLaurent (Polynomial.C a)
      rw [Polynomial.toLaurent_C, LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes]
    · change f (g (Polynomial.toLaurent (Polynomial.X : Polynomial k))) = Polynomial.toLaurent Polynomial.X
      rw [Polynomial.toLaurent_X, hx, P.universalModel_value]
      exact P.evaluate_X q.val ⟨⟨false⟩, PUnit.unit⟩
  · rw [← P.modelAlgHomEquiv_natural]
    have h : P.map g q = P.universalModel := by
      apply Subtype.ext
      funext j y
      obtain ⟨b⟩ := j
      have he : y = PUnit.unit := Subsingleton.elim (α := PUnit) _ _
      subst y
      cases b
      · exact hx
      · exact hy
    rw [h]
    exact P.modelAlgHomEquiv.apply_symm_apply _

end SHIGURE.Quantities
