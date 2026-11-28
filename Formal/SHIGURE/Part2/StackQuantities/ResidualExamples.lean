import Formal.SHIGURE.Part2.Realizations.PolynomialResidualCoefficients
import Mathlib.LinearAlgebra.Pi

/-! # Calculations with universal linear quantity inputs

The coefficient ring is arbitrary.  In particular these calculations do not
use cancellation, and the mixed coefficient is retained in characteristic 2.
-/

namespace SHIGURE.StackQuantities

open MvPolynomial SHIGURE.RealizationFamilies

noncomputable section

variable {R : Type*} [CommRing R]

/-- The value of a linear quantity on a formal rank-one input. -/
def rankOneInput (t : R) : MvPolynomial Unit R := C t * X ()

/-- The scalar extension of the linear quantity with coordinate `t`. -/
def rankOneQuantity (t : R) :
    MvPolynomial Unit R →ₗ[MvPolynomial Unit R] MvPolynomial Unit R :=
  LinearMap.mulLeft (MvPolynomial Unit R) (C t)

/-- The formal rank-one value is evaluation of the actual linear quantity. -/
theorem rankOneInput_eq_quantity (t : R) :
    rankOneInput t = rankOneQuantity t (X ()) := rfl

/-- The written residual of `q(v)^2 = q(v)` at the universal input. -/
def idempotentResidual (t : R) : Unit → MvPolynomial Unit R :=
  fun _ => rankOneInput t ^ 2 - rankOneInput t

/-- The coefficient of the linear term is the negative quantity coordinate. -/
theorem idempotentResidual_linear_coefficient (t : R) :
    coeff (Finsupp.single () 1) (idempotentResidual t ()) = -t := by
  have different : Finsupp.single () 1 + Finsupp.single () 1 ≠
      (Finsupp.single () 1 : Unit →₀ ℕ) := by
    intro h
    have h' := congrArg (fun x : Unit →₀ ℕ => x ()) h
    simp [Finsupp.add_apply] at h'
  simp [idempotentResidual, rankOneInput, C_mul_X_eq_monomial, pow_two,
    monomial_mul, different]

/-- All coefficients of the actual rank-one residual generate `(t)`. -/
theorem idempotentResidual_ideal (t : R) :
    polynomialResidualIdeal (idempotentResidual t) = Ideal.span {t} := by
  let J : Ideal R := Ideal.span {t}
  have ht : t ∈ J := Ideal.subset_span (Set.mem_singleton t)
  apply le_antisymm
  · apply (polynomialResidualIdeal_le_iff _ _).2
    intro o m
    have ht2 : t * t ∈ J := J.mul_mem_left t ht
    simp only [idempotentResidual, rankOneInput, C_mul_X_eq_monomial, pow_two,
      monomial_mul, coeff_sub, coeff_monomial]
    split_ifs
    · exact J.sub_mem ht2 ht
    · simpa using ht2
    · simpa using J.neg_mem ht
    · simp
  · apply Ideal.span_le.mpr
    intro x hx
    have hx' : x = t := Set.mem_singleton_iff.mp hx
    subst x
    have h := (polynomialResidualIdeal_le_iff (idempotentResidual t)
      (polynomialResidualIdeal (idempotentResidual t))).mp le_rfl () (Finsupp.single () 1)
    rw [idempotentResidual_linear_coefficient] at h
    simpa using (polynomialResidualIdeal (idempotentResidual t)).neg_mem h

/-- The formal value of a rank-two linear quantity. -/
def rankTwoInput (t₁ t₂ : R) : MvPolynomial (Fin 2) R :=
  C t₁ * X 0 + C t₂ * X 1

/-- The scalar extension of the linear quantity on a rank-two free module. -/
def rankTwoQuantity (t₁ t₂ : R) :
    (Fin 2 → MvPolynomial (Fin 2) R) →ₗ[MvPolynomial (Fin 2) R] MvPolynomial (Fin 2) R :=
  (C t₁ : MvPolynomial (Fin 2) R) • (LinearMap.proj (R := MvPolynomial (Fin 2) R)
      (φ := fun _ : Fin 2 => MvPolynomial (Fin 2) R) 0) +
    (C t₂ : MvPolynomial (Fin 2) R) • (LinearMap.proj (R := MvPolynomial (Fin 2) R)
      (φ := fun _ : Fin 2 => MvPolynomial (Fin 2) R) 1)

/-- The formal rank-two value is evaluation on the universal vector. -/
theorem rankTwoInput_eq_quantity (t₁ t₂ : R) :
    rankTwoInput t₁ t₂ = rankTwoQuantity t₁ t₂ (fun i => X i) := by
  simp [rankTwoInput, rankTwoQuantity, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

/-- The residual of the square-zero Law at its universal formal input. -/
def squareZeroResidual (t₁ t₂ : R) : Unit → MvPolynomial (Fin 2) R :=
  fun _ => rankTwoInput t₁ t₂ ^ 2

/-- The mixed coefficient records both ordered cross terms, with no division by two. -/
theorem squareZeroResidual_mixed_coefficient (t₁ t₂ : R) :
    coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
        (squareZeroResidual t₁ t₂ ()) = 2 * t₁ * t₂ := by
  let a : (Fin 2 →₀ ℕ) := Finsupp.single 0 1
  let b : (Fin 2 →₀ ℕ) := Finsupp.single 1 1
  have ha : a + a ≠ a + b := by
    intro h
    have h' := congrArg (fun x : Fin 2 →₀ ℕ => x 0) h
    simp [a, b, Finsupp.add_apply] at h'
  have hb : b + b ≠ a + b := by
    intro h
    have h' := congrArg (fun x : Fin 2 →₀ ℕ => x 1) h
    simp [a, b, Finsupp.add_apply] at h'
  have hc : b + a = a + b := add_comm b a
  change coeff (a + b) (squareZeroResidual t₁ t₂ ()) = _
  simp only [squareZeroResidual, rankTwoInput, C_mul_X_eq_monomial]
  rw [show (monomial a t₁ + monomial b t₂) ^ 2 =
      monomial a t₁ * monomial a t₁ + monomial a t₁ * monomial b t₂ +
      monomial b t₂ * monomial a t₁ + monomial b t₂ * monomial b t₂ by ring]
  simp only [monomial_mul, coeff_add, coeff_monomial, ha, hb, hc, if_false, if_true, zero_add,
    add_zero]
  ring

/-- The mixed coefficient belongs to the ideal generated by every coefficient. -/
theorem squareZeroResidual_mixed_mem (t₁ t₂ : R) :
    2 * t₁ * t₂ ∈ polynomialResidualIdeal (squareZeroResidual t₁ t₂) := by
  have h := (polynomialResidualIdeal_le_iff (squareZeroResidual t₁ t₂)
    (polynomialResidualIdeal (squareZeroResidual t₁ t₂))).mp le_rfl ()
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
  rwa [squareZeroResidual_mixed_coefficient] at h

/-- A quantity transported along a structure isomorphism preserves the Law
at the specified section carried by that isomorphism. -/
theorem specifiedSection_preserved {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (h : M ≃ₗ[R] N) (c : M) (c' : N)
    (hc : h c = c') (q' : N →ₗ[R] R) :
    (q'.comp h.toLinearMap) c = 1 ↔ q' c' = 1 := by
  simp [hc]

end
end SHIGURE.StackQuantities
