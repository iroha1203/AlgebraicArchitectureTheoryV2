import Formal.SHIGURE.Part2.Realizations.PolynomialResidualCoefficients
import Formal.SHIGURE.Part2.Realizations.PolynomialTerms
import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Change of coordinates for typed polynomial Laws

The universal tensor realization of the input tuple computes the basis
change of the written residuals. Their generating ideal is invariant
under these changes and commutes with arbitrary ring homomorphisms.
-/

namespace SHIGURE.RealizationFamilies

open MvPolynomial Module SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

universe u

variable {k R : Type u} [CommRing k] [CommRing R] {sig : Signature.{u}}
  {Γ : List sig.SortType} {rank : sig.SortType → ℕ}

/- The inputs form a finite list, independently of the size of the signature. -/
/-- The independent typed inputs together form the product module of the
input context. Its chart basis is indexed by the same polynomial variables. -/
def inputChartBasis (A : TensorStructure R sig) (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) :
    Basis (PolynomialInputCoordinates rank Γ) R (∀ i : TensorPosition Γ, A.carrier i.1) :=
  Basis.ofEquivFun ((LinearEquiv.piCongrRight (fun i => (basis i.1).equivFun)) ≪≫ₗ
    (LinearEquiv.piCurry R (fun (i : TensorPosition Γ) (_ : Fin (rank i.1)) => R)).symm)

/-- Coordinates on the product basis are the actual coordinates of each input. -/
theorem inputChartBasis_repr (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s))
    (x : ∀ i : TensorPosition Γ, A.carrier i.1) (z : PolynomialInputCoordinates rank Γ) :
    (inputChartBasis A basis).repr x z = PolynomialTerm.inputValues A basis x z := by
  rw [inputChartBasis, Basis.ofEquivFun_repr_apply]
  rfl

section ChartScalarExtension

variable {S : Type u} [CommRing S] [Algebra R S]
  (A : TensorStructure R sig) (b b' : ∀ s, Basis (Fin (rank s)) R (A.carrier s))

private theorem inputChartBasis_apply_extended (z : PolynomialInputCoordinates rank Γ) :
    inputChartBasis (extendStructure R S A) (extendedBasis A b) z =
      fun i => (1 : S) ⊗ₜ[R] (inputChartBasis A b z) i := by
  classical
  let B := inputChartBasis (Γ := Γ) A b
  let E := inputChartBasis (Γ := Γ) (extendStructure R S A) (extendedBasis A b)
  apply E.repr.injective
  ext v
  change E.repr (E z) v = E.repr (fun i => (1 : S) ⊗ₜ[R] (B z) i) v
  have read : E.repr (fun i => (1 : S) ⊗ₜ[R] (B z) i) v =
      PolynomialTerm.inputValues (extendStructure R S A) (extendedBasis A b)
        (fun i => (1 : S) ⊗ₜ[R] (B z) i) v :=
    inputChartBasis_repr _ _ _ _
  rw [read]
  change E.repr (E z) v = ((b v.1.1).baseChange S).repr ((1 : S) ⊗ₜ[R] (B z) v.1) v.2
  rw [Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  have value : (b v.1.1).repr ((B z) v.1) v.2 = B.repr (B z) v :=
    (inputChartBasis_repr A b (B z) v).symm
  rw [value, Basis.repr_self, Basis.repr_self]
  by_cases same : z = v
  · subst v
    simp only [Finsupp.single_eq_same, map_one]
  · simp only [Finsupp.single_eq_of_ne (Ne.symm same), map_zero]

/-- Changing the basis of the actual input block has the coefficientwise
matrix extension induced by the original ring map. -/
theorem inputChartMatrix_baseChange :
    (inputChartBasis (Γ := Γ) (extendStructure R S A) (extendedBasis A b)).toMatrix
        (inputChartBasis (Γ := Γ) (extendStructure R S A) (extendedBasis A b')) =
      ((inputChartBasis (Γ := Γ) A b).toMatrix (inputChartBasis (Γ := Γ) A b')).map (algebraMap R S) := by
  ext v z
  rw [Basis.toMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply, inputChartBasis_apply_extended,
    inputChartBasis_repr, inputChartBasis_repr]
  change ((b v.1.1).baseChange S).repr ((1 : S) ⊗ₜ[R] (inputChartBasis A b' z) v.1) v.2 = _
  rw [Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

/-- Changing the basis at the actual output is coefficientwise under every ring map. -/
theorem outputChartMatrix_baseChange (s : sig.SortType) :
    (extendedBasis (S := S) A b s).toMatrix (extendedBasis A b' s) =
      ((b s).toMatrix (b' s)).map (algebraMap R S) := by
  ext i j
  rw [Basis.toMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply]
  change ((b s).baseChange S).repr (((b' s).baseChange S) j) i = _
  rw [Basis.baseChange_apply, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

end ChartScalarExtension


local instance (Γ : List sig.SortType) : Fintype (TensorPosition Γ) :=
  Fintype.ofFinite _

namespace PolynomialLaw

variable {s : sig.SortType} (l : PolynomialLaw k sig Γ s) (c : k →+* R) (A : TensorStructure R sig)
  (b b' : ∀ t, Basis (Fin (rank t)) R (A.carrier t))

/-- The actual expanded residuals in a second basis are obtained by linearly
substituting the inputs and changing the output basis. -/
theorem residual_changeBasis :
    l.residual c A b' =
      transformPolynomialResiduals ((b' s).toMatrix (b s))
        (linearPolynomialSubstitution ((inputChartBasis (Γ := Γ) A b).toMatrix
          (inputChartBasis (Γ := Γ) A b'))) (l.residual c A b) := by
  classical
  let I := PolynomialInputCoordinates rank Γ
  let S := MvPolynomial I R
  let A' := extendStructure R S A
  let b₁ := extendedBasis (S := S) A b
  let b₂ := extendedBasis (S := S) A b'
  let x (i : TensorPosition Γ) : A'.carrier i.1 :=
    (b₂ i.1).equivFun.symm (fun n => X (⟨i, n⟩ : I))
  have targetCoordinates : PolynomialTerm.inputValues A' b₂ x = (X : I → S) := by
    funext i
    rcases i with ⟨i, n⟩
    change (b₂ i.1).repr (x i) n = X ⟨i, n⟩
    rw [← Basis.equivFun_apply]
    exact congrFun ((b₂ i.1).equivFun.apply_symm_apply _) n
  let B := (inputChartBasis (Γ := Γ) A b).toMatrix (inputChartBasis (Γ := Γ) A b')
  have sourceCoordinates : PolynomialTerm.inputValues A' b₁ x =
      fun i => ∑ j : I, C (B i j) * X j := by
    funext i
    have coordinates := congrFun
      (Basis.toMatrix_mulVec_repr (inputChartBasis A' b₂) (inputChartBasis A' b₁) x) i
    have right : (inputChartBasis A' b₁).repr x i = PolynomialTerm.inputValues A' b₁ x i :=
      inputChartBasis_repr _ _ _ _
    rw [right, inputChartMatrix_baseChange (S := S) A b b'] at coordinates
    rw [← coordinates, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.map_apply, inputChartBasis_repr, targetCoordinates]
    rfl
  let y := l.left.eval ((algebraMap R S).comp c) A' x -
    l.right.eval ((algebraMap R S).comp c) A' x
  have sourceEval (j : Fin (rank s)) :
      linearPolynomialSubstitution B (l.residual c A b j) = (b₁ s).repr y j := by
    have value := l.residual_eval c A b x j
    change aeval (PolynomialTerm.inputValues A' b₁ x) (l.residual c A b j) = (b₁ s).repr y j at value
    rw [sourceCoordinates] at value
    exact value
  have targetEval (j : Fin (rank s)) :
      l.residual c A b' j = (b₂ s).repr y j := by
    have value := l.residual_eval c A b' x j
    change aeval (PolynomialTerm.inputValues A' b₂ x) (l.residual c A b' j) = (b₂ s).repr y j at value
    rw [targetCoordinates, aeval_X_left_apply] at value
    exact value
  funext j
  change l.residual c A b' j =
    transformPolynomialResiduals ((b' s).toMatrix (b s)) (linearPolynomialSubstitution B)
      (l.residual c A b) j
  rw [targetEval]
  have coordinates := congrFun (Basis.toMatrix_mulVec_repr (b₁ s) (b₂ s) y) j
  rw [outputChartMatrix_baseChange (S := S) A b' b s] at coordinates
  rw [← coordinates, Matrix.mulVec, dotProduct, transformPolynomialResiduals]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.map_apply, sourceEval]
  rfl

/-- The vanishing locus of the written Law has the same coefficient ideal
in any choice of bases on its free carriers. -/
theorem residualIdeal_changeBasis :
    polynomialResidualIdeal (l.residual c A b') = polynomialResidualIdeal (l.residual c A b) := by
  classical
  rw [l.residual_changeBasis c A b b']
  exact polynomialResidualIdeal_linearCoordinateChange
    ((inputChartBasis (Γ := Γ) A b).toMatrix (inputChartBasis (Γ := Γ) A b'))
    ((inputChartBasis (Γ := Γ) A b').toMatrix (inputChartBasis (Γ := Γ) A b))
    (Basis.toMatrix_mul_toMatrix_flip _ _) (Basis.toMatrix_mul_toMatrix_flip _ _)
    ((b' s).toMatrix (b s)) ((b s).toMatrix (b' s)) (Basis.toMatrix_mul_toMatrix_flip _ _)
    (l.residual c A b)

/-- A written Law holds precisely when its coefficient ideal is zero. -/
theorem holds_iff_residualIdeal_eq_bot :
    l.Holds c A ↔ polynomialResidualIdeal (l.residual c A b) = ⊥ := by
  rw [l.holds_iff_all_monomial_coefficients_zero c A b, ← le_bot_iff,
    polynomialResidualIdeal_le_iff]
  simp only [Ideal.mem_bot]

/-- Coefficients of the actual residuals extend by the given ring homomorphism. -/
theorem residual_baseChange {S : Type u} [CommRing S] [Algebra R S]
    (j : Fin (rank s)) :
    l.residual ((algebraMap R S).comp c) (extendStructure R S A) (extendedBasis A b) j =
      map (algebraMap R S) (l.residual c A b j) := by
  simp only [residual, map_sub, PolynomialTerm.expand_baseChange]

/-- The coefficient ideal of the written Law commutes with extension of
scalars in the actual tensor structure. -/
theorem residualIdeal_baseChange {S : Type u} [CommRing S] [Algebra R S] :
    polynomialResidualIdeal (l.residual ((algebraMap R S).comp c) (extendStructure R S A)
      (extendedBasis A b)) = (polynomialResidualIdeal (l.residual c A b)).map (algebraMap R S) := by
  rw [← polynomialResidualIdeal_map]
  congr 1
  funext j
  exact l.residual_baseChange c A b j

include b in
/-- Evaluating after an injective coefficient extension detects written Laws
on free affine charts, using all monomial coefficients. -/
theorem holds_of_injective_baseChange {S : Type u} [CommRing S] [Algebra R S]
    (injective : Function.Injective (algebraMap R S))
    (h : l.Holds ((algebraMap R S).comp c) (extendStructure R S A)) : l.Holds c A := by
  rw [l.holds_iff_all_monomial_coefficients_zero c A b]
  intro j m
  have value := (l.holds_iff_all_monomial_coefficients_zero _ _ (extendedBasis A b)).1 h j m
  rw [l.residual_baseChange c A b, coeff_map] at value
  apply injective
  rw [value, map_zero]

end PolynomialLaw

end

end SHIGURE.RealizationFamilies
