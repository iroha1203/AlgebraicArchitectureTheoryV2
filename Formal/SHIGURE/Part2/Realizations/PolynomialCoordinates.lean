import Formal.SHIGURE.Part2.Realizations.PolynomialResidualCoefficients
import Formal.SHIGURE.Part2.Realizations.PolynomialTerms
import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Change of coordinates for typed polynomial Laws

## Implementation notes

The same universal tensor realization is used to compute the residual
in different bases. A recursion carrying a separate matrix through
every operation would repeat the substitution proof for each constructor.
The basis of the product module reads each input position in its own
basis. The generating ideal is invariant under these coordinate changes
and commutes with arbitrary ring homomorphisms.
-/

namespace SHIGURE.RealizationFamilies

open MvPolynomial Module SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

universe u

variable {k R : Type u} [CommRing k] [CommRing R] {sig : Signature.{u}}
  {Γ : List sig.SortType} {rank : sig.SortType → ℕ}

/-- Combine the bases of the independent input positions into the basis of
the tuple module. Equal input sorts may use different bases. -/
def inputChartBasis (A : TensorStructure R sig)
    (b : ∀ i : TensorPosition Γ, Basis (Fin (rank i.1)) R (A.carrier i.1)) :
    Basis (PolynomialInputCoordinates rank Γ) R (∀ i : TensorPosition Γ, A.carrier i.1) :=
  Basis.ofEquivFun ((LinearEquiv.piCongrRight (fun i => (b i).equivFun)) ≪≫ₗ
    (LinearEquiv.piCurry R (fun (i : TensorPosition Γ) (_ : Fin (rank i.1)) => R)).symm)

/-- The tuple basis reads the selected coordinate at the specified input position. -/
theorem inputChartBasis_repr (A : TensorStructure R sig)
    (b : ∀ i : TensorPosition Γ, Basis (Fin (rank i.1)) R (A.carrier i.1))
    (x : ∀ i : TensorPosition Γ, A.carrier i.1) (z : PolynomialInputCoordinates rank Γ) :
    (inputChartBasis A b).repr x z = (b z.1).repr (x z.1) z.2 := by
  rw [inputChartBasis, Basis.ofEquivFun_repr_apply]
  rfl

section ChartScalarExtension

variable {S : Type u} [CommRing S] [Algebra R S]
  (A : TensorStructure R sig)
  (b b' : ∀ i : TensorPosition Γ, Basis (Fin (rank i.1)) R (A.carrier i.1))

/-- The tuple basis extends by the unit tensors in all input positions. -/
private theorem inputChartBasis_apply_extended (z : PolynomialInputCoordinates rank Γ) :
    inputChartBasis (extendStructure R S A) (fun i => (b i).baseChange S) z =
      fun i => (1 : S) ⊗ₜ[R] (inputChartBasis A b z) i := by
  classical
  let B := inputChartBasis A b
  let E := inputChartBasis (extendStructure R S A) (fun i => (b i).baseChange S)
  apply E.repr.injective
  ext v
  change E.repr (E z) v = E.repr (fun i => (1 : S) ⊗ₜ[R] (B z) i) v
  have read : E.repr (fun i => (1 : S) ⊗ₜ[R] (B z) i) v =
      ((b v.1).baseChange S).repr ((1 : S) ⊗ₜ[R] (B z) v.1) v.2 :=
    inputChartBasis_repr _ _ _ _
  rw [read, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  have value : (b v.1).repr ((B z) v.1) v.2 = B.repr (B z) v :=
    (inputChartBasis_repr A b (B z) v).symm
  rw [value, Basis.repr_self, Basis.repr_self]
  by_cases same : z = v
  · subst v
    simp only [Finsupp.single_eq_same, map_one]
  · simp only [Finsupp.single_eq_of_ne (Ne.symm same), map_zero]

/-- Matrix entries of the input basis change commute with the coefficient map. -/
theorem inputChartMatrix_baseChange :
    (inputChartBasis (extendStructure R S A) (fun i => (b i).baseChange S)).toMatrix
        (inputChartBasis (extendStructure R S A) (fun i => (b' i).baseChange S)) =
      ((inputChartBasis A b).toMatrix (inputChartBasis A b')).map (algebraMap R S) := by
  ext v z
  rw [Basis.toMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply, inputChartBasis_apply_extended,
    inputChartBasis_repr, inputChartBasis_repr]
  change ((b v.1).baseChange S).repr ((1 : S) ⊗ₜ[R] (inputChartBasis A b' z) v.1) v.2 = _
  rw [Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

end ChartScalarExtension

/-- Changing two bases of a carrier has the coefficientwise extended matrix. -/
theorem outputChartMatrix_baseChange {S : Type u} [CommRing S] [Algebra R S]
    {M : Type u} [AddCommGroup M] [Module R M] {r : ℕ}
    (b b' : Basis (Fin r) R M) :
    (b.baseChange S).toMatrix (b'.baseChange S) =
      (b.toMatrix b').map (algebraMap R S) := by
  ext i j
  rw [Basis.toMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply,
    Basis.baseChange_apply, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

local instance (Γ : List sig.SortType) : Fintype (TensorPosition Γ) :=
  Fintype.ofFinite _

namespace PolynomialLaw

variable {s : sig.SortType} (l : PolynomialLaw k sig Γ s) (c : k →+* R) (A : TensorStructure R sig)
  (b : ∀ t, Basis (Fin (rank t)) R (A.carrier t))

section IndependentCoordinates

variable (e e' : ∀ i : TensorPosition Γ, Basis (Fin (rank i.1)) R (A.carrier i.1))
  (o o' : Basis (Fin (rank s)) R (A.carrier s))

/-- Evaluate the written terms at the universal tuple of the specified
input bases, and read the difference in the specified output basis. -/
def chartResidual (j : Fin (rank s)) : MvPolynomial (PolynomialInputCoordinates rank Γ) R :=
  let I := PolynomialInputCoordinates rank Γ
  let S := MvPolynomial I R
  let A' := extendStructure R S A
  let x (i : TensorPosition Γ) : A'.carrier i.1 :=
    ((e i).baseChange S).equivFun.symm (fun n => X (⟨i, n⟩ : I))
  let c' := (algebraMap R S).comp c
  (o.baseChange S).repr (l.left.eval c' A' x - l.right.eval c' A' x) j

/-- Compare the independently chosen input and output bases to the
recursive expansion in any family of bases of the free carriers. -/
theorem chartResidual_eq_transform :
    l.chartResidual c A e o =
      transformPolynomialResiduals (o.toMatrix (b s))
        (linearPolynomialSubstitution ((inputChartBasis A (fun i => b i.1)).toMatrix
          (inputChartBasis A e))) (l.residual c A b) := by
  classical
  let I := PolynomialInputCoordinates rank Γ
  let S := MvPolynomial I R
  let A' := extendStructure R S A
  let b₁ := extendedBasis (S := S) A b
  let e₂ (i : TensorPosition Γ) := (e i).baseChange S
  let x (i : TensorPosition Γ) : A'.carrier i.1 :=
    (e₂ i).equivFun.symm (fun n => X (⟨i, n⟩ : I))
  have targetCoordinates (i : I) : (e₂ i.1).repr (x i.1) i.2 = X i := by
    rw [← Basis.equivFun_apply]
    exact congrFun ((e₂ i.1).equivFun.apply_symm_apply _) i.2
  let B := (inputChartBasis A (fun i : TensorPosition Γ => b i.1)).toMatrix (inputChartBasis A e)
  have sourceCoordinates : PolynomialTerm.inputValues A' b₁ x =
      fun i => ∑ j : I, C (B i j) * X j := by
    funext i
    have coordinates := congrFun
      (Basis.toMatrix_mulVec_repr (inputChartBasis A' e₂) (inputChartBasis A' (fun i => b₁ i.1)) x) i
    have right : (inputChartBasis A' (fun i => b₁ i.1)).repr x i =
        PolynomialTerm.inputValues A' b₁ x i := inputChartBasis_repr _ _ _ _
    rw [right] at coordinates
    let z := (inputChartBasis A' e₂).repr x
    change ((inputChartBasis (extendStructure R S A) (fun i => (b i.1).baseChange S)).toMatrix
        (inputChartBasis (extendStructure R S A) (fun i => (e i).baseChange S))).mulVec z i = _ at coordinates
    rw [inputChartMatrix_baseChange (S := S) A (fun i => b i.1) e] at coordinates
    rw [← coordinates, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    have read : z j = (e₂ j.1).repr (x j.1) j.2 := inputChartBasis_repr _ _ _ _
    rw [Matrix.map_apply, read, targetCoordinates]
    rfl
  let y := l.left.eval ((algebraMap R S).comp c) A' x -
    l.right.eval ((algebraMap R S).comp c) A' x
  have sourceEval (j : Fin (rank s)) :
      linearPolynomialSubstitution B (l.residual c A b j) = (b₁ s).repr y j := by
    have value := l.residual_eval c A b x j
    change aeval (PolynomialTerm.inputValues A' b₁ x) (l.residual c A b j) = (b₁ s).repr y j at value
    rw [sourceCoordinates] at value
    exact value
  funext j
  change (o.baseChange S).repr y j =
    transformPolynomialResiduals (o.toMatrix (b s)) (linearPolynomialSubstitution B)
      (l.residual c A b) j
  have coordinates := congrFun (Basis.toMatrix_mulVec_repr (b₁ s) (o.baseChange S) y) j
  change ((o.baseChange S).toMatrix ((b s).baseChange S)).mulVec ((b₁ s).repr y) j = _ at coordinates
  rw [outputChartMatrix_baseChange (S := S) o (b s)] at coordinates
  refine coordinates.symm.trans ?_
  rw [Matrix.mulVec, dotProduct, transformPolynomialResiduals_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.map_apply, sourceEval]
  rfl

/-- In sortwise coordinates the universal evaluation agrees with the
recursive expansion on the same chart. -/
theorem chartResidual_sortwise :
    l.chartResidual c A (fun i => b i.1) (b s) = l.residual c A b := by
  classical
  rw [l.chartResidual_eq_transform c A b, Basis.toMatrix_self, Basis.toMatrix_self,
    linearPolynomialSubstitution_id, transformPolynomialResiduals_id]

include b in
/-- The residual transforms between any two independently chosen input
and output bases by the actual input substitution and output matrix. -/
theorem chartResidual_changeBasis :
    l.chartResidual c A e' o' =
      transformPolynomialResiduals (o'.toMatrix o)
        (linearPolynomialSubstitution ((inputChartBasis A e).toMatrix (inputChartBasis A e')))
        (l.chartResidual c A e o) := by
  classical
  rw [l.chartResidual_eq_transform c A b e' o', l.chartResidual_eq_transform c A b e o,
    transformPolynomialResiduals_comp, linearPolynomialSubstitution_comp,
    Basis.toMatrix_mul_toMatrix, Basis.toMatrix_mul_toMatrix]

include b in
/-- The generating ideal is independent of the choices at each separate
input and at the output. -/
theorem chartResidualIdeal_changeBasis :
    polynomialResidualIdeal (l.chartResidual c A e' o') =
      polynomialResidualIdeal (l.chartResidual c A e o) := by
  classical
  rw [l.chartResidual_changeBasis c A b e e' o o']
  exact polynomialResidualIdeal_linearCoordinateChange
    ((inputChartBasis A e).toMatrix (inputChartBasis A e'))
    ((inputChartBasis A e').toMatrix (inputChartBasis A e))
    (Basis.toMatrix_mul_toMatrix_flip _ _) (Basis.toMatrix_mul_toMatrix_flip _ _)
    (o'.toMatrix o) (o.toMatrix o') (Basis.toMatrix_mul_toMatrix_flip _ _)
    (l.chartResidual c A e o)

end IndependentCoordinates

/-- A written Law holds precisely when its coefficient ideal is zero. -/
theorem holds_iff_residualIdeal_eq_bot :
    l.Holds c A ↔ polynomialResidualIdeal (l.residual c A b) = ⊥ := by
  rw [l.holds_iff_all_monomial_coefficients_zero c A b, ← le_bot_iff,
    polynomialResidualIdeal_le_iff]
  simp only [Ideal.mem_bot]

include b in
/-- Law satisfaction is equivalent to the zero ideal in any independent chart. -/
theorem holds_iff_chartResidualIdeal_eq_bot
    (e : ∀ i : TensorPosition Γ, Basis (Fin (rank i.1)) R (A.carrier i.1))
    (o : Basis (Fin (rank s)) R (A.carrier s)) :
    l.Holds c A ↔ polynomialResidualIdeal (l.chartResidual c A e o) = ⊥ := by
  rw [l.chartResidualIdeal_changeBasis c A b (fun i => b i.1) e (b s) o,
    l.chartResidual_sortwise c A b]
  exact l.holds_iff_residualIdeal_eq_bot c A b

/-- Coefficients of the actual residuals extend by the given ring homomorphism. -/
theorem residual_baseChange {S : Type u} [CommRing S] [Algebra R S]
    (j : Fin (rank s)) :
    l.residual ((algebraMap R S).comp c) (extendStructure R S A) (extendedBasis A b) j =
      map (algebraMap R S) (l.residual c A b j) := by
  simp only [residual_apply, map_sub, PolynomialTerm.expand_baseChange]

/-- The coefficient ideal of the written Law commutes with extension of
scalars in the actual tensor structure. -/
theorem residualIdeal_baseChange {S : Type u} [CommRing S] [Algebra R S] :
    polynomialResidualIdeal (l.residual ((algebraMap R S).comp c) (extendStructure R S A)
      (extendedBasis A b)) = (polynomialResidualIdeal (l.residual c A b)).map (algebraMap R S) := by
  rw [← polynomialResidualIdeal_map]
  congr 1
  funext j
  exact l.residual_baseChange c A b j

section IndependentCoordinateBaseChange

variable {S : Type u} [CommRing S] [Algebra R S]
  (e : ∀ i : TensorPosition Γ, Basis (Fin (rank i.1)) R (A.carrier i.1))
  (o : Basis (Fin (rank s)) R (A.carrier s))

include b in
/-- With independent input and output bases, every residual polynomial
changes coefficients by the given ring map. -/
theorem chartResidual_baseChange :
    l.chartResidual ((algebraMap R S).comp c) (extendStructure R S A) (fun i => (e i).baseChange S)
        (o.baseChange S) =
      fun j => map (algebraMap R S) (l.chartResidual c A e o j) := by
  classical
  rw [l.chartResidual_eq_transform _ _ (extendedBasis A b), l.chartResidual_eq_transform c A b,
    map_linearCoordinateResiduals]
  let B := (inputChartBasis A (fun i : TensorPosition Γ => b i.1)).toMatrix (inputChartBasis A e)
  have inputs : (inputChartBasis (extendStructure R S A) (fun i => (extendedBasis A b) i.1)).toMatrix
      (inputChartBasis (extendStructure R S A) (fun i => (e i).baseChange S)) =
      B.map (algebraMap R S) := inputChartMatrix_baseChange (S := S) A (fun i => b i.1) e
  have output : (o.baseChange S).toMatrix ((extendedBasis A b) s) =
      (o.toMatrix (b s)).map (algebraMap R S) := outputChartMatrix_baseChange o (b s)
  rw [inputs, output]
  congr 1
  funext j
  exact l.residual_baseChange c A b j

include b in
/-- Every coefficient map carries the generating ideal of an independent
chart to its image ideal. -/
theorem chartResidualIdeal_baseChange :
    polynomialResidualIdeal (l.chartResidual ((algebraMap R S).comp c) (extendStructure R S A)
      (fun i => (e i).baseChange S) (o.baseChange S)) =
      (polynomialResidualIdeal (l.chartResidual c A e o)).map (algebraMap R S) := by
  rw [l.chartResidual_baseChange c A b e o, ← polynomialResidualIdeal_map]

end IndependentCoordinateBaseChange

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
