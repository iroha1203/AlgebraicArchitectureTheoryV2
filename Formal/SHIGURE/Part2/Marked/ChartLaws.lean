import Formal.SHIGURE.Part2.Marked.UniversalOperations
import Formal.SHIGURE.Part2.Marked.ChartResidualBaseChange
import Formal.SHIGURE.Part2.Families.AffineRealizations
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The residual ideal and coordinate ring of a marked chart

Construction 6.4 imposes every component of every written tensor Law and
every monomial coefficient of every written polynomial Law. The resulting
ideal lives in the actual polynomial ambient ring; its quotient is `B_I`.

## Implementation notes

Tensor shapes retain the parenthesization and argument-position types of
the existing `TensorExpression` API. Their bases are assembled from mathlib
singleton, finite-free, tensor-product and indexed tensor-product bases.
Thus residual components evaluate the original expressions on actual
modules. They are not a separate polynomial interpretation of the syntax.
The index families for primitives and Laws remain arbitrary small types.
-/

universe u

namespace SHIGURE.RealizationFamilies.Marked

open Module SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

variable {sig : Signature.{u}} (rank : sig.SortType → ℕ)

/-- A basis index for a written tensor shape, in the fixed small universe. -/
def ShapeCoordinate (rank : sig.SortType → ℕ) : TensorShape sig.SortType → Type u
  | .unit => PUnit.{u + 1}
  | .sort s => ULift.{u} (Fin (rank s))
  | .arguments Γ => ∀ i : TensorPosition Γ, Fin (rank i.1)
  | .tensor X Y => ShapeCoordinate rank X × ShapeCoordinate rank Y

variable {R : Type u} [CommRing R]

/-- The actual basis on each written shape, assembled from carrier bases. -/
def shapeBasis (A : TensorStructure R sig)
    (b : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) :
    (X : TensorShape sig.SortType) → Basis (ShapeCoordinate rank X) R (X.module A)
  | .unit => Basis.singleton PUnit R
  | .sort s => (b s).reindex Equiv.ulift.symm
  | .arguments Γ => Basis.piTensorProduct (fun i : TensorPosition Γ => b i.1)
  | .tensor X Y => (shapeBasis A b X).tensorProduct (shapeBasis A b Y)

/-- The actual shape scalar-extension comparison sends the old basis unit
tensors to the new basis, including indexed and parenthesized tensor shapes. -/
theorem freeShapeBaseChange_basis {A : Type u} [CommRing A] [Algebra A R]
    (c : OperationCoordinate sig rank → A) (X : TensorShape sig.SortType)
    (i : ShapeCoordinate rank X) :
    freeShapeBaseChange rank c X
        ((1 : R) ⊗ₜ[A] shapeBasis rank (freeStructure rank A c) (freeBasis rank A) X i) =
      shapeBasis rank (freeStructure rank R (fun z => algebraMap A R (c z)))
        (freeBasis rank R) X i := by
  induction X with
  | unit =>
    change extendScalarSort R ((1 : R) ⊗ₜ[A] (Basis.singleton PUnit.{u + 1} A) i) =
      (Basis.singleton PUnit.{u + 1} R) i
    rw [Basis.singleton_apply PUnit.{u + 1} A i, Basis.singleton_apply PUnit.{u + 1} R i,
      extendScalarSort_tmul]
    exact one_smul A (1 : R)
  | sort s =>
    change freeCarrierBaseChange rank s ((1 : R) ⊗ₜ[A]
      ((freeBasis rank A s).reindex Equiv.ulift.symm) i) =
      ((freeBasis rank R s).reindex Equiv.ulift.symm) i
    simp only [Basis.reindex_apply]
    exact freeCarrierBaseChange_basis rank s i.down
  | arguments Γ =>
    change (PiTensorProduct.congr (fun i : TensorPosition Γ => freeCarrierBaseChange rank i.1))
      (inputTensorBaseChange A (freeStructure rank A c).carrier R Γ
        ((1 : R) ⊗ₜ[A] (Basis.piTensorProduct (fun i : TensorPosition Γ => freeBasis rank A i.1)) i)) =
      (Basis.piTensorProduct (fun i : TensorPosition Γ => freeBasis rank R i.1)) i
    rw [Basis.piTensorProduct_apply (fun i : TensorPosition Γ => freeBasis rank A i.1) i,
      Basis.piTensorProduct_apply (fun i : TensorPosition Γ => freeBasis rank R i.1) i]
    calc
      _ = (PiTensorProduct.congr (fun t : TensorPosition Γ => freeCarrierBaseChange rank t.1))
          (PiTensorProduct.tprod R (fun t => (1 : R) ⊗ₜ[A] freeBasis rank A t.1 (i t))) :=
        congrArg (PiTensorProduct.congr (fun t : TensorPosition Γ => freeCarrierBaseChange rank t.1))
          (inputTensorBaseChange_unit_tprod A (freeStructure rank A c).carrier R Γ
            (fun t => freeBasis rank A t.1 (i t)))
      _ = PiTensorProduct.tprod R
          (fun t => freeCarrierBaseChange rank t.1 ((1 : R) ⊗ₜ[A] freeBasis rank A t.1 (i t))) :=
        PiTensorProduct.congr_tprod _ _
      _ = _ := congrArg (PiTensorProduct.tprod R)
        (funext fun t => freeCarrierBaseChange_basis rank t.1 (i t))
  | tensor X Y hx hy =>
    obtain ⟨i, j⟩ := i
    change freeShapeBaseChange rank c (.tensor X Y)
      ((1 : R) ⊗ₜ[A]
        ((shapeBasis rank (freeStructure rank A c) (freeBasis rank A) X).tensorProduct
          (shapeBasis rank (freeStructure rank A c) (freeBasis rank A) Y)) (i, j)) =
      ((shapeBasis rank (freeStructure rank R (fun z => algebraMap A R (c z))) (freeBasis rank R) X).tensorProduct
        (shapeBasis rank (freeStructure rank R (fun z => algebraMap A R (c z))) (freeBasis rank R) Y)) (i, j)
    rw [Basis.tensorProduct_apply, Basis.tensorProduct_apply]
    change TensorProduct.congr _ _
      (shapeBaseChange (freeStructure rank A c) (.tensor X Y)
        ((1 : R) ⊗ₜ[A]
          (shapeBasis rank (freeStructure rank A c) (freeBasis rank A) X i ⊗ₜ[A]
            shapeBasis rank (freeStructure rank A c) (freeBasis rank A) Y j))) = _
    rw [shapeBaseChange_tensor_tmul, TensorProduct.congr_tmul]
    exact congrArg₂ (TensorProduct.tmul R) (hx i) (hy j)

/-- Coordinates of arbitrary unit tensors specialize by the actual ring map. -/
theorem freeShapeBaseChange_repr {A : Type u} [CommRing A] [Algebra A R]
    (c : OperationCoordinate sig rank → A) (X : TensorShape sig.SortType)
    (x : X.module (freeStructure rank A c)) (j : ShapeCoordinate rank X) :
    (shapeBasis rank (freeStructure rank R (fun z => algebraMap A R (c z)))
      (freeBasis rank R) X).repr (freeShapeBaseChange rank c X ((1 : R) ⊗ₜ[A] x)) j =
      algebraMap A R ((shapeBasis rank (freeStructure rank A c) (freeBasis rank A) X).repr x j) := by
  let B := shapeBasis rank (freeStructure rank A c) (freeBasis rank A) X
  let C := shapeBasis rank (freeStructure rank R (fun z => algebraMap A R (c z))) (freeBasis rank R) X
  have maps : C.repr.toLinearMap.comp (freeShapeBaseChange rank c X).toLinearMap =
      (B.baseChange R).repr.toLinearMap := by
    apply (B.baseChange R).ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.baseChange_apply]
    rw [freeShapeBaseChange_basis]
    change C.repr (C i) = (B.baseChange R).repr ((1 : R) ⊗ₜ[A] B i)
    rw [← Basis.baseChange_apply, Basis.repr_self, Basis.repr_self]
  have coordinates := congrArg (fun f => f ((1 : R) ⊗ₜ[A] x) j) maps
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one] using coordinates

/-- A tensor Law residual is one actual matrix component of the difference
of its two evaluated maps in the specified finite-free bases. -/
def tensorResidual {k : Type u} [CommRing k] (c : k →+* R)
    (A : TensorStructure R sig) (b : ∀ s, Basis (Fin (rank s)) R (A.carrier s))
    (law : TensorLaw k sig) (i : ShapeCoordinate rank law.source)
    (j : ShapeCoordinate rank law.target) : R :=
  (shapeBasis rank A b law.target).repr
    (((law.left.mapScalars c).eval A - (law.right.mapScalars c).eval A)
      (shapeBasis rank A b law.source i)) j

/-- Every actual tensor residual component commutes with scalar extension
and the canonical free-carrier comparisons. -/
theorem tensorResidual_baseChange {k A : Type u} [CommRing k] [CommRing A] [Algebra A R]
    (q : k →+* A) (c : OperationCoordinate sig rank → A) (law : TensorLaw k sig)
    (i : ShapeCoordinate rank law.source) (j : ShapeCoordinate rank law.target) :
    algebraMap A R (tensorResidual rank q (freeStructure rank A c) (freeBasis rank A) law i j) =
      tensorResidual rank ((algebraMap A R).comp q)
        (freeStructure rank R (fun z => algebraMap A R (c z))) (freeBasis rank R) law i j := by
  let x := shapeBasis rank (freeStructure rank A c) (freeBasis rank A) law.source i
  have left := freeShapeBaseChange_eval (R := R) rank c (law.left.mapScalars q) x
  have right := freeShapeBaseChange_eval (R := R) rank c (law.right.mapScalars q) x
  rw [tensorExpression_mapScalars_comp, freeShapeBaseChange_basis] at left right
  have coordinates := freeShapeBaseChange_repr (R := R) rank c law.target
    (((law.left.mapScalars q).eval (freeStructure rank A c)) x -
      ((law.right.mapScalars q).eval (freeStructure rank A c)) x) j
  rw [TensorProduct.tmul_sub, map_sub, left, right] at coordinates
  simpa only [tensorResidual, LinearMap.sub_apply] using coordinates.symm

/-- All tensor components vanish exactly when the original tensor Law holds. -/
theorem tensorLaw_holds_iff_residual_zero {k : Type u} [CommRing k] (c : k →+* R)
    (A : TensorStructure R sig) (b : ∀ s, Basis (Fin (rank s)) R (A.carrier s))
    (law : TensorLaw k sig) :
    (law.mapScalars c).holds A ↔
      ∀ i j, tensorResidual rank c A b law i j = 0 := by
  change (law.left.mapScalars c).eval A = (law.right.mapScalars c).eval A ↔ _
  constructor
  · intro h i j
    simp [tensorResidual, h]
  · intro h
    apply (shapeBasis rank A b law.source).ext
    intro i
    apply (shapeBasis rank A b law.target).repr.injective
    apply Finsupp.ext
    intro j
    have zero := h i j
    simpa only [tensorResidual, LinearMap.sub_apply, map_sub, Finsupp.sub_apply, sub_eq_zero] using zero

variable {k : Type u} [CommRing k]
variable {generators : sig.SortType → ℕ} (I : ChartIndex (sig := sig) generators rank)

/-- Every matrix component of every tensor Law in the original presentation. -/
abbrev TensorResidualCoordinate (P : AffineLawPresentation k sig) :=
  Σ l : P.tensorIndex,
    ShapeCoordinate rank (P.tensorLaw l).source × ShapeCoordinate rank (P.tensorLaw l).target

/-- Every output component and every monomial coefficient of every polynomial Law. -/
abbrev PolynomialResidualCoordinate (P : AffineLawPresentation k sig) :=
  Σ l : P.polynomialIndex,
    Fin (rank (P.output l)) × (PolynomialInputCoordinates rank (P.inputs l) →₀ ℕ)

/-- The disjoint union retains all small tensor and polynomial Law families. -/
abbrev ResidualCoordinate (P : AffineLawPresentation k sig) :=
  TensorResidualCoordinate rank P ⊕ PolynomialResidualCoordinate rank P

/-- Read one component of one original Law on the universal free structure. -/
def chartResidual (P : AffineLawPresentation k sig) :
    ResidualCoordinate rank P → ChartAmbient k I
  | .inl ⟨l, i, j⟩ => tensorResidual rank (algebraMap k (ChartAmbient k I))
      (universalStructure rank k I) (freeBasis rank (ChartAmbient k I)) (P.tensorLaw l) i j
  | .inr ⟨l, j, m⟩ => MvPolynomial.coeff m
      (universalPolynomialResidual rank k I (P.polynomialLaw l) j)

/-- The ideal `J_I` generated by all required tensor and polynomial residuals. -/
def chartLawIdeal (P : AffineLawPresentation k sig) : Ideal (ChartAmbient k I) :=
  Ideal.span (Set.range (chartResidual rank I P))

/-- Ideal containment can be checked on precisely the required residual family. -/
theorem chartLawIdeal_le_iff (P : AffineLawPresentation k sig) (J : Ideal (ChartAmbient k I)) :
    chartLawIdeal rank I P ≤ J ↔ ∀ z, chartResidual rank I P z ∈ J := by
  rw [chartLawIdeal, Ideal.span_le]
  constructor
  · intro h z
    exact h ⟨z, rfl⟩
  · rintro h _ ⟨z, rfl⟩
    exact h z

/-- Every prescribed residual vanishes in the chart coordinate ring. -/
theorem chartResidual_mem (P : AffineLawPresentation k sig) (z : ResidualCoordinate rank P) :
    chartResidual rank I P z ∈ chartLawIdeal rank I P :=
  Ideal.subset_span ⟨z, rfl⟩

/-- The actual quotient ring `B_I=A_I/J_I` of Construction 6.4. -/
abbrev ChartRing (P : AffineLawPresentation k sig) :=
  ChartAmbient k I ⧸ chartLawIdeal rank I P

/-- Send the ambient polynomial ring to the required Law quotient. -/
def chartQuotient (P : AffineLawPresentation k sig) :
    ChartAmbient k I →ₐ[k] ChartRing rank I P :=
  Ideal.Quotient.mkₐ k (chartLawIdeal rank I P)

/-- The residue class of an independent marking or primitive coefficient. -/
def chartGenerator (P : AffineLawPresentation k sig) (z : ChartVariable I) : ChartRing rank I P :=
  chartQuotient rank I P (MvPolynomial.X z)

/-- The actual tensor residual specializes to the component of the original
Law on the specialized finite-free structure, for every coefficient assignment. -/
theorem tensorResidual_aeval (R : Type u) [CommRing R] [Algebra k R]
    (v : ChartVariable I → R) (law : TensorLaw k sig)
    (i : ShapeCoordinate rank law.source) (j : ShapeCoordinate rank law.target) :
    MvPolynomial.aeval v
      (tensorResidual rank (algebraMap k (ChartAmbient k I))
        (universalStructure rank k I) (freeBasis rank (ChartAmbient k I)) law i j) =
      tensorResidual rank (algebraMap k R)
        (freeStructure rank R (fun z => v (Sum.inr z))) (freeBasis rank R) law i j := by
  let A := ChartAmbient k I
  let f : A →ₐ[k] R := MvPolynomial.aeval v
  letI : Algebra A R := f.toRingHom.toAlgebra
  have scalars : (algebraMap A R).comp (algebraMap k A) = algebraMap k R := by
    ext a
    exact f.commutes a
  have coefficients : (fun z => algebraMap A R (operationEntry k I z)) =
      (fun z => v (Sum.inr z)) := by
    funext z
    exact MvPolynomial.aeval_X v (Sum.inr z)
  have result := tensorResidual_baseChange (R := R) rank (algebraMap k A)
    (operationEntry k I) law i j
  rw [scalars, coefficients] at result
  exact result

end

end SHIGURE.RealizationFamilies.Marked
