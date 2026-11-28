import Formal.SHIGURE.Part2.Marked.Coordinates
import Formal.SHIGURE.Part2.Realizations.PolynomialCoordinates
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis

/-! # The universal free tensor structure in a marked chart

Construction 6.4 interprets each primitive coefficient by an actual mathlib
multilinear map on finite free modules. The residual construction then uses
the existing typed polynomial terms and their coefficient expansion API.

## Implementation notes

The mathlib basis of multilinear maps constructs the maps from their
coefficient arrays. This includes nullary operations and zero-rank carriers
without separate conventions. Replacing multilinear maps by raw coefficient
arrays throughout the realization category would duplicate the existing
`TensorStructure` API, so arrays are confined to these free charts.
-/

universe u

namespace SHIGURE.RealizationFamilies.Marked

open Module

noncomputable section

variable {sig : Signature.{u}} (rank : sig.SortType → ℕ)
variable (R : Type u) [CommRing R]

/-- Read either original primitive family as a multilinear operation of
its declared arity. This is the common interface for basis transitions. -/
def primitiveOperation (A : TensorStructure R sig) (e : PrimitiveSymbol sig) :
    TensorOperation R A.carrier (primitiveArity e) :=
  match e with
  | .inl f => A.total f
  | .inr q => A.quantity q

/-- The standard basis on each actual finite free carrier of a chart. -/
def freeBasis (s : sig.SortType) : Basis (Fin (rank s)) R (Fin (rank s) → R) :=
  Pi.basisFun R (Fin (rank s))

/-- A coefficient array specifies a genuine multilinear operation in finite
free coordinates, using mathlib's basis of multilinear maps. -/
def operationOfCoefficients (a : Arity sig.SortType)
    (c : Fin (rank a.output) → (∀ i : TensorPosition a.inputs, Fin (rank i.1)) → R) :
    MultilinearMap R (fun i : TensorPosition a.inputs => Fin (rank i.1) → R)
      (Fin (rank a.output) → R) :=
  let B := Basis.multilinearMap (fun i : TensorPosition a.inputs => freeBasis rank R i.1)
    (freeBasis rank R a.output)
  B.repr.symm (Finsupp.equivFunOnFinite.symm (fun z => c z.2 z.1))

/-- Independent primitive coefficients give the existing tensor structure
on finite free modules, before any equation is imposed. -/
def freeStructure (c : OperationCoordinate sig rank → R) : TensorStructure R sig where
  carrier s := ModuleCat.of R (Fin (rank s) → R)
  total f := operationOfCoefficients rank R (sig.totalArity f)
    (fun b a => c ⟨Sum.inl f, b, a⟩)
  quantity q := operationOfCoefficients rank R (sig.quantityArity q)
    (fun b a => c ⟨Sum.inr q, b, a⟩)

/-- The coefficient array recovers the value on each tuple of standard basis
vectors. This is the comparison needed by the chart representation theorem. -/
theorem operationOfCoefficients_basis (a : Arity sig.SortType)
    (c : Fin (rank a.output) → (∀ i : TensorPosition a.inputs, Fin (rank i.1)) → R)
    (b : Fin (rank a.output)) (v : ∀ i : TensorPosition a.inputs, Fin (rank i.1)) :
    operationOfCoefficients rank R a c (fun i => freeBasis rank R i.1 (v i)) b = c b v := by
  classical
  letI : Fintype (TensorPosition a.inputs) := Fintype.ofFinite _
  let B := Basis.multilinearMap (fun i : TensorPosition a.inputs => freeBasis rank R i.1)
    (freeBasis rank R a.output)
  let coordinates :
      (((∀ i : TensorPosition a.inputs, Fin (rank i.1)) × Fin (rank a.output)) →₀ R) :=
    Finsupp.equivFunOnFinite.symm (fun z => c z.2 z.1)
  have expansion : B.repr.symm coordinates = ∑ z, coordinates z • B z := by
    simpa only [LinearEquiv.apply_symm_apply] using (B.sum_repr (B.repr.symm coordinates)).symm
  change (B.repr.symm coordinates) (fun i => freeBasis rank R i.1 (v i)) b = c b v
  rw [expansion]
  simp [B, coordinates, Basis.multilinearMap_apply_apply, freeBasis,
    Pi.single_apply, Fintype.prod_boole, ← funext_iff, Fintype.sum_prod_type,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_apply]

/-- Every actual multilinear operation on these finite free carriers is
reconstructed from its values on input basis vectors and output coordinates. -/
theorem operationOfCoefficients_reconstruct (a : Arity sig.SortType)
    (f : MultilinearMap R (fun i : TensorPosition a.inputs => Fin (rank i.1) → R)
      (Fin (rank a.output) → R)) :
    operationOfCoefficients rank R a
      (fun b v => f (fun i => freeBasis rank R i.1 (v i)) b) = f := by
  apply Module.Basis.ext_multilinear (fun i : TensorPosition a.inputs => freeBasis rank R i.1)
  intro v
  funext b
  exact operationOfCoefficients_basis rank R a _ b v

/-- Independent coefficient arrays and all actual multilinear operations on
the free carriers are equivalent; no freeness of an arbitrary test module is assumed. -/
def operationCoefficientEquiv (a : Arity sig.SortType) :
    MultilinearMap R (fun i : TensorPosition a.inputs => Fin (rank i.1) → R)
      (Fin (rank a.output) → R) ≃
      (Fin (rank a.output) → (∀ i : TensorPosition a.inputs, Fin (rank i.1)) → R) where
  toFun f b v := f (fun i => freeBasis rank R i.1 (v i)) b
  invFun := operationOfCoefficients rank R a
  left_inv := operationOfCoefficients_reconstruct rank R a
  right_inv c := by
    funext b v
    exact operationOfCoefficients_basis rank R a c b v

variable (k : Type u) [CommRing k]
variable {generators : sig.SortType → ℕ} (I : ChartIndex (sig := sig) generators rank)

/-- The universal primitive operations have the coordinate variables as their
actual multilinear coefficients. -/
def universalStructure : TensorStructure (ChartAmbient k I) sig :=
  freeStructure rank (ChartAmbient k I) (operationEntry k I)

/-- Expand an original typed polynomial Law on the universal free realization.
Every monomial coefficient, rather than point evaluation alone, is retained. -/
def universalPolynomialResidual {Γ : List sig.SortType} {s : sig.SortType}
    (law : PolynomialLaw k sig Γ s) (b : Fin (rank s)) :
    MvPolynomial (PolynomialInputCoordinates rank Γ) (ChartAmbient k I) :=
  law.residual (algebraMap k (ChartAmbient k I)) (universalStructure rank k I)
    (freeBasis rank (ChartAmbient k I)) b

/-- The universal polynomial residual ideal is the coefficient ideal from the
existing coordinate-independent polynomial Law API. -/
def universalPolynomialResidualIdeal {Γ : List sig.SortType} {s : sig.SortType}
    (law : PolynomialLaw k sig Γ s) : Ideal (ChartAmbient k I) :=
  polynomialResidualIdeal (universalPolynomialResidual rank k I law)

end

end SHIGURE.RealizationFamilies.Marked
