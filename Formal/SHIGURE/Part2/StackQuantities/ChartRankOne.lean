import Formal.SHIGURE.Part2.StackQuantities.ResidualExamples
import Formal.SHIGURE.Part2.Realizations.PolynomialCoordinates
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Fintype.BigOperators

/-! # The rank-one quantity as a typed polynomial Law

The quantity is an actual unary multilinear operation and multiplication is
an actual binary multilinear operation in the tensor structure. -/

open CategoryTheory Module MvPolynomial SHIGURE.TensorRealization SHIGURE.RealizationFamilies
open scoped BigOperators

universe u

noncomputable section
namespace SHIGURE.StackQuantities.RankOneChart

/-- One scalar sort, one binary product, and one unary linear quantity. -/
def signature : SHIGURE.Signature.{u} where
  SortType := PUnit
  Total := PUnit
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PUnit
  totalArity _ := ⟨[PUnit.unit, PUnit.unit], PUnit.unit⟩
  relInputs x := nomatch x
  partialArity x := nomatch x
  quantityArity _ := ⟨[PUnit.unit], PUnit.unit⟩

private instance onePositionUnique : Unique (TensorPosition ([PUnit.unit] : List PUnit.{u + 1})) where
  default := ⟨PUnit.unit, .here⟩
  uniq i := by
    rcases i with ⟨⟨⟩, _ | h⟩
    · rfl
    · exact nomatch h

def twoPositions : TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1}) ≃ Bool where
  toFun
    | ⟨_, .here⟩ => false
    | ⟨_, .there .here⟩ => true
  invFun
    | false => ⟨PUnit.unit, .here⟩
    | true => ⟨PUnit.unit, .there .here⟩
  left_inv
    | ⟨⟨⟩, .here⟩ => rfl
    | ⟨⟨⟩, .there .here⟩ => rfl
  right_inv
    | false => rfl
    | true => rfl

theorem twoPositions_card :
    letI : Fintype (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) := Fintype.ofFinite _
    Fintype.card (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) = 2 := by
  classical
  letI : Fintype (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) := Fintype.ofFinite _
  exact (Fintype.card_congr twoPositions).trans Fintype.card_bool

/-- Compute the product over the two typed positions by evaluating each one. -/
theorem prod_twoPositions {M : Type*} [CommMonoid M]
    (f : TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1}) → M) :
    letI : Fintype (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) := Fintype.ofFinite _
    (∏ i, f i) = f ⟨PUnit.unit, .here⟩ * f ⟨PUnit.unit, .there .here⟩ := by
  classical
  letI : Fintype (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) := Fintype.ofFinite _
  simpa [Fintype.prod_bool, twoPositions, mul_comm] using (Equiv.prod_comp twoPositions.symm f).symm

variable {R : Type u} [CommRing R]

/-- Finite scalar multiplication as the primitive operation for an arity. -/
def scalarProduct (Γ : List PUnit.{u + 1}) :
    TensorOperation R (fun _ => ModuleCat.of R R) ⟨Γ, PUnit.unit⟩ :=
  letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
  MultilinearMap.mkPiRing R (TensorPosition Γ) (1 : R)

/-- Interpret the quantity by `x ↦ t * x` and the total operation by multiplication. -/
def scalarStructure (t : R) : TensorStructure R signature.{u} where
  carrier _ := ModuleCat.of R R
  total _ := scalarProduct [PUnit.unit, PUnit.unit]
  quantity _ := t • scalarProduct [PUnit.unit]

/-- The written application `q(v)`. -/
def quantityTerm : PolynomialTerm R signature.{u} [PUnit.unit] PUnit.unit :=
  .quantity PUnit.unit (fun
    | ⟨⟨⟩, .here⟩ => .var .here)

/-- The written Law `q(v)^2 = q(v)`. -/
def law : PolynomialLaw R signature.{u} [PUnit.unit] PUnit.unit :=
  ⟨.total PUnit.unit (fun
    | ⟨⟨⟩, .here⟩ => quantityTerm
    | ⟨⟨⟩, .there .here⟩ => quantityTerm), quantityTerm⟩

/-- The scalar carrier has rank one at its unique sort. -/
abbrev scalarRank (_ : signature.{u}.SortType) : ℕ := 1

/-- The standard basis has the same carrier for every value of the quantity. -/
def basisFor (t : R) (s : signature.{u}.SortType) : Basis (Fin (scalarRank s)) R ((scalarStructure t).carrier s) :=
  Basis.singleton (Fin 1) R

/-- The coordinate of the sole formal input. -/
def inputIndex : PolynomialInputCoordinates (sig := signature.{u}) scalarRank.{u} [PUnit.unit] :=
  ⟨⟨PUnit.unit, .here⟩, 0⟩

/-- The actual chart residual of the written Law is the rank-one formal
quantity residual. -/
theorem chartResidual_eq (t : R) :
    law.chartResidual (rank := scalarRank.{u}) (RingHom.id R) (scalarStructure t) (fun i => basisFor t i.1)
        (basisFor t PUnit.unit) 0 =
      (C t * X (inputIndex.{u})) ^ 2 - C t * X inputIndex := by
  classical
  have reduction :
      law.chartResidual (rank := scalarRank.{u})
          (RingHom.id R) (scalarStructure t) (fun i => basisFor t i.1) (basisFor t PUnit.unit) =
        law.residual (rank := scalarRank.{u})
          (RingHom.id R) (scalarStructure t) (by
            intro s
            change Basis (Fin (scalarRank s)) R ((scalarStructure t).carrier s)
            exact basisFor t s) := by
    apply PolynomialLaw.chartResidual_sortwise
  rw [reduction]
  letI : Fintype (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) := Fintype.ofFinite _
  have cardTwo : Fintype.card (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) = 2 :=
    twoPositions_card
  have defaultPosition (inst : Inhabited (TensorPosition ([PUnit.unit] : List PUnit.{u + 1}))) :
      @default _ inst = ⟨PUnit.unit, .here⟩ := Subsingleton.elim _ _
  simp [PolynomialLaw.residual, law, quantityTerm, PolynomialTerm.expand,
    operationPolynomial, scalarStructure, scalarProduct, basisFor, scalarRank, signature, inputIndex,
    Basis.singleton_apply, Basis.singleton_repr, MultilinearMap.mkPiRing_apply,
    Fintype.sum_unique, Fintype.prod_unique, Finset.prod_const, cardTwo, smul_eq_mul,
    prod_twoPositions, onePositionUnique, defaultPosition, pow_two]

/-- Reindexing the output by its unique coordinate does not change the
ideal of all residual coefficients. -/
private theorem outputIdeal_singleton {I : Type u} (r : Fin 1 → MvPolynomial I R) :
    polynomialResidualIdeal r = polynomialResidualIdeal (fun _ : Unit => r 0) := by
  apply le_antisymm
  · apply (polynomialResidualIdeal_le_iff _ _).2
    intro j m
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (polynomialResidualIdeal_le_iff _ _).1 le_rfl () m
  · apply (polynomialResidualIdeal_le_iff _ _).2
    intro _ m
    exact (polynomialResidualIdeal_le_iff _ _).1 le_rfl 0 m

/-- Renaming the one input variable preserves the ideal generated by all
coefficients, since the reverse renaming sends that variable back to itself. -/
private theorem inputIdeal_singleton {I : Type u} (i : I) (r : Unit → MvPolynomial Unit R) :
    polynomialResidualIdeal (fun o => MvPolynomial.rename (fun _ : Unit => i) (r o)) =
      polynomialResidualIdeal r := by
  let f : MvPolynomial Unit R →ₐ[R] MvPolynomial I R := MvPolynomial.rename (fun _ => i)
  let g : MvPolynomial I R →ₐ[R] MvPolynomial Unit R := MvPolynomial.rename (fun _ => ())
  let r' : Unit → MvPolynomial I R := fun o => f (r o)
  have back : (fun o => g (r' o)) = r := by
    funext o
    dsimp [r', f, g]
    rw [MvPolynomial.rename_rename]
    have hid : (fun _ : I => ()) ∘ (fun _ : Unit => i) = id := by
      funext x
      cases x
      rfl
    rw [hid, MvPolynomial.rename_id_apply]
  change polynomialResidualIdeal r' = polynomialResidualIdeal r
  apply le_antisymm
  · exact polynomialResidualIdeal_reparameterize_le f r
  · simpa only [back] using polynomialResidualIdeal_reparameterize_le g r'

/-- All monomial coefficients of the actual typed chart residual generate `(t)`. -/
theorem chartResidual_ideal (t : R) :
    polynomialResidualIdeal
      (law.chartResidual (rank := scalarRank.{u}) (RingHom.id R) (scalarStructure t) (fun i => basisFor t i.1)
        (basisFor t PUnit.unit)) = Ideal.span {t} := by
  rw [outputIdeal_singleton]
  have chart : (fun _ : Unit => law.chartResidual (rank := scalarRank.{u}) (RingHom.id R) (scalarStructure t)
      (fun i => basisFor t i.1) (basisFor t PUnit.unit) 0) =
      (fun o => MvPolynomial.rename (fun _ : Unit => inputIndex.{u})
        (idempotentResidual t o)) := by
    funext o
    cases o
    rw [chartResidual_eq]
    simp [idempotentResidual, rankOneInput, MvPolynomial.rename_C]
  rw [chart, inputIdeal_singleton, idempotentResidual_ideal]

end SHIGURE.StackQuantities.RankOneChart
end
