import Formal.SHIGURE.Part2.Realizations.PolynomialTerms
import Mathlib.Order.Hom.Basic

/-! # Coordinates of normalized marked charts

Definition 6.3 and Construction 6.4 choose increasing lists of generating
columns and give the remaining marking entries and operation entries
independent polynomial coordinates. The operation families remain small
arbitrary types. No nonzero-ring or positive-rank assumption is used.

## Implementation notes

Increasing embeddings record the ordered column choices without quotienting
lists by permutations. The ambient ring is mathlib's `MvPolynomial`; only
the finite lists of argument positions and finite carrier ranks are summed
over. Finiteness of the sort family is needed later for the product of
overlap determinants, and is not needed for these coordinate definitions.
-/

universe u

namespace SHIGURE.RealizationFamilies.Marked

noncomputable section

variable {sig : Signature.{u}}

/-- The two primitive multilinear families of the existing tensor structure. -/
abbrev PrimitiveSymbol (sig : Signature.{u}) := sig.Total ⊕ sig.Quantity

/-- Read the declared input list and result sort of either primitive family. -/
def primitiveArity (e : PrimitiveSymbol sig) : Arity sig.SortType :=
  Sum.elim sig.totalArity sig.quantityArity e

/-- An output entry and one input basis index per argument of a primitive. -/
abbrev OperationCoordinate (sig : Signature.{u}) (rank : sig.SortType → ℕ) :=
  Σ e : PrimitiveSymbol sig,
    Fin (rank (primitiveArity e).output) ×
      (∀ i : TensorPosition (primitiveArity e).inputs, Fin (rank i.1))

/-- Increasing choices of the generating columns used as a basis in each sort.
When a rank exceeds its number of generators, there is no such chart. -/
abbrev ChartIndex (generators rank : sig.SortType → ℕ) :=
  ∀ s, Fin (rank s) ↪o Fin (generators s)

/-- The independent entries of marking columns outside the selected basis. -/
abbrev MarkingCoordinate {generators rank : sig.SortType → ℕ}
    (I : ChartIndex (sig := sig) generators rank) :=
  Σ s, Fin (rank s) × {j : Fin (generators s) // j ∉ Set.range (I s)}

/-- Construction 6.4 has marking coordinates and primitive-operation coordinates. -/
abbrev ChartVariable {generators rank : sig.SortType → ℕ}
    (I : ChartIndex (sig := sig) generators rank) :=
  MarkingCoordinate I ⊕ OperationCoordinate sig rank

/-- The actual polynomial ambient ring of Construction 6.4, before imposing Laws. -/
abbrev ChartAmbient (k : Type u) [CommRing k]
    {generators rank : sig.SortType → ℕ} (I : ChartIndex (sig := sig) generators rank) :=
  MvPolynomial (ChartVariable I) k

variable (k : Type u) [CommRing k]
variable {generators rank : sig.SortType → ℕ} (I : ChartIndex (sig := sig) generators rank)

open Classical in
/-- The normalized marking matrix has identity selected columns and independent
polynomial entries in every other column. -/
def markingEntry (s : sig.SortType) (a : Fin (rank s)) (j : Fin (generators s)) :
    ChartAmbient k I :=
  if h : j ∈ Set.range (I s) then
    if I s a = j then 1 else 0
  else MvPolynomial.X (Sum.inl ⟨s, a, ⟨j, h⟩⟩)

/-- Reading a selected column gives the ordinary identity matrix entry. -/
theorem markingEntry_selected (s : sig.SortType) (a b : Fin (rank s)) :
    markingEntry k I s a (I s b) = if a = b then 1 else 0 := by
  classical
  simp [markingEntry, (I s).injective.eq_iff]

/-- The named primitive coefficient is its independent variable in the ambient ring. -/
def operationEntry (z : OperationCoordinate sig rank) : ChartAmbient k I :=
  MvPolynomial.X (Sum.inr z)

/-- A marking coordinate outside the selected columns reads back its variable. -/
theorem markingEntry_unselected (s : sig.SortType) (a : Fin (rank s))
    (j : Fin (generators s)) (h : j ∉ Set.range (I s)) :
    markingEntry k I s a j = MvPolynomial.X (Sum.inl ⟨s, a, ⟨j, h⟩⟩) := by
  classical
  simp [markingEntry, h]

end

end SHIGURE.RealizationFamilies.Marked
