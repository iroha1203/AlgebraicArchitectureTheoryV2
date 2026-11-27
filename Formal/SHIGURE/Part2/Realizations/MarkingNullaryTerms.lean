import Formal.SHIGURE.Part2.Realizations.MarkedChart

/-! # Designated generators as actual nullary operations in Laws -/

namespace SHIGURE.RealizationFamilies

open SHIGURE.TensorRealization

noncomputable section

universe u

variable (sig : Signature.{u}) (generators : sig.SortType → ℕ)

/-- Allow an equation to mention the actual named generators without adding
any independent operation coordinate for a marking. -/
def markingSignature : Signature.{u} where
  SortType := sig.SortType
  Total := sig.Total ⊕ (Σ s : sig.SortType, Fin (generators s))
  Rel := sig.Rel
  Partial := sig.Partial
  Quantity := sig.Quantity
  totalArity
    | .inl e => sig.totalArity e
    | .inr ⟨s, _⟩ => ⟨[], s⟩
  relInputs := sig.relInputs
  partialArity := sig.partialArity
  quantityArity := sig.quantityArity

variable {R : Type u} [CommRing R]
  (A : TensorStructure R sig) (m : ∀ s, Fin (generators s) → A.carrier s)

/-- Insert the actual chosen generator vectors as nullary operations. -/
def withMarkingOperations : TensorStructure R (markingSignature sig generators) where
  carrier := A.carrier
  total
    | .inl e => A.total e
    | .inr ⟨s, j⟩ =>
      { toFun := fun _ => m s j
        map_update_add' := by
          intro _ _ i
          exact nomatch i.2
        map_update_smul' := by
          intro _ _ i
          exact nomatch i.2 }
  quantity := A.quantity

/-- A written occurrence of a generator evaluates to that original marking vector. -/
theorem withMarkingOperations_designated (s : sig.SortType) (j : Fin (generators s)) :
    (withMarkingOperations sig generators A m).designated (Sum.inr ⟨s, j⟩) rfl = m s j :=
  rfl

variable (rank : sig.SortType → ℕ) (choice : MarkedBasisChoice sig rank generators)

open MvPolynomial in
/-- In the universal chart the marked nullary operations are the columns
of the original universal marking matrix. -/
def universalNamedMarkedTensor :
    TensorStructure (MvPolynomial (MarkedChartVariable sig rank generators choice) R)
      (markingSignature sig generators) :=
  withMarkingOperations sig generators (universalMarkedTensor sig rank generators choice)
    (fun s j i => universalMarkingMatrix (R := R) sig rank generators choice s i j)

end

end SHIGURE.RealizationFamilies
