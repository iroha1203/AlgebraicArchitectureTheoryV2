import Formal.SHIGURE.Part2.Realizations.MarkingNullaryTerms
import Formal.SHIGURE.Part2.Tensor.CoefficientCoherence

/-! # Actual coefficient changes of the marked nullary operations -/

namespace SHIGURE.RealizationFamilies

open CategoryTheory TensorProduct SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (sig : Signature.{u}) (m : sig.SortType → ℕ)
  (A : TensorStructure R sig) (v : ∀ s, Fin (m s) → A.carrier s)

private theorem changed_nullary (s : sig.SortType) (j : Fin (m s))
    (x : ∀ i : TensorPosition ([] : List sig.SortType), extendCarriers R A.carrier S i.1) :
    extendOperation R A.carrier S
      ((withMarkingOperations sig m A v).total (Sum.inr ⟨s, j⟩)) x =
        (1 : S) ⊗ₜ[R] v s j := by
  let z : (i : TensorPosition ([] : List sig.SortType)) → A.carrier i.1 :=
    fun i => nomatch i.2
  have abs : x = fun i => (1 : S) ⊗ₜ[R] z i := funext fun i => nomatch i.2
  rw [abs]
  exact extendOperation_unit R A.carrier S
    ((withMarkingOperations sig m A v).total (Sum.inr ⟨s, j⟩)) z

/-- Extending coefficients of a named marking retains the actual image of its designated vector. -/
def markedScalarIso :
    extendStructure R S (withMarkingOperations sig m A v) ≅
      withMarkingOperations sig m (extendStructure R S A) (fun s j => (1 : S) ⊗ₜ[R] v s j) := by
  let source := extendStructure R S (withMarkingOperations sig m A v)
  let target := withMarkingOperations sig m (extendStructure R S A) (fun s j => (1 : S) ⊗ₜ[R] v s j)
  let f : source ⟶ target :=
    { onSort := fun _ => LinearMap.id
      preservesTotal := by
        intro k x
        cases k with
        | inl e => rfl
        | inr a =>
          obtain ⟨s, j⟩ := a
          exact changed_nullary sig m A v s j x
      preservesQuantity := fun _ _ => rfl }
  exact structureIsoOfCarrierEquiv f (fun _ => LinearEquiv.refl S _) (fun _ => rfl)

variable {A}
variable {B : TensorStructure R sig} {w : ∀ s, Fin (m s) → B.carrier s}

/-- A primitive-preserving map that sends each marking vector to the
corresponding marking vector preserves the named operations as well. -/
def markPreservingExtension (f : A ⟶ B) (same : ∀ s j, f.onSort s (v s j) = w s j) :
    withMarkingOperations sig m A v ⟶ withMarkingOperations sig m B w where
  onSort := f.onSort
  preservesTotal k x := by
    cases k with
    | inl e => exact f.preservesTotal e x
    | inr a => exact same a.1 a.2
  preservesQuantity := f.preservesQuantity

/-- An actual isomorphism preserving the marking vectors extends to the laws' named signature. -/
def markPreservingExtensionIso (e : A ≅ B) (same : ∀ s j, e.hom.onSort s (v s j) = w s j) :
    withMarkingOperations sig m A v ≅ withMarkingOperations sig m B w where
  hom := markPreservingExtension sig m v e.hom same
  inv := markPreservingExtension sig m w e.inv fun s j => by
    rw [← same s j]
    exact LinearMap.congr_fun (congrArg (fun x => x.onSort s) e.hom_inv_id) (v s j)
  hom_inv_id := TensorStructure.Hom.ext (funext fun s => congrArg (fun x => x.onSort s) e.hom_inv_id)
  inv_hom_id := TensorStructure.Hom.ext (funext fun s => congrArg (fun x => x.onSort s) e.inv_hom_id)

end

end SHIGURE.RealizationFamilies
