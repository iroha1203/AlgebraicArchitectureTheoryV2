import Formal.SHIGURE.Part1.MarkedRealizations

/-! # The fixed coefficient reduct of a marked model

The scalar context consists of the coefficient sort and its five ring
operations. All realizations which retain this context restrict to the
same structure of the fixed ring, as required by Definition 2.2 and
used in Proposition 3.6.

## Implementation notes

Use the coefficient subsignature obtained by the ordinary declaration
restriction. Its structure has no module kernels or extra maps to
choose. Equality of scalar reducts is therefore strict equality in the
existing model language.
-/

universe u

namespace SHIGURE.Marked

open Vocabulary DeclarationContext

variable {V : Vocabulary.{u}} {L : V.Laws} {R : Type u} [CommRing R]
variable {U : DeclarationContext (V.presentation L)}

/-- Keep the coefficient sort and exactly its ring operations. -/
def coefficients (L : V.Laws) : DeclarationContext (V.presentation L) where
  declarations := {d | d = .sort none ∨ ∃ f, d = V.coefficientDecl L f}
  closed kept := by
    rcases kept with same | ⟨f, same⟩
    · subst same
      exact Set.empty_subset _
    · subst same
      intro d used
      rw [V.coefficient_dependency] at used
      exact Or.inl (Set.mem_singleton_iff.mp used)

/-- Retaining the coefficient block makes the fixed scalar context available. -/
theorem coefficients_le (kept : RetainsCoefficients U) : coefficients L ≤ U := by
  intro d hd
  rcases hd with rfl | ⟨f, rfl⟩
  · exact kept.sort
  · exact kept.operation f

/-- A coefficient-only declaration context cannot contain a module sort. -/
private theorem no_module (s : V.SortName) :
    Declaration.sort (some s) ∉ (coefficients L).declarations := by
  rintro (different | ⟨f, different⟩)
  · have eq := Declaration.sort.inj different
    cases eq
  · cases different

/-- A coefficient-only declaration context cannot contain a marked multilinear symbol. -/
private theorem no_multilinear (f : V.Multilinear) :
    V.multilinearDecl L f ∉ (coefficients L).declarations := by
  rintro (different | ⟨op, different⟩)
  · cases different
  · have eq := Declaration.total.inj different
    cases eq

/-- The coefficient context has no module data to add to the fixed ring. -/
def coefficientData (R : Type u) [CommRing R] (L : V.Laws) : Data R (coefficients L) where
  kernel s kept := (no_module s kept).elim
  operation f kept := (no_multilinear f kept).elim

/-- The fixed coefficient structure on the actual ordinary scalar signature. -/
noncomputable def coefficientStructure (R : Type u) [CommRing R] (L : V.Laws) :
    Structure (Selected.signature (coefficients L)) :=
  Selected.readStructure (coefficientData R L).contextStructure

/-- The scalar reduct of a marked realization is the fixed ring as an ordinary structure. -/
theorem Realization.coefficient_restriction (A : Realization R U) (kept : RetainsCoefficients U) :
    ((Selected.modelRestriction (coefficients_le kept)).obj A.ordinaryModel).obj = coefficientStructure R L := by
  have agree : A.data.Agree (coefficientData R L) :=
    ⟨fun s _ hs => (no_module s hs).elim, fun f _ hf => (no_multilinear f hf).elim⟩
  rw [Selected.modelRestriction_obj, Realization.writeModel_ordinaryModel]
  exact congrArg Selected.readStructure (agree.contextStructure_restrict_eq (coefficients_le kept))

/-- Each retained module guarantees the fixed scalar reduct by its block condition. -/
theorem Realization.coefficient_restriction_of_module (A : Realization R U)
    (s : V.SortName) (kept : Declaration.sort (some s) ∈ U.declarations) :
    ((Selected.modelRestriction (coefficients_le (A.blocks.coefficients s kept))).obj A.ordinaryModel).obj =
      coefficientStructure R L :=
  A.coefficient_restriction (A.blocks.coefficients s kept)

end SHIGURE.Marked
