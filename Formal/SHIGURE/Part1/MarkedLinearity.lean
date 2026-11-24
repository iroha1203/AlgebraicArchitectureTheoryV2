import Formal.SHIGURE.Part1.MarkedInterpretation

/-! # The required multilinearity Laws hold in the marked semantics

The two Law declarations for each input position in Proposition 3.6 are
evaluated on an actual mathlib multilinear map. The selected position is
the same in the written terms and in the dependent tuple passed to the
map.
-/

universe u

namespace SHIGURE.Marked

open Vocabulary

variable {V : Vocabulary.{u}} {R : Type u} [CommRing R]
variable (K : ∀ s : V.SortName, Kernel R (V.generators s))
variable (maps : ∀ f, (kernelsOf K f).Map)
variable {Γ : List (Option V.SortName)}

/-- The coefficient and module addition terms both use their actual carrier addition. -/
theorem addTerm_totalValue (s : Option V.SortName) (x y : Term V.signature Γ s)
    (e : Assignment (quotientCarriers K) Γ) :
    (V.addTerm s x y).totalValue (quotientStructure K maps) e =
      @Add.add (quotientCarriers K s) _
        (x.totalValue (quotientStructure K maps) e) (y.totalValue (quotientStructure K maps) e) := by
  cases s <;> rfl

/-- The scalar multiplication term uses the actual action of the fixed coefficient ring. -/
theorem smulTerm_totalValue (s : Option V.SortName) (a : Term V.signature Γ none) (x : Term V.signature Γ s)
    (e : Assignment (quotientCarriers K) Γ) :
    (V.smulTerm s a x).totalValue (quotientStructure K maps) e =
      @SMul.smul R (quotientCarriers K s) _
        (a.totalValue (quotientStructure K maps) e) (x.totalValue (quotientStructure K maps) e) := by
  cases s <;> rfl

/-- Replacing an argument term evaluates to replacing the corresponding value. -/
theorem updatedTerm_totalValue {f : V.Multilinear} [DecidableEq (V.Position f)]
    (names : Renaming (V.inputs f) Γ) (i : V.Position f) (x : Term V.signature Γ i.1)
    (e : Assignment (quotientCarriers K) Γ) :
    (V.updatedTerm names i x).totalValue (quotientStructure K maps) e =
      maps f (Function.update (fun j => e (names j.2)) i (x.totalValue (quotientStructure K maps) e)) := by
  change maps f (fun j => (V.updatedTerms names i x j).totalValue (quotientStructure K maps) e) = _
  apply congrArg (maps f)
  funext j
  by_cases same : j = i
  · subst j
    rw [V.updatedTerms_same, Function.update_self]
  · rw [V.updatedTerms_other names i j x same, Function.update_of_ne same, Term.totalValue_var]

/-- The addition equation is a genuine required Law satisfied by any marked map. -/
theorem holds_addLinearityLaw {f : V.Multilinear} (i : V.Position f) :
    (V.addLinearityLaw i).Holds (quotientStructure K maps) := by
  classical
  simp only [addLinearityLaw_eq, Law.holds_equality_totalValue_iff, addTerm_totalValue, updatedTerm_totalValue,
    Term.totalValue_var]
  intro e
  exact (maps f).map_update_add (fun j => e (j.2.there.there)) i (e .here) (e (.there .here))

/-- The scalar equation is a genuine required Law satisfied by any marked map. -/
theorem holds_smulLinearityLaw {f : V.Multilinear} (i : V.Position f) :
    (V.smulLinearityLaw i).Holds (quotientStructure K maps) := by
  classical
  simp only [smulLinearityLaw_eq, Law.holds_equality_totalValue_iff, smulTerm_totalValue, updatedTerm_totalValue,
    Term.totalValue_var]
  intro e
  exact (maps f).map_update_smul (fun j => e (j.2.there.there)) i (e .here) (e (.there .here))

/-- Every generated Law of the ordinary presentation follows from the actual marked maps. -/
theorem holds_linearity {L : V.Laws} {U : DeclarationContext (V.presentation L)}
    (a : Data R U) (name : V.LinearityLaw) :
    ((V.presentation L).laws.statement (.inr name)).Holds a.structureData := by
  rw [V.linearity_statement]
  cases name with
  | add f i => exact holds_addLinearityLaw a.ambientKernel a.ambientOperation i
  | smul f i => exact holds_smulLinearityLaw a.ambientKernel a.ambientOperation i

end SHIGURE.Marked
