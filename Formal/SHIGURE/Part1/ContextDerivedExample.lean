import Formal.SHIGURE.Part1.ContextPresentation

/-! # The constant in a derivation of nonemptiness

The derived Law only asserts existence of a point. Its proof uses the
structural totality of a constant, which the restriction must also retain.
-/

namespace SHIGURE.Chapter3.DerivedNonempty

open DeclarationContext

/-- A single sort with one nullary total operation. -/
def signature : Signature where
  SortType := Unit
  Total := Unit
  totalArity _ := ⟨[], ()⟩
  Rel := PEmpty
  relInputs r := nomatch r
  Partial := PEmpty
  partialArity p := nomatch p
  Quantity := PEmpty
  quantityArity q := nomatch q

/-- Nonemptiness is written without referring to the constant. -/
def nonemptyLaw : Law signature := ⟨[], .truth, .ex (s := ()) .truth⟩

/-- The sole Law is declared derived. -/
def laws : LawDeclarations signature := ⟨Unit, fun _ => nonemptyLaw, fun _ => .derived⟩

/-- The constant graph under a binder for its value. -/
def graphFormula : Formula signature [()] :=
  .atom (.graph (.total ()) (fun i => .there i) .here)

/-- The actual structural rule supplies a value of the nullary constant. -/
def constantHasValue : Derivation laws.toTheory (Formula.truth (Γ := [])) graphFormula.ex := by
  simpa only [GraphAxiom.toLaw_totality, GraphAxiom.hasOutput_eq_ex_graph, graphFormula] using
    Derivation.graph (T := laws.toTheory) (.totality ())

/-- Existential elimination uses the graph witness to prove plain nonemptiness. -/
def forgetGraph : Derivation laws.toTheory ((Formula.truth (Γ := [])).conj graphFormula.ex)
    nonemptyLaw.conclusion := by
  apply Derivation.existsElim (T := laws.toTheory) (p := graphFormula) (c := Formula.truth)
    (q := nonemptyLaw.conclusion)
  let body : Formula signature [(), ()] := .truth
  have witness : Derivation laws.toTheory (Formula.truth (sig := signature) (Γ := [()])) body.ex :=
    Derivation.existsIntro (T := laws.toTheory) (Γ := [()]) (s := ()) body .here
  exact .cut (.truth _) witness

/-- Use the graph of the constant to witness nonemptiness. -/
def proof : Derivation laws.toTheory nonemptyLaw.input nonemptyLaw.conclusion :=
  .cut (.andIntro (.refl .truth) constantHasValue) forgetGraph

/-- The original presentation attaches this derivation to the existential Law. -/
def presentation : PrimitivePresentation where
  signature := signature
  laws := laws
  derived _ _ := proof

/-- The constant does not occur in the visible statement of the derived Law. -/
theorem constant_absent_from_statement :
    Declaration.total () ∉ Declaration.lawBody (P := presentation) nonemptyLaw := by
  simp [Declaration.lawBody_eq, Declaration.sorts_eq_image, Declaration.formula_truth,
    Declaration.formula_ex, nonemptyLaw]

/-- The graph axiom keeps the constant among the derivation's required declarations. -/
theorem constant_used_by_derivation :
    Declaration.total () ∈ Declaration.derivation (P := presentation) (presentation.derived () rfl) := by
  have used : Declaration.total () ∈ Declaration.derivation (P := presentation) constantHasValue :=
    Declaration.graphRuleName_mem_derivation (P := presentation) (.totality ())
  exact Declaration.derivation_cut_left _ _ (Declaration.derivation_andIntro_right _ _ used)

/-- A closed context that keeps the derived Law also keeps the constant used in its proof. -/
theorem derived_keeps_constant (U : DeclarationContext presentation)
    (kept : Declaration.law () ∈ U.declarations) : Declaration.total () ∈ U.declarations :=
  U.closed kept (Declaration.derivation_subset_dependsOn () rfl constant_used_by_derivation)

/-- The original proof is available as a checked derivation in the restricted presentation. -/
noncomputable def retainedProof (U : DeclarationContext presentation)
    (kept : Declaration.law () ∈ U.declarations) : U.DerivationIn nonemptyLaw.input nonemptyLaw.conclusion :=
  U.derived ⟨(), kept⟩ rfl

end SHIGURE.Chapter3.DerivedNonempty
