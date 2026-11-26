import Formal.SHIGURE.Part1.ContextSelectedStructures

/-!
# Fixed state in a quantity Law

Replacing candidate values preserves the argument carriers, partial
domains and fixed primitive interpretations. The grammar of state
terms and guards permits reads of the fixed domain of a partial
quantity independently of the value returned there.
-/

universe u

namespace SHIGURE.Quantities

/-- A fixed-state formula may read partial domains without reading the varying value graphs. -/
def StateFormula {sig : Signature.{u}} (variableValues : Set (Operation sig)) :
    {Γ : List sig.SortType} → Formula sig Γ → Prop
  | _, .atom (.graph op _ _) => op ∉ variableValues
  | _, .atom (.eq ..) | _, .atom (.rel ..) | _, .atom (.domain ..) => True
  | _, .truth | _, .falsehood => True
  | _, .conj p q | _, .disj p q => StateFormula variableValues p ∧ StateFormula variableValues q
  | _, .ex p => StateFormula variableValues p

/-- A state term uses no graph whose values are supplied by a candidate quantity. -/
def StateTerm {sig : Signature.{u}} (variableValues : Set (Operation sig)) :
    {Γ : List sig.SortType} → {s : sig.SortType} → Term sig Γ s → Prop
  | _, _, .var _ => True
  | _, _, .app op args => op ∉ variableValues ∧ ∀ {s} (i : Var op.arity.inputs s),
      StateTerm variableValues (args i)
  | _, _, .letBind x t => StateTerm variableValues x ∧ StateTerm variableValues t

/-- A finite conjunction retains fixed-state dependence if each conjunct does. -/
private theorem stateFormula_conjoin {sig : Signature.{u}} {variableValues : Set (Operation sig)}
    {Γ : List sig.SortType} (Λ : List sig.SortType)
    (parts : ∀ {s}, Var Λ s → Formula sig Γ)
    (state : ∀ {s} (i : Var Λ s), StateFormula variableValues (parts i)) :
    StateFormula variableValues (Formula.conjoin Λ parts) := by
  induction Λ with
  | nil => rw [Formula.conjoin_nil]; trivial
  | cons s rest ih =>
    rw [Formula.conjoin_cons]
    exact ⟨state .here, ih (fun i => parts (.there i)) (fun i => state (.there i))⟩

/-- Existential closure leaves the formula's dependencies on value graphs unchanged. -/
private theorem stateFormula_existsMany {sig : Signature.{u}} {variableValues : Set (Operation sig)}
    {Γ : List sig.SortType} (Λ : List sig.SortType) (p : Formula sig (Λ ++ Γ))
    (state : StateFormula variableValues p) :
    StateFormula variableValues (Formula.existsMany Λ p) := by
  induction Λ with
  | nil => simpa only [Formula.existsMany_nil] using state
  | cons s rest ih =>
    rw [Formula.existsMany_cons]
    exact ih p.ex state

/-- Writing the graph of a fixed-state term preserves independence of the candidate quantity values. -/
theorem stateFormula_graphAt {sig : Signature.{u}} {variableValues : Set (Operation sig)}
    {Γ : List sig.SortType} {s : sig.SortType} (t : Term sig Γ s) (state : StateTerm variableValues t) :
    ∀ {Δ : List sig.SortType} (ρ : Renaming Γ Δ) (y : Var Δ s),
      StateFormula variableValues (t.graphAt ρ y) := by
  induction t with
  | var i =>
    intro Δ ρ y
    rw [Term.graphAt_var]
    trivial
  | app op ts ih =>
    intro Δ ρ y
    rw [Term.graphAt_app]
    apply stateFormula_existsMany
    refine ⟨stateFormula_conjoin _ _ (fun i => ?_), state.1⟩
    exact ih i (state.2 i) _ _
  | letBind x t hx ht =>
    intro Δ ρ y
    rw [Term.graphAt_letBind]
    exact ⟨hx state.1 _ _, ht state.2 _ _⟩

open DeclarationContext

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P} {X : P.signature.SortType → Type u}

/-- The state interpretation and all domains agree when candidate quantity values are replaced. -/
structure SameStateEvaluation (variableValues : Set (Operation P.signature))
    (A B : RestrictedEvaluation U X) : Prop where
  relation : ∀ r keep x, A.relation r keep x ↔ B.relation r keep x
  domain : ∀ p keep x, A.domain p keep x ↔ B.domain p keep x
  graph : ∀ op ∉ variableValues, ∀ keep x y, A.graph op keep x y ↔ B.graph op keep x y

/-- A guard with only fixed-state reads has the same truth for all candidate quantity values. -/
theorem SameStateEvaluation.holds_iff {variableValues : Set (Operation P.signature)}
    {A B : RestrictedEvaluation U X} (same : SameStateEvaluation variableValues A B)
    {Γ : List P.signature.SortType} (p : Formula P.signature Γ)
    (state : StateFormula variableValues p)
    (keep : Declaration.formulaSupport p ⊆ U.declarations) (e : Assignment X Γ) :
    A.holds p keep e ↔ B.holds p keep e := by
  induction p with
  | atom a =>
    rw [RestrictedEvaluation.holds_atom_iff, RestrictedEvaluation.holds_atom_iff]
    cases a with
    | eq x y => rfl
    | rel r vars => exact same.relation r _ (e.pull vars)
    | domain p vars => exact same.domain p _ (e.pull vars)
    | graph op vars y => exact same.graph op state _ (e.pull vars) (e y)
  | truth => rfl
  | falsehood => rfl
  | conj p q hp hq =>
    rw [RestrictedEvaluation.holds_conj_iff, RestrictedEvaluation.holds_conj_iff]
    exact and_congr (hp state.1 _ e) (hq state.2 _ e)
  | disj p q hp hq =>
    rw [RestrictedEvaluation.holds_disj_iff, RestrictedEvaluation.holds_disj_iff]
    exact or_congr (hp state.1 _ e) (hq state.2 _ e)
  | ex p hp =>
    rw [RestrictedEvaluation.holds_ex_iff, RestrictedEvaluation.holds_ex_iff]
    exact exists_congr (fun x => hp state _ (Assignment.cons x e))

/-- State argument evaluation is unchanged when the designated quantity values are replaced. -/
theorem SameStateEvaluation.evaluates_iff {variableValues : Set (Operation P.signature)}
    {A B : RestrictedEvaluation U X} (same : SameStateEvaluation variableValues A B)
    {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : U.TermIn Γ s) (state : StateTerm variableValues t.val) (e : Assignment X Γ)
    (y : X s) :
    A.holds t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property) (Assignment.cons y e) ↔
    B.holds t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property) (Assignment.cons y e) := by
  apply same.holds_iff
  rw [Term.graph_eq_graphAt]
  exact stateFormula_graphAt t.val state _ _

end SHIGURE.Quantities
