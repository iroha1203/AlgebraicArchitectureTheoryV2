import Formal.SHIGURE.Part1.MarkedVocabulary
import Formal.SHIGURE.Part1.ContextSelectedTerms

/-! # Supported equational terms in a marked context

The written Law support can be verified from the term references and the
typed arities of its retained operations. This avoids examining the
existential value-graph expansion when closing the contexts of Example 3.7.
-/

universe u

namespace SHIGURE.Marked

open DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {D : Set (Declaration P)}
variable {Γ : List P.signature.SortType} {s : P.signature.SortType}

/-- A variable contributes no operation or bound-sort references. -/
theorem variable_refs (i : Var Γ s) : termReferences (Term.var (sig := P.signature) i) ⊆ D :=
  Set.empty_subset _

/-- Keeping an application requires its graph symbol and the references of its arguments. -/
theorem app_refs (op : Operation P.signature)
    (xs : ∀ {t}, Var op.arity.inputs t → Term P.signature Γ t)
    (kept : Declaration.ofOperation op ∈ D)
    (args : ∀ {t} (i : Var op.arity.inputs t), termReferences (xs i) ⊆ D) :
    termReferences (Term.app op xs) ⊆ D := by
  intro d used
  rcases used with hd | ⟨_, i, hd⟩
  · simpa only [Set.mem_singleton_iff.mp hd] using kept
  · exact args i hd

/-- If the declaration set supports each conjunct, it also supports the conjunction. -/
private theorem conjoined_support (Λ : List P.signature.SortType)
    (ps : ∀ {t}, Var Λ t → Formula P.signature Γ)
    (kept : ∀ {t} (i : Var Λ t), Declaration.formula (ps i) ⊆ D) :
    Declaration.formula (Formula.conjoin Λ ps) ⊆ D := by
  induction Λ with
  | nil =>
    rw [Formula.conjoin_nil, Declaration.formula_truth]
    exact Set.empty_subset _
  | cons s more ih =>
    rw [Formula.conjoin_cons, Declaration.formula_conj]
    exact Set.union_subset (kept .here) (ih (fun i => ps (.there i)) (fun i => kept (.there i)))

/-- Record the bound sort together with the support of the existential body. -/
private theorem bound_support (Λ : List P.signature.SortType) (p : Formula P.signature (Λ ++ Γ))
    (sorts : Declaration.sorts Λ ⊆ D) (kept : Declaration.formula p ⊆ D) :
    Declaration.formula (Formula.existsMany Λ p) ⊆ D := by
  induction Λ with
  | nil =>
    rw [Formula.existsMany_nil]
    exact kept
  | cons s more ih =>
    rw [Formula.existsMany_cons]
    apply ih p.ex ((DeclarationContext.tailSortsSubset s more).trans sorts)
    rw [Declaration.formula_ex]
    refine Set.union_subset ?_ kept
    exact Set.singleton_subset_iff.mpr (sorts ⟨s, List.mem_cons_self, rfl⟩)

/-- Track all typed names used by a term's value graph. -/
private theorem graphAt_support (t : Term P.signature Γ s)
    (types : ∀ op : Operation P.signature, Declaration.ofOperation op ∈ D → Declaration.sorts op.arity.inputs ⊆ D)
    (references : termReferences t ⊆ D) :
    ∀ {Δ : List P.signature.SortType} (ρ : Renaming Γ Δ) (y : Var Δ s),
      Declaration.formula (t.graphAt ρ y) ⊆ D := by
  induction t with
  | var i =>
    intro Δ names out
    rw [Term.graphAt_var, Declaration.formula_atom, Declaration.atomic_eq]
    exact Set.empty_subset _
  | app op xs ih =>
    intro Δ names out
    rw [Term.graphAt_app]
    have kept := references (Or.inl (Set.mem_singleton _))
    apply bound_support _ _ (types op kept)
    rw [Declaration.formula_conj, Declaration.formula_atom, Declaration.atomic_graph]
    refine Set.union_subset (conjoined_support _ _ (fun i => ?_)) (Set.singleton_subset_iff.mpr kept)
    exact ih i (fun _ used => references (Or.inr ⟨_, i, used⟩)) _ _
  | letBind init body initIH bodyIH =>
    intro Δ names out
    rw [Term.graphAt_letBind, Declaration.formula_ex, Declaration.formula_conj]
    refine Set.union_subset (Set.singleton_subset_iff.mpr (references (Or.inl (Set.mem_singleton _)))) ?_
    exact Set.union_subset (initIH (fun _ used => references (Or.inr (Or.inl used))) _ _)
      (bodyIH (fun _ used => references (Or.inr (Or.inr used))) _ _)

/-- An equality Law is supported by its context, result sort and the typed references of both terms. -/
theorem equality_law_support (left right : Term P.signature Γ s)
    (types : ∀ op : Operation P.signature, Declaration.ofOperation op ∈ D → Declaration.sorts op.arity.inputs ⊆ D)
    (context : Declaration.sorts Γ ⊆ D) (result : Declaration.sort s ∈ D)
    (leftRefs : termReferences left ⊆ D) (rightRefs : termReferences right ⊆ D) :
    Declaration.lawBody (Law.equality left right) ⊆ D := by
  rw [Law.equality_eq, Declaration.lawBody_eq]
  simp only [Declaration.formula_truth, Formula.termEq_eq_ex, Declaration.formula_ex,
    Declaration.formula_conj, Term.graph_eq_graphAt]
  refine Set.union_subset (Set.union_subset context (Set.empty_subset _)) ?_
  exact Set.union_subset (Set.singleton_subset_iff.mpr result)
    (Set.union_subset (graphAt_support left types leftRefs _ _) (graphAt_support right types rightRefs _ _))

/-- Account for both typed argument positions of a binary application in its reference set. -/
private theorem two_arg_ref {t : P.signature.SortType} (x : Term P.signature Γ s) (y : Term P.signature Γ t)
    (hx : termReferences x ⊆ D) (hy : termReferences y ⊆ D)
    {a : P.signature.SortType} (i : Var [s, t] a) :
    termReferences (x.argsCons (y.argsCons Term.argsNil) i) ⊆ D := by
  cases i with
  | here => exact hx
  | there tail =>
    cases tail with
    | here => exact hy
    | there empty => cases empty

section Arithmetic

open Vocabulary

variable {V : Vocabulary.{u}} {L : V.Laws} {keep : Set (Declaration (V.presentation L))}
variable {Δ : List (Option V.SortName)}

/-- The references of addition come from its two terms and the indicated addition symbol. -/
theorem addTerm_refs (s : Option V.SortName) (x y : Term V.signature Δ s)
    (op : (match s with | none => V.coefficientDecl L .add | some s => V.moduleDecl L s .add) ∈ keep)
    (hx : termReferences x ⊆ keep) (hy : termReferences y ⊆ keep) :
    termReferences (V.addTerm s x y) ⊆ keep := by
  cases s with
  | none =>
    exact app_refs (P := V.presentation L) (.total (Symbol.coefficient .add)) _ op
      (fun i => two_arg_ref (P := V.presentation L) x y hx hy i)
  | some s =>
    exact app_refs (P := V.presentation L) (.total (Symbol.moduleOp s .add)) _ op
      (fun i => two_arg_ref (P := V.presentation L) x y hx hy i)

/-- The references of scalar multiplication include the correct coefficient or module symbol. -/
theorem smulTerm_refs (s : Option V.SortName) (a : Term V.signature Δ none) (x : Term V.signature Δ s)
    (op : (match s with | none => V.coefficientDecl L .mul | some s => V.moduleDecl L s .smul) ∈ keep)
    (ha : termReferences a ⊆ keep) (hx : termReferences x ⊆ keep) :
    termReferences (V.smulTerm s a x) ⊆ keep := by
  cases s with
  | none =>
    exact app_refs (P := V.presentation L) (.total (Symbol.coefficient .mul)) _ op
      (fun i => two_arg_ref (P := V.presentation L) a x ha hx i)
  | some s =>
    exact app_refs (P := V.presentation L) (.total (Symbol.moduleOp s .smul)) _ op
      (fun i => two_arg_ref (P := V.presentation L) a x ha hx i)

end Arithmetic

end SHIGURE.Marked
