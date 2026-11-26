import Formal.SHIGURE.Part1.ContextSelectedEquations

/-! # Expanding binders in declared coefficient terms

Strict evaluation of the original term supplies the values inserted by
substitution. Expansion uses only declarations from the written term and
commutes with selecting its signature.
-/

namespace SHIGURE
namespace Term

universe u

variable {sig : Signature.{u}} {Γ : List sig.SortType} {a s : sig.SortType}

/-- Substitute only the new head; earlier variables keep their original positions. -/
def bindReplacement (init : Term sig Γ a) : Substitution sig (a :: Γ) Γ :=
  ⟨fun i => match i with
    | .here => init
    | .there j => .var j⟩

/-- Expand strict binders by substituting into their normalized bodies. -/
def inlineLets : {Γ : List sig.SortType} → {s : sig.SortType} → Term sig Γ s → Term sig Γ s
  | _, _, .var i => .var i
  | _, _, .app op args => .app op (fun i => (args i).inlineLets)
  | _, _, .letBind init body => body.inlineLets.substitute (bindReplacement init.inlineLets)

/-- An original term with a value keeps that value when its binders are expanded. -/
theorem evaluates_inlineLets (A : Structure sig) (t : Term sig Γ s) :
    ∀ (e : Assignment A.carrier Γ) (y : A.carrier s), t.Evaluates A e y →
      t.inlineLets.Evaluates A e y := by
  induction t with
  | var i => intros; assumption
  | app op args ih =>
    intro e y value
    obtain ⟨xs, each, edge⟩ := (evaluates_app_iff op (fun i => args i) A e y).1 value
    exact (evaluates_app_iff op (fun i => (args i).inlineLets) A e y).2
      ⟨xs, fun i => ih i e (xs i) (each i), edge⟩
  | letBind init body initIH bodyIH =>
    intro e y value
    obtain ⟨x, hx, hy⟩ := (evaluates_let_iff init body A e y).1 value
    have hθ : (bindReplacement init.inlineLets).EvaluatesAt A e (Assignment.cons x e) := by
      intro s i
      cases i with
      | here => exact initIH e x hx
      | there i => rfl
    exact (body.inlineLets.evaluates_substitute_of_evaluatesAt A _
      e (Assignment.cons x e) y hθ).2 (bodyIH (Assignment.cons x e) y hy)

/-- Expanding a term is independent of how its free context was identified. -/
theorem inlineLets_cast_context {Δ : List sig.SortType} (same : Γ = Δ) (t : Term sig Γ s) :
    (cast (congrArg (fun ctx => Term sig ctx s) same) t).inlineLets =
      cast (congrArg (fun ctx => Term sig ctx s) same) t.inlineLets := by
  cases same
  rfl

/-- Expanding a reindexed application expands only its arguments. -/
theorem inlineLets_reindexedApp (op : Operation sig) {profile : Arity sig.SortType}
    (same : op.arity = profile) (args : ∀ {s}, Var profile.inputs s → Term sig Γ s) :
    (Term.reindexedApp op same args).inlineLets =
      Term.reindexedApp op same (fun i => (args i).inlineLets) := by
  cases same
  rfl

end Term

namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- Substituting supported terms introduces only references from the original term and the substitution. -/
theorem termReferences_substitute_le {Γ : List P.signature.SortType}
    {s : P.signature.SortType} (t : Term P.signature Γ s) :
    ∀ {Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
      (_keep : termReferences t ⊆ U.declarations)
      (_terms : ∀ {a} (i : Var Γ a), termReferences (θ i) ⊆ U.declarations),
        termReferences (t.substitute θ) ⊆ U.declarations := by
  induction t with
  | var i => intro Δ θ keep terms; exact terms i
  | app op args ih =>
    intro Δ θ keep terms
    simp only [Term.substitute_app, termReferences_app] at keep ⊢
    intro d used
    rcases used with operation | ⟨a, i, arg⟩
    · exact keep (Or.inl operation)
    · exact (ih i θ (fun _ h => keep (Or.inr ⟨_, i, h⟩)) terms) arg
  | letBind init body hi hb =>
    intro Δ θ keep terms
    simp only [Term.substitute_letBind, termReferences_letBind] at keep ⊢
    intro d used
    rcases used with sort | arg | bodyRef
    · exact keep (Or.inl sort)
    · exact (hi θ (fun _ h => keep (Or.inr (Or.inl h))) terms) arg
    · exact (hb θ.lift (fun _ h => keep (Or.inr (Or.inr h))) (liftTermReferences θ terms)) bodyRef

/-- Expansion of strict binders keeps only references already in the original term. -/
theorem inlineLets_supported {Γ : List P.signature.SortType}
    {s : P.signature.SortType} (t : Term P.signature Γ s)
    (keep : termReferences t ⊆ U.declarations) :
    termReferences t.inlineLets ⊆ U.declarations := by
  induction t with
  | var i => exact keep
  | app op args ih =>
    simp only [Term.inlineLets, termReferences_app] at keep ⊢
    intro d used
    rcases used with operation | ⟨a, i, arg⟩
    · exact keep (Or.inl operation)
    · exact (ih i (fun _ h => keep (Or.inr ⟨_, i, h⟩))) arg
  | letBind init body hi hb =>
    simp only [Term.inlineLets, termReferences_letBind] at keep ⊢
    apply termReferences_substitute_le _ _
      (hb (fun _ h => keep (Or.inr (Or.inr h))))
    intro a i
    cases i with
    | here => exact hi (fun _ h => keep (Or.inr (Or.inl h)))
    | there i =>
      change termReferences (.var i) ⊆ U.declarations
      simp only [termReferences_var, Set.empty_subset]

private theorem bindReplacement_supported {Γ : List P.signature.SortType} {a : P.signature.SortType}
    (init : Term P.signature Γ a) (keep : termReferences init ⊆ U.declarations)
    {s : P.signature.SortType} (i : Var (a :: Γ) s) :
    termReferences (init.bindReplacement i) ⊆ U.declarations := by
  cases i with
  | here => exact keep
  | there i =>
    change termReferences (.var i) ⊆ U.declarations
    rw [termReferences_var]
    exact Set.empty_subset _

private theorem selectBindReplacement {Γ : List P.signature.SortType} {a : P.signature.SortType}
    (init : Term P.signature Γ a) (hΓ : Declaration.sorts Γ ⊆ U.declarations)
    (ha : Declaration.sort a ∈ U.declarations) (ht : termReferences init ⊆ U.declarations) :
    cast (congrArg (fun ctx => Substitution (signature U) ctx (context Γ hΓ))
        (context_cons a Γ (Declaration.sorts_cons_subset ha hΓ)))
      (selectSubstitution init.bindReplacement (Declaration.sorts_cons_subset ha hΓ) hΓ
        (bindReplacement_supported init ht)) =
      (selectTerm init hΓ ha ht).bindReplacement := by
  apply Substitution.ext
  intro s v
  let start := Declaration.sorts_cons_subset ha hΓ
  let source := context_cons a Γ start
  change (cast (congrArg₂ (Substitution (signature U)) source rfl)
    (selectSubstitution init.bindReplacement start hΓ (bindReplacement_supported init ht))) v = _
  rw [Substitution.cast_context_apply source rfl, selectSubstitution_at]
  simp only [cast_eq]
  cases v with
  | here =>
    let original := ambientVar start (cast (congrArg (Var · (⟨a, ha⟩ : SortName U)) source.symm) .here)
    have known : init.bindReplacement original = init :=
      congrArg (fun i : Var (a :: Γ) a => init.bindReplacement i) (ambientVar_cast_here start)
    exact selectTerm_congr known hΓ ha (bindReplacement_supported init ht original) ht
  | there v =>
    let original := ambientVar start (cast (congrArg (Var · s) source.symm) (.there v))
    let i := ambientVar hΓ v
    have known : init.bindReplacement original = .var i :=
      congrArg (fun j : Var (a :: Γ) s.val => init.bindReplacement j) (ambientVar_cast_there start v)
    have keepVar : termReferences (Term.var (sig := P.signature) i) ⊆ U.declarations := by
      rw [termReferences_var]
      exact Set.empty_subset _
    change selectTerm (init.bindReplacement original) hΓ s.property (bindReplacement_supported init ht original) = .var v
    exact (selectTerm_congr known hΓ s.property (bindReplacement_supported init ht original) keepVar).trans
      ((selectTerm_var i hΓ s.property keepVar).trans (congrArg (Term.var (sig := signature U))
        (selectVar_ambientVar hΓ v)))

/-- Selecting a term commutes with expanding the strict binders. -/
theorem selectTerm_inlineLets {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : Term P.signature Γ s) (hΓ : Declaration.sorts Γ ⊆ U.declarations)
    (hs : Declaration.sort s ∈ U.declarations) (ht : termReferences t ⊆ U.declarations) :
    selectTerm t.inlineLets hΓ hs (inlineLets_supported t ht) =
      (selectTerm t hΓ hs ht).inlineLets := by
  induction t with
  | var i => rfl
  | app op args ih =>
    simp only [Term.inlineLets, selectTerm_app, Term.inlineLets_reindexedApp]
    congr 1
    funext s i
    exact ih _ hΓ s.property _
  | @letBind Γ a s init body hi hb =>
    have kept := (termReferences_letBind init body).ge.trans ht
    let ha := kept (Or.inl (Set.mem_singleton (Declaration.sort a)))
    let hΓ' := Declaration.sorts_cons_subset ha hΓ
    let hInit : termReferences init ⊆ U.declarations := fun _ h => kept (Or.inr (Or.inl h))
    let hBody : termReferences body ⊆ U.declarations := fun _ h => kept (Or.inr (Or.inr h))
    let source := context_cons a Γ hΓ'
    let θ := init.inlineLets.bindReplacement
    let hθ : ∀ {s} (i : Var (a :: Γ) s), termReferences (θ i) ⊆ U.declarations :=
      fun i => bindReplacement_supported init.inlineLets (inlineLets_supported init hInit) i
    change selectTerm (body.inlineLets.substitute θ) hΓ hs _ = _
    rw [selectTerm_substitute body.inlineLets θ hΓ' hΓ hs (inlineLets_supported body hBody) hθ,
      selectTerm_letBind_cast, Term.inlineLets]
    let A := selectTerm body.inlineLets hΓ' hs (inlineLets_supported body hBody)
    let A' := selectTerm body hΓ' hs hBody
    have bodySame : A = A'.inlineLets := hb hΓ' hs hBody
    have initSame := hi hΓ ha hInit
    let head : SortName U := ⟨a, ha⟩
    let carry := cast (congrArg (fun ctx => Term (signature U) ctx ⟨s, hs⟩) source)
    let selected := selectSubstitution θ hΓ' hΓ hθ
    change A.substitute selected =
      (carry A').inlineLets.substitute ((selectTerm init hΓ ha hInit).inlineLets.bindReplacement (a := head))
    rw [Term.inlineLets_cast_context source A', ← bodySame, ← initSame,
      ← selectBindReplacement init.inlineLets hΓ ha (inlineLets_supported init hInit)]
    exact (Term.substitute_cast_context source rfl selected A).symm

end DeclarationContext.Selected
end SHIGURE
