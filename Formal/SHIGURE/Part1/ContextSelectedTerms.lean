import Formal.SHIGURE.Part1.ContextSelectedSyntax

/-! # Ordered terms over the selected signature

The same supported term can be read over the smaller signature. Its
variables retain their positions, and the read commutes with graph syntax.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- The primitive references of a term, apart from its free context and result sort. -/
def termReferences : {Γ : List P.signature.SortType} → {s : P.signature.SortType} →
    Term P.signature Γ s → Set (Declaration P)
  | _, _, .var _ => ∅
  | _, _, .app op args =>
    {Declaration.ofOperation op} ∪ {d | ∃ (s : P.signature.SortType) (i : Var op.arity.inputs s),
      d ∈ termReferences (args i)}
  | _, _, @Term.letBind _ _ s _ x y => {Declaration.sort s} ∪ (termReferences x ∪ termReferences y)

/-- A variable contributes no primitive or binder references. -/
theorem termReferences_var {Γ : List P.signature.SortType} {s : P.signature.SortType} (i : Var Γ s) :
    termReferences (Term.var (sig := P.signature) i) = ∅ :=
  rfl

/-- An application references its operation and every argument term. -/
theorem termReferences_app {Γ : List P.signature.SortType} (op : Operation P.signature)
    (args : ∀ {s}, Var op.arity.inputs s → Term P.signature Γ s) :
    termReferences (Term.app op args) =
      {Declaration.ofOperation op} ∪
        {d | ∃ (s : P.signature.SortType) (i : Var op.arity.inputs s), d ∈ termReferences (args i)} :=
  rfl

/-- A strict let references its bound sort, initial value and body. -/
theorem termReferences_letBind {Γ : List P.signature.SortType} {a s : P.signature.SortType}
    (init : Term P.signature Γ a) (body : Term P.signature (a :: Γ) s) :
    termReferences (init.letBind body) =
      {Declaration.sort a} ∪ (termReferences init ∪ termReferences body) :=
  rfl

/-- Read the primitive references of a member of a conjunction from the conjunction's support. -/
private theorem formula_conjoin_subset {Γ Λ : List P.signature.SortType}
    (ps : ∀ {s}, Var Λ s → Formula P.signature Γ) {s} (i : Var Λ s) :
    Declaration.formula (ps i) ⊆ Declaration.formula (Formula.conjoin Λ ps) := by
  induction i with
  | here =>
    rw [Formula.conjoin_cons, Declaration.formula_conj]
    intro d hd
    exact Or.inl hd
  | there i ih =>
    rw [Formula.conjoin_cons, Declaration.formula_conj]
    intro d hd
    exact Or.inr (ih (fun j => ps (.there j)) hd)

/-- Keep the body's primitive references after existentially quantifying the context prefix. -/
private theorem formula_existsMany_subset {Γ : List P.signature.SortType}
    (Λ : List P.signature.SortType) (p : Formula P.signature (Λ ++ Γ)) :
    Declaration.formula p ⊆ Declaration.formula (Formula.existsMany Λ p) := by
  induction Λ with
  | nil => rw [Formula.existsMany_nil]
  | cons s Λ ih =>
    rw [Formula.existsMany_cons]
    exact (show Declaration.formula p ⊆ Declaration.formula p.ex by
      rw [Declaration.formula_ex]
      exact Set.subset_union_right).trans (ih p.ex)

/-- The written graph keeps every primitive reference of the original term. -/
theorem termReferences_subset_graphAt {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : Term P.signature Γ s) :
    ∀ {Δ : List P.signature.SortType} (ρ : Renaming Γ Δ) (y : Var Δ s),
      termReferences t ⊆ Declaration.formula (t.graphAt ρ y) := by
  induction t with
  | var i =>
    intro Δ ρ y
    rw [termReferences_var]
    exact Set.empty_subset _
  | app op args ih =>
    intro Δ ρ y d hd
    rw [Term.graphAt_app]
    apply formula_existsMany_subset
    rw [Declaration.formula_conj, Declaration.formula_atom, Declaration.atomic_graph]
    rw [termReferences_app] at hd
    rcases hd with hd | ⟨s, i, hd⟩
    · exact Or.inr hd
    · exact Or.inl (formula_conjoin_subset _ i (ih i _ _ hd))
  | letBind x t hx ht =>
    intro Δ ρ y d hd
    rw [Term.graphAt_letBind, Declaration.formula_ex, Declaration.formula_conj]
    rw [termReferences_letBind] at hd
    rcases hd with hd | hd | hd
    · exact Or.inl hd
    · exact Or.inr (Or.inl (hx _ _ hd))
    · exact Or.inr (Or.inr (ht _ _ hd))

/-- Each term reference can be read directly from its written value graph. -/
theorem termReferences_subset_graph {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : Term P.signature Γ s) : termReferences t ⊆ Declaration.formula t.graph := by
  rw [Term.graph_eq_graphAt]
  exact termReferences_subset_graphAt t _ _

open Term (reindexedApp reindexedApp_rfl)

/-- Select the operations and variable positions of a supported term. -/
def selectTerm : {Γ : List P.signature.SortType} → {s : P.signature.SortType} →
    (t : Term P.signature Γ s) → (keepΓ : Declaration.sorts Γ ⊆ U.declarations) →
    (keepS : Declaration.sort s ∈ U.declarations) → termReferences t ⊆ U.declarations →
    Term (signature U) (context Γ keepΓ) ⟨s, keepS⟩
  | _, _, .var i, keepΓ, _, _ => .var (selectVar keepΓ i)
  | _, _, .app op args, keepΓ, keepS, keep => by
    have support := (termReferences_app op args).ge.trans keep
    have keepOp := support (Or.inl (Set.mem_singleton (Declaration.ofOperation op)))
    refine reindexedApp (operation op keepOp) (operation_arity op keepOp) (fun {s} j => ?_)
    let i := ambientVar (operationInputs op keepOp) j
    have term := selectTerm (args i) keepΓ s.property (fun _ hd => support (Or.inr ⟨_, i, hd⟩))
    exact term
  | _, _, @Term.letBind _ _ a _ x y, keepΓ, keepS, keep =>
    let support := (termReferences_letBind x y).ge.trans keep
    let keepA := support (Or.inl (Set.mem_singleton (Declaration.sort a)))
    .letBind (selectTerm x keepΓ keepA (fun _ hd => support (Or.inr (Or.inl hd))))
      (selectTerm y (Declaration.sorts_cons_subset keepA keepΓ) keepS (fun _ hd => support (Or.inr (Or.inr hd))))


/-- Selecting a variable term keeps the position selected in its context. -/
theorem selectTerm_var {Γ : List P.signature.SortType} {s : P.signature.SortType} (i : Var Γ s)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepS : Declaration.sort s ∈ U.declarations)
    (keep : termReferences (Term.var (sig := P.signature) i) ⊆ U.declarations) :
    selectTerm (.var i) keepΓ keepS keep = .var (selectVar keepΓ i) :=
  rfl

/-- Selecting an application selects its operation and all of its arguments in order. -/
theorem selectTerm_app {Γ : List P.signature.SortType} (op : Operation P.signature)
    (args : ∀ {s}, Var op.arity.inputs s → Term P.signature Γ s)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations)
    (keepS : Declaration.sort op.arity.output ∈ U.declarations)
    (keep : termReferences (Term.app op args) ⊆ U.declarations) :
    selectTerm (.app op args) keepΓ keepS keep =
      let support := (termReferences_app op args).ge.trans keep
      let keepOp := support (Or.inl (Set.mem_singleton (Declaration.ofOperation op)))
      reindexedApp (operation op keepOp) (operation_arity op keepOp) (fun {s} j =>
        let i := ambientVar (operationInputs op keepOp) j
        selectTerm (args i) keepΓ s.property (fun _ hd => support (Or.inr ⟨_, i, hd⟩))) :=
  rfl

/-- Selecting a binding selects its initializer and extends the context for its body. -/
theorem selectTerm_letBind {Γ : List P.signature.SortType} {a s : P.signature.SortType}
    (init : Term P.signature Γ a) (body : Term P.signature (a :: Γ) s)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepS : Declaration.sort s ∈ U.declarations)
    (keep : termReferences (init.letBind body) ⊆ U.declarations) :
    selectTerm (init.letBind body) keepΓ keepS keep =
      let support := (termReferences_letBind init body).ge.trans keep
      let keepA := support (Or.inl (Set.mem_singleton (Declaration.sort a)))
      .letBind (selectTerm init keepΓ keepA (fun _ hd => support (Or.inr (Or.inl hd))))
        (selectTerm body (Declaration.sorts_cons_subset keepA keepΓ) keepS
          (fun _ hd => support (Or.inr (Or.inr hd)))) :=
  rfl

/-- Select the body of a binding on the explicit cons context of its selected initializer. -/
theorem selectTerm_letBind_cast {Γ : List P.signature.SortType} {a s : P.signature.SortType}
    (init : Term P.signature Γ a) (body : Term P.signature (a :: Γ) s)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepS : Declaration.sort s ∈ U.declarations)
    (keep : termReferences (init.letBind body) ⊆ U.declarations) :
    selectTerm (init.letBind body) keepΓ keepS keep =
      let support := (termReferences_letBind init body).ge.trans keep
      let keepA := support (Or.inl (Set.mem_singleton (Declaration.sort a)))
      let keepBody := Declaration.sorts_cons_subset keepA keepΓ
      .letBind (selectTerm init keepΓ keepA (fun _ hd => support (Or.inr (Or.inl hd))))
        (cast (congrArg (fun ctx => Term (signature U) ctx ⟨s, keepS⟩) (context_cons a Γ keepBody))
          (selectTerm body keepBody keepS (fun _ hd => support (Or.inr (Or.inr hd))))) :=
  selectTerm_letBind init body keepΓ keepS keep

/-- Selection respects equality of the original terms, independently of how support was shown. -/
theorem selectTerm_congr {Γ : List P.signature.SortType} {s : P.signature.SortType}
    {left right : Term P.signature Γ s} (same : left = right)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepS : Declaration.sort s ∈ U.declarations)
    (keptLeft : termReferences left ⊆ U.declarations) (keptRight : termReferences right ⊆ U.declarations) :
    selectTerm left keepΓ keepS keptLeft = selectTerm right keepΓ keepS keptRight := by
  subst right
  rfl

/-- An application of a typed total symbol refers to its primitive and all its argument terms. -/
theorem typedTermReferences {Γ : List P.signature.SortType} {profile : Arity P.signature.SortType}
    (f : TypedTotal P.signature profile) (args : ∀ {s}, Var profile.inputs s → Term P.signature Γ s) :
    termReferences (f.term args) =
      {Declaration.ofOperation f.symbol.operation} ∪
        {d | ∃ (s : P.signature.SortType) (i : Var profile.inputs s), d ∈ termReferences (args i)} := by
  rcases f with ⟨symbol, same⟩
  cases same
  rw [TypedTotal.term_eq_reindexedApp, reindexedApp_rfl, termReferences_app]

/-- Selection commutes with applying a typed total symbol to supported terms. -/
theorem selectTypedTotal_term {Γ : List P.signature.SortType} {profile : Arity P.signature.SortType}
    (f : TypedTotal P.signature profile) (args : ∀ {s}, Var profile.inputs s → Term P.signature Γ s)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations)
    (inputs : Declaration.sorts profile.inputs ⊆ U.declarations)
    (output : Declaration.sort profile.output ∈ U.declarations)
    (ht : termReferences (f.term args) ⊆ U.declarations)
    (ha : ∀ {s} (i : Var profile.inputs s), termReferences (args i) ⊆ U.declarations) :
    selectTerm (f.term args) hΓ output ht = (selectTypedTotal f keep inputs output).term
      (fun {s} i => selectTerm (args (ambientVar inputs i)) hΓ s.property (ha _)) := by
  rcases f with ⟨symbol, same⟩
  cases same
  let original : TypedTotal P.signature symbol.operation.arity := ⟨symbol, rfl⟩
  have originalApp : original.term args = .app symbol.operation args :=
    (TypedTotal.term_eq_reindexedApp original args).trans (reindexedApp_rfl symbol.operation args)
  have keptApp : termReferences (.app symbol.operation args) ⊆ U.declarations := originalApp ▸ ht
  refine (selectTerm_congr originalApp hΓ output ht keptApp).trans ?_
  rw [selectTerm_app, TypedTotal.term_eq_reindexedApp]
  exact Term.reindexedApp_congr (selectTypedTotal_operation original keep inputs output).symm _ _ _

/-- Retain the sort names of both parts of a concatenated context. -/
private theorem appendSupport {Γ Δ : List P.signature.SortType}
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations) :
    Declaration.sorts (Γ ++ Δ) ⊆ U.declarations := by
  simp only [Declaration.sorts_eq_image] at hΓ hΔ ⊢
  rintro _ ⟨s, hs, rfl⟩
  exact (List.mem_append.mp hs).elim (fun left => hΓ ⟨s, left, rfl⟩) (fun right => hΔ ⟨s, right, rfl⟩)

/-- The selected context of the concatenation identifies with the concatenation of the selected parts. -/
private theorem context_append {Γ Δ : List P.signature.SortType}
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations) :
    context (Γ ++ Δ) (appendSupport hΓ hΔ) = context Γ hΓ ++ context Δ hΔ := by
  induction Γ with
  | nil =>
    simp only [List.nil_append, context_nil]
  | cons s Γ ih =>
    simp only [List.cons_append, context_cons]
    exact congrArg (List.cons _) (ih ((tailSortsSubset s Γ).trans hΓ))

/-- Transport the first variable when the remainder of its context is reindexed. -/
private theorem cast_var_here {S : Type u} {Γ Δ : List S} {s : S} (h : Γ = Δ) :
    cast (congrArg (fun Λ => Var Λ s) (congrArg (List.cons s) h)) Var.here = Var.here := by
  cases h
  rfl

/-- Transport a variable past the first position when its tail context is reindexed. -/
private theorem cast_var_there {S : Type u} {Γ Δ : List S} {s t : S} (h : Γ = Δ) (i : Var Γ s) :
    cast (congrArg (fun Λ => Var Λ s) (congrArg (List.cons t) h)) (.there i) =
      .there (cast (congrArg (fun Λ => Var Λ s) h) i) := by
  cases h
  rfl

/-- Reindex a shifted variable when the prefix is given by an equal list. -/
private theorem shift_context_congr {S : Type u} {Γ Λ Ξ : List S} {s : S}
    (same : Λ = Ξ) (i : Var Γ s) :
    cast (congrArg (fun ctx => Var (ctx ++ Γ) s) same) (i.shift Λ) = i.shift Ξ := by
  cases same
  rfl

/-- Selecting a variable commutes with shifting it past the retained prefix. -/
private theorem selectVar_shift {Γ Δ : List P.signature.SortType}
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    {s : P.signature.SortType} (i : Var Δ s) :
    cast (congrArg (fun Λ => Var Λ ⟨s, varKept hΔ i⟩) (context_append hΓ hΔ))
      (selectVar (appendSupport hΓ hΔ) (i.shift Γ)) = (selectVar hΔ i).shift (context Γ hΓ) := by
  induction Γ with
  | nil =>
    have left : i.shift [] = i :=
      congrArg (fun f : Renaming Δ Δ => f i) Var.shift_nil
    have right : (selectVar hΔ i).shift [] = selectVar hΔ i :=
      congrArg (fun f : Renaming (context Δ hΔ) (context Δ hΔ) => f (selectVar hΔ i)) Var.shift_nil
    let step := congrArg (fun ctx => Var (ctx ++ context Δ hΔ) ⟨s, varKept hΔ i⟩) (context_nil hΓ)
    apply (cast_inj step).1
    rw [cast_cast, shift_context_congr (context_nil hΓ), right]
    rw [left]
    rfl
  | cons t Γ ih =>
    let keepΓ := (tailSortsSubset t Γ).trans hΓ
    let selected : SortName U := ⟨t, hΓ (Declaration.sort_mem_sorts List.mem_cons_self)⟩
    let name : SortName U := ⟨s, varKept hΔ i⟩
    let step := congrArg (fun ctx => Var (ctx ++ context Δ hΔ) name) (context_cons t Γ hΓ)
    apply (cast_inj step).1
    rw [cast_cast, shift_context_congr (context_cons t Γ hΓ),
      Var.shift_cons (t := selected), Var.shift_cons]
    let head := congrArg (fun ctx => Var ctx name) (context_cons t (Γ ++ Δ) (appendSupport hΓ hΔ))
    let rest := congrArg (fun ctx => Var ctx name) (congrArg (List.cons selected) (context_append keepΓ hΔ))
    rw [show cast _ (selectVar _ (Var.there (i.shift Γ))) =
        cast rest (cast head (selectVar (appendSupport hΓ hΔ) (Var.there (t := t) (i.shift Γ)))) from
      (cast_cast head rest _).symm]
    rw [selectVar_cast_there]
    exact (cast_var_there (context_append keepΓ hΔ) _).trans (congrArg Var.there (ih keepΓ))

/-- Reindex the leading variable before or after appending the same tail context. -/
private theorem inLeft_context_congr {S : Type u} {Γ Γ' : List S} {s : S}
    (same : Γ = Γ') (i : Var Γ s) (Δ : List S) :
    cast (congrArg (fun ctx => Var (ctx ++ Δ) s) same) (i.inLeft Δ) =
      (cast (congrArg (fun ctx => Var ctx s) same) i).inLeft Δ := by
  cases same
  rfl

/-- The selected inclusion of the left block keeps the same variable position. -/
private theorem selectVar_inLeft {Γ Δ : List P.signature.SortType}
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    {s : P.signature.SortType} (i : Var Γ s) :
    cast (congrArg (fun Λ => Var Λ ⟨s, varKept hΓ i⟩) (context_append hΓ hΔ))
      (selectVar (appendSupport hΓ hΔ) (i.inLeft Δ)) = (selectVar hΓ i).inLeft (context Δ hΔ) := by
  induction i with
  | @here Γ t =>
    let name : SortName U := ⟨t, varKept hΓ .here⟩
    let alignment := context_cons t Γ hΓ
    let step := congrArg (fun ctx => Var (ctx ++ context Δ hΔ) name) alignment
    apply (cast_inj step).1
    rw [cast_cast, inLeft_context_congr alignment, selectVar_cast_here, Var.inLeft_here, Var.inLeft_here]
    let head := congrArg (fun ctx => Var ctx name) (context_cons t (Γ ++ Δ) (appendSupport hΓ hΔ))
    let rest := congrArg (fun ctx => Var ctx name)
      (congrArg (List.cons name) (context_append ((tailSortsSubset t Γ).trans hΓ) hΔ))
    rw [show cast _ (selectVar _ Var.here) = cast rest (cast head (selectVar (appendSupport hΓ hΔ) Var.here)) from
      (cast_cast head rest _).symm]
    rw [selectVar_cast_here]
    exact cast_var_here (context_append ((tailSortsSubset t Γ).trans hΓ) hΔ)
  | @there Γ s t i ih =>
    let keepΓ := (tailSortsSubset t Γ).trans hΓ
    let name : SortName U := ⟨s, varKept hΓ (.there i)⟩
    let first : SortName U := ⟨t, hΓ (Declaration.sort_mem_sorts List.mem_cons_self)⟩
    let alignment := context_cons t Γ hΓ
    let step := congrArg (fun ctx => Var (ctx ++ context Δ hΔ) name) alignment
    apply (cast_inj step).1
    rw [cast_cast, inLeft_context_congr alignment, selectVar_cast_there, Var.inLeft_there, Var.inLeft_there]
    let head := congrArg (fun ctx => Var ctx name) (context_cons t (Γ ++ Δ) (appendSupport hΓ hΔ))
    let rest := congrArg (fun ctx => Var ctx name) (congrArg (List.cons first) (context_append keepΓ hΔ))
    rw [show cast _ (selectVar _ (Var.there (i.inLeft Δ))) =
      cast rest (cast head (selectVar (appendSupport hΓ hΔ) (Var.there (t := t) (i.inLeft Δ)))) from
      (cast_cast head rest _).symm]
    rw [selectVar_cast_there]
    exact (cast_var_there (context_append keepΓ hΔ) _).trans (congrArg Var.there (ih keepΓ))

/-- Retaining the existential closure provides the hidden context and the body's support. -/
private theorem keepExistsMany {Γ Λ : List P.signature.SortType}
    (p : Formula P.signature (Λ ++ Γ)) (kept : Declaration.formulaSupport (Formula.existsMany Λ p) ⊆ U.declarations) :
    Declaration.formulaSupport p ⊆ U.declarations := by
  induction Λ with
  | nil =>
    rw [Formula.existsMany_nil] at kept
    exact kept
  | cons s Λ ih =>
    rw [Formula.existsMany_cons] at kept
    exact existsSupport (ih p.ex kept)

/-- Transporting the context of an existential also transports the context of its body. -/
private theorem cast_formula_ex {sig : Signature.{u}} {Γ Δ : List sig.SortType} {s : sig.SortType}
    (h : Γ = Δ) (p : Formula sig (s :: Γ)) :
    cast (congrArg (Formula sig) h) p.ex =
      (cast (congrArg (Formula sig) (congrArg (List.cons s) h)) p).ex := by
  cases h
  rfl

/-- Reindex a quantified prefix and its bound body together. -/
private theorem existsMany_context_congr {sig : Signature.{u}} {Γ Λ Ξ : List sig.SortType}
    (same : Λ = Ξ) (body : Formula sig (Λ ++ Γ)) :
    Formula.existsMany Λ body =
      Formula.existsMany Ξ (cast (congrArg (fun ctx => Formula sig (ctx ++ Γ)) same) body) := by
  cases same
  rfl

/-- Select the body over both retained contexts before closing the quantified prefix. -/
private theorem selectFormula_existsMany {Γ Λ : List P.signature.SortType}
    (p : Formula P.signature (Λ ++ Γ)) (kept : Declaration.formulaSupport (Formula.existsMany Λ p) ⊆ U.declarations)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΛ : Declaration.sorts Λ ⊆ U.declarations) :
    selectFormula (Formula.existsMany Λ p) kept =
      Formula.existsMany (context Λ hΛ)
        (cast (congrArg (Formula (signature U)) (context_append hΛ hΓ))
          (selectFormula p (keepExistsMany p kept))) := by
  induction Λ with
  | nil =>
    simp only [Formula.existsMany_nil] at kept ⊢
    conv_rhs => rw [existsMany_context_congr (context_nil hΛ), Formula.existsMany_nil, cast_cast]
    rfl
  | cons s Λ ih =>
    let tail := (tailSortsSubset s Λ).trans hΛ
    have rewritten : Declaration.formulaSupport (Formula.existsMany Λ p.ex) ⊆ U.declarations := by
      rw [← Formula.existsMany_cons]
      exact kept
    simp only [Formula.existsMany_cons]
    refine (ih p.ex rewritten tail).trans ?_
    erw [selectFormula_ex_cast]
    conv_rhs => rw [existsMany_context_congr (context_cons s Λ hΛ), Formula.existsMany_cons]
    rw [cast_formula_ex (context_append tail hΓ)]
    simp only [cast_cast]

/-- The full finite conjunction retains the support needed for each of its conjuncts. -/
private theorem keepConjoin {Γ Λ : List P.signature.SortType} (ps : ∀ {s}, Var Λ s → Formula P.signature Γ)
    (keep : Declaration.formulaSupport (Formula.conjoin Λ ps) ⊆ U.declarations) {s} (i : Var Λ s) :
    Declaration.formulaSupport (ps i) ⊆ U.declarations := by
  simp only [Declaration.formulaSupport_eq] at keep ⊢
  exact Set.union_subset (Set.subset_union_left.trans keep)
    ((formula_conjoin_subset ps i).trans (Set.subset_union_right.trans keep))

/-- Equal formulas select to equal formulas regardless of their support proofs. -/
private theorem selectFormula_congr {Γ : List P.signature.SortType} {p q : Formula P.signature Γ}
    (same : p = q) {hp : Declaration.formulaSupport p ⊆ U.declarations}
    {hq : Declaration.formulaSupport q ⊆ U.declarations} : selectFormula p hp = selectFormula q hq := by
  subst q
  rfl

/-- Reindex the variables that enumerate a finite conjunction's conjuncts. -/
private theorem conjoin_context_congr {sig : Signature.{u}} {Γ Λ Ξ : List sig.SortType}
    (same : Λ = Ξ) (ps : ∀ {s}, Var Λ s → Formula sig Γ) :
    Formula.conjoin Λ ps = Formula.conjoin Ξ
      (fun {s} i => ps (cast (congrArg (fun ctx => Var ctx s) same.symm) i)) := by
  cases same
  rfl

/-- Select every formula of a finite conjunction and combine them in the selected signature. -/
private theorem selectFormula_conjoin {Γ Λ : List P.signature.SortType} (ps : ∀ {s}, Var Λ s → Formula P.signature Γ)
    (keep : Declaration.formulaSupport (Formula.conjoin Λ ps) ⊆ U.declarations)
    (hΛ : Declaration.sorts Λ ⊆ U.declarations) :
    selectFormula (Formula.conjoin Λ ps) keep =
      Formula.conjoin (context Λ hΛ) (fun i =>
        selectFormula (ps (ambientVar hΛ i)) (keepConjoin ps keep (ambientVar hΛ i))) := by
  induction Λ with
  | nil =>
    have written := Formula.conjoin_nil ps
    have supported : Declaration.formulaSupport (Formula.truth (sig := P.signature) (Γ := Γ)) ⊆
        U.declarations := by
      rw [← written]
      exact keep
    refine (selectFormula_congr written (hq := supported)).trans ?_
    rw [selectFormula_truth]
    conv_rhs => rw [conjoin_context_congr (context_nil hΛ), Formula.conjoin_nil]
  | cons s Λ ih =>
    let tail := (tailSortsSubset s Λ).trans hΛ
    have written := Formula.conjoin_cons ps
    have rewritten : Declaration.formulaSupport ((ps .here).conj (Formula.conjoin Λ (fun i => ps (.there i)))) ⊆ U.declarations := by
      rw [← written]
      exact keep
    refine (selectFormula_congr written (hq := rewritten)).trans ?_
    rw [selectFormula_conj]
    refine (congrArg (Formula.conj _) (ih (fun i => ps (.there i)) ((Declaration.binarySupport_right (Declaration.formula_conj _ _)).trans rewritten) tail)).trans ?_
    conv_rhs => rw [conjoin_context_congr (context_cons s Λ hΛ), Formula.conjoin_cons]
    apply congrArg₂ Formula.conj
    · exact selectFormula_congr (congrArg (fun i : Var (s :: Λ) s => ps i) (ambientVar_cast_here hΛ).symm)
    · apply congrArg (Formula.conjoin (sig := signature U) (context Λ tail))
      funext t i
      exact selectFormula_congr (congrArg (fun j : Var (s :: Λ) t.val => ps j) (ambientVar_cast_there hΛ i).symm)

/-- Transport all conjuncts to the same reindexed context. -/
private theorem cast_formula_conjoin {sig : Signature.{u}} {Γ Δ Λ : List sig.SortType}
    (h : Γ = Δ) (ps : ∀ {s}, Var Λ s → Formula sig Γ) :
    cast (congrArg (Formula sig) h) (Formula.conjoin Λ ps) =
      Formula.conjoin Λ (fun i => cast (congrArg (Formula sig) h) (ps i)) := by
  cases h
  rfl

/-- Form the graph atom from variables indexed by an equal presentation of the operation's arity.

Implementation notes: transport along the arity equality keeps the argument
and result positions typed by the operation used in the graph. -/
private def reindexedGraph {sig : Signature.{u}} {Γ : List sig.SortType} (op : Operation sig)
    {a : Arity sig.SortType} (same : op.arity = a) (ρ : Renaming a.inputs Γ) (y : Var Γ a.output) :
    Atomic sig Γ :=
  .graph op (fun {s} i => ρ (cast (congrArg (fun arity => Var arity.inputs s) same) i))
    (cast (congrArg (Var Γ) (congrArg Arity.output same.symm)) y)

/-- Renaming the operation along equality does not change its graph at the common arity. -/
private theorem reindexedGraph_congr {sig : Signature.{u}} {Γ : List sig.SortType} {op op' : Operation sig}
    (equal : op = op') {a : Arity sig.SortType} (shape : op.arity = a) (shape' : op'.arity = a)
    (ρ : Renaming a.inputs Γ) (y : Var Γ a.output) :
    reindexedGraph op shape ρ y = reindexedGraph op' shape' ρ y := by
  subst op'
  rfl

/-- The selected graph atom uses the same named input and output positions as its reindexed form. -/
private theorem selectGraph_reindexed {Γ : List P.signature.SortType} (op : Operation P.signature)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hOp : Declaration.ofOperation op ∈ U.declarations)
    (ρ : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output) :
    selectGraph hΓ op hOp ρ y = reindexedGraph (operation op hOp) (operation_arity op hOp)
      (selectRenaming (operationInputs op hOp) hΓ ρ) (selectVar hΓ y) := by
  cases op with
  | total f =>
    refine (selectGraph_total hΓ f hOp ρ y).trans ?_
    have same := operation_total f hOp
    exact (reindexedGraph_congr same (operation_arity (.total f) hOp) (operation_arity_of_eq same) _ _).symm
  | partialOp p =>
    refine (selectGraph_partialOp hΓ p hOp ρ y).trans ?_
    have same := operation_partialOp p hOp
    exact (reindexedGraph_congr same (operation_arity (.partialOp p) hOp) (operation_arity_of_eq same) _ _).symm
  | quantity q =>
    refine (selectGraph_quantity hΓ q hOp ρ y).trans ?_
    have same := operation_quantity q hOp
    exact (reindexedGraph_congr same (operation_arity (.quantity q) hOp) (operation_arity_of_eq same) _ _).symm

/-- Expand the value graph of an application whose arguments are indexed by an equal arity. -/
private theorem graphAt_reindexedApp {sig : Signature.{u}} {Γ Δ : List sig.SortType}
    (op : Operation sig) {a : Arity sig.SortType} (same : op.arity = a)
    (args : ∀ {s}, Var a.inputs s → Term sig Γ s) (ρ : Renaming Γ Δ) (y : Var Δ a.output) :
    (reindexedApp op same args).graphAt ρ y = Formula.existsMany a.inputs
      ((Formula.conjoin a.inputs fun i =>
        (args i).graphAt (fun j => (ρ j).shift a.inputs) (i.inLeft Δ)).conj
        (.atom (reindexedGraph op same (Var.inLeft Δ) (y.shift a.inputs)))) := by
  cases same
  simpa only [reindexedApp_rfl, reindexedGraph] using Term.graphAt_app op args ρ y

/-- Relate a term's value graph before and after transport of its free context. -/
private theorem cast_graphAt {sig : Signature.{u}} {Γ Δ Ξ : List sig.SortType} {s : sig.SortType}
    (h : Δ = Ξ) (t : Term sig Γ s) (ρ : Renaming Γ Δ) (y : Var Δ s) :
    cast (congrArg (Formula sig) h) (t.graphAt ρ y) =
      t.graphAt (fun i => cast (congrArg (fun Δ => Var Δ _) h) (ρ i))
        (cast (congrArg (Var · s) h) y) := by
  cases h
  rfl

/-- Transport the variable context of a reindexed graph atom while retaining its operation. -/
private theorem cast_reindexedGraph {sig : Signature.{u}} {Γ Δ : List sig.SortType}
    (h : Γ = Δ) (op : Operation sig) {a : Arity sig.SortType} (same : op.arity = a)
    (ρ : Renaming a.inputs Γ) (y : Var Γ a.output) :
    cast (congrArg (Formula sig) h) (.atom (reindexedGraph op same ρ y)) =
      .atom (reindexedGraph op same (fun i => cast (congrArg (fun Δ => Var Δ _) h) (ρ i))
        (cast (congrArg (fun Δ => Var Δ a.output) h) y)) := by
  cases h
  rfl

/-- Insert the selected prefix before the older variable positions. -/
private theorem shiftedRenaming {Γ Δ Λ : List P.signature.SortType}
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    (hΛ : Declaration.sorts Λ ⊆ U.declarations) (ρ : Renaming Γ Δ) :
    (fun {s} (i : Var (context Γ hΓ) s) =>
      cast (congrArg (fun Ξ => Var Ξ s) (context_append hΛ hΔ))
        (selectRenaming hΓ (appendSupport hΛ hΔ) (fun j => (ρ j).shift Λ) i)) =
      (fun {s} (i : Var (context Γ hΓ) s) => (selectRenaming hΓ hΔ ρ i).shift (context Λ hΛ)) := by
  funext s i
  simp only [selectRenaming_apply]
  exact selectVar_shift hΛ hΔ (ρ (ambientVar hΓ i))

/-- Keep positions of the selected left context in the selected concatenation. -/
private theorem inLeftRenaming {Δ Λ : List P.signature.SortType}
    (hΔ : Declaration.sorts Δ ⊆ U.declarations) (hΛ : Declaration.sorts Λ ⊆ U.declarations) :
    (fun {s} (i : Var (context Λ hΛ) s) =>
      cast (congrArg (fun Ξ => Var Ξ s) (context_append hΛ hΔ))
        (selectRenaming hΛ (appendSupport hΛ hΔ) (Var.inLeft Δ) i)) =
      (fun {s} (i : Var (context Λ hΛ) s) => i.inLeft (context Δ hΔ)) := by
  funext s i
  rw [selectRenaming_apply]
  exact (selectVar_inLeft hΛ hΔ (ambientVar hΛ i)).trans
    (congrArg (Var.inLeft (context Δ hΔ)) (selectVar_ambientVar hΛ i))


/-- Selection of terms commutes with writing their value graphs at any variable positions. -/
theorem selectFormula_graphAt {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : Term P.signature Γ s) :
    ∀ {Δ : List P.signature.SortType} (ρ : Renaming Γ Δ) (y : Var Δ s)
      (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
      (hTerm : termReferences t ⊆ U.declarations)
      (hGraph : Declaration.formulaSupport (t.graphAt ρ y) ⊆ U.declarations),
      selectFormula (t.graphAt ρ y) hGraph =
        (selectTerm t hΓ (varKept hΔ y) hTerm).graphAt (selectRenaming hΓ hΔ ρ) (selectVar hΔ y) := by
  induction t with
  | var i =>
    intro Δ ρ y hΓ hΔ hTerm hGraph
    have support : Declaration.formulaSupport (Formula.atom (.eq (ρ i) y)) ⊆ U.declarations := by
      simpa only [← Term.graphAt_var i ρ y] using hGraph
    refine (selectFormula_congr (Term.graphAt_var i ρ y) (hq := support)).trans ?_
    rw [selectFormula_atom, selectAtomic_eq]
    rw [selectTerm_var]
    refine Eq.trans ?_ (Term.graphAt_var (sig := signature U) (selectVar hΓ i)
      (selectRenaming hΓ hΔ ρ) (selectVar hΔ y)).symm
    exact congrArg (fun (v : Var (context Δ hΔ) _) => Formula.atom (sig := signature U) (.eq v (selectVar hΔ y)))
      (renaming_selectVar hΓ hΔ ρ i).symm
  | @app Γ op ts ih =>
    intro Δ ρ y hΓ hΔ hTerm hGraph
    rw [termReferences_app] at hTerm
    let hOp : Declaration.ofOperation op ∈ U.declarations := hTerm (Or.inl (Set.mem_singleton _))
    let hΛ := operationInputs op hOp
    let fs : ∀ {s}, Var op.arity.inputs s → Formula P.signature (op.arity.inputs ++ Δ) :=
      fun i => (ts i).graphAt (fun j => (ρ j).shift op.arity.inputs) (i.inLeft Δ)
    let p : Formula P.signature (op.arity.inputs ++ Δ) :=
      .atom (.graph op (Var.inLeft Δ) (y.shift op.arity.inputs))
    let body := (Formula.conjoin op.arity.inputs fs).conj p
    have written : (Term.app op ts).graphAt ρ y = Formula.existsMany op.arity.inputs body :=
      Term.graphAt_app op ts ρ y
    have support : Declaration.formulaSupport (Formula.existsMany op.arity.inputs body) ⊆ U.declarations := by
      rw [← written]
      exact hGraph
    have hBody := keepExistsMany body support
    let writtenBody := Declaration.formula_conj (P := P) (Formula.conjoin op.arity.inputs fs) p
    let hArgs := (Declaration.binarySupport_left writtenBody).trans hBody
    let hAtom := (Declaration.binarySupport_right writtenBody).trans hBody
    let hAppend := appendSupport hΛ hΔ
    let crossing := context_append hΛ hΔ
    let lowerArgs : ∀ {s}, Var (context op.arity.inputs hΛ) s → Term (signature U) (context Γ hΓ) s :=
      fun {s} i => selectTerm (ts (ambientVar hΛ i)) hΓ s.property (fun _ hd => hTerm (Or.inr ⟨_, _, hd⟩))
    refine (selectFormula_congr written (hq := support)).trans ?_
    rw [selectTerm_app]
    change _ = (reindexedApp (operation op hOp) (operation_arity op hOp) lowerArgs).graphAt
        (selectRenaming hΓ hΔ ρ) (selectVar hΔ y)
    rw [selectFormula_existsMany body support hΔ hΛ, graphAt_reindexedApp]
    erw [selectFormula_conj]
    change Formula.existsMany (context op.arity.inputs hΛ)
        (cast (congrArg (Formula (signature U)) crossing)
          ((selectFormula (Formula.conjoin op.arity.inputs fs) hArgs).conj (selectFormula p hAtom))) = _
    rw [Formula.cast_conj_context crossing, selectFormula_conjoin fs hArgs hΛ, cast_formula_conjoin crossing]
    apply congrArg (Formula.existsMany (sig := signature U) (context op.arity.inputs hΛ))
    apply congrArg₂ (Formula.conj (sig := signature U))
    · apply congrArg (Formula.conjoin (sig := signature U) (context op.arity.inputs hΛ))
      funext s i
      let j := ambientVar hΛ i
      have h := ih j (fun j => (ρ j).shift op.arity.inputs) (j.inLeft Δ)
        hΓ hAppend (fun _ hd => hTerm (Or.inr ⟨_, _, hd⟩)) (keepConjoin fs hArgs j)
      change cast (congrArg (Formula (signature U)) crossing)
        (selectFormula (fs j) (keepConjoin fs hArgs j)) = _
      refine (congrArg (cast (congrArg (Formula (signature U)) crossing)) h).trans ?_
      refine (cast_graphAt crossing (lowerArgs i) _ _).trans ?_
      exact congrArg₂ (fun (mapVars : Renaming (context Γ hΓ) (context op.arity.inputs hΛ ++ context Δ hΔ))
        (out : Var (context op.arity.inputs hΛ ++ context Δ hΔ) s) => (lowerArgs i).graphAt mapVars out)
        (shiftedRenaming hΓ hΔ hΛ ρ) ((selectVar_inLeft hΛ hΔ j).trans
          (congrArg (Var.inLeft (context Δ hΔ)) (selectVar_ambientVar hΛ i)))
    · erw [selectFormula_atom, selectAtomic_graph]
      change cast (congrArg (Formula (signature U)) crossing)
        (.atom (selectGraph hAppend op hOp (Var.inLeft Δ) (y.shift op.arity.inputs))) = _
      rw [selectGraph_reindexed]
      refine (cast_reindexedGraph crossing (operation op hOp) (operation_arity op hOp) _ _).trans ?_
      exact congrArg₂ (fun (mapVars : Renaming (context op.arity.inputs hΛ)
          (context op.arity.inputs hΛ ++ context Δ hΔ)) (out : Var (context op.arity.inputs hΛ ++ context Δ hΔ) _) =>
            Formula.atom (reindexedGraph (operation op hOp) (operation_arity op hOp) mapVars out))
        (inLeftRenaming hΔ hΛ) (selectVar_shift hΛ hΔ y)
  | @letBind Γ a s init body hi hb =>
    intro Δ ρ y hΓ hΔ hTerm hGraph
    rw [termReferences_letBind] at hTerm
    have written := Term.graphAt_letBind init body ρ y
    have support : Declaration.formulaSupport
        (((init.graphAt (fun i => .there (ρ i)) .here).conj (body.graphAt ρ.lift (.there y))).ex) ⊆
        U.declarations := by simpa only [← written] using hGraph
    refine (selectFormula_congr written (hq := support)).trans ?_
    rw [selectFormula_ex_cast, selectFormula_conj, selectTerm_letBind_cast]
    let hA : Declaration.sort a ∈ U.declarations := hTerm (Or.inl (Set.mem_singleton _))
    let hΓ' := Declaration.sorts_cons_subset hA hΓ
    let hΔ' := Declaration.sorts_cons_subset hA hΔ
    let sourceCtx := context_cons a Γ hΓ'
    let targetCtx := context_cons a Δ hΔ'
    let head : SortName U := ⟨a, hA⟩
    let retainedInit := selectTerm init hΓ hA (fun _ hd => hTerm (Or.inr (Or.inl hd)))
    let retainedBody := cast (congrArg (fun ctx => Term (signature U) ctx ⟨s, varKept hΔ y⟩) sourceCtx)
      (selectTerm body hΓ' (varKept hΔ y) (fun _ hd => hTerm (Or.inr (Or.inr hd))))
    refine Eq.trans ?_ (Term.graphAt_letBind retainedInit retainedBody
      (selectRenaming hΓ hΔ ρ) (selectVar hΔ y)).symm
    let hBody := existsSupport support
    let writtenBody := Declaration.formula_conj (P := P)
      (init.graphAt (fun i => .there (ρ i)) .here) (body.graphAt ρ.lift (.there y))
    have left := hi (fun i => .there (ρ i)) .here hΓ hΔ'
      (fun _ hd => hTerm (Or.inr (Or.inl hd))) ((Declaration.binarySupport_left writtenBody).trans hBody)
    have right := hb ρ.lift (.there y) hΓ' hΔ'
      (fun _ hd => hTerm (Or.inr (Or.inr hd))) ((Declaration.binarySupport_right writtenBody).trans hBody)
    rw [Formula.cast_conj_context targetCtx]
    refine congrArg (Formula.ex (sig := signature U)) (congrArg₂ Formula.conj ?_ ?_)
    · have moved := congrArg (cast (congrArg (Formula (signature U)) targetCtx)) left
      rw [Term.graphAt_cast_context rfl targetCtx] at moved
      exact moved.trans (congrArg₂ (fun (mapVars : Renaming (context Γ hΓ) (head :: context Δ hΔ))
        (out : Var (head :: context Δ hΔ) head) => retainedInit.graphAt mapVars out)
        (selectRenaming_there_cast hA hΓ hΔ ρ) (selectVar_cast_here hΔ'))
    · have moved := congrArg (cast (congrArg (Formula (signature U)) targetCtx)) right
      rw [Term.graphAt_cast_context sourceCtx targetCtx] at moved
      exact moved.trans (congrArg₂ (fun (mapVars : Renaming (head :: context Γ hΓ) (head :: context Δ hΔ))
        (out : Var (head :: context Δ hΔ) ⟨s, varKept hΔ y⟩) => retainedBody.graphAt mapVars out)
        (selectRenaming_lift_cast hA hΓ hΔ ρ) (selectVar_cast_there hΔ' y))

/-- Selecting a term's value graph agrees with taking the graph of the selected term. -/
private theorem selectFormula_graph {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : Term P.signature Γ s) (hΓ : Declaration.sorts Γ ⊆ U.declarations)
    (hs : Declaration.sort s ∈ U.declarations) (ht : termReferences t ⊆ U.declarations)
    (hg : Declaration.formulaSupport t.graph ⊆ U.declarations) :
    cast (congrArg (Formula (signature U)) (context_cons s Γ (Declaration.sorts_cons_subset hs hΓ)))
      (selectFormula t.graph hg) = (selectTerm t hΓ hs ht).graph := by
  simp only [Term.graph_eq_graphAt] at hg ⊢
  let hΔ := Declaration.sorts_cons_subset hs hΓ
  let alignment := context_cons s Γ hΔ
  let name : SortName U := ⟨s, hs⟩
  have graph := selectFormula_graphAt t (fun i => .there i) .here hΓ hΔ ht hg
  have moved := congrArg (cast (congrArg (Formula (signature U)) alignment)) graph
  rw [Term.graphAt_cast_context rfl alignment] at moved
  have shifted := selectRenaming_there_cast hs hΓ hΓ (fun i => i)
  simp only [selectRenaming_id] at shifted
  exact moved.trans (congrArg₂ (fun (mapVars : Renaming (context Γ hΓ) (name :: context Γ hΓ))
    (out : Var (name :: context Γ hΓ) name) => (selectTerm t hΓ hs ht).graphAt mapVars out)
    shifted (selectVar_cast_here hΔ))

/-- Selection commutes with the existential definedness formula of a term. -/
theorem selectFormula_defined {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : Term P.signature Γ s) (hΓ : Declaration.sorts Γ ⊆ U.declarations)
    (hs : Declaration.sort s ∈ U.declarations) (ht : termReferences t ⊆ U.declarations)
    (hg : Declaration.formulaSupport t.defined ⊆ U.declarations) :
    selectFormula t.defined hg = (selectTerm t hΓ hs ht).defined := by
  simp only [Term.defined_eq_ex_graph] at hg ⊢
  rw [selectFormula_ex_cast]
  exact congrArg (Formula.ex (sig := signature U)) (selectFormula_graph t hΓ hs ht (existsSupport hg))

/-- Selection commutes with the value-witness expansion of a literal term equality. -/
theorem selectFormula_termEq {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t w : Term P.signature Γ s) (hΓ : Declaration.sorts Γ ⊆ U.declarations)
    (hs : Declaration.sort s ∈ U.declarations) (ht : termReferences t ⊆ U.declarations)
    (hw : termReferences w ⊆ U.declarations)
    (hg : Declaration.formulaSupport (Formula.termEq t w) ⊆ U.declarations) :
    selectFormula (Formula.termEq t w) hg = Formula.termEq (selectTerm t hΓ hs ht) (selectTerm w hΓ hs hw) := by
  simp only [Formula.termEq_eq_ex] at hg ⊢
  rw [selectFormula_ex_cast, selectFormula_conj,
    Formula.cast_conj_context (context_cons s Γ (Declaration.sorts_cons_subset hs hΓ))]
  let supported := Declaration.formula_conj (P := P) t.graph w.graph
  exact congrArg (Formula.ex (sig := signature U))
    (congrArg₂ (Formula.conj (sig := signature U))
      (selectFormula_graph t hΓ hs ht ((Declaration.binarySupport_left supported).trans (existsSupport hg)))
      (selectFormula_graph w hΓ hs hw ((Declaration.binarySupport_right supported).trans (existsSupport hg))))

/-- The support of a written equality retains its shared sort and both term graphs. -/
theorem termEq_support {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (left right : Term P.signature Γ s)
    (h : Declaration.formulaSupport (Formula.termEq left right) ⊆ U.declarations) :
    Declaration.sort s ∈ U.declarations ∧ termReferences left ⊆ U.declarations ∧
      termReferences right ⊆ U.declarations := by
  rw [Formula.termEq_eq_ex] at h
  refine ⟨h (Declaration.boundSort_mem_formulaSupport _), ?_⟩
  have body := (Declaration.formulaSupport_ex_body _).trans h
  rw [Declaration.formulaSupport_eq, Declaration.formula_conj] at body
  exact ⟨(termReferences_subset_graph left).trans ((Set.subset_union_left.trans Set.subset_union_right).trans body),
    (termReferences_subset_graph right).trans ((Set.subset_union_right.trans Set.subset_union_right).trans body)⟩

/-- Renaming variables preserves the primitive references of a term. -/
theorem termReferences_rename {Γ Δ : List P.signature.SortType} {s : P.signature.SortType}
    (t : Term P.signature Γ s) (ρ : Renaming Γ Δ) : termReferences (t.rename ρ) = termReferences t := by
  induction t generalizing Δ with
  | var i => simp only [Term.rename_var, termReferences_var]
  | app op args ih =>
    simp only [Term.rename_app, termReferences_app, ih]
  | letBind init body hi hb =>
    simp only [Term.rename_letBind, termReferences_letBind, hi, hb]

/-- Rename each argument of an application indexed by an equal arity. -/
private theorem rename_reindexedApp {sig : Signature.{u}} {Γ Δ : List sig.SortType} (op : Operation sig)
    {a : Arity sig.SortType} (same : op.arity = a) (args : ∀ {s}, Var a.inputs s → Term sig Γ s)
    (ρ : Renaming Γ Δ) :
    (reindexedApp op same args).rename ρ = reindexedApp op same (fun i => (args i).rename ρ) := by
  cases same
  simp only [reindexedApp_rfl, Term.rename_app]

/-- Selection commutes with the renaming of variables in a supported term. -/
theorem selectTerm_rename {Γ : List P.signature.SortType} {s : P.signature.SortType} (t : Term P.signature Γ s) :
    ∀ {Δ : List P.signature.SortType} (ρ : Renaming Γ Δ)
      (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
      (hs : Declaration.sort s ∈ U.declarations) (ht : termReferences t ⊆ U.declarations)
      (hRen : termReferences (t.rename ρ) ⊆ U.declarations),
      selectTerm (t.rename ρ) hΔ hs hRen = (selectTerm t hΓ hs ht).rename (selectRenaming hΓ hΔ ρ) := by
  induction t with
  | var i =>
    intro Δ ρ hΓ hΔ hs ht hRen
    simp only [Term.rename_var] at hRen ⊢
    simp only [selectTerm_var, Term.rename_var]
    exact congrArg (Term.var (sig := signature U)) (renaming_selectVar hΓ hΔ ρ i).symm
  | @app Γ op args ih =>
    intro Δ ρ hΓ hΔ hs ht hRen
    simp only [Term.rename_app] at hRen ⊢
    rw [termReferences_app] at ht hRen
    have keepOp := ht (Or.inl (Set.mem_singleton (Declaration.ofOperation op)))
    let hΛ := operationInputs op keepOp
    let ts : ∀ {s}, Var (context op.arity.inputs hΛ) s → Term (signature U) (context Γ hΓ) s :=
      fun {s} i => selectTerm (args (ambientVar hΛ i)) hΓ s.property (fun _ hd => ht (Or.inr ⟨_, _, hd⟩))
    let ts' : ∀ {s}, Var (context op.arity.inputs hΛ) s → Term (signature U) (context Δ hΔ) s :=
      fun {s} i => selectTerm ((args (ambientVar hΛ i)).rename ρ) hΔ s.property (fun _ hd => hRen (Or.inr ⟨_, _, hd⟩))
    let op' := operation op keepOp
    let same := operation_arity op keepOp
    simp only [selectTerm_app]
    change reindexedApp op' same ts' = (reindexedApp op' same ts).rename (selectRenaming hΓ hΔ ρ)
    refine (congrArg (fun (as' : ∀ {s}, Var (context op.arity.inputs hΛ) s →
        Term (signature U) (context Δ hΔ) s) => reindexedApp op' same as') ?_).trans
      (rename_reindexedApp op' same ts (selectRenaming hΓ hΔ ρ)).symm
    funext s i
    exact ih (ambientVar hΛ i) ρ hΓ hΔ s.property _ _
  | @letBind Γ a s init body hi hb =>
    intro Δ ρ hΓ hΔ hs ht hRen
    simp only [Term.rename_letBind] at hRen ⊢
    rw [termReferences_letBind] at ht hRen
    let ha := ht (Or.inl (Set.mem_singleton (Declaration.sort a)))
    let hΓ' := Declaration.sorts_cons_subset ha hΓ
    let hΔ' := Declaration.sorts_cons_subset ha hΔ
    let source := context_cons a Γ hΓ'
    let target := context_cons a Δ hΔ'
    let head : SortName U := ⟨a, ha⟩
    let transport := fun {C D : List (SortName U)} (same : C = D) =>
      cast (congrArg (fun ctx => Term (signature U) ctx ⟨s, hs⟩) same)
    let body' := transport source (selectTerm body hΓ' hs (fun _ hd => ht (Or.inr (Or.inr hd))))
    have first := hi ρ hΓ hΔ ha (fun _ hd => ht (Or.inr (Or.inl hd))) (fun _ hd => hRen (Or.inr (Or.inl hd)))
    have second := hb ρ.lift hΓ' hΔ' hs (fun _ hd => ht (Or.inr (Or.inr hd)))
      (fun _ hd => hRen (Or.inr (Or.inr hd)))
    have moved := congrArg (transport target) second
    dsimp only [transport] at moved
    rw [Term.rename_cast_context source target] at moved
    have lifted := congrArg (fun (mapVars : Renaming (head :: context Γ hΓ) (head :: context Δ hΔ)) =>
      body'.rename mapVars) (selectRenaming_lift_cast ha hΓ hΔ ρ)
    simp only [selectTerm_letBind_cast, Term.rename_letBind]
    exact congrArg₂ (Term.letBind (sig := signature U)) first (moved.trans lifted)


/-- Binding term arguments preserves the primitive references from the body. -/
theorem formula_subset_bindArguments {Γ : List P.signature.SortType} (Λ : List P.signature.SortType)
    (ts : ∀ {s}, Var Λ s → Term P.signature Γ s) (p : Formula P.signature (Λ ++ Γ)) :
    Declaration.formula p ⊆ Declaration.formula (Formula.bindArguments Λ ts p) := by
  rw [Formula.bindArguments_eq_existsMany]
  apply Set.Subset.trans _ (formula_existsMany_subset Λ _)
  rw [Declaration.formula_conj]
  exact Set.subset_union_right

/-- Read the body support separately from the argument witnesses in a bound formula. -/
private theorem bindArguments_body_kept {Γ Λ : List P.signature.SortType}
    (ts : ∀ {s}, Var Λ s → Term P.signature Γ s) (p : Formula P.signature (Λ ++ Γ))
    (h : Declaration.formulaSupport (Formula.bindArguments Λ ts p) ⊆ U.declarations) :
    Declaration.formulaSupport p ⊆ U.declarations := by
  rw [Formula.bindArguments_eq_existsMany] at h
  exact (Declaration.binarySupport_right (Declaration.formula_conj _ p)).trans (keepExistsMany _ h)

/-- Retyping the strict argument witnesses commutes with binding those arguments. -/
private theorem selectFormula_bindArguments {Γ Λ : List P.signature.SortType}
    (ts : ∀ {s}, Var Λ s → Term P.signature Γ s) (p : Formula P.signature (Λ ++ Γ))
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΛ : Declaration.sorts Λ ⊆ U.declarations)
    (hTerms : ∀ {s} (i : Var Λ s), termReferences (ts i) ⊆ U.declarations)
    (h : Declaration.formulaSupport (Formula.bindArguments Λ ts p) ⊆ U.declarations) :
    selectFormula (Formula.bindArguments Λ ts p) h =
      Formula.bindArguments (sig := signature U) (context Λ hΛ)
        (fun {s} i => selectTerm (ts (ambientVar hΛ i)) hΓ s.property (hTerms (ambientVar hΛ i)))
        (cast (congrArg (Formula (signature U)) (context_append hΛ hΓ))
          (selectFormula p (bindArguments_body_kept ts p h))) := by
  let fs : ∀ {s}, Var Λ s → Formula P.signature (Λ ++ Γ) := fun i => (ts i).graphAt (Var.shift Λ) (i.inLeft Γ)
  let body := (Formula.conjoin Λ fs).conj p
  have written : Formula.bindArguments Λ ts p = Formula.existsMany Λ body :=
    Formula.bindArguments_eq_existsMany Λ ts p
  have support : Declaration.formulaSupport (Formula.existsMany Λ body) ⊆ U.declarations := by
    rw [← written]
    exact h
  have hBody := keepExistsMany body support
  let writtenBody := Declaration.formula_conj (P := P) (Formula.conjoin Λ fs) p
  let hArgs := (Declaration.binarySupport_left writtenBody).trans hBody
  let hGuarded := (Declaration.binarySupport_right writtenBody).trans hBody
  let crossing := context_append hΛ hΓ
  refine (selectFormula_congr written (hq := support)).trans ?_
  conv_rhs => rw [Formula.bindArguments_eq_existsMany]
  rw [selectFormula_existsMany body support hΓ hΛ]
  erw [selectFormula_conj]
  change Formula.existsMany (context Λ hΛ) (cast (congrArg (Formula (signature U)) crossing)
    ((selectFormula (Formula.conjoin Λ fs) hArgs).conj (selectFormula p hGuarded))) = _
  rw [Formula.cast_conj_context crossing, selectFormula_conjoin fs hArgs hΛ, cast_formula_conjoin crossing]
  apply congrArg (Formula.existsMany (sig := signature U) (context Λ hΛ))
  apply congrArg (fun x : Formula (signature U) (context Λ hΛ ++ context Γ hΓ) => Formula.conj x _)
  apply congrArg (Formula.conjoin (sig := signature U) (context Λ hΛ))
  funext s i
  let j := ambientVar hΛ i
  let t := selectTerm (ts j) hΓ s.property (hTerms j)
  have selected := selectFormula_graphAt (ts j) (Var.shift Λ) (j.inLeft Γ) hΓ (appendSupport hΛ hΓ)
    (hTerms j) (keepConjoin fs hArgs j)
  refine (congrArg (cast (congrArg (Formula (signature U)) crossing)) selected).trans ?_
  refine (cast_graphAt crossing t _ _).trans ?_
  have shifted : (fun {s} (i : Var (context Γ hΓ) s) =>
      cast (congrArg (fun Ξ => Var Ξ s) crossing)
        (selectRenaming hΓ (appendSupport hΛ hΓ) (Var.shift Λ) i)) =
        (fun {s} (i : Var (context Γ hΓ) s) => i.shift (context Λ hΛ)) := by
    funext s i
    rw [selectRenaming_apply]
    exact (selectVar_shift hΛ hΓ (ambientVar hΓ i)).trans
      (congrArg (Var.shift (context Λ hΛ)) (selectVar_ambientVar hΓ i))
  exact congrArg₂ (fun (mapVars : Renaming (context Γ hΓ) (context Λ hΛ ++ context Γ hΓ))
    (out : Var (context Λ hΛ ++ context Γ hΓ) s) => t.graphAt mapVars out) shifted
    ((selectVar_inLeft hΛ hΓ j).trans
      (congrArg (Var.inLeft (context Γ hΓ)) (selectVar_ambientVar hΛ i)))

/-- Transport a relation atom by reindexing its argument positions in the free context. -/
private theorem cast_relationAtom {sig : Signature.{u}} {Γ Δ : List sig.SortType}
    (h : Γ = Δ) (r : sig.Rel) (ρ : Renaming (sig.relInputs r) Γ) :
    cast (congrArg (Formula sig) h) (.atom (.rel r ρ)) =
      .atom (.rel r (fun i => cast (congrArg (fun Δ => Var Δ _) h) (ρ i))) := by
  cases h
  rfl

/-- Transport a domain atom by reindexing its argument positions in the free context. -/
private theorem cast_domainAtom {sig : Signature.{u}} {Γ Δ : List sig.SortType}
    (h : Γ = Δ) (p : sig.Partial) (ρ : Renaming (sig.partialArity p).inputs Γ) :
    cast (congrArg (Formula sig) h) (.atom (.domain p ρ)) =
      .atom (.domain p (fun i => cast (congrArg (fun Δ => Var Δ _) h) (ρ i))) := by
  cases h
  rfl

/-- Selection commutes with the graph expansion of a relation applied to terms. -/
theorem selectFormula_termRel {Γ : List P.signature.SortType} (r : P.signature.Rel)
    (ts : ∀ {s}, Var (P.signature.relInputs r) s → Term P.signature Γ s)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hr : Declaration.relation r ∈ U.declarations)
    (ht : ∀ {s} (i : Var (P.signature.relInputs r) s), termReferences (ts i) ⊆ U.declarations)
    (h : Declaration.formulaSupport (Formula.termRel r ts) ⊆ U.declarations) :
    selectFormula (Formula.termRel r ts) h = Formula.termRel (sig := signature U) ⟨r, hr⟩
      (fun {s} i => selectTerm (ts (ambientVar (relationInputs r hr) i)) hΓ s.property (ht _)) := by
  simp only [Formula.termRel_eq_bindArguments] at h ⊢
  let hΛ := relationInputs r hr
  let r' : (signature U).Rel := ⟨r, hr⟩
  refine (selectFormula_bindArguments ts (.atom (.rel r (Var.inLeft Γ))) hΓ hΛ ht h).trans ?_
  apply congrArg (Formula.bindArguments (sig := signature U) (context (P.signature.relInputs r) hΛ) _)
  rw [selectFormula_atom, selectAtomic_rel]
  refine (cast_relationAtom (context_append hΛ hΓ) r' (selectRenaming hΛ (appendSupport hΛ hΓ) (Var.inLeft Γ))).trans ?_
  exact congrArg (fun (mapVars : Renaming (context (P.signature.relInputs r) hΛ)
    (context (P.signature.relInputs r) hΛ ++ context Γ hΓ)) => Formula.atom (.rel r' mapVars))
    (inLeftRenaming hΓ hΛ)

/-- Selection commutes with the graph expansion of a partial domain applied to terms. -/
theorem selectFormula_termDomain {Γ : List P.signature.SortType} (p : P.signature.Partial)
    (ts : ∀ {s}, Var (P.signature.partialArity p).inputs s → Term P.signature Γ s)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hp : Declaration.partialOp p ∈ U.declarations)
    (ht : ∀ {s} (i : Var (P.signature.partialArity p).inputs s), termReferences (ts i) ⊆ U.declarations)
    (h : Declaration.formulaSupport (Formula.termDomain p ts) ⊆ U.declarations) :
    selectFormula (Formula.termDomain p ts) h = Formula.termDomain (sig := signature U) ⟨p, hp⟩
      (fun {s} i => selectTerm (ts (ambientVar (operationInputs (.partialOp p)
        (Declaration.ofOperation_partialOp_mem p hp)) i)) hΓ s.property (ht _)) := by
  simp only [Formula.termDomain_eq_bindArguments] at h ⊢
  let hΛ := operationInputs (.partialOp p) (Declaration.ofOperation_partialOp_mem p hp)
  let p' : (signature U).Partial := ⟨p, hp⟩
  refine (selectFormula_bindArguments ts (.atom (.domain p (Var.inLeft Γ))) hΓ hΛ ht h).trans ?_
  apply congrArg (Formula.bindArguments (sig := signature U) (context (P.signature.partialArity p).inputs hΛ) _)
  rw [selectFormula_atom, selectAtomic_domain]
  refine (cast_domainAtom (context_append hΛ hΓ) p' (selectRenaming hΛ (appendSupport hΛ hΓ) (Var.inLeft Γ))).trans ?_
  exact congrArg (fun (mapVars : Renaming (context (P.signature.partialArity p).inputs hΛ)
    (context (P.signature.partialArity p).inputs hΛ ++ context Γ hΓ)) => Formula.atom (.domain p' mapVars))
    (inLeftRenaming hΓ hΛ)


/-- Expand the graph atom with term inputs and a term output along an equal arity. -/
private theorem termGraph_reindexed {sig : Signature.{u}} {Γ : List sig.SortType} (op : Operation sig)
    {a : Arity sig.SortType} (same : op.arity = a) (terms : ∀ {s}, Var a.inputs s → Term sig Γ s)
    (out : Term sig Γ a.output) :
    Formula.termGraph op
        (fun {s} i => terms (cast (congrArg (fun b => Var b.inputs s) same) i))
        (cast (congrArg (Term sig Γ) (congrArg Arity.output same.symm)) out) =
      Formula.bindArguments (a.output :: a.inputs) (Term.argsCons out terms)
        (.atom (reindexedGraph op same (fun i => (Var.there i).inLeft Γ) (Var.here.inLeft Γ))) := by
  cases same
  rw [Formula.termGraph_eq_bindArguments]
  rfl

/-- Selection commutes with the graph expansion applied to terms for the inputs and result. -/
theorem selectFormula_termGraph {Γ : List P.signature.SortType} (op : Operation P.signature)
    (ts : ∀ {s}, Var op.arity.inputs s → Term P.signature Γ s) (out : Term P.signature Γ op.arity.output)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (ho : Declaration.ofOperation op ∈ U.declarations)
    (ht : ∀ {s} (i : Var op.arity.inputs s), termReferences (ts i) ⊆ U.declarations)
    (hy : termReferences out ⊆ U.declarations)
    (h : Declaration.formulaSupport (Formula.termGraph op ts out) ⊆ U.declarations) :
    selectFormula (Formula.termGraph op ts out) h =
      Formula.termGraph (operation op ho)
        (fun {s} i => let j := cast (congrArg (fun a => Var a.inputs s) (operation_arity op ho)) i
          selectTerm (ts (ambientVar (operationInputs op ho) j)) hΓ s.property (ht _))
        (cast (congrArg (Term (signature U) (context Γ hΓ))
          (congrArg Arity.output (operation_arity op ho).symm))
          (selectTerm out hΓ (operationOutput op ho) hy)) := by
  simp only [Formula.termGraph_eq_bindArguments op ts out] at h ⊢
  let hΛ := operationInputs op ho
  let hs := operationOutput op ho
  let lead := Declaration.sorts_cons_subset hs hΛ
  let selected := operation op ho
  let same := operation_arity op ho
  let ht' : ∀ {s}, (i : Var (op.arity.output :: op.arity.inputs) s) →
      termReferences (Term.argsCons out ts i) ⊆ U.declarations := fun i =>
      match i with
      | .here => by simpa only [Term.argsCons_here] using hy
      | .there j => by simpa only [Term.argsCons_there] using ht j
  let p := Formula.atom (.graph op (fun i => (Var.there i).inLeft Γ) (Var.here.inLeft Γ))
  let lowered : ∀ {s}, Var (context op.arity.inputs hΛ) s → Term (signature U) (context Γ hΓ) s :=
    fun {s} i => selectTerm (ts (ambientVar hΛ i)) hΓ s.property (ht _)
  refine (selectFormula_bindArguments (Term.argsCons out ts) p hΓ lead ht' h).trans ?_
  refine Eq.trans ?_ (termGraph_reindexed selected same lowered (selectTerm out hΓ hs hy)).symm
  apply congrArg₂ (Formula.bindArguments (sig := signature U) (context (op.arity.output :: op.arity.inputs) lead))
  · funext s i
    cases i with
    | here =>
      simp only [ambientVar_here, Term.argsCons_here]
      exact (Term.argsCons_here (selectTerm out hΓ hs hy) lowered).symm
    | there i =>
      simp only [ambientVar_there, Term.argsCons_there]
      exact (Term.argsCons_there (selectTerm out hΓ hs hy) lowered i).symm
  · let crossing := context_append lead hΓ
    rw [selectFormula_atom, selectAtomic_graph]
    change cast (congrArg (Formula (signature U)) crossing)
      (.atom (selectGraph (appendSupport lead hΓ) op ho
        (fun i => (Var.there i).inLeft Γ) (Var.here.inLeft Γ))) = _
    rw [selectGraph_reindexed]
    refine (cast_reindexedGraph crossing selected same _ _).trans ?_
    apply congrArg (Formula.atom (sig := signature U))
    apply congrArg₂ (fun (mapVars : Renaming (context op.arity.inputs hΛ)
        (context (op.arity.output :: op.arity.inputs) lead ++ context Γ hΓ))
        (y : Var (context (op.arity.output :: op.arity.inputs) lead ++ context Γ hΓ) _) =>
      reindexedGraph selected same mapVars y)
    · funext s i
      exact (selectVar_inLeft lead hΓ (.there (ambientVar hΛ i))).trans
        (congrArg (fun j => (Var.there j).inLeft (context Γ hΓ)) (selectVar_ambientVar hΛ i))
    · exact selectVar_inLeft lead hΓ .here


/-- Selection reads each supported term of a substitution at its original variable position. -/
def selectSubstitution {Γ Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations) :
    Substitution (signature U) (context Γ hΓ) (context Δ hΔ) :=
  ⟨fun {s} i => selectTerm (θ (ambientVar hΓ i)) hΔ s.property (hθ (ambientVar hΓ i))⟩

/-- A selected position reads the retyped term at its ambient position. -/
theorem selectSubstitution_at {Γ Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations)
    {s : SortName U} (i : Var (context Γ hΓ) s) :
    selectSubstitution θ hΓ hΔ hθ i =
      selectTerm (θ (ambientVar hΓ i)) hΔ s.property (hθ (ambientVar hΓ i)) :=
  rfl

/-- The selected substitution at a selected position is the original substituted term retyped. -/
theorem selectSubstitution_apply {Γ Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations) {s} (i : Var Γ s) :
    selectSubstitution θ hΓ hΔ hθ (selectVar hΓ i) =
      selectTerm (θ i) hΔ (varKept hΓ i) (hθ i) := by
  have atOriginal := ambientVar_selectVar hΓ i
  rw [selectSubstitution_at]
  exact congrArg (fun j : Var Γ s => selectTerm (θ j) hΔ (varKept hΓ i) (hθ j)) atOriginal

/-- The substitution under a binder uses the same supported primitives as before. -/
theorem liftTermReferences {Γ Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
    (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations)
    {a s} (i : Var (a :: Γ) s) : termReferences (θ.lift i) ⊆ U.declarations := by
  cases i with
  | here => rw [Substitution.lift_here, termReferences_var]; exact Set.empty_subset _
  | there i =>
    rw [Substitution.lift_there, termReferences_rename]
    exact hθ i

/-- Selection commutes with lifting a substitution into one more binder. -/
theorem selectSubstitution_lift {Γ Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations)
    {a} (ha : Declaration.sort a ∈ U.declarations) :
    selectSubstitution (θ.lift (s := a)) (Declaration.sorts_cons_subset ha hΓ)
      (Declaration.sorts_cons_subset ha hΔ) (liftTermReferences θ hθ) =
      (selectSubstitution θ hΓ hΔ hθ).lift (s := (⟨a, ha⟩ : SortName U)) := by
  apply Substitution.ext
  intro s v
  cases v with
  | here =>
    simp only [selectSubstitution_at, ambientVar_here, Substitution.lift_here, selectTerm_var, selectVar_here]
    exact (Substitution.lift_here (s := (⟨a, ha⟩ : SortName U)) (selectSubstitution θ hΓ hΔ hθ)).symm
  | there v =>
    have atOld := Substitution.lift_there (s := (⟨a, ha⟩ : SortName U)) (selectSubstitution θ hΓ hΔ hθ) v
    rw [atOld]
    simp only [selectSubstitution_at, ambientVar_there, Substitution.lift_there]
    let i := ambientVar hΓ v
    let t := selectTerm (θ i) hΔ s.property (hθ i)
    have moved : termReferences ((θ i).rename (fun j => Var.there (t := a) j)) ⊆ U.declarations := by
      rw [termReferences_rename]
      exact hθ i
    exact (selectTerm_rename (θ i) (fun j => .there j) hΔ (Declaration.sorts_cons_subset ha hΔ)
      s.property (hθ i) moved).trans
      (congrArg (fun (mapVars : Renaming (context Δ hΔ) (context (a :: Δ) (Declaration.sorts_cons_subset ha hΔ))) =>
        t.rename mapVars) (selectRenaming_there ha hΔ))

/-- The selected lift agrees with the ordinary lift after transporting both contexts. -/
theorem selectSubstitution_lift_cast {Γ Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations)
    {a} (ha : Declaration.sort a ∈ U.declarations) :
    @cast _ _ (congrArg₂ (Substitution (signature U))
      (context_cons a Γ (Declaration.sorts_cons_subset ha hΓ))
      (context_cons a Δ (Declaration.sorts_cons_subset ha hΔ)))
      (selectSubstitution (θ.lift (s := a)) (Declaration.sorts_cons_subset ha hΓ)
        (Declaration.sorts_cons_subset ha hΔ) (liftTermReferences θ hθ)) =
      (selectSubstitution θ hΓ hΔ hθ).lift (s := (⟨a, ha⟩ : SortName U)) :=
  selectSubstitution_lift θ hΓ hΔ hθ ha

/-- Substitute in each argument of an application indexed by an equal arity. -/
private theorem substitute_reindexedApp {sig : Signature.{u}} {Γ Δ : List sig.SortType} (op : Operation sig)
    {a : Arity sig.SortType} (same : op.arity = a) (args : ∀ {s}, Var a.inputs s → Term sig Γ s)
    (θ : Substitution sig Γ Δ) :
    (reindexedApp op same args).substitute θ = reindexedApp op same (fun i => (args i).substitute θ) := by
  cases same
  simp only [reindexedApp_rfl, Term.substitute_app]

/-- Selection commutes with capture-free substitution in a supported term. -/
theorem selectTerm_substitute {Γ : List P.signature.SortType} {s : P.signature.SortType} (t : Term P.signature Γ s) :
    ∀ {Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
      (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
      (hs : Declaration.sort s ∈ U.declarations) (ht : termReferences t ⊆ U.declarations)
      (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations)
      (hSub : termReferences (t.substitute θ) ⊆ U.declarations),
      selectTerm (t.substitute θ) hΔ hs hSub = (selectTerm t hΓ hs ht).substitute (selectSubstitution θ hΓ hΔ hθ) := by
  induction t with
  | var i =>
    intro Δ θ hΓ hΔ hs ht hθ hSub
    simp only [Term.substitute_var] at hSub ⊢
    simp only [selectTerm_var, Term.substitute_var]
    exact (selectSubstitution_apply θ hΓ hΔ hθ i).symm
  | @app Γ op args ih =>
    intro Δ θ hΓ hΔ hs ht hθ hSub
    simp only [Term.substitute_app] at hSub ⊢
    rw [termReferences_app] at ht hSub
    have keepOp := ht (Or.inl (Set.mem_singleton (Declaration.ofOperation op)))
    let hΛ := operationInputs op keepOp
    let ts : ∀ {s}, Var (context op.arity.inputs hΛ) s → Term (signature U) (context Γ hΓ) s :=
      fun {s} i => selectTerm (args (ambientVar hΛ i)) hΓ s.property (fun _ hd => ht (Or.inr ⟨_, _, hd⟩))
    let ts' : ∀ {s}, Var (context op.arity.inputs hΛ) s → Term (signature U) (context Δ hΔ) s :=
      fun {s} i => selectTerm ((args (ambientVar hΛ i)).substitute θ) hΔ s.property (fun _ hd => hSub (Or.inr ⟨_, _, hd⟩))
    let op' := operation op keepOp
    let same := operation_arity op keepOp
    let θ' := selectSubstitution θ hΓ hΔ hθ
    simp only [selectTerm_app]
    change reindexedApp op' same ts' = (reindexedApp op' same ts).substitute θ'
    refine (congrArg (fun (as' : ∀ {s}, Var (context op.arity.inputs hΛ) s →
        Term (signature U) (context Δ hΔ) s) => reindexedApp op' same as') ?_).trans
      (substitute_reindexedApp op' same ts θ').symm
    funext s i
    exact ih (ambientVar hΛ i) θ hΓ hΔ s.property _ hθ _
  | @letBind Γ a s init body hi hb =>
    intro Δ θ hΓ hΔ hs ht hθ hSub
    simp only [Term.substitute_letBind] at hSub ⊢
    rw [termReferences_letBind] at ht hSub
    let ha := ht (Or.inl (Set.mem_singleton (Declaration.sort a)))
    let hΓ' := Declaration.sorts_cons_subset ha hΓ
    let hΔ' := Declaration.sorts_cons_subset ha hΔ
    let source := context_cons a Γ hΓ'
    let target := context_cons a Δ hΔ'
    let head : SortName U := ⟨a, ha⟩
    let transport := fun {C D : List (SortName U)} (same : C = D) =>
      cast (congrArg (fun ctx => Term (signature U) ctx ⟨s, hs⟩) same)
    let body' := transport source (selectTerm body hΓ' hs (fun _ hd => ht (Or.inr (Or.inr hd))))
    have first := hi θ hΓ hΔ ha (fun _ hd => ht (Or.inr (Or.inl hd))) hθ (fun _ hd => hSub (Or.inr (Or.inl hd)))
    have second := hb θ.lift hΓ' hΔ' hs (fun _ hd => ht (Or.inr (Or.inr hd)))
      (liftTermReferences θ hθ) (fun _ hd => hSub (Or.inr (Or.inr hd)))
    have moved := congrArg (transport target) second
    dsimp only [transport] at moved
    rw [Term.substitute_cast_context source target] at moved
    have lifted := congrArg (fun (replacement : Substitution (signature U)
        (head :: context Γ hΓ) (head :: context Δ hΔ)) => body'.substitute replacement)
      (selectSubstitution_lift_cast θ hΓ hΔ hθ ha)
    simp only [selectTerm_letBind_cast, Term.substitute_letBind]
    exact congrArg₂ (Term.letBind (sig := signature U)) first (moved.trans lifted)

/-- A supported definedness guard supplies the result sort and references of each substitution term. -/
theorem substitution_term_kept {Γ Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
    (h : Declaration.formulaSupport θ.defined ⊆ U.declarations)
    {s} (i : Var Γ s) : Declaration.sort s ∈ U.declarations ∧ termReferences (θ i) ⊆ U.declarations := by
  rw [Substitution.defined_eq_conjoin] at h
  have one := keepConjoin (fun j => (θ j).defined) h i
  rw [Term.defined_eq_ex_graph] at one
  refine ⟨one (Declaration.boundSort_mem_formulaSupport (θ i).graph), ?_⟩
  have written : Declaration.formula (θ i).graph ⊆ Declaration.formulaSupport (θ i).graph.ex := by
    rw [Declaration.formulaSupport_eq, Declaration.formula_ex]
    exact Set.subset_union_right.trans Set.subset_union_right
  exact (termReferences_subset_graph (θ i)).trans (written.trans one)

/-- A sort named in a context has a typed variable witnessing that occurrence. -/
private theorem variable_of_mem {S : Type u} {Γ : List S} {s : S} (h : s ∈ Γ) : Nonempty (Var Γ s) := by
  induction Γ with
  | nil => cases h
  | cons t Γ ih =>
    rcases List.mem_cons.mp h with rfl | tail
    · exact ⟨.here⟩
    · exact ⟨.there (ih tail).some⟩

/-- The guard retains the source sorts of a substitution, including unused positions. -/
theorem substitution_source_kept {Γ Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
    (h : Declaration.formulaSupport θ.defined ⊆ U.declarations) : Declaration.sorts Γ ⊆ U.declarations := by
  rw [Declaration.sorts_eq_image]
  rintro _ ⟨s, xs, rfl⟩
  obtain ⟨i⟩ := variable_of_mem xs
  exact (substitution_term_kept θ h i).1

attribute [local irreducible] Substitution.defined selectSubstitution in
/-- Retyping the definedness guard is the definedness guard of the retyped substitution. -/
theorem selectSubstitution_defined {Γ Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations)
    (h : Declaration.formulaSupport θ.defined ⊆ U.declarations) :
    selectFormula θ.defined h = (selectSubstitution θ hΓ hΔ hθ).defined := by
  have same := Substitution.defined_eq_conjoin θ
  have support : Declaration.formulaSupport (Formula.conjoin Γ (fun i => (θ i).defined)) ⊆ U.declarations :=
    same ▸ h
  refine (selectFormula_congr same (hp := h) (hq := support)).trans ?_
  refine (selectFormula_conjoin (fun i => (θ i).defined) support hΓ).trans ?_
  rw [Substitution.defined_eq_conjoin]
  apply congrArg (Formula.conjoin (sig := signature U) (context Γ hΓ))
  funext s i
  rw [selectSubstitution_at]
  exact selectFormula_defined (θ (ambientVar hΓ i)) hΔ s.property (hθ _) _

end DeclarationContext.Selected
end SHIGURE
