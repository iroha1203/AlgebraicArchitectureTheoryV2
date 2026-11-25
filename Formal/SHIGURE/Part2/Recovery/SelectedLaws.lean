import Formal.SHIGURE.Part1.ContextSelectedCategories
import Formal.SHIGURE.Part1.CompositionComparison
import Formal.SHIGURE.Part2.Realizations.TensorRestriction

/-!
# Written Laws under an inclusion of declaration contexts

Selecting a Law in the smaller vocabulary and then including its names
retains the same written formula as selecting in the larger vocabulary.
-/

universe u

namespace SHIGURE.DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}

/-- All original variable positions are retained by the inclusion of contexts. -/
theorem namesOfLE_context (inside : V ≤ U) (Γ : List P.signature.SortType)
    (keep : Declaration.sorts Γ ⊆ V.declarations) :
    (context Γ keep).map (namesOfLE inside).onSort = context Γ (keep.trans inside) := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih =>
    exact congrArg (List.cons ⟨s, inside (keep (Declaration.sort_mem_sorts List.mem_cons_self))⟩) (ih _)

/-- Including a selected variable retains its original position, also under a binder. -/
theorem namesOfLE_selectVar (inside : V ≤ U) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ V.declarations) {s : P.signature.SortType} (v : Var Γ s) :
    Renaming.castContext (namesOfLE_context inside Γ keep) ((selectVar keep v).mapSorts (namesOfLE inside).onSort) =
      selectVar (keep.trans inside) v := by
  induction v with
  | @here Γ s =>
    have shape := namesOfLE_context inside Γ ((tailSortsSubset s Γ).trans keep)
    change Renaming.castContext (congrArg (List.cons _) shape) Var.here = Var.here
    exact congrFun (congrFun (Renaming.castContext_cons shape) _) Var.here
  | @there Γ s t v ih =>
    have shape := namesOfLE_context inside Γ ((tailSortsSubset t Γ).trans keep)
    change Renaming.castContext (congrArg (List.cons _) shape)
        (Var.there ((selectVar _ v).mapSorts (namesOfLE inside).onSort)) = _
    rw [Renaming.castContext_cons shape]
    exact congrArg Var.there (ih _)

private theorem namesOfLE_selectRenaming (inside : V ≤ U) {Γ Δ : List P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ V.declarations) (keepΔ : Declaration.sorts Δ ⊆ V.declarations)
    (ρ : Renaming Γ Δ) :
    @Renaming.comp (SortName U) _ _ _ (Renaming.castContext (namesOfLE_context inside Δ keepΔ))
      (Renaming.mapSorts (namesOfLE inside).onSort (selectRenaming keepΓ keepΔ ρ)) =
    @Renaming.comp (SortName U) _ _ _ (selectRenaming (keepΓ.trans inside) (keepΔ.trans inside) ρ)
      (Renaming.castContext (namesOfLE_context inside Γ keepΓ)) := by
  let l : Renaming _ _ := Renaming.comp (Renaming.castContext (namesOfLE_context inside Δ keepΔ))
    (Renaming.mapSorts (namesOfLE inside).onSort (selectRenaming keepΓ keepΔ ρ))
  let r : Renaming _ _ := Renaming.comp (selectRenaming (keepΓ.trans inside) (keepΔ.trans inside) ρ)
    (Renaming.castContext (namesOfLE_context inside Γ keepΓ))
  change @l = @r
  funext s i
  refine Var.forall_mapSorts (namesOfLE inside).onSort (P := fun {_} j => l j = r j) ?_ i
  intro s i
  obtain ⟨j, rfl⟩ : ∃ j : Var Γ s.val, selectVar keepΓ j = i :=
    ⟨ambientVar keepΓ i, selectVar_ambientVar keepΓ i⟩
  simp only [l, r, Renaming.comp_apply, Renaming.mapSorts_apply, renaming_selectVar, namesOfLE_selectVar]

private def castRenamingInput {K : Type u} {A A' B : List K} (src : A = A')
    (r : Renaming A B) : Renaming A' B :=
  fun {s} => src ▸ (r (s := s))

private theorem rename_cast_input {K : Type u} {A A' B B' : List K} (src : A = A') (dst : B = B')
    (r : Renaming A B) (r' : Renaming A' B')
    (commutes : @Renaming.comp K A B B' (Renaming.castContext dst) r =
      @Renaming.comp K A A' B' r' (Renaming.castContext src)) :
    @Renaming.comp K A' B B' (Renaming.castContext dst) (castRenamingInput src r) = @r' := by
  cases src
  exact commutes

private theorem namesOfLE_selectAtomic (inside : V ≤ U) {Γ : List P.signature.SortType}
    (a : Atomic P.signature Γ) (keep : Declaration.atomicSupport a ⊆ V.declarations) :
    ((namesOfLE inside).formula (.atom (selectAtomic a keep))).castContext
      (namesOfLE_context inside Γ ((Declaration.sorts_subset_atomicSupport a).trans keep)) =
      .atom (selectAtomic a (keep.trans inside)) := by
  rw [Formula.castContext_eq_rename]
  let kept := (Declaration.sorts_subset_atomicSupport a).trans keep
  let dst := namesOfLE_context inside Γ kept
  cases a with
  | eq x y =>
    change Formula.atom (Atomic.eq (sig := signature U)
      (Renaming.castContext dst ((selectVar kept x).mapSorts (namesOfLE inside).onSort))
      (Renaming.castContext dst ((selectVar kept y).mapSorts (namesOfLE inside).onSort))) = _
    rw [namesOfLE_selectVar, namesOfLE_selectVar]
    rfl
  | rel r ρ =>
    let keptR := relationInputs r (keep (Declaration.relation_mem_atomicSupport r ρ))
    let src := namesOfLE_context inside _ keptR
    let rU : Rel U := ⟨r, inside (keep (Declaration.relation_mem_atomicSupport r ρ))⟩
    change Formula.atom (Atomic.rel (sig := signature U) rU (Renaming.comp (Renaming.castContext dst)
      (castRenamingInput src (Renaming.mapSorts (namesOfLE inside).onSort (selectRenaming keptR kept ρ))))) = _
    rw [rename_cast_input src dst _ _ (namesOfLE_selectRenaming inside keptR kept ρ)]
    rfl
  | domain p ρ =>
    let hp := keep (Declaration.domain_mem_atomicSupport p ρ)
    let keptP := operationInputs (.partialOp p) (Declaration.ofOperation_partialOp_mem p hp)
    let src := namesOfLE_context inside _ keptP
    let pU : Partial U := ⟨p, inside hp⟩
    change Formula.atom (Atomic.domain (sig := signature U) pU (Renaming.comp (Renaming.castContext dst)
      (castRenamingInput src (Renaming.mapSorts (namesOfLE inside).onSort (selectRenaming keptP kept ρ))))) = _
    rw [rename_cast_input src dst _ _ (namesOfLE_selectRenaming inside keptP kept ρ)]
    rfl
  | graph op ρ y =>
    let hp := keep (Declaration.graph_mem_atomicSupport op ρ y)
    let keptP := operationInputs op hp
    let src := namesOfLE_context inside _ keptP
    let opU : Operation (signature U) := operation op (inside hp)
    let moved : Renaming _ _ := fun i =>
      castRenamingInput src (Renaming.mapSorts (namesOfLE inside).onSort (selectRenaming keptP kept ρ)) i
    have args := rename_cast_input src dst _ _ (namesOfLE_selectRenaming inside keptP kept ρ)
    have result := namesOfLE_selectVar inside kept y
    cases op <;>
      change Formula.atom (.graph opU (Renaming.comp (Renaming.castContext dst) moved)
        (Renaming.castContext dst ((selectVar kept y).mapSorts (namesOfLE inside).onSort))) = _ <;>
      dsimp only [moved] <;> rw [args, result] <;>
      rfl

private theorem namesOfLE_selectFormula (inside : V ≤ U) {Γ : List P.signature.SortType}
    (p : Formula P.signature Γ) (keep : Declaration.formulaSupport p ⊆ V.declarations) :
    ((namesOfLE inside).formula (selectFormula p keep)).castContext
      (namesOfLE_context inside Γ ((Declaration.sorts_subset_formulaSupport p).trans keep)) =
      selectFormula p (keep.trans inside) := by
  induction p with
  | atom a =>
    rw [selectFormula_atom, selectFormula_atom]
    exact namesOfLE_selectAtomic inside a ((Declaration.formulaSupport_atom a).ge.trans keep)
  | truth => simp only [selectFormula_truth, SignatureNames.formula_truth, Formula.castContext_truth]
  | falsehood => simp only [selectFormula_falsehood, SignatureNames.formula_falsehood, Formula.castContext_falsehood]
  | conj p q hp hq =>
    simp only [selectFormula_conj, SignatureNames.formula_conj, Formula.castContext_conj]
    rw [hp, hq]
  | disj p q hp hq =>
    simp only [selectFormula_disj, SignatureNames.formula_disj, Formula.castContext_disj]
    rw [hp, hq]
  | ex p ih =>
    simp only [selectFormula_ex, SignatureNames.formula_ex, Formula.castContext_ex]
    exact congrArg Formula.ex (ih (existsSupport keep))

private theorem law_eq_of_context {sig : Signature.{u}} {Γ Δ : List sig.SortType}
    (h : Γ = Δ) {p q : Formula sig Γ} {p' q' : Formula sig Δ}
    (hp : p.castContext h = p') (hq : q.castContext h = q') :
    (⟨Γ, p, q⟩ : Law sig) = ⟨Δ, p', q'⟩ := by
  cases h
  simp only [Formula.castContext_rfl] at hp hq
  rw [hp, hq]

/-- Including a selected Law is exactly selecting the original Law in the larger context. -/
theorem namesOfLE_selectLaw (inside : V ≤ U) (l : Law P.signature)
    (keep : Declaration.lawBody l ⊆ V.declarations) :
    (namesOfLE inside).law (selectLaw l keep) = selectLaw l (keep.trans inside) := by
  rw [SignatureNames.law_eq, selectLaw_eq, selectLaw_eq]
  exact law_eq_of_context (namesOfLE_context inside l.context ((Declaration.sorts_subset_lawBody l).trans keep))
    (namesOfLE_selectFormula inside l.input ((Declaration.formulaSupport_input_subset_lawBody l).trans keep))
    (namesOfLE_selectFormula inside l.conclusion ((Declaration.formulaSupport_conclusion_subset_lawBody l).trans keep))

/-- A retained required Law has the same role and ambient name in the larger context. -/
def requiredNameOfLE (inside : V ≤ U) (l : (theory V).LawName) : (theory U).LawName :=
  ⟨⟨l.val.val, inside l.val.property⟩, l.property⟩

/-- The inclusion transports each required Law to its original declaration in the larger theory. -/
theorem namesOfLE_requiredLaw (inside : V ≤ U) (l : (theory V).LawName) :
    (namesOfLE inside).law ((theory V).law l) = (theory U).law (requiredNameOfLE inside l) :=
  namesOfLE_selectLaw inside (P.laws.statement l.val.val) (Declaration.lawBody_subset_of_mem l.val.property)

end SHIGURE.DeclarationContext.Selected
