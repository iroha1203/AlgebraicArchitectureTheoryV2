import Formal.SHIGURE.Part1.ContextSelectedVocabulary

/-! # Positive syntax in the selected signature

Restriction selects the actual names of every retained symbol and keeps the
same variable positions. This is the typed syntax used by the restricted
ordinary theory.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- Split support of the left side of a binary formula. -/
theorem leftSupport {Γ : List P.signature.SortType} {p q : Formula P.signature Γ}
    (h : Declaration.sorts Γ ∪ (Declaration.formula p ∪ Declaration.formula q) ⊆ U.declarations) :
    Declaration.formulaSupport p ⊆ U.declarations :=
  fun _ x => x.elim (fun x => h (Or.inl x)) (fun x => h (Or.inr (Or.inl x)))

/-- Split support of the right side of a binary formula. -/
theorem rightSupport {Γ : List P.signature.SortType} {p q : Formula P.signature Γ}
    (h : Declaration.sorts Γ ∪ (Declaration.formula p ∪ Declaration.formula q) ⊆ U.declarations) :
    Declaration.formulaSupport q ⊆ U.declarations :=
  fun _ x => x.elim (fun x => h (Or.inl x)) (fun x => h (Or.inr (Or.inr x)))

/-- Include the bound sort and the free context of an existential body. -/
theorem existsSupport {Γ : List P.signature.SortType} {s : P.signature.SortType}
    {p : Formula P.signature (s :: Γ)} (h : Declaration.formulaSupport p.ex ⊆ U.declarations) :
    Declaration.formulaSupport p ⊆ U.declarations :=
  fun _ x => x.elim (fun x => Declaration.sorts_cons_subset
    (h (Or.inr (Or.inl (Set.mem_singleton _)))) (fun _ t => h (Or.inl t)) x)
      (fun x => h (Or.inr (Or.inr x)))

/-- Select a graph atom with exactly the original operation and variable positions. -/
def selectGraph {Γ : List P.signature.SortType} (keepΓ : Declaration.sorts Γ ⊆ U.declarations)
    (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ U.declarations)
    (ρ : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output) :
    Atomic (signature U) (context Γ keepΓ) := by
  cases op <;> exact .graph (operation _ keep) (selectRenaming (operationInputs _ keep) keepΓ ρ)
    (selectVar keepΓ y)

/-- Read an atomic formula over the actual selected signature. -/
def selectAtomic {Γ : List P.signature.SortType} (a : Atomic P.signature Γ)
    (keep : Declaration.atomicSupport a ⊆ U.declarations) :
    Atomic (signature U) (context Γ (fun _ t => keep (Or.inl t))) := by
  let keepΓ : Declaration.sorts Γ ⊆ U.declarations := fun _ t => keep (Or.inl t)
  cases a with
  | eq x y => exact .eq (selectVar keepΓ x) (selectVar keepΓ y)
  | rel r ρ =>
    have keepR : Declaration.relation r ∈ U.declarations := keep (Or.inr (Set.mem_singleton _))
    exact .rel ⟨r, keepR⟩ (selectRenaming (relationInputs r keepR) keepΓ ρ)
  | domain p ρ =>
    have keepP : Declaration.partialOp p ∈ U.declarations := keep (Or.inr (Set.mem_singleton _))
    exact .domain ⟨p, keepP⟩ (selectRenaming (operationInputs (.partialOp p) keepP) keepΓ ρ)
  | graph op ρ y => exact selectGraph keepΓ op (keep (Or.inr (Set.mem_singleton _))) ρ y

/-- Read an arbitrary supported positive formula over the selected signature. -/
def selectFormula : {Γ : List P.signature.SortType} → (p : Formula P.signature Γ) →
    (keep : Declaration.formulaSupport p ⊆ U.declarations) →
    Formula (signature U) (context Γ (fun _ t => keep (Or.inl t)))
  | _, .atom a, keep => .atom (selectAtomic a keep)
  | _, .truth, _ => .truth
  | _, .falsehood, _ => .falsehood
  | _, .conj p q, keep => .conj (selectFormula p (leftSupport keep)) (selectFormula q (rightSupport keep))
  | _, .disj p q, keep => .disj (selectFormula p (leftSupport keep)) (selectFormula q (rightSupport keep))
  | _, @Formula.ex _ _ s body, keep =>
    .ex (s := ⟨s, keep (Or.inr (Or.inl (Set.mem_singleton _)))⟩) (selectFormula body (existsSupport keep))

/-- The same literal Law has a writing in the genuinely smaller vocabulary. -/
def selectLaw (law : Law P.signature) (keep : Declaration.lawBody law ⊆ U.declarations) : Law (signature U) :=
  ⟨context law.context (fun _ t => keep (Or.inl (Or.inl t))),
    selectFormula law.input (fun _ t => t.elim (fun h => keep (Or.inl (Or.inl h)))
      (fun h => keep (Or.inl (Or.inr h)))),
    selectFormula law.conclusion (fun _ t => t.elim (fun h => keep (Or.inl (Or.inl h)))
      (fun h => keep (Or.inr h)))⟩

/-- Retyping two successive renamings retypes their composite. -/
theorem selectRenaming_comp {Γ Δ Ξ : List P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepΔ : Declaration.sorts Δ ⊆ U.declarations)
    (keepΞ : Declaration.sorts Ξ ⊆ U.declarations) (ρ : Renaming Γ Δ) (τ : Renaming Δ Ξ) :
    (fun {_} i => selectRenaming keepΔ keepΞ τ (selectRenaming keepΓ keepΔ ρ i)) =
      (selectRenaming keepΓ keepΞ (fun i => τ (ρ i)) : Renaming _ _) := by
  funext s i
  simp only [selectRenaming]
  rw [ambientVar_selectVar keepΔ (ρ (ambientVar keepΓ i))]

/-- Selection commutes with lifting a renaming across an existential binder. -/
theorem selectRenaming_lift {Γ Δ : List P.signature.SortType} {s : P.signature.SortType}
    (kept : Declaration.sort s ∈ U.declarations)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepΔ : Declaration.sorts Δ ⊆ U.declarations)
    (ρ : Renaming Γ Δ) :
    (selectRenaming (Declaration.sorts_cons_subset kept keepΓ) (Declaration.sorts_cons_subset kept keepΔ) ρ.lift :
      Renaming _ _) = (Renaming.lift (selectRenaming keepΓ keepΔ ρ) (s := (⟨s, kept⟩ : SortName U)) :
        Renaming _ _) := by
  funext t i
  cases i <;> rfl

/-- Select a weakening into a context extended by one new sort. -/
theorem selectRenaming_there {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (kept : Declaration.sort s ∈ U.declarations) (keepΓ : Declaration.sorts Γ ⊆ U.declarations) :
    (selectRenaming keepΓ (Declaration.sorts_cons_subset kept keepΓ) (fun i => .there i) : Renaming _ _) =
      (fun {_} i => Var.there (t := (⟨s, kept⟩ : SortName U)) i) := by
  funext t i
  change Var.there (selectVar keepΓ (ambientVar keepΓ i)) = Var.there i
  rw [selectVar_ambientVar]

/-- Select the variable map that substitutes an existing variable for a new head. -/
theorem selectRenaming_openHead {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (x : Var Γ s) :
    (selectRenaming (Declaration.sorts_cons_subset (varKept keepΓ x) keepΓ) keepΓ (Renaming.openHead x) :
      Renaming _ _) =
      (Renaming.openHead (selectVar keepΓ x) : Renaming _ _) := by
  funext t i
  cases i with
  | here => rfl
  | there i => exact selectVar_ambientVar keepΓ i

/-- Selecting an atom commutes with reorganizing its variable positions. -/
theorem selectAtomic_rename {Γ Δ : List P.signature.SortType} (a : Atomic P.signature Γ) (ρ : Renaming Γ Δ)
    (keep : Declaration.atomicSupport a ⊆ U.declarations)
    (renamed : Declaration.atomicSupport (a.rename ρ) ⊆ U.declarations) :
    selectAtomic (a.rename ρ) renamed = (selectAtomic a keep).rename
      (selectRenaming (fun _ h => keep (Or.inl h)) (fun _ h => renamed (Or.inl h)) ρ) := by
  cases a with
  | eq x y => simp only [Atomic.rename_eq, selectAtomic, renaming_selectVar]
  | rel r vars =>
    simp only [Atomic.rename_rel, selectAtomic]
    congr 1
    exact (selectRenaming_comp _ _ _ vars ρ).symm
  | domain p vars =>
    simp only [Atomic.rename_domain, selectAtomic]
    congr 1
    exact (selectRenaming_comp _ _ _ vars ρ).symm
  | graph op vars y =>
    cases op <;> simp only [Atomic.rename_graph, selectAtomic, selectGraph, renaming_selectVar]
    all_goals
      congr 1
      exact (selectRenaming_comp _ _ _ vars ρ).symm

/-- Selecting a supported formula commutes with renaming, including across binders. -/
theorem selectFormula_rename {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    ∀ {Δ : List P.signature.SortType} (ρ : Renaming Γ Δ)
      (keep : Declaration.formulaSupport p ⊆ U.declarations)
      (renamed : Declaration.formulaSupport (p.rename ρ) ⊆ U.declarations),
      selectFormula (p.rename ρ) renamed = (selectFormula p keep).rename
        (selectRenaming (fun _ h => keep (Or.inl h)) (fun _ h => renamed (Or.inl h)) ρ) := by
  induction p with
  | atom a =>
    intro Δ ρ keep renamed
    exact congrArg Formula.atom (selectAtomic_rename a ρ keep renamed)
  | truth | falsehood => intros; rfl
  | conj p q hp hq =>
    intro Δ ρ keep renamed
    exact congrArg₂ Formula.conj (hp ρ (leftSupport keep) (leftSupport renamed))
      (hq ρ (rightSupport keep) (rightSupport renamed))
  | disj p q hp hq =>
    intro Δ ρ keep renamed
    exact congrArg₂ Formula.disj (hp ρ (leftSupport keep) (leftSupport renamed))
      (hq ρ (rightSupport keep) (rightSupport renamed))
  | @ex Γ s body ih =>
    intro Δ ρ keep renamed
    let kept : Declaration.sort s ∈ U.declarations := keep (Or.inr (Or.inl (Set.mem_singleton _)))
    let free : Declaration.sorts Γ ⊆ U.declarations := fun _ h => keep (Or.inl h)
    let target : Declaration.sorts Δ ⊆ U.declarations := fun _ h => renamed (Or.inl h)
    have inside := ih ρ.lift (existsSupport keep) (existsSupport renamed)
    have underBinder := congrArg (fun r : Renaming
        (context (s :: Γ) (Declaration.sorts_cons_subset kept free))
        (context (s :: Δ) (Declaration.sorts_cons_subset kept target)) =>
      (selectFormula body (existsSupport keep)).rename r) (selectRenaming_lift kept free target ρ)
    exact congrArg Formula.ex (inside.trans underBinder)

/-- Selecting the substitution of a variable for an existential head preserves its position. -/
theorem selectFormula_openHead {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (p : Formula P.signature (s :: Γ)) (x : Var Γ s) (keep : Declaration.formulaSupport p ⊆ U.declarations)
    (after : Declaration.formulaSupport (p.rename (Renaming.openHead x)) ⊆ U.declarations) :
    selectFormula (p.rename (Renaming.openHead x)) after =
      (selectFormula p keep).rename (Renaming.openHead (selectVar (fun _ h => after (Or.inl h)) x)) := by
  let free : Declaration.sorts Γ ⊆ U.declarations := fun _ h => after (Or.inl h)
  have changeMap := congrArg (fun r : Renaming
      (context (s :: Γ) (Declaration.sorts_cons_subset (varKept free x) free)) (context Γ free) =>
    (selectFormula p keep).rename r) (selectRenaming_openHead free x)
  exact (selectFormula_rename p (Renaming.openHead x) keep after).trans changeMap

/-- Selecting a weakened formula weakens the selected formula by the same head sort. -/
theorem selectFormula_there {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (p : Formula P.signature Γ) (keep : Declaration.formulaSupport p ⊆ U.declarations)
    (after : Declaration.formulaSupport (p.rename (fun i => Var.there (t := s) i)) ⊆ U.declarations) :
    selectFormula (p.rename (fun i => Var.there (t := s) i)) after =
      (selectFormula p keep).rename (fun i => Var.there
        (t := (⟨s, after (Or.inl ⟨s, List.mem_cons_self, rfl⟩)⟩ : SortName U)) i) := by
  let free : Declaration.sorts Γ ⊆ U.declarations := fun _ h => keep (Or.inl h)
  let head : Declaration.sort s ∈ U.declarations := after (Or.inl ⟨s, List.mem_cons_self, rfl⟩)
  have changeMap := congrArg (fun r : Renaming (context Γ free)
      (context (s :: Γ) (Declaration.sorts_cons_subset head free)) => (selectFormula p keep).rename r)
    (selectRenaming_there head free)
  exact (selectFormula_rename p (fun i => Var.there (t := s) i) keep after).trans changeMap

end DeclarationContext.Selected
end SHIGURE
