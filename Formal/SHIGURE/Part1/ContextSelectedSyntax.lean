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
    Declaration.formulaSupport p ⊆ U.declarations := by
  rw [Declaration.formulaSupport_eq]
  exact fun _ x => x.elim (fun x => h (Or.inl x)) (fun x => h (Or.inr (Or.inl x)))

/-- Split support of the right side of a binary formula. -/
theorem rightSupport {Γ : List P.signature.SortType} {p q : Formula P.signature Γ}
    (h : Declaration.sorts Γ ∪ (Declaration.formula p ∪ Declaration.formula q) ⊆ U.declarations) :
    Declaration.formulaSupport q ⊆ U.declarations := by
  rw [Declaration.formulaSupport_eq]
  exact fun _ x => x.elim (fun x => h (Or.inl x)) (fun x => h (Or.inr (Or.inr x)))

/-- Include the bound sort and the free context of an existential body. -/
theorem existsSupport {Γ : List P.signature.SortType} {s : P.signature.SortType}
    {p : Formula P.signature (s :: Γ)} (h : Declaration.formulaSupport p.ex ⊆ U.declarations) :
    Declaration.formulaSupport p ⊆ U.declarations :=
  (Declaration.formulaSupport_ex_body p).trans h

/-- Select a graph atom with exactly the original operation and variable positions. -/
def selectGraph {Γ : List P.signature.SortType} (keepΓ : Declaration.sorts Γ ⊆ U.declarations)
    (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ U.declarations)
    (ρ : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output) :
    Atomic (signature U) (context Γ keepΓ) :=
  .graph (operation op keep)
    (fun {s} i => selectRenaming (operationInputs op keep) keepΓ ρ
      (cast (congrArg (Var · s) (operation_selectedInputs (keep := keep) rfl)) i))
    (cast (congrArg (Var (context Γ keepΓ)) (operation_selectedOutput (keep := keep) rfl).symm)
      (selectVar keepΓ y))

/-- Select a graph at the actual input and output types of an equal retained operation. -/
theorem selectGraph_atOperation {Γ : List P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (selected : Operation (signature U))
    (same : operation op keep = selected) (ρ : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output) :
    selectGraph keepΓ op keep ρ y = .graph selected
      (fun {s} i => selectRenaming (operationInputs op keep) keepΓ ρ
        (cast (congrArg (Var · s) (operation_selectedInputs same)) i))
      (cast (congrArg (Var (context Γ keepΓ)) (operation_selectedOutput same).symm)
        (selectVar keepΓ y)) := by
  cases same
  rfl

/-- A selected graph of a retained total operation keeps its original argument
and result positions. This is the total branch of the structural rule comparison. -/
theorem selectGraph_total {Γ : List P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (f : P.signature.Total)
    (keep : Declaration.ofOperation (.total f) ∈ U.declarations)
    (ρ : Renaming (P.signature.totalArity f).inputs Γ) (y : Var Γ (P.signature.totalArity f).output) :
    selectGraph keepΓ (.total f) keep ρ y =
      .graph (.total ⟨f, Declaration.ofOperation_total f ▸ keep⟩)
        (selectRenaming (operationInputs (.total f) keep) keepΓ ρ) (selectVar keepΓ y) :=
  rfl

/-- A selected graph of a retained partial operation keeps its original
argument positions and result, with the same partial-operation tag. -/
theorem selectGraph_partialOp {Γ : List P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (p : P.signature.Partial)
    (keep : Declaration.ofOperation (.partialOp p) ∈ U.declarations)
    (ρ : Renaming (P.signature.partialArity p).inputs Γ) (y : Var Γ (P.signature.partialArity p).output) :
    selectGraph keepΓ (.partialOp p) keep ρ y =
      .graph (.partialOp ⟨p, Declaration.ofOperation_partialOp p ▸ keep⟩)
        (selectRenaming (operationInputs (.partialOp p) keep) keepΓ ρ)
        (selectVar keepΓ y) :=
  rfl

/-- A selected graph of a retained quantity keeps its argument and result
positions under the quantity tag. -/
theorem selectGraph_quantity {Γ : List P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (q : P.signature.Quantity)
    (keep : Declaration.ofOperation (.quantity q) ∈ U.declarations)
    (ρ : Renaming (P.signature.quantityArity q).inputs Γ) (y : Var Γ (P.signature.quantityArity q).output) :
    selectGraph keepΓ (.quantity q) keep ρ y =
      .graph (.quantity ⟨q, Declaration.ofOperation_quantity q ▸ keep⟩)
        (selectRenaming (operationInputs (.quantity q) keep) keepΓ ρ) (selectVar keepΓ y) :=
  rfl

/-- Read an atomic formula over the actual selected signature. -/
def selectAtomic {Γ : List P.signature.SortType} (a : Atomic P.signature Γ)
    (keep : Declaration.atomicSupport a ⊆ U.declarations) :
    Atomic (signature U) (context Γ ((Declaration.sorts_subset_atomicSupport a).trans keep)) := by
  let keepΓ : Declaration.sorts Γ ⊆ U.declarations := (Declaration.sorts_subset_atomicSupport a).trans keep
  cases a with
  | eq x y => exact .eq (selectVar keepΓ x) (selectVar keepΓ y)
  | rel r ρ =>
    have keepR : Declaration.relation r ∈ U.declarations := keep (Declaration.relation_mem_atomicSupport r ρ)
    exact .rel ⟨r, keepR⟩ (selectRenaming (relationInputs r keepR) keepΓ ρ)
  | domain p ρ =>
    have keepP : Declaration.partialOp p ∈ U.declarations := keep (Declaration.domain_mem_atomicSupport p ρ)
    exact .domain ⟨p, keepP⟩
      (fun {s} i => selectRenaming
        (operationInputs (.partialOp p) (Declaration.ofOperation_partialOp_mem p keepP)) keepΓ ρ
        (cast (congrArg (Var · s) (signature_partialInputs ⟨p, keepP⟩)) i))
  | graph op ρ y => exact selectGraph keepΓ op (keep (Declaration.graph_mem_atomicSupport op ρ y)) ρ y

/-- Selecting an equality retains the compared positions in the selected context. -/
theorem selectAtomic_eq {Γ : List P.signature.SortType} {s : P.signature.SortType} (x y : Var Γ s)
    (keep : Declaration.atomicSupport (Atomic.eq (sig := P.signature) x y) ⊆ U.declarations) :
    selectAtomic (.eq x y) keep =
      .eq (selectVar ((Declaration.sorts_subset_atomicSupport (.eq x y)).trans keep) x)
        (selectVar ((Declaration.sorts_subset_atomicSupport (.eq x y)).trans keep) y) :=
  rfl

/-- Selecting a relation reads its retained name and reindexes its arguments. -/
theorem selectAtomic_rel {Γ : List P.signature.SortType} (r : P.signature.Rel)
    (ρ : Renaming (P.signature.relInputs r) Γ) (keep : Declaration.atomicSupport (.rel r ρ) ⊆ U.declarations) :
    selectAtomic (.rel r ρ) keep =
      .rel ⟨r, keep (Declaration.relation_mem_atomicSupport r ρ)⟩
        (selectRenaming (relationInputs r (keep (Declaration.relation_mem_atomicSupport r ρ)))
          ((Declaration.sorts_subset_atomicSupport (.rel r ρ)).trans keep) ρ) :=
  rfl

/-- Selecting a domain atom reindexes the retained partial operation's arguments. -/
theorem selectAtomic_domain {Γ : List P.signature.SortType} (p : P.signature.Partial)
    (ρ : Renaming (P.signature.partialArity p).inputs Γ)
    (keep : Declaration.atomicSupport (.domain p ρ) ⊆ U.declarations) :
    selectAtomic (.domain p ρ) keep =
      .domain ⟨p, keep (Declaration.domain_mem_atomicSupport p ρ)⟩
        (selectRenaming (operationInputs (.partialOp p)
          (Declaration.ofOperation_partialOp_mem p (keep (Declaration.domain_mem_atomicSupport p ρ))))
          ((Declaration.sorts_subset_atomicSupport (.domain p ρ)).trans keep) ρ) :=
  rfl

/-- A selected domain atom reads inputs at the partial operation's actual retained arity. -/
theorem selectAtomic_domain_cast {Γ : List P.signature.SortType} (p : P.signature.Partial)
    (ρ : Renaming (P.signature.partialArity p).inputs Γ)
    (keep : Declaration.atomicSupport (.domain p ρ) ⊆ U.declarations)
    (d : Declaration.partialOp p ∈ U.declarations) :
    selectAtomic (.domain p ρ) keep =
      .domain ⟨p, d⟩ (fun {s} i => selectRenaming
        (operationInputs (.partialOp p) (Declaration.ofOperation_partialOp_mem p d))
        ((Declaration.sorts_subset_atomicSupport (.domain p ρ)).trans keep) ρ
        (cast (congrArg (Var · s) (signature_partialInputs ⟨p, d⟩)) i)) :=
  rfl

/-- A selected graph atom uses the retained operation and its reindexed positions. -/
theorem selectAtomic_graph {Γ : List P.signature.SortType} (op : Operation P.signature)
    (ρ : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output)
    (keep : Declaration.atomicSupport (.graph op ρ y) ⊆ U.declarations) :
    selectAtomic (.graph op ρ y) keep =
      selectGraph ((Declaration.sorts_subset_atomicSupport (.graph op ρ y)).trans keep) op
        (keep (Declaration.graph_mem_atomicSupport op ρ y)) ρ y :=
  rfl

/-- Read an arbitrary supported positive formula over the selected signature. -/
def selectFormula : {Γ : List P.signature.SortType} → (p : Formula P.signature Γ) →
    (keep : Declaration.formulaSupport p ⊆ U.declarations) →
    Formula (signature U) (context Γ ((Declaration.sorts_subset_formulaSupport p).trans keep))
  | _, .atom a, keep => .atom (selectAtomic a ((Declaration.formulaSupport_atom a).ge.trans keep))
  | _, .truth, _ => .truth
  | _, .falsehood, _ => .falsehood
  | _, .conj p q, keep =>
    .conj (selectFormula p ((Declaration.binarySupport_left (Declaration.formula_conj p q)).trans keep))
      (selectFormula q ((Declaration.binarySupport_right (Declaration.formula_conj p q)).trans keep))
  | _, .disj p q, keep =>
    .disj (selectFormula p ((Declaration.binarySupport_left (Declaration.formula_disj p q)).trans keep))
      (selectFormula q ((Declaration.binarySupport_right (Declaration.formula_disj p q)).trans keep))
  | _, @Formula.ex _ _ s body, keep =>
    .ex (s := ⟨s, keep (Declaration.boundSort_mem_formulaSupport body)⟩) (selectFormula body (existsSupport keep))

/-- Selecting an atomic formula uses the primitive comparison in Proposition 3.2. -/
theorem selectFormula_atom {Γ : List P.signature.SortType} (a : Atomic P.signature Γ)
    (keep : Declaration.formulaSupport (.atom a) ⊆ U.declarations) :
    selectFormula (.atom a) keep = .atom (selectAtomic a ((Declaration.formulaSupport_atom a).ge.trans keep)) :=
  rfl

/-- Truth in the selected context has no further primitive dependency. -/
theorem selectFormula_truth {Γ : List P.signature.SortType}
    (keep : Declaration.formulaSupport (Formula.truth (sig := P.signature) (Γ := Γ)) ⊆ U.declarations) :
    selectFormula .truth keep = .truth :=
  rfl

/-- Falsehood remains falsehood under the selected context. -/
theorem selectFormula_falsehood {Γ : List P.signature.SortType}
    (keep : Declaration.formulaSupport (Formula.falsehood (sig := P.signature) (Γ := Γ)) ⊆ U.declarations) :
    selectFormula .falsehood keep = .falsehood :=
  rfl

/-- Selection keeps a conjunction by selecting each supported part. -/
theorem selectFormula_conj {Γ : List P.signature.SortType} (p q : Formula P.signature Γ)
    (keep : Declaration.formulaSupport (p.conj q) ⊆ U.declarations) :
    selectFormula (p.conj q) keep =
      .conj (selectFormula p ((Declaration.binarySupport_left (Declaration.formula_conj p q)).trans keep))
      (selectFormula q ((Declaration.binarySupport_right (Declaration.formula_conj p q)).trans keep)) :=
  rfl

/-- Selection keeps a disjunction by selecting each supported alternative. -/
theorem selectFormula_disj {Γ : List P.signature.SortType} (p q : Formula P.signature Γ)
    (keep : Declaration.formulaSupport (p.disj q) ⊆ U.declarations) :
    selectFormula (p.disj q) keep =
      .disj (selectFormula p ((Declaration.binarySupport_left (Declaration.formula_disj p q)).trans keep))
      (selectFormula q ((Declaration.binarySupport_right (Declaration.formula_disj p q)).trans keep)) :=
  rfl

/-- Selection retains the bound sort and the body's typed positions of an existential. -/
theorem selectFormula_ex {Γ : List P.signature.SortType} {s : P.signature.SortType} (p : Formula P.signature (s :: Γ))
    (keep : Declaration.formulaSupport p.ex ⊆ U.declarations) :
    selectFormula p.ex keep =
      .ex (s := ⟨s, keep (Declaration.boundSort_mem_formulaSupport p)⟩) (selectFormula p (existsSupport keep)) :=
  rfl

/-- Select an existential using explicit transport of the retained body's context. -/
theorem selectFormula_ex_cast {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (p : Formula P.signature (s :: Γ)) (keep : Declaration.formulaSupport p.ex ⊆ U.declarations) :
    selectFormula p.ex keep =
      .ex (s := ⟨s, keep (Declaration.boundSort_mem_formulaSupport p)⟩)
        (cast (congrArg (Formula (signature U)) (context_cons s Γ
          ((Declaration.sorts_subset_formulaSupport p).trans (existsSupport keep))))
          (selectFormula p (existsSupport keep))) :=
  selectFormula_ex p keep

/-- The same literal Law has a writing in the genuinely smaller vocabulary. -/
def selectLaw (law : Law P.signature) (keep : Declaration.lawBody law ⊆ U.declarations) : Law (signature U) :=
  ⟨context law.context ((Declaration.sorts_subset_lawBody law).trans keep),
    selectFormula law.input ((Declaration.formulaSupport_input_subset_lawBody law).trans keep),
    selectFormula law.conclusion ((Declaration.formulaSupport_conclusion_subset_lawBody law).trans keep)⟩

/-- The selected Law in Definition 3.1 uses exactly the retained context
sorts, input and conclusion of its written Law. -/
theorem selectLaw_eq (law : Law P.signature) (keep : Declaration.lawBody law ⊆ U.declarations) :
    selectLaw law keep =
      ⟨context law.context ((Declaration.sorts_subset_lawBody law).trans keep),
        selectFormula law.input ((Declaration.formulaSupport_input_subset_lawBody law).trans keep),
        selectFormula law.conclusion ((Declaration.formulaSupport_conclusion_subset_lawBody law).trans keep)⟩ :=
  rfl

/-- The selected variable map of an identity is an identity. -/
theorem selectRenaming_id {Γ : List P.signature.SortType} (kept : Declaration.sorts Γ ⊆ U.declarations) :
    (selectRenaming kept kept (fun i => i) : Renaming _ _) = (fun {_} i => i) := by
  funext _ i
  rw [selectRenaming_apply]
  exact selectVar_ambientVar kept i

/-- Retyping two successive renamings retypes their composite. -/
theorem selectRenaming_comp {Γ Δ Ξ : List P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepΔ : Declaration.sorts Δ ⊆ U.declarations)
    (keepΞ : Declaration.sorts Ξ ⊆ U.declarations) (ρ : Renaming Γ Δ) (τ : Renaming Δ Ξ) :
    (fun {_} i => selectRenaming keepΔ keepΞ τ (selectRenaming keepΓ keepΔ ρ i)) =
      (selectRenaming keepΓ keepΞ (fun i => τ (ρ i)) : Renaming _ _) := by
  funext s i
  simp only [selectRenaming_apply]
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
  cases i with
  | here => simp only [selectRenaming_apply, ambientVar_here, Renaming.lift_here, selectVar_here]
  | there i => simp only [selectRenaming_apply, ambientVar_there, Renaming.lift_there, selectVar_there]

/-- The selected lifted renaming agrees with the lift on both explicit cons contexts. -/
theorem selectRenaming_lift_cast {Γ Δ : List P.signature.SortType} {s : P.signature.SortType}
    (kept : Declaration.sort s ∈ U.declarations)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepΔ : Declaration.sorts Δ ⊆ U.declarations)
    (ρ : Renaming Γ Δ) :
    @cast _ _ (congrArg₂ Renaming (context_cons s Γ (Declaration.sorts_cons_subset kept keepΓ))
      (context_cons s Δ (Declaration.sorts_cons_subset kept keepΔ)))
      (selectRenaming (Declaration.sorts_cons_subset kept keepΓ) (Declaration.sorts_cons_subset kept keepΔ) ρ.lift) =
      (Renaming.lift (selectRenaming keepΓ keepΔ ρ) (s := (⟨s, kept⟩ : SortName U)) : Renaming _ _) := by
  funext t i
  rw [Renaming.cast_context_apply (context_cons s Γ (Declaration.sorts_cons_subset kept keepΓ))
    (context_cons s Δ (Declaration.sorts_cons_subset kept keepΔ)), selectRenaming_apply]
  cases i with
  | here => rw [ambientVar_cast_here, Renaming.lift_here, selectVar_cast_here, Renaming.lift_here]
  | there i =>
    rw [ambientVar_cast_there, Renaming.lift_there, selectVar_cast_there, Renaming.lift_there,
      selectRenaming_apply]

/-- Select a weakening into a context extended by one new sort. -/
theorem selectRenaming_there {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (kept : Declaration.sort s ∈ U.declarations) (keepΓ : Declaration.sorts Γ ⊆ U.declarations) :
    (selectRenaming keepΓ (Declaration.sorts_cons_subset kept keepΓ) (fun i => .there i) : Renaming _ _) =
      (fun {_} i => Var.there (t := (⟨s, kept⟩ : SortName U)) i) := by
  funext t i
  simp only [selectRenaming_apply, selectVar_there, selectVar_ambientVar]

/-- Transport the target of a selected variable map across a newly inserted head. -/
theorem selectRenaming_there_cast {Γ Δ : List P.signature.SortType} {s : P.signature.SortType}
    (kept : Declaration.sort s ∈ U.declarations)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepΔ : Declaration.sorts Δ ⊆ U.declarations)
    (ρ : Renaming Γ Δ) :
    @cast _ _ (congrArg (Renaming (context Γ keepΓ))
      (context_cons s Δ (Declaration.sorts_cons_subset kept keepΔ)))
      (selectRenaming keepΓ (Declaration.sorts_cons_subset kept keepΔ) (fun i => .there (ρ i))) =
      (fun {_} i => Var.there (t := (⟨s, kept⟩ : SortName U)) (selectRenaming keepΓ keepΔ ρ i)) := by
  funext t i
  rw [Renaming.cast_target_apply (context_cons s Δ (Declaration.sorts_cons_subset kept keepΔ)),
    selectRenaming_apply, selectVar_cast_there, selectRenaming_apply]

/-- Select the variable map that substitutes an existing variable for a new head. -/
theorem selectRenaming_openHead {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (x : Var Γ s) :
    (selectRenaming (Declaration.sorts_cons_subset (varKept keepΓ x) keepΓ) keepΓ (Renaming.openHead x) :
      Renaming _ _) =
      (Renaming.openHead (selectVar keepΓ x) : Renaming _ _) := by
  funext t i
  cases i with
  | here => simp only [selectRenaming_apply, ambientVar_here, Renaming.openHead_here]
  | there i =>
    simp only [selectRenaming_apply, ambientVar_there, Renaming.openHead_there, selectVar_ambientVar]

/-- Selecting an atom commutes with reorganizing its variable positions. -/
theorem selectAtomic_rename {Γ Δ : List P.signature.SortType} (a : Atomic P.signature Γ) (ρ : Renaming Γ Δ)
    (keep : Declaration.atomicSupport a ⊆ U.declarations)
    (renamed : Declaration.atomicSupport (a.rename ρ) ⊆ U.declarations) :
    selectAtomic (a.rename ρ) renamed = (selectAtomic a keep).rename
      (selectRenaming ((Declaration.sorts_subset_atomicSupport a).trans keep)
        ((Declaration.sorts_subset_atomicSupport (a.rename ρ)).trans renamed) ρ) := by
  cases a with
  | eq x y =>
    simp only [Atomic.rename_eq] at renamed ⊢
    simp only [selectAtomic_eq, Atomic.rename_eq, renaming_selectVar]
  | rel r vars =>
    simp only [Atomic.rename_rel] at renamed ⊢
    simp only [selectAtomic_rel, Atomic.rename_rel]
    congr 1
    exact (selectRenaming_comp _ _ _ vars ρ).symm
  | domain p vars =>
    simp only [Atomic.rename_domain] at renamed ⊢
    simp only [selectAtomic_domain, Atomic.rename_domain]
    congr 1
    exact (selectRenaming_comp _ _ _ vars ρ).symm
  | graph op vars y =>
    cases op <;> simp only [Atomic.rename_graph] at renamed ⊢
    all_goals simp only [selectAtomic_graph, selectGraph_total, selectGraph_partialOp,
      selectGraph_quantity, Atomic.rename_graph, renaming_selectVar]
    all_goals
      congr 1
      exact (selectRenaming_comp _ _ _ vars ρ).symm

/-- Selecting a supported formula commutes with renaming, including across binders. -/
theorem selectFormula_rename {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    ∀ {Δ : List P.signature.SortType} (ρ : Renaming Γ Δ)
      (keep : Declaration.formulaSupport p ⊆ U.declarations)
      (renamed : Declaration.formulaSupport (p.rename ρ) ⊆ U.declarations),
      selectFormula (p.rename ρ) renamed = (selectFormula p keep).rename
        (selectRenaming ((Declaration.sorts_subset_formulaSupport p).trans keep)
          ((Declaration.sorts_subset_formulaSupport (p.rename ρ)).trans renamed) ρ) := by
  induction p with
  | atom a =>
    intro Δ ρ keep renamed
    simp only [Formula.rename_atom, selectFormula_atom] at renamed ⊢
    exact congrArg Formula.atom (selectAtomic_rename a ρ
      ((Declaration.formulaSupport_atom a).ge.trans keep)
      ((Declaration.formulaSupport_atom (a.rename ρ)).ge.trans renamed))
  | truth =>
    intro Δ ρ keep renamed
    simp only [Formula.rename_truth, selectFormula_truth] at renamed ⊢
  | falsehood =>
    intro Δ ρ keep renamed
    simp only [Formula.rename_falsehood, selectFormula_falsehood] at renamed ⊢
  | conj p q hp hq =>
    intro Δ ρ keep renamed
    simp only [Formula.rename_conj, selectFormula_conj] at renamed ⊢
    have written := Declaration.formula_conj (P := P) p q
    have moved := Declaration.formula_conj (P := P) (p.rename ρ) (q.rename ρ)
    exact congrArg₂ Formula.conj
      (hp ρ ((Declaration.binarySupport_left written).trans keep) ((Declaration.binarySupport_left moved).trans renamed))
      (hq ρ ((Declaration.binarySupport_right written).trans keep) ((Declaration.binarySupport_right moved).trans renamed))
  | disj p q hp hq =>
    intro Δ ρ keep renamed
    simp only [Formula.rename_disj, selectFormula_disj] at renamed ⊢
    have written := Declaration.formula_disj (P := P) p q
    have moved := Declaration.formula_disj (P := P) (p.rename ρ) (q.rename ρ)
    exact congrArg₂ Formula.disj
      (hp ρ ((Declaration.binarySupport_left written).trans keep) ((Declaration.binarySupport_left moved).trans renamed))
      (hq ρ ((Declaration.binarySupport_right written).trans keep) ((Declaration.binarySupport_right moved).trans renamed))
  | @ex Γ s body ih =>
    intro Δ ρ keep renamed
    simp only [Formula.rename_ex, selectFormula_ex_cast] at renamed ⊢
    let kept : Declaration.sort s ∈ U.declarations := keep (Declaration.boundSort_mem_formulaSupport body)
    let free : Declaration.sorts Γ ⊆ U.declarations := (Declaration.sorts_subset_formulaSupport body.ex).trans keep
    let target : Declaration.sorts Δ ⊆ U.declarations := (Declaration.sorts_subset_formulaSupport (body.rename ρ.lift).ex).trans renamed
    have inside := ih ρ.lift (existsSupport keep) (existsSupport renamed)
    let oldCtx := context_cons s Γ (Declaration.sorts_cons_subset kept free)
    let newCtx := context_cons s Δ (Declaration.sorts_cons_subset kept target)
    have transported := congrArg (cast (congrArg (Formula (signature U)) newCtx)) inside
    rw [Formula.rename_cast_context oldCtx newCtx] at transported
    let selected : SortName U := ⟨s, kept⟩
    have lifted := congrArg (fun (rename : Renaming (selected :: context Γ free) (selected :: context Δ target)) =>
      (cast (congrArg (Formula (signature U)) oldCtx) (selectFormula body (existsSupport keep))).rename rename)
      (selectRenaming_lift_cast kept free target ρ)
    exact congrArg Formula.ex (transported.trans lifted)

/-- Selecting the substitution of a variable for an existential head preserves its position. -/
theorem selectFormula_openHead {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (p : Formula P.signature (s :: Γ)) (x : Var Γ s) (keep : Declaration.formulaSupport p ⊆ U.declarations)
    (after : Declaration.formulaSupport (p.rename (Renaming.openHead x)) ⊆ U.declarations) :
    selectFormula (p.rename (Renaming.openHead x)) after =
      (selectFormula p keep).rename (Renaming.openHead
        (selectVar ((Declaration.sorts_subset_formulaSupport (p.rename (Renaming.openHead x))).trans after) x)) := by
  let free : Declaration.sorts Γ ⊆ U.declarations := (Declaration.sorts_subset_formulaSupport (p.rename (Renaming.openHead x))).trans after
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
        (t := (⟨s, after (Declaration.sorts_subset_formulaSupport _ (Declaration.sort_mem_sorts List.mem_cons_self))⟩ : SortName U)) i) := by
  let free : Declaration.sorts Γ ⊆ U.declarations := (Declaration.sorts_subset_formulaSupport p).trans keep
  let head : Declaration.sort s ∈ U.declarations := after (Declaration.sorts_subset_formulaSupport _ (Declaration.sort_mem_sorts List.mem_cons_self))
  have changeMap := congrArg (fun r : Renaming (context Γ free)
      (context (s :: Γ) (Declaration.sorts_cons_subset head free)) => (selectFormula p keep).rename r)
    (selectRenaming_there head free)
  exact (selectFormula_rename p (fun i => Var.there (t := s) i) keep after).trans changeMap

/-- Opening a selected head uses the body transported to the explicit cons context. -/
theorem selectFormula_openHead_cast {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (p : Formula P.signature (s :: Γ)) (x : Var Γ s) (keep : Declaration.formulaSupport p ⊆ U.declarations)
    (after : Declaration.formulaSupport (p.rename (Renaming.openHead x)) ⊆ U.declarations) :
    selectFormula (p.rename (Renaming.openHead x)) after =
      (cast (congrArg (Formula (signature U)) (context_cons s Γ
        ((Declaration.sorts_subset_formulaSupport p).trans keep))) (selectFormula p keep)).rename
          (Renaming.openHead
            (selectVar ((Declaration.sorts_subset_formulaSupport (p.rename (Renaming.openHead x))).trans after) x)) :=
  selectFormula_openHead p x keep after

/-- Weakening into the selected cons context keeps the explicit retained head sort. -/
theorem selectFormula_there_cast {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (p : Formula P.signature Γ) (keep : Declaration.formulaSupport p ⊆ U.declarations)
    (after : Declaration.formulaSupport (p.rename (fun i => Var.there (t := s) i)) ⊆ U.declarations) :
    cast (congrArg (Formula (signature U)) (context_cons s Γ
      ((Declaration.sorts_subset_formulaSupport _).trans after)))
      (selectFormula (p.rename (fun i => Var.there (t := s) i)) after) =
      (selectFormula p keep).rename (fun i => Var.there
        (t := (⟨s, after (Declaration.sorts_subset_formulaSupport _ (Declaration.sort_mem_sorts List.mem_cons_self))⟩ : SortName U)) i) :=
  selectFormula_there p keep after

/-- An equality of written Laws identifies their selected Laws as well. -/
theorem selectLaw_congr {p q : Law P.signature} (same : p = q)
    (hp : Declaration.lawBody p ⊆ U.declarations) (hq : Declaration.lawBody q ⊆ U.declarations) :
    selectLaw p hp = selectLaw q hq := by
  subst q
  rfl

end DeclarationContext.Selected
end SHIGURE
