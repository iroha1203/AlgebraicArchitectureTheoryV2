import Formal.SHIGURE.Part1.ContextPresentation
import Formal.SHIGURE.Part1.RestrictedEvaluation

/-! # Evaluation after declaration restriction

The common carrier maps are indexed by retained sorts. Tuples are mapped
position by position. Restriction preserves quantifier witnesses because the
carrier maps used for restriction are bijective at every retained sort.
-/

universe u

namespace SHIGURE
namespace DeclarationContext

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}

/-- The declarations of a context's tail also occur in the context with its head. -/
theorem tailSortsSubset (s : P.signature.SortType) (Γ : List P.signature.SortType) :
    Declaration.sorts (P := P) Γ ⊆ Declaration.sorts (s :: Γ) := by
  rw [Declaration.sorts_eq_image, Declaration.sorts_eq_image]
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, List.mem_cons_of_mem _ ht, rfl⟩

/-- Carrier maps indexed only by a context's retained sorts. -/
abbrev CarrierMap (U : DeclarationContext P) (X Y : P.signature.SortType → Type u) :=
  ∀ s, Declaration.sort s ∈ U.declarations → X s → Y s

/-- A retained operation's input sorts occur among its dependencies. -/
theorem operationInputs (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) :
    Declaration.sorts op.arity.inputs ⊆ U.declarations :=
  (tailSortsSubset (P := P) op.arity.output op.arity.inputs).trans
    ((Declaration.operationSorts_subset_dependsOn op).trans (U.closed keep))

/-- A retained operation's result sort occurs among its dependencies. -/
theorem operationOutput (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) :
    Declaration.sort op.arity.output ∈ U.declarations := by
  apply U.closed keep (Declaration.operationSorts_subset_dependsOn op ?_)
  rw [Declaration.sorts_eq_image]
  exact ⟨_, List.mem_cons_self, rfl⟩

/-- A retained relation requires all its input sorts. -/
theorem relationInputs (r : P.signature.Rel) (keep : Declaration.relation r ∈ U.declarations) :
    Declaration.sorts (P.signature.relInputs r) ⊆ U.declarations := by
  rw [← Declaration.relation_dependencies r]
  exact U.closed keep

/-- Retaining all the variable positions retains the sort of each variable. -/
theorem varKept {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (var : Var Γ s) :
    Declaration.sort s ∈ U.declarations :=
  keep (by
    rw [Declaration.sorts_eq_image]
    exact ⟨s, var.sort_mem, rfl⟩)

/-- Map an assignment along the carrier maps at its retained positions. -/
def mapAssignment {X Y : P.signature.SortType → Type u} (f : CarrierMap U X Y)
    {Γ : List P.signature.SortType} (keep : Declaration.sorts Γ ⊆ U.declarations)
    (e : Assignment X Γ) : Assignment Y Γ :=
  ⟨fun var => f _ (varKept keep var) (e var)⟩

/-- A mapped assignment reads the mapped value at each original variable. -/
@[simp] theorem mapAssignment_apply {X Y : P.signature.SortType → Type u} (f : CarrierMap U X Y)
    {Γ : List P.signature.SortType} (keep : Declaration.sorts Γ ⊆ U.declarations)
    (e : Assignment X Γ) {s : P.signature.SortType} (var : Var Γ s) :
    mapAssignment f keep e var = f s (varKept keep var) (e var) :=
  rfl

/-- Mapping assigns every variable its original value for identity carrier maps. -/
@[simp] theorem mapAssignment_id {X : P.signature.SortType → Type u}
    {Γ : List P.signature.SortType} (keep : Declaration.sorts Γ ⊆ U.declarations)
    (e : Assignment X Γ) : mapAssignment (fun _ _ x => x) keep e = e :=
  Assignment.ext fun _ => rfl

/-- Mapping twice composes the two carrier maps at every retained position. -/
theorem mapAssignment_comp {X Y Z : P.signature.SortType → Type u}
    (f : CarrierMap V X Y) (g : CarrierMap U Y Z) (inside : V ≤ U)
    {Γ : List P.signature.SortType} (keep : Declaration.sorts Γ ⊆ V.declarations) (e : Assignment X Γ) :
    mapAssignment g (fun _ hd => inside (keep hd)) (mapAssignment f keep e) =
      mapAssignment (fun s h x => g s (inside h) (f s h x)) keep e :=
  Assignment.ext fun _ => rfl

/-- Mapping and selecting variable positions commute. -/
theorem mapAssignment_pull {X Y : P.signature.SortType → Type u} (f : CarrierMap U X Y)
    {Γ Δ : List P.signature.SortType} (keepΓ : Declaration.sorts Γ ⊆ U.declarations)
    (keepΔ : Declaration.sorts Δ ⊆ U.declarations) (ρ : Renaming Γ Δ) (e : Assignment X Δ) :
    mapAssignment f keepΓ (e.pull ρ) = (mapAssignment f keepΔ e).pull ρ :=
  Assignment.ext fun _ => rfl

/-- The binder and all old positions map using their own carrier map. -/
theorem mapAssignment_cons {X Y : P.signature.SortType → Type u} (f : CarrierMap U X Y)
    {Γ : List P.signature.SortType} {s : P.signature.SortType} (keepS : Declaration.sort s ∈ U.declarations)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (x : X s) (e : Assignment X Γ) :
    mapAssignment f (Declaration.sorts_cons_subset keepS keepΓ) (Assignment.cons x e) =
      Assignment.cons (f s keepS x) (mapAssignment f keepΓ e) := by
  apply Assignment.ext
  intro _ var
  cases var <;> rfl

/-- Maps agreeing on the retained sorts induce equal maps on every supported tuple. -/
theorem mapAssignment_congr {X Y : P.signature.SortType → Type u} {f g : CarrierMap U X Y}
    (same : ∀ s keep x, f s keep x = g s keep x)
    {Γ : List P.signature.SortType} (keep : Declaration.sorts Γ ⊆ U.declarations) (e : Assignment X Γ) :
    mapAssignment f keep e = mapAssignment g keep e :=
  Assignment.ext fun var => same _ _ (e var)

end DeclarationContext

namespace RestrictedEvaluation

open DeclarationContext

variable {P : PrimitivePresentation.{u}} {U V W : DeclarationContext P}
  {X Y Z : P.signature.SortType → Type u}

/-- Retained evaluation data are equal if all primitive relation, domain and graph facts agree. -/
@[ext] theorem ext {A B : RestrictedEvaluation U X}
    (relation : ∀ r kept e, A.relation r kept e ↔ B.relation r kept e)
    (domain : ∀ p kept e, A.domain p kept e ↔ B.domain p kept e)
    (graph : ∀ op kept e y, A.graph op kept e y ↔ B.graph op kept e y) : A = B := by
  cases A with
  | mk RA DA GA =>
    cases B with
    | mk RB DB GB =>
      have sameRel : RA = RB := funext fun r => funext fun kept => funext fun e => propext (relation r kept e)
      have sameDom : DA = DB := funext fun p => funext fun kept => funext fun e => propext (domain p kept e)
      have sameGraph : GA = GB := funext fun op => funext fun kept =>
        funext fun e => funext fun y => propext (graph op kept e y)
      cases sameRel
      cases sameDom
      cases sameGraph
      rfl

/-- Restrict primitive evaluations and pull their tuples back along the retained carrier maps. -/
def pullback (A : RestrictedEvaluation U Y) (inside : V ≤ U) (f : CarrierMap V X Y) :
    RestrictedEvaluation V X where
  relation r kept e := A.relation r (inside kept) (mapAssignment f (relationInputs r kept) e)
  domain p kept e := A.domain p (inside kept) (mapAssignment f (operationInputs (.partialOp p) kept) e)
  graph op kept e y := A.graph op (inside kept) (mapAssignment f (operationInputs op kept) e)
    (f _ (operationOutput op kept) y)

/-- The restricted relation is the original relation on the mapped tuple. -/
@[simp] theorem pullback_relation (A : RestrictedEvaluation U Y) (inside : V ≤ U) (f : CarrierMap V X Y)
    (r : P.signature.Rel) (kept : Declaration.relation r ∈ V.declarations) (e : Assignment X (P.signature.relInputs r)) :
    (A.pullback inside f).relation r kept e ↔ A.relation r (inside kept) (mapAssignment f (relationInputs r kept) e) :=
  Iff.rfl

/-- The restricted partial domain is the original domain on the mapped tuple. -/
@[simp] theorem pullback_domain (A : RestrictedEvaluation U Y) (inside : V ≤ U) (f : CarrierMap V X Y)
    (p : P.signature.Partial) (kept : Declaration.partialOp p ∈ V.declarations)
    (e : Assignment X (P.signature.partialArity p).inputs) :
    (A.pullback inside f).domain p kept e ↔
      A.domain p (inside kept) (mapAssignment f (operationInputs (.partialOp p) kept) e) :=
  Iff.rfl

/-- The restricted operation graph relates the mapped input tuple and mapped result. -/
@[simp] theorem pullback_graph (A : RestrictedEvaluation U Y) (inside : V ≤ U) (f : CarrierMap V X Y)
    (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ V.declarations)
    (e : Assignment X op.arity.inputs) (y : X op.arity.output) :
    (A.pullback inside f).graph op kept e y ↔
      A.graph op (inside kept) (mapAssignment f (operationInputs op kept) e) (f _ (operationOutput op kept) y) :=
  Iff.rfl

/-- Identity pullback keeps every interpreted primitive. -/
theorem pullback_id (A : RestrictedEvaluation U X) : A.pullback (le_refl U) (fun _ _ x => x) = A := by
  apply ext <;> intros <;> simp only [pullback_relation, pullback_domain, pullback_graph, mapAssignment_id]

/-- Successive pullbacks compose the carrier maps at each retained sort. -/
theorem pullback_comp (A : RestrictedEvaluation U Z) (h : V ≤ U) (k : W ≤ V)
    (f : CarrierMap V Y Z) (g : CarrierMap W X Y) :
    (A.pullback h f).pullback k g = A.pullback (k.trans h) (fun s kept x => f s (k kept) (g s kept x)) := by
  apply ext <;> intros <;> simp only [pullback_relation, pullback_domain, pullback_graph, mapAssignment_comp _ _ k]

/-- Equal carrier maps induce the same restriction of all the primitive interpretations. -/
theorem pullback_congr (A : RestrictedEvaluation U Y) (inside : V ≤ U) {f g : CarrierMap V X Y}
    (same : ∀ s keep x, f s keep x = g s keep x) : A.pullback inside f = A.pullback inside g := by
  apply ext
  · intro r keep e
    rw [pullback_relation, pullback_relation, mapAssignment_congr same]
  · intro p keep e
    rw [pullback_domain, pullback_domain, mapAssignment_congr same]
  · intro op keep e y
    rw [pullback_graph, pullback_graph, mapAssignment_congr same, same]

/-- Transporting an evaluator to equal carrier types pulls back along the inverse casts. -/
theorem cast_evaluation {X Y : P.signature.SortType → Type u} (A : RestrictedEvaluation U X) (h : X = Y) :
    cast (congrArg (RestrictedEvaluation U) h) A =
      A.pullback (le_refl U) (fun s _ => cast (congrFun h.symm s)) := by
  cases h
  exact A.pullback_id.symm

/-- Pullback has the same supported atomic facts when the carrier maps are injective. -/
theorem atomic_pullback_iff (A : RestrictedEvaluation U Y) (inside : V ≤ U) (f : CarrierMap V X Y)
    (inj : ∀ s kept, Function.Injective (f s kept)) {Γ : List P.signature.SortType}
    (a : Atomic P.signature Γ) (support : Declaration.atomicSupport a ⊆ V.declarations) (e : Assignment X Γ) :
    (A.pullback inside f).atomic e a support ↔ A.atomic
      (mapAssignment f (fun _ hd => support (Or.inl hd)) e) a (fun _ hd => inside (support hd)) := by
  cases a with
  | eq x y =>
    rw [atomic_eq_iff, atomic_eq_iff]
    exact ⟨fun same => congrArg (f _ _) same, fun same => inj _ _ same⟩
  | rel r vars =>
    simp only [atomic_rel_iff, pullback_relation]
    rw [mapAssignment_pull f _ (fun _ hd => support (Or.inl hd)) vars e]
  | domain p vars =>
    simp only [atomic_domain_iff, pullback_domain]
    rw [mapAssignment_pull f _ (fun _ hd => support (Or.inl hd)) vars e]
  | graph op vars y =>
    simp only [atomic_graph_iff, pullback_graph, mapAssignment_apply]
    rw [mapAssignment_pull f _ (fun _ hd => support (Or.inl hd)) vars e]

/-- Every supported formula agrees with its original evaluation on the mapped assignment. -/
theorem holds_pullback_iff (A : RestrictedEvaluation U Y) (inside : V ≤ U) (f : CarrierMap V X Y)
    (bij : ∀ s kept, Function.Bijective (f s kept)) {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    ∀ (support : Declaration.formulaSupport p ⊆ V.declarations) (e : Assignment X Γ),
      (A.pullback inside f).holds p support e ↔ A.holds p (fun _ hd => inside (support hd))
        (mapAssignment f (fun _ hd => support (Or.inl hd)) e) := by
  induction p with
  | atom a =>
    intro support e
    rw [holds_atom_iff, holds_atom_iff]
    exact atomic_pullback_iff A inside f (fun s kept => (bij s kept).1) a support e
  | truth =>
    intro support e
    simp only [holds_truth_iff]
  | falsehood =>
    intro support e
    simp only [holds_falsehood_iff]
  | conj p q hp hq =>
    intro support e
    rw [holds_conj_iff, holds_conj_iff, hp, hq]
  | disj p q hp hq =>
    intro support e
    rw [holds_disj_iff, holds_disj_iff, hp, hq]
  | @ex Γ s p ih =>
    intro support e
    have kept : Declaration.sort s ∈ V.declarations := support (Or.inr (Or.inl (Set.mem_singleton _)))
    let keepΓ : Declaration.sorts Γ ⊆ V.declarations := fun _ hd => support (Or.inl hd)
    rw [holds_ex_iff, holds_ex_iff]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨f s kept x, ?_⟩
      have lifted := (ih _ _).1 hx
      rw [mapAssignment_cons f kept keepΓ] at lifted
      exact lifted
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := (bij s kept).2 y
      refine ⟨x, (ih _ _).2 ?_⟩
      rw [mapAssignment_cons f kept keepΓ]
      exact hy

end RestrictedEvaluation
end SHIGURE
