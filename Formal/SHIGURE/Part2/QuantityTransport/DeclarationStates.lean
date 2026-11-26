import Formal.SHIGURE.Part1.ContextSelectedStructures
import Formal.SHIGURE.Part2.QuantityTransport.DeclarationBinders
import Formal.SHIGURE.Part1.MarkedLawSupport

/-!
# Fixed state in a quantity Law

Replacing candidate values preserves the argument carriers, partial
domains and fixed primitive interpretations. Restricted term evaluation
and ordered equation expansion are read in the actual selected structure.
The syntax conditions provide sufficient tests for independence of the
varying value graphs.
-/

universe u

namespace SHIGURE

open DeclarationContext DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
variable {X : P.signature.SortType → Type u}

namespace RestrictedEvaluation

/-- Functional graphs with the prescribed domains supply all retained graph axioms. -/
theorem structural_of_graphs (B : RestrictedEvaluation U X)
    (functional : ∀ op keep, Relator.RightUnique (B.graph op keep))
    (total : ∀ (f : P.signature.Total) keep x, ∃ y, B.graph (.total f) keep x y)
    (quantity : ∀ (q : P.signature.Quantity) keep x, ∃ y, B.graph (.quantity q) keep x y)
    (partialDomain : ∀ (p : P.signature.Partial) keep x,
      (∃ y, B.graph (.partialOp p) keep x y) ↔ B.domain p (Declaration.ofOperation_partialOp p ▸ keep) x) :
    B.Structural := by
  rw [structural_iff]
  intro rule keep
  cases rule with
  | functional op =>
    simp only [satisfies_iff, GraphAxiom.toLaw_functional, holds_conj_iff, holds_atom_iff,
      atomic_graph_iff, atomic_eq_iff]
    exact fun e h => functional op _ h.1 h.2
  | totality f =>
    simp only [satisfies_iff, GraphAxiom.toLaw_totality, GraphAxiom.hasOutput_eq_ex_graph,
      holds_truth_iff, true_implies, holds_ex_iff, holds_atom_iff, atomic_graph_iff,
      Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here]
    exact total f _
  | quantityTotality q =>
    simp only [satisfies_iff, GraphAxiom.toLaw_quantityTotality, GraphAxiom.hasOutput_eq_ex_graph,
      holds_truth_iff, true_implies, holds_ex_iff, holds_atom_iff, atomic_graph_iff,
      Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here]
    exact quantity q _
  | graphImpliesDomain p =>
    simp only [satisfies_iff, GraphAxiom.toLaw_graphImpliesDomain, holds_atom_iff,
      atomic_graph_iff, atomic_domain_iff]
    exact fun e h => (partialDomain p _ _).1 ⟨_, h⟩
  | domainImpliesGraph p =>
    simp only [satisfies_iff, GraphAxiom.toLaw_domainImpliesGraph, GraphAxiom.hasOutput_eq_ex_graph,
      holds_ex_iff, holds_atom_iff, atomic_domain_iff, atomic_graph_iff,
      Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here]
    exact fun e h => (partialDomain p _ e).2 h

/-- A supported finite conjunction holds exactly when all of its components hold. -/
theorem holds_conjoin_iff (B : RestrictedEvaluation U X) {Γ : List P.signature.SortType}
    (Λ : List P.signature.SortType) (fs : ∀ {s}, Var Λ s → Formula P.signature Γ)
    (keep : Declaration.formulaSupport (Formula.conjoin Λ fs) ⊆ U.declarations)
    (components : ∀ {s} (i : Var Λ s), Declaration.formulaSupport (fs i) ⊆ U.declarations)
    (e : Assignment X Γ) :
    B.holds (Formula.conjoin Λ fs) keep e ↔ ∀ {s} (i : Var Λ s), B.holds (fs i) (components i) e := by
  induction Λ with
  | nil =>
    constructor
    · intro _ _ i
      nomatch i
    · intro _
      trivial
  | cons s Λ ih =>
    change B.holds ((fs .here).conj (Formula.conjoin Λ (fun i => fs (.there i)))) keep e ↔ _
    rw [holds_conj_iff, ih (components := fun i => components (.there i))]
    constructor
    · intro h _ i
      cases i with
      | here => exact h.1
      | there i => exact h.2 i
    · intro h
      exact ⟨h .here, fun i => h (.there i)⟩

/-- A supported block of existential variables is witnessed by their typed assignment. -/
theorem holds_existsMany_iff (B : RestrictedEvaluation U X) {Γ : List P.signature.SortType}
    (Λ : List P.signature.SortType) (p : Formula P.signature (Λ ++ Γ))
    (keep : Declaration.formulaSupport (Formula.existsMany Λ p) ⊆ U.declarations)
    (body : Declaration.formulaSupport p ⊆ U.declarations) (e : Assignment X Γ) :
    B.holds (Formula.existsMany Λ p) keep e ↔ ∃ a : Assignment X Λ, B.holds p body (a.append e) := by
  induction Λ with
  | nil =>
    simp only [Formula.existsMany_nil, Assignment.append_empty]
    exact ⟨fun h => ⟨Assignment.empty, h⟩, fun ⟨_, h⟩ => h⟩
  | cons s Λ ih =>
    change B.holds (Formula.existsMany Λ p.ex) keep e ↔ _
    rw [ih p.ex keep (existsMany_body_supported p.ex keep)]
    change (∃ a : Assignment X Λ, ∃ x : X s, B.holds p body (Assignment.cons x (a.append e))) ↔ _
    constructor
    · rintro ⟨a, x, h⟩
      exact ⟨Assignment.cons x a, h⟩
    · rintro ⟨a, h⟩
      refine ⟨a.tail, a.head, ?_⟩
      simpa only [← Assignment.append_cons, Assignment.cons_head_tail] using h

/-- Replace just the supported graphs of a smaller context, keeping other state data fixed. -/
noncomputable def replaceRetainedGraphs {V : DeclarationContext P} (A : RestrictedEvaluation U X)
    (B : RestrictedEvaluation V X) : RestrictedEvaluation U X where
  relation := A.relation
  domain := A.domain
  graph op keep e y := by
    classical
    exact if retained : Declaration.ofOperation op ∈ V.declarations then B.graph op retained e y else A.graph op keep e y

/-- The replacement reads the smaller evaluation at each retained operation. -/
theorem replaceRetainedGraphs_graph {V : DeclarationContext P} (A : RestrictedEvaluation U X)
    (B : RestrictedEvaluation V X) (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ U.declarations)
    (retained : Declaration.ofOperation op ∈ V.declarations) (e : Assignment X op.arity.inputs)
    (y : X op.arity.output) :
    (A.replaceRetainedGraphs B).graph op keep e y ↔ B.graph op retained e y := by
  classical
  simp only [replaceRetainedGraphs, dif_pos retained]

/-- The replacement leaves each operation outside the smaller context unchanged. -/
theorem replaceRetainedGraphs_graph_of_omitted {V : DeclarationContext P} (A : RestrictedEvaluation U X)
    (B : RestrictedEvaluation V X) (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ U.declarations)
    (omitted : Declaration.ofOperation op ∉ V.declarations) (e : Assignment X op.arity.inputs)
    (y : X op.arity.output) :
    (A.replaceRetainedGraphs B).graph op keep e y ↔ A.graph op keep e y := by
  classical
  simp only [replaceRetainedGraphs, dif_neg omitted]

/-- Structural graphs from a smaller context can be extended to all declarations
provided their partial domains agree with the original state. -/
theorem replaceRetainedGraphs_structural {V : DeclarationContext P}
    (A : RestrictedEvaluation U X) (B : RestrictedEvaluation V X) (inside : V ≤ U)
    (upperValid : A.Structural) (lowerValid : B.Structural)
    (domains : ∀ p keep e, B.domain p keep e ↔ A.domain p (inside keep) e) :
    (A.replaceRetainedGraphs B).Structural := by
  classical
  apply structural_of_graphs
  · intro op keep e y z hy hz
    by_cases retained : Declaration.ofOperation op ∈ V.declarations
    · let toLocal := fun w => (A.replaceRetainedGraphs_graph B op keep retained e w).1
      exact graph_rightUnique lowerValid op retained (toLocal y hy) (toLocal z hz)
    · let toOriginal := fun w => (A.replaceRetainedGraphs_graph_of_omitted B op keep retained e w).1
      exact graph_rightUnique upperValid op keep (toOriginal y hy) (toOriginal z hz)
  · intro f keep e
    by_cases retained : Declaration.ofOperation (.total f) ∈ V.declarations
    · obtain ⟨y, hy⟩ := (total_graph_valid lowerValid f retained).2 e
      exact ⟨y, (A.replaceRetainedGraphs_graph B (.total f) keep retained e y).2 hy⟩
    · obtain ⟨y, hy⟩ := (total_graph_valid upperValid f keep).2 e
      exact ⟨y, (A.replaceRetainedGraphs_graph_of_omitted B (.total f) keep retained e y).2 hy⟩
  · intro q keep e
    by_cases retained : Declaration.ofOperation (.quantity q) ∈ V.declarations
    · obtain ⟨y, hy⟩ := (quantity_graph_valid lowerValid q retained).2 e
      exact ⟨y, (A.replaceRetainedGraphs_graph B (.quantity q) keep retained e y).2 hy⟩
    · obtain ⟨y, hy⟩ := (quantity_graph_valid upperValid q keep).2 e
      exact ⟨y, (A.replaceRetainedGraphs_graph_of_omitted B (.quantity q) keep retained e y).2 hy⟩
  · intro p keep e
    by_cases retained : Declaration.ofOperation (.partialOp p) ∈ V.declarations
    · have valid := partial_graph_valid lowerValid p retained
      exact (exists_congr (A.replaceRetainedGraphs_graph B (.partialOp p) keep retained e)).trans
        (Iff.trans ⟨fun ⟨_, hy⟩ => valid.2.1 e _ hy, valid.2.2 e⟩ (domains p retained e))
    · have valid := partial_graph_valid upperValid p keep
      exact (exists_congr (A.replaceRetainedGraphs_graph_of_omitted B (.partialOp p) keep retained e)).trans
        ⟨fun ⟨_, hy⟩ => valid.2.1 e _ hy, valid.2.2 e⟩

end RestrictedEvaluation

namespace RestrictedStructure

/-- The evaluator of ordinary restricted operations is structural. -/
theorem evaluation_structural (B : RestrictedStructure U) : B.evaluation.Structural := by
  apply B.evaluation.structural_of_graphs
  · intro op keep e y z hy hz
    cases op with
    | total f => exact hy.symm.trans hz
    | quantity q => exact hy.symm.trans hz
    | partialOp p => exact (Exists.choose_spec hy).symm.trans (Exists.choose_spec hz)
  · intro f keep x
    exact ⟨B.total f keep x, rfl⟩
  · intro q keep x
    exact ⟨B.quantity q keep x, rfl⟩
  · intro p keep x
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨B.partialValue p keep ⟨x, h⟩, h, rfl⟩⟩

end RestrictedStructure

namespace DeclarationContext.Selected

/-- The original term's context is selected when its free variables, result and references are selected. -/
theorem termContext_le_of_references {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (term : Term P.signature Γ s) (context : Declaration.sorts Γ ⊆ U.declarations)
    (result : Declaration.sort s ∈ U.declarations) (refs : termReferences term ⊆ U.declarations) :
    Declaration.termContext term ≤ U := by
  have equality := lawConclusionSupport (Marked.equality_law_support term term operationInputs context result refs refs)
  change Declaration.formulaSupport (Formula.termEq term term) ⊆ U.declarations at equality
  rw [Formula.termEq_eq_ex] at equality
  exact (Declaration.termContext_le_iff term).2
    ((Declaration.binarySupport_left (Declaration.formula_conj term.graph term.graph)).trans
      ((Declaration.formulaSupport_ex_body _).trans equality))

end DeclarationContext.Selected

namespace ContextStructure

variable (B : ContextStructure U)
variable {Γ Δ : List P.signature.SortType} {s : P.signature.SortType}

/-- The context of a supported term retains its result sort. -/
theorem termResultSupport (t : U.TermIn Γ s) : Declaration.sort s ∈ U.declarations :=
  termSortSupport t (Declaration.sort_mem_sorts (by simp))

private theorem selected_evaluates_iff (t : U.TermIn Γ s)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hs : Declaration.sort s ∈ U.declarations)
    (refs : termReferences t.val ⊆ U.declarations) (e : Assignment B.carrier Γ) (z : B.carrier s) :
    (selectTerm t.val hΓ hs refs).Evaluates (readStructure B)
      (selectAssignment (readCarrierEquiv B) hΓ e) (readCarrierEquiv B s hs z) ↔ B.evaluates t e z := by
  let E := readCarrierEquiv B
  let keep := (Declaration.termContext_le_iff t.val).1 t.property
  let support := termSortSupport t
  have evaluated := read_evaluates_iff B t e z
  change (selectFormula (t.val.graphAt (fun i => .there i) .here) keep).Holds (readStructure B)
    (selectAssignment E support (Assignment.cons z e)) ↔ _ at evaluated
  rw [selectFormula_graphAt _ (fun i => .there i) .here hΓ support refs keep, Term.holds_graphAt] at evaluated
  let shift : Renaming Γ (s :: Γ) := fun i => .there i
  let selected := selectTerm t.val hΓ hs refs
  change selected.Evaluates (readStructure B)
    ((selectAssignment E support (Assignment.cons z e)).pull (selectRenaming hΓ support shift))
    ((selectAssignment E support (Assignment.cons z e)) (selectVar support .here)) ↔ _ at evaluated
  have pulled := selectAssignment_pull E hΓ support (Assignment.cons z e) shift
  change _ = selectAssignment E hΓ e at pulled
  rw [pulled, selectAssignment_selectVar] at evaluated
  exact evaluated

/-- Equal written terms have the same evaluation with either support proof. -/
theorem evaluates_congr {t v : Term P.signature Γ s} (same : t = v)
    (keepT : Declaration.termContext t ≤ U) (keepV : Declaration.termContext v ≤ U)
    (e : Assignment B.carrier Γ) (y : B.carrier s) :
    B.evaluates ⟨t, keepT⟩ e y ↔ B.evaluates ⟨v, keepV⟩ e y := by
  cases same
  rfl

/-- Expanding a supported original term preserves every value it actually evaluates. -/
theorem evaluates_inlineLets (t : U.TermIn Γ s) (inlineKept : Declaration.termContext t.val.inlineLets ≤ U)
    (e : Assignment B.carrier Γ) (y : B.carrier s) (held : B.evaluates t e y) :
    B.evaluates ⟨t.val.inlineLets, inlineKept⟩ e y := by
  let hSorts := termSortSupport t
  let hΓ := (tailSortsSubset s Γ).trans hSorts
  have hs : Declaration.sort s ∈ U.declarations := hSorts (Declaration.sort_mem_sorts (by simp))
  have keep := (Declaration.termContext_le_iff t.val).1 t.property
  have refs : termReferences t.val ⊆ U.declarations :=
    (termReferences_subset_graph t.val).trans (Set.subset_union_right.trans keep)
  have selected := (B.selected_evaluates_iff t hΓ hs refs e y).2 held
  apply (B.selected_evaluates_iff ⟨_, inlineKept⟩ hΓ hs (inlineLets_supported t.val refs) e y).1
  rw [selectTerm_inlineLets t.val hΓ hs refs]
  exact Term.evaluates_inlineLets (readStructure B) _ _ _ selected

/-- Every supported written value graph evaluates the same term at its named coordinates. -/
theorem holds_graphAt_iff (t : U.TermIn Γ s) (ρ : Renaming Γ Δ) (out : Var Δ s)
    (keep : Declaration.formulaSupport (t.val.graphAt ρ out) ⊆ U.declarations)
    (e : Assignment B.carrier Δ) :
    B.evaluation.holds (t.val.graphAt ρ out) keep e ↔ B.evaluates t (e.pull ρ) (e out) := by
  have hΔ := (Declaration.sorts_subset_formulaSupport _).trans keep
  have ht := (Declaration.termContext_le_iff t.val).1 t.property
  have hΓ := (tailSortsSubset s Γ).trans (termSortSupport t)
  have refs : termReferences t.val ⊆ U.declarations :=
    (termReferences_subset_graph t.val).trans (Set.subset_union_right.trans ht)
  let E := readCarrierEquiv B
  let selected := selectTerm t.val hΓ (varKept hΔ out) refs
  have graphAt := (readStructure_matches B).formula_iff _ keep e
  rw [selectFormula_graphAt _ ρ out hΓ hΔ refs keep, Term.holds_graphAt] at graphAt
  change selected.Evaluates (readStructure B)
    ((selectAssignment E hΔ e).pull (selectRenaming hΓ hΔ ρ))
    ((selectAssignment E hΔ e) (selectVar hΔ out)) ↔ _ at graphAt
  simp only [selectAssignment_pull, selectAssignment_selectVar] at graphAt
  exact graphAt.symm.trans (B.selected_evaluates_iff t hΓ _ refs _ _)

/-- An actual application evaluates exactly through its typed inputs and primitive graph. -/
theorem evaluates_app_iff (op : Operation P.signature)
    (args : ∀ {t}, Var op.arity.inputs t → Term P.signature Γ t)
    (term : U.TermIn Γ op.arity.output) (application : term.val = .app op args)
    (input : Assignment B.carrier Γ)
    (keepOp : Declaration.ofOperation op ∈ U.declarations) (y : B.carrier op.arity.output) :
    B.evaluates term input y ↔
      ∃ values : Assignment B.carrier op.arity.inputs,
        (∀ {t} (i : Var op.arity.inputs t), ∃ ht, B.evaluates ⟨args i, ht⟩ input (values i)) ∧
        B.evaluation.graph op keepOp values y := by
  obtain ⟨term, supported⟩ := term
  change term = Term.app op args at application
  subst term
  let e := Assignment.cons y input
  let Λ := op.arity.inputs
  let Δ := op.arity.output :: Γ
  let fs : ∀ {s}, Var Λ s → Formula P.signature (Λ ++ Δ) :=
    fun i => (args i).graphAt (fun j => (Var.there j : Var Δ _).shift Λ) (i.inLeft Δ)
  let atom : Formula P.signature (Λ ++ Δ) := .atom (.graph op (Var.inLeft Δ) ((Var.here : Var Δ _).shift Λ))
  let body := (Formula.conjoin Λ fs).conj atom
  have keep : Declaration.formulaSupport (Formula.existsMany Λ body) ⊆ U.declarations :=
    (Declaration.termContext_le_iff (.app op args)).1 supported
  change B.evaluation.holds (Formula.existsMany Λ body) keep e ↔ _
  have bodyKeep := existsMany_body_supported body keep
  rw [B.evaluation.holds_existsMany_iff Λ body keep bodyKeep e]
  let argsKeep := (Declaration.binarySupport_left (Declaration.formula_conj (Formula.conjoin Λ fs) atom)).trans bodyKeep
  apply exists_congr
  intro values
  rw [RestrictedEvaluation.holds_conj_iff]
  refine and_congr ?_ ?_
  · refine (B.evaluation.holds_conjoin_iff Λ fs argsKeep
      (fun i => conjoin_component_supported fs argsKeep i) (values.append e)).trans ?_
    constructor
    · intro held s i
      have hi : Declaration.termContext (args i) ≤ U := by
        apply termContext_le_of_references (args i)
        · exact (tailSortsSubset op.arity.output Γ).trans (termSortSupport ⟨_, supported⟩)
        · exact varKept (operationInputs op keepOp) i
        · have keptTerm : termReferences (Term.app op args) ⊆ U.declarations :=
            (termReferences_subset_graph (Term.app op args)).trans (Set.subset_union_right.trans keep)
          exact fun _ h => keptTerm (Or.inr ⟨_, i, h⟩)
      refine ⟨hi, ?_⟩
      have evaluated := (B.holds_graphAt_iff ⟨args i, hi⟩ _ _ _ _).1 (held i)
      have inputEq : (values.append e).pull (fun {s} (j : Var Γ s) => (Var.there j : Var Δ s).shift Λ) = input := by
        apply Assignment.ext
        intro s j
        rw [Assignment.pull_apply, Assignment.append_shift, Assignment.cons_there]
      rwa [inputEq, Assignment.append_inLeft] at evaluated
    · intro each t i
      obtain ⟨hi, evaluated⟩ := each i
      apply (B.holds_graphAt_iff ⟨args i, hi⟩ _ _ _ _).2
      have inputEq : (values.append e).pull (fun {s} (j : Var Γ s) => (Var.there j : Var Δ s).shift Λ) = input := by
        apply Assignment.ext
        intro s j
        rw [Assignment.pull_apply, Assignment.append_shift, Assignment.cons_there]
      rwa [inputEq, Assignment.append_inLeft]
  · change B.evaluation.graph op keepOp
      ((values.append e).pull (Var.inLeft Δ)) ((values.append e) ((Var.here : Var Δ _).shift Λ)) ↔ _
    rw [Assignment.pull_append_left, Assignment.append_shift, Assignment.cons_here]

/-- An application evaluates when its typed arguments evaluate and its primitive graph holds. -/
theorem evaluates_app_of_graph (op : Operation P.signature)
    (args : ∀ {t}, Var op.arity.inputs t → Term P.signature Γ t)
    (term : U.TermIn Γ op.arity.output) (application : term.val = .app op args)
    (input : Assignment B.carrier Γ) (values : Assignment B.carrier op.arity.inputs)
    (each : ∀ {t} (i : Var op.arity.inputs t), ∃ h, B.evaluates ⟨args i, h⟩ input (values i))
    (keepOp : Declaration.ofOperation op ∈ U.declarations) (y : B.carrier op.arity.output)
    (edge : B.evaluation.graph op keepOp values y) :
    B.evaluates term input y :=
  (B.evaluates_app_iff op args term application input keepOp y).2 ⟨values, each, edge⟩

/-- A strict binding evaluates its initializer and then its body at the extended input. -/
theorem evaluates_let_of_values {a : P.signature.SortType} (init : U.TermIn Γ a) (body : U.TermIn (a :: Γ) s)
    (support : Declaration.termContext (init.val.letBind body.val) ≤ U)
    (e : Assignment B.carrier Γ) (x : B.carrier a) (y : B.carrier s)
    (hx : B.evaluates init e x) (hy : B.evaluates body (Assignment.cons x e) y) :
    B.evaluates ⟨init.val.letBind body.val, support⟩ e y := by
  let e' := Assignment.cons y e
  let Δ := s :: Γ
  let first : Renaming Γ (a :: Δ) := fun i => .there (.there i)
  let rest : Renaming (a :: Γ) (a :: Δ) := Renaming.lift (fun i => .there i)
  let p := init.val.graphAt first (Var.here : Var (a :: Δ) a)
  let q := body.val.graphAt rest (Var.there (Var.here : Var Δ s))
  have keep : Declaration.formulaSupport ((p.conj q).ex) ⊆ U.declarations :=
    (Declaration.termContext_le_iff (init.val.letBind body.val)).1 support
  change B.evaluation.holds (p.conj q).ex keep e'
  refine ⟨x, ?_⟩
  rw [RestrictedEvaluation.holds_conj_iff]
  constructor
  · change B.evaluation.holds (init.val.graphAt first .here) _ (Assignment.cons x e')
    apply (B.holds_graphAt_iff init first .here _ _).2
    exact hx
  · change B.evaluation.holds (body.val.graphAt rest (.there .here)) _ (Assignment.cons x e')
    apply (B.holds_graphAt_iff body rest (.there .here) _ _).2
    have pull : (Assignment.cons x e').pull rest = Assignment.cons x e := by
      apply Assignment.ext
      intro s i
      cases i <;> rfl
    rw [pull]
    exact hy

/-- A supported term has at most one value on its actual input assignment. -/
theorem evaluates_unique (t : U.TermIn Γ s) (input : Assignment B.carrier Γ) {x y : B.carrier s}
    (hx : B.evaluates t input x) (hy : B.evaluates t input y) : x = y := by
  let hSorts := termSortSupport t
  let hΓ := (tailSortsSubset s Γ).trans hSorts
  have hs : Declaration.sort s ∈ U.declarations := hSorts (Declaration.sort_mem_sorts (by simp))
  have keep := (Declaration.termContext_le_iff t.val).1 t.property
  have refs : termReferences t.val ⊆ U.declarations :=
    (termReferences_subset_graph t.val).trans (Set.subset_union_right.trans keep)
  let lhs := B.selected_evaluates_iff t hΓ hs refs input x
  let rhs := B.selected_evaluates_iff t hΓ hs refs input y
  exact (readCarrierEquiv B s hs).injective ((selectTerm t.val hΓ hs refs).evaluates_unique _ _
    (lhs.2 hx) (rhs.2 hy))

/-- A declared expansion on its guard holds exactly when its two actual term values agree. -/
theorem holds_written_iff_of_evaluates (w : OrderedEquation.Written P.signature)
    (keep : Declaration.lawBody w.toLaw ⊆ U.declarations)
    (input : Assignment B.carrier w.equation.context)
    (guard : B.evaluation.holds w.equation.input (lawInputSupport keep) input)
    {left right : B.carrier w.equation.result}
    {keptLeft : Declaration.termContext w.equation.left ≤ U}
    {keptRight : Declaration.termContext w.equation.right ≤ U}
    (hl : B.evaluates ⟨w.equation.left, keptLeft⟩ input left)
    (hr : B.evaluates ⟨w.equation.right, keptRight⟩ input right) :
    B.evaluation.holds w.conclusion (lawConclusionSupport keep) input ↔ left = right := by
  let written := selectWritten w keep
  let E := readCarrierEquiv B
  let hΓ := lawSortSupport keep
  let hTerms := selectWritten_terms_kept w keep
  let hs := hTerms.1
  let assignment := selectAssignment E hΓ input
  let selectedLeft := selectTerm w.equation.left hΓ hs hTerms.2.1
  let selectedRight := selectTerm w.equation.right hΓ hs hTerms.2.2
  have inputHeld : written.equation.input.Holds (readStructure B) assignment :=
    ((readStructure_matches B).formula_iff _ (lawInputSupport keep) input).2 guard
  have expansion := written.expansion.holds_iff (readStructure B) assignment inputHeld
  simp only [Formula.holds_termEq, Term.mem_eval_iff] at expansion
  change written.conclusion.Holds (readStructure B) assignment ↔
    ∃ z, selectedLeft.Evaluates (readStructure B) assignment z ∧
      selectedRight.Evaluates (readStructure B) assignment z at expansion
  have compared := (readStructure_matches B).formula_iff w.conclusion (lawConclusionSupport keep) input
  have lv := (B.selected_evaluates_iff ⟨_, keptLeft⟩ hΓ hs hTerms.2.1 input left).2 hl
  have rv := (B.selected_evaluates_iff ⟨_, keptRight⟩ hΓ hs hTerms.2.2 input right).2 hr
  refine compared.symm.trans (expansion.trans ?_)
  constructor
  · rintro ⟨z, atLeft, atRight⟩
    exact (E _ hs).injective
      ((selectedLeft.evaluates_unique _ _ lv atLeft).trans (selectedRight.evaluates_unique _ _ atRight rv))
  · intro equal
    exact ⟨E _ hs left, lv, equal.symm ▸ rv⟩

end ContextStructure

end SHIGURE

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
