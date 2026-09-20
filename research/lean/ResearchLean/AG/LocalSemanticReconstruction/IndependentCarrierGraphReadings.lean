import ResearchLean.AG.LocalSemanticReconstruction.PrimitiveFunctionGraphCategory
import Mathlib.Data.Finset.Card
import Formal.Util.AssertStandardAxioms

/-!
# Primitive function graphs indexed before carrier selection

Candidate source/target carrier references and one point pair form the query.
Each local value is a Boolean. Carrier activation and exact-one output rows
are separate conditions; no completed function is a local value. The common
query type is independent of the two selected native carriers.

This component is intended for the common geometry Hom declaration. It proves
carrier matching, totality, both inverse readings, and finite point composition
before connecting the individual native Hom roles.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentCarrierGraph

noncomputable section

universe u v w z

/-- One candidate-carrier point pair, declared before selecting a function's native carriers. -/
inductive Query where
  /-- A single Bool edge at raw source and target carrier references. -/
  | edge (S : Type u) (T : Type v) (x : S) (y : T)

/-- Every graph cell is one Boolean, including all inactive candidate carriers. -/
abbrev Table := Query.{u, v} → Bool

variable (α : Type u) (β : Type v)

/-- Edges at every incorrect carrier pair must be false. -/
def IsTyped (t : Table.{u, v}) : Prop :=
  ∀ S T x y, (S ≠ α ∨ T ≠ β) → t (.edge S T x y) = false

/-- The selected source carrier has exactly one true output in each selected target-carrier row. -/
def IsTotal (t : Table.{u, v}) : Prop :=
  ∀ x : α, ∃! y : β, t (.edge α β x y) = true

/-- Independent graph conditions retain totality separately from candidate inactivity. -/
def IsLawful (t : Table.{u, v}) : Prop := IsTyped α β t ∧ IsTotal α β t

/-- The selected carrier rows form the existing total-functional primitive graph code. -/
def graph (t : Table.{u, v}) (ht : IsTotal α β t) : PrimitiveFunctionGraph.GraphCode α β :=
  ⟨⟨fun x y => t (.edge α β x y)⟩, ⟨ht⟩⟩

/-- Read an existing primitive graph at matching candidate carriers and set every other pair to false. -/
def readGraph (g : PrimitiveFunctionGraph.GraphCode α β) : Table.{u, v} := by
  classical
  intro q
  cases q with
  | edge S T x y => exact (if hS : S = α then
      if hT : T = β then g.edge (hS ▸ x) (hT ▸ y) else false else false)

/-- Native primitive graph readings have no values at mismatched carrier references. -/
theorem readGraph_isTyped (g : PrimitiveFunctionGraph.GraphCode α β) : IsTyped α β (readGraph α β g) := by
  classical
  intro S T x y h
  rcases h with hS | hT
  · simp [readGraph, hS]
  · by_cases hS : S = α
    · simp [readGraph, hS, hT]
    · simp [readGraph, hS]

/-- Exact-one native graph rows remain exact-one rows in the common candidate declaration. -/
theorem readGraph_isTotal (g : PrimitiveFunctionGraph.GraphCode α β) : IsTotal α β (readGraph α β g) := by
  classical
  intro x
  simpa [readGraph] using g.row_existsUnique x

/-- Restricting a candidate reading to its selected carriers recovers the original full graph. -/
theorem graph_readGraph (g : PrimitiveFunctionGraph.GraphCode α β) :
    graph α β (readGraph α β g) (readGraph_isTotal α β g) = g := by
  apply PrimitiveFunctionGraph.GraphCode.ext
  funext x y
  simp [graph, PrimitiveFunctionGraph.GraphCode.edge, readGraph]

/-- Re-reading a lawful candidate table restores its active edges and all inactive false values. -/
theorem readGraph_graph (t : Table.{u, v}) (ht : IsTyped α β t) (hl : IsTotal α β t) :
    readGraph α β (graph α β t hl) = t := by
  classical
  funext q
  cases q with
  | edge S T x y =>
    by_cases hS : S = α
    · subst S
      by_cases hT : T = β
      · subst T
        simp [readGraph, graph, PrimitiveFunctionGraph.GraphCode.edge]
      · simp [readGraph, hT, ht α T x y (Or.inr hT)]
    · simp [readGraph, hS, ht S T x y (Or.inl hS)]

/-- The candidate-carrier declaration represents every total-function graph exactly. -/
def graphEquiv : PrimitiveFunctionGraph.GraphCode α β ≃ {t : Table.{u, v} // IsLawful α β t} where
  toFun g := ⟨readGraph α β g, readGraph_isTyped α β g, readGraph_isTotal α β g⟩
  invFun t := graph α β t.val t.property.2
  left_inv := graph_readGraph α β
  right_inv t := Subtype.ext (readGraph_graph α β t.val t.property.1 t.property.2)

/-- Every directed function, without an injectivity hypothesis, has an exact candidate-point presentation. -/
def functionEquiv : (α → β) ≃ {t : Table.{u, v} // IsLawful α β t} :=
  PrimitiveFunctionGraph.GraphCode.graphEquivFunction.symm.trans (graphEquiv α β)

/-- Read a directed function into candidate point-pair Booleans. -/
def read (f : α → β) : Table.{u, v} := (functionEquiv α β f).val

/-- Function readings satisfy both candidate inactivity and exact-one selected rows. -/
theorem read_isLawful (f : α → β) : IsLawful α β (read α β f) := (functionEquiv α β f).property

/-- Assemble a directed function by the unique true output in each selected primitive row. -/
def assemble (t : Table.{u, v}) (h : IsLawful α β t) : α → β :=
  (functionEquiv α β).symm ⟨t, h⟩

/-- Primitive assembly restores all directed functions on the selected raw carriers. -/
theorem assemble_read (f : α → β) : assemble α β (read α β f) (read_isLawful α β f) = f :=
  (functionEquiv α β).left_inv f

/-- Every lawful primitive candidate cell is recovered, independently of exact-one witnesses. -/
theorem read_assemble (t : Table.{u, v}) (h : IsLawful α β t) : read α β (assemble α β t h) = t :=
  congrArg Subtype.val ((functionEquiv α β).right_inv ⟨t, h⟩)

/-- Each assembled function value has its original true graph edge. -/
theorem edge_assemble (t : Table.{u, v}) (h : IsLawful α β t) (x : α) :
    t (.edge α β x (assemble α β t h x)) = true :=
  (graph α β t h.2).edge_target x

/-- Any true point pair determines the unique assembled value in that row. -/
theorem assemble_eq_of_edge (t : Table.{u, v}) (h : IsLawful α β t) {x : α} {y : β}
    (hy : t (.edge α β x y) = true) : assemble α β t h x = y :=
  (graph α β t h.2).target_eq_of_edge hy

/-- An active function reading is true precisely at its actual point image. -/
theorem read_edge (f : α → β) (x : α) (y : β) : read α β f (.edge α β x y) = true ↔ f x = y := by
  classical
  simp [read, functionEquiv, graphEquiv, readGraph, PrimitiveFunctionGraph.GraphCode.graphEquivFunction,
    PrimitiveFunctionGraph.GraphCode.read, PrimitiveFunctionGraph.GraphCode.edge]

variable {α β}

/-- Wrong-carrier values are rejected even if every selected function row is otherwise total. -/
theorem mismatched_carrier_rejected (t : Table.{u, v}) (S : Type u) (T : Type v) (x : S) (y : T)
    (hc : S ≠ α ∨ T ≠ β) (he : t (.edge S T x y) = true) : ¬ IsLawful α β t := by
  intro h
  exact Bool.noConfusion ((h.1 S T x y hc).symm.trans he)

/-- A pair of different true outputs in a selected row violates the required uniqueness. -/
theorem duplicate_outputs_rejected (t : Table.{u, v}) (x : α) (y z : β) (hne : y ≠ z)
    (hy : t (.edge α β x y) = true) (hz : t (.edge α β x z) = true) : ¬ IsLawful α β t := by
  intro h
  exact hne ((assemble_eq_of_edge α β t h hy).symm.trans (assemble_eq_of_edge α β t h hz))

/-- An all-false graph is not total on any selected carrier with a supplied input point. -/
theorem false_table_rejected (x : α) : ¬ IsLawful α β (fun _ => false) := by
  intro h
  obtain ⟨_, he, _⟩ := h.2 x
  exact Bool.noConfusion he

/-- Direct composition reads one second-graph point after choosing the first graph's unique row image. -/
def compose (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) : Table.{u, w} := by
  classical
  intro q
  cases q with
  | edge S T x z => exact (if hS : S = α then if hT : T = γ then
      s (.edge β γ (assemble α β t ht (hS ▸ x)) (hT ▸ z)) else false else false)

/-- Active composed graph cells use exactly the intermediate point chosen by the first primitive row. -/
theorem compose_edge (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) (x : α) (z : γ) :
    compose α β γ t ht s (.edge α γ x z) = s (.edge β γ (assemble α β t ht x) z) := by
  classical
  simp [compose]

/-- Two primitive cells suffice for an active composition value on arbitrary lawful comparison graphs. -/
theorem compose_point_finite_support (α : Type u) (β : Type v) (γ : Type w)
    (t t' : Table.{u, v}) (ht : IsLawful α β t) (ht' : IsLawful α β t')
    (s s' : Table.{v, w}) (x : α) (z : γ)
    (h1 : t (.edge α β x (assemble α β t ht x)) = t' (.edge α β x (assemble α β t ht x)))
    (h2 : s (.edge β γ (assemble α β t ht x) z) = s' (.edge β γ (assemble α β t ht x) z)) :
    compose α β γ t ht s (.edge α γ x z) = compose α β γ t' ht' s' (.edge α γ x z) := by
  have hp : t' (.edge α β x (assemble α β t ht x)) = true := h1.symm.trans (edge_assemble α β t ht x)
  have he := assemble_eq_of_edge α β t' ht' hp
  rw [compose_edge, compose_edge, he]
  exact h2


/-- Direct point composition preserves inactive carriers and exactly one active output per row. -/
theorem compose_isLawful (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) (hs : IsLawful β γ s) :
    IsLawful α γ (compose α β γ t ht s) := by
  classical
  constructor
  · intro S T x z h
    rcases h with hS | hT
    · simp [compose, hS]
    · by_cases hS : S = α
      · simp [compose, hS, hT]
      · simp [compose, hS]
  · intro x
    simpa [compose] using hs.2 (assemble α β t ht x)

/-- Native function assembly sends primitive graph composition to ordinary directed composition. -/
theorem assemble_compose (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) (hs : IsLawful β γ s) :
    assemble α γ (compose α β γ t ht s) (compose_isLawful α β γ t ht s hs) =
      assemble β γ s hs ∘ assemble α β t ht := by
  funext x
  apply assemble_eq_of_edge
  rw [compose_edge]
  exact edge_assemble β γ s hs _

/-- All query constructors have at most two queried cells in a composition support. -/
theorem compose_finite_support (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) (q : Query.{u, w}) :
    ∃ (D : Finset Query.{u, v}) (E : Finset Query.{v, w}), D.card + E.card ≤ 2 ∧
      ∀ (t' : Table.{u, v}) (ht' : IsLawful α β t') (s' : Table.{v, w}),
        (∀ p ∈ D, t p = t' p) → (∀ p ∈ E, s p = s' p) →
          compose α β γ t ht s q = compose α β γ t' ht' s' q := by
  classical
  cases q with
  | edge S T x z =>
    by_cases hS : S = α
    · subst S
      by_cases hT : T = γ
      · subst T
        refine ⟨{.edge α β x (assemble α β t ht x)},
          {.edge β γ (assemble α β t ht x) z}, by simp, ?_⟩
        intro t' ht' s' hD hE
        exact compose_point_finite_support α β γ t t' ht ht' s s' x z
          (hD _ (by simp)) (hE _ (by simp))
      · refine ⟨∅, ∅, by simp, ?_⟩
        intro t' ht' s' _ _
        simp [compose, hT]
    · refine ⟨∅, ∅, by simp, ?_⟩
      intro t' ht' s' _ _
      simp [compose, hS]

/-- Primitive identity is the diagonal Bool graph at the selected carrier pair. -/
def identity (α : Type u) : Table.{u, u} := read α α id

/-- Every selected input has one identical output in the primitive identity graph. -/
theorem identity_isLawful (α : Type u) : IsLawful α α (identity α) := read_isLawful α α id

/-- Identity evaluation is exactly equality of the two raw points. -/
theorem identity_edge (α : Type u) (x y : α) : identity α (.edge α α x y) = true ↔ x = y :=
  read_edge α α id x y

/-- The primitive identity assembles to the native identity function. -/
theorem assemble_identity (α : Type u) : assemble α α (identity α) (identity_isLawful α) = id :=
  assemble_read α α id

/-- Function assembly separates all lawful candidate cells, including inactive carrier references. -/
theorem assemble_injective (α : Type u) (β : Type v) (t s : Table.{u, v})
    (ht : IsLawful α β t) (hs : IsLawful α β s) (h : assemble α β t ht = assemble α β s hs) : t = s := by
  rw [← read_assemble α β t ht, ← read_assemble α β s hs, h]

/-- The left primitive identity law follows from point composition and both inverse readings. -/
theorem identity_compose (α : Type u) (β : Type v) (t : Table.{u, v}) (ht : IsLawful α β t) :
    compose α α β (identity α) (identity_isLawful α) t = t := by
  apply assemble_injective α β _ t (compose_isLawful _ _ _ _ _ _ ht) ht
  rw [assemble_compose α α β (identity α) (identity_isLawful α) t ht, assemble_identity]
  rfl

/-- The right primitive identity law retains the complete common candidate table. -/
theorem compose_identity (α : Type u) (β : Type v) (t : Table.{u, v}) (ht : IsLawful α β t) :
    compose α β β t ht (identity β) = t := by
  apply assemble_injective α β _ t (compose_isLawful _ _ _ _ _ _ (identity_isLawful β)) ht
  rw [assemble_compose α β β t ht (identity β) (identity_isLawful β), assemble_identity]
  rfl

/-- Re-reading a native composite is the direct finite point composition of the two primitive readings. -/
theorem read_compose (α : Type u) (β : Type v) (γ : Type w) (f : α → β) (g : β → γ) :
    read α γ (g ∘ f) = compose α β γ (read α β f) (read_isLawful α β f) (read β γ g) := by
  have h := read_assemble α γ (compose α β γ (read α β f) (read_isLawful α β f) (read β γ g))
    (compose_isLawful _ _ _ _ (read_isLawful α β f) _ (read_isLawful β γ g))
  rw [assemble_compose α β γ (read α β f) (read_isLawful α β f)
    (read β γ g) (read_isLawful β γ g), assemble_read, assemble_read] at h
  exact h


/-- Primitive graph composition is associative on all lawful candidate tables. -/
theorem compose_assoc (α : Type u) (β : Type v) (γ : Type w) (δ : Type z)
    (t : Table.{u, v}) (ht : IsLawful α β t)
    (s : Table.{v, w}) (hs : IsLawful β γ s) (r : Table.{w, z}) (hr : IsLawful γ δ r) :
    compose α γ δ (compose α β γ t ht s) (compose_isLawful α β γ t ht s hs) r =
      compose α β δ t ht (compose β γ δ s hs r) := by
  apply assemble_injective α δ _ _
    (compose_isLawful α γ δ _ (compose_isLawful α β γ t ht s hs) r hr)
    (compose_isLawful α β δ t ht _ (compose_isLawful β γ δ s hs r hr))
  rw [assemble_compose α γ δ _ (compose_isLawful α β γ t ht s hs) r hr,
    assemble_compose α β γ t ht s hs,
    assemble_compose α β δ t ht _ (compose_isLawful β γ δ s hs r hr),
    assemble_compose β γ δ s hs r hr]
  rfl

end

end AAT.AG.LocalSemanticReconstruction.IndependentCarrierGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentCarrierGraph
