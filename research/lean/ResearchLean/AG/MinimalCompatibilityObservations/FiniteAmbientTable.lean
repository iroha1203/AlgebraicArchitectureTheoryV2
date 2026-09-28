import ResearchLean.AG.MinimalCompatibilityObservations.ProtocolFiberDisplay
import ResearchLean.AG.ProtocolHolonomy.FiniteDirectDecision
import ResearchLean.AG.ProtocolHolonomy.FiniteSelectedAllLifts
import Formal.Util.AssertStandardAxioms

/-!
# G-128: exhaustive ambient changes from primitive finite tables

The candidate test checks only the two inverse laws. In particular, the
named-edge equation is not used to generate the ambient group.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy
open AAT.AG.RealizationReconstruction

universe u v w

variable {Q : FixedFDirectedMultigraph.{u, v}}
variable (D : ReversibleData.{u, v, w} Q)
variable (H : Subgroup (FixedFGraphAutomorphism Q))

/-- The two inverse equations alone make every vertex table a bijection. -/
def InverseCandidate (g : FixedFGraphAutomorphism Q)
    (f : D.CandidateMaps g) : Prop :=
  (∀ (v : Q.Vertex) (x : D.Fiber v), f.2 v (f.1 v x) = x) ∧
  (∀ (v : Q.Vertex) (y : D.Fiber (g.vertex v)), f.1 v (f.2 v y) = y)

/-- Turn mutually inverse fiber tables into the corresponding ambient
fiberwise pair, without imposing any named-edge equation. -/
def fiberPairOfInverseCandidate (g : H) (f : D.CandidateMaps g.1)
    (hf : InverseCandidate D g.1 f) : AmbientFiberPair D H :=
  ⟨g, fun v =>
    { toFun := f.1 v
      invFun := f.2 v
      left_inv := hf.1 v
      right_inv := hf.2 v }⟩

section ExplicitTables

variable [DecidableEq Q.Vertex]
  [∀ v : Q.Vertex, DecidableEq (D.Fiber v)]

/-- Search all forward/inverse tables over a supplied visible change,
accepting only mutually inverse tables. -/
def candidateFiberPairs (g : H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    List (AmbientFiberPair D H) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : ∀ v : Q.Vertex, Fintype (D.Fiber v) :=
    fun v => (fibers v).toFintype
  exact (D.allCandidateMaps g.1 vertices fibers).values.filterMap fun f =>
    letI : Decidable (InverseCandidate D g.1 f) := by
      unfold InverseCandidate
      infer_instance
    if hf : InverseCandidate D g.1 f then
      some (fiberPairOfInverseCandidate D H g f hf)
    else none

/-- Every arbitrary fiber-bijection family over the supplied visible change
appears in the inverse-only table search. -/
theorem mem_candidateFiberPairs (a : AmbientFiberPair D H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    a ∈ candidateFiberPairs D H a.1 vertices fibers := by
  rcases a with ⟨g, f⟩
  let cand : D.CandidateMaps g.1 :=
    ⟨fun v => f v, fun v => (f v).symm⟩
  have hmem : cand ∈ (D.allCandidateMaps g.1 vertices fibers).values :=
    (D.allCandidateMaps g.1 vertices fibers).complete cand
  have hinv : InverseCandidate D g.1 cand := by
    constructor
    · intro v x
      exact (f v).symm_apply_apply x
    · intro v y
      exact (f v).apply_symm_apply y
  have hpair : fiberPairOfInverseCandidate D H g cand hinv =
      (⟨g, f⟩ : AmbientFiberPair D H) := by
    apply Sigma.ext rfl
    rfl
  unfold candidateFiberPairs
  apply List.mem_filterMap.mpr
  refine ⟨cand, hmem, ?_⟩
  simp [hinv, hpair]

/-- A complete input-ordered list of every visible/fiber-bijection pair. -/
def allAmbientFiberPairs
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    ExplicitEnumeration (AmbientFiberPair D H) where
  values := visible.values.flatMap fun g => candidateFiberPairs D H g vertices fibers
  complete := by
    intro a
    apply List.mem_flatMap.mpr
    exact ⟨a.1, visible.complete a.1,
      mem_candidateFiberPairs D H a vertices fibers⟩

/-- Generate every ambient change from the original visible and fiber
tables, without testing any named-edge equation. -/
def allAmbientChanges
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    ExplicitEnumeration (ambientChange D H) where
  values := (allAmbientFiberPairs D H visible vertices fibers).values.map
    (fiberPairToAmbient D H)
  complete := by
    intro a
    let p := ambientEquivFiberPair D H a
    have hp : p ∈ (allAmbientFiberPairs D H visible vertices fibers).values :=
      (allAmbientFiberPairs D H visible vertices fibers).complete p
    exact List.mem_map.mpr ⟨p, hp,
      (ambientEquivFiberPair D H).left_inv a⟩

end ExplicitTables

namespace ExplicitEnumeration

/-- Assemble a dependent-state table from supplied vertex and fiber lists. -/
def sigma {ι : Type u} {α : ι → Type w}
    (indices : ExplicitEnumeration ι)
    (values : ∀ i, ExplicitEnumeration (α i)) :
    ExplicitEnumeration (Σ i, α i) where
  values := indices.values.flatMap fun i => (values i).values.map (Sigma.mk i)
  complete := by
    rintro ⟨i, x⟩
    apply List.mem_flatMap.mpr
    exact ⟨i, indices.complete i,
      List.mem_map.mpr ⟨x, (values i).complete x, rfl⟩⟩

/-- Concatenate the two original component lists into a disjoint-union
observation table. -/
def sum {α : Type u} {β : Type v}
    (left : ExplicitEnumeration α) (right : ExplicitEnumeration β) :
    ExplicitEnumeration (α ⊕ β) where
  values := left.values.map Sum.inl ++ right.values.map Sum.inr
  complete := by
    intro x
    cases x with
    | inl a =>
        exact List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨a, left.complete a, rfl⟩))
    | inr b =>
        exact List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨b, right.complete b, rfl⟩))

end ExplicitEnumeration

/-- The supplied state table, retaining its vertex/fiber order. -/
def allProtocolStates
    (vertices : ExplicitEnumeration Q.Vertex)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    ExplicitEnumeration (ProtocolStates D) :=
  ExplicitEnumeration.sigma vertices fibers

/-- The full vertex, named-edge, and state observation table. -/
def allProtocolFullPoints
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    ExplicitEnumeration (ProtocolFullPoints D) :=
  ExplicitEnumeration.sum vertices
    (ExplicitEnumeration.sum edges (allProtocolStates D vertices fibers))

section DecidableTables

variable [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
  [∀ v : Q.Vertex, DecidableEq (D.Fiber v)]

/-- The supplied finite tables also decide equality of ambient changes. -/
def ambientDecidableEq
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    DecidableEq (ambientChange D H) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : Fintype Q.Edge := edges.toFintype
  letI : ∀ v : Q.Vertex, Fintype (D.Fiber v) :=
    fun v => (fibers v).toFintype
  letI : DecidableEq (FixedFGraphAutomorphism Q) :=
    (show Function.Injective
      (fun g : FixedFGraphAutomorphism Q =>
        ((fun v => g.vertex v), (fun e => g.edge e))) from by
      intro a b h
      apply FixedFGraphAutomorphism.ext
      · apply Equiv.ext
        intro v
        exact congrFun (congrArg Prod.fst h) v
      · apply Equiv.ext
        intro e
        exact congrFun (congrArg Prod.snd h) e).decidableEq
  infer_instance

/-- Check the original named-operation relation at every edge and state
pair, using the input tables rather than a compatibility certificate. -/
def compatibleDecidablePred
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    DecidablePred (· ∈ compatibleChange D H) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : Fintype Q.Edge := edges.toFintype
  letI : ∀ v : Q.Vertex, Fintype (D.Fiber v) :=
    fun v => (fibers v).toFintype
  intro a
  change Decidable (∀ e p q, D.NamedExecution e p q ↔
    D.NamedExecution (a.1.1.1.edge e) (a.1.2 p) (a.1.2 q))
  unfold ReversibleData.NamedExecution
  infer_instance

end DecidableTables

section CompatibleTables

variable [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
  [∀ v : Q.Vertex, DecidableEq (D.Fiber v)]

/-- The original G-127 selected-forest lift list, embedded in the new
ambient group over one visible change. -/
def selectedCompatibleChanges (g : H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    List (ambientChange D H) :=
  (D.finiteSelectedAllLifts g.1 vertices edges fibers).map fun l =>
    fiberPairToAmbient D H ⟨g, l.fiber⟩

/-- Exactly the compatible ambient changes over this visible change occur
in the original finite selected-lift output. -/
theorem mem_selectedCompatibleChanges_iff (g : H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v))
    (a : ambientChange D H) :
    a ∈ selectedCompatibleChanges D H g vertices edges fibers ↔
      a ∈ compatibleChange D H ∧ a.1.1 = g := by
  constructor
  · intro ha
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp ha
    constructor
    · exact (fiberPair_compatible_iff D H ⟨g, l.fiber⟩).2 l.edge_naturality
    · rfl
  · rintro ⟨ha, hg⟩
    let p := ambientEquivFiberPair D H a
    have hp : p.1 = g := hg
    have hpambient : fiberPairToAmbient D H p = a :=
      (ambientEquivFiberPair D H).left_inv a
    have hpcompat : fiberPairToAmbient D H p ∈ compatibleChange D H := by
      rw [hpambient]
      exact ha
    let l : D.Lift g.1 := by
      cases hp
      exact ⟨p.2, (fiberPair_compatible_iff D H p).1
        hpcompat⟩
    apply List.mem_map.mpr
    refine ⟨l, D.mem_finiteSelectedAllLifts g.1 vertices edges fibers l, ?_⟩
    cases hp
    exact hpambient

/-- Concatenate the original selected-lift outputs over all supplied
visible changes. -/
def allSelectedCompatibleChanges
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v)) :
    List (ambientChange D H) :=
  visible.values.flatMap fun g =>
    selectedCompatibleChanges D H g vertices edges fibers

/-- The generated compatible list has precisely the carrier of the
independently defined E1 subgroup. -/
theorem mem_allSelectedCompatibleChanges_iff
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ v, ExplicitEnumeration (D.Fiber v))
    (a : ambientChange D H) :
    a ∈ allSelectedCompatibleChanges D H visible vertices edges fibers ↔
      a ∈ compatibleChange D H := by
  rw [allSelectedCompatibleChanges, List.mem_flatMap]
  constructor
  · rintro ⟨g, _, hm⟩
    exact (mem_selectedCompatibleChanges_iff D H g vertices edges fibers a).1 hm |>.1
  · intro ha
    exact ⟨a.1.1, visible.complete a.1.1,
      (mem_selectedCompatibleChanges_iff D H a.1.1 vertices edges fibers a).2
        ⟨ha, rfl⟩⟩

end CompatibleTables

namespace FiniteProtocolInput

/-- The ambient search for the very same primitive protocol input used by
G-127. The explicit lists are execution inputs; `Finite` alone does not
silently choose their order. -/
def ambientTable (P : FiniteProtocolInput.{u, v, w} Q)
    [DecidableEq Q.Vertex]
    [∀ v : Q.Vertex, DecidableEq (P.data.Fiber v)]
    (visible : ExplicitEnumeration P.H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (fibers : ∀ v, ExplicitEnumeration (P.data.Fiber v)) :
    ExplicitEnumeration (ambientChange P.data P.H) :=
  allAmbientChanges P.data P.H visible vertices fibers

end FiniteProtocolInput

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
