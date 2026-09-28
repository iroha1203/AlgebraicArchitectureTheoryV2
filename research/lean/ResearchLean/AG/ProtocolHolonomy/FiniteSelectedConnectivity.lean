import ResearchLean.AG.ProtocolHolonomy.FiniteComponents
import Formal.Util.AssertStandardAxioms

/-!
# Decide connectivity of any selected original named-edge subset

For an actual finite set of original edge names, forget orientation only for
reachability. The bounded simple-graph walk decision computes precisely the
equivalence closure of selected original directed edge steps. Selecting every
original edge recovers the original component relation. This is the finite
connectivity test needed to search for a genuine named spanning forest; the
selection and bridge proof are later obligations.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- One directed step bearing a selected original edge name. -/
def selectedNamedStep (Q : FixedFDirectedMultigraph.{u, v})
    (selected : Finset Q.Edge) (a b : Q.Vertex) : Prop :=
  ∃ e : Q.Edge, e ∈ selected ∧ Q.source e = a ∧ Q.target e = b

/-- Undirected reachability through only selected original edge names. -/
def SelectedNamedReachable (Q : FixedFDirectedMultigraph.{u, v})
    (selected : Finset Q.Edge) (a b : Q.Vertex) : Prop :=
  Relation.EqvGen (selectedNamedStep Q selected) a b

/-- A finite simple graph used only to decide selected named connectivity. -/
def selectedReachabilityGraph (Q : FixedFDirectedMultigraph.{u, v})
    (selected : Finset Q.Edge) : SimpleGraph Q.Vertex where
  Adj a b := a ≠ b ∧
    (selectedNamedStep Q selected a b ∨ selectedNamedStep Q selected b a)
  symm := by
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    refine ⟨?_⟩
    intro a h
    exact h.1 rfl

/-- The finite graph's walks describe exactly the selected original
edge-step closure, including backwards passages and loops. -/
theorem selectedReachable_iff_named
    (Q : FixedFDirectedMultigraph.{u, v})
    (selected : Finset Q.Edge) (a b : Q.Vertex) :
    (selectedReachabilityGraph Q selected).Reachable a b ↔
      SelectedNamedReachable Q selected a b := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Relation.EqvGen.refl _
    | cons hab p ih =>
        rcases hab.2 with h | h
        · exact Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.rel _ _ h) ih
        · exact Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)) ih
  · intro h
    induction h with
    | rel a b hab =>
        by_cases heq : a = b
        · subst b
          exact SimpleGraph.Reachable.rfl
        · exact SimpleGraph.Adj.reachable ⟨heq, Or.inl hab⟩
    | refl a => exact SimpleGraph.Reachable.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ih₁ ih₂ => exact ih₁.trans ih₂

/-- The selected edge table gives a finite adjacency decision. -/
def selectedAdjDecidable (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (selected : Finset Q.Edge) :
    DecidableRel (selectedReachabilityGraph Q selected).Adj := by
  intro a b
  unfold selectedReachabilityGraph selectedNamedStep
  infer_instance

/-- A terminating bounded-walk decision for connectivity in any selected
original named-edge subset. -/
def selectedReachableDecidable (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (selected : Finset Q.Edge) :
    DecidableRel (SelectedNamedReachable Q selected) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : DecidableRel (selectedReachabilityGraph Q selected).Adj :=
    selectedAdjDecidable Q selected
  letI : DecidableRel (selectedReachabilityGraph Q selected).Reachable :=
    inferInstance
  intro a b
  exact decidable_of_iff' _ (selectedReachable_iff_named Q selected a b).symm

/-- The complete edge table as a finite set of original names. -/
def allNamedEdges (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Edge] (edges : ExplicitEnumeration Q.Edge) :
    Finset Q.Edge := edges.values.toFinset

/-- Selecting all original names gives exactly the original undirected
component relation, not a new quotient. -/
theorem allNamedEdges_reachable_iff_original
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Edge] (edges : ExplicitEnumeration Q.Edge)
    (a b : Q.Vertex) :
    SelectedNamedReachable Q (allNamedEdges Q edges) a b ↔
      FixedFUndirectedReachable Q a b := by
  have hstep : selectedNamedStep Q (allNamedEdges Q edges) =
      fixedFDirectedEdgeStep Q := by
    funext x y
    apply propext
    constructor
    · rintro ⟨e, _, hs, ht⟩
      exact ⟨e, hs, ht⟩
    · rintro ⟨e, hs, ht⟩
      exact ⟨e, List.mem_toFinset.mpr (edges.complete e), hs, ht⟩
  change Relation.EqvGen (selectedNamedStep Q (allNamedEdges Q edges)) a b ↔
    Relation.EqvGen (fixedFDirectedEdgeStep Q) a b
  rw [hstep]

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.selectedNamedStep
#print axioms AAT.AG.ProtocolHolonomy.SelectedNamedReachable
#print axioms AAT.AG.ProtocolHolonomy.selectedReachabilityGraph
#print axioms AAT.AG.ProtocolHolonomy.selectedReachable_iff_named
#print axioms AAT.AG.ProtocolHolonomy.selectedAdjDecidable
#print axioms AAT.AG.ProtocolHolonomy.selectedReachableDecidable
#print axioms AAT.AG.ProtocolHolonomy.allNamedEdges
#print axioms AAT.AG.ProtocolHolonomy.allNamedEdges_reachable_iff_original

private def selectedSmokeQ :
    AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := PUnit
  source := fun _ => false
  target := fun _ => true

private def selectedSmokeVertices :
    AAT.AG.ProtocolHolonomy.ExplicitEnumeration selectedSmokeQ.Vertex where
  values := [false, true]
  complete := by intro x; cases x <;> simp

#eval (letI : DecidableEq selectedSmokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq selectedSmokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  letI : DecidableRel (AAT.AG.ProtocolHolonomy.SelectedNamedReachable
      selectedSmokeQ ({PUnit.unit} : Finset PUnit)) :=
    AAT.AG.ProtocolHolonomy.selectedReachableDecidable
      selectedSmokeQ selectedSmokeVertices {PUnit.unit}
  decide (AAT.AG.ProtocolHolonomy.SelectedNamedReachable
    selectedSmokeQ {PUnit.unit} false true))

#eval (letI : DecidableEq selectedSmokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq selectedSmokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  letI : DecidableRel (AAT.AG.ProtocolHolonomy.SelectedNamedReachable
      selectedSmokeQ (∅ : Finset PUnit)) :=
    AAT.AG.ProtocolHolonomy.selectedReachableDecidable
      selectedSmokeQ selectedSmokeVertices ∅
  decide (AAT.AG.ProtocolHolonomy.SelectedNamedReachable
    selectedSmokeQ ∅ false true))

#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
