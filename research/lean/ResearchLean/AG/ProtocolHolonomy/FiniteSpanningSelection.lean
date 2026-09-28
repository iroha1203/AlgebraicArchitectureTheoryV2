import ResearchLean.AG.ProtocolHolonomy.FiniteSelectedConnectivity
import Formal.Util.AssertStandardAxioms

/-!
# Input-generated selected original edges spanning every component

Start with the complete original named-edge table and consider each edge
name in table order. Remove that name exactly when the selected-edge finite
connectivity test says all original component connections remain. This
terminating deletion process returns a subset of original edge names that
still connects every original component. Showing that every retained edge
is a bridge, and constructing its tree paths, are separate obligations.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- Selected original edges span every original undirected component. -/
def SpansOriginalComponents (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Edge] (edges : ExplicitEnumeration Q.Edge)
    (selected : Finset Q.Edge) : Prop :=
  ∀ a b : Q.Vertex,
    SelectedNamedReachable Q (allNamedEdges Q edges) a b →
      SelectedNamedReachable Q selected a b

/-- All original named edges trivially span the original components. -/
theorem allNamedEdges_spans (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Edge] (edges : ExplicitEnumeration Q.Edge) :
    SpansOriginalComponents Q edges (allNamedEdges Q edges) := by
  intro a b h
  exact h

/-- The finite selected-edge connectivity test decides whether a subset
still spans every original component. -/
instance spansOriginalDecidable (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (selected : Finset Q.Edge) :
    Decidable (SpansOriginalComponents Q edges selected) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : DecidableRel (SelectedNamedReachable Q (allNamedEdges Q edges)) :=
    selectedReachableDecidable Q vertices (allNamedEdges Q edges)
  letI : DecidableRel (SelectedNamedReachable Q selected) :=
    selectedReachableDecidable Q vertices selected
  unfold SpansOriginalComponents
  infer_instance

/-- Prune the finite original edge-name list using the exact selected-edge
spanning decision after each attempted deletion. -/
def pruneNamedEdges (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge) :
    List Q.Edge → Finset Q.Edge → Finset Q.Edge
  | [], selected => selected
  | e :: rest, selected => by
      let smaller := selected.erase e
      letI : Decidable (SpansOriginalComponents Q edges smaller) :=
        spansOriginalDecidable Q vertices edges smaller
      exact if SpansOriginalComponents Q edges smaller then
        pruneNamedEdges Q vertices edges rest smaller
      else pruneNamedEdges Q vertices edges rest selected

/-- Every pruning step preserves all original component connections. -/
theorem pruneNamedEdges_spans (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (names : List Q.Edge) (selected : Finset Q.Edge)
    (h : SpansOriginalComponents Q edges selected) :
    SpansOriginalComponents Q edges
      (pruneNamedEdges Q vertices edges names selected) := by
  induction names generalizing selected with
  | nil => simpa [pruneNamedEdges] using h
  | cons e rest ih =>
      by_cases hsmall : SpansOriginalComponents Q edges (selected.erase e)
      · simpa [pruneNamedEdges, hsmall] using ih (selected.erase e) hsmall
      · simpa [pruneNamedEdges, hsmall] using ih selected h

/-- Pruning never introduces any edge name. -/
theorem pruneNamedEdges_subset (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (names : List Q.Edge) (selected : Finset Q.Edge) :
    pruneNamedEdges Q vertices edges names selected ⊆ selected := by
  induction names generalizing selected with
  | nil => simp [pruneNamedEdges]
  | cons e rest ih =>
      by_cases hsmall : SpansOriginalComponents Q edges (selected.erase e)
      · simpa [pruneNamedEdges, hsmall] using
          (ih (selected.erase e)).trans (Finset.erase_subset e selected)
      · simpa [pruneNamedEdges, hsmall] using ih selected

/-- A terminating selected original edge set generated from only the
explicit vertex and named-edge tables. -/
def finiteSpanningEdgeSelection (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge) : Finset Q.Edge :=
  pruneNamedEdges Q vertices edges edges.values (allNamedEdges Q edges)

theorem finiteSpanningEdgeSelection_subset (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge) :
    finiteSpanningEdgeSelection Q vertices edges ⊆ allNamedEdges Q edges :=
  pruneNamedEdges_subset Q vertices edges _ _

/-- The produced original named edge set connects every original component. -/
theorem finiteSpanningEdgeSelection_spans (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge) :
    SpansOriginalComponents Q edges
      (finiteSpanningEdgeSelection Q vertices edges) :=
  pruneNamedEdges_spans Q vertices edges _ _ (allNamedEdges_spans Q edges)

/-- The spanning guarantee is stated against the original component
relation, rather than only the temporary selected-graph relation. -/
theorem finiteSpanningEdgeSelection_originalReachable (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (a b : Q.Vertex) (h : FixedFUndirectedReachable Q a b) :
    SelectedNamedReachable Q (finiteSpanningEdgeSelection Q vertices edges) a b :=
  finiteSpanningEdgeSelection_spans Q vertices edges a b
    ((allNamedEdges_reachable_iff_original Q edges a b).mpr h)

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.SpansOriginalComponents
#print axioms AAT.AG.ProtocolHolonomy.allNamedEdges_spans
#print axioms AAT.AG.ProtocolHolonomy.spansOriginalDecidable
#print axioms AAT.AG.ProtocolHolonomy.pruneNamedEdges
#print axioms AAT.AG.ProtocolHolonomy.pruneNamedEdges_spans
#print axioms AAT.AG.ProtocolHolonomy.pruneNamedEdges_subset
#print axioms AAT.AG.ProtocolHolonomy.finiteSpanningEdgeSelection
#print axioms AAT.AG.ProtocolHolonomy.finiteSpanningEdgeSelection_subset
#print axioms AAT.AG.ProtocolHolonomy.finiteSpanningEdgeSelection_spans
#print axioms AAT.AG.ProtocolHolonomy.finiteSpanningEdgeSelection_originalReachable

private def pruneSmokeQ :
    AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := Fin 3
  source := fun _ => false
  target := fun e => if e = 2 then false else true

private def pruneSmokeVertices :
    AAT.AG.ProtocolHolonomy.ExplicitEnumeration pruneSmokeQ.Vertex where
  values := [false, true]
  complete := by intro x; cases x <;> simp

private def pruneSmokeEdges :
    AAT.AG.ProtocolHolonomy.ExplicitEnumeration pruneSmokeQ.Edge where
  values := ([0, 1, 2] : List (Fin 3))
  complete := by
    intro x
    change Fin 3 at x
    change x ∈ ([0, 1, 2] : List (Fin 3))
    have h : x = (0 : Fin 3) ∨ x = (1 : Fin 3) ∨ x = (2 : Fin 3) := by omega
    rcases h with h | h | h <;> simp [h]

#eval (letI : DecidableEq pruneSmokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq pruneSmokeQ.Edge := inferInstanceAs (DecidableEq (Fin 3))
  (AAT.AG.ProtocolHolonomy.finiteSpanningEdgeSelection
    pruneSmokeQ pruneSmokeVertices pruneSmokeEdges).card)

#eval (letI : DecidableEq pruneSmokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq pruneSmokeQ.Edge := inferInstanceAs (DecidableEq (Fin 3))
  (2 : Fin 3) ∈ AAT.AG.ProtocolHolonomy.finiteSpanningEdgeSelection
    pruneSmokeQ pruneSmokeVertices pruneSmokeEdges)

#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
