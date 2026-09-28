import ResearchLean.AG.ProtocolHolonomy.FiniteNamedForest
import Formal.Util.AssertStandardAxioms

/-!
# Compute original named passages from selected finite graph walks

Every selected graph adjacency is resolved by scanning the finite selected
set of original edge names. The resulting signed passage and its name proof
are computed together; finite walk recursion preserves that proof.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- Test an original name for a selected forward or backward signed step. -/
def selectedSignedStepCandidate
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (selected : Finset Q.Edge) (a b : Q.Vertex) (e : Q.Edge) :
    Option {p : SignedPath Q a b //
      UsesNamedEdges (fun f => f ∈ selected) p} := by
  if he : e ∈ selected then
    if hpos : Q.source e = a ∧ Q.target e = b then
      exact some ⟨signedToPath Q (Sum.inl ⟨e, hpos.1, hpos.2⟩),
        usesNamedEdges_single Q _ _ he⟩
    else if hneg : Q.target e = a ∧ Q.source e = b then
      exact some ⟨signedToPath Q (Sum.inr ⟨e, hneg.2, hneg.1⟩),
        usesNamedEdges_single Q _ _ he⟩
    else exact none
  else exact none

theorem selectedSignedStepCandidate_ne_none_of_pos
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (selected : Finset Q.Edge) (a b : Q.Vertex) (e : Q.Edge)
    (he : e ∈ selected)
    (h : Q.source e = a ∧ Q.target e = b) :
    selectedSignedStepCandidate Q selected a b e ≠ none := by
  simp [selectedSignedStepCandidate, he, h]

theorem selectedSignedStepCandidate_ne_none_of_neg
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (selected : Finset Q.Edge) (a b : Q.Vertex) (e : Q.Edge)
    (he : e ∈ selected)
    (h : Q.target e = a ∧ Q.source e = b) :
    selectedSignedStepCandidate Q selected a b e ≠ none := by
  unfold selectedSignedStepCandidate
  split_ifs <;> simp_all

/-- Scan the original finite edge table, accepting only selected names, to
realize a selected adjacency. -/
def selectedSignedEdgeOfAdj
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (selected : Finset Q.Edge) (edges : ExplicitEnumeration Q.Edge)
    {a b : Q.Vertex}
    (h : (selectedReachabilityGraph Q selected).Adj a b) :
    {p : SignedPath Q a b //
      UsesNamedEdges (fun f => f ∈ selected) p} := by
  let scan := edges.values.findSome?
    (selectedSignedStepCandidate Q selected a b)
  have hscan : scan ≠ none := by
    intro hn
    have hnone := List.findSome?_eq_none_iff.mp hn
    rcases h.2 with hp | hn
    · obtain ⟨e, he, hs, ht⟩ := hp
      exact (selectedSignedStepCandidate_ne_none_of_pos
        Q selected a b e he ⟨hs, ht⟩)
        (hnone e (edges.complete e))
    · obtain ⟨e, he, hs, ht⟩ := hn
      exact (selectedSignedStepCandidate_ne_none_of_neg
        Q selected a b e he ⟨ht, hs⟩)
        (hnone e (edges.complete e))
  cases hs : scan with
  | none => exact (hscan hs).elim
  | some p => exact p

/-- Resolve each selected finite-graph walk step into a computed signed path
whose names all belong to the same selected original edge set. -/
def selectedSignedPathOfWalk
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (selected : Finset Q.Edge) (edges : ExplicitEnumeration Q.Edge)
    {a b : Q.Vertex} :
    (walk : (selectedReachabilityGraph Q selected).Walk a b) →
      {p : SignedPath Q a b //
        UsesNamedEdges (fun f => f ∈ selected) p}
  | .nil => ⟨signedNil Q _, UsesNamedEdges.nil _⟩
  | .cons h walk =>
      let first := selectedSignedEdgeOfAdj Q selected edges h
      let rest := selectedSignedPathOfWalk Q selected edges walk
      ⟨signedComp Q first.1 rest.1,
        usesNamedEdges_comp Q _ first.1 rest.1 first.2 rest.2⟩

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.selectedSignedStepCandidate
#print axioms AAT.AG.ProtocolHolonomy.selectedSignedStepCandidate_ne_none_of_pos
#print axioms AAT.AG.ProtocolHolonomy.selectedSignedStepCandidate_ne_none_of_neg
#print axioms AAT.AG.ProtocolHolonomy.selectedSignedEdgeOfAdj
#print axioms AAT.AG.ProtocolHolonomy.selectedSignedPathOfWalk

private def selectedWalkSmokeQ :
    AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := Bool
  source := fun _ => false
  target := fun _ => true

private def selectedWalkSmokeEdges :
    AAT.AG.ProtocolHolonomy.ExplicitEnumeration selectedWalkSmokeQ.Edge where
  values := [false, true]
  complete := by intro x; cases x <;> simp

#eval (letI : DecidableEq selectedWalkSmokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq selectedWalkSmokeQ.Edge := inferInstanceAs (DecidableEq Bool)
  letI : Quiver selectedWalkSmokeQ.Vertex :=
    AAT.AG.ProtocolHolonomy.typedQuiver selectedWalkSmokeQ
  letI : Quiver (Quiver.Symmetrify selectedWalkSmokeQ.Vertex) :=
    Quiver.symmetrifyQuiver selectedWalkSmokeQ.Vertex
  let h : (AAT.AG.ProtocolHolonomy.selectedReachabilityGraph
      selectedWalkSmokeQ {false}).Adj false true :=
    ⟨Bool.false_ne_true, Or.inl ⟨false, by simp, rfl, rfl⟩⟩
  (AAT.AG.ProtocolHolonomy.selectedSignedEdgeOfAdj
    selectedWalkSmokeQ {false} selectedWalkSmokeEdges h).1.length)

#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
