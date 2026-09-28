import ResearchLean.AG.ProtocolHolonomy.FiniteComponents
import Formal.Util.AssertStandardAxioms

/-!
# Executable original named-edge paths from finite undirected walks

Each adjacency step of the finite reachability graph is resolved by scanning
the original edge table for a forward or reverse named edge. Thus a finite
simple-graph walk yields an original signed named path without choosing an
edge witness noncomputably. Root-path selection and spanning-forest assembly
are separate E obligations.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- Test one original edge name for a signed passage between two vertices. -/
def signedStepCandidate (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] (a b : Q.Vertex) (e : Q.Edge) :
    Option (SignedPath Q a b) :=
  if hpos : Q.source e = a ∧ Q.target e = b then
    some (signedToPath Q (Sum.inl ⟨e, hpos.1, hpos.2⟩))
  else if hneg : Q.target e = a ∧ Q.source e = b then
    some (signedToPath Q (Sum.inr ⟨e, hneg.2, hneg.1⟩))
  else none

theorem signedStepCandidate_ne_none_of_pos
    (Q : FixedFDirectedMultigraph.{u, v}) [DecidableEq Q.Vertex]
    (a b : Q.Vertex) (e : Q.Edge)
    (h : Q.source e = a ∧ Q.target e = b) :
    signedStepCandidate Q a b e ≠ none := by
  simp [signedStepCandidate, h]

theorem signedStepCandidate_ne_none_of_neg
    (Q : FixedFDirectedMultigraph.{u, v}) [DecidableEq Q.Vertex]
    (a b : Q.Vertex) (e : Q.Edge)
    (h : Q.target e = a ∧ Q.source e = b) :
    signedStepCandidate Q a b e ≠ none := by
  unfold signedStepCandidate
  split_ifs <;> simp_all

/-- A complete original edge list yields a signed named passage for every
finite-graph adjacency. The returned path is computed by list search. -/
def signedEdgeOfAdj (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex]
    (edges : ExplicitEnumeration Q.Edge) {a b : Q.Vertex}
    (h : (finiteReachabilityGraph Q).Adj a b) : SignedPath Q a b := by
  let scan := edges.values.findSome? (signedStepCandidate Q a b)
  have hscan : scan ≠ none := by
    intro hn
    have hnone := List.findSome?_eq_none_iff.mp hn
    rcases h.2 with hp | hn
    · obtain ⟨e, hs, ht⟩ := hp
      exact (signedStepCandidate_ne_none_of_pos Q a b e ⟨hs, ht⟩)
        (hnone e (edges.complete e))
    · obtain ⟨e, hs, ht⟩ := hn
      exact (signedStepCandidate_ne_none_of_neg Q a b e ⟨ht, hs⟩)
        (hnone e (edges.complete e))
  cases hs : scan with
  | none => exact (hscan hs).elim
  | some p => exact p

/-- Convert every step of a finite undirected walk to an original signed
named edge, retaining the orientation chosen by the edge-table search. -/
def signedPathOfFiniteWalk (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex]
    (edges : ExplicitEnumeration Q.Edge)
    {a b : Q.Vertex} : (p : (finiteReachabilityGraph Q).Walk a b) →
    SignedPath Q a b
  | .nil => signedNil Q _
  | .cons h p =>
      signedComp Q (signedEdgeOfAdj Q edges h)
        (signedPathOfFiniteWalk Q edges p)

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.signedStepCandidate
#print axioms AAT.AG.ProtocolHolonomy.signedStepCandidate_ne_none_of_pos
#print axioms AAT.AG.ProtocolHolonomy.signedStepCandidate_ne_none_of_neg
#print axioms AAT.AG.ProtocolHolonomy.signedEdgeOfAdj
#print axioms AAT.AG.ProtocolHolonomy.signedPathOfFiniteWalk

private def smokeQ : AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := Bool
  source := fun _ => false
  target := fun _ => true

private def smokeEdges : AAT.AG.ProtocolHolonomy.ExplicitEnumeration smokeQ.Edge where
  values := [false, true]
  complete := by intro x; cases x <;> simp

private def smokeLastPassage {a b : smokeQ.Vertex}
    (p : AAT.AG.ProtocolHolonomy.SignedPath smokeQ a b) :
    Option (Bool × smokeQ.Edge) := by
  letI : Quiver smokeQ.Vertex := AAT.AG.ProtocolHolonomy.typedQuiver smokeQ
  letI : Quiver (Quiver.Symmetrify smokeQ.Vertex) :=
    Quiver.symmetrifyQuiver smokeQ.Vertex
  cases p with
  | nil => exact none
  | cons _ e =>
      cases e with
      | inl f => exact some (true, f.1)
      | inr f => exact some (false, f.1)

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : Quiver smokeQ.Vertex := AAT.AG.ProtocolHolonomy.typedQuiver smokeQ
  letI : Quiver (Quiver.Symmetrify smokeQ.Vertex) :=
    Quiver.symmetrifyQuiver smokeQ.Vertex
  let h : (AAT.AG.ProtocolHolonomy.finiteReachabilityGraph smokeQ).Adj false true :=
    ⟨Bool.false_ne_true, Or.inl ⟨false, rfl, rfl⟩⟩
  (AAT.AG.ProtocolHolonomy.signedEdgeOfAdj smokeQ smokeEdges h).length)

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  let h : (AAT.AG.ProtocolHolonomy.finiteReachabilityGraph smokeQ).Adj false true :=
    ⟨Bool.false_ne_true, Or.inl ⟨false, rfl, rfl⟩⟩
  smokeLastPassage (AAT.AG.ProtocolHolonomy.signedEdgeOfAdj smokeQ smokeEdges h))

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : Quiver smokeQ.Vertex := AAT.AG.ProtocolHolonomy.typedQuiver smokeQ
  letI : Quiver (Quiver.Symmetrify smokeQ.Vertex) :=
    Quiver.symmetrifyQuiver smokeQ.Vertex
  let h : (AAT.AG.ProtocolHolonomy.finiteReachabilityGraph smokeQ).Adj true false :=
    ⟨by decide, Or.inr ⟨false, rfl, rfl⟩⟩
  (AAT.AG.ProtocolHolonomy.signedEdgeOfAdj smokeQ smokeEdges h).length)

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  let h : (AAT.AG.ProtocolHolonomy.finiteReachabilityGraph smokeQ).Adj true false :=
    ⟨by decide, Or.inr ⟨false, rfl, rfl⟩⟩
  smokeLastPassage (AAT.AG.ProtocolHolonomy.signedEdgeOfAdj smokeQ smokeEdges h))

#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
