import ResearchLean.AG.ProtocolHolonomy.FiniteCentralizerDecision
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Formal.Util.AssertStandardAxioms

/-!
# Finite decision of original undirected components

Forget direction only for reachability, retaining the original named graph
as the source. Loop edges are irrelevant to component equality. The finite
simple graph's bounded-walk algorithm decides the existing component
quotient's equality from explicit finite vertex and edge lists.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- An undirected adjacency exists when some original named edge joins two
different vertices in either orientation. -/
def finiteReachabilityGraph (Q : FixedFDirectedMultigraph.{u, v}) :
    SimpleGraph Q.Vertex where
  Adj a b := a ≠ b ∧
    (fixedFDirectedEdgeStep Q a b ∨ fixedFDirectedEdgeStep Q b a)
  symm := by
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    refine ⟨?_⟩
    intro a h
    exact h.1 rfl

/-- The bounded simple-graph reachability predicate is exactly the original
endpoint equivalence closure, including loops and parallel named edges. -/
theorem finiteReachable_iff_original
    (Q : FixedFDirectedMultigraph.{u, v}) (a b : Q.Vertex) :
    (finiteReachabilityGraph Q).Reachable a b ↔
      FixedFUndirectedReachable Q a b := by
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

/-- Edge-table equality decision for the finite simple graph. -/
def finiteAdjDecidable (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (edges : ExplicitEnumeration Q.Edge) :
    DecidableRel (finiteReachabilityGraph Q).Adj := by
  letI : Fintype Q.Edge := edges.toFintype
  intro a b
  unfold finiteReachabilityGraph fixedFDirectedEdgeStep
  infer_instance

/-- Decidable equality on the original component quotient, computed via
bounded walks in the finite graph made from original endpoint tables. -/
def finiteComponentDecidableEq (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge) :
    DecidableEq (FixedFComponent Q) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : DecidableRel (finiteReachabilityGraph Q).Adj :=
    finiteAdjDecidable Q edges
  letI : DecidableRel (finiteReachabilityGraph Q).Reachable := inferInstance
  letI : (a b : Q.Vertex) → Decidable ((fixedFComponentSetoid Q).r a b) := by
    intro a b
    exact decidable_of_iff' _ (finiteReachable_iff_original Q a b).symm
  exact Quotient.decidableEq

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.finiteReachabilityGraph
#print axioms AAT.AG.ProtocolHolonomy.finiteReachable_iff_original
#print axioms AAT.AG.ProtocolHolonomy.finiteAdjDecidable
#print axioms AAT.AG.ProtocolHolonomy.finiteComponentDecidableEq

private def connectedSmokeQ : AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := PUnit
  source := fun _ => false
  target := fun _ => true

private def smokeVertices : AAT.AG.ProtocolHolonomy.ExplicitEnumeration Bool where
  values := [false, true]
  complete := by intro x; cases x <;> simp

private def connectedSmokeEdges :
    AAT.AG.ProtocolHolonomy.ExplicitEnumeration connectedSmokeQ.Edge where
  values := [PUnit.unit]
  complete := by intro x; cases x; simp

#eval (letI : DecidableEq connectedSmokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq connectedSmokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  letI : DecidableEq (AAT.AG.RealizationReconstruction.FixedFComponent connectedSmokeQ) :=
    (AAT.AG.ProtocolHolonomy.finiteComponentDecidableEq
      connectedSmokeQ smokeVertices connectedSmokeEdges)
  decide (AAT.AG.RealizationReconstruction.fixedFComponentMk connectedSmokeQ false =
    AAT.AG.RealizationReconstruction.fixedFComponentMk connectedSmokeQ true))

private def disconnectedSmokeQ : AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

private def disconnectedSmokeEdges :
    AAT.AG.ProtocolHolonomy.ExplicitEnumeration disconnectedSmokeQ.Edge where
  values := []
  complete := by intro x; exact Empty.elim x

#eval (letI : DecidableEq disconnectedSmokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq disconnectedSmokeQ.Edge := inferInstanceAs (DecidableEq Empty)
  letI : DecidableEq (AAT.AG.RealizationReconstruction.FixedFComponent disconnectedSmokeQ) :=
    (AAT.AG.ProtocolHolonomy.finiteComponentDecidableEq
      disconnectedSmokeQ smokeVertices disconnectedSmokeEdges)
  decide (AAT.AG.RealizationReconstruction.fixedFComponentMk disconnectedSmokeQ false =
    AAT.AG.RealizationReconstruction.fixedFComponentMk disconnectedSmokeQ true))

#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
