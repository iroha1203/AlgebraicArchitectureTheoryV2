import ResearchLean.AG.ProtocolHolonomy.FiniteSelectedAllLifts
import Formal.Util.AssertStandardAxioms

/-!
# Fixed one-vertex, two-loop example: the name swap has no lift

The original edge `false` acts identically on Bool, while original edge
`true` swaps its two states. The visible graph change fixes the sole vertex
and swaps these two distinct edge names. Its original A1 edge square is
impossible at `false`; the selected-forest E procedure returns no lift.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

/-- One vertex and exactly two distinct named loops. -/
def oneLoopGraph : FixedFDirectedMultigraph.{0, 0} where
  Vertex := PUnit
  Edge := Bool
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit

instance : DecidableEq oneLoopGraph.Vertex := inferInstanceAs (DecidableEq PUnit)
instance : DecidableEq oneLoopGraph.Edge := inferInstanceAs (DecidableEq Bool)

/-- The specified identity and transposition edge actions on a two-point
fiber, without identifying the two original loop names. -/
def oneLoopData : ReversibleData.{0, 0, 0} oneLoopGraph where
  Fiber := fun _ => Bool
  edgeEquiv := fun e =>
    if e = true then Equiv.swap false true else Equiv.refl Bool

instance (x : oneLoopGraph.Vertex) :
    DecidableEq (oneLoopData.Fiber x) := inferInstanceAs (DecidableEq Bool)

/-- The visible change fixes the vertex and exchanges the original names. -/
def oneLoopSwap : FixedFGraphAutomorphism oneLoopGraph where
  vertex := Equiv.refl PUnit
  edge := Equiv.swap false true
  source_rename := by intro e; rfl
  target_rename := by intro e; rfl

/-- The unchanged original edge action cannot be conjugated to the swapped
action: A1 at the identity loop would fix a point under the transposition. -/
theorem oneLoopSwap_noLift : IsEmpty (oneLoopData.Lift oneLoopSwap) := by
  constructor
  intro a
  have h := a.edge_naturality false false
  change (a.fiber PUnit.unit) false =
    (Equiv.swap false true) ((a.fiber PUnit.unit) false) at h
  cases hv : (a.fiber PUnit.unit) false <;> simp [hv] at h

def oneLoopVertices : ExplicitEnumeration oneLoopGraph.Vertex where
  values := [PUnit.unit]
  complete := by intro x; cases x; simp

def oneLoopEdges : ExplicitEnumeration oneLoopGraph.Edge where
  values := [false, true]
  complete := by intro x; cases x <;> simp

def oneLoopFibers :
    ∀ x, ExplicitEnumeration (oneLoopData.Fiber x) := by
  intro x
  change ExplicitEnumeration Bool
  exact {
    values := [false, true]
    complete := by intro y; cases y <;> simp }

/-- The exact E search on this fixed input reports nonexistence of an
original A1 lift for the edge-name swap. -/
theorem oneLoopSwap_finiteSelected_none :
    oneLoopData.findSelectedRootLift oneLoopSwap
      oneLoopVertices oneLoopEdges oneLoopFibers = none := by
  have h := (oneLoopData.findSelectedRootLift_isSome_iff
    oneLoopSwap oneLoopVertices oneLoopEdges oneLoopFibers)
  cases hs : oneLoopData.findSelectedRootLift oneLoopSwap
      oneLoopVertices oneLoopEdges oneLoopFibers with
  | none => rfl
  | some a =>
      have hyes : Nonempty (oneLoopData.Lift oneLoopSwap) :=
        h.mp (by simp [hs])
      exact (oneLoopSwap_noLift.false hyes.some).elim

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.oneLoopGraph
#print axioms AAT.AG.ProtocolHolonomy.oneLoopData
#print axioms AAT.AG.ProtocolHolonomy.oneLoopSwap
#print axioms AAT.AG.ProtocolHolonomy.oneLoopSwap_noLift
#print axioms AAT.AG.ProtocolHolonomy.oneLoopSwap_finiteSelected_none
#eval (AAT.AG.ProtocolHolonomy.oneLoopData.findSelectedRootLift
  AAT.AG.ProtocolHolonomy.oneLoopSwap
  AAT.AG.ProtocolHolonomy.oneLoopVertices
  AAT.AG.ProtocolHolonomy.oneLoopEdges
  AAT.AG.ProtocolHolonomy.oneLoopFibers).isSome
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
