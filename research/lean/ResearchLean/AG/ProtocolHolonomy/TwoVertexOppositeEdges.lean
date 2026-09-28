import ResearchLean.AG.ProtocolHolonomy.OneVertexTwoLoopsLiftable
import Formal.Util.AssertStandardAxioms

/-!
# Fixed two-vertex, opposite-edge example

The original names `false` and `true` are the edges 0→1 and 1→0.
Their Bool-fiber actions are identity and transposition. The visible change
exchanges both vertices and both original edge names, and admits an
explicit original A1 lift.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

def twoVertexGraph : FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := Bool
  source := id
  target := fun e => !e

instance : DecidableEq twoVertexGraph.Vertex := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq twoVertexGraph.Edge := inferInstanceAs (DecidableEq Bool)

def twoVertexData : ReversibleData.{0, 0, 0} twoVertexGraph where
  Fiber := fun _ => Bool
  edgeEquiv := fun e =>
    if e = true then Equiv.swap false true else Equiv.refl Bool

instance (x : twoVertexGraph.Vertex) :
    DecidableEq (twoVertexData.Fiber x) := inferInstanceAs (DecidableEq Bool)

/-- Simultaneous vertex and original edge-name exchange. -/
def twoVertexSwap : FixedFGraphAutomorphism twoVertexGraph where
  vertex := Equiv.swap false true
  edge := Equiv.swap false true
  source_rename := by intro e; cases e <;> rfl
  target_rename := by intro e; cases e <;> rfl

/-- An A1 lift of the visible exchange: identity at vertex 0 and the
transposition at vertex 1. -/
def twoVertexSwapLift : twoVertexData.Lift twoVertexSwap where
  fiber := fun v => if v = true then Equiv.swap false true else Equiv.refl Bool
  edge_naturality := by
    intro e x
    cases e <;> cases x <;> rfl

/-- There are no authored path equations in the fixed example. -/
def twoVertexEmptyEquations : PathEquations twoVertexGraph where
  Index := PEmpty
  finiteIndex := inferInstance
  source := PEmpty.elim
  target := PEmpty.elim
  left := fun r => PEmpty.elim r
  right := fun r => PEmpty.elim r

/-- The complete finite primitive input with its full visible graph
automorphism subgroup. Its identification with C₂ is proved separately. -/
def twoVertexInput : FiniteProtocolInput twoVertexGraph where
  data := twoVertexData
  finiteVertex := by change Finite Bool; infer_instance
  finiteEdge := by change Finite Bool; infer_instance
  finiteFiber := by
    intro x
    change Finite Bool
    infer_instance
  equations := twoVertexEmptyEquations
  satisfies := fun r => PEmpty.elim r
  H := ⊤
  renaming_preserves := fun _ _ r => PEmpty.elim r

theorem twoVertexSwap_mem_H : twoVertexSwap ∈ twoVertexInput.H := by
  trivial

theorem twoVertexInput_no_equations : IsEmpty twoVertexInput.equations.Index := by
  change IsEmpty PEmpty
  infer_instance

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertexGraph
#print axioms AAT.AG.ProtocolHolonomy.twoVertexData
#print axioms AAT.AG.ProtocolHolonomy.twoVertexSwap
#print axioms AAT.AG.ProtocolHolonomy.twoVertexSwapLift
#print axioms AAT.AG.ProtocolHolonomy.twoVertexEmptyEquations
#print axioms AAT.AG.ProtocolHolonomy.twoVertexInput
#print axioms AAT.AG.ProtocolHolonomy.twoVertexSwap_mem_H
#print axioms AAT.AG.ProtocolHolonomy.twoVertexInput_no_equations
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
