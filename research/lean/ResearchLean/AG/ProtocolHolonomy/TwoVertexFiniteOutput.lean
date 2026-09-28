import ResearchLean.AG.ProtocolHolonomy.TwoVertexNoSection
import ResearchLean.AG.ProtocolHolonomy.FiniteSelectedAllLifts
import Formal.Util.AssertStandardAxioms

/-!
# The finite E output in the two-vertex fixed example

The supplied tables enumerate the two original vertices, opposite edge
names, and the two states in each fiber. The selected-forest C1 search
returns one original swap lift, and its C3/B2 expansion lists exactly the
two classified A1 solutions.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

def twoVertexVertices : ExplicitEnumeration twoVertexGraph.Vertex where
  values := [false, true]
  complete := by intro x; cases x <;> simp

def twoVertexEdges : ExplicitEnumeration twoVertexGraph.Edge where
  values := [false, true]
  complete := by intro e; cases e <;> simp

def twoVertexFibers :
    ∀ x, ExplicitEnumeration (twoVertexData.Fiber x) := by
  intro x
  change ExplicitEnumeration Bool
  exact {
    values := [false, true]
    complete := by intro y; cases y <;> simp }

/-- On the actual finite input, E's selected-tree search returns an
original A1 lift of the visible exchange, and it is one of the two
classified solutions. -/
theorem twoVertex_finite_selected_some :
    ∃ a : twoVertexData.Lift twoVertexSwap,
      twoVertexData.findSelectedRootLift twoVertexSwap
        twoVertexVertices twoVertexEdges twoVertexFibers = some a ∧
      (a = twoVertexSwapLift ∨ a = twoVertexSecondSwapLift) := by
  have h := (twoVertexData.findSelectedRootLift_isSome_iff
    twoVertexSwap twoVertexVertices twoVertexEdges twoVertexFibers).mpr
      ⟨twoVertexSwapLift⟩
  cases hs : twoVertexData.findSelectedRootLift twoVertexSwap
      twoVertexVertices twoVertexEdges twoVertexFibers with
  | none => simp [hs] at h
  | some a => exact ⟨a, rfl, twoVertex_swap_lift_cases a⟩

/-- The actual finite C1/B2/C3 all-lifts output contains precisely the
two original A1 swap solutions. -/
theorem twoVertex_mem_finite_all_lifts
    (a : twoVertexData.Lift twoVertexSwap) :
    a ∈ twoVertexData.finiteSelectedAllLifts twoVertexSwap
      twoVertexVertices twoVertexEdges twoVertexFibers ↔
      a = twoVertexSwapLift ∨ a = twoVertexSecondSwapLift := by
  constructor
  · intro _
    exact twoVertex_swap_lift_cases a
  · intro _
    exact twoVertexData.mem_finiteSelectedAllLifts
      twoVertexSwap twoVertexVertices twoVertexEdges twoVertexFibers a

theorem twoVertex_first_mem_finite_all_lifts :
    twoVertexSwapLift ∈ twoVertexData.finiteSelectedAllLifts
      twoVertexSwap twoVertexVertices twoVertexEdges twoVertexFibers :=
  (twoVertex_mem_finite_all_lifts twoVertexSwapLift).mpr (Or.inl rfl)

theorem twoVertex_second_mem_finite_all_lifts :
    twoVertexSecondSwapLift ∈ twoVertexData.finiteSelectedAllLifts
      twoVertexSwap twoVertexVertices twoVertexEdges twoVertexFibers :=
  (twoVertex_mem_finite_all_lifts twoVertexSecondSwapLift).mpr (Or.inr rfl)

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertexVertices
#print axioms AAT.AG.ProtocolHolonomy.twoVertexEdges
#print axioms AAT.AG.ProtocolHolonomy.twoVertexFibers
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_finite_selected_some
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_mem_finite_all_lifts
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
