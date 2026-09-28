import ResearchLean.AG.ProtocolHolonomy.TwoVertexFiniteOutput
import ResearchLean.AG.ProtocolHolonomy.LiftFiberTorsor
import Formal.Util.AssertStandardAxioms

/-!
# The actual C torsor in the two-vertex fixed example

The specified visible exchange has two original A1 lifts. The nontrivial
original vertical A1 change sends the first to the second by the literal
right action on fiber maps. Freeness and transitivity give the unique
vertical displacement between any two lifts.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

/-- The visible swap as an element of the actual liftable C1 image. -/
def twoVertexSwapLiftable :
    twoVertexData.LiftableVisible twoVertexInput.H :=
  ⟨twoVertexVisibleSwap,
    (twoVertexData.mem_liftableVisible_iff_lift
      twoVertexInput.H twoVertexVisibleSwap).mpr ⟨twoVertexSwapLift⟩⟩

/-- The literal C right action by simultaneous vertical transposition
turns the first original swap lift into the second. -/
theorem twoVertex_rightAction_swap :
    twoVertexData.verticalRightAction twoVertexInput.H
      twoVertexSwapLiftable twoVertexSwapLift twoVertexVerticalSwap =
      twoVertexSecondSwapLift := by
  apply ReversibleData.Lift.ext
  intro v x
  rw [twoVertexData.verticalRightAction_fiber_apply]
  cases v <;> cases x <;> rfl

theorem twoVertex_rightAction_one :
    twoVertexData.verticalRightAction twoVertexInput.H
      twoVertexSwapLiftable twoVertexSwapLift 1 =
      twoVertexSwapLift :=
  twoVertexData.verticalRightAction_one
    twoVertexInput.H twoVertexSwapLiftable twoVertexSwapLift

/-- Every original swap lift is obtained from the first by an explicit
vertical change. -/
theorem twoVertex_rightAction_reaches_both
    (b : twoVertexData.Lift twoVertexSwap) :
    ∃ α : twoVertexData.Lift
        (1 : FixedFGraphAutomorphism twoVertexGraph),
      twoVertexData.verticalRightAction twoVertexInput.H
        twoVertexSwapLiftable twoVertexSwapLift α = b := by
  rcases twoVertex_swap_lift_cases b with h | h
  · exact ⟨1, by rw [h]; exact twoVertex_rightAction_one⟩
  · exact ⟨twoVertexVerticalSwap, by
      rw [h]
      exact twoVertex_rightAction_swap⟩

/-- The specified two-element swap-lift fiber is a free transitive right
torsor under the actual original vertical A1 group. -/
theorem twoVertex_rightAction_existsUnique
    (a b : twoVertexData.Lift twoVertexSwap) :
    ∃! α : twoVertexData.Lift
        (1 : FixedFGraphAutomorphism twoVertexGraph),
      twoVertexData.verticalRightAction twoVertexInput.H
        twoVertexSwapLiftable a α = b :=
  twoVertexData.verticalRightAction_existsUnique
    twoVertexInput.H twoVertexSwapLiftable a b

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertexSwapLiftable
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_rightAction_swap
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_rightAction_reaches_both
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_rightAction_existsUnique
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
