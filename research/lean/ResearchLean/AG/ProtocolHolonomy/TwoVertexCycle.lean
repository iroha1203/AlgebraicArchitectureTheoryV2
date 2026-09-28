import ResearchLean.AG.ProtocolHolonomy.TwoVertexVerticalGroup
import ResearchLean.AG.ProtocolHolonomy.LiftBridge
import Formal.Util.AssertStandardAxioms

/-!
# An order-four actual state change in the two-vertex fixed example

The explicit A1 lift of the visible exchange acts as a four-cycle on the
four original states. Its square is the nontrivial identity-visible
transposition on both fibers.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

/-- The chosen swap lift as an element of the actual operation-preserving
change group over the specified H. -/
def twoVertexCycleChange : twoVertexData.ChangeGroup twoVertexInput.H :=
  ⟨twoVertexSwapLift.toStateChange, by trivial⟩

/-- The explicit nontrivial vertical lift in the same actual change group. -/
def twoVertexVerticalChange : twoVertexData.ChangeGroup twoVertexInput.H :=
  ⟨twoVertexVerticalSwap.toStateChange, by trivial⟩

/-- The square of the visible-swap lift is the simultaneous fiber swap. -/
theorem twoVertexCycleChange_sq :
    twoVertexCycleChange ^ 2 = twoVertexVerticalChange := by
  rw [pow_two]
  apply Subtype.ext
  apply ReversibleData.StateChange.ext
  · apply FixedFGraphAutomorphism.ext
    · apply Equiv.ext
      intro x
      cases x <;> rfl
    · apply Equiv.ext
      intro e
      cases e <;> rfl
  · apply Equiv.ext
    intro p
    rcases p with ⟨v, x⟩
    cases v <;> cases x <;> rfl

/-- The nontrivial vertical change has order two in the actual A2 group. -/
theorem twoVertexVerticalChange_sq :
    twoVertexVerticalChange ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply ReversibleData.StateChange.ext
  · rfl
  · apply Equiv.ext
    intro p
    rcases p with ⟨v, x⟩
    cases v <;> cases x <;> rfl

theorem twoVertexCycleChange_ne_one : twoVertexCycleChange ≠ 1 := by
  intro h
  have hv := congrArg
    (fun c : twoVertexData.ChangeGroup twoVertexInput.H => c.1.visible.edge false) h
  change true = false at hv
  cases hv

theorem twoVertexVerticalChange_ne_one : twoVertexVerticalChange ≠ 1 := by
  intro h
  have hs := congrArg
    (fun c : twoVertexData.ChangeGroup twoVertexInput.H =>
      c.1.state ⟨false, false⟩) h
  have hx := congrArg Sigma.snd hs
  change true = false at hx
  cases hx

theorem twoVertexCycleChange_pow_four : twoVertexCycleChange ^ 4 = 1 := by
  calc
    twoVertexCycleChange ^ 4 = (twoVertexCycleChange ^ 2) ^ 2 := by group
    _ = 1 := by rw [twoVertexCycleChange_sq, twoVertexVerticalChange_sq]

theorem twoVertexCycleChange_order_four : orderOf twoVertexCycleChange = 4 := by
  apply (orderOf_eq_iff (by omega : 0 < 4)).mpr
  constructor
  · exact twoVertexCycleChange_pow_four
  · intro m hm hpos
    interval_cases m <;> norm_num at *
    · exact twoVertexCycleChange_ne_one
    · simpa [twoVertexCycleChange_sq] using twoVertexVerticalChange_ne_one
    · intro hthree
      have hfirst : twoVertexCycleChange = 1 := by
        calc
          twoVertexCycleChange = twoVertexCycleChange ^ 4 := by
            calc
              twoVertexCycleChange = twoVertexCycleChange *
                  (twoVertexCycleChange ^ 3) := by rw [hthree]; group
              _ = twoVertexCycleChange ^ 4 := by group
          _ = 1 := twoVertexCycleChange_pow_four
      exact twoVertexCycleChange_ne_one hfirst

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertexCycleChange
#print axioms AAT.AG.ProtocolHolonomy.twoVertexVerticalChange
#print axioms AAT.AG.ProtocolHolonomy.twoVertexCycleChange_sq
#print axioms AAT.AG.ProtocolHolonomy.twoVertexVerticalChange_sq
#print axioms AAT.AG.ProtocolHolonomy.twoVertexCycleChange_order_four
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
