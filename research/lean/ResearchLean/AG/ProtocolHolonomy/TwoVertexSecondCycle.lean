import ResearchLean.AG.ProtocolHolonomy.TwoVertexTotalGroup
import Formal.Util.AssertStandardAxioms

/-!
# The second original swap lift also has order four

The other A1 solution above the visible exchange is converted to the actual
A2 change group. Its square is the same nontrivial vertical change.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

/-- The second A1 swap lift as an actual operation-preserving change. -/
def twoVertexSecondCycleChange :
    twoVertexData.ChangeGroup twoVertexInput.H :=
  ⟨twoVertexSecondSwapLift.toStateChange, by trivial⟩

theorem twoVertexSecondCycleChange_sq :
    twoVertexSecondCycleChange ^ 2 = twoVertexVerticalChange := by
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

theorem twoVertexSecondCycleChange_ne_one :
    twoVertexSecondCycleChange ≠ 1 := by
  intro h
  have hv := congrArg
    (fun c : twoVertexData.ChangeGroup twoVertexInput.H =>
      c.1.visible.edge false) h
  change true = false at hv
  cases hv

theorem twoVertexSecondCycleChange_pow_four :
    twoVertexSecondCycleChange ^ 4 = 1 := by
  calc
    twoVertexSecondCycleChange ^ 4 =
        (twoVertexSecondCycleChange ^ 2) ^ 2 := by group
    _ = 1 := by rw [twoVertexSecondCycleChange_sq,
      twoVertexVerticalChange_sq]

/-- Every classified swap lift has order four: this is the second of the
two original A1 solutions. -/
theorem twoVertexSecondCycleChange_order_four :
    orderOf twoVertexSecondCycleChange = 4 := by
  apply (orderOf_eq_iff (by omega : 0 < 4)).mpr
  constructor
  · exact twoVertexSecondCycleChange_pow_four
  · intro m hm hpos
    interval_cases m <;> norm_num at *
    · exact twoVertexSecondCycleChange_ne_one
    · simpa [twoVertexSecondCycleChange_sq] using
        twoVertexVerticalChange_ne_one
    · intro hthree
      have hfirst : twoVertexSecondCycleChange = 1 := by
        calc
          twoVertexSecondCycleChange = twoVertexSecondCycleChange ^ 4 := by
            calc
              twoVertexSecondCycleChange = twoVertexSecondCycleChange *
                  (twoVertexSecondCycleChange ^ 3) := by rw [hthree]; group
              _ = twoVertexSecondCycleChange ^ 4 := by group
          _ = 1 := twoVertexSecondCycleChange_pow_four
      exact twoVertexSecondCycleChange_ne_one hfirst

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertexSecondCycleChange
#print axioms AAT.AG.ProtocolHolonomy.twoVertexSecondCycleChange_sq
#print axioms AAT.AG.ProtocolHolonomy.twoVertexSecondCycleChange_order_four
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
