import ResearchLean.AG.ProtocolHolonomy.TwoVertexLiftableVisible
import Formal.Util.AssertStandardAxioms

/-!
# The two-vertex extension has no group section

The visible exchange has exactly two original A1 lifts. Both actual A2
changes above it have order four, while the visible exchange has order two.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

private theorem twoVertex_perm_cases_again (p : Equiv.Perm Bool) :
    p = 1 ∨ p = Equiv.swap false true := by
  rcases twoVertex_visible_eq_one_or_swap (twoVertexGraphAutOfPerm p) with h | h
  · exact Or.inl (congrArg
      (fun g : FixedFGraphAutomorphism twoVertexGraph => g.edge) h)
  · exact Or.inr (congrArg
      (fun g : FixedFGraphAutomorphism twoVertexGraph => g.edge) h)

/-- The two previously constructed A1 solutions exhaust the actual fiber
above the visible exchange. -/
theorem twoVertex_swap_lift_cases
    (a : twoVertexData.Lift twoVertexSwap) :
    a = twoVertexSwapLift ∨ a = twoVertexSecondSwapLift := by
  rcases twoVertex_perm_cases_again (a.fiber false) with h | h
  · left
    apply twoVertexSwapFiberEquivPermBool.injective
    simpa [twoVertexSwapFiberEquivPermBool, twoVertexSwapLift] using h
  · right
    apply twoVertexSwapFiberEquivPermBool.injective
    simpa [twoVertexSwapFiberEquivPermBool, twoVertexSecondSwapLift,
      twoVertexSwapLiftOfPerm] using h

/-- Every actual change over the visible exchange is one of the two
classified original A1 solutions, viewed in the original A2 group. -/
theorem twoVertex_swap_change_cases
    (c : twoVertexData.ChangeGroup twoVertexInput.H)
    (hc : (ReversibleData.ChangeGroup.projection c).1 = twoVertexSwap) :
    c = twoVertexCycleChange ∨ c = twoVertexSecondCycleChange := by
  let b : twoVertexData.StateChangeOver twoVertexSwap := ⟨c.1, hc⟩
  let a := (twoVertexData.liftEquivStateChangeOver twoVertexSwap).symm b
  have hab : (twoVertexData.liftEquivStateChangeOver twoVertexSwap) a = b :=
    Equiv.apply_symm_apply _ b
  rcases twoVertex_swap_lift_cases a with ha | ha
  · left
    rw [ha] at hab
    apply Subtype.ext
    exact (congrArg Subtype.val hab).symm
  · right
    rw [ha] at hab
    apply Subtype.ext
    exact (congrArg Subtype.val hab).symm

/-- The specified visible exchange is an involution in H. -/
def twoVertexVisibleSwap : twoVertexInput.H :=
  ⟨twoVertexSwap, twoVertexSwap_mem_H⟩

theorem twoVertexVisibleSwap_sq : twoVertexVisibleSwap ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply FixedFGraphAutomorphism.ext
  · apply Equiv.ext
    intro v
    cases v <;> rfl
  · apply Equiv.ext
    intro e
    cases e <;> rfl

/-- The original visible projection to H has no multiplicative section. -/
theorem twoVertex_no_group_section :
    ¬ ∃ s : twoVertexInput.H →*
        twoVertexData.ChangeGroup twoVertexInput.H,
      Function.RightInverse s
        (ReversibleData.ChangeGroup.projection
          (D := twoVertexData) (H := twoVertexInput.H)) := by
  rintro ⟨s, hs⟩
  have hp :
      (ReversibleData.ChangeGroup.projection (s twoVertexVisibleSwap)).1 =
        twoVertexSwap := by
    exact congrArg Subtype.val (hs twoVertexVisibleSwap)
  have hsquare : (s twoVertexVisibleSwap) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, ← pow_two, twoVertexVisibleSwap_sq, map_one]
  rcases twoVertex_swap_change_cases (s twoVertexVisibleSwap) hp with h | h
  · rw [h] at hsquare
    have hvertical : twoVertexVerticalChange = 1 :=
      twoVertexCycleChange_sq ▸ hsquare
    exact twoVertexVerticalChange_ne_one hvertical
  · rw [h] at hsquare
    have hvertical : twoVertexVerticalChange = 1 :=
      twoVertexSecondCycleChange_sq ▸ hsquare
    exact twoVertexVerticalChange_ne_one hvertical

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertex_swap_lift_cases
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_swap_change_cases
#print axioms AAT.AG.ProtocolHolonomy.twoVertexVisibleSwap_sq
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_no_group_section
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
