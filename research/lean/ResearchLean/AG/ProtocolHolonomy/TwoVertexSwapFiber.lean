import ResearchLean.AG.ProtocolHolonomy.TwoVertexCycle
import Formal.Util.AssertStandardAxioms

/-!
# All original A1 lifts above the two-vertex visible exchange

The original identity edge determines the fiber map at vertex 1 from the
arbitrary Bool permutation at vertex 0. The second edge holds because all
Bool permutations commute with the specified transposition. Hence the
actual swap-lift fiber has precisely two elements.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

private theorem twoVertex_swap_perm_cases (p : Equiv.Perm Bool) :
    p = 1 ∨ p = Equiv.swap false true := by
  rcases twoVertex_visible_eq_one_or_swap (twoVertexGraphAutOfPerm p) with h | h
  · exact Or.inl (congrArg
      (fun g : FixedFGraphAutomorphism twoVertexGraph => g.edge) h)
  · exact Or.inr (congrArg
      (fun g : FixedFGraphAutomorphism twoVertexGraph => g.edge) h)

/-- Every choice at vertex 0 yields an original A1 lift of the simultaneous
visible exchange, with vertex-1 map equal to transposition after that choice. -/
def twoVertexSwapLiftOfPerm (p : Equiv.Perm Bool) :
    twoVertexData.Lift twoVertexSwap where
  fiber := fun v => if v = true then p.trans (Equiv.swap false true) else p
  edge_naturality := by
    intro e x
    rcases twoVertex_swap_perm_cases p with hp | hp
    · subst p; cases e <;> cases x <;> rfl
    · subst p; cases e <;> cases x <;> rfl

/-- The original false-edge A1 square forces the vertex-1 fiber map. -/
theorem twoVertex_swap_fiber_true
    (a : twoVertexData.Lift twoVertexSwap) :
    a.fiber true = (a.fiber false).trans (Equiv.swap false true) := by
  apply Equiv.ext
  intro x
  have h := a.edge_naturality false x
  exact h

/-- The complete original lift fiber over the visible swap is the two-point
permutation space, read at vertex 0. -/
def twoVertexSwapFiberEquivPermBool :
    twoVertexData.Lift twoVertexSwap ≃ Equiv.Perm Bool where
  toFun a := a.fiber false
  invFun := twoVertexSwapLiftOfPerm
  left_inv a := by
    apply ReversibleData.Lift.ext
    intro v x
    cases v with
    | false => rfl
    | true =>
        exact congrArg (fun p : Equiv.Perm Bool => p x)
          (twoVertex_swap_fiber_true a).symm
  right_inv p := rfl

theorem twoVertex_swap_fiber_card_two :
    Nat.card (twoVertexData.Lift twoVertexSwap) = 2 := by
  rw [Nat.card_congr twoVertexSwapFiberEquivPermBool]
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_bool]
  decide

/-- The other original A1 lift has a transposition at vertex 0 and identity
at vertex 1. -/
def twoVertexSecondSwapLift : twoVertexData.Lift twoVertexSwap :=
  twoVertexSwapLiftOfPerm (Equiv.swap false true)

theorem twoVertex_second_swap_ne_first :
    twoVertexSecondSwapLift ≠ twoVertexSwapLift := by
  intro h
  have hf := congrArg
    (fun a : twoVertexData.Lift twoVertexSwap => a.fiber false false) h
  change true = false at hf
  cases hf

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertexSwapLiftOfPerm
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_swap_fiber_true
#print axioms AAT.AG.ProtocolHolonomy.twoVertexSwapFiberEquivPermBool
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_swap_fiber_card_two
#print axioms AAT.AG.ProtocolHolonomy.twoVertexSecondSwapLift
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_second_swap_ne_first
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
