import ResearchLean.AG.ProtocolHolonomy.TwoVertexVisibleGroup
import ResearchLean.AG.ProtocolHolonomy.VerticalCentralizer
import Formal.Util.AssertStandardAxioms

/-!
# Actual vertical C₂ in the two-vertex fixed example

The identity edge transports unchanged from vertex 0 to vertex 1, forcing
the two fiber permutations of any vertical A1 lift to be equal. Every
permutation of the Bool fiber commutes with the other, transposition edge.
Root evaluation at vertex 0 is therefore a group isomorphism for the
actual A2 vertical multiplication.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

private theorem twoVertex_bool_perm_eq_one_or_swap (p : Equiv.Perm Bool) :
    p = 1 ∨ p = Equiv.swap false true := by
  rcases twoVertex_visible_eq_one_or_swap (twoVertexGraphAutOfPerm p) with h | h
  · exact Or.inl (congrArg
      (fun g : FixedFGraphAutomorphism twoVertexGraph => g.edge) h)
  · exact Or.inr (congrArg
      (fun g : FixedFGraphAutomorphism twoVertexGraph => g.edge) h)

/-- The same Bool permutation at both vertices is an original vertical A1
change: it commutes with both specified edge actions. -/
def twoVertexVerticalOfPerm (p : Equiv.Perm Bool) :
    twoVertexData.Lift (1 : FixedFGraphAutomorphism twoVertexGraph) where
  fiber := fun _ => p
  edge_naturality := by
    intro e x
    rcases twoVertex_bool_perm_eq_one_or_swap p with hp | hp
    · subst p; cases e <;> cases x <;> rfl
    · subst p; cases e <;> cases x <;> rfl

/-- The original identity edge forces equality of a vertical lift's two
fiber permutations. -/
theorem twoVertex_vertical_fibers_eq
    (a : twoVertexData.Lift (1 : FixedFGraphAutomorphism twoVertexGraph)) :
    a.fiber true = a.fiber false := by
  apply Equiv.ext
  intro x
  have h := a.edge_naturality false x
  exact h

/-- The actual vertical A1 group, with its A2-derived multiplication, is
the permutation group of the Bool fiber at vertex 0. -/
noncomputable def twoVertexVerticalEquivPermBool :
    twoVertexData.Lift (1 : FixedFGraphAutomorphism twoVertexGraph) ≃*
      Equiv.Perm Bool where
  toFun a := a.fiber false
  invFun := twoVertexVerticalOfPerm
  left_inv a := by
    apply ReversibleData.Lift.ext
    intro v x
    cases v with
    | false => rfl
    | true =>
        exact congrArg (fun p : Equiv.Perm Bool => p x)
          (twoVertex_vertical_fibers_eq a).symm
  right_inv p := rfl
  map_mul' a b := by
    apply Equiv.ext
    intro x
    exact twoVertexData.vertical_mul_fiber_apply a b false x

theorem twoVertex_vertical_card_two :
    Nat.card (twoVertexData.Lift
      (1 : FixedFGraphAutomorphism twoVertexGraph)) = 2 := by
  rw [Nat.card_congr twoVertexVerticalEquivPermBool.toEquiv]
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_bool]
  decide

theorem twoVertex_vertical_isCyclic :
    IsCyclic (twoVertexData.Lift
      (1 : FixedFGraphAutomorphism twoVertexGraph)) :=
  isCyclic_of_prime_card twoVertex_vertical_card_two

/-- The nontrivial vertical A1 change uses transposition at both vertices. -/
def twoVertexVerticalSwap :
    twoVertexData.Lift (1 : FixedFGraphAutomorphism twoVertexGraph) :=
  twoVertexVerticalOfPerm (Equiv.swap false true)

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertexVerticalOfPerm
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_vertical_fibers_eq
#print axioms AAT.AG.ProtocolHolonomy.twoVertexVerticalEquivPermBool
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_vertical_card_two
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_vertical_isCyclic
#print axioms AAT.AG.ProtocolHolonomy.twoVertexVerticalSwap
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
