import ResearchLean.AG.ProtocolHolonomy.OneVertexTwoLoopsInput
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Formal.Util.AssertStandardAxioms

/-!
# The first fixed example's visible group

Every automorphism fixes its unique vertex. Its two named edges are either
fixed or exchanged, giving exactly the specified C₂ action.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

private theorem bool_perm_eq_one_or_swap (p : Equiv.Perm Bool) :
    p = 1 ∨ p = Equiv.swap false true := by
  cases hfalse : p false with
  | false =>
      left
      apply Equiv.ext
      intro x
      cases x with
      | false => exact hfalse
      | true =>
          have hne : p true ≠ false := by
            intro h
            have := p.injective (h.trans hfalse.symm)
            cases this
          cases htrue : p true <;> simp_all
  | true =>
      right
      apply Equiv.ext
      intro x
      cases x with
      | false => simpa using hfalse
      | true =>
          have hne : p true ≠ true := by
            intro h
            have := p.injective (h.trans hfalse.symm)
            cases this
          cases htrue : p true <;> simp_all

/-- The full graph automorphism group consists of the identity and the
exchange of the two original named loops. -/
theorem oneLoop_visible_eq_one_or_swap
    (g : FixedFGraphAutomorphism oneLoopGraph) :
    g = 1 ∨ g = oneLoopSwap := by
  rcases bool_perm_eq_one_or_swap g.edge with he | he
  · left
    apply FixedFGraphAutomorphism.ext
    · apply Equiv.ext
      intro x
      cases x
      rfl
    · exact he
  · right
    apply FixedFGraphAutomorphism.ext
    · apply Equiv.ext
      intro x
      cases x
      rfl
    · exact he

theorem oneLoopSwap_ne_one :
    oneLoopSwap ≠ (1 : FixedFGraphAutomorphism oneLoopGraph) := by
  intro h
  have he := congrArg (fun g : FixedFGraphAutomorphism oneLoopGraph => g.edge false) h
  change true = false at he
  cases he

theorem oneLoop_H_exact (g : oneLoopInput.H) :
    g.1 = 1 ∨ g.1 = oneLoopSwap :=
  oneLoop_visible_eq_one_or_swap g.1

/-- Any permutation of the two names defines a visible graph change. -/
def oneLoopGraphAutOfPerm (p : Equiv.Perm Bool) :
    FixedFGraphAutomorphism oneLoopGraph where
  vertex := Equiv.refl PUnit
  edge := p
  source_rename := by intro e; rfl
  target_rename := by intro e; rfl

/-- The actual chosen H is exactly the permutation group on the two named
loops, with its genuine graph-automorphism multiplication. -/
def oneLoopHEquivPermBool : oneLoopInput.H ≃* Equiv.Perm Bool where
  toFun g := g.1.edge
  invFun p := ⟨oneLoopGraphAutOfPerm p, by trivial⟩
  left_inv g := by
    apply Subtype.ext
    apply FixedFGraphAutomorphism.ext
    · apply Equiv.ext
      intro x
      cases x
      rfl
    · rfl
  right_inv p := rfl
  map_mul' _ _ := rfl

theorem oneLoop_H_card_two : Nat.card oneLoopInput.H = 2 := by
  rw [Nat.card_congr oneLoopHEquivPermBool.toEquiv]
  rw [Nat.card_perm]
  rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  decide

/-- Thus the actual visible subgroup is the cyclic group of order two. -/
theorem oneLoop_H_isCyclic : IsCyclic oneLoopInput.H :=
  isCyclic_of_prime_card oneLoop_H_card_two

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.oneLoop_visible_eq_one_or_swap
#print axioms AAT.AG.ProtocolHolonomy.oneLoopSwap_ne_one
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_H_exact
#print axioms AAT.AG.ProtocolHolonomy.oneLoopGraphAutOfPerm
#print axioms AAT.AG.ProtocolHolonomy.oneLoopHEquivPermBool
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_H_card_two
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_H_isCyclic
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
