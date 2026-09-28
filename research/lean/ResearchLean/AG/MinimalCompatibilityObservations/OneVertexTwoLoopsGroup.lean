import ResearchLean.AG.MinimalCompatibilityObservations.ProtocolFiberDisplay
import ResearchLean.AG.ProtocolHolonomy.OneVertexTwoLoopsLiftable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Formal.Util.AssertStandardAxioms

/-!
# G-128: the actual ambient and compatible groups in the two-loop example

The two factors retain their original meanings: the first permutes the two
named edges, while the second permutes the two states at the sole vertex.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy
open AAT.AG.RealizationReconstruction

/-- An ambient fiberwise pair over the fixed one-vertex example is precisely
a visible change together with its permutation of the sole Bool fiber. -/
def oneLoopFiberPairMulEquiv :
    AmbientFiberPair oneLoopData oneLoopInput.H ≃*
      (oneLoopInput.H × Equiv.Perm Bool) where
  toFun a := (a.1, a.2 PUnit.unit)
  invFun p := ⟨p.1, fun v => by cases v; exact p.2⟩
  left_inv a := by
    rcases a with ⟨u, f⟩
    have hf : (fun v => by cases v; exact f PUnit.unit) = f := by
      funext v
      cases v
      rfl
    exact congrArg (Sigma.mk u) hf
  right_inv p := rfl
  map_mul' a b := by
    apply Prod.ext
    · rfl
    · apply Equiv.ext
      intro x
      have hv : b.1.1.vertex PUnit.unit = PUnit.unit := by
        cases b.1.1.vertex PUnit.unit
        rfl
      simpa only [hv, Equiv.Perm.mul_apply] using
        (fiberPair_mul_fiber_apply oneLoopData oneLoopInput.H a b PUnit.unit x)

/-- The fixed G-127 input's ambient group, with its actual multiplication,
is the product of edge-name and state permutations. -/
noncomputable def oneLoopAmbientEquiv :
    ambientChange oneLoopData oneLoopInput.H ≃*
      (Equiv.Perm Bool × Equiv.Perm Bool) :=
  (ambientMulEquivFiberPair oneLoopData oneLoopInput.H).trans
    (oneLoopFiberPairMulEquiv.trans {
      toFun := fun p => (oneLoopHEquivPermBool p.1, p.2)
      invFun := fun p => (oneLoopHEquivPermBool.symm p.1, p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      map_mul' := by intro p q; simp })

@[simp] theorem oneLoopAmbientEquiv_first
    (a : ambientChange oneLoopData oneLoopInput.H) :
    (oneLoopAmbientEquiv a).1 = oneLoopHEquivPermBool a.1.1 := rfl

@[simp] theorem oneLoopAmbientEquiv_second
    (a : ambientChange oneLoopData oneLoopInput.H) :
    (oneLoopAmbientEquiv a).2 =
      (ambientEquivFiberPair oneLoopData oneLoopInput.H a).2 PUnit.unit := rfl

/-- The state factor is itself cyclic of order two. Together with the
original `oneLoop_H_card_two`, this identifies both displayed factors as C₂. -/
theorem oneLoop_state_factor_card_two :
    Nat.card (Equiv.Perm Bool) = 2 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_bool]
  decide

theorem oneLoop_state_factor_isCyclic : IsCyclic (Equiv.Perm Bool) :=
  isCyclic_of_prime_card oneLoop_state_factor_card_two

/-- Every Bool-fiber permutation commutes with both original named actions.
This is the centralizer computation in the concrete one-vertex presentation. -/
private theorem oneLoop_fiber_pair_compatible_of_visible_one
    (a : AmbientFiberPair oneLoopData oneLoopInput.H)
    (ha : a.1 = 1) : a ∈ fiberCompatible oneLoopData oneLoopInput.H := by
  rcases a with ⟨u, f⟩
  change u = 1 at ha
  subst u
  letI : IsCyclic (Equiv.Perm Bool) := oneLoop_state_factor_isCyclic
  letI : CommGroup (Equiv.Perm Bool) := IsCyclic.commGroup
  rw [mem_fiberCompatible_iff]
  intro e x
  let p : Equiv.Perm Bool := f PUnit.unit
  let T : Equiv.Perm Bool := oneLoopData.edgeEquiv e
  have hcomm : p * T = T * p := mul_comm p T
  have hpoint := congrArg (fun p : Equiv.Perm Bool => p x) hcomm
  change p (T x) = T (p x)
  simpa only [Equiv.Perm.mul_apply] using hpoint

/-- The original G-127 compatible subgroup is exactly the identity-visible
factor of the actual ambient product. -/
theorem oneLoop_compatible_iff_first_one
    (a : ambientChange oneLoopData oneLoopInput.H) :
    a ∈ compatibleChange oneLoopData oneLoopInput.H ↔
      (oneLoopAmbientEquiv a).1 = 1 := by
  constructor
  · intro ha
    let c : compatibleChange oneLoopData oneLoopInput.H := ⟨a, ha⟩
    have hc : compatibleVisible oneLoopData oneLoopInput.H c ∈
        oneLoopData.LiftableVisible oneLoopInput.H := by
      exact ⟨compatibleMulEquivChangeGroup oneLoopData oneLoopInput.H c,
        (compatibleMulEquiv_projection oneLoopData oneLoopInput.H c)⟩
    rw [oneLoop_H_lift_eq_bot] at hc
    have hvisible : a.1.1 = 1 := Subgroup.mem_bot.mp hc
    simp [oneLoopAmbientEquiv_first, hvisible]
  · intro ha
    have hv : a.1.1 = 1 := oneLoopHEquivPermBool.injective (by
      simpa [oneLoopAmbientEquiv_first] using ha)
    have hpair : ambientEquivFiberPair oneLoopData oneLoopInput.H a ∈
        fiberCompatible oneLoopData oneLoopInput.H :=
      oneLoop_fiber_pair_compatible_of_visible_one
        (ambientEquivFiberPair oneLoopData oneLoopInput.H a) (by
          simpa using hv)
    rw [fiberCompatible, Subgroup.mem_map_equiv] at hpair
    simpa using hpair

end AAT.AG.MinimalCompatibilityObservations

#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopFiberPairMulEquiv
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopAmbientEquiv
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopAmbientEquiv_first
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoopAmbientEquiv_second
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_state_factor_card_two
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_state_factor_isCyclic
#print axioms AAT.AG.MinimalCompatibilityObservations.oneLoop_compatible_iff_first_one
#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
