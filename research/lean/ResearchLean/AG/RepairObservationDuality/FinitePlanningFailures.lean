import ResearchLean.AG.RepairObservationDuality.FiniteMinimumPlan

/-!
# G-131 D: finite symbolic failure certificates for primitive planning

## Implementation notes

A failed plan returns an actual unknown direction, from the complete finite
parameter enumeration, invisible to every original primitive but changing
the specified target. Adding this direction to a generated successful base
produces the indistinguishable input used for impossibility. No supplied
correct procedure or supplied counterexample is an algorithm input.
-/
namespace AAT.AG.RepairObservationDuality.FinitePlanningFailures
open RelativeRepairComposition
variable {k V I W J : Type*} [Field k] [DecidableEq k]
variable [AddCommGroup V] [Module k V] [AddCommGroup I] [Module k I] [DecidableEq I]
variable [AddCommGroup W] [Module k W] [DecidableEq W] [DecidableEq J]
variable (enumV : FiniteElimination.Enumeration V) (enumJ : FiniteElimination.Enumeration J)
variable (lam : J → V →ₗ[k] k) (L : V →ₗ[k] I) (Q : V →ₗ[k] W)

/-- D searches for a genuine direction invisible to all allowed primitive replies but changing the target. -/
def findDirection : Option V := enumV.values.find? fun n =>
  decide (L n = 0 ∧ (∀ j ∈ enumJ.values, lam j n = 0) ∧ Q n ≠ 0)

omit [DecidableEq J] in
/-- Every returned finite direction has all three independent failure properties. -/
theorem findDirection_spec {n : V}
    (hn : findDirection enumV enumJ lam L Q = some n) :
    L n = 0 ∧ (∀ j : J, lam j n = 0) ∧ Q n ≠ 0 := by
  have ht := List.find?_some hn
  have hs : L n = 0 ∧ (∀ j ∈ enumJ.values, lam j n = 0) ∧ Q n ≠ 0 := of_decide_eq_true ht
  exact ⟨hs.1,fun j => hs.2.1 j (enumJ.complete j),hs.2.2⟩

/-- The terminating failure search succeeds exactly when no sufficient primitive set exists. -/
theorem findDirection_isSome_iff :
    (findDirection enumV enumJ lam L Q).isSome = true ↔
      ¬ ∃ points, SufficientSet lam L (LinearMap.ker Q) points := by
  constructor
  · intro hf ⟨points,hp⟩
    have hn := findDirection_spec enumV enumJ lam L Q (Option.some_get hf).symm
    apply hn.2.2
    have hk := (sufficientSet_iff lam L _ points).mp hp
    exact hk ⟨hn.1,(mem_ker_observation lam points _).mpr (fun j _ => hn.2.1 j)⟩
  · intro hno
    by_contra hn
    apply hno
    refine ⟨enumJ.values.toFinset, (sufficientSet_iff lam L _ _).mpr ?_⟩
    intro n hk
    change Q n = 0
    by_contra hq
    apply hn
    rw [findDirection, List.find?_isSome]
    refine ⟨n,enumV.complete n,decide_eq_true ?_⟩
    refine ⟨hk.1,?_,hq⟩
    intro j hj
    exact (mem_ker_observation lam _ n).mp hk.2 j (List.mem_toFinset.mpr hj)

omit [DecidableEq J] in
/-- A returned failure direction produces a distinct target with identical known information and all primitive replies. -/
theorem indistinguishable {n : V} (hn : findDirection enumV enumJ lam L Q = some n) (w : V) :
    L (w + n) = L w ∧ (∀ j : J, lam j (w + n) = lam j w) ∧ Q (w + n) ≠ Q w := by
  obtain ⟨hl,ho,hq⟩ := findDirection_spec enumV enumJ lam L Q hn
  refine ⟨by rw [map_add,hl,add_zero],fun j => by rw [map_add,ho j,add_zero],?_⟩
  rw [map_add]
  exact fun he => hq (add_left_cancel (he.trans (add_zero (Q w)).symm))

end AAT.AG.RepairObservationDuality.FinitePlanningFailures
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FinitePlanningFailures
