import ResearchLean.AG.RepairObservationDuality.FiniteMinimumPlan
import ResearchLean.AG.RepairObservationDuality.FinitePrimitiveProcedure

/-!
# G-131 D: finite value acquisition from known information and visible replies

## Implementation notes

The input enumeration describes the known model's parameter space. The
algorithm searches that finite list using only L v = s and the actual reply
history. Unknown input v is used only in the correctness theorem. A selected
sufficient kernel forces every matching representative to have the same
specified value; no extra primitive evaluations occur in this recovery.
-/
namespace AAT.AG.RepairObservationDuality.FiniteObservedValues
open RelativeRepairComposition PrimitiveQueries
variable {k V I W J : Type*} [Field k] [DecidableEq k]
variable [AddCommGroup V] [Module k V] [AddCommGroup I] [Module k I] [DecidableEq I]
variable [AddCommGroup W] [Module k W] [DecidableEq W] [DecidableEq J]
variable (enumV : FiniteElimination.Enumeration V) (lam : J → V →ₗ[k] k)
variable (L : V →ₗ[k] I) (s : I)

/-- D searches the known finite parameter model using only retained data and observed replies. -/
def findInput (hist : History J k) : Option V := enumV.values.find? fun v =>
  decide (L v = s ∧ ∀ pair ∈ hist, lam pair.1 v = pair.2)

omit [DecidableEq J] in
/-- Each returned parameter matches exactly the known value and all actual observed replies. -/
theorem findInput_spec (hist : History J k) {w : V}
    (hw : findInput enumV lam L s hist = some w) :
    L w = s ∧ ∀ pair ∈ hist, lam pair.1 w = pair.2 := by
  have ht := List.find?_some hw
  exact of_decide_eq_true ht

omit [DecidableEq J] in
/-- A consistent actual input guarantees termination of the finite recovery with a matching parameter. -/
theorem findInput_isSome (hist : History J k) {v : V}
    (hv : L v = s) (hc : ∀ pair ∈ hist, lam pair.1 v = pair.2) :
    (findInput enumV lam L s hist).isSome = true := by
  rw [findInput, List.find?_isSome]
  exact ⟨v, enumV.complete v, decide_eq_true ⟨hv,hc⟩⟩

omit [DecidableEq J] in
/-- Every actual transcript has a finite returned representative of precisely its known response fiber. -/
theorem findInput_transcript (points : List J) {v : V} (hv : L v = s) :
    ∃ w, findInput enumV lam L s (transcript (fun v j => lam j v) points v) = some w := by
  have hs := findInput_isSome enumV lam L s (transcript (fun v j => lam j v) points v)
    hv ((transcript_consistent_iff _ points v v).mpr (fun _ _ => rfl))
  exact ⟨_,(Option.some_get hs).symm⟩

/-- A matching recovered parameter differs from the actual input only in unobserved unknown directions. -/
theorem difference_ker (enumJ : FiniteElimination.Enumeration J) (points : Finset J)
    {v w : V} (hv : L v = s)
    (hw : findInput enumV lam L s
      (transcript (fun v j => lam j v) (FiniteMinimumPlan.questions enumJ points) v) = some w) :
    w - v ∈ LinearMap.ker L ⊓ LinearMap.ker (observation lam points) := by
  have hf := findInput_spec enumV lam L s _ hw
  constructor
  · exact mem_fiber_sub L s hf.1 hv
  · apply (mem_ker_observation lam points (w - v)).mpr
    intro j hj
    have hq := (transcript_consistent_iff _ (FiniteMinimumPlan.questions enumJ points) v w).mp hf.2
    rw [map_sub,hq j ((FiniteMinimumPlan.mem_questions enumJ points j).mpr hj),sub_self]

omit [DecidableEq W] in
/-- The same specified value of every recovered representative equals the actual input's value. -/
theorem recovered_value (enumJ : FiniteElimination.Enumeration J) (points : Finset J)
    (Q : V →ₗ[k] W) (hs : SufficientSet lam L (LinearMap.ker Q) points)
    {v w : V} (hv : L v = s)
    (hw : findInput enumV lam L s
      (transcript (fun v j => lam j v) (FiniteMinimumPlan.questions enumJ points) v) = some w) :
    Q w = Q v := by
  have hn := (sufficientSet_iff lam L _ points).mp hs
    (difference_ker enumV lam L s enumJ points hv hw)
  change Q (w - v) = 0 at hn
  rw [map_sub] at hn
  exact sub_eq_zero.mp hn

/-- D's acquired value is fully computed from the known affine expression and visible history. -/
def readAffine (Q : V →ₗ[k] W) (c : W) (hist : History J k) : W :=
  ((findInput enumV lam L s hist).map (fun w => c + Q w)).getD c

omit [DecidableEq W] [DecidableEq J] in
/-- Recovery of a matching parameter returns its exact fully evaluated affine value. -/
theorem readAffine_of_some (Q : V →ₗ[k] W) (c : W) (hist : History J k) {w : V}
    (hw : findInput enumV lam L s hist = some w) :
    readAffine enumV lam L s Q c hist = c + Q w := by
  simp only [readAffine,hw,Option.map_some,Option.getD_some]

omit [DecidableEq W] in
/-- The terminating finite recovery yields the same affine value on every actual known-fiber transcript. -/
theorem readAffine_transcript (enumJ : FiniteElimination.Enumeration J) (points : Finset J)
    (Q : V →ₗ[k] W) (c : W) (hs : SufficientSet lam L (LinearMap.ker Q) points)
    {v : V} (hv : L v = s) :
    readAffine enumV lam L s Q c
      (transcript (fun v j => lam j v) (FiniteMinimumPlan.questions enumJ points) v) = c + Q v := by
  obtain ⟨w,hw⟩ := findInput_transcript enumV lam L s (FiniteMinimumPlan.questions enumJ points) hv
  rw [readAffine_of_some enumV lam L s Q c _ hw,recovered_value enumV lam L s enumJ points Q hs hv hw]

end AAT.AG.RepairObservationDuality.FiniteObservedValues
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FiniteObservedValues
