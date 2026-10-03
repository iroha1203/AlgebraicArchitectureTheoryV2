import ResearchLean.AG.RepairObservationDuality.W1NumericalEquation
import ResearchLean.AG.RepairObservationDuality.FiniteMinimumPlan

/-!
# G-131 E: W1's exact additional primitive costs

## Implementation notes

The three known-information maps disclose nothing, x only, or both values.
Their sufficient sets are checked on all nine input directions. These checks
are kernel proofs, not execution measurements. C's replay theorem supplies
the lower bound over all adaptive history-only controllers. All four original
output coordinates and the candidate masks remain in the validator.
-/
namespace AAT.AG.RepairObservationDuality.W1ObservationCosts
open RelativeRepairComposition W1PhysicalInputs W1NumericalEquation PrimitiveQueries
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The three known-information regimes: none, x alone, or the whole pair. -/
def known (m : Fin 3) : Values →ₗ[ZMod 3] Values :=
  if m = 0 then 0 else if m = 1 then
    LinearMap.pi (fun j => if j then 0 else LinearMap.proj false) else LinearMap.id

/-- Known-information evaluation keeps exactly the prescribed existing values. -/
theorem known_apply (m : Fin 3) (v : Values) :
    known m v = if m = 0 then 0 else if m = 1 then (fun j => if j then 0 else v false) else v := by
  fin_cases m <;> ext j <;> cases j <;> simp [known]

/-- The unasked directions must vanish at both unknown coordinates. -/
theorem sufficient_numeric (m : Fin 3) (points : Finset Bool) :
    SufficientSet primitive (known m) (LinearMap.ker rhsLinear) points ↔
      (m = 0 → false ∈ points ∧ true ∈ points) ∧ (m = 1 → true ∈ points) := by
  rw [sufficientSet_iff]
  have h : ∀ (m : Fin 3) (points : Finset Bool),
      (∀ v : Values, known m v = 0 → (∀ j ∈ points, v j = 0) → rhsLinear v = 0) ↔
        (m = 0 → false ∈ points ∧ true ∈ points) ∧ (m = 1 → true ∈ points) := by decide
  rw [← h m points]
  constructor
  · intro hp v hl ho
    exact hp ⟨hl,(mem_ker_observation primitive points v).mpr ho⟩
  · intro hp v hv
    exact hp v hv.1 ((mem_ker_observation primitive points v).mp hv.2)

/-- All numerical sufficient sets contain every as-yet-unknown original primitive. -/
theorem sufficient_numeric_card (m : Fin 3) (points : Finset Bool)
    (hp : SufficientSet primitive (known m) (LinearMap.ker rhsLinear) points) :
    2 - m.val ≤ points.card := by
  have h := (sufficient_numeric m points).mp hp
  fin_cases m
  · have hs : ({false,true} : Finset Bool) ⊆ points := by
      intro j hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact (h.1 rfl).1
      · exact (h.1 rfl).2
    have hc := Finset.card_le_card hs
    simpa using hc
  · have hc := Finset.card_pos.mpr ⟨true,h.2 rfl⟩
    simpa using hc
  · simp

/-- The minimum fixed numerical sets have the exact unknown-coordinate costs. -/
theorem numerical_minimum (m : Fin 3) :
    minimum primitive (known m) (LinearMap.ker rhsLinear) = (2 - m.val : Nat) := by
  apply le_antisymm
  · fin_cases m
    · have hs := (sufficient_numeric 0 {false,true}).mpr (by simp)
      simpa using minimum_le_card primitive (known 0) (LinearMap.ker rhsLinear) {false,true} hs
    · have hs := (sufficient_numeric 1 {true}).mpr (by simp)
      simpa using minimum_le_card primitive (known 1) (LinearMap.ker rhsLinear) {true} hs
    · have hs := (sufficient_numeric 2 ∅).mpr (by simp)
      simpa using minimum_le_card primitive (known 2) (LinearMap.ker rhsLinear) ∅ hs
  · exact le_minimum primitive (known m) (LinearMap.ker rhsLinear) _
      (fun points hp => ENat.coe_le_coe.mpr (sufficient_numeric_card m points hp))

/-- C's all-adaptive numerical optimum is exact on every known fiber containing a successful input. -/
theorem numerical_cost (p : Permissions) (m : Fin 3) (w : Values)
    (hw : Solvable (differential p) (affineRhs rhsLinear 0) w) :
    optimum (fun v j => primitive j v) (informationFiber (known m) (known m w))
      (ValidOutput (differential p) (affineRhs rhsLinear 0)) = (2 - m.val : Nat) := by
  rw [numerical_optimum primitive (differential p) rhsLinear 0 (known m) (known m w) rfl hw,
    numerical_minimum]

/-- The same numerical optimum holds over all actual physical input controllers. -/
theorem actual_numerical_cost (p : Permissions) (m : Fin 3) (w : Values)
    (hw : Solvable (differential p) (affineRhs rhsLinear 0) w) :
    optimum evaluate (values ⁻¹' informationFiber (known m) (known m w))
      (fun X out => ValidOutput (differential p) (affineRhs rhsLinear 0) (values X) out) =
      (2 - m.val : Nat) := by
  rw [PrimitiveInputQueries.optimum_eq values realize values_realize evaluate
    (fun v j => primitive j v) evaluate_values]
  exact numerical_cost p m w hw

/-- A decision sufficient set is empty whenever an original candidate is permitted; otherwise it observes each remaining input. -/
theorem sufficient_decision (p : Permissions) (m : Fin 3) (points : Finset Bool) :
    SufficientSet primitive (known m)
      (LinearMap.ker ((LinearMap.range (differential p)).mkQ.comp rhsLinear)) points ↔
      (p false = true ∨ p true = true) ∨
        ((m = 0 → false ∈ points ∧ true ∈ points) ∧ (m = 1 → true ∈ points)) := by
  have h : ∀ (b c : Bool) (m : Fin 3) (points : Finset Bool),
      (∀ v : Values, known m v = 0 → (∀ j ∈ points, v j = 0) →
        (v true = v false ∨ b = true ∨ c = true)) ↔
      (b = true ∨ c = true) ∨
        ((m = 0 → false ∈ points ∧ true ∈ points) ∧ (m = 1 → true ∈ points)) := by
    intro b c
    cases b <;> cases c
    · decide
    · simp
    · simp
    · simp
  rw [← h (p false) (p true) m points,sufficientSet_iff]
  constructor
  · intro hp v hl ho
    exact (residual_kernel_iff p v).mp (hp ⟨hl,(mem_ker_observation primitive points v).mpr ho⟩)
  · intro hp v hv
    exact (residual_kernel_iff p v).mpr (hp v hv.1 ((mem_ker_observation primitive points v).mp hv.2))

/-- The empty candidate set has the same exact minimum for decision and numerical output. -/
theorem empty_decision_minimum (m : Fin 3) :
    minimum primitive (known m)
      (LinearMap.ker ((LinearMap.range (differential (fun _ => false))).mkQ.comp rhsLinear)) =
      (2 - m.val : Nat) := by
  have h : (fun points => SufficientSet primitive (known m)
      (LinearMap.ker ((LinearMap.range (differential (fun _ => false))).mkQ.comp rhsLinear)) points) =
      (fun points => SufficientSet primitive (known m) (LinearMap.ker rhsLinear) points) := by
    funext points
    apply propext
    rw [sufficient_decision,sufficient_numeric]
    simp
  change (⨅ points : {p : Finset Bool // _}, (points.1.card : ℕ∞)) = _
  rw [h]
  exact numerical_minimum m

/-- Any original permitted candidate makes the decision minimum exactly zero without disclosing x or y. -/
theorem nonempty_decision_minimum (p : Permissions) (m : Fin 3)
    (hp : p false = true ∨ p true = true) :
    minimum primitive (known m)
      (LinearMap.ker ((LinearMap.range (differential p)).mkQ.comp rhsLinear)) = 0 := by
  apply le_antisymm
  · have hs := (sufficient_decision p m ∅).mpr (Or.inl hp)
    simpa using minimum_le_card primitive (known m) _ ∅ hs
  · exact bot_le

/-- C's adaptive lower bound gives the complete empty-permission decision row. -/
theorem empty_decision_cost (m : Fin 3) (w : Values)
    (hw : Solvable (differential (fun _ => false)) (affineRhs rhsLinear 0) w) :
    optimum (fun v j => primitive j v) (informationFiber (known m) (known m w))
      (ValidDecision (differential (fun _ => false)) rhsLinear 0) = (2 - m.val : Nat) := by
  rw [decision_optimum primitive _ rhsLinear 0 (known m) (known m w) rfl hw,empty_decision_minimum]

/-- The nonempty-permission decision controller has zero additional cost on every input fiber. -/
theorem nonempty_decision_cost (p : Permissions) (m : Fin 3) (w : Values)
    (hp : p false = true ∨ p true = true) :
    optimum (fun v j => primitive j v) (informationFiber (known m) (known m w))
      (ValidDecision (differential p) rhsLinear 0) = 0 := by
  have hs : Solvable (differential p) (affineRhs rhsLinear 0) w := (solvable_iff p w).mpr (Or.inr hp)
  rw [decision_optimum primitive _ rhsLinear 0 (known m) (known m w) rfl hs,
    nonempty_decision_minimum p m hp]

/-- Unless both values are already known, the same known fiber contains a diagonal successful actual input. -/
theorem success_or_both_known (p : Permissions) (m : Fin 3) (w : Values) :
    (∃ v, known m v = known m w ∧ Solvable (differential p) (affineRhs rhsLinear 0) v) ∨ m = 2 := by
  fin_cases m
  · refine Or.inl ⟨0,?_,(solvable_iff p 0).mpr (Or.inl rfl)⟩
    simp [known_apply]
  · let v : Values := fun _ => w false
    refine Or.inl ⟨v,?_,(solvable_iff p v).mpr (Or.inl rfl)⟩
    ext j
    cases j <;> simp [known_apply,v]
  · exact Or.inr rfl

/-- The numerical table holds for every known pair, including entirely impossible fibers. -/
theorem numerical_table (p : Permissions) (m : Fin 3) (w : Values) :
    optimum (fun v j => primitive j v) (informationFiber (known m) (known m w))
      (ValidOutput (differential p) (affineRhs rhsLinear 0)) = (2 - m.val : Nat) := by
  by_cases hs : ∃ v, known m v = known m w ∧ Solvable (differential p) (affineRhs rhsLinear 0) v
  · obtain ⟨v,hv,hr⟩ := hs
    rw [numerical_optimum primitive _ rhsLinear 0 (known m) (known m w) hv hr,numerical_minimum]
  · have hm := (success_or_both_known p m w).resolve_left hs
    have hi : ∀ v ∈ informationFiber (known m) (known m w),
        ¬ Solvable (differential p) (affineRhs rhsLinear 0) v := by
      intro v hv hr
      exact hs ⟨v,hv,hr⟩
    rw [(all_impossible_optima_zero primitive (differential p) rhsLinear 0 (known m) (known m w) hi).2,hm]
    rfl

/-- The empty-permission decision table holds also when the fully known input is impossible. -/
theorem empty_decision_table (m : Fin 3) (w : Values) :
    optimum (fun v j => primitive j v) (informationFiber (known m) (known m w))
      (ValidDecision (differential (fun _ => false)) rhsLinear 0) = (2 - m.val : Nat) := by
  by_cases hs : ∃ v, known m v = known m w ∧
      Solvable (differential (fun _ => false)) (affineRhs rhsLinear 0) v
  · obtain ⟨v,hv,hr⟩ := hs
    rw [decision_optimum primitive _ rhsLinear 0 (known m) (known m w) hv hr,empty_decision_minimum]
  · have hm := (success_or_both_known (fun _ => false) m w).resolve_left hs
    have hi : ∀ v ∈ informationFiber (known m) (known m w),
        ¬ Solvable (differential (fun _ => false)) (affineRhs rhsLinear 0) v := by
      intro v hv hr
      exact hs ⟨v,hv,hr⟩
    rw [(all_impossible_optima_zero primitive (differential (fun _ => false)) rhsLinear 0
      (known m) (known m w) hi).1,hm]
    rfl

end AAT.AG.RepairObservationDuality.W1ObservationCosts
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1ObservationCosts
