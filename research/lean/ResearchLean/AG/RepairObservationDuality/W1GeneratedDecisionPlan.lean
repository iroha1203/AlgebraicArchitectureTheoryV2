import ResearchLean.AG.RepairObservationDuality.W1GeneratedNumericalPlan

/-!
# G-131 E: the generated W1 decision controller and the full table

## Implementation notes

The original candidate permissions and the proven native residual kernel
select either no queries or the computed minimum unknown-coordinate plan.
The finisher is D's generated residual evaluation on the visible history.
Correctness includes fully known impossible inputs and every actual input.
-/
namespace AAT.AG.RepairObservationDuality.W1GeneratedDecisionPlan
open RelativeRepairComposition W1PhysicalInputs W1NumericalEquation W1ObservationCosts
open PrimitiveQueries
set_option autoImplicit false

/-- The original permission test determines the minimum decision plan before values are acquired. -/
def points (p : Permissions) (m : Fin 3) : Finset Bool :=
  if p false = true ∨ p true = true then ∅ else W1GeneratedNumericalPlan.points m

/-- The known decision index set exposes only the original permission test and generated numeric plan. -/
theorem points_apply (p : Permissions) (m : Fin 3) :
    points p m = if p false = true ∨ p true = true then ∅ else W1GeneratedNumericalPlan.points m := rfl

/-- The selected decision indices satisfy exactly the same original native cokernel condition. -/
theorem sufficient (p : Permissions) (m : Fin 3) :
    SufficientSet primitive (known m)
      (LinearMap.ker ((LinearMap.range (differential p)).mkQ.comp rhsLinear)) (points p m) := by
  rw [sufficient_decision,points_apply]
  split_ifs with hp
  · exact Or.inl hp
  · exact Or.inr ((sufficient_numeric m _).mp
      (FiniteMinimumPlan.plan_spec W1GeneratedNumericalPlan.indices W1GeneratedNumericalPlan.inputs
        primitive (known m) rhsLinear (W1GeneratedNumericalPlan.plan_points m)).1)

/-- The exact fixed decision count is zero for a permitted candidate, otherwise the remaining unknown-coordinate count. -/
theorem points_card (p : Permissions) (m : Fin 3) :
    (points p m).card = if p false = true ∨ p true = true then 0 else 2 - m.val := by
  rw [points_apply]
  split_ifs <;> simp [W1GeneratedNumericalPlan.points_card]

/-- The generated decision procedure computes the same original residual from its retained value and visible replies. -/
noncomputable def procedure (p : Permissions) (m : Fin 3) (s : Values) : Procedure Bool (ZMod 3) Bool :=
  FiniteRepairPlanning.decisionProcedure W1FiniteCoefficients.enumK W1GeneratedNumericalPlan.coordinates
    W1GeneratedNumericalPlan.coordinates W1GeneratedNumericalPlan.inputs W1GeneratedNumericalPlan.indices
    (matrix p) rhsLinear 0 primitive (known m) s (points p m)

/-- The finite decision controller is total and correct for every original physical input of the known fiber. -/
theorem correct (p : Permissions) (m : Fin 3) (w : Values) :
    Correct evaluate (values ⁻¹' informationFiber (known m) (known m w))
      (fun X out => ValidDecision (differential p) rhsLinear 0 (values X) out) (procedure p m (known m w)) := by
  apply (PrimitiveInputQueries.correct_iff values realize values_realize evaluate
    (fun v j => primitive j v) evaluate_values _ _ _).mpr
  have hs : SufficientSet primitive (known m)
      (LinearMap.ker ((FiniteMatrixSolver.residual W1FiniteCoefficients.enumK W1GeneratedNumericalPlan.coordinates
        W1GeneratedNumericalPlan.coordinates (matrix p)).comp rhsLinear)) (points p m) := by
    rw [FiniteMatrixSolver.residual_comp_ker,matrix_differential]
    exact sufficient p m
  have h := FiniteRepairPlanning.decision_correct W1FiniteCoefficients.enumK W1GeneratedNumericalPlan.coordinates
    W1GeneratedNumericalPlan.coordinates W1GeneratedNumericalPlan.inputs W1GeneratedNumericalPlan.indices
    (matrix p) rhsLinear 0 primitive (known m) (known m w) (points p m) hs
  simpa only [matrix_differential] using h

/-- All original candidate permissions have the exact adaptive decision table, on every known input fiber. -/
theorem table (p : Permissions) (m : Fin 3) (w : Values) :
    optimum (fun v j => primitive j v) (informationFiber (known m) (known m w))
      (ValidDecision (differential p) rhsLinear 0) =
      if p false = true ∨ p true = true then 0 else (2 - m.val : Nat) := by
  split_ifs with hp
  · exact nonempty_decision_cost p m w hp
  · have hz : p = (fun _ => false) := by
      funext j
      cases j
      · exact Bool.eq_false_iff.mpr (fun h => hp (Or.inl h))
      · exact Bool.eq_false_iff.mpr (fun h => hp (Or.inr h))
    rw [hz]
    exact empty_decision_table m w

/-- The generated decision controller attains the all-adaptive actual-input optimum and exact full table cost. -/
theorem optimal (p : Permissions) (m : Fin 3) (w : Values) :
    worst evaluate (values ⁻¹' informationFiber (known m) (known m w)) (procedure p m (known m w)) =
      optimum evaluate (values ⁻¹' informationFiber (known m) (known m w))
        (fun X out => ValidDecision (differential p) rhsLinear 0 (values X) out) ∧
    worst evaluate (values ⁻¹' informationFiber (known m) (known m w)) (procedure p m (known m w)) =
      if p false = true ∨ p true = true then 0 else (2 - m.val : Nat) := by
  have hcost : worst evaluate (values ⁻¹' informationFiber (known m) (known m w))
      (procedure p m (known m w)) =
      if p false = true ∨ p true = true then 0 else (2 - m.val : Nat) := by
    rw [PrimitiveInputQueries.worst_eq values realize values_realize evaluate
      (fun v j => primitive j v) evaluate_values]
    change worst _ _ (FiniteRepairPlanning.decisionProcedure _ _ _ _ _ _ _ _ _ _ _ _) = _
    rw [FiniteRepairPlanning.decisionProcedure_apply,
      FinitePrimitiveProcedure.worst_eq _ _ _ _ (show w ∈ informationFiber (known m) (known m w) from rfl),
      FiniteMinimumPlan.questions_length,points_card]
  refine ⟨?_,hcost⟩
  rw [hcost,PrimitiveInputQueries.optimum_eq values realize values_realize evaluate
    (fun v j => primitive j v) evaluate_values,table]

end AAT.AG.RepairObservationDuality.W1GeneratedDecisionPlan
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1GeneratedDecisionPlan
