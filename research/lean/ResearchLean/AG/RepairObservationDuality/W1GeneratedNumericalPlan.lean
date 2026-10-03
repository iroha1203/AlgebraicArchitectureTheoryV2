import ResearchLean.AG.RepairObservationDuality.W1ObservationCosts

/-!
# G-131 E: generated W1 numerical plans and actual complete outputs

## Implementation notes

The finite planner receives the original two primitive indices and all nine
directions. No sufficient set or successful repair is supplied. The generated
controller sees only its known value and its reply history, returns the whole
u,h,z,v vector or none, and uses G-130's generated section of the same matrix.
Every returned vector restores the independently specified actual repair.
-/
namespace AAT.AG.RepairObservationDuality.W1GeneratedNumericalPlan
open RelativeRepairComposition W1PhysicalInputs W1NumericalEquation W1ObservationCosts PrimitiveQueries
set_option autoImplicit false

/-- The exact two permitted original primitive queries, in rx/ry order. -/
def indices : FiniteElimination.Enumeration Bool := ⟨[false,true],by intro j; cases j <;> simp⟩

/-- All nine original unknown directions are generated from the complete field and primitive lists. -/
def inputs : FiniteElimination.Enumeration Values := indices.pi (fun _ => W1FiniteCoefficients.enumK)

/-- The complete list includes every whole original output coordinate, including h. -/
def coordinates : FiniteElimination.Enumeration (Fin 4) := ⟨List.finRange 4,by simp⟩

/-- The finite argmin plan is determined before knowing the input values. -/
def plan (m : Fin 3) : Option (Finset Bool) :=
  FiniteMinimumPlan.plan indices inputs primitive (known m) rhsLinear

/-- The plan's selected index set; the default is unreachable by the complete-kernel proof. -/
def points (m : Fin 3) : Finset Bool := (plan m).getD ∅

/-- The generated finite plan always returns its actual sufficient set. -/
theorem plan_points (m : Fin 3) : plan m = some (points m) := by
  cases he : plan m with
  | none =>
    have hn := (FiniteMinimumPlan.plan_none_iff indices inputs primitive (known m) rhsLinear).mp he
    exact (hn ⟨{false,true},(sufficient_numeric m {false,true}).mpr (by simp)⟩).elim
  | some p => simp [points,he]

/-- The generated finite plan has exactly the prescribed minimum cardinal. -/
theorem points_card (m : Fin 3) : (points m).card = 2 - m.val := by
  have h := FiniteMinimumPlan.plan_card indices inputs primitive (known m) rhsLinear (plan_points m)
  rw [W1ObservationCosts.numerical_minimum] at h
  exact ENat.coe_inj.mp h

/-- The actual numerical controller reads only the selected primitives and visible history. -/
noncomputable def procedure (p : Permissions) (m : Fin 3) (s : Values) :
    Procedure Bool (ZMod 3) (Option Corrections) :=
  FiniteRepairPlanning.numericalProcedure W1FiniteCoefficients.enumK coordinates coordinates
    inputs indices (matrix p) rhsLinear 0 primitive (known m) s (points m)

/-- The generated numerical controller is total and correct on every actual physical input of the known fiber. -/
theorem correct (p : Permissions) (m : Fin 3) (w : Values) :
    Correct evaluate (values ⁻¹' informationFiber (known m) (known m w))
      (fun X out => ValidOutput (differential p) (affineRhs rhsLinear 0) (values X) out)
      (procedure p m (known m w)) := by
  apply (PrimitiveInputQueries.correct_iff values realize values_realize evaluate
    (fun v j => primitive j v) evaluate_values _ _ _).mpr
  have h := FiniteRepairPlanning.numerical_correct W1FiniteCoefficients.enumK coordinates coordinates
    inputs indices (matrix p) rhsLinear 0 primitive (known m) (known m w) (points m)
    (FiniteMinimumPlan.plan_spec indices inputs primitive (known m) rhsLinear (plan_points m)).1
  simpa only [matrix_differential] using h

/-- Every execution returns a fully acquired RHS solution after precisely the generated original questions. -/
theorem run (p : Permissions) (m : Fin 3) (w : Values) (X : Inputs)
    (hX : known m (values X) = known m w) :
    Run evaluate (procedure p m (known m w)) X []
      (FiniteMatrixSolver.solve W1FiniteCoefficients.enumK coordinates coordinates (matrix p)
        (affineRhs rhsLinear 0 (values X))) (FiniteMinimumPlan.questions indices (points m)) := by
  apply (W1PhysicalInputs.run_iff _ X [] _ _).mpr
  have h := FinitePrimitiveProcedure.run (fun v j => primitive j v)
    (FiniteMinimumPlan.questions indices (points m))
    (FiniteRepairPlanning.numericalFinish W1FiniteCoefficients.enumK coordinates coordinates inputs
      (matrix p) rhsLinear 0 primitive (known m) (known m w)) (values X)
  rw [FiniteRepairPlanning.numericalFinish_transcript W1FiniteCoefficients.enumK coordinates coordinates
    inputs indices (matrix p) rhsLinear 0 primitive (known m) (known m w) (points m)
    (FiniteMinimumPlan.plan_spec indices inputs primitive (known m) rhsLinear (plan_points m)).1 hX] at h
  exact h

/-- The controller's exact worst cost attains the optimum over every correct adaptive actual-input procedure. -/
theorem optimal (p : Permissions) (m : Fin 3) (w : Values) :
    worst evaluate (values ⁻¹' informationFiber (known m) (known m w)) (procedure p m (known m w)) =
      optimum evaluate (values ⁻¹' informationFiber (known m) (known m w))
        (fun X out => ValidOutput (differential p) (affineRhs rhsLinear 0) (values X) out) ∧
    worst evaluate (values ⁻¹' informationFiber (known m) (known m w)) (procedure p m (known m w)) =
      (2 - m.val : Nat) := by
  have hcost : worst evaluate (values ⁻¹' informationFiber (known m) (known m w))
      (procedure p m (known m w)) = (2 - m.val : Nat) := by
    rw [PrimitiveInputQueries.worst_eq values realize values_realize evaluate
      (fun v j => primitive j v) evaluate_values]
    change worst _ _ (FiniteRepairPlanning.numericalProcedure _ _ _ _ _ _ _ _ _ _ _ _) = _
    rw [FiniteRepairPlanning.numericalProcedure_apply,
      FinitePrimitiveProcedure.worst_eq _ _ _ _ (show w ∈ informationFiber (known m) (known m w) from rfl),
      FiniteMinimumPlan.questions_length,points_card]
  refine ⟨?_,hcost⟩
  rw [hcost,PrimitiveInputQueries.optimum_eq values realize values_realize evaluate
    (fun v j => primitive j v) evaluate_values,numerical_table]

/-- Every full computed answer restores the original actual affine repair, with both original Laws and all masks. -/
noncomputable def restoreAnswer (p : Permissions) (X : Inputs) (a : Corrections)
    (ha : FiniteMatrixSolver.solve W1FiniteCoefficients.enumK coordinates coordinates (matrix p)
      (affineRhs rhsLinear 0 (values X)) = some a) :=
  W1NumericalEquation.restore p X a (by
    have h := ((FiniteMatrixSolver.solve_some_iff W1FiniteCoefficients.enumK coordinates coordinates
      (matrix p) _ a).mp ha).2
    simpa only [matrix_differential] using h)

end AAT.AG.RepairObservationDuality.W1GeneratedNumericalPlan
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1GeneratedNumericalPlan
