import ResearchLean.AG.RepairObservationDuality.KPlusNativeEquation
import ResearchLean.AG.RepairObservationDuality.FiniteMinimumPlan
import ResearchLean.AG.RepairObservationDuality.PrimitiveInputQueries

/-!
# G-131 E: K+ numerical optimum and generated whole solver

The lower bound ranges over all total adaptive controllers on all physical
inputs. The attaining controller generates its finite minimum plan and native
matrix section before values are known and returns the complete u/z pair.
-/
namespace AAT.AG.RepairObservationDuality.KPlusNumericalQueries
open RelativeRepairComposition KPlusInput KPlusActualRepairs KPlusNativeEquation PrimitiveQueries
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- No physical input value is initially known. -/
def known : Values →ₗ[ZMod 2] Values := 0
/-- With no initial value, the known fiber is the entire original parameter space. -/
theorem known_fiber : informationFiber known 0 = Set.univ := by
  ext v
  simp [mem_informationFiber,known]
/-- The numerical and reference controllers both range over every same original physical input. -/
theorem physical_fiber : values ⁻¹' informationFiber known 0 = Set.univ := by
  rw [known_fiber]
  rfl
/-- A sufficient numeric set must contain both independent original physical queries. -/
theorem sufficient (points : Finset Bool) :
    SufficientSet primitive known (LinearMap.ker rhsLinear) points ↔
      false ∈ points ∧ true ∈ points := by
  rw [sufficientSet_iff]
  have h : ∀ points : Finset Bool,
      (∀ v : Values, (∀ j ∈ points, v j = 0) → v = 0) ↔
        false ∈ points ∧ true ∈ points := by decide
  rw [← h points]
  constructor
  · intro hp v ho
    exact hp ⟨rfl,(mem_ker_observation primitive points v).mpr ho⟩
  · intro hp v hv
    exact hp v ((mem_ker_observation primitive points v).mp hv.2)
/-- Every sufficient numeric set has at least two original queries. -/
theorem sufficient_card (points : Finset Bool)
    (hp : SufficientSet primitive known (LinearMap.ker rhsLinear) points) : 2 ≤ points.card := by
  have h := (sufficient points).mp hp
  have hs : ({false,true} : Finset Bool) ⊆ points := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact h.1
    · exact h.2
  simpa using Finset.card_le_card hs
/-- The minimum fixed plan is precisely two original queries. -/
theorem minimum_two : minimum primitive known (LinearMap.ker rhsLinear) = 2 := by
  apply le_antisymm
  · simpa using minimum_le_card primitive known (LinearMap.ker rhsLinear) {false,true}
      ((sufficient {false,true}).mpr (by simp))
  · exact le_minimum primitive known (LinearMap.ker rhsLinear) 2
      (fun points hp => ENat.coe_le_coe.mpr (sufficient_card points hp))
/-- C's replay lower bound and upper construction give two over all adaptive parameter controllers. -/
theorem numerical_cost :
    optimum (fun v j => primitive j v) (informationFiber known 0)
      (ValidOutput differential (affineRhs rhsLinear 0)) = 2 := by
  rw [numerical_optimum primitive differential rhsLinear 0 known 0
    (show known (0 : Values) = 0 from rfl) (solvable 0),minimum_two]
/-- The same optimum two holds over the entire original physical operation family. -/
theorem physical_cost :
    optimum evaluate (values ⁻¹' informationFiber known 0)
      (fun X out => ValidOutput differential (affineRhs rhsLinear 0) (values X) out) = 2 := by
  rw [PrimitiveInputQueries.optimum_eq values realize values_realize evaluate
    (fun v j => primitive j v) evaluate_values,numerical_cost]
/-- The complete primitive index list is fixed before input acquisition. -/
def indices : FiniteElimination.Enumeration Bool := ⟨[false,true],by intro j; cases j <;> simp⟩
/-- The complete field list includes both F2 values. -/
def field : FiniteElimination.Enumeration (ZMod 2) := ⟨[0,1],by intro x; fin_cases x <;> simp⟩
/-- Every original physical parameter direction is enumerated, independent of feasibility. -/
def inputs : FiniteElimination.Enumeration Values := indices.pi (fun _ => field)
/-- The minimum plan is generated from the complete known finite data. -/
def plan : Option (Finset Bool) := FiniteMinimumPlan.plan indices inputs primitive known rhsLinear
/-- The computed sufficient set's selected indices. -/
def points : Finset Bool := plan.getD ∅
/-- The generated plan always exists and returns its actual sufficient set. -/
theorem plan_points : plan = some points := by
  cases he : plan with
  | none =>
    have hn := (FiniteMinimumPlan.plan_none_iff indices inputs primitive known rhsLinear).mp he
    exact (hn ⟨{false,true},(sufficient {false,true}).mpr (by simp)⟩).elim
  | some p => simp [points,he]
/-- The generated plan itself contains exactly two original indices. -/
theorem points_card : points.card = 2 := by
  have h := FiniteMinimumPlan.plan_card indices inputs primitive known rhsLinear plan_points
  rw [minimum_two] at h
  exact ENat.coe_inj.mp h
/-- The finite history-only controller uses the section of the same whole native matrix. -/
noncomputable def procedure : Procedure Bool (ZMod 2) (Option Values) :=
  FiniteRepairPlanning.numericalProcedure field indices indices inputs indices matrix rhsLinear 0
    primitive known 0 points
/-- Every actual physical input terminates with a complete correct numeric answer. -/
theorem correct :
    Correct evaluate (values ⁻¹' informationFiber known 0)
      (fun X out => ValidOutput differential (affineRhs rhsLinear 0) (values X) out) procedure := by
  apply (PrimitiveInputQueries.correct_iff values realize values_realize evaluate
    (fun v j => primitive j v) evaluate_values _ _ _).mpr
  have h := FiniteRepairPlanning.numerical_correct field indices indices inputs indices matrix rhsLinear 0
    primitive known 0 points (FiniteMinimumPlan.plan_spec indices inputs primitive known rhsLinear plan_points).1
  simpa only [matrix_differential] using h
/-- The exact trace is the generated original question list and the full native section answer. -/
theorem run (X : Inputs) :
    Run evaluate procedure X []
      (FiniteMatrixSolver.solve field indices indices matrix (affineRhs rhsLinear 0 (values X)))
      (FiniteMinimumPlan.questions indices points) := by
  apply (PrimitiveInputQueries.run_iff values evaluate (fun v j => primitive j v)
    evaluate_values _ X [] _ _).mpr
  have h := FinitePrimitiveProcedure.run (fun v j => primitive j v)
    (FiniteMinimumPlan.questions indices points)
    (FiniteRepairPlanning.numericalFinish field indices indices inputs matrix rhsLinear 0 primitive known 0)
    (values X)
  rw [FiniteRepairPlanning.numericalFinish_transcript field indices indices inputs indices matrix rhsLinear 0
    primitive known 0 points (FiniteMinimumPlan.plan_spec indices inputs primitive known rhsLinear plan_points).1
    (show known (values X) = 0 from rfl)] at h
  exact h
/-- The computed controller attains two, the optimum over all correct adaptive physical controllers. -/
theorem optimal :
    worst evaluate (values ⁻¹' informationFiber known 0) procedure = 2 ∧
    worst evaluate (values ⁻¹' informationFiber known 0) procedure =
      optimum evaluate (values ⁻¹' informationFiber known 0)
        (fun X out => ValidOutput differential (affineRhs rhsLinear 0) (values X) out) := by
  have hcost : worst evaluate (values ⁻¹' informationFiber known 0) procedure = 2 := by
    rw [PrimitiveInputQueries.worst_eq values realize values_realize evaluate
      (fun v j => primitive j v) evaluate_values]
    change worst _ _ (FiniteRepairPlanning.numericalProcedure _ _ _ _ _ _ _ _ _ _ _ _) = _
    rw [FiniteRepairPlanning.numericalProcedure_apply,
      FinitePrimitiveProcedure.worst_eq _ _ _ _ (show (0 : Values) ∈ informationFiber known 0 from rfl),
      FiniteMinimumPlan.questions_length,points_card]
    rfl
  exact ⟨hcost,hcost.trans physical_cost.symm⟩

/-- Every physical input actually yields a whole numeric pair; the generated solver cannot return none. -/
theorem answer_exists (X : Inputs) : ∃ h : Values,
    FiniteMatrixSolver.solve field indices indices matrix
      (affineRhs rhsLinear 0 (values X)) = some h := by
  cases he : FiniteMatrixSolver.solve field indices indices matrix
      (affineRhs rhsLinear 0 (values X)) with
  | some h => exact ⟨h,rfl⟩
  | none =>
    have hn := (FiniteMatrixSolver.solve_none_iff field indices indices matrix _).mp he
    have hs := solvable (values X)
    rw [← matrix_differential] at hs
    exact (hn hs).elim
/-- Every section answer restores the independent actual repairs of the same two original faces. -/
noncomputable def restoreAnswer (X : Inputs) (h : Values)
    (he : FiniteMatrixSolver.solve field indices indices matrix
      (affineRhs rhsLinear 0 (values X)) = some h) : RealRepairs (values X) :=
  restore (values X) h (by
    have hs := ((FiniteMatrixSolver.solve_some_iff field indices indices matrix _ h).mp he).2
    simpa only [matrix_differential] using hs)
/-- The whole solver answer is exactly what is acquired from all restored original operations. -/
theorem restoreAnswer_values (X : Inputs) (h : Values)
    (he : FiniteMatrixSolver.solve field indices indices matrix
      (affineRhs rhsLinear 0 (values X)) = some h) :
    coordinates (restoreAnswer X h he) = h := restore_values (values X) h _

end AAT.AG.RepairObservationDuality.KPlusNumericalQueries
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.KPlusNumericalQueries
