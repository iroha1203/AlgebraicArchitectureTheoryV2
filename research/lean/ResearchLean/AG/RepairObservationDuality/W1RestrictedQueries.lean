import ResearchLean.AG.RepairObservationDuality.W1GeneratedNumericalPlan

/-!
# G-131 E: rx-only actual indistinguishability and adaptive impossibility

## Implementation notes

The original empty-permission problem still has both physical inputs. Only
the permitted primitive index type changes to rx. The direction (0,1) is an
actual realized input direction, invisible to every permitted repeated query.
C's replay lower bound excludes all total correct adaptive controllers for
both output languages, not merely this example's fixed numerical plan.
-/
namespace AAT.AG.RepairObservationDuality.W1RestrictedQueries
open W1PhysicalInputs W1NumericalEquation PrimitiveQueries
set_option autoImplicit false

/-- The sole permitted primitive is the actual original rx evaluation. -/
def primitiveRx (_ : Unit) : Values →ₗ[ZMod 3] ZMod 3 := primitive false

/-- The physical rx-only evaluator keeps the same original actual operation. -/
def evaluateRx (X : Inputs) (_ : Unit) : ZMod 3 := evaluate X false

/-- All physical rx-only replies agree with the same input coordinate. -/
theorem evaluateRx_values (X : Inputs) (j : Unit) : evaluateRx X j = primitiveRx j (values X) := rfl

/-- The explicit unknown direction changes ry and keeps rx zero. -/
def invisible : Values := fun j => if j then 1 else 0

/-- The same two actual realized inputs give identical rx replies but opposite original repair predicates. -/
theorem actual_pair :
    values (realize 0) = 0 ∧ values (realize invisible) = invisible ∧
    (∀ j, evaluateRx (realize 0) j = evaluateRx (realize invisible) j) ∧
    Nonempty (RelativeRepairComposition.W1ActualRepairs.RealRepairs true 0 0 (allowed (fun _ => false))) ∧
    ¬ Nonempty (RelativeRepairComposition.W1ActualRepairs.RealRepairs true 0 1 (allowed (fun _ => false))) := by
  refine ⟨values_realize _,values_realize _,?_,?_,?_⟩
  · intro j
    rw [evaluateRx_values,evaluateRx_values,values_realize,values_realize]
    rfl
  · have h := (actual_iff (fun _ => false) (realize 0)).mpr
      (by simpa only [values_realize] using (solvable_iff (fun _ => false) 0).mpr (Or.inl rfl))
    simpa only [values_realize] using h
  · have h : ¬ Solvable (differential (fun _ => false)) (affineRhs rhsLinear 0) invisible := by
      rw [solvable_iff]
      simp [invisible]
    have hn := fun hr => h ((actual_iff (fun _ => false) (realize invisible)).mp hr)
    simpa only [values_realize,invisible] using hn

/-- No rx-only set is numerically sufficient, even if every possible rx query is included. -/
theorem no_numerical_set : ¬ ∃ points : Finset Unit,
    SufficientSet primitiveRx (0 : Values →ₗ[ZMod 3] Values) (LinearMap.ker rhsLinear) points := by
  rintro ⟨points,hp⟩
  have ho : invisible ∈ LinearMap.ker (observation primitiveRx points) :=
    (mem_ker_observation primitiveRx points invisible).mpr (by intro j _; rfl)
  have hn := hp ⟨by simp,ho⟩
  have he := congrFun hn 1
  exact (one_ne_zero : (1 : ZMod 3) ≠ 0) he

/-- No rx-only set is decision sufficient for the same empty candidate problem. -/
theorem no_decision_set : ¬ ∃ points : Finset Unit,
    SufficientSet primitiveRx (0 : Values →ₗ[ZMod 3] Values)
      (LinearMap.ker ((LinearMap.range (differential (fun _ => false))).mkQ.comp rhsLinear)) points := by
  rintro ⟨points,hp⟩
  have ho : invisible ∈ LinearMap.ker (observation primitiveRx points) :=
    (mem_ker_observation primitiveRx points invisible).mpr (by intro j _; rfl)
  have hn := (residual_kernel_iff (fun _ => false) invisible).mp (hp ⟨by simp,ho⟩)
  simp [invisible] at hn

/-- C's replay theorem excludes every correct total physical rx-only numerical procedure. -/
theorem no_actual_numerical : ¬ ∃ next : Procedure Unit (ZMod 3) (Option Corrections),
    Correct evaluateRx (values ⁻¹' informationFiber (0 : Values →ₗ[ZMod 3] Values) 0)
      (fun X out => ValidOutput (differential (fun _ => false)) (affineRhs rhsLinear 0) (values X) out) next := by
  rintro ⟨next,hnext⟩
  have hn := no_numerical_procedure primitiveRx (differential (fun _ => false)) rhsLinear 0
    (0 : Values →ₗ[ZMod 3] Values) 0 (w := 0) rfl
    ((solvable_iff (fun _ => false) 0).mpr (Or.inl rfl)) no_numerical_set
  exact hn ⟨next,(PrimitiveInputQueries.correct_iff values realize values_realize evaluateRx
    (fun v j => primitiveRx j v) evaluateRx_values _ _ next).mp hnext⟩

/-- The same replay theorem excludes every correct total physical rx-only decision procedure. -/
theorem no_actual_decision : ¬ ∃ next : Procedure Unit (ZMod 3) Bool,
    Correct evaluateRx (values ⁻¹' informationFiber (0 : Values →ₗ[ZMod 3] Values) 0)
      (fun X out => ValidDecision (differential (fun _ => false)) rhsLinear 0 (values X) out) next := by
  rintro ⟨next,hnext⟩
  have hn := no_decision_procedure primitiveRx (differential (fun _ => false)) rhsLinear 0
    (0 : Values →ₗ[ZMod 3] Values) 0 (w := 0) rfl
    ((solvable_iff (fun _ => false) 0).mpr (Or.inl rfl)) no_decision_set
  exact hn ⟨next,(PrimitiveInputQueries.correct_iff values realize values_realize evaluateRx
    (fun v j => primitiveRx j v) evaluateRx_values _ _ next).mp hnext⟩

end AAT.AG.RepairObservationDuality.W1RestrictedQueries
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1RestrictedQueries
