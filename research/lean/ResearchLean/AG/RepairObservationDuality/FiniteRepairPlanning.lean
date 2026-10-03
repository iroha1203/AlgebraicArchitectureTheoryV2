import ResearchLean.AG.RepairObservationDuality.FiniteObservedValues
import ResearchLean.AG.RepairObservationDuality.FiniteMatrixSolver
import ResearchLean.AG.RepairObservationDuality.FinitePlanningFailures

/-!
# G-131 D: finite success branches and minimum query execution

## Implementation notes

All symbolic tests and planning precede actual replies. The success search
uses the known finite family model and the generated residual matrix. A
numerical finisher receives only the retained value and visible replies,
recovers the entire RHS, and applies the same generated G-130 section.
-/
namespace AAT.AG.RepairObservationDuality.FiniteRepairPlanning
open RelativeRepairComposition PrimitiveQueries
universe uk ui uv uI uJ
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {m n : Type ui} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {V : Type uv} [AddCommGroup V] [Module k V]
variable {I : Type uI} [AddCommGroup I] [Module k I] [DecidableEq I]
variable {J : Type uJ} [DecidableEq J]
variable (enumK : FiniteElimination.Enumeration k) (enumM : FiniteElimination.Enumeration m)
variable (enumN : FiniteElimination.Enumeration n) (enumV : FiniteElimination.Enumeration V)
variable (enumJ : FiniteElimination.Enumeration J)
variable (D : Matrix m n k) (B : V →ₗ[k] (m → k)) (b₀ : m → k)
variable (lam : J → V →ₗ[k] k) (L : V →ₗ[k] I) (s : I)

/-- D's success search constructs a known-fiber successful base from finite symbolic model data. -/
def findSuccess : Option V := enumV.values.find? fun v =>
  decide (L v = s ∧ FiniteMatrixSolver.residual enumK enumM enumN D (affineRhs B b₀ v) = 0)

/-- Every returned symbolic base has the retained value and independently solvable original equation. -/
theorem findSuccess_spec {w : V}
    (hw : findSuccess enumK enumM enumN enumV D B b₀ L s = some w) :
    L w = s ∧ Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) w := by
  have ht := List.find?_some hw
  have hs := of_decide_eq_true ht
  exact ⟨hs.1,(FiniteMatrixSolver.residual_zero_iff enumK enumM enumN D _).mp hs.2⟩

/-- The finite success search covers exactly every successful input of the same known fiber. -/
theorem findSuccess_isSome_iff :
    (findSuccess enumK enumM enumN enumV D B b₀ L s).isSome = true ↔
      ∃ w, L w = s ∧ Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) w := by
  rw [findSuccess,List.find?_isSome]
  constructor
  · rintro ⟨w,_,hw⟩
    have hs := of_decide_eq_true hw
    exact ⟨w,hs.1,(FiniteMatrixSolver.residual_zero_iff enumK enumM enumN D _).mp hs.2⟩
  · rintro ⟨w,hl,hs⟩
    exact ⟨w,enumV.complete w,decide_eq_true ⟨hl,
      (FiniteMatrixSolver.residual_zero_iff enumK enumM enumN D _).mpr hs⟩⟩

/-- Finite failure to find a base means every original known-fiber input is impossible. -/
theorem findSuccess_none_iff :
    findSuccess enumK enumM enumN enumV D B b₀ L s = none ↔
      ∀ v, L v = s → ¬ Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) v := by
  constructor
  · intro he v hv hs
    have ht := (findSuccess_isSome_iff enumK enumM enumN enumV D B b₀ L s).mpr ⟨v,hv,hs⟩
    simp only [he,Option.isSome_none] at ht
    exact Bool.false_ne_true ht
  · intro hi
    cases he : findSuccess enumK enumM enumN enumV D B b₀ L s with
    | none => rfl
    | some w =>
      obtain ⟨hl,hs⟩ := findSuccess_spec enumK enumM enumN enumV D B b₀ L s he
      exact (hi w hl hs).elim

/-- D's numerical finisher reads the whole acquired RHS and returns a fully evaluated correction vector. -/
def numericalFinish (hist : History J k) : Option (n → k) :=
  FiniteMatrixSolver.solve enumK enumM enumN D
    (FiniteObservedValues.readAffine enumV lam L s B b₀ hist)

/-- Every actual sufficient transcript feeds the same original RHS into the generated numerical solver. -/
theorem numericalFinish_transcript (points : Finset J)
    (hp : SufficientSet lam L (LinearMap.ker B) points) {v : V} (hv : L v = s) :
    numericalFinish enumK enumM enumN enumV D B b₀ lam L s
      (transcript (fun v j => lam j v) (FiniteMinimumPlan.questions enumJ points) v) =
        FiniteMatrixSolver.solve enumK enumM enumN D (affineRhs B b₀ v) := by
  rw [numericalFinish,FiniteObservedValues.readAffine_transcript enumV lam L s enumJ points B b₀ hp hv,
    ← affineRhs_apply]

/-- D's finite numerical procedure asks only its generated primitive list and returns its generated full answer. -/
def numericalProcedure (points : Finset J) : Procedure J k (Option (n → k)) :=
  FinitePrimitiveProcedure.procedure (FiniteMinimumPlan.questions enumJ points)
    (numericalFinish enumK enumM enumN enumV D B b₀ lam L s)

/-- The numerical controller uses exactly its known question list and generated finisher. -/
theorem numericalProcedure_apply (points : Finset J) :
    numericalProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points =
      FinitePrimitiveProcedure.procedure (FiniteMinimumPlan.questions enumJ points)
        (numericalFinish enumK enumM enumN enumV D B b₀ lam L s) := rfl

/-- D's generated numerical procedure terminates and solves the whole equation on every known-fiber input. -/
theorem numerical_correct (points : Finset J) (hp : SufficientSet lam L (LinearMap.ker B) points) :
    Correct (fun v j => lam j v) (informationFiber L s)
      (ValidOutput (FiniteMatrixSolver.differential D) (affineRhs B b₀))
      (numericalProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) := by
  apply FinitePrimitiveProcedure.correct
  intro v hv
  rw [numericalFinish_transcript enumK enumM enumN enumV enumJ D B b₀ lam L s points hp hv]
  exact FiniteMatrixSolver.solve_valid enumK enumM enumN D (affineRhs B b₀) v

/-- D's finite numerical minimum plan realizes the optimum over all correct adaptive procedures. -/
theorem numerical_minimum (points : Finset J)
    (hp : FiniteMinimumPlan.plan enumJ enumV lam L B = some points)
    {w : V} (hw : L w = s) (hs : Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) w) :
    Correct (fun v j => lam j v) (informationFiber L s)
      (ValidOutput (FiniteMatrixSolver.differential D) (affineRhs B b₀))
      (numericalProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) ∧
    worst (fun v j => lam j v) (informationFiber L s)
      (numericalProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) =
    optimum (fun v j => lam j v) (informationFiber L s)
      (ValidOutput (FiniteMatrixSolver.differential D) (affineRhs B b₀)) := by
  refine ⟨numerical_correct enumK enumM enumN enumV enumJ D B b₀ lam L s points
    (FiniteMinimumPlan.plan_spec enumJ enumV lam L B hp).1,?_⟩
  rw [numerical_optimum lam (FiniteMatrixSolver.differential D) B b₀ L s hw hs]
  calc
    _ = ((FiniteMinimumPlan.questions enumJ points).length : ℕ∞) :=
      by
        rw [numericalProcedure_apply]
        exact FinitePrimitiveProcedure.worst_eq _ _ _ _ (show w ∈ informationFiber L s from hw)
    _ = (points.card : ℕ∞) := congrArg (fun a : Nat => (a : ℕ∞)) (FiniteMinimumPlan.questions_length enumJ points)
    _ = _ := FiniteMinimumPlan.plan_card enumJ enumV lam L B hp

/-- D's finite Boolean finisher computes the native residual from the visible replies alone. -/
def decisionFinish (hist : History J k) : Bool :=
  decide (FiniteObservedValues.readAffine enumV lam L s
    ((FiniteMatrixSolver.residual enumK enumM enumN D).comp B)
    (FiniteMatrixSolver.residual enumK enumM enumN D b₀) hist = 0)

/-- D's Boolean finisher on a sufficient transcript decides the same complete original equation. -/
theorem decisionFinish_transcript (points : Finset J)
    (hp : SufficientSet lam L
      (LinearMap.ker ((FiniteMatrixSolver.residual enumK enumM enumN D).comp B)) points)
    {v : V} (hv : L v = s) :
    decisionFinish enumK enumM enumN enumV D B b₀ lam L s
      (transcript (fun v j => lam j v) (FiniteMinimumPlan.questions enumJ points) v) =
      decide (FiniteMatrixSolver.residual enumK enumM enumN D (affineRhs B b₀ v) = 0) := by
  rw [decisionFinish,FiniteObservedValues.readAffine_transcript enumV lam L s enumJ points _ _ hp hv]
  simp only [affineRhs_apply, map_add, LinearMap.comp_apply]

/-- D's Boolean controller asks exactly its computed finite minimum question list. -/
def decisionProcedure (points : Finset J) : Procedure J k Bool :=
  FinitePrimitiveProcedure.procedure (FiniteMinimumPlan.questions enumJ points)
    (decisionFinish enumK enumM enumN enumV D B b₀ lam L s)

/-- The Boolean controller exposes precisely its known list and generated residual finisher. -/
theorem decisionProcedure_apply (points : Finset J) :
    decisionProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points =
      FinitePrimitiveProcedure.procedure (FiniteMinimumPlan.questions enumJ points)
        (decisionFinish enumK enumM enumN enumV D B b₀ lam L s) := rfl

/-- D's generated Boolean procedure terminates and decides independently defined repairability on every known input. -/
theorem decision_correct (points : Finset J)
    (hp : SufficientSet lam L
      (LinearMap.ker ((FiniteMatrixSolver.residual enumK enumM enumN D).comp B)) points) :
    Correct (fun v j => lam j v) (informationFiber L s)
      (ValidDecision (FiniteMatrixSolver.differential D) B b₀)
      (decisionProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) := by
  rw [decisionProcedure_apply]
  apply FinitePrimitiveProcedure.correct
  intro v hv
  rw [decisionFinish_transcript enumK enumM enumN enumV enumJ D B b₀ lam L s points hp hv,
    valid_decision_decide_iff]
  exact FiniteMatrixSolver.residual_zero_iff enumK enumM enumN D (affineRhs B b₀ v)

/-- D's generated minimum residual plan attains the optimum over all correct adaptive decisions. -/
theorem decision_minimum (points : Finset J)
    (hp : FiniteMinimumPlan.plan enumJ enumV lam L
      ((FiniteMatrixSolver.residual enumK enumM enumN D).comp B) = some points)
    {w : V} (hw : L w = s) (hs : Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) w) :
    Correct (fun v j => lam j v) (informationFiber L s)
      (ValidDecision (FiniteMatrixSolver.differential D) B b₀)
      (decisionProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) ∧
    worst (fun v j => lam j v) (informationFiber L s)
      (decisionProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) =
    optimum (fun v j => lam j v) (informationFiber L s)
      (ValidDecision (FiniteMatrixSolver.differential D) B b₀) := by
  refine ⟨decision_correct enumK enumM enumN enumV enumJ D B b₀ lam L s points
    (FiniteMinimumPlan.plan_spec enumJ enumV lam L _ hp).1,?_⟩
  rw [decision_optimum lam (FiniteMatrixSolver.differential D) B b₀ L s hw hs,
    ← FiniteMatrixSolver.residual_comp_ker enumK enumM enumN D B]
  calc
    _ = ((FiniteMinimumPlan.questions enumJ points).length : ℕ∞) := by
      rw [decisionProcedure_apply]
      exact FinitePrimitiveProcedure.worst_eq _ _ _ _ (show w ∈ informationFiber L s from hw)
    _ = (points.card : ℕ∞) := congrArg (fun a : Nat => (a : ℕ∞)) (FiniteMinimumPlan.questions_length enumJ points)
    _ = _ := FiniteMinimumPlan.plan_card enumJ enumV lam L _ hp

end AAT.AG.RepairObservationDuality.FiniteRepairPlanning
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FiniteRepairPlanning
