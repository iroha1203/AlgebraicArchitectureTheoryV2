import ResearchLean.AG.RepairObservationDuality.FiniteRepairPlanning
/-!
# G-131 D: complete symbolic planning branches

## Implementation notes

The planner takes only the known model and retained values, before actual
replies. It returns an impossible fiber, a minimum question set, or a computed
successful base and invisible changing direction. No sufficient answer or
counterexample is supplied. Plain output data has an independent theorem.
-/
namespace AAT.AG.RepairObservationDuality.FinitePlanningBranches
open RelativeRepairComposition PrimitiveQueries
universe uk ui uv uI uJ uW
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {m n : Type ui} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {V : Type uv} [AddCommGroup V] [Module k V]
variable {I : Type uI} [AddCommGroup I] [Module k I] [DecidableEq I]
variable {J : Type uJ} [DecidableEq J]
variable {W : Type uW} [AddCommGroup W] [Module k W] [DecidableEq W]
variable (enumK : FiniteElimination.Enumeration k) (enumM : FiniteElimination.Enumeration m)
variable (enumN : FiniteElimination.Enumeration n) (enumV : FiniteElimination.Enumeration V)
variable (enumJ : FiniteElimination.Enumeration J)
variable (D : Matrix m n k) (B : V →ₗ[k] (m → k)) (b₀ : m → k)
variable (lam : J → V →ₗ[k] k) (L : V →ₗ[k] I) (s : I) (Q : V →ₗ[k] W)

/-- D's computed plan returns an impossible fiber, minimum questions, or a genuine invisible changing pair. -/
def plan : Option (Finset J) ⊕ (V × V) :=
  match FiniteRepairPlanning.findSuccess enumK enumM enumN enumV D B b₀ L s with
  | none => Sum.inl none
  | some w => match FiniteMinimumPlan.plan enumJ enumV lam L Q with
    | some points => Sum.inl (some points)
    | none => Sum.inr (w,(FinitePlanningFailures.findDirection enumV enumJ lam L Q).getD 0)

/-- Every finite planner branch satisfies the independent original equation and full kernel specification. -/
theorem plan_spec :
    match plan enumK enumM enumN enumV enumJ D B b₀ lam L s Q with
    | Sum.inl none => ∀ v, L v = s → ¬ Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) v
    | Sum.inl (some points) =>
        (∃ w, L w = s ∧ Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) w) ∧
          FiniteMinimumPlan.plan enumJ enumV lam L Q = some points
    | Sum.inr (w,r) => L w = s ∧ Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) w ∧
        L r = 0 ∧ (∀ j : J, lam j r = 0) ∧ Q r ≠ 0 ∧
          FiniteMinimumPlan.plan enumJ enumV lam L Q = none := by
  unfold plan
  cases hw : FiniteRepairPlanning.findSuccess enumK enumM enumN enumV D B b₀ L s with
  | none => exact (FiniteRepairPlanning.findSuccess_none_iff enumK enumM enumN enumV D B b₀ L s).mp hw
  | some w =>
    have hs := FiniteRepairPlanning.findSuccess_spec enumK enumM enumN enumV D B b₀ L s hw
    cases hp : FiniteMinimumPlan.plan enumJ enumV lam L Q with
    | some points => exact ⟨⟨w,hs⟩,rfl⟩
    | none =>
      have hd := (FinitePlanningFailures.findDirection_isSome_iff enumV enumJ lam L Q).mpr
        ((FiniteMinimumPlan.plan_none_iff enumJ enumV lam L Q).mp hp)
      cases hr : FinitePlanningFailures.findDirection enumV enumJ lam L Q with
      | none => rw [hr] at hd; exact (Bool.false_ne_true hd).elim
      | some r =>
        simp only [Option.getD_some]
        have hc := FinitePlanningFailures.findDirection_spec enumV enumJ lam L Q hr
        exact ⟨hs.1,hs.2,hc.1,hc.2.1,hc.2.2,True.intro⟩

/-- A returned ready branch has a generated successful base and the actual finite argmin plan. -/
theorem ready_spec {points : Finset J}
    (hp : plan enumK enumM enumN enumV enumJ D B b₀ lam L s Q = Sum.inl (some points)) :
    (∃ w, L w = s ∧ Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) w) ∧
      FiniteMinimumPlan.plan enumJ enumV lam L Q = some points := by
  have h := plan_spec enumK enumM enumN enumV enumJ D B b₀ lam L s Q
  rw [hp] at h
  exact h

/-- The computed impossible-fiber branch certifies every original known input is impossible. -/
theorem impossible_spec
    (hp : plan enumK enumM enumN enumV enumJ D B b₀ lam L s Q = Sum.inl none) :
    ∀ v, L v = s → ¬ Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) v := by
  have h := plan_spec enumK enumM enumN enumV enumJ D B b₀ lam L s Q
  rw [hp] at h
  exact h

/-- A computed failure gives two known inputs with identical replies but distinct specified targets. -/
theorem failure_spec {w r : V}
    (hp : plan enumK enumM enumN enumV enumJ D B b₀ lam L s Q = Sum.inr (w,r)) :
    L w = s ∧ Solvable (FiniteMatrixSolver.differential D) (affineRhs B b₀) w ∧
    L (w + r) = s ∧ (∀ j : J, lam j (w + r) = lam j w) ∧ Q (w + r) ≠ Q w ∧
    ¬ ∃ points, SufficientSet lam L (LinearMap.ker Q) points := by
  have h := plan_spec enumK enumM enumN enumV enumJ D B b₀ lam L s Q
  rw [hp] at h
  refine ⟨h.1,h.2.1,by rw [map_add,h.1,h.2.2.1,add_zero],
    fun j => by rw [map_add,h.2.2.2.1 j,add_zero],?_,
    (FiniteMinimumPlan.plan_none_iff enumJ enumV lam L Q).mp h.2.2.2.2.2⟩
  rw [map_add]
  exact fun he => h.2.2.2.2.1 (add_left_cancel (he.trans (add_zero (Q w)).symm))

/-- A generated numerical ready plan terminates correctly and attains the all-adaptive full-output optimum. -/
theorem numerical_ready {points : Finset J}
    (hp : plan enumK enumM enumN enumV enumJ D B b₀ lam L s B = Sum.inl (some points)) :
    Correct (fun v j => lam j v) (informationFiber L s)
      (ValidOutput (FiniteMatrixSolver.differential D) (affineRhs B b₀))
      (FiniteRepairPlanning.numericalProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) ∧
    worst (fun v j => lam j v) (informationFiber L s)
      (FiniteRepairPlanning.numericalProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) =
    optimum (fun v j => lam j v) (informationFiber L s)
      (ValidOutput (FiniteMatrixSolver.differential D) (affineRhs B b₀)) := by
  obtain ⟨⟨w,hw,hs⟩,hm⟩ := ready_spec enumK enumM enumN enumV enumJ D B b₀ lam L s B hp
  exact FiniteRepairPlanning.numerical_minimum enumK enumM enumN enumV enumJ D B b₀ lam L s points hm hw hs

/-- A generated decision ready plan attains the all-adaptive optimum using the residual criterion. -/
theorem decision_ready {points : Finset J}
    (hp : plan enumK enumM enumN enumV enumJ D B b₀ lam L s
      ((FiniteMatrixSolver.residual enumK enumM enumN D).comp B) = Sum.inl (some points)) :
    Correct (fun v j => lam j v) (informationFiber L s)
      (ValidDecision (FiniteMatrixSolver.differential D) B b₀)
      (FiniteRepairPlanning.decisionProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) ∧
    worst (fun v j => lam j v) (informationFiber L s)
      (FiniteRepairPlanning.decisionProcedure enumK enumM enumN enumV enumJ D B b₀ lam L s points) =
    optimum (fun v j => lam j v) (informationFiber L s)
      (ValidDecision (FiniteMatrixSolver.differential D) B b₀) := by
  obtain ⟨⟨w,hw,hs⟩,hm⟩ := ready_spec enumK enumM enumN enumV enumJ D B b₀ lam L s _ hp
  exact FiniteRepairPlanning.decision_minimum enumK enumM enumN enumV enumJ D B b₀ lam L s points hm hw hs

/-- A generated numerical failure excludes every correct total adaptive full-output procedure. -/
theorem numerical_failure {w r : V}
    (hp : plan enumK enumM enumN enumV enumJ D B b₀ lam L s B = Sum.inr (w,r)) :
    ¬ ∃ next : Procedure J k (Option (n → k)),
      Correct (fun v j => lam j v) (informationFiber L s)
        (ValidOutput (FiniteMatrixSolver.differential D) (affineRhs B b₀)) next := by
  have h := failure_spec enumK enumM enumN enumV enumJ D B b₀ lam L s B hp
  exact no_numerical_procedure lam (FiniteMatrixSolver.differential D) B b₀ L s h.1 h.2.1 h.2.2.2.2.2

/-- A generated decision failure excludes every correct total adaptive repairability procedure. -/
theorem decision_failure {w r : V}
    (hp : plan enumK enumM enumN enumV enumJ D B b₀ lam L s
      ((FiniteMatrixSolver.residual enumK enumM enumN D).comp B) = Sum.inr (w,r)) :
    ¬ ∃ next : Procedure J k Bool,
      Correct (fun v j => lam j v) (informationFiber L s)
        (ValidDecision (FiniteMatrixSolver.differential D) B b₀) next := by
  have h := failure_spec enumK enumM enumN enumV enumJ D B b₀ lam L s _ hp
  apply no_decision_procedure lam (FiniteMatrixSolver.differential D) B b₀ L s h.1 h.2.1
  simpa only [← FiniteMatrixSolver.residual_comp_ker enumK enumM enumN D B] using h.2.2.2.2.2

/-- A computed impossible fiber gives correct zero-query answers and zero optima for both output types. -/
theorem impossible_zero
    (hp : plan enumK enumM enumN enumV enumJ D B b₀ lam L s Q = Sum.inl none) :
    Correct (fun v j => lam j v) (informationFiber L s)
      (ValidDecision (FiniteMatrixSolver.differential D) B b₀) (constant false) ∧
    Correct (fun v j => lam j v) (informationFiber L s)
      (ValidOutput (FiniteMatrixSolver.differential D) (affineRhs B b₀)) (constant none) ∧
    optimum (fun v j => lam j v) (informationFiber L s)
      (ValidDecision (FiniteMatrixSolver.differential D) B b₀) = 0 ∧
    optimum (fun v j => lam j v) (informationFiber L s)
      (ValidOutput (FiniteMatrixSolver.differential D) (affineRhs B b₀)) = 0 := by
  have hi := impossible_spec enumK enumM enumN enumV enumJ D B b₀ lam L s Q hp
  refine ⟨constant_correct _ _ _ false (fun v hv => iff_of_false Bool.false_ne_true (hi v hv)),
    constant_correct _ _ _ none hi,?_⟩
  exact all_impossible_optima_zero lam (FiniteMatrixSolver.differential D) B b₀ L s hi

end AAT.AG.RepairObservationDuality.FinitePlanningBranches
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FinitePlanningBranches
