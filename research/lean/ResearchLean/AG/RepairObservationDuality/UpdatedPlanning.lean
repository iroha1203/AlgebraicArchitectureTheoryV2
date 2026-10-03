import ResearchLean.AG.RepairObservationDuality.FinitePlanningBranches
import ResearchLean.AG.RepairObservationDuality.KnownValueUpdates
/-!
# G-131 D: minimum additional planning after retained values and notifications

## Implementation notes

The same structural matrix and generated G-130 section are reused. Only the
information fiber changes: the model retains specified old rows and adds the
received notification rows. Stale unreceived values are no algorithm input.
The finite planner and all-adaptive optimum are applied to precisely this
new fiber, including entirely impossible and no-sufficient-plan branches.
-/
namespace AAT.AG.RepairObservationDuality.UpdatedPlanning
open RelativeRepairComposition PrimitiveQueries
universe uk ui uv uI uT uJ
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {m n : Type ui} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {V : Type uv} [AddCommGroup V] [Module k V]
variable {I : Type uI} [AddCommGroup I] [Module k I] [DecidableEq I]
variable {T : Type uT} [AddCommGroup T] [Module k T] [DecidableEq T]
variable {J : Type uJ} [DecidableEq J]
variable (enumK : FiniteElimination.Enumeration k) (enumM : FiniteElimination.Enumeration m)
variable (enumN : FiniteElimination.Enumeration n) (enumV : FiniteElimination.Enumeration V)
variable (enumJ : FiniteElimination.Enumeration J)
variable (D : Matrix m n k) (B : V →ₗ[k] (m → k)) (b₀ : m → k)
variable (lam : J → V →ₗ[k] k) (retained : V →ₗ[k] I) (notified : V →ₗ[k] T) (s : I) (t : T)

omit [Fintype k] [DecidableEq k] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [DecidableEq I] [DecidableEq T] [DecidableEq J] in
/-- D's updated sufficient-set test uses exactly the unknown directions after actual retained and notified values. -/
theorem sufficient_after_update_iff (R : Submodule k V) (points : Finset J) :
    SufficientSet lam (KnownValueUpdates.information retained notified) R points ↔
    (LinearMap.ker retained ⊓ LinearMap.ker notified) ⊓ LinearMap.ker (observation lam points) ≤ R := by
  rw [sufficientSet_iff,KnownValueUpdates.information_ker]

/-- The returned additional numerical minimum executes correctly on the updated fiber and attains its all-adaptive optimum. -/
theorem numerical_ready {points : Finset J}
    (hp : FinitePlanningBranches.plan enumK enumM enumN enumV enumJ D B b₀ lam
      (KnownValueUpdates.information retained notified) (s,t) B = Sum.inl (some points)) :
    Correct (fun v j => lam j v) (informationFiber (KnownValueUpdates.information retained notified) (s,t))
      (ValidOutput (FiniteMatrixSolver.differential D) (affineRhs B b₀))
      (FiniteRepairPlanning.numericalProcedure enumK enumM enumN enumV enumJ D B b₀ lam
        (KnownValueUpdates.information retained notified) (s,t) points) ∧
    worst (fun v j => lam j v) (informationFiber (KnownValueUpdates.information retained notified) (s,t))
      (FiniteRepairPlanning.numericalProcedure enumK enumM enumN enumV enumJ D B b₀ lam
        (KnownValueUpdates.information retained notified) (s,t) points) =
      minimum lam (KnownValueUpdates.information retained notified) (LinearMap.ker B) := by
  have h := FinitePlanningBranches.numerical_ready enumK enumM enumN enumV enumJ D B b₀ lam
    (KnownValueUpdates.information retained notified) (s,t) hp
  obtain ⟨⟨w,hw,hs⟩,_⟩ := FinitePlanningBranches.ready_spec enumK enumM enumN enumV enumJ D B b₀ lam
    (KnownValueUpdates.information retained notified) (s,t) B hp
  exact ⟨h.1,h.2.trans (numerical_optimum lam (FiniteMatrixSolver.differential D) B b₀
    (KnownValueUpdates.information retained notified) (s,t) hw hs)⟩

/-- The returned additional decision minimum attains the updated adaptive optimum with the residual target kernel. -/
theorem decision_ready {points : Finset J}
    (hp : FinitePlanningBranches.plan enumK enumM enumN enumV enumJ D B b₀ lam
      (KnownValueUpdates.information retained notified) (s,t)
      ((FiniteMatrixSolver.residual enumK enumM enumN D).comp B) = Sum.inl (some points)) :
    Correct (fun v j => lam j v) (informationFiber (KnownValueUpdates.information retained notified) (s,t))
      (ValidDecision (FiniteMatrixSolver.differential D) B b₀)
      (FiniteRepairPlanning.decisionProcedure enumK enumM enumN enumV enumJ D B b₀ lam
        (KnownValueUpdates.information retained notified) (s,t) points) ∧
    worst (fun v j => lam j v) (informationFiber (KnownValueUpdates.information retained notified) (s,t))
      (FiniteRepairPlanning.decisionProcedure enumK enumM enumN enumV enumJ D B b₀ lam
        (KnownValueUpdates.information retained notified) (s,t) points) =
      minimum lam (KnownValueUpdates.information retained notified)
        (LinearMap.ker ((LinearMap.range (FiniteMatrixSolver.differential D)).mkQ.comp B)) := by
  have h := FinitePlanningBranches.decision_ready enumK enumM enumN enumV enumJ D B b₀ lam
    (KnownValueUpdates.information retained notified) (s,t) hp
  obtain ⟨⟨w,hw,hs⟩,_⟩ := FinitePlanningBranches.ready_spec enumK enumM enumN enumV enumJ D B b₀ lam
    (KnownValueUpdates.information retained notified) (s,t) _ hp
  exact ⟨h.1,h.2.trans (decision_optimum lam (FiniteMatrixSolver.differential D) B b₀
    (KnownValueUpdates.information retained notified) (s,t) hw hs)⟩

end AAT.AG.RepairObservationDuality.UpdatedPlanning
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.UpdatedPlanning
