import ResearchLean.AG.RepairObservationDuality.FiniteObservedValues
import ResearchLean.AG.RepairObservationDuality.DualValueAcquisition
/-!
# G-131 D: finite acquisition of the same specified residual dual value

## Implementation notes

The executable value is the finite visible-history recovery from the known
parameter model. Its affine constant and pullback are those of the specified
original dual. A minimum sufficient plan is generated before its replies;
the restricted-span criterion supplies exactly the same kernel test.
-/
namespace AAT.AG.RepairObservationDuality.FiniteDualAcquisition
open RelativeRepairComposition PrimitiveQueries
variable {k V I H W J : Type*} [Field k] [DecidableEq k]
variable [AddCommGroup V] [Module k V] [AddCommGroup I] [Module k I] [DecidableEq I]
variable [AddCommGroup H] [Module k H] [AddCommGroup W] [Module k W] [DecidableEq J]
variable (enumV : FiniteElimination.Enumeration V) (enumJ : FiniteElimination.Enumeration J)
variable (lam : J → V →ₗ[k] k) (L : V →ₗ[k] I) (s : I)
variable (D : H →ₗ[k] W) (B : V →ₗ[k] W) (b₀ : W)
variable (ell : Module.Dual k (W ⧸ LinearMap.range D))

/-- D's finite minimum plan computes the same specified original residual dual value on every actual transcript. -/
theorem minimum_value (points : Finset J)
    (hp : FiniteMinimumPlan.plan enumJ enumV lam L
      (ell.comp ((LinearMap.range D).mkQ.comp B)) = some points) {v : V} (hv : L v = s) :
    FiniteObservedValues.readAffine enumV lam L s (ell.comp ((LinearMap.range D).mkQ.comp B))
      (ell ((LinearMap.range D).mkQ b₀))
      (transcript (fun v j => lam j v) (FiniteMinimumPlan.questions enumJ points) v) =
        ell ((LinearMap.range D).mkQ (b₀ + B v)) := by
  rw [FiniteObservedValues.readAffine_transcript enumV lam L s enumJ points _ _
    (FiniteMinimumPlan.plan_spec enumJ enumV lam L _ hp).1 hv]
  exact (DualValueAcquisition.residual_value_affine D B b₀ ell v).symm

/-- The original restricted primitive span guarantees exact terminating finite acquisition of that same dual value. -/
theorem value_of_span [FiniteDimensional k V] (points : Finset J)
    (hs : (ell.comp ((LinearMap.range D).mkQ.comp B)).comp (LinearMap.ker L).subtype ∈
      LinearObservationDuality.evaluationSpan
        (fun j => (lam j).comp (LinearMap.ker L).subtype) points)
    {v : V} (hv : L v = s) :
    FiniteObservedValues.readAffine enumV lam L s (ell.comp ((LinearMap.range D).mkQ.comp B))
      (ell ((LinearMap.range D).mkQ b₀))
      (transcript (fun v j => lam j v) (FiniteMinimumPlan.questions enumJ points) v) =
        ell ((LinearMap.range D).mkQ (b₀ + B v)) := by
  have hspan : (ell.comp ((LinearMap.range D).mkQ.comp B)).comp (LinearMap.ker L).subtype ∈
      (LinearMap.ker (observation (fun j => (lam j).comp (LinearMap.ker L).subtype) points)).dualAnnihilator := by
    rwa [LinearObservationDuality.observation_annihilator]
  have hk := (DualValueAcquisition.restriction_iff L lam points _).mp hspan
  rw [FiniteObservedValues.readAffine_transcript enumV lam L s enumJ points _ _
    ((sufficientSet_iff lam L _ points).mpr hk) hv]
  exact (DualValueAcquisition.residual_value_affine D B b₀ ell v).symm

end AAT.AG.RepairObservationDuality.FiniteDualAcquisition
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FiniteDualAcquisition
