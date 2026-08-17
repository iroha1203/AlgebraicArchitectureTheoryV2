import ResearchLean.AG.CrossStageCoherence.RealizablePushforward
import ResearchLean.AG.CrossStageCoherence.PathGaugeEffectivityInstances
import ResearchLean.AG.CrossStageCoherence.CorePushforwardInstances

/-!
# Finite acceptance instances for core path-gauge realizability

The positive certificate is the pointwise core image of the reviewed
noncentral-twist upper realization.  The negative certificate is impossible
on the reviewed finite datum admitting no core comparison section at all.
Thus the new core realizability structure has both inhabited and uninhabited
finite instances, without weakening its realization field.
-/

namespace AAT.AG.CrossStageCoherence

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

namespace RealizablePushforwardInstances

/-- The noncentral upper realization has an explicit pointwise core image. -/
noncomputable def noncentralTwistCoreRealizableSection :
    CoreEdgeRealizableCellComparisonSection NoncentralTwistWitness.data :=
  PathGaugeEffectivityInstances.noncentralTwistRealizableSection.pushforwardCore

/-- No core realization can exist when even its underlying core section is absent. -/
theorem no_coreEdgeRealizableSection :
    ¬ Nonempty
      (CoreEdgeRealizableCellComparisonSection
        CorePushforwardRefutation.data) := by
  rintro ⟨realizable⟩
  exact CorePushforwardRefutation.no_coreCellComparisonSection
    ⟨realizable.comparison⟩

/-- Core edge-realizable certificates have concrete positive and negative instances. -/
theorem coreEdgeRealizableCellComparisonSection_instances :
    Nonempty
        (CoreEdgeRealizableCellComparisonSection
          NoncentralTwistWitness.data) ∧
      ¬ Nonempty
        (CoreEdgeRealizableCellComparisonSection
          CorePushforwardRefutation.data) :=
  ⟨⟨noncentralTwistCoreRealizableSection⟩,
    no_coreEdgeRealizableSection⟩

end RealizablePushforwardInstances

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
