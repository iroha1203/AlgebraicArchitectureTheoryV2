import ResearchLean.AG.CrossStageCoherence.PathGaugeEffectivity
import ResearchLean.AG.CrossStageCoherence.CompatiblePairRefutation
import ResearchLean.AG.CrossStageCoherence.ComparisonDescentInstances

/-!
# Finite acceptance instances for path-gauge effectivity

The reviewed noncentral-twist finite diagram supplies an explicit realizable
section at the identity edge gauge.  Its canonical comparator is nonidentity
and noncentral.  The reviewed compatible-pair counterexample admits no
realizable section, since theorem (D) would turn one into the already refuted
joint vanishing statement.

Both fixtures have actual finite presentations and nondegenerate geometric
qualification; the negative result is not obtained from an empty graph or an
uninhabited ambient type.
-/

namespace AAT.AG.CrossStageCoherence

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

namespace PathGaugeEffectivityInstances

/-- The noncentral-twist fixture is realized by its coherent identity gauge. -/
noncomputable def noncentralTwistRealizableSection :
    EdgeRealizableCellComparisonSection NoncentralTwistWitness.data :=
  edgeRealizableSectionOfCoherentAt NoncentralTwistWitness.data 1
    NoncentralTwistWitness.coherentAt_identity

/-- The compatible-pair refutation has no edge-realizable comparison section. -/
theorem compatiblePair_no_edgeRealizableSection :
    ¬ Nonempty
      (EdgeRealizableCellComparisonSection
        CompatiblePairRefutation.data) := by
  intro realizable
  exact CompatiblePairRefutation.not_joint
    ((jointVanishes_iff_nonempty_edgeRealizableSection
      CompatiblePairRefutation.data).2 realizable)

/-- Edge-realizable comparison sections have concrete positive and negative finite instances. -/
theorem edgeRealizableCellComparisonSection_instances :
    Nonempty
        (EdgeRealizableCellComparisonSection NoncentralTwistWitness.data) ∧
      ¬ Nonempty
        (EdgeRealizableCellComparisonSection
          CompatiblePairRefutation.data) :=
  ⟨⟨noncentralTwistRealizableSection⟩,
    compatiblePair_no_edgeRealizableSection⟩

end PathGaugeEffectivityInstances

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
