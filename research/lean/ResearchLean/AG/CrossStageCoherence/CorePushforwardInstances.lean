import ResearchLean.AG.CrossStageCoherence.CorePushforward
import ResearchLean.AG.CrossStageCoherence.ComparisonDescentInstances

/-!
# Finite acceptance instances for core cell-chain pushforward

The positive instance pushes the reviewed noncentral comparison section to the
core evaluator.  The negative instance reuses the nondegenerate
compatible-pair presentation but gives its two parallel active cells distinct
core projections; one core section would therefore force the known
nonidentity visible core automorphism to be identity.  The original
compatible-pair fixture separately fires theorem (G)'s kernel conclusion with
a holonomy that is both nonidentity and an actual member of `H_G`.

## Implementation notes

The negative datum changes authored comparators only; the finite presentation,
actual site, relation system, and two independent local strong certificates
are the reviewed fixture.  Empty graphs and identity-only pushforwards were
rejected as acceptance instances.
-/

namespace AAT.AG.CrossStageCoherence

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

namespace CorePushforwardRefutation

open FiniteCrossStageWitness
open CompatiblePairRefutation

/-- Finite parallel-cell data whose two authored comparators have distinct core images. -/
noncomputable def data :
    TwoLayerTransportData CompatiblePairRefutation.presentation
      FiniteModel.carrier where
  lift := CompatiblePairRefutation.liftData
  twoCellBase := by
    intro cell
    rw [CompatiblePairRefutation.pathLift_eq_id,
      CompatiblePairRefutation.pathLift_eq_id]
  comparator
    | .activeFirst => visibleComposite
    | .activeSecond => 1
    | .strict => 1

/-- The first active core factor is the reviewed nonidentity visible automorphism. -/
theorem firstCoreAuthoredFactor :
    coreCellAuthoredFactor data CellChainRefutation.firstStep =
      visibleCore := by
  rw [show CellChainRefutation.firstStep =
    @CellChainStep.forward CompatiblePairRefutation.presentation
      WitnessTwoCell.activeFirst from rfl,
    coreCellAuthoredFactor_forward]
  exact visibleComposite_pushforward

/-- The second active core factor is identity on the same semantic boundary. -/
theorem secondCoreAuthoredFactor :
    coreCellAuthoredFactor data CellChainRefutation.secondStep = 1 := by
  rw [show CellChainRefutation.secondStep =
    @CellChainStep.forward CompatiblePairRefutation.presentation
      WitnessTwoCell.activeSecond from rfl,
    coreCellAuthoredFactor_forward]
  exact map_one _

/-- No core comparison section can satisfy both parallel forward equations. -/
theorem no_coreCellComparisonSection :
    ¬ Nonempty (CoreCellComparisonSection data) := by
  rintro ⟨comparison⟩
  have firstNaturality :=
    comparison.naturality_affine CellChainRefutation.firstStep
  have secondNaturality :=
    comparison.naturality_affine CellChainRefutation.secondStep
  rw [coreCellAffineStep_apply] at firstNaturality secondNaturality
  have canonicalEquality := coreCellCanonicalFactor_eq_of_parallel data
    CellChainRefutation.firstStep CellChainRefutation.secondStep
  have authoredEquality :
      coreCellAuthoredFactor data CellChainRefutation.firstStep =
        coreCellAuthoredFactor data CellChainRefutation.secondStep := by
    calc
      coreCellAuthoredFactor data CellChainRefutation.firstStep =
          (coreCellAuthoredFactor data CellChainRefutation.firstStep *
              comparison.value CellChainRefutation.leftNode *
              (coreCellCanonicalFactor data
                CellChainRefutation.firstStep)⁻¹) *
            coreCellCanonicalFactor data CellChainRefutation.firstStep *
            (comparison.value CellChainRefutation.leftNode)⁻¹ := by group
      _ = comparison.value CellChainRefutation.rightNode *
            coreCellCanonicalFactor data CellChainRefutation.firstStep *
            (comparison.value CellChainRefutation.leftNode)⁻¹ := by
          rw [← firstNaturality]
      _ = (coreCellAuthoredFactor data CellChainRefutation.secondStep *
              comparison.value CellChainRefutation.leftNode *
              (coreCellCanonicalFactor data
                CellChainRefutation.secondStep)⁻¹) *
            coreCellCanonicalFactor data CellChainRefutation.firstStep *
            (comparison.value CellChainRefutation.leftNode)⁻¹ := by
          rw [secondNaturality]
      _ = coreCellAuthoredFactor data CellChainRefutation.secondStep := by
          rw [canonicalEquality]
          group
  rw [firstCoreAuthoredFactor, secondCoreAuthoredFactor] at authoredEquality
  exact visibleCore_ne_one authoredEquality

end CorePushforwardRefutation

namespace CorePushforwardInstances

open FiniteCrossStageWitness

/-- Core comparison-section certificates have concrete positive and negative finite instances. -/
theorem coreCellComparisonSection_instances :
    Nonempty (CoreCellComparisonSection NoncentralTwistWitness.data) ∧
      ¬ Nonempty
        (CoreCellComparisonSection CorePushforwardRefutation.data) :=
  ⟨⟨NoncentralTwistWitness.comparisonSection.pushforwardCore⟩,
    CorePushforwardRefutation.no_coreCellComparisonSection⟩

/-- The reviewed parallel interference is a nonidentity holonomy lying in `H_G`. -/
theorem compatiblePair_holonomy_nontrivial_inner :
    CellChainHolonomy CompatiblePairRefutation.data
          CellChainRefutation.twoChain ∈
        innerFiberAutSubgroup FiniteCrossStageWitness.package ∧
      CellChainHolonomy CompatiblePairRefutation.data
          CellChainRefutation.twoChain ≠ 1 := by
  refine ⟨?_, CellChainRefutation.twoChain_holonomy_ne_one⟩
  apply parallelCellTwoChain_holonomy_mem_innerFiberAutSubgroup_of_pushforward_eq
    CompatiblePairRefutation.data CellChainRefutation.firstStep
      CellChainRefutation.secondStep
  rw [pushforward_cellAuthoredFactor, pushforward_cellAuthoredFactor]
  rw [show CellChainRefutation.firstStep =
      @CellChainStep.forward CompatiblePairRefutation.presentation
        WitnessTwoCell.activeFirst from rfl,
    show CellChainRefutation.secondStep =
      @CellChainStep.forward CompatiblePairRefutation.presentation
        WitnessTwoCell.activeSecond from rfl,
    coreCellAuthoredFactor_forward, coreCellAuthoredFactor_forward]
  exact FiniteCrossStageWitness.visibleComposite_pushforward.trans
    CompatiblePairRefutation.shiftedVisibleComposite_pushforward.symm

end CorePushforwardInstances

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence

