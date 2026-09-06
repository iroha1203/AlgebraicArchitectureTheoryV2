import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF14
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonCoefficientNonfactorization

/-!
# Fixed changed-input coefficient-invisible separation

This module transports the fixed positive and negative qualified-comparison
pairs through the inverse of the actual `swap01` source-presentation action.
The transported endpoint pairs are identified with the result of applying the
independently generated comparison map of the reconstructed changed input to
the transported source pairs.  Full qualified membership, the exact residual
kernel criterion, coefficient collision, and nonfactorization are then proved
on that changed input.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence
open UpperGeometryCompatibleProblemInputData

set_option maxHeartbeats 4000000

namespace UpperDecisionWitness

/-- The independently reconstructed input for the fixed horizontal source
presentation change. -/
noncomputable abbrev swap01ChangedInput :=
  swap01SourcePresentationChange.changedInput

/-- The changed source pair obtained from the fixed positive source pair. -/
noncomputable def swap01ChangedPositiveSourcePair :
    CompositeFiberAut (swap01ChangedInput.sourceGeometry PUnit.unit).package ×
      CompositeFiberAut (swap01ChangedInput.sourceGeometry PUnit.unit).package :=
  (swap01SourcePresentationChange.generatedSourcePairMulEquivAt
    PUnit.unit).symm (compositeSwap12, compositeSwap12)

/-- The changed source pair obtained from the fixed negative source pair. -/
noncomputable def swap01ChangedNegativeSourcePair :
    CompositeFiberAut (swap01ChangedInput.sourceGeometry PUnit.unit).package ×
      CompositeFiberAut (swap01ChangedInput.sourceGeometry PUnit.unit).package :=
  (swap01SourcePresentationChange.generatedSourcePairMulEquivAt
    PUnit.unit).symm (compositeSwap12, 1)

/-- The changed generated-endpoint pair transported from the fixed positive
qualified pair. -/
noncomputable def swap01ChangedPositiveQualifiedPair :
    swap01ChangedInput.GeneratedQualifiedPairAt PUnit.unit :=
  (swap01SourcePresentationChange.generatedEndpointPairMulEquivAt
    PUnit.unit).symm fixedPositiveQualifiedPair

/-- The changed generated-endpoint pair transported from the fixed negative
qualified pair. -/
noncomputable def swap01ChangedNegativeQualifiedPair :
    swap01ChangedInput.GeneratedQualifiedPairAt PUnit.unit :=
  (swap01SourcePresentationChange.generatedEndpointPairMulEquivAt
    PUnit.unit).symm fixedNegativeQualifiedPair

/-- The complete product coefficient observation on the changed generated
endpoints. -/
noncomputable def swap01ChangedCoefficientObservation :
    swap01ChangedInput.GeneratedQualifiedPairAt PUnit.unit →*
      (Aut (CommRingCat.of Int) × Aut (CommRingCat.of Int)) :=
  swap01ChangedInput.generatedPairCoefficientObservationAt PUnit.unit

/-- Literal qualified-comparison membership on the changed generated
comparison. -/
def Swap01ChangedQualifiedDecision
    (pair : swap01ChangedInput.GeneratedQualifiedPairAt PUnit.unit) : Prop :=
  pair ∈ qualifiedComparisonSubgroup
    (swap01ChangedInput.generatedCompatibleUpperGeometryMateAt PUnit.unit)

/-- The old fixed positive pair is independently generated from the actual
positive source pair. -/
theorem fixedPositiveQualifiedPair_eq_generatedComparisonPairHomAt :
    fixedPositiveQualifiedPair =
      problem.data.generatedComparisonPairHomAt PUnit.unit
        (compositeSwap12, compositeSwap12) := by
  rfl

/-- The old fixed negative pair is independently generated from the actual
negative source pair. -/
theorem fixedNegativeQualifiedPair_eq_generatedComparisonPairHomAt :
    fixedNegativeQualifiedPair =
      problem.data.generatedComparisonPairHomAt PUnit.unit
        (compositeSwap12, 1) := by
  apply Prod.ext
  · rfl
  · simp [fixedNegativeQualifiedPair,
      UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt]

/-- The transported positive endpoint pair is the independently generated C3
image of the transported positive source pair. -/
theorem swap01ChangedPositiveQualifiedPair_eq_generatedComparisonPairHomAt :
    swap01ChangedPositiveQualifiedPair =
      swap01ChangedInput.generatedComparisonPairHomAt PUnit.unit
        swap01ChangedPositiveSourcePair := by
  apply (swap01SourcePresentationChange.generatedEndpointPairMulEquivAt
    PUnit.unit).injective
  simp only [swap01ChangedPositiveQualifiedPair, MulEquiv.apply_symm_apply]
  rw [swap01SourcePresentationChange.generatedEndpointPairMulEquivAt_generatedComparisonPairHomAt]
  simp only [swap01ChangedPositiveSourcePair, MulEquiv.apply_symm_apply]
  exact fixedPositiveQualifiedPair_eq_generatedComparisonPairHomAt

/-- The transported negative endpoint pair is the independently generated C3
image of the transported negative source pair. -/
theorem swap01ChangedNegativeQualifiedPair_eq_generatedComparisonPairHomAt :
    swap01ChangedNegativeQualifiedPair =
      swap01ChangedInput.generatedComparisonPairHomAt PUnit.unit
        swap01ChangedNegativeSourcePair := by
  apply (swap01SourcePresentationChange.generatedEndpointPairMulEquivAt
    PUnit.unit).injective
  simp only [swap01ChangedNegativeQualifiedPair, MulEquiv.apply_symm_apply]
  rw [swap01SourcePresentationChange.generatedEndpointPairMulEquivAt_generatedComparisonPairHomAt]
  simp only [swap01ChangedNegativeSourcePair, MulEquiv.apply_symm_apply]
  exact fixedNegativeQualifiedPair_eq_generatedComparisonPairHomAt

/-- The exact generated C3 reflection condition remains true on the fixed
changed input. -/
theorem swap01Changed_generatedPulledComparisonKernel_eq_bot :
    swap01ChangedInput.generatedPulledComparisonKernel PUnit.unit = ⊥ :=
  (swap01SourcePresentationChange.generatedPulledComparisonKernel_eq_bot_sourcePresentation_iff
      PUnit.unit).2 generatedPulledComparisonKernel_eq_bot

/-- The transported positive endpoint pair remains literally qualified for
the independently generated changed comparison. -/
theorem swap01ChangedPositiveQualifiedDecision :
    Swap01ChangedQualifiedDecision swap01ChangedPositiveQualifiedPair := by
  apply (swap01SourcePresentationChange.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
      PUnit.unit swap01ChangedPositiveQualifiedPair).mpr
  simpa only [swap01ChangedPositiveQualifiedPair,
    MulEquiv.apply_symm_apply] using fixedPositiveQualifiedDecision

/-- The transported negative endpoint pair remains outside the literal
qualified-comparison subgroup. -/
theorem swap01ChangedNegativeNotQualifiedDecision :
    ¬ Swap01ChangedQualifiedDecision swap01ChangedNegativeQualifiedPair := by
  apply (swap01SourcePresentationChange.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
      PUnit.unit swap01ChangedNegativeQualifiedPair).not.mpr
  simpa only [swap01ChangedNegativeQualifiedPair,
    MulEquiv.apply_symm_apply] using fixedNegativeNotQualifiedDecision

/-- The transported positive and negative endpoint pairs remain invisible to
the complete product coefficient observation. -/
theorem swap01ChangedCoefficientObservation_positive_eq_negative :
    swap01ChangedCoefficientObservation swap01ChangedPositiveQualifiedPair =
      swap01ChangedCoefficientObservation swap01ChangedNegativeQualifiedPair := by
  calc
    _ = problem.data.generatedPairCoefficientObservationAt PUnit.unit
        (swap01SourcePresentationChange.generatedEndpointPairMulEquivAt
          PUnit.unit swap01ChangedPositiveQualifiedPair) :=
      (swap01SourcePresentationChange.generatedEndpointPairMulEquivAt_coefficientObservation
          PUnit.unit swap01ChangedPositiveQualifiedPair).symm
    _ = problem.data.generatedPairCoefficientObservationAt PUnit.unit
        fixedPositiveQualifiedPair := by
      rw [swap01ChangedPositiveQualifiedPair, MulEquiv.apply_symm_apply]
    _ = problem.data.generatedPairCoefficientObservationAt PUnit.unit
        fixedNegativeQualifiedPair := by
      simpa only [fixedCoefficientObservation] using
        fixedCoefficientObservation_positive_eq_negative
    _ = problem.data.generatedPairCoefficientObservationAt PUnit.unit
        (swap01SourcePresentationChange.generatedEndpointPairMulEquivAt
          PUnit.unit swap01ChangedNegativeQualifiedPair) := by
      rw [swap01ChangedNegativeQualifiedPair, MulEquiv.apply_symm_apply]
    _ = _ :=
      swap01SourcePresentationChange.generatedEndpointPairMulEquivAt_coefficientObservation
          PUnit.unit swap01ChangedNegativeQualifiedPair

/-- Exact C3 reflection recovers source identity-comparison membership of the
transported positive source pair. -/
theorem swap01ChangedPositiveSourceDecision :
    swap01ChangedPositiveSourcePair ∈ qualifiedComparisonSubgroup
      (𝟙 (swap01ChangedInput.sourceGeometry PUnit.unit).package) := by
  apply (swap01ChangedInput.generatedComparisonPairHomAt_mem_qualifiedComparison_iff_of_kernel_eq_bot
      PUnit.unit swap01Changed_generatedPulledComparisonKernel_eq_bot
      swap01ChangedPositiveSourcePair).mp
  rw [← swap01ChangedPositiveQualifiedPair_eq_generatedComparisonPairHomAt]
  exact swap01ChangedPositiveQualifiedDecision

/-- Exact C3 reflection recovers failure of source identity-comparison
membership for the transported negative source pair. -/
theorem swap01ChangedNegativeSourceNotQualifiedDecision :
    ¬ swap01ChangedNegativeSourcePair ∈ qualifiedComparisonSubgroup
      (𝟙 (swap01ChangedInput.sourceGeometry PUnit.unit).package) := by
  apply (swap01ChangedInput.generatedComparisonPairHomAt_mem_qualifiedComparison_iff_of_kernel_eq_bot
      PUnit.unit swap01Changed_generatedPulledComparisonKernel_eq_bot
      swap01ChangedNegativeSourcePair).not.mp
  rw [← swap01ChangedNegativeQualifiedPair_eq_generatedComparisonPairHomAt]
  exact swap01ChangedNegativeNotQualifiedDecision

/-- The transported source pairs have equal complete coefficient
observations, as witnessed through their independently generated C3 images. -/
theorem swap01ChangedSourceCoefficientObservation_positive_eq_negative :
    swap01ChangedInput.sourcePairCoefficientObservationAt PUnit.unit
        swap01ChangedPositiveSourcePair =
      swap01ChangedInput.sourcePairCoefficientObservationAt PUnit.unit
        swap01ChangedNegativeSourcePair := by
  calc
    _ = swap01ChangedInput.generatedPairCoefficientObservationAt PUnit.unit
        (swap01ChangedInput.generatedComparisonPairHomAt PUnit.unit
          swap01ChangedPositiveSourcePair) :=
      (swap01ChangedInput.generatedComparisonPairHomAt_coefficientObservation
        PUnit.unit swap01ChangedPositiveSourcePair).symm
    _ = swap01ChangedInput.generatedPairCoefficientObservationAt PUnit.unit
        swap01ChangedPositiveQualifiedPair := by
      rw [swap01ChangedPositiveQualifiedPair_eq_generatedComparisonPairHomAt]
    _ = swap01ChangedInput.generatedPairCoefficientObservationAt PUnit.unit
        swap01ChangedNegativeQualifiedPair :=
      swap01ChangedCoefficientObservation_positive_eq_negative
    _ = swap01ChangedInput.generatedPairCoefficientObservationAt PUnit.unit
        (swap01ChangedInput.generatedComparisonPairHomAt PUnit.unit
          swap01ChangedNegativeSourcePair) := by
      rw [swap01ChangedNegativeQualifiedPair_eq_generatedComparisonPairHomAt]
    _ = _ :=
      swap01ChangedInput.generatedComparisonPairHomAt_coefficientObservation
        PUnit.unit swap01ChangedNegativeSourcePair

/-- The changed qualified decision still cannot factor through its complete
coefficient observation. -/
theorem swap01ChangedQualifiedDecision_not_factor_through_coefficientObservation :
    ¬ ∃ diagnostic :
        (Aut (CommRingCat.of Int) × Aut (CommRingCat.of Int)) → Prop,
      ∀ pair : swap01ChangedInput.GeneratedQualifiedPairAt PUnit.unit,
        Swap01ChangedQualifiedDecision pair ↔
          diagnostic (swap01ChangedCoefficientObservation pair) := by
  simpa only [Swap01ChangedQualifiedDecision,
    swap01ChangedCoefficientObservation] using
    (swap01ChangedInput.generatedQualifiedDecision_not_factor_of_source_collision
      PUnit.unit swap01Changed_generatedPulledComparisonKernel_eq_bot
      swap01ChangedPositiveSourcePair swap01ChangedNegativeSourcePair
      swap01ChangedSourceCoefficientObservation_positive_eq_negative
      swap01ChangedPositiveSourceDecision
      swap01ChangedNegativeSourceNotQualifiedDecision)

/-- Cycle 28 acceptance packet: the actual source-presentation action fires,
both transported pairs are independently regenerated by C3 on the changed
input, the exact pulled kernel remains trivial, literal endpoint and reflected
source decisions separate, the complete coefficient observation collides, and
the changed-input decision cannot factor through that observation. -/
theorem swap01ChangedInput_transport_packet :
    swap01SourcePresentationChange.generatedSourcePairMulEquivAt PUnit.unit
        (compositeSwap12, 1) ≠ (compositeSwap12, 1) ∧
      swap01ChangedPositiveQualifiedPair =
        swap01ChangedInput.generatedComparisonPairHomAt PUnit.unit
          swap01ChangedPositiveSourcePair ∧
      swap01ChangedNegativeQualifiedPair =
        swap01ChangedInput.generatedComparisonPairHomAt PUnit.unit
          swap01ChangedNegativeSourcePair ∧
      swap01ChangedInput.generatedPulledComparisonKernel PUnit.unit = ⊥ ∧
      Swap01ChangedQualifiedDecision swap01ChangedPositiveQualifiedPair ∧
      ¬ Swap01ChangedQualifiedDecision swap01ChangedNegativeQualifiedPair ∧
      swap01ChangedPositiveSourcePair ∈ qualifiedComparisonSubgroup
        (𝟙 (swap01ChangedInput.sourceGeometry PUnit.unit).package) ∧
      ¬ swap01ChangedNegativeSourcePair ∈ qualifiedComparisonSubgroup
        (𝟙 (swap01ChangedInput.sourceGeometry PUnit.unit).package) ∧
      swap01ChangedCoefficientObservation swap01ChangedPositiveQualifiedPair =
        swap01ChangedCoefficientObservation swap01ChangedNegativeQualifiedPair ∧
      ¬ ∃ diagnostic :
          (Aut (CommRingCat.of Int) × Aut (CommRingCat.of Int)) → Prop,
        ∀ pair : swap01ChangedInput.GeneratedQualifiedPairAt PUnit.unit,
          Swap01ChangedQualifiedDecision pair ↔
            diagnostic (swap01ChangedCoefficientObservation pair) := by
  exact ⟨swap01_induced_source_pair_action_ne,
    swap01ChangedPositiveQualifiedPair_eq_generatedComparisonPairHomAt,
    swap01ChangedNegativeQualifiedPair_eq_generatedComparisonPairHomAt,
    swap01Changed_generatedPulledComparisonKernel_eq_bot,
    swap01ChangedPositiveQualifiedDecision,
    swap01ChangedNegativeNotQualifiedDecision,
    swap01ChangedPositiveSourceDecision,
    swap01ChangedNegativeSourceNotQualifiedDecision,
    swap01ChangedCoefficientObservation_positive_eq_negative,
    swap01ChangedQualifiedDecision_not_factor_through_coefficientObservation⟩

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
