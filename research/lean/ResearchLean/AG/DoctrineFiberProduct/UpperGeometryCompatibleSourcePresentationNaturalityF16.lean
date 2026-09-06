import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF15
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonEdgeReselectionConsequences

/-!
# Changed-input C2 provenance and mixed C1 closure

This module reconstructs the fixed coefficient-trivial edge reselections from
the authored comparator of the changed input itself.  Their generated base and
pulled values are connected to the changed C3 positive pair, while replacing
the pulled value by identity gives the changed negative pair.  The resulting
decision split is then transported through every type-correct C1t-before,
C1s, C1t-after composite.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence
open UpperGeometryCompatibleProblemInputData

set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 200000

namespace UpperGeometryCompatibleSourcePresentationChange

universe u v

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- The comparator reconstructed inside the changed input is sent back to the
old authored comparator by the actual source conjugation equivalence. -/
theorem generatedSourceConjugation_changedComparator
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (cell : P.TwoCell) :
    CompositeFiberAut.conjugationMulEquiv
        (change.geometryIso (P.twoTarget cell))
        (change.changedInput.sourceTransport.comparator cell) =
      input.sourceTransport.comparator cell := by
  change CompositeFiberAut.conjugationEquiv
      (change.geometryIso (P.twoTarget cell))
      (CompositeFiberAut.conjugationEquiv
        (change.geometryIso (P.twoTarget cell)).symm
        (input.sourceTransport.comparator cell)) =
    input.sourceTransport.comparator cell
  exact (CompositeFiberAut.conjugationEquiv
    (change.geometryIso (P.twoTarget cell))).apply_symm_apply _

end UpperGeometryCompatibleSourcePresentationChange

namespace UpperDecisionWitness

/-- The changed authored comparator, used uniformly on the one-edge fixed
presentation, is an actual coefficient-trivial source reselection. -/
noncomputable def swap01ChangedSourceComparatorReselection :
    SourceCoefficientTrivialUpperEdgeReselection swap01ChangedInput where
  toUpperEdgeReselection := fun _ _ _ =>
    swap01ChangedInput.sourceTransport.comparator DecisionCell.comparison
  coefficient_id := fun _ =>
    swap01ChangedInput.sourceTransport.comparator_coefficient_id
      DecisionCell.comparison

/-- Apply the changed input's independently generated base map to its source
comparator reselection. -/
noncomputable def swap01ChangedBaseComparatorReselection :
    GeneratedBaseCoefficientTrivialUpperEdgeReselection swap01ChangedInput :=
  swap01ChangedInput.generatedBaseOfSourceCoefficientTrivialUpperEdgeReselection
    swap01ChangedSourceComparatorReselection

/-- Apply the changed input's independently generated pulled map to the same
source comparator reselection. -/
noncomputable def swap01ChangedPulledComparatorReselection :
    GeneratedPulledCoefficientTrivialUpperEdgeReselection swap01ChangedInput :=
  swap01ChangedInput.generatedPulledOfSourceCoefficientTrivialUpperEdgeReselection
    swap01ChangedSourceComparatorReselection

/-- The positive C2 edge value reconstructed entirely inside the changed
input. -/
noncomputable def swap01ChangedC2PositiveQualifiedPair :
    swap01ChangedInput.GeneratedQualifiedPairAt PUnit.unit :=
  (swap01ChangedBaseComparatorReselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist,
    swap01ChangedPulledComparatorReselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist)

/-- The negative C2 edge value retains the reconstructed generated base value
and independently selects identity on the changed pulled route. -/
noncomputable def swap01ChangedC2NegativeQualifiedPair :
    swap01ChangedInput.GeneratedQualifiedPairAt PUnit.unit :=
  (swap01ChangedBaseComparatorReselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist,
    (CoefficientTrivialUpperEdgeReselection.one
      swap01ChangedInput.generatedPulledRouteTransport).toUpperEdgeReselection
        PUnit.unit PUnit.unit DecisionEdge.twist)

/-- The source pair used by the changed C2 construction is exactly the C1s
inverse image fixed in Cycle 28. -/
theorem swap01ChangedComparatorSourcePair_eq :
    (swap01ChangedInput.sourceTransport.comparator DecisionCell.comparison,
      swap01ChangedInput.sourceTransport.comparator DecisionCell.comparison) =
      swap01ChangedPositiveSourcePair := by
  apply (swap01SourcePresentationChange.generatedSourcePairMulEquivAt
    PUnit.unit).injective
  rw [swap01ChangedPositiveSourcePair, MulEquiv.apply_symm_apply]
  apply Prod.ext <;>
    exact swap01SourcePresentationChange.generatedSourceConjugation_changedComparator
      DecisionCell.comparison

/-- The corresponding source pair with identity in the pulled coordinate is
the C1s inverse image of the old negative source pair. -/
theorem swap01ChangedComparatorIdentitySourcePair_eq :
    (swap01ChangedInput.sourceTransport.comparator DecisionCell.comparison,
      1) = swap01ChangedNegativeSourcePair := by
  apply (swap01SourcePresentationChange.generatedSourcePairMulEquivAt
    PUnit.unit).injective
  rw [swap01ChangedNegativeSourcePair, MulEquiv.apply_symm_apply]
  apply Prod.ext
  · exact swap01SourcePresentationChange.generatedSourceConjugation_changedComparator
      DecisionCell.comparison
  · exact (CompositeFiberAut.conjugationMulEquiv
      (swap01SourcePresentationChange.geometryIso PUnit.unit)).map_one

/-- The actual changed C2 positive edge value is the independently generated
C3 positive pair from Cycle 28. -/
theorem swap01ChangedC2PositiveQualifiedPair_eq :
    swap01ChangedC2PositiveQualifiedPair =
      swap01ChangedPositiveQualifiedPair := by
  rw [swap01ChangedPositiveQualifiedPair_eq_generatedComparisonPairHomAt]
  rw [← swap01ChangedComparatorSourcePair_eq]
  rfl

/-- The actual changed C2 negative edge value is the independently generated
C3 negative pair from Cycle 28. -/
theorem swap01ChangedC2NegativeQualifiedPair_eq :
    swap01ChangedC2NegativeQualifiedPair =
      swap01ChangedNegativeQualifiedPair := by
  rw [swap01ChangedNegativeQualifiedPair_eq_generatedComparisonPairHomAt]
  rw [← swap01ChangedComparatorIdentitySourcePair_eq]
  apply Prod.ext
  · rfl
  · change 1 = swap01ChangedInput.generatedPulledCompositeFiberAutAt
      PUnit.unit 1
    exact (swap01ChangedInput.generatedPulledCompositeFiberAutAt_one
      PUnit.unit).symm

/-- The independently regenerated changed C2 pair satisfies endpoint
intertwining at every edge. -/
theorem swap01ChangedComparatorEndpointIntertwining_fires :
    CoefficientTrivialUpperReselectionEndpointIntertwining
      swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution
      swap01ChangedBaseComparatorReselection
      swap01ChangedPulledComparatorReselection :=
  swap01ChangedInput.sourceCoefficientTrivialUpperEdgeReselection_generated_endpointIntertwining
    swap01ChangedSourceComparatorReselection

/-- The changed source comparator family supplies the actual reselected path
triangle. -/
theorem swap01ChangedComparatorPathLegTriangle :
    ReselectedPathLegTriangle
      swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution
      swap01ChangedBaseComparatorReselection
      swap01ChangedPulledComparatorReselection :=
  swap01ChangedInput.sourceCoefficientTrivialUpperEdgeReselection_generatedPath_legTriangle
    swap01ChangedSourceComparatorReselection

/-- The same independently generated family preserves authored-comparator
pasting. -/
theorem swap01ChangedComparatorAuthoredPasting :
    ReselectedAuthoredComparatorPasting
      swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution
      swap01ChangedBaseComparatorReselection
      swap01ChangedPulledComparatorReselection :=
  swap01ChangedInput.sourceCoefficientTrivialUpperEdgeReselection_generatedAuthoredComparator_pasting
    swap01ChangedSourceComparatorReselection

/-- The changed comparator family supplies the complete paired reselection
relation. -/
theorem swap01ChangedComparatorPaired :
    PairedCoefficientTrivialUpperReselection
      swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution
      swap01ChangedBaseComparatorReselection
      swap01ChangedPulledComparatorReselection :=
  swap01ChangedInput.sourceCoefficientTrivialUpperEdgeReselection_generatedPaired
    swap01ChangedSourceComparatorReselection

/-- The actual changed C2 family is consumed by the raw-cochain API at the
fixed comparison cell. -/
theorem swap01ChangedComparatorRawCochain_intertwining :
    (CompositeFiberAut.hom
      (upperRawDefectCochain swap01ChangedInput.generatedBaseRouteData
        swap01ChangedBaseComparatorReselection.toUpperEdgeReselection
        DecisionCell.comparison)).comp
        (swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution.component
          PUnit.unit) =
      (swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution.component
        PUnit.unit).comp
        (CompositeFiberAut.hom
          (upperRawDefectCochain swap01ChangedInput.generatedPulledRouteData
            swap01ChangedPulledComparatorReselection.toUpperEdgeReselection
            DecisionCell.comparison)) :=
  swap01ChangedInput.sourceCoefficientTrivialUpperEdgeReselection_generatedRawCochain_intertwining
    swap01ChangedSourceComparatorReselection DecisionCell.comparison

/-- The independently generated pulled family is a concrete point of the
coefficient-trivial partner torsor over the changed base family. -/
noncomputable def swap01ChangedPulledPartner :
    GeneratedCoefficientTrivialPulledPartner
      swap01ChangedInput swap01ChangedBaseComparatorReselection :=
  ⟨swap01ChangedPulledComparatorReselection,
    swap01ChangedComparatorEndpointIntertwining_fires⟩

/-- The fixed changed partner fiber is nonempty. -/
theorem swap01ChangedPulledPartner_nonempty :
    Nonempty (GeneratedCoefficientTrivialPulledPartner
      swap01ChangedInput swap01ChangedBaseComparatorReselection) :=
  ⟨swap01ChangedPulledPartner⟩

/-- The existing coefficient-trivial target-stabilizer action is free on the
fixed changed partner fiber. -/
theorem swap01ChangedPulledPartnerAction_free
    (partner : GeneratedCoefficientTrivialPulledPartner
      swap01ChangedInput swap01ChangedBaseComparatorReselection)
    {left right : GeneratedCoefficientTrivialTargetStabilizerFamily
      swap01ChangedInput}
    (equality :
      generatedCoefficientTrivialPulledPartnerAction left partner =
        generatedCoefficientTrivialPulledPartnerAction right partner) :
    left = right := by
  apply generatedCoefficientTrivialPulledPartnerAction_free partner
  exact equality

/-- The same action is transitive on the fixed changed partner fiber. -/
theorem swap01ChangedPulledPartnerAction_transitive
    (source target : GeneratedCoefficientTrivialPulledPartner
      swap01ChangedInput swap01ChangedBaseComparatorReselection) :
    ∃ stabilizer : GeneratedCoefficientTrivialTargetStabilizerFamily
        swap01ChangedInput,
      generatedCoefficientTrivialPulledPartnerAction stabilizer source = target := by
  obtain ⟨stabilizer, equality⟩ :=
    generatedCoefficientTrivialPulledPartnerAction_transitive source target
  exact ⟨stabilizer, equality⟩

/-- Hence every two fixed changed partners differ by one unique family in
the literal coefficient-trivial pulled stabilizer. -/
theorem swap01ChangedPulledPartner_existsUnique
    (source target : GeneratedCoefficientTrivialPulledPartner
      swap01ChangedInput swap01ChangedBaseComparatorReselection) :
    ∃! stabilizer : GeneratedCoefficientTrivialTargetStabilizerFamily
        swap01ChangedInput,
      generatedCoefficientTrivialPulledPartnerAction stabilizer source = target := by
  obtain ⟨stabilizer, equality, unique⟩ :=
    generatedCoefficientTrivialPulledPartner_existsUnique source target
  exact ⟨stabilizer, equality, fun other otherEquality =>
    unique other otherEquality⟩

/-- The changed C2 positive edge value is literally qualified. -/
theorem swap01ChangedC2PositiveQualifiedDecision :
    Swap01ChangedQualifiedDecision swap01ChangedC2PositiveQualifiedPair := by
  rw [swap01ChangedC2PositiveQualifiedPair_eq]
  exact swap01ChangedPositiveQualifiedDecision

/-- Replacing the changed pulled C2 value by identity is literally rejected. -/
theorem swap01ChangedC2NegativeNotQualifiedDecision :
    ¬ Swap01ChangedQualifiedDecision swap01ChangedC2NegativeQualifiedPair := by
  rw [swap01ChangedC2NegativeQualifiedPair_eq]
  exact swap01ChangedNegativeNotQualifiedDecision

/-- The actual changed C2 positive and negative edge values collide under the
complete generated-endpoint coefficient observation. -/
theorem swap01ChangedC2CoefficientObservation_positive_eq_negative :
    swap01ChangedCoefficientObservation swap01ChangedC2PositiveQualifiedPair =
      swap01ChangedCoefficientObservation swap01ChangedC2NegativeQualifiedPair := by
  rw [swap01ChangedC2PositiveQualifiedPair_eq,
    swap01ChangedC2NegativeQualifiedPair_eq]
  exact swap01ChangedCoefficientObservation_positive_eq_negative

/-- The regenerated changed base reselection is genuinely nonidentity. -/
theorem swap01ChangedBaseComparatorReselection_ne_one :
    swap01ChangedBaseComparatorReselection ≠
      CoefficientTrivialUpperEdgeReselection.one
        swap01ChangedInput.generatedBaseRouteTransport := by
  intro equality
  have edgeEquality := congrArg
    (fun reselection => reselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist) equality
  have changedBase :
      swap01ChangedInput.generatedBaseCompositeFiberAutAt PUnit.unit
          (swap01ChangedInput.sourceTransport.comparator
            DecisionCell.comparison) = 1 := by
    simpa [swap01ChangedBaseComparatorReselection,
      swap01ChangedSourceComparatorReselection,
      UpperGeometryCompatibleProblemInputData.generatedBaseOfSourceCoefficientTrivialUpperEdgeReselection]
      using edgeEquality
  have naturality :=
    swap01SourcePresentationChange.generatedBaseCompositeFiberAutAt_naturality
      PUnit.unit
      (swap01ChangedInput.sourceTransport.comparator DecisionCell.comparison)
  rw [changedBase, map_one,
    swap01SourcePresentationChange.generatedSourceConjugation_changedComparator]
      at naturality
  exact generated_base_comparator_ne_one (by
    simpa [UpperGeometryCompatibleProblemInputData.generatedBaseRouteComparator]
      using naturality.symm)

/-- The actual changed positive C2 edge pair is nonidentity already at the
generated endpoint. -/
theorem swap01ChangedC2PositiveQualifiedPair_ne_one :
    swap01ChangedC2PositiveQualifiedPair ≠ 1 := by
  intro equality
  have baseEquality := congrArg Prod.fst equality
  apply swap01ChangedBaseComparatorReselection_ne_one
  apply CoefficientTrivialUpperEdgeReselection.ext
  funext i j edge
  cases i
  cases j
  cases edge
  simpa only [swap01ChangedC2PositiveQualifiedPair, Prod.fst_one] using
    baseEquality

/-- The one-link dependent C1s chain represented by the fixed source change. -/
noncomputable def swap01SourcePresentationChain :
    UpperGeometryCompatibleSourcePresentationChange.Chain problem.data :=
  .cons swap01SourcePresentationChange (.nil swap01ChangedInput)

/-- The cast-free C1t-before/C1s/C1t-after pair equivalence for the one-link
fixed source change. -/
noncomputable def swap01MixedC1PairMulEquivAt
    {sourceDisplay targetDisplay : QualifiedComparisonDisplay}
    (before : swap01ChangedInput.QualifiedComparisonC1Chain
      PUnit.unit sourceDisplay .generated)
    (after : problem.data.QualifiedComparisonC1Chain
      PUnit.unit .generated targetDisplay) :
    swap01ChangedInput.qualifiedComparisonDisplayPairAt
        PUnit.unit sourceDisplay ≃*
      problem.data.qualifiedComparisonDisplayPairAt
        PUnit.unit targetDisplay :=
  swap01SourcePresentationChain.mixedC1sC1tPairMulEquivAt
    PUnit.unit before after

/-- The fixed mixed equivalence preserves and reflects literal qualified
membership. -/
theorem swap01MixedC1PairMulEquivAt_decision_iff
    {sourceDisplay targetDisplay : QualifiedComparisonDisplay}
    (before : swap01ChangedInput.QualifiedComparisonC1Chain
      PUnit.unit sourceDisplay .generated)
    (after : problem.data.QualifiedComparisonC1Chain
      PUnit.unit .generated targetDisplay)
    (pair : swap01ChangedInput.qualifiedComparisonDisplayPairAt
      PUnit.unit sourceDisplay) :
    problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit targetDisplay
        (swap01MixedC1PairMulEquivAt before after pair) ↔
      swap01ChangedInput.qualifiedComparisonDisplayDecisionAt
        PUnit.unit sourceDisplay pair :=
  swap01SourcePresentationChain.mixedC1sC1tPairMulEquivAt_decision_iff
    PUnit.unit before after pair

/-- The fixed mixed equivalence commutes with the complete pair coefficient
observation. -/
theorem swap01MixedC1PairMulEquivAt_observation_apply
    {sourceDisplay targetDisplay : QualifiedComparisonDisplay}
    (before : swap01ChangedInput.QualifiedComparisonC1Chain
      PUnit.unit sourceDisplay .generated)
    (after : problem.data.QualifiedComparisonC1Chain
      PUnit.unit .generated targetDisplay)
    (pair : swap01ChangedInput.qualifiedComparisonDisplayPairAt
      PUnit.unit sourceDisplay) :
    problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit targetDisplay
        (swap01MixedC1PairMulEquivAt before after pair) =
      swap01ChangedInput.qualifiedComparisonDisplayObservationAt
        PUnit.unit sourceDisplay pair :=
  swap01SourcePresentationChain.mixedC1sC1tPairMulEquivAt_observation_apply
    PUnit.unit before after pair

/-- The actual positive C2 edge pair remains nonidentity after every legal
C1t-before/C1s/C1t-after composite. -/
theorem swap01MixedC1Positive_ne_one
    {sourceDisplay targetDisplay : QualifiedComparisonDisplay}
    (before : swap01ChangedInput.QualifiedComparisonC1Chain
      PUnit.unit sourceDisplay .generated)
    (after : problem.data.QualifiedComparisonC1Chain
      PUnit.unit .generated targetDisplay) :
    swap01MixedC1PairMulEquivAt before after
        (before.pairMulEquivAt.symm
          swap01ChangedC2PositiveQualifiedPair) ≠ 1 := by
  intro equality
  have sourceIdentity :=
    (swap01MixedC1PairMulEquivAt before after).injective
      (equality.trans (map_one
        (swap01MixedC1PairMulEquivAt before after)).symm)
  have generatedIdentity := congrArg before.pairMulEquivAt sourceIdentity
  simp only [MulEquiv.apply_symm_apply, map_one] at generatedIdentity
  exact swap01ChangedC2PositiveQualifiedPair_ne_one generatedIdentity

/-- For every legal C1t-before and C1t-after chain, the actual changed C2
positive and negative edge values pull back to a coefficient-indistinguishable
decision split, so the mixed C1s/C1t decision still cannot factor through the
complete coefficient observation. -/
theorem swap01ChangedC2_not_factor_after_mixed_c1
    {sourceDisplay targetDisplay : QualifiedComparisonDisplay}
    (before : swap01ChangedInput.QualifiedComparisonC1Chain
      PUnit.unit sourceDisplay .generated)
    (after : problem.data.QualifiedComparisonC1Chain
      PUnit.unit .generated targetDisplay) :
    let positiveSource := before.pairMulEquivAt.symm
      swap01ChangedC2PositiveQualifiedPair
    let negativeSource := before.pairMulEquivAt.symm
      swap01ChangedC2NegativeQualifiedPair
    let positive := swap01MixedC1PairMulEquivAt before after positiveSource
    let negative := swap01MixedC1PairMulEquivAt before after negativeSource
    problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit
        targetDisplay positive =
      problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit
        targetDisplay negative ∧
    problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit
        targetDisplay positive ∧
    ¬ problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit
        targetDisplay negative ∧
    positive ≠ 1 ∧
    ¬ ∃ diagnostic :
        (Aut (CommRingCat.of Int) × Aut (CommRingCat.of Int)) → Prop,
      ∀ pair : problem.data.qualifiedComparisonDisplayPairAt
          PUnit.unit targetDisplay,
        problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit
            targetDisplay pair ↔
          diagnostic
            (problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit
              targetDisplay pair) := by
  dsimp only
  have positiveSource :
      swap01ChangedInput.qualifiedComparisonDisplayDecisionAt PUnit.unit
        sourceDisplay
        (before.pairMulEquivAt.symm
          swap01ChangedC2PositiveQualifiedPair) := by
    apply (before.decision_iff _).mp
    rw [MulEquiv.apply_symm_apply]
    exact swap01ChangedC2PositiveQualifiedDecision
  have negativeSource :
      ¬ swap01ChangedInput.qualifiedComparisonDisplayDecisionAt PUnit.unit
        sourceDisplay
        (before.pairMulEquivAt.symm
          swap01ChangedC2NegativeQualifiedPair) := by
    apply (before.decision_iff _).not.mp
    rw [MulEquiv.apply_symm_apply]
    exact swap01ChangedC2NegativeNotQualifiedDecision
  have positive :=
    (swap01MixedC1PairMulEquivAt_decision_iff before after _).mpr
      positiveSource
  have negative :=
    (swap01MixedC1PairMulEquivAt_decision_iff before after _).not.mpr
      negativeSource
  have nonidentity := swap01MixedC1Positive_ne_one before after
  have collision :
      problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit
          targetDisplay
          (swap01MixedC1PairMulEquivAt before after
            (before.pairMulEquivAt.symm
              swap01ChangedC2PositiveQualifiedPair)) =
        problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit
          targetDisplay
          (swap01MixedC1PairMulEquivAt before after
            (before.pairMulEquivAt.symm
              swap01ChangedC2NegativeQualifiedPair)) := by
    rw [swap01MixedC1PairMulEquivAt_observation_apply,
      swap01MixedC1PairMulEquivAt_observation_apply]
    rw [← before.observation_apply, ← before.observation_apply]
    simp only [MulEquiv.apply_symm_apply]
    exact swap01ChangedC2CoefficientObservation_positive_eq_negative
  refine ⟨collision, positive, negative, nonidentity, ?_⟩
  rintro ⟨diagnostic, factors⟩
  have positiveObserved := (factors _).mp positive
  have negativeObserved := (factors _).mpr (collision ▸ positiveObserved)
  exact negative negativeObserved

/-- The changed canonical endpoint is sent forward to its generated endpoint
before the source change. -/
noncomputable def swap01ChangedCanonicalToGeneratedChain :
    swap01ChangedInput.QualifiedComparisonC1Chain PUnit.unit
      .canonical .generated :=
  .cons .forward (.nil .generated)

/-- After the source change, the old generated endpoint is sent backward to
the canonical-authored display. -/
noncomputable def swap01OldGeneratedToCanonicalChain :
    problem.data.QualifiedComparisonC1Chain PUnit.unit
      .generated .canonical :=
  .cons .backward (.nil .canonical)

/-- The explicit positive changed C2 pair after forward C1t, C1s, and inverse
C1t. -/
noncomputable def swap01ChangedC2CanonicalMixedPositivePair :
    problem.data.qualifiedComparisonDisplayPairAt PUnit.unit .canonical :=
  swap01MixedC1PairMulEquivAt swap01ChangedCanonicalToGeneratedChain
      swap01OldGeneratedToCanonicalChain
    (swap01ChangedCanonicalToGeneratedChain.pairMulEquivAt.symm
      swap01ChangedC2PositiveQualifiedPair)

/-- The corresponding pulled-identity negative pair in the same canonical
display. -/
noncomputable def swap01ChangedC2CanonicalMixedNegativePair :
    problem.data.qualifiedComparisonDisplayPairAt PUnit.unit .canonical :=
  swap01MixedC1PairMulEquivAt swap01ChangedCanonicalToGeneratedChain
      swap01OldGeneratedToCanonicalChain
    (swap01ChangedCanonicalToGeneratedChain.pairMulEquivAt.symm
      swap01ChangedC2NegativeQualifiedPair)

/-- The mandatory fixed inverse-display instance retains the positive and
negative decision split, coefficient collision, positive nonidentity, and
universal information loss. -/
theorem swap01ChangedC2CanonicalMixed_packet :
    problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit .canonical
        swap01ChangedC2CanonicalMixedPositivePair =
      problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit .canonical
        swap01ChangedC2CanonicalMixedNegativePair ∧
    problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit .canonical
        swap01ChangedC2CanonicalMixedPositivePair ∧
    ¬ problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit .canonical
        swap01ChangedC2CanonicalMixedNegativePair ∧
    swap01ChangedC2CanonicalMixedPositivePair ≠ 1 ∧
    ¬ ∃ diagnostic :
        (Aut (CommRingCat.of Int) × Aut (CommRingCat.of Int)) → Prop,
      ∀ pair : problem.data.qualifiedComparisonDisplayPairAt
          PUnit.unit .canonical,
        problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit
            .canonical pair ↔
          diagnostic
            (problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit
              .canonical pair) := by
  simpa only [swap01ChangedC2CanonicalMixedPositivePair,
    swap01ChangedC2CanonicalMixedNegativePair] using
    (swap01ChangedC2_not_factor_after_mixed_c1
      swap01ChangedCanonicalToGeneratedChain
      swap01OldGeneratedToCanonicalChain)

/-- Cycle 29 acceptance packet: actual changed-input C2 provenance, its
nonidentity firing and downstream laws, the fixed partner torsor, and mixed
C1t-before/C1s/C1t-after information loss. -/
theorem swap01ChangedC2_mixed_transport_packet :
    swap01ChangedC2PositiveQualifiedPair =
        swap01ChangedPositiveQualifiedPair ∧
      swap01ChangedC2NegativeQualifiedPair =
        swap01ChangedNegativeQualifiedPair ∧
      CoefficientTrivialUpperReselectionEndpointIntertwining
        swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution
        swap01ChangedBaseComparatorReselection
        swap01ChangedPulledComparatorReselection ∧
      ReselectedPathLegTriangle
        swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution
        swap01ChangedBaseComparatorReselection
        swap01ChangedPulledComparatorReselection ∧
      ReselectedAuthoredComparatorPasting
        swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution
        swap01ChangedBaseComparatorReselection
        swap01ChangedPulledComparatorReselection ∧
      PairedCoefficientTrivialUpperReselection
        swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution
        swap01ChangedBaseComparatorReselection
        swap01ChangedPulledComparatorReselection ∧
      (CompositeFiberAut.hom
        (upperRawDefectCochain swap01ChangedInput.generatedBaseRouteData
          swap01ChangedBaseComparatorReselection.toUpperEdgeReselection
          DecisionCell.comparison)).comp
          (swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution.component
            PUnit.unit) =
        (swap01ChangedInput.generatedGeometryCompatibleUpperRefinementBCSolution.component
          PUnit.unit).comp
          (CompositeFiberAut.hom
            (upperRawDefectCochain swap01ChangedInput.generatedPulledRouteData
              swap01ChangedPulledComparatorReselection.toUpperEdgeReselection
              DecisionCell.comparison)) ∧
      swap01ChangedBaseComparatorReselection ≠
        CoefficientTrivialUpperEdgeReselection.one
          swap01ChangedInput.generatedBaseRouteTransport ∧
      Swap01ChangedQualifiedDecision swap01ChangedC2PositiveQualifiedPair ∧
      ¬ Swap01ChangedQualifiedDecision swap01ChangedC2NegativeQualifiedPair ∧
      Nonempty (GeneratedCoefficientTrivialPulledPartner
        swap01ChangedInput swap01ChangedBaseComparatorReselection) ∧
      ∀ source target : GeneratedCoefficientTrivialPulledPartner
          swap01ChangedInput swap01ChangedBaseComparatorReselection,
        ∃! stabilizer : GeneratedCoefficientTrivialTargetStabilizerFamily
            swap01ChangedInput,
          generatedCoefficientTrivialPulledPartnerAction stabilizer source =
            target := by
  exact ⟨swap01ChangedC2PositiveQualifiedPair_eq,
    swap01ChangedC2NegativeQualifiedPair_eq,
    swap01ChangedComparatorEndpointIntertwining_fires,
    swap01ChangedComparatorPathLegTriangle,
    swap01ChangedComparatorAuthoredPasting,
    swap01ChangedComparatorPaired,
    swap01ChangedComparatorRawCochain_intertwining,
    swap01ChangedBaseComparatorReselection_ne_one,
    swap01ChangedC2PositiveQualifiedDecision,
    swap01ChangedC2NegativeNotQualifiedDecision,
    swap01ChangedPulledPartner_nonempty,
    swap01ChangedPulledPartner_existsUnique⟩

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
