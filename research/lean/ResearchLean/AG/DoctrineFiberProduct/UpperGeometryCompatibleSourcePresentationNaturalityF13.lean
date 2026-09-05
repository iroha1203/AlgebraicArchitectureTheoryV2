import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF12
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonTransportClosure

/-!
# Typed C1s/C1t integration

This module fixes the type-correct order for mixing a dependent source-change
chain C1s with the existing canonical/generated endpoint-display chains C1t.
A terminal-input C1t chain first reaches the terminal generated display, the
pasted C1s endpoint action then reaches the initial generated display, and an
initial-input C1t chain finally reaches the selected initial display.

The same order connects the terminal generated comparison map to C3, full
qualified membership, its exact residual-subgroup reflection criterion,
coefficient observation, and the independently generated range.  Core types
use `chain.composite.changedInput` rather than inserting dependent casts to
the propositionally equal `chain.terminalInput`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleSourcePresentationChange.Chain

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- G-118 C1s/C1t mixed raw-pair equivalence in the only cast-free order:
terminal C1t, pasted C1s endpoint action, then initial C1t. -/
noncomputable def mixedC1sC1tPairMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {sourceDisplay targetDisplay :
      UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (before : chain.composite.changedInput.QualifiedComparisonC1Chain
      i sourceDisplay .generated)
    (after : input.QualifiedComparisonC1Chain
      i .generated targetDisplay) :
    chain.composite.changedInput.qualifiedComparisonDisplayPairAt
        i sourceDisplay ≃*
      input.qualifiedComparisonDisplayPairAt i targetDisplay :=
  before.pairMulEquivAt.trans
    ((chain.pastedEndpointPairMulEquivAt i).trans after.pairMulEquivAt)

/-- The mixed pair equivalence applies the terminal C1t chain, then C1s,
then the initial C1t chain. -/
@[simp] theorem mixedC1sC1tPairMulEquivAt_apply
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {sourceDisplay targetDisplay :
      UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (before : chain.composite.changedInput.QualifiedComparisonC1Chain
      i sourceDisplay .generated)
    (after : input.QualifiedComparisonC1Chain
      i .generated targetDisplay)
    (pair : chain.composite.changedInput.qualifiedComparisonDisplayPairAt
      i sourceDisplay) :
    chain.mixedC1sC1tPairMulEquivAt i before after pair =
      after.pairMulEquivAt
        (chain.pastedEndpointPairMulEquivAt i
          (before.pairMulEquivAt pair)) := by
  rfl

/-- With identity C1t chains on both sides, the mixed equivalence is exactly
the pasted C1s generated-endpoint action. -/
theorem mixedC1sC1tPairMulEquivAt_generated_generated
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.mixedC1sC1tPairMulEquivAt i
        (.nil .generated) (.nil .generated) =
      chain.pastedEndpointPairMulEquivAt i := by
  apply MulEquiv.ext
  intro pair
  rfl

/-- Every type-correct C1t-before/C1s/C1t-after composite preserves and
reflects literal qualified membership. -/
theorem mixedC1sC1tPairMulEquivAt_decision_iff
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {sourceDisplay targetDisplay :
      UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (before : chain.composite.changedInput.QualifiedComparisonC1Chain
      i sourceDisplay .generated)
    (after : input.QualifiedComparisonC1Chain
      i .generated targetDisplay)
    (pair : chain.composite.changedInput.qualifiedComparisonDisplayPairAt
      i sourceDisplay) :
    input.qualifiedComparisonDisplayDecisionAt i targetDisplay
        (chain.mixedC1sC1tPairMulEquivAt i before after pair) ↔
      chain.composite.changedInput.qualifiedComparisonDisplayDecisionAt
        i sourceDisplay pair := by
  exact (after.decision_iff _).trans
    ((chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
      i (before.pairMulEquivAt pair)).symm.trans (before.decision_iff pair))

/-- Every type-correct C1t-before/C1s/C1t-after composite commutes with the
complete pair coefficient observation. -/
theorem mixedC1sC1tPairMulEquivAt_observation_apply
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {sourceDisplay targetDisplay :
      UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (before : chain.composite.changedInput.QualifiedComparisonC1Chain
      i sourceDisplay .generated)
    (after : input.QualifiedComparisonC1Chain
      i .generated targetDisplay)
    (pair : chain.composite.changedInput.qualifiedComparisonDisplayPairAt
      i sourceDisplay) :
    input.qualifiedComparisonDisplayObservationAt i targetDisplay
        (chain.mixedC1sC1tPairMulEquivAt i before after pair) =
      chain.composite.changedInput.qualifiedComparisonDisplayObservationAt
        i sourceDisplay pair := by
  exact (after.observation_apply _).trans
    ((chain.pastedEndpointPairMulEquivAt_coefficientObservation
      i (before.pairMulEquivAt pair)).trans (before.observation_apply pair))

/-- G-118 `C1s ; C3 ; C1t`: generate the terminal endpoint pair, transport
it by the pasted C1s endpoint action, and postcompose by an initial C1t chain. -/
noncomputable def c1sC3C1tPairHomAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {display : UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (after : input.QualifiedComparisonC1Chain i .generated display) :
    (CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package ×
      CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package) →*
      input.qualifiedComparisonDisplayPairAt i display :=
  after.pairMulEquivAt.toMonoidHom.comp
    ((chain.pastedEndpointPairMulEquivAt i).toMonoidHom.comp
      (chain.composite.changedInput.generatedComparisonPairHomAt i))

/-- The mixed C3 map is definitionally the three-stage source-to-display
route. -/
@[simp] theorem c1sC3C1tPairHomAt_apply
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {display : UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (after : input.QualifiedComparisonC1Chain i .generated display)
    (pair : CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package ×
      CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package) :
    chain.c1sC3C1tPairHomAt i after pair =
      after.pairMulEquivAt
        (chain.pastedEndpointPairMulEquivAt i
          (chain.composite.changedInput.generatedComparisonPairHomAt i pair)) := by
  rfl

/-- Central C1s naturality rewrites the mixed map as initial C3 applied after
the actual pasted source action, followed by the same C1t chain. -/
theorem c1sC3C1tPairHomAt_source_route
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {display : UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (after : input.QualifiedComparisonC1Chain i .generated display)
    (pair : CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package ×
      CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package) :
    chain.c1sC3C1tPairHomAt i after pair =
      after.pairMulEquivAt
        (input.generatedComparisonPairHomAt i
          (chain.pastedSourcePairMulEquivAt i pair)) := by
  rw [c1sC3C1tPairHomAt_apply,
    chain.pastedEndpointPairMulEquivAt_generatedComparisonPairHomAt]

/-- The mixed C1s/C3/C1t map preserves literal qualified membership. -/
theorem c1sC3C1tPairHomAt_preserves_qualifiedComparison
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {display : UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (after : input.QualifiedComparisonC1Chain i .generated display)
    {pair : CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package ×
      CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package}
    (membership : pair ∈ qualifiedComparisonSubgroup
      (𝟙 (chain.composite.changedInput.sourceGeometry i).package)) :
    input.qualifiedComparisonDisplayDecisionAt i display
      (chain.c1sC3C1tPairHomAt i after pair) := by
  apply (after.decision_iff _).2
  apply (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
    i _).mp
  exact UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt_preserves_qualifiedComparison
    chain.composite.changedInput i membership

/-- Exact reflection for every mixed C1s/C3/C1t display is equivalent to the
initial residual criterion, hence also to the terminal criterion by F12. -/
theorem c1sC3C1tPairHomAt_reflects_qualifiedComparison_iff
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {display : UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (after : input.QualifiedComparisonC1Chain i .generated display) :
    (∀ pair : CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package ×
        CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package,
      input.qualifiedComparisonDisplayDecisionAt i display
          (chain.c1sC3C1tPairHomAt i after pair) →
        pair ∈ qualifiedComparisonSubgroup
          (𝟙 (chain.composite.changedInput.sourceGeometry i).package)) ↔
      input.generatedPulledComparisonKernel i = ⊥ := by
  rw [← chain.generatedPulledComparisonKernel_eq_bot_pasted_iff,
    ← UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt_reflects_qualifiedComparison_iff
      chain.composite.changedInput i]
  constructor
  · intro reflects pair membership
    apply reflects pair
    apply (after.decision_iff _).2
    apply (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
      i _).mp
    exact membership
  · intro reflects pair membership
    apply reflects pair
    apply (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
      i _).mpr
    exact (after.decision_iff _).1 membership

/-- The mixed C1s/C3/C1t map commutes with complete coefficient observation
through both the C1t chain and the actual pasted source action. -/
theorem c1sC3C1tPairHomAt_coefficientObservation
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {display : UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (after : input.QualifiedComparisonC1Chain i .generated display)
    (pair : CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package ×
      CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package) :
    input.qualifiedComparisonDisplayObservationAt i display
        (chain.c1sC3C1tPairHomAt i after pair) =
      chain.composite.changedInput.sourcePairCoefficientObservationAt i pair := by
  rw [chain.c1sC3C1tPairHomAt_source_route]
  exact (input.closedComparisonPairHomAt_coefficientObservation i after
    (chain.pastedSourcePairMulEquivAt i pair)).trans
      (chain.pastedSourcePairMulEquivAt_coefficientObservation i pair)

/-- The image of the mixed C1s/C3/C1t map is exactly the initial generated
range transported through the selected initial C1t chain. -/
theorem c1sC3C1tPairHomAt_range
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    {display : UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (after : input.QualifiedComparisonC1Chain i .generated display) :
    Set.range (chain.c1sC3C1tPairHomAt i after) =
      after.pairMulEquivAt ''
        Set.range (input.generatedComparisonPairHomAt i) := by
  apply Set.ext
  intro endpointPair
  constructor
  · rintro ⟨sourcePair, rfl⟩
    refine ⟨input.generatedComparisonPairHomAt i
        (chain.pastedSourcePairMulEquivAt i sourcePair), ?_, ?_⟩
    · exact ⟨chain.pastedSourcePairMulEquivAt i sourcePair, rfl⟩
    · exact (chain.c1sC3C1tPairHomAt_source_route i after sourcePair).symm
  · rintro ⟨generatedPair, ⟨sourcePair, rfl⟩, rfl⟩
    let terminalPair :=
      (chain.pastedSourcePairMulEquivAt i).symm sourcePair
    refine ⟨terminalPair, ?_⟩
    rw [chain.c1sC3C1tPairHomAt_source_route]
    simp only [terminalPair, MulEquiv.apply_symm_apply]

end UpperGeometryCompatibleSourcePresentationChange.Chain
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
