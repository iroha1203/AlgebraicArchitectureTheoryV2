import Formal.Arch.Evolution.SFTTheoremRoadmap
import Formal.Arch.Evolution.SFTDescentObstruction

/-!
Final conservative assembly surface for the SFT roadmap.

This module does not prove an assumption-free Fundamental Modularity Theorem.
It packages the selected theorem-family components into a checked final
assembly: under explicit descent, obstruction, review, governance,
calibration, and confluence assumptions, bounded selected evolution is governed
or exposes a typed boundary failure.
-/

namespace Formal.Arch
namespace SFTFundamentalModularity

universe u v w x y z

/-- Docs-facing outcome vocabulary for the final conservative assembly. -/
inductive FundamentalEvolutionOutcome where
  | computablyGoverned
  | typedBoundaryFailure
  deriving DecidableEq, Repr

/-- Typed boundary-failure classes exposed by the final assembly. -/
inductive FundamentalBoundaryFailureKind where
  | descentFailure
  | obstructionUnclassified
  | governanceUncut
  | reviewEnvelopeMissing
  | calibrationBoundaryExpanded
  | agenticConfluenceMissing
  | theoremFamilyAssumptionMissing
  deriving DecidableEq, Repr

/-- A typed computation-boundary failure witness for the final conclusion. -/
structure TypedComputationBoundaryFailure where
  kind : FundamentalBoundaryFailureKind
  explainsBrokenBoundary : Prop
  evidenceBoundary : Prop
  nonConclusions : Prop

/-- Positive side of the governed-or-typed-failure conclusion. -/
structure ComputablyGoverned where
  descentAvailable : Prop
  obstructionHandled : Prop
  minimalEnvelopeAvailable : Prop
  governanceCutsBad : Prop
  closedLoopSettles : Prop
  agenticConfluenceAvailable : Prop
  governedBoundary : Prop
  nonConclusions : Prop

namespace ComputablyGoverned

/-- The governed package records selected governance cutting. -/
theorem computablyGoverned_records_governance
    (governed : ComputablyGoverned)
    (hGovernance : governed.governanceCutsBad) :
    governed.governanceCutsBad :=
  hGovernance

/-- The governed package records selected ForecastCone descent availability. -/
theorem computablyGoverned_records_descent
    (governed : ComputablyGoverned)
    (hDescent : governed.descentAvailable) :
    governed.descentAvailable :=
  hDescent

/-- The governed package records selected agentic confluence availability. -/
theorem computablyGoverned_records_agentic
    (governed : ComputablyGoverned)
    (hAgentic : governed.agenticConfluenceAvailable) :
    governed.agenticConfluenceAvailable :=
  hAgentic

end ComputablyGoverned

/-- Final assembly descent component. -/
structure FundamentalDescentComponent where
  modularityAsDescent : Prop
  forecastConeDescent : Prop
  modularity_iff_descent :
    modularityAsDescent ↔ forecastConeDescent
  descentBoundary : Prop
  nonConclusions : Prop

/-- Final assembly obstruction component. -/
structure FundamentalObstructionComponent where
  technicalDebtAsObstruction : Prop
  typedFailureWitnessAvailable : Prop
  obstructionBoundary : Prop
  nonConclusions : Prop

/-- Final assembly review / minimal-envelope component. -/
structure FundamentalReviewComponent where
  minimalDecisionPreservingEnvelope : Prop
  reviewBoundary : Prop
  nonConclusions : Prop

/-- Final assembly governance component. -/
structure FundamentalGovernanceComponent where
  governanceAsObstructionCutting : Prop
  selectedBadWitnessesCut : Prop
  desiredFamiliesPreserved : Prop
  governanceBoundary : Prop
  nonConclusions : Prop

/-- Final assembly calibration component. -/
structure FundamentalCalibrationComponent where
  boundaryExplicitFixedPoint : Prop
  fixedPointOrBoundaryExpansion : Prop
  calibrationBoundary : Prop
  nonConclusions : Prop

/-- Final assembly agentic-confluence component. -/
structure FundamentalAgenticComponent where
  agenticConfluence : Prop
  fairInterleavingsConverge : Prop
  agentBoundary : Prop
  nonConclusions : Prop

/--
Turn final assembly components into the existing roadmap conclusion shape.

The governed/failure disjunction is still an explicit hypothesis; this bridge
does not prove classifier completeness or governance effectiveness.
-/
def toRoadmapConclusion
    (descent : FundamentalDescentComponent)
    (obstruction : FundamentalObstructionComponent)
    (review : FundamentalReviewComponent)
    (governance : FundamentalGovernanceComponent)
    (calibration : FundamentalCalibrationComponent)
    (agentic : FundamentalAgenticComponent)
    (governed : ComputablyGoverned)
    (failure : TypedComputationBoundaryFailure)
    (hOutcome :
      governed.governedBoundary ∨ failure.explainsBrokenBoundary) :
    SFTTheoremRoadmap.FundamentalModularityConclusion where
  modularityAsDescent := descent.modularityAsDescent
  technicalDebtAsObstruction := obstruction.technicalDebtAsObstruction
  reviewAsMinimalEnvelope := review.minimalDecisionPreservingEnvelope
  governanceAsObstructionCutting :=
    governance.governanceAsObstructionCutting
  learningAsBoundaryExplicitFixedPoint :=
    calibration.boundaryExplicitFixedPoint
  computablyGoverned := governed.governedBoundary
  typedBoundaryFailureWitness := failure.explainsBrokenBoundary
  governed_or_failure := hOutcome
  nonConclusions :=
    descent.nonConclusions ∧ obstruction.nonConclusions ∧
      review.nonConclusions ∧ governance.nonConclusions ∧
        calibration.nonConclusions ∧ agentic.nonConclusions ∧
          governed.nonConclusions ∧ failure.nonConclusions

/-- Hypotheses for the final conservative Fundamental Modularity assembly. -/
structure FundamentalModularityHypotheses where
  descent : FundamentalDescentComponent
  obstruction : FundamentalObstructionComponent
  review : FundamentalReviewComponent
  governance : FundamentalGovernanceComponent
  calibration : FundamentalCalibrationComponent
  agentic : FundamentalAgenticComponent
  governed : ComputablyGoverned
  failure : TypedComputationBoundaryFailure
  hModularity :
    descent.modularityAsDescent
  hDebt :
    obstruction.technicalDebtAsObstruction
  hReview :
    review.minimalDecisionPreservingEnvelope
  hGovernance :
    governance.governanceAsObstructionCutting
  hLearning :
    calibration.boundaryExplicitFixedPoint
  hAgentic :
    agentic.agenticConfluence
  hAgenticAvailable :
    agentic.agenticConfluence -> governed.agenticConfluenceAvailable
  governed_or_failure :
    governed.governedBoundary ∨ failure.explainsBrokenBoundary
  theoremBoundary : Prop
  nonConclusions : Prop

/-- Roadmap conclusion assembled from final hypotheses. -/
def roadmapConclusion_of_hypotheses
    (h : FundamentalModularityHypotheses) :
    SFTTheoremRoadmap.FundamentalModularityConclusion :=
  toRoadmapConclusion h.descent h.obstruction h.review h.governance
    h.calibration h.agentic h.governed h.failure h.governed_or_failure

/-- Roadmap grand theorem package assembled from final hypotheses. -/
def roadmapPackage_of_hypotheses
    (h : FundamentalModularityHypotheses) :
    SFTTheoremRoadmap.FundamentalModularityTheoremPackage :=
  SFTTheoremRoadmap.FundamentalModularityTheoremPackage.ofTheoremFamily
    (roadmapConclusion_of_hypotheses h)
    h.hModularity
    h.hDebt
    h.hReview
    h.hGovernance
    h.hLearning
    h.theoremBoundary

/-- Final conservative assembly theorem for the SFT theorem family. -/
theorem fundamental_modularity_final_assembly
    (h : FundamentalModularityHypotheses) :
    h.descent.modularityAsDescent ∧
      h.obstruction.technicalDebtAsObstruction ∧
      h.review.minimalDecisionPreservingEnvelope ∧
      h.governance.governanceAsObstructionCutting ∧
      h.calibration.boundaryExplicitFixedPoint ∧
      h.agentic.agenticConfluence ∧
      (h.governed.governedBoundary ∨
        h.failure.explainsBrokenBoundary) :=
  ⟨h.hModularity, h.hDebt, h.hReview, h.hGovernance, h.hLearning,
    h.hAgentic, h.governed_or_failure⟩

/-- Final accessor: selected agentic confluence is part of the assembly hypotheses. -/
theorem final_agentic_confluence
    (h : FundamentalModularityHypotheses) :
    h.agentic.agenticConfluence :=
  h.hAgentic

/--
Final accessor: the governed-side package records the selected agentic
confluence component through the assembly bridge.
-/
theorem final_governed_agenticConfluenceAvailable
    (h : FundamentalModularityHypotheses) :
    h.governed.agenticConfluenceAvailable :=
  h.hAgenticAvailable h.hAgentic

/-- Final accessor: selected bounded evolution is governed or has typed failure. -/
theorem final_bounded_evolution_governed_or_typed_failure
    (h : FundamentalModularityHypotheses) :
    h.governed.governedBoundary ∨ h.failure.explainsBrokenBoundary :=
  h.governed_or_failure

/-- Final accessor: the assembled roadmap package records modularity as descent. -/
theorem final_modularity_iff_forecastConeDescent
    (h : FundamentalModularityHypotheses) :
    (roadmapPackage_of_hypotheses h).modularity ↔
      (roadmapPackage_of_hypotheses h).forecastConeDescent :=
  SFTTheoremRoadmap.FundamentalModularityTheoremPackage.fundamental_modularity
    (roadmapPackage_of_hypotheses h)

/-- Read finite obstruction-governance cutting as the final governance component. -/
def governanceComponent_of_finiteObstructionGovernance
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteObstructionGovernancePackage model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (_hBadClassified :
      ∀ witness,
        package.obstructionPackage.classifier.classify failure =
          some witness ->
        package.governancePackage.target.bad witness) :
    FundamentalGovernanceComponent where
  governanceAsObstructionCutting :=
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      package.obstructionPackage.classifier.classify failure = some witness ∧
        package.governancePackage.cutsBad
          package.governancePackage.selectedIntervention witness
  selectedBadWitnessesCut :=
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      package.obstructionPackage.classifier.classify failure = some witness ∧
        package.governancePackage.cutsBad
          package.governancePackage.selectedIntervention witness
  desiredFamiliesPreserved :=
    ∀ family : FiniteLocalClockedConeFamily cover model source horizon,
      package.governancePackage.target.desiredPreserved family ->
        package.governancePackage.preservesDesired
          package.governancePackage.selectedIntervention family
  governanceBoundary := package.obstructionToGovernanceBoundary
  nonConclusions := package.nonConclusions

/-- The finite obstruction-governance component records the selected cut. -/
theorem governanceComponent_records_finite_cut
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteObstructionGovernancePackage model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hBadClassified :
      ∀ witness,
        package.obstructionPackage.classifier.classify failure =
          some witness ->
        package.governancePackage.target.bad witness) :
    (governanceComponent_of_finiteObstructionGovernance
      package failure hBadClassified).governanceAsObstructionCutting :=
  governance_cuts_obstruction_of_finite_failure
    package failure hBadClassified

/-- The finite obstruction-governance component records desired preservation. -/
theorem governanceComponent_records_desired_preservation
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteObstructionGovernancePackage model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hBadClassified :
      ∀ witness,
        package.obstructionPackage.classifier.classify failure =
          some witness ->
        package.governancePackage.target.bad witness) :
    (governanceComponent_of_finiteObstructionGovernance
      package failure hBadClassified).desiredFamiliesPreserved :=
  fun family hDesired =>
    finite_governance_preserves_desired_family
      package.governancePackage family hDesired

/-- Read a minimal consequence-envelope package as the final review component. -/
def reviewComponent_of_minimalEnvelopePackage
    {ConePath : Type u} {MinimalEnvelope : Type v}
    (package :
      SFTTheoremRoadmap.MinimalConsequenceEnvelopePackage.{u, v, w}
        ConePath MinimalEnvelope) :
    FundamentalReviewComponent where
  minimalDecisionPreservingEnvelope :=
    ∀ (OtherEnvelope : Type w)
      (otherProjection : ConePath -> OtherEnvelope),
      SFTTheoremRoadmap.DecisionSoundProjection
        package.reviewEquivalent otherProjection ->
        ∃ factor : MinimalEnvelope -> OtherEnvelope,
          ∀ path, factor (package.projection path) = otherProjection path
  reviewBoundary := package.envelopeBoundary
  nonConclusions := package.nonConclusions

/-- The review component exposes the selected minimal-envelope universal property. -/
theorem reviewComponent_records_minimalEnvelope
    {ConePath : Type u} {MinimalEnvelope : Type v}
    (package :
      SFTTheoremRoadmap.MinimalConsequenceEnvelopePackage.{u, v, w}
        ConePath MinimalEnvelope) :
    (reviewComponent_of_minimalEnvelopePackage
      package).minimalDecisionPreservingEnvelope :=
  fun _OtherEnvelope otherProjection hSound =>
    SFTTheoremRoadmap.MinimalConsequenceEnvelopePackage.minimal_consequenceEnvelope_factors
      package otherProjection hSound

/-- Read closed-loop calibration package data as the final calibration component. -/
def calibrationComponent_of_closedLoopPackage
    {Estimate : Type u} {update : Estimate -> Estimate}
    (package :
      SFTTheoremRoadmap.ClosedLoopCalibrationPackage Estimate update)
    (_hMonotone : package.monotone)
    (_hEvidence : package.evidencePreserving)
    (_hBoundary : package.boundaryExplicit)
    (_hNonConclusion : package.nonConclusionPreserving)
    (_hError : package.forecastErrorRefining)
    (initial : Estimate) :
    FundamentalCalibrationComponent where
  boundaryExplicitFixedPoint := package.boundaryExplicit
  fixedPointOrBoundaryExpansion :=
    SFTTheoremRoadmap.EventuallyFixedOrBoundary update
      package.boundaryExpansionRequirement initial
  calibrationBoundary := package.calibrationBoundary
  nonConclusions := package.nonConclusions

/-- The calibration component records fixed point or boundary expansion. -/
theorem calibrationComponent_records_fixedPointOrBoundary
    {Estimate : Type u} {update : Estimate -> Estimate}
    (package :
      SFTTheoremRoadmap.ClosedLoopCalibrationPackage Estimate update)
    (hMonotone : package.monotone)
    (hEvidence : package.evidencePreserving)
    (hBoundary : package.boundaryExplicit)
    (hNonConclusion : package.nonConclusionPreserving)
    (hError : package.forecastErrorRefining)
    (initial : Estimate) :
    (calibrationComponent_of_closedLoopPackage package hMonotone hEvidence
      hBoundary hNonConclusion hError initial).fixedPointOrBoundaryExpansion :=
  SFTTheoremRoadmap.ClosedLoopCalibrationPackage.closedLoop_calibration_fixedPoint_or_boundary
    package hMonotone hEvidence hBoundary hNonConclusion hError initial

/-- Read agentic confluence package data as the final agentic component. -/
def agenticComponent_of_agenticConfluencePackage
    {Interleaving : Type u} {ConeQuotient : Type v}
    (package :
      SFTTheoremRoadmap.AgenticConfluencePackage
        Interleaving ConeQuotient)
    (_hTermination : package.localTermination)
    (_hConfluence : package.localConfluence)
    (_hDescent : package.forecastConeDescent)
    (_hInterface : package.interfaceConstraintsPreserved)
    (_hPolicy : package.policiesCommutationInvariant) :
    FundamentalAgenticComponent where
  agenticConfluence :=
    SFTTheoremRoadmap.FairInterleavingsConverge package.landing
  fairInterleavingsConverge :=
    SFTTheoremRoadmap.FairInterleavingsConverge package.landing
  agentBoundary := package.agentBoundary
  nonConclusions := package.nonConclusions

/-- The agentic component records the selected agentic confluence conclusion. -/
theorem agenticComponent_records_agenticConfluence
    {Interleaving : Type u} {ConeQuotient : Type v}
    (package :
      SFTTheoremRoadmap.AgenticConfluencePackage
        Interleaving ConeQuotient)
    (hTermination : package.localTermination)
    (hConfluence : package.localConfluence)
    (hDescent : package.forecastConeDescent)
    (hInterface : package.interfaceConstraintsPreserved)
    (hPolicy : package.policiesCommutationInvariant) :
    (agenticComponent_of_agenticConfluencePackage
      package hTermination hConfluence hDescent hInterface hPolicy).agenticConfluence :=
  SFTTheoremRoadmap.AgenticConfluencePackage.agentic_confluence
    package hTermination hConfluence hDescent hInterface hPolicy

/-- The agentic component records selected confluence of fair interleavings. -/
theorem agenticComponent_records_confluence
    {Interleaving : Type u} {ConeQuotient : Type v}
    (package :
      SFTTheoremRoadmap.AgenticConfluencePackage
        Interleaving ConeQuotient)
    (hTermination : package.localTermination)
    (hConfluence : package.localConfluence)
    (hDescent : package.forecastConeDescent)
    (hInterface : package.interfaceConstraintsPreserved)
    (hPolicy : package.policiesCommutationInvariant) :
    (agenticComponent_of_agenticConfluencePackage
      package hTermination hConfluence hDescent hInterface hPolicy).fairInterleavingsConverge :=
  agenticComponent_records_agenticConfluence
    package hTermination hConfluence hDescent hInterface hPolicy

end SFTFundamentalModularity
end Formal.Arch
