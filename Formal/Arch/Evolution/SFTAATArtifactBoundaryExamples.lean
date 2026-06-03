import Formal.Arch.Evolution.SFTAATFundamentalModularityExamples
import Formal.Arch.Evolution.SFTArtifactBoundaryBridge
import Formal.Arch.Observation.AtomPresentation
import Formal.Arch.Observation.ArchMap
import Formal.Arch.Examples.AtomFoundationExamples

/-!
Selected finite artifact-boundary examples for AAT-supported SFT.

The examples reuse the canonical finite SFT model and route an ArchMap
preservation package plus an ArchSig report boundary through the
AAT-supported Grand Theorem package.  The artifact inputs remain boundary
evidence; they are not read as extractor completeness, calibrated forecasts, or
global software claims.
-/

namespace Formal.Arch
namespace SFTAATFundamentalModularity
namespace Examples

open SFTFundamentalModularity

universe u v w q r s t

def artifactSoftwareField :
    SoftwareField Unit Unit Unit Unit Unit Unit where
  state := ()
  architectureProjection := {
    static := { edge := fun _ _ => False }
    runtime := { edge := fun _ _ => False }
    projection := { expose := fun _ => () }
    abstractStatic := { edge := fun _ _ => False }
    staticObservation := { observe := fun _ => () }
    boundaryAllowed := fun _ _ => True
    abstractionAllowed := fun _ _ => True
    runtimeAllowed := fun _ _ => True
    semantic := { eval := fun _ => () }
    requiredSemantic := fun _ => False
    measuredSemantic := []
  }
  observedSignatureRecord := True
  historyBoundary := True
  operationSupportBoundary := True
  operationPolicyBoundary := True
  constraintEnvironmentBoundary := True
  observationModelBoundary := True
  governanceInterventionBoundary := True
  exogenousArtifactInputBoundary := True
  fieldBoundary := True
  nonConclusions := True

def artifactSoftwareFieldEstimate :
    SoftwareFieldEstimate Unit Unit Unit Unit Unit Unit where
  field := artifactSoftwareField
  coverageAssumptions := True
  observationBoundary := True
  reconstructionBoundary := True
  estimatorBoundary := True
  missingEvidence := True
  nonConclusions := True

def artifactArchSigReport :
    ArchSigSFTReport Unit Unit Unit Unit Unit Unit where
  selectedEstimate := artifactSoftwareFieldEstimate
  actionClassCandidates := True
  targetRegions := True
  candidateOperationFamilies := True
  comparableSignatureAxes := True
  coverageAssumptions := True
  observationBoundary := True
  reconstructionBoundary := True
  missingInvariants := True
  unmeasuredAxes := True
  theoremBoundary := True
  forecastBoundary := True
  reportBoundary := True
  nonConclusions := True

def artifactArchSigEstimateBoundary :
    ArchSigSFTReportEstimateBoundary artifactArchSigReport
      artifactSoftwareFieldEstimate canonicalForecastStatus where
  reportSelectsEstimate := rfl
  preservesCoverageAssumptions := fun _ => trivial
  preservesObservationBoundary := fun _ => trivial
  preservesReconstructionBoundary := fun _ => trivial
  preservesMissingInvariants := fun _ => trivial
  preservesUnmeasuredAxes := fun _ => trivial
  preservesTheoremBoundary := fun _ => trivial
  preservesForecastBoundary := fun _ => trivial
  recordsReportBoundary := fun _ => trivial
  recordsNonConclusions := fun _ => ⟨⟨trivial, trivial⟩, trivial⟩

def artifactDerivedReportBoundary :
    ArchSigDerivedSFTReportBoundary artifactArchSigReport
      artifactSoftwareFieldEstimate canonicalForecastStatus where
  boundary := artifactArchSigEstimateBoundary
  recordsObservationBoundary := trivial
  recordsReconstructionBoundary := trivial
  recordsMissingInvariants := trivial
  recordsTheoremBoundary := trivial
  recordsForecastBoundary := trivial
  recordsReportBoundary := trivial
  recordsNonConclusions := trivial

def artifactAtomPresentation :
    Observation.AtomPresentation
      AtomFoundationExamples.exampleAtomAxiomSystem Unit where
  rawCandidate := fun _ => False
  observed := fun _ => True
  validated := fun _ => True
  rejected := fun _ => False
  uncertain := fun _ => False
  missing := fun _ => False
  validationBoundary := True
  rawCandidateIsNotAtomTruth := True
  rawCandidateIsNotAtomTruthEvidence := trivial
  rejectedIsNotMeasuredZero := True
  rejectedIsNotMeasuredZeroEvidence := trivial
  uncertainIsNotMeasuredZero := True
  uncertainIsNotMeasuredZeroEvidence := trivial
  missingIsNotMeasuredZero := True
  missingIsNotMeasuredZeroEvidence := trivial
  missingIsNotAtomAbsence := True
  missingIsNotAtomAbsenceEvidence := trivial
  nonConclusions := True

def artifactArchMapObservationLayer :
    Observation.ArchMapObservationLayer
      AtomFoundationExamples.exampleAtomAxiomSystem Unit Unit where
  presentation := artifactAtomPresentation
  selectedSource := fun _ => True
  observesAtoms := True
  observesAtomsEvidence := trivial
  archMapDoesNotCreateAtomsEvidence :=
    AtomFoundationExamples.exampleAtomAxiomSystem_observation_boundary_does_not_create_atoms
  archMapDoesNotDefineAAT := True
  archMapDoesNotDefineAATEvidence := trivial
  rawCandidateBoundary := True
  validationBoundary := True
  coverageBoundary := True
  exactnessBoundary := True
  nonConclusions := True

def artifactArchMapAATSliceBoundary :
    AATSelectedArchitectureSlice.ArchMapDerivedAATSliceBoundary
      artifactArchMapObservationLayer where
  recordsProjectionBoundary := trivial
  recordsObservationBoundary := ⟨trivial, trivial⟩
  recordsReconstructionBoundary := trivial
  recordsMissingEvidence := trivial
  recordsNonConclusions := ⟨trivial, trivial⟩

def canonicalArtifactSupportedBoundary :
    AATSupportedSFTBoundary canonicalExactModel () 1 :=
  AATSupportedSFTBoundary.ofArchMapAndArchSigBoundaries
    (exactModel := canonicalExactModel) (source := ()) (horizon := 1)
    artifactArchMapAATSliceBoundary artifactDerivedReportBoundary
    canonicalInterfaceBoundary
    True True
    canonicalExactModel_recordsFiniteModelBoundary
    canonicalExactModel_recordsExactCoverBoundary
    canonicalExactModel_recordsObservationBoundary
    True True True

theorem canonicalArtifactSupportedBoundary_records_artifact_slice :
    canonicalArtifactSupportedBoundary.RecordsAATSliceBoundaries :=
  canonicalArtifactSupportedBoundary.records_projection_observation_reconstruction_missingEvidence

theorem canonicalArtifactSupportedBoundary_records_report_boundary :
    canonicalArtifactSupportedBoundary.archSigReportBoundary := by
  change canonicalForecastStatus.RecordsToolingBoundary
  exact artifactDerivedReportBoundary.report_boundary_remains_toolingBoundary

theorem canonicalArtifactSupportedBoundary_preserves_nonConclusions :
    canonicalArtifactSupportedBoundary.RecordsNonConclusions := by
  exact canonicalArtifactSupportedBoundary.preserves_nonConclusions
    trivial
    (AATSelectedArchitectureSlice.archMap_preserves_nonConclusions
      artifactArchMapAATSliceBoundary)
    trivial canonicalExactModel_recordsNonConclusions

def canonicalArtifactSupportedFundamentalModularityPackage :
    AATSupportedFundamentalModularityPackage canonicalExactModel () 1 :=
  AATSupportedFundamentalModularityPackage.ofBoundaryAndFiniteSelectedHypotheses
    (exactModel := canonicalExactModel) (source := ()) (horizon := 1)
    canonicalArtifactSupportedBoundary
    canonicalFundamentalModularityHypotheses
    canonicalExactModel_recordsGovernanceBoundary
    trivial trivial
    canonicalArtifactSupportedBoundary_records_report_boundary
    trivial trivial trivial
    (AATSelectedArchitectureSlice.archMap_preserves_nonConclusions
      artifactArchMapAATSliceBoundary)
    trivial canonicalExactModel_recordsNonConclusions trivial

theorem canonicalArtifactSupported_final_typed_conclusion :
    canonicalArtifactSupportedFundamentalModularityPackage.AATSupportedFinalTypedConclusion :=
  canonicalArtifactSupportedFundamentalModularityPackage.governed_or_finite_failure_or_aat_boundary_failure

theorem canonicalArtifactSupported_preserves_nonConclusions :
    canonicalArtifactSupportedFundamentalModularityPackage.boundary.RecordsNonConclusions ∧
      canonicalArtifactSupportedFundamentalModularityPackage.finalPackage.RecordsNonConclusions :=
  canonicalArtifactSupportedFundamentalModularityPackage.does_not_promote_to_unconditional_claim

end Examples
end SFTAATFundamentalModularity
end Formal.Arch
