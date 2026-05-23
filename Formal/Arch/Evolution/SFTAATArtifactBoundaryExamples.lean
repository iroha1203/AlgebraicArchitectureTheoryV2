import Formal.Arch.Evolution.SFTAATFundamentalModularityExamples
import Formal.Arch.Evolution.SFTArtifactBoundaryBridge

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

variable {Src : Type u} {Tgt : Type v} {Abs : Type w}
variable {StaticObs : Type q} {SrcExpr : Type r}
variable {TgtExpr : Type s} {SemanticObs : Type t}
variable {M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs}

def canonicalArtifactSupportedBoundary
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M) :
    AATSupportedSFTBoundary canonicalExactModel () 1 :=
  AATSupportedSFTBoundary.ofArchMapAndArchSigBoundaries
    (exactModel := canonicalExactModel) (source := ()) (horizon := 1)
    archMapPackage artifactDerivedReportBoundary canonicalInterfaceBoundary
    True True
    canonicalExactModel_recordsFiniteModelBoundary
    canonicalExactModel_recordsExactCoverBoundary
    canonicalExactModel_recordsObservationBoundary
    True True True

theorem canonicalArtifactSupportedBoundary_records_artifact_slice
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M) :
    (canonicalArtifactSupportedBoundary archMapPackage).RecordsAATSliceBoundaries :=
  (canonicalArtifactSupportedBoundary
    archMapPackage).records_projection_observation_reconstruction_missingEvidence

theorem canonicalArtifactSupportedBoundary_records_report_boundary
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M) :
    (canonicalArtifactSupportedBoundary archMapPackage).archSigReportBoundary :=
  artifactDerivedReportBoundary.report_boundary_remains_toolingBoundary

theorem canonicalArtifactSupportedBoundary_preserves_nonConclusions
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M) :
    (canonicalArtifactSupportedBoundary archMapPackage).RecordsNonConclusions :=
  (canonicalArtifactSupportedBoundary archMapPackage).preserves_nonConclusions
    trivial
    (AATSelectedArchitectureSlice.archMap_preserves_nonConclusions
      archMapPackage)
    trivial canonicalExactModel_recordsNonConclusions

def canonicalArtifactSupportedFundamentalModularityPackage
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M) :
    AATSupportedFundamentalModularityPackage canonicalExactModel () 1 :=
  AATSupportedFundamentalModularityPackage.ofBoundaryAndFiniteSelectedHypotheses
    (exactModel := canonicalExactModel) (source := ()) (horizon := 1)
    (canonicalArtifactSupportedBoundary archMapPackage)
    canonicalFundamentalModularityHypotheses
    canonicalExactModel_recordsGovernanceBoundary
    trivial trivial
    (canonicalArtifactSupportedBoundary_records_report_boundary archMapPackage)
    trivial trivial trivial
    (AATSelectedArchitectureSlice.archMap_preserves_nonConclusions
      archMapPackage)
    trivial canonicalExactModel_recordsNonConclusions trivial

theorem canonicalArtifactSupported_final_typed_conclusion
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M) :
    (canonicalArtifactSupportedFundamentalModularityPackage
      archMapPackage).AATSupportedFinalTypedConclusion :=
  (canonicalArtifactSupportedFundamentalModularityPackage
    archMapPackage).governed_or_finite_failure_or_aat_boundary_failure

theorem canonicalArtifactSupported_preserves_nonConclusions
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M) :
    (canonicalArtifactSupportedFundamentalModularityPackage
      archMapPackage).boundary.RecordsNonConclusions ∧
      (canonicalArtifactSupportedFundamentalModularityPackage
        archMapPackage).finalPackage.RecordsNonConclusions :=
  (canonicalArtifactSupportedFundamentalModularityPackage
    archMapPackage).does_not_promote_to_unconditional_claim

end Examples
end SFTAATFundamentalModularity
end Formal.Arch
