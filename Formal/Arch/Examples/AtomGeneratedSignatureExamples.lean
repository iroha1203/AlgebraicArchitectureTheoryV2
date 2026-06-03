import Formal.Arch.AAT.GeneratedAnalyticRepresentation
import Formal.Arch.AAT.GeneratedFeatureExtension
import Formal.Arch.AAT.GeneratedSFT
import Formal.Arch.Examples.AtomGeneratedMoleculeExamples

namespace Formal.Arch.AtomGeneratedSignatureExamples

open Formal.Arch.AtomGeneratedMoleculeExamples

/--
Positive acceptance: source-like AtomShape facts generate a compatible molecule.

This theorem starts from the generated molecule example rather than a
hand-authored `Molecule`.
-/
def atomGeneratedSignature_hasGeneratedMolecule :
    AAT.GeneratedMolecule componentShapePresentation :=
  generatedComponentMolecule

/--
Positive acceptance: the generated architecture object is built from the
generated molecule, not from a supplied graph.
-/
def atomGeneratedSignature_hasGeneratedObject :
    AAT.GeneratedArchitectureObject componentShapePresentation :=
  generatedComponentObject

/--
Positive acceptance: the generated law model is the source of the legacy
`ArchitectureLawModel` bridge.
-/
def atomGeneratedSignature_generatesArchitectureLawModel :
    ArchitectureSignature.ArchitectureLawModel
      (AAT.GeneratedCarrier generatedComponentObject)
      (AAT.GeneratedCarrier generatedComponentObject)
      AAT.GeneratedObservationCoordinate :=
  generatedComponentLawModel.toArchitectureLawModel

/--
Positive acceptance: required Signature axes are derived for the generated
law model.
-/
theorem atomGeneratedSignature_requiredAxesZero :
    ArchitectureSignature.RequiredSignatureAxesZero
      (generatedComponentLawModel.signatureOfGenerated) := by
  exact generatedComponentLawModel.generated_requiredSignatureAxesZero

/--
Positive acceptance: generated lawfulness is equivalent to generated required
Signature axes being zero.
-/
theorem atomGeneratedSignature_lawful_iff_requiredAxesZero :
    ArchitectureSignature.ArchitectureLawful
        generatedComponentLawModel.toArchitectureLawModel ↔
      ArchitectureSignature.RequiredSignatureAxesZero
        (generatedComponentLawModel.signatureOfGenerated) := by
  exact generatedComponentLawModel.generatedArchitectureLawful_iff_requiredSignatureAxesZero

/--
Positive acceptance: the generated signature theorem uses the generated law
model directly and does not require an `architectureLawfulFromAAT` field.
-/
theorem atomGeneratedSignature_architectureLawful :
    ArchitectureSignature.ArchitectureLawful
      generatedComponentLawModel.toArchitectureLawModel := by
  exact generatedComponentLawModel.generatedArchitectureLawful

/--
Positive acceptance: generated law models have a generated analytic
representation into Signature v1.
-/
noncomputable def atomGeneratedSignature_analyticRepresentation :
    AnalyticRepresentation
      (AAT.GeneratedArchitectureLawModel generatedComponentObject)
      ArchitectureSignature.ArchitectureSignatureV1
      AAT.GeneratedAnalyticWitness :=
  AAT.GeneratedArchitectureLawModel.generatedAnalyticRepresentation
    (object := generatedComponentObject)

theorem atomGeneratedSignature_analytic_zeroPreserving :
    AnalyticRepresentation.ZeroPreserving
      atomGeneratedSignature_analyticRepresentation := by
  exact
    AAT.GeneratedArchitectureLawModel.generatedAnalyticRepresentation_zeroPreserving
      (object := generatedComponentObject)

theorem atomGeneratedSignature_analytic_zero :
    atomGeneratedSignature_analyticRepresentation.analyticZero
      (atomGeneratedSignature_analyticRepresentation.represent
        generatedComponentLawModel) := by
  exact
    AnalyticRepresentation.analyticZero_of_structuralZero
      atomGeneratedSignature_analyticRepresentation
      atomGeneratedSignature_analytic_zeroPreserving
      generatedComponentLawModel.generatedArchitectureLawful

theorem atomGeneratedSignature_analytic_zeroReflecting :
    AnalyticRepresentation.ZeroReflecting
      atomGeneratedSignature_analyticRepresentation := by
  exact
    AAT.GeneratedArchitectureLawModel.generatedAnalyticRepresentation_zeroReflecting
      (object := generatedComponentObject)

/--
Positive acceptance: generated law models also trigger the existing bounded
feature-extension flatness theorem through a generated identity feature
extension.
-/
theorem atomGeneratedSignature_featureExtension_flatWithin :
    ArchitectureFlatWithin
      generatedComponentObject.generatedIdentityExtensionFlatnessModel
      generatedComponentObject.generatedIdentityExtensionComponentUniverse := by
  exact generatedComponentLawModel.generatedFeatureExtension_architectureFlatWithin

/--
Positive acceptance: the generated Signature theorem package is available as
SFT input without becoming a forecast-correctness theorem.
-/
noncomputable def atomGeneratedSignature_sftInput :
    AAT.GeneratedSFTInput generatedComponentLawModel where
  theoremStatus :=
    generatedComponentLawModel.generatedAATTheoremStatusForSFT
      True True True True True
  theoremStatusFromGenerated :=
    generatedComponentLawModel.generatedAATTheoremStatusForSFT_recordsTheoremPackage
  sftReadsGeneratedAAT := True
  sftReadsGeneratedAATEvidence := trivial
  sftDoesNotRedefineAtoms := True
  sftDoesNotRedefineAtomsEvidence := trivial
  sftDoesNotRedefineAAT := True
  sftDoesNotRedefineAATEvidence := trivial
  forecastCorrectnessBoundary := True
  forecastCorrectnessBoundaryEvidence := trivial
  sftEventDoesNotCreateAtomsEvidence :=
    componentSystem.sft_event_does_not_create_atoms
  nonConclusions := True

theorem atomGeneratedSignature_sft_reads_generated_aat :
    atomGeneratedSignature_sftInput.sftReadsGeneratedAAT := by
  exact atomGeneratedSignature_sftInput.reads_generated_aat

theorem atomGeneratedSignature_sft_forecast_correctness_boundary :
    atomGeneratedSignature_sftInput.forecastCorrectnessBoundary := by
  exact atomGeneratedSignature_sftInput.forecast_correctness_remains_boundary

end Formal.Arch.AtomGeneratedSignatureExamples
