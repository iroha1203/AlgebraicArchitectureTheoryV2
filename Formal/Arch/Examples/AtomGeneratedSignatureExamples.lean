import Formal.Arch.AAT.GeneratedAnalyticRepresentation
import Formal.Arch.AAT.GeneratedFeatureExtension
import Formal.Arch.AAT.GeneratedSFT
import Formal.Arch.Evolution.Chapter7TheoremPackages
import Formal.Arch.Evolution.Chapter10ArchitectureExtensionFormula
import Formal.Arch.Evolution.Chapter11AnalyticRepresentation
import Formal.Arch.Evolution.SFTArchSigBoundary
import Formal.Arch.Examples.AtomGeneratedMoleculeExamples
import Formal.Arch.Signature.AATCoreBridge

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
Positive acceptance: the AATCore-to-Signature bridge is built from the generated
law model without supplying an `architectureLawfulFromAAT` field.
-/
noncomputable def atomGeneratedSignature_coreSignatureBridge :
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge
      generatedComponentLawModel.generatedAATCore
      generatedComponentLawModel.toArchitectureLawModel :=
  ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel
    generatedComponentLawModel True True True True True True
    trivial trivial trivial

theorem atomGeneratedSignature_coreSignatureBridge_architectureLawful :
    ArchitectureSignature.ArchitectureLawful
      generatedComponentLawModel.toArchitectureLawModel := by
  exact
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge.architectureLawful
      atomGeneratedSignature_coreSignatureBridge

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
    Formal.Arch.Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroPreserving
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
    Formal.Arch.Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroReflecting
      (object := generatedComponentObject)

theorem atomGeneratedSignature_analytic_obstructionPreserving :
    AnalyticRepresentation.ObstructionPreserving
      atomGeneratedSignature_analyticRepresentation := by
  exact
    Formal.Arch.Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionPreserving
      (object := generatedComponentObject)

theorem atomGeneratedSignature_analytic_obstructionReflecting :
    AnalyticRepresentation.ObstructionReflecting
      atomGeneratedSignature_analyticRepresentation := by
  exact
    Formal.Arch.Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionReflecting
      (object := generatedComponentObject)

theorem atomGeneratedSignature_analytic_nonConclusions :
    atomGeneratedSignature_analyticRepresentation.nonConclusions := by
  exact
    Formal.Arch.Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_nonConclusions
      (object := generatedComponentObject)

theorem atomGeneratedSignature_analytic_represent_eq_signatureOfGenerated :
    atomGeneratedSignature_analyticRepresentation.represent
        generatedComponentLawModel =
      generatedComponentLawModel.signatureOfGenerated := by
  exact
    Formal.Arch.Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_represent_eq_signatureOfGenerated
      generatedComponentLawModel

/--
Positive acceptance: generated law models also trigger the existing bounded
feature-extension flatness theorem through a generated identity feature
extension.
-/
theorem atomGeneratedSignature_featureExtension_flatWithin :
    ArchitectureFlatWithin
      generatedComponentObject.generatedIdentityExtensionFlatnessModel
      generatedComponentObject.generatedIdentityExtensionComponentUniverse := by
  exact
    Formal.Arch.Chapter7TheoremPackages.generatedSplitFeatureExtension_flatWithin
      generatedComponentLawModel

def atomGeneratedSignature_extensionWitness :
    ExtensionObstructionWitness
      generatedComponentObject.generatedIdentityFeatureExtension Unit where
  witness := ()
  classifiesAs := ExtensionObstructionClass.residualCoverageGap

theorem atomGeneratedSignature_extensionFormula_structural :
    ClassifiedAsInheritedCore
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness ∨
      ClassifiedAsFeatureLocal
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness ∨
      ClassifiedAsInteraction
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness ∨
      ClassifiedAsLiftingFailure
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness ∨
      ClassifiedAsFillingFailure
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness ∨
      ClassifiedAsComplexityTransfer
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness ∨
      ClassifiedAsResidualCoverageGap
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness := by
  exact
    Formal.Arch.Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_structural
      generatedComponentObject atomGeneratedSignature_extensionWitness

theorem atomGeneratedSignature_extensionFormula_multilabel_structural :
    MultiLabelClassifiedAsInheritedCore
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness.toMultiLabel ∨
      MultiLabelClassifiedAsFeatureLocal
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness.toMultiLabel ∨
      MultiLabelClassifiedAsInteraction
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness.toMultiLabel ∨
      MultiLabelClassifiedAsLiftingFailure
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness.toMultiLabel ∨
      MultiLabelClassifiedAsFillingFailure
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness.toMultiLabel ∨
      MultiLabelClassifiedAsComplexityTransfer
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness.toMultiLabel ∨
      MultiLabelClassifiedAsResidualCoverageGap
        generatedComponentObject.generatedIdentityFeatureExtension
        generatedComponentObject.generatedIdentityExtensionComponentUniverse
        atomGeneratedSignature_extensionWitness.toMultiLabel := by
  exact
    Formal.Arch.Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_multilabel_structural
      generatedComponentObject atomGeneratedSignature_extensionWitness.toMultiLabel

/--
Positive acceptance: the generated Signature theorem package is available as
SFT input without becoming a forecast-correctness theorem.
-/
noncomputable def atomGeneratedSignature_sftInput :
    AAT.GeneratedSFTInput generatedComponentLawModel where
  theoremBoundary := True
  unmeasuredAxisBoundary := True
  toolingBoundary := True
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

theorem atomGeneratedSignature_sft_theoremStatusFromGenerated :
    atomGeneratedSignature_sftInput.theoremStatus.RecordsTheoremPackage := by
  exact atomGeneratedSignature_sftInput.theoremStatusFromGenerated

theorem atomGeneratedSignature_sft_measuredZeroFromGenerated :
    atomGeneratedSignature_sftInput.theoremStatus.RecordsMeasuredZeroEvidence := by
  exact atomGeneratedSignature_sftInput.measured_zero_from_generated

theorem atomGeneratedSignature_sft_reads_generated_aat :
    atomGeneratedSignature_sftInput.sftReadsGeneratedAAT := by
  exact atomGeneratedSignature_sftInput.reads_generated_aat

theorem atomGeneratedSignature_sft_forecast_correctness_boundary :
    atomGeneratedSignature_sftInput.forecastCorrectnessBoundary := by
  exact atomGeneratedSignature_sftInput.forecast_correctness_remains_boundary

noncomputable def atomGeneratedSignature_sftForecastStatus :
    SFTForecastStatus where
  localPremise := True
  supportBoundary := True
  trajectorySafetyBoundary := True
  measuredAxisBoundary := True
  unmeasuredAxisBoundary := True
  theoremBoundary := True
  toolingBoundary := True
  forecastBoundary := True
  nonConclusions := True

noncomputable def atomGeneratedSignature_sftInterfaceBoundary :
    AATToSFTInterfaceBoundary
      atomGeneratedSignature_sftInput.theoremStatus
      atomGeneratedSignature_sftForecastStatus where
  readsAATAsLocalPremise := by
    intro _hGeneratedStatus
    trivial
  preservesAATTheoremBoundary := by
    intro _hTheoremBoundary
    trivial
  preservesMeasuredAxisBoundary := by
    intro _hMeasured
    trivial
  preservesUnmeasuredAxisBoundary := by
    intro _hUnmeasured
    trivial
  preservesToolingBoundary := by
    intro _hTooling
    trivial
  recordsSupportBoundary := trivial
  recordsTrajectorySafetyBoundary := trivial
  recordsForecastBoundary := trivial
  recordsNonConclusions := by
    intro _hNonConclusions
    trivial

theorem atomGeneratedSignature_sft_localPremiseFromGenerated :
    atomGeneratedSignature_sftForecastStatus.RecordsLocalPremise := by
  exact
    atomGeneratedSignature_sftInput.reads_generated_aat_as_sft_local_premise
      atomGeneratedSignature_sftInterfaceBoundary

/--
Positive acceptance: the generated law model supplies an AATCore transition
without a hand-authored `ArchitectureLawModel` or Signature bridge.
-/
def atomGeneratedSignature_operationPreservation :
    AAT.OperationPreservationPackage
      generatedComponentLawModel.generatedAATCore
      generatedComponentLawModel.generatedAATCore where
  selectedMolecule := generatedComponentLawModel.requiredGeneratedMolecule
  selectedLaw := fun law => law = generatedComponentLawModel.generatedDesignLaw
  preservesMolecule := by
    intro _molecule _hSelected hSource
    exact hSource
  preservesLaw := by
    intro _law _hSelected hSource
    exact hSource
  operationDoesNotCreateAtomsEvidence :=
    componentSystem.tool_output_does_not_create_atoms
  operationBoundary := True
  theoremPackageBoundary := True
  nonConclusions := True

def atomGeneratedSignature_atomDelta :
    AATCoreAtomDelta
      generatedComponentLawModel.generatedAATCore
      generatedComponentLawModel.generatedAATCore where
  sourceAtom := generatedComponentMolecule.atoms
  targetAtom := generatedComponentMolecule.atoms
  preservedAtom := generatedComponentMolecule.atoms
  transformedAtom := fun source target => source = target
  sourceAtomPrimitive := by
    intro atom hAtom
    exact generatedComponentMolecule.atoms_primitive hAtom
  targetAtomPrimitive := by
    intro atom hAtom
    exact generatedComponentMolecule.atoms_primitive hAtom
  preservedAtomOnSource := by
    intro _atom hAtom
    exact hAtom
  preservedAtomOnTarget := by
    intro _atom hAtom
    exact hAtom
  transitionBoundary := True
  doesNotCreateAtomsEvidence :=
    componentSystem.sft_event_does_not_create_atoms
  nonConclusions := True

def atomGeneratedSignature_semanticDelta :
    AATCoreSemanticDelta atomGeneratedSignature_atomDelta where
  semanticAtom := generatedComponentMolecule.atoms
  sourceSemanticAtomsPrimitive := by
    intro atom _hSource hSemantic
    exact generatedComponentMolecule.atoms_primitive hSemantic
  targetSemanticAtomsPrimitive := by
    intro atom _hTarget hSemantic
    exact generatedComponentMolecule.atoms_primitive hSemantic
  semanticBoundary := True
  doesNotCreateAtomsEvidence :=
    componentSystem.sft_event_does_not_create_atoms
  nonConclusions := True

def atomGeneratedSignature_circuitDelta :
    AATCoreCircuitDelta
      generatedComponentLawModel.generatedAATCore
      generatedComponentLawModel.generatedAATCore where
  law := generatedComponentLawModel.generatedDesignLaw
  molecule := generatedComponentObject.molecule.toMolecule
  lawOnSource := generatedComponentLawModel.generated_law_on_core
  lawOnTarget := generatedComponentLawModel.generated_law_on_core
  moleculeOnSource := generatedComponentLawModel.generated_molecule_on_core
  moleculeOnTarget := generatedComponentLawModel.generated_molecule_on_core
  createdCircuit := fun _ => False
  removedCircuit := fun _ => False
  preservedCircuit := fun _ => True
  circuitBoundary := True
  doesNotCreateAtomsEvidence :=
    componentSystem.sft_event_does_not_create_atoms
  nonConclusions := True

def atomGeneratedSignature_aatCoreTransition :
    AATCoreTransition
      generatedComponentLawModel.generatedAATCore
      generatedComponentLawModel.generatedAATCore where
  operationPackage := atomGeneratedSignature_operationPreservation
  atomDelta := atomGeneratedSignature_atomDelta
  semanticDelta := atomGeneratedSignature_semanticDelta
  circuitDelta := atomGeneratedSignature_circuitDelta
  transitionBoundary := True
  fieldSigBoundary := True
  nonConclusions := True

theorem atomGeneratedSignature_transition_does_not_create_atoms :
    componentSystem.noToolOutputCreatesAtoms := by
  exact atomGeneratedSignature_aatCoreTransition.operation_does_not_create_atoms

noncomputable def atomGeneratedSignature_generatedArchSigTransition :
    GeneratedArchSigAATCoreTransition
      generatedComponentLawModel
      generatedComponentLawModel where
  transition := atomGeneratedSignature_aatCoreTransition
  analyzesUsingAAT := True
  analyzesUsingAATEvidence := trivial
  transitionBoundary := True
  transitionBoundaryEvidence := trivial
  archsigDoesNotDefineAAT := True
  archsigDoesNotDefineAATEvidence := trivial
  fieldSigAnalysisBoundary := True
  fieldSigAnalysisBoundaryEvidence := trivial
  unknownRejectedUnmeasuredSeparated := True
  unknownRejectedUnmeasuredSeparatedEvidence := trivial
  measuredZeroBoundary := True
  validationIsNotTheoremDischarge := True
  nonConclusions := True

theorem atomGeneratedSignature_generatedArchSig_sourceLawful :
    ArchitectureSignature.ArchitectureLawful
      generatedComponentLawModel.toArchitectureLawModel := by
  exact
    atomGeneratedSignature_generatedArchSigTransition
      |>.source_bridge_architectureLawful

theorem atomGeneratedSignature_generatedArchSig_targetLawful :
    ArchitectureSignature.ArchitectureLawful
      generatedComponentLawModel.toArchitectureLawModel := by
  exact
    atomGeneratedSignature_generatedArchSigTransition
      |>.target_bridge_architectureLawful

def atomGeneratedSignature_generatedSoftwareField :
    SoftwareField
      Unit
      (AAT.GeneratedCarrier generatedComponentObject)
      (AAT.GeneratedCarrier generatedComponentObject)
      AAT.GeneratedObservationCoordinate
      (AAT.GeneratedArchitectureObject.GeneratedSemanticExpr
        generatedComponentObject)
      AAT.GeneratedObservationCoordinate where
  state := ()
  architectureProjection := generatedComponentObject.generatedFlatnessModel
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

def atomGeneratedSignature_generatedSoftwareFieldEstimate :
    SoftwareFieldEstimate
      Unit
      (AAT.GeneratedCarrier generatedComponentObject)
      (AAT.GeneratedCarrier generatedComponentObject)
      AAT.GeneratedObservationCoordinate
      (AAT.GeneratedArchitectureObject.GeneratedSemanticExpr
        generatedComponentObject)
      AAT.GeneratedObservationCoordinate where
  field := atomGeneratedSignature_generatedSoftwareField
  coverageAssumptions := True
  observationBoundary := True
  reconstructionBoundary := True
  estimatorBoundary := True
  missingEvidence := True
  nonConclusions := True

def atomGeneratedSignature_generatedArchSigSFTReport :
    ArchSigSFTReport
      Unit
      (AAT.GeneratedCarrier generatedComponentObject)
      (AAT.GeneratedCarrier generatedComponentObject)
      AAT.GeneratedObservationCoordinate
      (AAT.GeneratedArchitectureObject.GeneratedSemanticExpr
        generatedComponentObject)
      AAT.GeneratedObservationCoordinate where
  selectedEstimate := atomGeneratedSignature_generatedSoftwareFieldEstimate
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

def atomGeneratedSignature_generatedReportEstimateBoundary :
    ArchSigSFTReportEstimateBoundary
      atomGeneratedSignature_generatedArchSigSFTReport
      atomGeneratedSignature_generatedSoftwareFieldEstimate
      atomGeneratedSignature_sftForecastStatus where
  reportSelectsEstimate := rfl
  preservesCoverageAssumptions := by
    intro h
    exact h
  preservesObservationBoundary := by
    intro h
    exact h
  preservesReconstructionBoundary := by
    intro h
    exact h
  preservesMissingInvariants := by
    intro h
    exact h
  preservesUnmeasuredAxes := by
    intro h
    exact h
  preservesTheoremBoundary := by
    intro h
    exact h
  preservesForecastBoundary := by
    intro h
    exact h
  recordsReportBoundary := by
    intro h
    exact h
  recordsNonConclusions := by
    intro _h
    exact ⟨⟨trivial, trivial⟩, trivial⟩

def atomGeneratedSignature_generatedFieldSigAnalysis :
    GeneratedFieldSigAATCoreTransitionAnalysis
      atomGeneratedSignature_generatedArchSigTransition
      atomGeneratedSignature_generatedArchSigSFTReport
      atomGeneratedSignature_generatedSoftwareFieldEstimate
      atomGeneratedSignature_sftForecastStatus where
  reportBoundary := atomGeneratedSignature_generatedReportEstimateBoundary
  readsGeneratedArchSigTransitionAsSFTAnalysisEvidence := trivial
  fieldSigDoesNotDefineAATEvidence := trivial
  transitionDoesNotCreateAtoms :=
    atomGeneratedSignature_aatCoreTransition.operation_does_not_create_atoms
  forecastBoundary := trivial
  theoremBoundary := trivial
  nonConclusions := trivial

theorem atomGeneratedSignature_fieldsig_reads_generated_transition :
    atomGeneratedSignature_generatedArchSigTransition.fieldSigAnalysisBoundary := by
  exact
    atomGeneratedSignature_generatedFieldSigAnalysis
      |>.fieldsig_reads_generated_archsig_transition_as_sft_analysis

theorem atomGeneratedSignature_fieldsig_forecast_correctness_boundary :
    atomGeneratedSignature_sftForecastStatus.RecordsForecastBoundary := by
  exact
    atomGeneratedSignature_generatedFieldSigAnalysis
      |>.forecast_correctness_remains_boundary

end Formal.Arch.AtomGeneratedSignatureExamples
