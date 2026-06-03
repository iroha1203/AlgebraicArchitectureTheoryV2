import Formal.Arch.Evolution.Chapter7TheoremPackages
import Formal.Arch.Evolution.Chapter8HomotopySkeleton
import Formal.Arch.Evolution.Chapter9DiagramFilling
import Formal.Arch.Evolution.Chapter10ArchitectureExtensionFormula
import Formal.Arch.Evolution.Chapter11AnalyticRepresentation
import Formal.Arch.Evolution.SFTTheoremPackages
import Formal.Arch.Observation.ArchMapGeneratedHandoff

/-!
Atom-based AAT reconstruction classification registry.

The reconstruction plan requires each theorem package to be classified as
Atom-generated, bridge-assumed, or representation-level.  This module makes
that status a Lean surface: a registry row cannot be constructed without the
evidence list required by its classification, and there is no `unclassified`
constructor.
-/

namespace Formal.Arch
namespace AATReconstructionClassification

/-- Classification required by the atom-based reconstruction plan. -/
inductive TheoremPackageClass where
  | atomGenerated
  | bridgeAssumed
  | representationLevel
  deriving DecidableEq, Repr

/-- Migration action allowed for a classified theorem package. -/
inductive ReconstructionAction where
  | aatSourceOfTruth
  | temporaryBridge
  | downstreamLibrary
  | rewriteTarget
  deriving DecidableEq, Repr

/--
Evidence required by each classification.

Atom-generated rows must name at least one generated entrypoint,
bridge-assumed rows must name the bridge assumption, and representation-level
rows must name the representation surface they remain relative to.
-/
inductive ClassificationEvidence :
    TheoremPackageClass -> List String -> List String -> List String -> Prop where
  | atomGenerated
      {generatedEntrypoints bridgeAssumptions representationEntrypoints :
        List String}
      (hGenerated : generatedEntrypoints ≠ []) :
      ClassificationEvidence .atomGenerated generatedEntrypoints
        bridgeAssumptions representationEntrypoints
  | bridgeAssumed
      {generatedEntrypoints bridgeAssumptions representationEntrypoints :
        List String}
      (hBridge : bridgeAssumptions ≠ []) :
      ClassificationEvidence .bridgeAssumed generatedEntrypoints
        bridgeAssumptions representationEntrypoints
  | representationLevel
      {generatedEntrypoints bridgeAssumptions representationEntrypoints :
        List String}
      (hRepresentation : representationEntrypoints ≠ []) :
      ClassificationEvidence .representationLevel generatedEntrypoints
        bridgeAssumptions representationEntrypoints

/-- Allowed actions for each classification. -/
inductive ActionAllowed :
    TheoremPackageClass -> ReconstructionAction -> Prop where
  | atomGeneratedSourceOfTruth :
      ActionAllowed .atomGenerated .aatSourceOfTruth
  | bridgeAssumedTemporary :
      ActionAllowed .bridgeAssumed .temporaryBridge
  | representationDownstream :
      ActionAllowed .representationLevel .downstreamLibrary
  | representationRewriteTarget :
      ActionAllowed .representationLevel .rewriteTarget

/-- A classified theorem-package registry row. -/
structure TheoremPackageClassification where
  packageId : String
  representativeDeclarations : List String
  classification : TheoremPackageClass
  generatedEntrypoints : List String
  bridgeAssumptions : List String
  representationEntrypoints : List String
  action : ReconstructionAction
  reason : String
  evidence :
    ClassificationEvidence classification generatedEntrypoints
      bridgeAssumptions representationEntrypoints
  actionEvidence : ActionAllowed classification action

namespace TheoremPackageClassification

/-- A row passes the reconstruction classification evidence check. -/
def Passes (row : TheoremPackageClassification) : Prop :=
  ClassificationEvidence row.classification row.generatedEntrypoints
    row.bridgeAssumptions row.representationEntrypoints

/-- The selected migration action is allowed for the row's classification. -/
def HasAllowedAction (row : TheoremPackageClassification) : Prop :=
  ActionAllowed row.classification row.action

theorem passes (row : TheoremPackageClassification) : row.Passes :=
  row.evidence

theorem action_allowed
    (row : TheoremPackageClassification) : row.HasAllowedAction :=
  row.actionEvidence

end TheoremPackageClassification

def atomGeneratedRow
    (packageId : String)
    (representativeDeclarations generatedEntrypoints : List String)
    (hGenerated : generatedEntrypoints ≠ [])
    (reason : String) :
    TheoremPackageClassification where
  packageId := packageId
  representativeDeclarations := representativeDeclarations
  classification := .atomGenerated
  generatedEntrypoints := generatedEntrypoints
  bridgeAssumptions := []
  representationEntrypoints := []
  action := .aatSourceOfTruth
  reason := reason
  evidence := ClassificationEvidence.atomGenerated hGenerated
  actionEvidence := ActionAllowed.atomGeneratedSourceOfTruth

def bridgeAssumedRow
    (packageId : String)
    (representativeDeclarations bridgeAssumptions : List String)
    (hBridge : bridgeAssumptions ≠ [])
    (reason : String) :
    TheoremPackageClassification where
  packageId := packageId
  representativeDeclarations := representativeDeclarations
  classification := .bridgeAssumed
  generatedEntrypoints := []
  bridgeAssumptions := bridgeAssumptions
  representationEntrypoints := []
  action := .temporaryBridge
  reason := reason
  evidence := ClassificationEvidence.bridgeAssumed hBridge
  actionEvidence := ActionAllowed.bridgeAssumedTemporary

def representationRow
    (packageId : String)
    (representativeDeclarations representationEntrypoints : List String)
    (hRepresentation : representationEntrypoints ≠ [])
    (action : ReconstructionAction)
    (hAction : ActionAllowed .representationLevel action)
    (reason : String) :
    TheoremPackageClassification where
  packageId := packageId
  representativeDeclarations := representativeDeclarations
  classification := .representationLevel
  generatedEntrypoints := []
  bridgeAssumptions := []
  representationEntrypoints := representationEntrypoints
  action := action
  reason := reason
  evidence := ClassificationEvidence.representationLevel hRepresentation
  actionEvidence := hAction

/--
Bridge surfaces that still exist as compatibility APIs, but are no longer
registered as theorem-package source rows.

This keeps the bridge assumption visible without allowing it to satisfy the
Atom-based theorem-package completion check.  Such a surface must name both
the bridge field that made it invalid as AAT source and the generated
entrypoint that replaces it.
-/
structure LegacyBridgeSurface where
  surfaceId : String
  representativeDeclarations : List String
  bridgeAssumptions : List String
  generatedReplacementEntrypoints : List String
  reason : String
  bridgeEvidence : bridgeAssumptions ≠ []
  replacementEvidence : generatedReplacementEntrypoints ≠ []

namespace LegacyBridgeSurface

def IsBridgeAssumptionSurface (surface : LegacyBridgeSurface) : Prop :=
  surface.bridgeAssumptions ≠ []

def HasGeneratedReplacement (surface : LegacyBridgeSurface) : Prop :=
  surface.generatedReplacementEntrypoints ≠ []

theorem bridge_assumption_surface
    (surface : LegacyBridgeSurface) :
    surface.IsBridgeAssumptionSurface :=
  surface.bridgeEvidence

theorem has_generated_replacement
    (surface : LegacyBridgeSurface) :
    surface.HasGeneratedReplacement :=
  surface.replacementEvidence

end LegacyBridgeSurface

def genericSignatureBridgeLegacySurface : LegacyBridgeSurface where
  surfaceId := "aat.genericSignatureBridge"
  representativeDeclarations :=
    ["ArchitectureSignature.AATCoreSignatureLawfulnessBridge",
     "ArchitectureSignature.AATCoreSignatureLawfulnessBridge.architectureLawful",
     "ArchitectureSignature.AATCoreSignatureLawfulnessBridge.requiredSignatureAxesZero"]
  bridgeAssumptions := ["architectureLawfulFromAAT"]
  generatedReplacementEntrypoints :=
    ["ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel"]
  reason :=
    "The generic bridge stores a caller-supplied lawfulness callback; the theorem-package registry uses the generated law-model constructor as the AAT source-of-truth entrypoint instead."
  bridgeEvidence := by simp
  replacementEvidence := by simp

def legacyBridgeSurfaces : List LegacyBridgeSurface :=
  [genericSignatureBridgeLegacySurface]

/-- AAT-side theorem packages not already represented by chapter candidates. -/
inductive AATCandidate where
  | finiteStaticStructuralCore
  | generatedSignatureBridge
  | atomGeneratedAlgebraKernel
  | archMapObservationBoundary
  | crossPackageSmoke
  deriving DecidableEq, Repr

namespace AATCandidate

def representativeDeclarations : AATCandidate -> List String
  | finiteStaticStructuralCore =>
      ["ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero",
       "ArchitectureSignature.architectureLawful_iff_architectureZeroCurvatureTheoremPackage",
       "ArchitectureSignature.ArchitectureLawModel.signatureOf"]
  | generatedSignatureBridge =>
      ["ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel",
       "ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel_architectureLawful",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_coreSignatureBridge"]
  | atomGeneratedAlgebraKernel =>
      ["AAT.GeneratedMolecule",
       "AAT.GeneratedArchitectureObject",
       "AAT.GeneratedArchitectureLawModel",
       "AtomGeneratedSignatureExamples.*",
       "AtomGeneratedRepairExamples.*",
       "IncompatibleAtomCompositionExamples.*"]
  | archMapObservationBoundary =>
      ["Observation.ArchMapObservationLayer",
       "Observation.ArchMapObservationLayer.archmap_does_not_create_atoms",
       "Observation.ArchMapObservationLayer.archmap_does_not_define_aat",
       "Observation.ArchMapObservedAtomSelection.toGeneratedMolecule",
       "Observation.ArchMapGeneratedArchitectureObjectInput.toGeneratedArchitectureObject"]
  | crossPackageSmoke =>
      ["AATCoreSmokeExamples.generated_transport_handoff_reads_nonidentity_transition",
       "AATCoreSmokeExamples.generated_transport_circuit_delta_keeps_source_target_surfaces"]

end AATCandidate

def classifyAATCandidate
    (candidate : AATCandidate) : TheoremPackageClassification :=
  match candidate with
  | .finiteStaticStructuralCore =>
      representationRow
        "aat.finiteStaticStructuralCore"
        (AATCandidate.representativeDeclarations
          .finiteStaticStructuralCore)
        ["ArchitectureLawModel", "ArchGraph", "Observation"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "The static Signature anchor is a representation-level theorem retained as a downstream library; generated law models invoke it through generated bridge entrypoints."
  | .generatedSignatureBridge =>
      atomGeneratedRow
        "aat.generatedSignatureBridge"
        (AATCandidate.representativeDeclarations .generatedSignatureBridge)
        ["ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel"]
        (by simp)
        "The generated constructor derives Signature lawfulness from GeneratedArchitectureLawModel and does not ask callers for architectureLawfulFromAAT."
  | .atomGeneratedAlgebraKernel =>
      atomGeneratedRow
        "aat.atomGeneratedAlgebraKernel"
        (AATCandidate.representativeDeclarations .atomGeneratedAlgebraKernel)
        ["AAT.GeneratedArchitectureObject",
         "AAT.GeneratedArchitectureLawModel",
         "AtomGeneratedSignatureExamples.*"]
        (by simp)
        "The kernel starts from AtomShape / compatible composition and reaches generated molecule, object, law model, signature, repair, and negative acceptance examples."
  | .archMapObservationBoundary =>
      atomGeneratedRow
        "aat.archMapObservationBoundary"
        (AATCandidate.representativeDeclarations .archMapObservationBoundary)
        ["Observation.ArchMapObservedAtomSelection.toGeneratedMolecule",
         "Observation.ArchMapGeneratedArchitectureObjectInput.toGeneratedArchitectureObject"]
        (by simp)
        "ArchMap remains an observation boundary outside pure AAT, but observed atoms now have a positive handoff into GeneratedMolecule and GeneratedArchitectureObject without letting ArchMap create atoms or define AAT."
  | .crossPackageSmoke =>
      atomGeneratedRow
        "aat.crossPackageSmoke"
        (AATCandidate.representativeDeclarations .crossPackageSmoke)
        ["AATCoreSmokeExamples.generated_transport_handoff_reads_nonidentity_transition"]
        (by simp)
        "The smoke examples now include a non-identity generated transport handoff and source/target transport circuit delta acceptance."

def classifyChapter7
    (candidate : Chapter7TheoremPackages.Candidate) :
    TheoremPackageClassification :=
  match candidate with
  | .splitExtensionPreservation =>
      atomGeneratedRow
        "chapter7.splitExtensionPreservation"
        (Chapter7TheoremPackages.Candidate.representativeDeclarations
          .splitExtensionPreservation)
        ["Chapter7TheoremPackages.generatedSplitFeatureExtension_flatWithin"]
        (by simp)
        "The package has generated identity feature-extension entrypoints and is read as an Atom-generated source-of-truth entry for the split-extension flatness direction."
  | .nonSplitExtensionWitness =>
      atomGeneratedRow
        "chapter7.nonSplitExtensionWitness"
        (Chapter7TheoremPackages.Candidate.representativeDeclarations
          .nonSplitExtensionWitness)
        ["Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage",
         "Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists"]
        (by simp)
        "The non-split witness package has a generated filling-failure bridge over generated diagrams and the generated identity feature extension."
  | .repairAsResplitting =>
      atomGeneratedRow
        "chapter7.repairAsResplitting"
        (Chapter7TheoremPackages.Candidate.representativeDeclarations
          .repairAsResplitting)
        ["Chapter7TheoremPackages.generatedRepairFromProblem_toRepairClearingPackage"]
        (by simp)
        "Repair is connected through generated repair targets and pre-molecule repair problems."
  | .complexityTransfer =>
      atomGeneratedRow
        "chapter7.complexityTransfer"
        (Chapter7TheoremPackages.Candidate.representativeDeclarations
          .complexityTransfer)
        ["Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
         "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_multilabel_classified"]
        (by simp)
        "Bounded complexity transfer has generated identity feature-extension entrypoints into the Architecture Extension Formula classification layer."
  | .noSolutionCertificate =>
      atomGeneratedRow
        "chapter7.noSolutionCertificate"
        (Chapter7TheoremPackages.Candidate.representativeDeclarations
          .noSolutionCertificate)
        ["Chapter7TheoremPackages.generatedSynthesisCandidate_toSynthesisSoundnessPackage"]
        (by simp)
        "Generated synthesis candidates induce the downstream synthesis soundness package."
  | .architectureEvolution =>
      atomGeneratedRow
        "chapter7.architectureEvolution"
        (Chapter7TheoremPackages.Candidate.representativeDeclarations
          .architectureEvolution)
        ["Chapter7TheoremPackages.generatedOperation_toOperationTransportPackage"]
        (by simp)
        "Generated operations expose AtomShape transformation and non-identity AATCore transport."

def classifyChapter8
    (candidate : Chapter8HomotopySkeleton.Candidate) :
    TheoremPackageClassification :=
  match candidate with
  | .architecturePaths =>
      atomGeneratedRow
        "chapter8.architecturePaths"
        (Chapter8HomotopySkeleton.Candidate.representativeDeclarations
          .architecturePaths)
        ["AAT.GeneratedArchitecturePath.preservesInvariant",
         "Chapter8HomotopySkeleton.generatedPath_preservesInvariant"]
        (by simp)
        "Path calculus has a generated relation-backed path entrypoint for invariant preservation."
  | .generatedPathHomotopy =>
      atomGeneratedRow
        "chapter8.generatedPathHomotopy"
        (Chapter8HomotopySkeleton.Candidate.representativeDeclarations
          .generatedPathHomotopy)
        ["AAT.GeneratedPathHomotopy"]
        (by simp)
        "Generated path homotopy is an Atom-generated entrypoint over generated carriers and steps."
  | .selectedObservationInvariance =>
      atomGeneratedRow
        "chapter8.selectedObservationInvariance"
        (Chapter8HomotopySkeleton.Candidate.representativeDeclarations
          .selectedObservationInvariance)
        ["Chapter8HomotopySkeleton.generatedPathHomotopy_observation_eq_append",
         "Chapter8HomotopySkeleton.generatedPathHomotopy_observation_eq"]
        (by simp)
        "Selected observation invariance has generated path-homotopy entrypoints over generated relation-backed paths."
  | .diagramFiller =>
      atomGeneratedRow
        "chapter8.diagramFiller"
        (Chapter8HomotopySkeleton.Candidate.representativeDeclarations
          .diagramFiller)
        ["AAT.GeneratedDiagramFiller",
         "Chapter8HomotopySkeleton.generatedDiagramFiller_observation_eq",
         "Chapter8HomotopySkeleton.generatedObservationDifference_refutesDiagramFiller"]
        (by simp)
        "Diagram filling has generated diagram entrypoints and generated observation-difference refutation."
  | .obstructionAsNonFillability =>
      atomGeneratedRow
        "chapter8.obstructionAsNonFillability"
        (Chapter8HomotopySkeleton.Candidate.representativeDeclarations
          .obstructionAsNonFillability)
        ["AAT.GeneratedNonFillabilityWitnessFor",
         "Chapter8HomotopySkeleton.generated_obstructionAsNonFillability_sound",
         "Chapter8HomotopySkeleton.generatedObservationDifference_nonFillabilityWitnessFor"]
        (by simp)
        "Non-fillability has generated witness entrypoints over generated diagrams and generated observation differences."

def classifyChapter9
    (candidate : Chapter9DiagramFilling.Candidate) :
    TheoremPackageClassification :=
  match candidate with
  | .diagramFillingObstruction =>
      atomGeneratedRow
        "chapter9.diagramFillingObstruction"
        (Chapter9DiagramFilling.Candidate.representativeDeclarations
          .diagramFillingObstruction)
        ["AAT.GeneratedArchitectureDiagram",
         "AAT.GeneratedDiagramFiller",
         "AAT.GeneratedNonFillabilityWitnessFor"]
        (by simp)
        "Diagram filling and non-fillability have generated diagram and generated witness entrypoints."
  | .splitExtensionLifting =>
      atomGeneratedRow
        "chapter9.splitExtensionLifting"
        (Chapter9DiagramFilling.Candidate.representativeDeclarations
          .splitExtensionLifting)
        ["Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData",
         "Chapter9DiagramFilling.generatedSelfSplitExtensionLifting_preservationPackage"]
        (by simp)
        "Split-extension lifting has a generated self-view feature extension entrypoint over generated carriers and generated lifting data."
  | .fillingFailureBridge =>
      atomGeneratedRow
        "chapter9.fillingFailureBridge"
        (Chapter9DiagramFilling.Candidate.representativeDeclarations
          .fillingFailureBridge)
        ["Chapter9DiagramFilling.generatedFillingFailureWitnessPayload",
         "Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage"]
        (by simp)
        "Filling failure is generated from GeneratedNonFillabilityWitnessFor and embedded into the generated identity extension obstruction layer."

def classifyChapter10
    (candidate : Chapter10ArchitectureExtensionFormula.Candidate) :
    TheoremPackageClassification :=
  match candidate with
  | .obstructionUniverse =>
      atomGeneratedRow
        "chapter10.obstructionUniverse"
        (Chapter10ArchitectureExtensionFormula.Candidate.representativeDeclarations
          .obstructionUniverse)
        ["Chapter10ArchitectureExtensionFormula.GeneratedExtensionObstructionWitness",
         "Chapter10ArchitectureExtensionFormula.GeneratedMultiLabelExtensionObstructionWitness",
         "Chapter10ArchitectureExtensionFormula.generatedExtensionObstructionWitness_toMultiLabel"]
        (by simp)
        "The extension-obstruction witness universe has generated identity feature-extension witness carriers and a generated single-to-multi-label bridge."
  | .nonSplitWitnessPackage =>
      atomGeneratedRow
        "chapter10.nonSplitWitnessPackage"
        (Chapter10ArchitectureExtensionFormula.Candidate.representativeDeclarations
          .nonSplitWitnessPackage)
        ["Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage",
         "Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists"]
        (by simp)
        "The non-split witness package is specialized by a generated filling-failure bridge over generated diagrams and generated identity extensions."
  | .singleLabelClassification =>
      atomGeneratedRow
        "chapter10.singleLabelClassification"
        (Chapter10ArchitectureExtensionFormula.Candidate.representativeDeclarations
          .singleLabelClassification)
        ["Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_structural"]
        (by simp)
        "The structural classification theorem fires on generated identity feature extensions."
  | .multiLabelClassification =>
      atomGeneratedRow
        "chapter10.multiLabelClassification"
        (Chapter10ArchitectureExtensionFormula.Candidate.representativeDeclarations
          .multiLabelClassification)
        ["Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_multilabel_structural"]
        (by simp)
        "The multi-label classification theorem fires on generated identity feature extensions."
  | .fillingFailureBridge =>
      atomGeneratedRow
        "chapter10.fillingFailureBridge"
        (Chapter10ArchitectureExtensionFormula.Candidate.representativeDeclarations
          .fillingFailureBridge)
        ["Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness_classified",
         "Chapter10ArchitectureExtensionFormula.generatedFillingFailureExtensionObstructionWitness_multilabel_classified"]
        (by simp)
        "Generated filling-failure payloads are classified in both single-label and multi-label extension-obstruction layers for generated identity extensions."
  | .liftingFailureBridge =>
      atomGeneratedRow
        "chapter10.liftingFailureBridge"
        (Chapter10ArchitectureExtensionFormula.Candidate.representativeDeclarations
          .liftingFailureBridge)
        ["Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitness_classified",
         "Chapter10ArchitectureExtensionFormula.generatedSelfLiftingFailureExtensionObstructionWitness_multilabel_classified"]
        (by simp)
        "Generated self-view lifting failures are classified in both single-label and multi-label extension-obstruction layers."
  | .complexityTransferBridge =>
      atomGeneratedRow
        "chapter10.complexityTransferBridge"
        (Chapter10ArchitectureExtensionFormula.Candidate.representativeDeclarations
          .complexityTransferBridge)
        ["Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_classified",
         "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
         "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_multilabel_classified"]
        (by simp)
        "Complexity-transfer witnesses classify over the generated identity feature extension."
  | .residualCoverageGapBridge =>
      atomGeneratedRow
        "chapter10.residualCoverageGapBridge"
        (Chapter10ArchitectureExtensionFormula.Candidate.representativeDeclarations
          .residualCoverageGapBridge)
        ["Chapter10ArchitectureExtensionFormula.generatedResidualCoverageGapExtensionObstructionWitness_classified",
         "Chapter10ArchitectureExtensionFormula.generatedResidualCoverageGapExtensionObstructionWitness_multilabel_classified",
         "Chapter10ArchitectureExtensionFormula.generatedIdentityExtension_noResidualCoverageGapPayload"]
        (by simp)
        "Residual-coverage diagnostics have generated identity feature-extension classification entrypoints, and generated identity coverage rules out residual-gap payloads."

def classifyChapter11
    (candidate : Chapter11AnalyticRepresentation.Candidate) :
    TheoremPackageClassification :=
  match candidate with
  | .analyticRepresentation =>
      representationRow
        "chapter11.analyticRepresentation"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .analyticRepresentation)
        ["AnalyticRepresentation"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "The generic analytic representation package is a downstream representation theorem."
  | .toolingReportMetadata =>
      representationRow
        "chapter11.toolingReportMetadata"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .toolingReportMetadata)
        ["ToolingTheoremPackageMetadata", "ClaimClassification"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Report metadata separates measurement and theorem claims; it is not an Atom-generated theorem source."
  | .architectureSignatureRepresentation =>
      atomGeneratedRow
        "chapter11.architectureSignatureRepresentation"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .architectureSignatureRepresentation)
        ["AAT.GeneratedArchitectureLawModel.generatedAnalyticRepresentation",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_represent_eq_signatureOfGenerated"]
        (by simp)
        "ArchitectureSignature representation has a generated law-model entrypoint."
  | .obstructionValuation =>
      atomGeneratedRow
        "chapter11.obstructionValuation"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .obstructionValuation)
        ["AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation",
         "AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation_value_zero",
         "AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation_noSelectedObstruction"]
        (by simp)
        "Obstruction valuation has a generated selected Signature-axis valuation over generated law models."
  | .analyticExtensionFormula =>
      atomGeneratedRow
        "chapter11.analyticExtensionFormula"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .analyticExtensionFormula)
        ["Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormulaPackage",
         "Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_formula_holds",
         "Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_obstructionValue_zero"]
        (by simp)
        "The analytic extension formula has a generated identity specialization over generated law models, generated analytic representation, and generated selected obstruction valuation."
  | .couponAnalyticSnapshot =>
      representationRow
        "chapter11.couponAnalyticSnapshot"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .couponAnalyticSnapshot)
        ["CouponAnalyticSnapshot"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Coupon snapshots are concrete representation-level counterexample fixtures."
  | .couponHiddenInteractionLiftingBridge =>
      representationRow
        "chapter11.couponHiddenInteractionLiftingBridge"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .couponHiddenInteractionLiftingBridge)
        ["CouponHiddenInteractionLiftingBridge"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "The coupon lifting bridge is a concrete downstream witness bridge."
  | .couponStaticExample =>
      representationRow
        "chapter11.couponStaticExample"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .couponStaticExample)
        ["CouponStaticDependencyExample"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Coupon static examples are concrete representation-level fixtures."
  | .couponSemanticValuation =>
      representationRow
        "chapter11.couponSemanticValuation"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .couponSemanticValuation)
        ["CouponDiscountExample"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Coupon semantic valuation is a concrete downstream semantic fixture."
  | .staticSemanticCounterexample =>
      representationRow
        "chapter11.staticSemanticCounterexample"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .staticSemanticCounterexample)
        ["StaticSemanticCounterexample"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "The static-semantic counterexample is a downstream negative fixture."
  | .generatedExternalSemanticBoundary =>
      atomGeneratedRow
        "chapter11.generatedExternalSemanticBoundary"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .generatedExternalSemanticBoundary)
        ["Chapter11AnalyticRepresentation.GeneratedExternalSemanticObstructionBoundary.generated_semantic_flatness_does_not_discharge_external",
         "Chapter11AnalyticRepresentation.coupon_generated_semantic_flatness_does_not_discharge_static_semantic_counterexample"]
        (by simp)
        "Generated semantic flatness is scoped to generated reflexive diagrams and does not discharge external selected semantic obstructions."
  | .measurementBoundary =>
      representationRow
        "chapter11.measurementBoundary"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .measurementBoundary)
        ["MeasurementBoundary", "AnalyticAxisBoundary"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Measurement boundary is a downstream tooling/analytic boundary surface."

def classifySFT
    (candidate : SFTTheoremPackages.Candidate) :
    TheoremPackageClassification :=
  match candidate with
  | .softwareFieldProjection =>
      representationRow
        "sft.softwareFieldProjection"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .softwareFieldProjection)
        ["SoftwareField", "SoftwareFieldEstimate"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "SFT software-field projection is a downstream SFT package, not an Atom-generated AAT theorem."
  | .forecastConeCore =>
      representationRow
        "sft.forecastConeCore"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .forecastConeCore)
        ["ForecastCone"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "ForecastCone is downstream SFT evolution vocabulary."
  | .coneProjection =>
      representationRow
        "sft.coneProjection"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .coneProjection)
        ["ForecastConeProjection"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Cone projection is downstream SFT support/projection vocabulary."
  | .artifactAction =>
      representationRow
        "sft.artifactAction"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .artifactAction)
        ["ArtifactAction"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Artifact actions are downstream SFT workflow vocabulary."
  | .operationPolicyGovernance =>
      representationRow
        "sft.operationPolicyGovernance"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .operationPolicyGovernance)
        ["OperationPolicy", "GovernanceIntervention"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Policy/governance is downstream SFT control vocabulary."
  | .stableRegionReachability =>
      representationRow
        "sft.stableRegionReachability"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .stableRegionReachability)
        ["StableRegion", "MayReach", "MustReach"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Reachability is downstream SFT field vocabulary."
  | .supportSafety =>
      representationRow
        "sft.supportSafety"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .supportSafety)
        ["SFTSupportSafetyPackage"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Support safety is an assumption-relative downstream SFT package."
  | .fieldUpdate =>
      representationRow
        "sft.fieldUpdate"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .fieldUpdate)
        ["FieldUpdate"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Field updates are downstream SFT feedback vocabulary."
  | .consequenceEnvelope =>
      atomGeneratedRow
        "sft.consequenceEnvelope"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .consequenceEnvelope)
        ["GeneratedAATConsequenceEnvelope",
         "AAT.GeneratedSFTInput.toAATCoreLocalAlgebraForSFT",
         "GeneratedAATConsequenceEnvelope.theorem_status_from_generated"]
        (by simp)
        "The consequence envelope has a generated entrypoint from GeneratedSFTInput and generated ArchSig transition evidence while preserving forecast boundaries."
  | .aatInterfaceBoundary =>
      atomGeneratedRow
        "sft.aatInterfaceBoundary"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .aatInterfaceBoundary)
        ["AAT.GeneratedSFTInput",
         "AAT.GeneratedSFTInput.theoremStatusFromGenerated"]
        (by simp)
        "Generated SFT input computes theorem status from GeneratedArchitectureLawModel."
  | .archSigReportBoundary =>
      atomGeneratedRow
        "sft.archSigReportBoundary"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .archSigReportBoundary)
        ["GeneratedArchSigAATCoreTransition",
         "GeneratedFieldSigAATCoreTransitionAnalysis",
         "GeneratedArchSigAATCoreTransportTransition"]
        (by simp)
        "ArchSig / FieldSig boundary includes generated preservation and non-identity transport handoff."
  | .counterexamplePackage =>
      representationRow
        "sft.counterexamplePackage"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .counterexamplePackage)
        ["SFTCounterexamples.Package"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Counterexamples are downstream forbidden-reading fixtures."
  | .theoremRoadmap =>
      representationRow
        "sft.theoremRoadmap"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .theoremRoadmap)
        ["SFTTheoremRoadmap"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "The SFT theorem roadmap is downstream SFT theorem-package assembly."
  | .finiteExactModel =>
      representationRow
        "sft.finiteExactModel"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .finiteExactModel)
        ["FiniteExactSFTModel"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Finite exact SFT models are downstream selected finite field models."
  | .aatSupportedFundamentalModularity =>
      atomGeneratedRow
        "sft.aatSupportedFundamentalModularity"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .aatSupportedFundamentalModularity)
        ["SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInput",
         "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary"]
        (by simp)
        "The AAT-supported SFT boundary has generated handoff constructors and examples."

def aatClassifications : List TheoremPackageClassification :=
  [ classifyAATCandidate .finiteStaticStructuralCore
  , classifyAATCandidate .generatedSignatureBridge
  , classifyAATCandidate .atomGeneratedAlgebraKernel
  , classifyAATCandidate .archMapObservationBoundary
  , classifyAATCandidate .crossPackageSmoke
  ]

def chapter7Classifications : List TheoremPackageClassification :=
  [ classifyChapter7 .splitExtensionPreservation
  , classifyChapter7 .nonSplitExtensionWitness
  , classifyChapter7 .repairAsResplitting
  , classifyChapter7 .complexityTransfer
  , classifyChapter7 .noSolutionCertificate
  , classifyChapter7 .architectureEvolution
  ]

def chapter8Classifications : List TheoremPackageClassification :=
  [ classifyChapter8 .architecturePaths
  , classifyChapter8 .generatedPathHomotopy
  , classifyChapter8 .selectedObservationInvariance
  , classifyChapter8 .diagramFiller
  , classifyChapter8 .obstructionAsNonFillability
  ]

def chapter9Classifications : List TheoremPackageClassification :=
  [ classifyChapter9 .diagramFillingObstruction
  , classifyChapter9 .splitExtensionLifting
  , classifyChapter9 .fillingFailureBridge
  ]

def chapter10Classifications : List TheoremPackageClassification :=
  [ classifyChapter10 .obstructionUniverse
  , classifyChapter10 .nonSplitWitnessPackage
  , classifyChapter10 .singleLabelClassification
  , classifyChapter10 .multiLabelClassification
  , classifyChapter10 .fillingFailureBridge
  , classifyChapter10 .liftingFailureBridge
  , classifyChapter10 .complexityTransferBridge
  , classifyChapter10 .residualCoverageGapBridge
  ]

def chapter11Classifications : List TheoremPackageClassification :=
  [ classifyChapter11 .analyticRepresentation
  , classifyChapter11 .toolingReportMetadata
  , classifyChapter11 .architectureSignatureRepresentation
  , classifyChapter11 .obstructionValuation
  , classifyChapter11 .analyticExtensionFormula
  , classifyChapter11 .couponAnalyticSnapshot
  , classifyChapter11 .couponHiddenInteractionLiftingBridge
  , classifyChapter11 .couponStaticExample
  , classifyChapter11 .couponSemanticValuation
  , classifyChapter11 .staticSemanticCounterexample
  , classifyChapter11 .generatedExternalSemanticBoundary
  , classifyChapter11 .measurementBoundary
  ]

def sftClassifications : List TheoremPackageClassification :=
  [ classifySFT .softwareFieldProjection
  , classifySFT .forecastConeCore
  , classifySFT .coneProjection
  , classifySFT .artifactAction
  , classifySFT .operationPolicyGovernance
  , classifySFT .stableRegionReachability
  , classifySFT .supportSafety
  , classifySFT .fieldUpdate
  , classifySFT .consequenceEnvelope
  , classifySFT .aatInterfaceBoundary
  , classifySFT .archSigReportBoundary
  , classifySFT .counterexamplePackage
  , classifySFT .theoremRoadmap
  , classifySFT .finiteExactModel
  , classifySFT .aatSupportedFundamentalModularity
  ]

theorem aat_candidates_are_registered
    (candidate : AATCandidate) :
    classifyAATCandidate candidate ∈ aatClassifications := by
  cases candidate <;> simp [aatClassifications]

theorem chapter7_candidates_are_registered
    (candidate : Chapter7TheoremPackages.Candidate) :
    classifyChapter7 candidate ∈ chapter7Classifications := by
  cases candidate <;> simp [chapter7Classifications]

theorem chapter8_candidates_are_registered
    (candidate : Chapter8HomotopySkeleton.Candidate) :
    classifyChapter8 candidate ∈ chapter8Classifications := by
  cases candidate <;> simp [chapter8Classifications]

theorem chapter9_candidates_are_registered
    (candidate : Chapter9DiagramFilling.Candidate) :
    classifyChapter9 candidate ∈ chapter9Classifications := by
  cases candidate <;> simp [chapter9Classifications]

theorem chapter10_candidates_are_registered
    (candidate : Chapter10ArchitectureExtensionFormula.Candidate) :
    classifyChapter10 candidate ∈ chapter10Classifications := by
  cases candidate <;> simp [chapter10Classifications]

theorem chapter11_candidates_are_registered
    (candidate : Chapter11AnalyticRepresentation.Candidate) :
    classifyChapter11 candidate ∈ chapter11Classifications := by
  cases candidate <;> simp [chapter11Classifications]

theorem sft_candidates_are_registered
    (candidate : SFTTheoremPackages.Candidate) :
    classifySFT candidate ∈ sftClassifications := by
  cases candidate <;> simp [sftClassifications]

/-- Registry for the theorem-package classification check in the reconstruction plan. -/
def allClassifications : List TheoremPackageClassification :=
  aatClassifications ++
  chapter7Classifications ++
  chapter8Classifications ++
  chapter9Classifications ++
  chapter10Classifications ++
  chapter11Classifications ++
  sftClassifications

def allPackageIds : List String :=
  allClassifications.map (fun row => row.packageId)

def allClassificationClasses : List TheoremPackageClass :=
  allClassifications.map (fun row => row.classification)

def allClassificationActions : List ReconstructionAction :=
  allClassifications.map (fun row => row.action)

def allClassificationClassActions :
    List (TheoremPackageClass × ReconstructionAction) :=
  allClassifications.map (fun row => (row.classification, row.action))

/-- Decidable footprint extracted from a classification row for registry-wide checks. -/
structure ClassificationFootprint where
  packageId : String
  classification : TheoremPackageClass
  action : ReconstructionAction
  generatedEntrypoints : List String
  bridgeAssumptions : List String
  representationEntrypoints : List String
  deriving DecidableEq, Repr

def classificationFootprintOf
    (row : TheoremPackageClassification) : ClassificationFootprint where
  packageId := row.packageId
  classification := row.classification
  action := row.action
  generatedEntrypoints := row.generatedEntrypoints
  bridgeAssumptions := row.bridgeAssumptions
  representationEntrypoints := row.representationEntrypoints

def allClassificationFootprints : List ClassificationFootprint :=
  allClassifications.map classificationFootprintOf

theorem registry_rows_have_classification_evidence
    {row : TheoremPackageClassification}
    (_hRow : row ∈ allClassifications) :
    row.Passes :=
  row.passes

theorem registry_rows_have_allowed_actions
    {row : TheoremPackageClassification}
    (_hRow : row ∈ allClassifications) :
    row.HasAllowedAction :=
  row.action_allowed

theorem theorem_package_registry_has_no_bridge_assumed_rows :
    .bridgeAssumed ∉ allClassificationClasses := by
  native_decide

theorem theorem_package_registry_has_no_rewrite_targets :
    .rewriteTarget ∉ allClassificationActions := by
  native_decide

theorem theorem_package_registry_has_no_temporary_bridge_actions :
    .temporaryBridge ∉ allClassificationActions := by
  native_decide

theorem theorem_package_registry_has_unique_package_ids :
    allPackageIds.Nodup := by
  native_decide

theorem theorem_package_registry_has_no_bridge_assumption_footprints :
    ∀ footprint ∈ allClassificationFootprints,
      footprint.bridgeAssumptions = [] := by
  native_decide

theorem theorem_package_registry_source_rows_are_atom_generated :
    ∀ classAction ∈ allClassificationClassActions,
      classAction.2 = .aatSourceOfTruth ->
        classAction.1 = .atomGenerated := by
  native_decide

theorem theorem_package_registry_source_footprints_are_generated_only :
    ∀ footprint ∈ allClassificationFootprints,
      footprint.action = .aatSourceOfTruth ->
        footprint.classification = .atomGenerated ∧
        footprint.generatedEntrypoints ≠ [] ∧
        footprint.bridgeAssumptions = [] ∧
        footprint.representationEntrypoints = [] := by
  native_decide

theorem theorem_package_registry_representation_rows_are_downstream_libraries :
    ∀ classAction ∈ allClassificationClassActions,
      classAction.1 = .representationLevel ->
        classAction.2 = .downstreamLibrary := by
  native_decide

theorem theorem_package_registry_representation_footprints_are_downstream_only :
    ∀ footprint ∈ allClassificationFootprints,
      footprint.classification = .representationLevel ->
        footprint.action = .downstreamLibrary ∧
        footprint.generatedEntrypoints = [] ∧
        footprint.bridgeAssumptions = [] ∧
        footprint.representationEntrypoints ≠ [] := by
  native_decide

theorem generic_signature_bridge_is_not_theorem_package_registry_row :
    "aat.genericSignatureBridge" ∉ allPackageIds := by
  native_decide

theorem generic_signature_bridge_is_legacy_replaced_surface :
    genericSignatureBridgeLegacySurface.IsBridgeAssumptionSurface ∧
    genericSignatureBridgeLegacySurface.HasGeneratedReplacement := by
  exact
    ⟨LegacyBridgeSurface.bridge_assumption_surface
        genericSignatureBridgeLegacySurface,
      LegacyBridgeSurface.has_generated_replacement
        genericSignatureBridgeLegacySurface⟩

theorem generated_signature_bridge_is_atom_generated :
    (classifyAATCandidate .generatedSignatureBridge).classification =
      .atomGenerated ∧
    (classifyAATCandidate .generatedSignatureBridge).action =
      .aatSourceOfTruth := by
  exact ⟨rfl, rfl⟩

theorem nonidentity_transport_handoff_is_atom_generated :
    (classifyAATCandidate .crossPackageSmoke).classification =
      .atomGenerated ∧
    (classifySFT .archSigReportBoundary).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl⟩

theorem finite_static_core_is_downstream_representation_library :
    (classifyAATCandidate .finiteStaticStructuralCore).classification =
      .representationLevel ∧
    (classifyAATCandidate .finiteStaticStructuralCore).action =
      .downstreamLibrary := by
  exact ⟨rfl, rfl⟩

theorem archmap_observation_handoff_is_atom_generated :
    (classifyAATCandidate .archMapObservationBoundary).classification =
      .atomGenerated ∧
    (classifyAATCandidate .archMapObservationBoundary).action =
      .aatSourceOfTruth := by
  exact ⟨rfl, rfl⟩

theorem generated_filling_failure_bridge_is_atom_generated :
    (classifyChapter7 .nonSplitExtensionWitness).classification =
      .atomGenerated ∧
    (classifyChapter9 .fillingFailureBridge).classification =
      .atomGenerated ∧
    (classifyChapter10 .nonSplitWitnessPackage).classification =
      .atomGenerated ∧
    (classifyChapter10 .fillingFailureBridge).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem generated_split_lifting_bridge_is_atom_generated :
    (classifyChapter9 .splitExtensionLifting).classification =
      .atomGenerated ∧
    (classifyChapter10 .liftingFailureBridge).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl⟩

theorem generated_consequence_envelope_is_atom_generated :
    (classifySFT .consequenceEnvelope).classification =
      .atomGenerated := by
  rfl

theorem generated_analytic_extension_formula_is_atom_generated :
    (classifyChapter11 .obstructionValuation).classification =
      .atomGenerated ∧
    (classifyChapter11 .analyticExtensionFormula).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl⟩

theorem generated_external_semantic_boundary_is_atom_generated :
    (classifyChapter11 .generatedExternalSemanticBoundary).classification =
      .atomGenerated ∧
    (classifyChapter11 .generatedExternalSemanticBoundary).action =
      .aatSourceOfTruth := by
  exact ⟨rfl, rfl⟩

theorem generated_chapter8_path_diagram_is_atom_generated :
    (classifyChapter8 .architecturePaths).classification =
      .atomGenerated ∧
    (classifyChapter8 .selectedObservationInvariance).classification =
      .atomGenerated ∧
    (classifyChapter8 .diagramFiller).classification =
      .atomGenerated ∧
    (classifyChapter8 .obstructionAsNonFillability).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem generated_complexity_residual_bridge_is_atom_generated :
    (classifyChapter7 .complexityTransfer).classification =
      .atomGenerated ∧
    (classifyChapter10 .complexityTransferBridge).classification =
      .atomGenerated ∧
    (classifyChapter10 .residualCoverageGapBridge).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl, rfl⟩

theorem generated_extension_obstruction_universe_is_atom_generated :
    (classifyChapter10 .obstructionUniverse).classification =
      .atomGenerated := by
  rfl

end AATReconstructionClassification
end Formal.Arch
