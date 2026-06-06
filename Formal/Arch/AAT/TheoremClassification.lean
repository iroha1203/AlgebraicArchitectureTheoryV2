import Formal.Arch.Evolution.Chapter7TheoremPackages
import Formal.Arch.Evolution.Chapter8HomotopySkeleton
import Formal.Arch.Evolution.Chapter9DiagramFilling
import Formal.Arch.Evolution.Chapter10ArchitectureExtensionFormula
import Formal.Arch.Evolution.Chapter11AnalyticRepresentation
import Formal.Arch.Evolution.Part4DistanceMeasureGeometry
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

def generatedWalkAcyclicLawModelLegacySurface : LegacyBridgeSurface where
  surfaceId := "aat.generatedLawModelFromWalkAcyclic"
  representativeDeclarations :=
    ["AAT.GeneratedArchitectureLawModel.generatedWalkAcyclic_eq_graphRank_walkAcyclic"]
  bridgeAssumptions := ["obsolete generatedWalkAcyclic field: WalkAcyclic (GeneratedArchGraph object)"]
  generatedReplacementEntrypoints :=
    ["AAT.GeneratedArchitectureLawModel.graphRank",
     "AAT.GeneratedGraphRank.walkAcyclic",
     "AAT.GeneratedArchitectureLawModel.ofGraphRank",
     "AAT.GeneratedArchitectureLawModel.generated_law_model_from_generated_object",
     "AAT.GeneratedArchitectureLawModel.generated_law_model_from_generated_graph_rank"]
  reason :=
    "The old law-model state accepted a caller-supplied generated-graph acyclicity premise.  The current state stores GeneratedGraphRank and derives WalkAcyclic from that generated certificate."
  bridgeEvidence := by simp
  replacementEvidence := by simp

def legacyBridgeSurfaces : List LegacyBridgeSurface :=
  [genericSignatureBridgeLegacySurface,
   generatedWalkAcyclicLawModelLegacySurface]

def legacyBridgeSurfaceIds : List String :=
  legacyBridgeSurfaces.map (fun surface => surface.surfaceId)

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
       "ArchitectureSignature.ArchitectureLawModel.signatureOf",
       "AAT.GeneratedArchitectureLawModel.generatedArchitectureLawful_iff_requiredSignatureAxesZero",
       "AAT.GeneratedArchitectureLawModel.generatedArchitectureZeroCurvatureTheoremPackage",
       "AAT.GeneratedArchitectureLawModel.generatedArchitectureZeroCurvatureTheoremPackage_holds",
       "AAT.GeneratedArchitectureLawModel.generatedArchitectureLawful_iff_generatedArchitectureZeroCurvatureTheoremPackage",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_zeroCurvatureTheoremPackage",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_lawful_iff_zeroCurvatureTheoremPackage"]
  | generatedSignatureBridge =>
      ["ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel",
       "ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel_architectureLawful",
       "AAT.GeneratedArchitectureLawModel.generatedAATCoreNoObservationDependency_recorded",
       "AAT.GeneratedArchitectureLawModel.generatedAATCoreCircuitBoundary_recorded",
       "AAT.GeneratedArchitectureLawModel.generatedAATCoreCircuit_impossible",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_coreSignatureBridge"]
  | atomGeneratedAlgebraKernel =>
      ["AAT.GeneratedMolecule",
       "AAT.GeneratedMolecule.not_arbitrary_set",
       "AtomGeneratedMoleculeExamples.generatedComponentMolecule_not_arbitrary_set",
       "AAT.GeneratedArchitectureObject",
       "AAT.GeneratedArchitectureObject.generated_authority_effect_law_satisfied_from_authority_policy",
       "AtomGeneratedMoleculeExamples.generatedAuthorityPolicy_from_authority_atom",
       "AtomGeneratedMoleculeExamples.generatedEffectLawInput_from_effect_atom",
       "AtomGeneratedMoleculeExamples.generatedAuthorityEffectLaw_locally_satisfied",
       "AAT.GeneratedArchitectureObject.generated_semantic_contract_coverage_from_contract_atoms",
       "AtomGeneratedMoleculeExamples.generatedContract_from_contract_atom",
       "AtomGeneratedMoleculeExamples.generatedSemanticInterpretation_from_semantic_atom",
       "AtomGeneratedMoleculeExamples.generatedSemanticContractCoverage_from_contract_atom",
       "AAT.GeneratedArchitectureObject.generated_capability_data_state_support_from_data_state_atoms",
       "AtomGeneratedMoleculeExamples.generatedCapability_from_capability_atom",
       "AtomGeneratedMoleculeExamples.generatedDataState_from_data_state_atom",
       "AtomGeneratedMoleculeExamples.generatedCapabilityDataStateSupport_from_data_state_atom",
       "AtomShapeKindCoverageExamples.coverage_shape_exists_for_every_atom_kind",
       "AtomShapeKindCoverageExamples.coverage_shape_has_valence_port",
       "AAT.GeneratedAtomShapeCoordinate",
       "AAT.GeneratedArchitectureObject.generatedCarrierShapeDistance",
       "AAT.generatedAtomShapeCoordinateDistance",
       "AAT.GeneratedArchitectureObject.generated_shapeCoordinateTotalCurvature_eq_zero",
       "AtomGeneratedMoleculeExamples.generatedComponent_shapeCoordinateTotalCurvature_eq_zero",
       "AAT.GeneratedRelationAtom",
       "AtomGeneratedMoleculeExamples.directedRelationGeneratedGraph_api_to_database_edge",
       "AtomGeneratedMoleculeExamples.directedRelationGeneratedGraph_edge_uses_source_target_ports",
       "AtomGeneratedMoleculeExamples.directedRelationGeneratedGraph_no_database_to_api_edge",
       "AtomGeneratedMoleculeExamples.directedRelationGraphRank",
       "AtomGeneratedMoleculeExamples.directedRelation_law_model_from_graph_rank",
       "AtomGeneratedMoleculeExamples.directedRuntimeGeneratedGraph_api_to_database_edge",
       "AtomGeneratedMoleculeExamples.directedRuntimeGeneratedGraph_edge_uses_source_target_ports",
       "AtomGeneratedMoleculeExamples.directedRuntimeGeneratedGraph_no_database_to_api_edge",
       "AAT.GeneratedRuntimeGraphRank",
       "AAT.GeneratedRuntimeGraphRank.walkAcyclic",
       "AtomGeneratedMoleculeExamples.directedRuntimeGraphRank",
       "AtomGeneratedMoleculeExamples.directedRuntimeGraphRank_walkAcyclic",
       "AAT.GeneratedGraphRank",
       "AAT.GeneratedGraphRank.walkAcyclic",
       "AAT.GeneratedArchitectureLawModel",
       "AAT.GeneratedArchitectureLawModel.ofGraphRank",
       "AAT.GeneratedArchitectureLawModel.generated_law_model_from_generated_graph_rank",
       "AtomGeneratedSignatureExamples.*",
       "AtomGeneratedMoleculeExamples.generatedComponentObject_api_database_shapeDistance_eq_one",
       "AtomGeneratedMoleculeExamples.generatedApiExpansionOperation_mapped_api_shapeDistance_eq_zero",
       "AtomGeneratedMoleculeExamples.generatedApiExpansionOperation_database_unmapped",
       "AtomGeneratedMoleculeExamples.generatedApiExpansionOperation_unmapped_database_primitive",
       "AtomGeneratedRepairExamples.repairedGeneratedGraphRank",
       "AtomGeneratedRepairExamples.repaired_law_model_from_graph_rank",
       "AtomGeneratedRepairExamples.*",
       "IncompatibleAtomCompositionExamples.effect_atom_without_authority_not_generated_molecule",
       "IncompatibleAtomCompositionExamples.capability_atom_without_data_state_not_generated_molecule",
       "IncompatibleAtomCompositionExamples.semantic_atom_without_contract_not_generated_molecule",
       "IncompatibleAtomCompositionExamples.*"]
  | archMapObservationBoundary =>
      ["Observation.ArchMapObservationLayer",
       "Observation.ArchMapObservationLayer.archmap_does_not_create_atoms",
       "Observation.ArchMapObservationLayer.archmap_does_not_define_aat",
       "Observation.ArchMapObservedAtomSelection.toGeneratedMolecule",
       "ArchMapObservationExamples.archMap_observed_atom_selection_not_arbitrary",
       "ArchMapObservationExamples.archMap_observed_atom_handoff_not_arbitrary",
       "Observation.ArchMapGeneratedArchitectureObjectInput.toGeneratedArchitectureObject"]
  | crossPackageSmoke =>
      ["AATCoreSmokeExamples.generated_transport_handoff_reads_nonidentity_transition",
       "AATCoreSmokeExamples.generated_transport_circuit_delta_keeps_source_target_surfaces"]

end AATCandidate

def classifyAATCandidate
    (candidate : AATCandidate) : TheoremPackageClassification :=
  match candidate with
  | .finiteStaticStructuralCore =>
      atomGeneratedRow
        "aat.finiteStaticStructuralCore"
        (AATCandidate.representativeDeclarations
          .finiteStaticStructuralCore)
        ["AAT.GeneratedArchitectureLawModel.generatedArchitectureLawful_iff_requiredSignatureAxesZero",
         "AAT.GeneratedArchitectureLawModel.generatedArchitectureZeroCurvatureTheoremPackage",
         "AAT.GeneratedArchitectureLawModel.generatedArchitectureZeroCurvatureTheoremPackage_holds",
         "AAT.GeneratedArchitectureLawModel.generatedArchitectureLawful_iff_generatedArchitectureZeroCurvatureTheoremPackage",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_zeroCurvatureTheoremPackage"]
        (by simp)
        "The static Signature zero-curvature anchor is source-of-truth only through generated law-model entrypoints; the hand-authored ArchitectureLawModel theorem remains the downstream library surface invoked by those generated wrappers."
  | .generatedSignatureBridge =>
      atomGeneratedRow
        "aat.generatedSignatureBridge"
        (AATCandidate.representativeDeclarations .generatedSignatureBridge)
        ["ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel",
         "AAT.GeneratedArchitectureLawModel.generatedAATCoreCircuitBoundary_recorded"]
        (by simp)
        "The generated constructor derives Signature lawfulness and pure AAT circuit boundaries from GeneratedArchitectureLawModel and does not ask callers for architectureLawfulFromAAT."
  | .atomGeneratedAlgebraKernel =>
      atomGeneratedRow
        "aat.atomGeneratedAlgebraKernel"
        (AATCandidate.representativeDeclarations .atomGeneratedAlgebraKernel)
        ["AAT.GeneratedArchitectureObject",
         "AAT.GeneratedMolecule.not_arbitrary_set",
         "AtomGeneratedMoleculeExamples.generatedComponentMolecule_not_arbitrary_set",
         "AtomGeneratedMoleculeExamples.generatedAuthorityEffectLaw_locally_satisfied",
         "AtomGeneratedMoleculeExamples.generatedSemanticContractCoverage_from_contract_atom",
         "AtomGeneratedMoleculeExamples.generatedCapabilityDataStateSupport_from_data_state_atom",
         "AtomShapeKindCoverageExamples.coverage_shape_exists_for_every_atom_kind",
         "AAT.GeneratedArchitectureObject.generatedCarrierShapeDistance",
         "AAT.GeneratedArchitectureObject.generated_shapeCoordinateTotalCurvature_eq_zero",
         "AtomGeneratedMoleculeExamples.directedRelationGeneratedGraph_api_to_database_edge",
         "AtomGeneratedMoleculeExamples.directedRelation_law_model_from_graph_rank",
         "AtomGeneratedMoleculeExamples.directedRuntimeGeneratedGraph_api_to_database_edge",
         "AtomGeneratedMoleculeExamples.directedRuntimeGraphRank_walkAcyclic",
         "AAT.GeneratedArchitectureLawModel.ofGraphRank",
         "AtomGeneratedRepairExamples.repaired_law_model_from_graph_rank",
         "AAT.GeneratedArchitectureLawModel",
         "AtomGeneratedSignatureExamples.*"]
        (by simp)
        "The kernel starts from AtomShape / compatible composition, covers the current AtomKind grammar as shaped typed facts, and reaches generated molecule, object, authority/effect local law satisfaction, semantic-contract coverage, capability/data-state support, shape distance, shape-coordinate curvature, oriented relation/runtime edge generation, generated graph rank, law model, signature, repair, and negative acceptance examples."
  | .archMapObservationBoundary =>
      atomGeneratedRow
        "aat.archMapObservationBoundary"
        (AATCandidate.representativeDeclarations .archMapObservationBoundary)
        ["Observation.ArchMapObservedAtomSelection.toGeneratedMolecule",
         "ArchMapObservationExamples.archMap_observed_atom_handoff_not_arbitrary",
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
        ["Chapter7TheoremPackages.generatedRepairProblemOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount",
         "Chapter7TheoremPackages.generatedRepairProblemOperation_unmapped_target_atom_primitive",
         "Chapter7TheoremPackages.generatedRepairFromProblem_toRepairClearingPackage"]
        (by simp)
        "Repair is connected through generated repair targets, pre-molecule repair problem operations with AtomShape distance and unmapped target primitive evidence, and the downstream repair-clearing package."
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
        ["Chapter7TheoremPackages.generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount",
         "Chapter7TheoremPackages.generatedOperation_unmapped_target_atom_primitive",
         "Chapter7TheoremPackages.generatedOperation_toOperationTransportPackage"]
        (by simp)
        "Generated operations expose AtomShape transformation, mapped shape distance, unmapped target primitive evidence, and non-identity AATCore transport."

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
         "Chapter9DiagramFilling.generatedSelfFeatureExtension_preservesRequiredInvariants",
         "Chapter9DiagramFilling.generatedSelfFeatureExtension_interactionFactorsThroughDeclaredInterfaces",
         "Chapter9DiagramFilling.generatedSelfFeatureExtension_coverageAssumptions",
         "Chapter9DiagramFilling.generatedSelfFeatureExtension_proofObligations",
         "Chapter9DiagramFilling.generatedSelfSplitExtensionLifting_preservationPackage"]
        (by simp)
        "Split-extension lifting has a generated self-view feature extension entrypoint whose fields are discharged from generated carriers, relation atoms, and carrier coverage."
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
      atomGeneratedRow
        "chapter11.analyticRepresentation"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .analyticRepresentation)
        ["AAT.GeneratedArchitectureLawModel.generatedAnalyticRepresentation",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_represent_eq_signatureOfGenerated",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_coverageAssumptions",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_witnessCompleteness",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_semanticContractCoverage",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroPreserving",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_zeroReflecting",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionPreserving",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_obstructionReflecting",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_nonConclusions"]
        (by simp)
        "The generic analytic representation package has an Atom-generated law-model specialization with generated coverage, preserving, reflecting, and non-conclusion evidence."
  | .toolingReportMetadata =>
      atomGeneratedRow
        "chapter11.toolingReportMetadata"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .toolingReportMetadata)
        ["Chapter11AnalyticRepresentation.generatedToolingTheoremPackageMetadata",
         "Chapter11AnalyticRepresentation.generatedToolingTheoremPackageMetadata_formalProvedClaim",
         "Chapter11AnalyticRepresentation.generatedToolingTheoremPackageMetadata_recordsNonConclusions"]
        (by simp)
        "Report metadata has a generated formal-claim package for generated analytic representation, while measured tooling witnesses remain separated from theorem claims."
  | .architectureSignatureRepresentation =>
      atomGeneratedRow
        "chapter11.architectureSignatureRepresentation"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .architectureSignatureRepresentation)
        ["AAT.GeneratedArchitectureLawModel.generatedAnalyticRepresentation",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_represent_eq_signatureOfGenerated",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_coverageAssumptions",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_witnessCompleteness",
         "Chapter11AnalyticRepresentation.generatedAnalyticRepresentation_semanticContractCoverage"]
        (by simp)
        "ArchitectureSignature representation has a generated law-model entrypoint and generated coverage assumptions."
  | .obstructionValuation =>
      atomGeneratedRow
        "chapter11.obstructionValuation"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .obstructionValuation)
        ["AAT.GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation",
         "Chapter11AnalyticRepresentation.generatedRequiredSignatureObstructionValuation_coverageAssumptions",
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
         "Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_representationMapAssumptions",
         "Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_valuationStructureAssumptions",
         "Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_decompositionCertificate",
         "Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_coverageAssumptions",
         "Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_complexityTransferBoundary",
         "Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_formula_holds",
         "Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_obstructionValue_zero"]
        (by simp)
        "The analytic extension formula has a generated identity specialization whose assumptions are discharged from generated coverage, identity decomposition, and zero-transfer evidence."
  | .couponAnalyticSnapshot =>
      atomGeneratedRow
        "chapter11.couponAnalyticSnapshot"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .couponAnalyticSnapshot)
        ["Chapter11AnalyticRepresentation.generatedCouponAnalyticSnapshot_bad_staticHiddenInteraction_bridge"]
        (by simp)
        "Coupon analytic snapshots have a generated boundary acceptance that reads generated semantic flatness alongside the selected static hidden-interaction obstruction."
  | .couponHiddenInteractionLiftingBridge =>
      atomGeneratedRow
        "chapter11.couponHiddenInteractionLiftingBridge"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .couponHiddenInteractionLiftingBridge)
        ["Chapter11AnalyticRepresentation.generatedCouponHiddenInteraction_liftingFailure_bridge"]
        (by simp)
        "Coupon hidden interaction lifting has a generated boundary acceptance that keeps the selected lifting failure visible next to generated semantic flatness."
  | .couponStaticExample =>
      atomGeneratedRow
        "chapter11.couponStaticExample"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .couponStaticExample)
        ["Chapter11AnalyticRepresentation.generatedCouponStaticExample_bad_not_split",
         "Chapter11AnalyticRepresentation.generatedCouponStaticExample_repaired_split"]
        (by simp)
        "Coupon static examples have generated boundary acceptance for both bad non-split and repaired split readings."
  | .couponSemanticValuation =>
      atomGeneratedRow
        "chapter11.couponSemanticValuation"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .couponSemanticValuation)
        ["Chapter11AnalyticRepresentation.generatedCouponSemanticValuation_roundingOrder_positive",
         "Chapter11AnalyticRepresentation.generatedCouponSemanticValuation_recordsNonConclusions"]
        (by simp)
        "Coupon semantic valuation has generated boundary acceptance that preserves the selected positive rounding-order obstruction and non-conclusions."
  | .staticSemanticCounterexample =>
      atomGeneratedRow
        "chapter11.staticSemanticCounterexample"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .staticSemanticCounterexample)
        ["Chapter11AnalyticRepresentation.generatedStaticSemanticCounterexample_boundary"]
        (by simp)
        "Static-semantic counterexample has a generated boundary acceptance that keeps external static-flat semantic obstruction separate from generated semantic flatness."
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
      atomGeneratedRow
        "chapter11.measurementBoundary"
        (Chapter11AnalyticRepresentation.Candidate.representativeDeclarations
          .measurementBoundary)
        ["Chapter11AnalyticRepresentation.generatedAnalyticAxisBoundary",
         "Chapter11AnalyticRepresentation.generatedAnalyticAxisBoundary_value_eq_generatedValuation",
         "Chapter11AnalyticRepresentation.generatedAnalyticAxisBoundary_measuredZero",
         "Chapter11AnalyticRepresentation.generatedAnalyticAxisBoundary_canDischargeZeroReflectingClaim",
         "Chapter11AnalyticRepresentation.generatedMeasurementBoundary_unmeasured_remains_not_measuredZero"]
        (by simp)
        "Measurement boundary has generated selected-axis acceptance for generated obstruction valuation zero while preserving unmeasured-vs-measured-zero separation."

def classifyPart4
    (candidate : Part4DistanceMeasureGeometry.Candidate) :
    TheoremPackageClassification :=
  match candidate with
  | .distanceFoundation =>
      representationRow
        "part4.distanceFoundation"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .distanceFoundation)
        ["DistanceValue",
         "DistanceProfile",
         "SelectedDistanceScope",
         "BoundedDiagnosticConclusion",
         "DistanceValue.unmeasured_not_measuredZero"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Part IV distance foundations are selected-scope representation surfaces that keep unmeasured axes distinct from measured zero."
  | .distanceAATOverlay =>
      representationRow
        "part4.distanceAATOverlay"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .distanceAATOverlay)
        ["DistanceBundle",
         "DistanceBundle.records_selectedOverlay",
         "DistanceAAT",
         "DistanceAAT.distance_does_not_generate_atoms",
         "DistanceAAT.distance_does_not_replace_aatCore"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "DistanceAAT registers Part IV as a selected overlay on an existing AAT core, not as an Atom generator or replacement theorem."
  | .atomRootGeometry =>
      representationRow
        "part4.atomRootGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .atomRootGeometry)
        ["AtomRootDistanceBundle",
         "AtomRootDistanceBundle.layoutDistance_eq_weighted_components",
         "GeneratedAtomShapeDistanceBridge",
         "GeneratedAtomShapeDistanceBridge.generatedDistance_eq_coordinateMismatch"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Root Atom geometry records selected component distances while keeping semantic distance calibration and law overlays bounded."
  | .atomConfigurationGeometry =>
      atomGeneratedRow
        "part4.atomConfigurationGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .atomConfigurationGeometry)
        ["AAT.GeneratedArchitectureObject.generatedCarrierShapeDistance_eq_coordinate_mismatchCount",
         "AAT.GeneratedOperation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount",
         "Part4DistanceMeasureGeometry.generatedCarrierShapeDistance_eq_coordinate_mismatchCount",
         "Part4DistanceMeasureGeometry.generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount"]
        (by simp)
        "Atom and operation distance entrypoints unfold to generated AtomShape-coordinate mismatch counts."
  | .configurationContextGeometry =>
      representationRow
        "part4.configurationContextGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .configurationContextGeometry)
        ["ConfigurationDistanceSchema",
         "ConfigurationDistanceSchema.distance_le_suppliedPathCost",
         "ConfigurationDistanceSchema.samePairDistanceDiffers_of_witness",
         "ContextDistanceSchema",
         "ContextDistanceSchema.records_finiteContext"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Configuration and context distance rows are supplied finite-witness schemas without global shortest-path or context completeness."
  | .signaturePathGeometry =>
      representationRow
        "part4.signaturePathGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .signaturePathGeometry)
        ["SignatureDistanceSchema",
         "SignatureDistanceSchema.endpointDistance_le_pathLength",
         "SignatureDistanceSchema.margin_stability",
         "SignatureDistanceSchema.endpointDistance_add_hiddenExcursion_eq_pathLength",
         "Part4DistanceMeasureGeometry.signatureEndpointDistance_le_pathLength",
         "Part4DistanceMeasureGeometry.signatureEndpointDistance_add_hiddenExcursion_eq_pathLength"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Signature path geometry is finite-path and selected-scope, with margin stability requiring explicit preservation evidence."
  | .finiteWitnessInfimumCore =>
      representationRow
        "part4.finiteWitnessInfimumCore"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .finiteWitnessInfimumCore)
        ["FiniteRouteCost",
         "FiniteFillerCost",
         "FiniteHomotopyCost",
         "SelectedFiniteOptimum",
         "Part4DistanceMeasureGeometry.selectedFiniteOptimum_lowerBound_for_selected_candidates"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Finite witness and selected optimum rows are scoped to supplied finite candidate sets and do not assert global optimization completeness."
  | .distanceToLawfulnessGeometry =>
      representationRow
        "part4.distanceToLawfulnessGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .distanceToLawfulnessGeometry)
        ["SelectedDistanceToRegion",
         "SelectedDistanceToRegion.region_of_distance_zero",
         "SelectedDistanceToRegion.distance_zero_of_region",
         "Part4DistanceMeasureGeometry.selectedDistanceToRegion_region_of_distance_zero"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Distance-to-lawfulness and distance-to-flatness zero bridges are selected-scope and exactness-assumption relative."
  | .metricGaloisCorrespondence =>
      representationRow
        "part4.metricGaloisCorrespondence"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .metricGaloisCorrespondence)
        ["MetricOperationAction",
         "MetricOperationAction.NonExpansive",
         "MetricOperationAction.SelectedMetricGaloisPackage",
         "Part4DistanceMeasureGeometry.metricGalois_operation_nonExpansive"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Metric Galois correspondence is registered only for selected finite operation universes."
  | .operationRepairGeometry =>
      representationRow
        "part4.operationRepairGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .operationRepairGeometry)
        ["OperationCostModel",
         "OperationPathCost",
         "DistanceToFlatRegion",
         "BoundedSideEffectRepair",
         "Part4DistanceMeasureGeometry.boundedSideEffectRepair_targetDistance_decreases"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Operation repair geometry records selected costs, distance-to-flat wrappers, and bounded side-effect decreases without solver-completeness claims."
  | .contractiveRepairGeometry =>
      representationRow
        "part4.contractiveRepairGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .contractiveRepairGeometry)
        ["FiniteRepairSequence",
         "FiniteRepairSequence.allStepsDecrease",
         "ContractiveRepairStep",
         "ContractiveRepairStep.target_contracts",
         "Part4DistanceMeasureGeometry.contractiveRepairStep_target_contracts"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Contractive repair is a supplied finite-sequence / selected-step package and does not imply solver completeness or global convergence."
  | .curvatureFillingGeometry =>
      representationRow
        "part4.curvatureFillingGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .curvatureFillingGeometry)
        ["totalCurvature",
         "totalWeightedCurvature",
         "totalWeightedCurvature_eq_zero_iff_forall_measured_DiagramCommutes",
         "FillingCostLowerBound",
         "Part4DistanceMeasureGeometry.fillingCostLowerBound_observationGap_le"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Curvature mass and filling-cost rows are finite measured-universe theorem packages and do not assert universal filling completeness."
  | .curvatureTransportGeometry =>
      representationRow
        "part4.curvatureTransportGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .curvatureTransportGeometry)
        ["SelectedCurvatureReading",
         "CurvatureTransport",
         "CurvatureTransport.target_curvature_decreases",
         "CurvatureTransport.transported_curvature_increases"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Curvature transport is scoped to selected measured axes and does not treat unmeasured axes as zero."
  | .quantitativeHomotopyFillingGeometry =>
      representationRow
        "part4.quantitativeHomotopyFillingGeometry"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .quantitativeHomotopyFillingGeometry)
        ["QuantitativeHomotopyBound",
         "FiniteDehnBound",
         "PersistentNonFillability",
         "Part4DistanceMeasureGeometry.quantitativeHomotopyBound_observationDistance_le",
         "Part4DistanceMeasureGeometry.finiteDehnBound_fillingArea_le"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Quantitative homotopy, filling, finite Dehn, and persistent non-fillability rows are selected finite-candidate packages."
  | .representationMetric =>
      representationRow
        "part4.representationMetric"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .representationMetric)
        ["LipschitzRepresentation",
         "BiLipschitzRepresentation",
         "LipschitzRepresentation.analyticDistance_le_lipschitz",
         "BiLipschitzRepresentation.structuralDistance_le_analyticDistance"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Representation metrics are selected-scope Lipschitz and bi-Lipschitz surfaces with explicit comparability, coverage, and witness assumptions."
  | .representationSpectralStability =>
      representationRow
        "part4.representationSpectralStability"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .representationSpectralStability)
        ["LipschitzRepresentation.analyticDistance_le_of_structuralDistance_le",
         "SpectralStabilityPackage",
         "SpectralStabilityPackage.spectralDistance_le",
         "Part4DistanceMeasureGeometry.spectralStabilityPackage_spectralDistance_le"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Representation / spectral stability is selected-scope Lipschitz control, not empirical spectral calibration."
  | .abstractInfimumInterface =>
      representationRow
        "part4.abstractInfimumInterface"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .abstractInfimumInterface)
        ["AbstractInfimumInterface",
         "AbstractInfimumInterface.lowerBound",
         "AbstractInfimumInterface.exists_approximatingWitness",
         "AbstractInfimumInterface.ofSelectedFiniteOptimum"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "The abstract infimum interface records lower-bound and approximation witnesses without computing a global optimizer."
  | .diagnosticConclusionDetail =>
      representationRow
        "part4.diagnosticConclusionDetail"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .diagnosticConclusionDetail)
        ["DetailedBoundedDiagnosticConclusion",
         "DetailedBoundedDiagnosticConclusion.records_nonConclusions",
         "DetailedBoundedDiagnosticConclusion.records_recommendation_boundary",
         "Part4DistanceMeasureGeometry.detailedDiagnostic_records_nonConclusions",
         "Part4DistanceMeasureGeometry.detailedDiagnostic_records_recommendation_boundary"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "Detailed diagnostic conclusions keep supporting distances and recommended operations scoped without proving empirical repair success."
  | .docsClassificationBoundary =>
      representationRow
        "part4.docsClassificationBoundary"
        (Part4DistanceMeasureGeometry.Candidate.representativeDeclarations
          .docsClassificationBoundary)
        ["Part4DistanceMeasureGeometry.Candidate",
         "Part4DistanceMeasureGeometry.Candidate.schematicCorrespondence",
         "AATReconstructionClassification.classifyPart4"]
        (by simp)
        .downstreamLibrary
        ActionAllowed.representationDownstream
        "The Part IV entrypoint synchronizes theorem-index and proof-obligation rows without editing the mathematical Part IV source text."

def classifySFT
    (candidate : SFTTheoremPackages.Candidate) :
    TheoremPackageClassification :=
  match candidate with
  | .softwareFieldProjection =>
      atomGeneratedRow
        "sft.softwareFieldProjection"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .softwareFieldProjection)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareFieldEstimate",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedArchitectureProjectionBoundary",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField_projects_to_generated",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField_records_nonConclusions"]
        (by simp)
        "Software-field projection has an Atom-generated carrier instantiation whose selected estimate projects to the generated flatness model while preserving field and non-conclusion boundaries."
  | .forecastConeCore =>
      atomGeneratedRow
        "sft.forecastConeCore"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .forecastConeCore)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_sftSupportSafetyPackage",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_mem",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_length_le_horizon",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_monotone_succ"]
        (by simp)
        "ForecastCone core has an Atom-generated carrier witness induced by the generated support-safety package and finite supported trajectory."
  | .coneProjection =>
      atomGeneratedRow
        "sft.coneProjection"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .coneProjection)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_supportSelfInclusion",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_projects_self",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_exists_projected_generatedForecastCone",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_projects_horizon_succ"]
        (by simp)
        "Cone projection has generated carrier evidence through generated support self-inclusion, projected path existence, and horizon-extension projection."
  | .artifactAction =>
      atomGeneratedRow
        "sft.artifactAction"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .artifactAction)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_artifactAction",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_deterministicArtifactAction",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_forecastConeAfterArtifact",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_forecastConeAfterArtifact_candidate_member",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_forecastConeAfterArtifact_length_le_horizon"]
        (by simp)
        "Artifact action has an Atom-generated SFT input artifact and deterministic keep-carrier update whose after-action cone is the generated carrier ForecastCone witness."
  | .operationPolicyGovernance =>
      atomGeneratedRow
        "sft.operationPolicyGovernance"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .operationPolicyGovernance)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedOperationPolicy",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernanceIntervention",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernance_restrictive",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernance_projects_forecastCone",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernance_keeps_nonConclusion"]
        (by simp)
        "Operation policy and governance have a generated support self-restriction instantiation that projects the generated ForecastCone and preserves policy-pass non-conclusions."
  | .stableRegionReachability =>
      atomGeneratedRow
        "sft.stableRegionReachability"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .stableRegionReachability)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFieldRegion",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedStableRegion",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedMayReach",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedMustReach",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedReachablePreimage"]
        (by simp)
        "Stable-region reachability has generated carrier may-reach, must-reach, stable-region, and reachable-preimage witnesses induced by the generated ForecastCone."
  | .supportSafety =>
      atomGeneratedRow
        "sft.supportSafety"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .supportSafety)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_sftSupportSafetyPackage",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_acceptedSupportedTrajectory",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_supportSafety_forecastCone_and_safety"]
        (by simp)
        "Support safety has an Atom-generated carrier instantiation with a generated identity support operation, accepted supported trajectory, and forecast-cone/safety theorem."
  | .fieldUpdate =>
      atomGeneratedRow
        "sft.fieldUpdate"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .fieldUpdate)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastRecord",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFieldUpdate",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFieldUpdate_sound",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFieldUpdate_records_calibration",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFieldUpdate_records_nonConclusions"]
        (by simp)
        "FieldUpdate has an Atom-generated ForecastCone prior and generated carrier posterior record whose soundness package preserves calibration and non-conclusion boundaries."
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
         "AAT.GeneratedSFTInput.theoremStatusFromGenerated",
         "AAT.GeneratedSFTInput.sft_event_does_not_create_atoms",
         "AAT.GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta_circuitBoundary"]
        (by simp)
        "Generated SFT input computes theorem status from GeneratedArchitectureLawModel, inherits SFT event non-creation from the root AtomAxiomSystem, and uses generated lawfulness for identity circuit-delta boundaries."
  | .archSigReportBoundary =>
      atomGeneratedRow
        "sft.archSigReportBoundary"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .archSigReportBoundary)
        ["GeneratedArchSigAATCoreTransition",
         "GeneratedArchSigAATCoreTransition.ofTransition",
         "GeneratedFieldSigAATCoreTransitionAnalysis",
         "GeneratedArchSigAATCoreTransportTransition",
         "GeneratedArchSigAATCoreTransportTransition.ofTransportTransition"]
        (by simp)
        "ArchSig / FieldSig boundary includes generated preservation and non-identity transport handoff with generated boundary constructors instead of caller-supplied Signature bridge or handoff fields."
  | .counterexamplePackage =>
      atomGeneratedRow
        "sft.counterexamplePackage"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .counterexamplePackage)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_sftCounterexamplePackage",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_sftCounterexamples_record_nonConclusions",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_supportSafety_does_not_discharge_counterexamples"]
        (by simp)
        "SFT counterexamples have a generated support-safety acceptance row that records canonical forbidden readings as non-conclusions instead of discharging them."
  | .theoremRoadmap =>
      atomGeneratedRow
        "sft.theoremRoadmap"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .theoremRoadmap)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_clockedConeDescentPackage",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_clockedConeDescent_forecastCone_descent",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_modularityRepresentationPackage",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_modularity_representation",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_fundamentalModularityTheoremPackage",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_fundamental_modularity",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_fundamental_modularity_nonConclusions"]
        (by simp)
        "The SFT theorem roadmap has generated carrier instances for clocked descent, modularity representation, and fundamental modularity theorem-package acceptance."
  | .finiteExactModel =>
      atomGeneratedRow
        "sft.finiteExactModel"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .finiteExactModel)
        ["AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFiniteExactModel",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFiniteExactModel_indices_selected",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFiniteExactModel_records_exactCover",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFiniteExactModel_records_operation",
         "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFiniteExactModel_records_nonConclusions"]
        (by simp)
        "Finite exact SFT model has a generated carrier singleton-index instantiation with generated support, relation, exact-cover, operation-boundary, and non-conclusion evidence."
  | .aatSupportedFundamentalModularity =>
      atomGeneratedRow
        "sft.aatSupportedFundamentalModularity"
        (SFTTheoremPackages.Candidate.representativeDeclarations
          .aatSupportedFundamentalModularity)
        ["SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInput",
         "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition",
         "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary"]
        (by simp)
        "The AAT-supported SFT boundary has generated handoff constructors that read generated SFT input and generated ArchSig transition evidence before the finite selected final package."

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

def part4Classifications : List TheoremPackageClassification :=
  [ classifyPart4 .distanceFoundation
  , classifyPart4 .distanceAATOverlay
  , classifyPart4 .atomRootGeometry
  , classifyPart4 .atomConfigurationGeometry
  , classifyPart4 .configurationContextGeometry
  , classifyPart4 .signaturePathGeometry
  , classifyPart4 .finiteWitnessInfimumCore
  , classifyPart4 .distanceToLawfulnessGeometry
  , classifyPart4 .metricGaloisCorrespondence
  , classifyPart4 .operationRepairGeometry
  , classifyPart4 .contractiveRepairGeometry
  , classifyPart4 .curvatureFillingGeometry
  , classifyPart4 .curvatureTransportGeometry
  , classifyPart4 .quantitativeHomotopyFillingGeometry
  , classifyPart4 .representationMetric
  , classifyPart4 .representationSpectralStability
  , classifyPart4 .abstractInfimumInterface
  , classifyPart4 .diagnosticConclusionDetail
  , classifyPart4 .docsClassificationBoundary
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

theorem part4_candidates_are_registered
    (candidate : Part4DistanceMeasureGeometry.Candidate) :
    classifyPart4 candidate ∈ part4Classifications := by
  cases candidate <;> simp [part4Classifications]

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
  part4Classifications ++
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

theorem generated_walk_acyclic_law_model_is_not_theorem_package_registry_row :
    "aat.generatedLawModelFromWalkAcyclic" ∉ allPackageIds := by
  native_decide

theorem generated_walk_acyclic_law_model_is_legacy_replaced_surface :
    generatedWalkAcyclicLawModelLegacySurface.IsBridgeAssumptionSurface ∧
    generatedWalkAcyclicLawModelLegacySurface.HasGeneratedReplacement := by
  exact
    ⟨LegacyBridgeSurface.bridge_assumption_surface
        generatedWalkAcyclicLawModelLegacySurface,
      LegacyBridgeSurface.has_generated_replacement
        generatedWalkAcyclicLawModelLegacySurface⟩

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

theorem finite_static_core_is_atom_generated :
    (classifyAATCandidate .finiteStaticStructuralCore).classification =
      .atomGenerated ∧
    (classifyAATCandidate .finiteStaticStructuralCore).action =
      .aatSourceOfTruth := by
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

theorem generated_support_safety_is_atom_generated :
    (classifySFT .supportSafety).classification =
      .atomGenerated ∧
    (classifySFT .supportSafety).action =
      .aatSourceOfTruth := by
  exact ⟨rfl, rfl⟩

theorem generated_sft_projection_cone_is_atom_generated :
    (classifySFT .softwareFieldProjection).classification =
      .atomGenerated ∧
    (classifySFT .forecastConeCore).classification =
      .atomGenerated ∧
    (classifySFT .coneProjection).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl, rfl⟩

theorem generated_sft_action_policy_reachability_is_atom_generated :
    (classifySFT .artifactAction).classification =
      .atomGenerated ∧
    (classifySFT .operationPolicyGovernance).classification =
      .atomGenerated ∧
    (classifySFT .stableRegionReachability).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl, rfl⟩

theorem generated_sft_field_update_is_atom_generated :
    (classifySFT .fieldUpdate).classification =
      .atomGenerated ∧
    (classifySFT .fieldUpdate).action =
      .aatSourceOfTruth := by
  exact ⟨rfl, rfl⟩

theorem generated_sft_finite_exact_model_is_atom_generated :
    (classifySFT .finiteExactModel).classification =
      .atomGenerated ∧
    (classifySFT .finiteExactModel).action =
      .aatSourceOfTruth := by
  exact ⟨rfl, rfl⟩

theorem generated_sft_counterexample_roadmap_is_atom_generated :
    (classifySFT .counterexamplePackage).classification =
      .atomGenerated ∧
    (classifySFT .theoremRoadmap).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl⟩

theorem generated_analytic_representation_is_atom_generated :
    (classifyChapter11 .analyticRepresentation).classification =
      .atomGenerated ∧
    (classifyChapter11 .architectureSignatureRepresentation).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl⟩

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

theorem generated_chapter11_fixture_boundary_is_atom_generated :
    (classifyChapter11 .toolingReportMetadata).classification =
      .atomGenerated ∧
    (classifyChapter11 .couponAnalyticSnapshot).classification =
      .atomGenerated ∧
    (classifyChapter11 .couponHiddenInteractionLiftingBridge).classification =
      .atomGenerated ∧
    (classifyChapter11 .couponStaticExample).classification =
      .atomGenerated ∧
    (classifyChapter11 .couponSemanticValuation).classification =
      .atomGenerated ∧
    (classifyChapter11 .staticSemanticCounterexample).classification =
      .atomGenerated ∧
    (classifyChapter11 .measurementBoundary).classification =
      .atomGenerated := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
