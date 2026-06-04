import Formal.Arch.AAT.GeneratedSignature
import Formal.Arch.AAT.TheoremClassification

namespace Formal.Arch
namespace AAT

universe u v

/--
The theorem families that make up the Atom-generated AAT completion contract.

This is a coordination surface: sub-agents should receive one constructor or a
small group of constructors and fill the matching suite field, rather than
inventing parallel `Generated*` entrypoints.
-/
inductive AATTheoremFamily where
  | atomShapeCompositionKernel
  | generatedMoleculeObject
  | generatedGraphRank
  | generatedLawSignature
  | generatedFlatnessCurvature
  | generatedPathDiagram
  | generatedFeatureExtension
  | generatedOperationRepairSynthesis
  | generatedAnalyticRepresentation
  | generatedSFTArchSigFieldSig
  | theoremClassification
  deriving DecidableEq, Repr

/-- Current implementation status of a theorem-suite family. -/
inductive AATFieldImplementationStatus where
  | connected
  | parallelReady
  | needsCoreCoordination
  deriving DecidableEq, Repr

/--
Concrete work-package row for the complete-formalization frontier.

`parallelAllowed = true` means a sub-agent may fill this field after the
complete-formalization skeleton is on `main`.  `coordinationRequired = true`
marks fields that must not be changed independently because they define the
shared world or source/downstream split.
-/
structure AATImplementationFrontier where
  family : AATTheoremFamily
  suiteField : String
  status : AATFieldImplementationStatus
  existingEntrypoints : List String
  nextWorkPackage : String
  parallelAllowed : Bool
  coordinationRequired : Bool
  docsTarget : String
  deriving DecidableEq, Repr

namespace AATImplementationFrontier

def HasExistingEntrypoints (row : AATImplementationFrontier) : Prop :=
  row.existingEntrypoints ≠ []

def IsParallelWorkPackage (row : AATImplementationFrontier) : Prop :=
  row.parallelAllowed = true /\ row.coordinationRequired = false

def NeedsCoreCoordination (row : AATImplementationFrontier) : Prop :=
  row.coordinationRequired = true

end AATImplementationFrontier

/--
Shared world read by the complete AAT theorem suite.

The world starts at an Atom root and a shape presentation, then carries the
generated object and law model used by source-of-truth theorem fields.  It
stores decidability instances only so generated Signature and static structural
core fields can be stated without passing hand-authored law models.
-/
structure AtomGeneratedAATWorld where
  system : AtomAxiomSystem.{u, v}
  presentation : AtomShapePresentation system
  object : GeneratedArchitectureObject presentation
  lawModel : GeneratedArchitectureLawModel object
  atomDecidable : DecidableEq system.Atom
  relationDecidable : DecidableRel (GeneratedRelation object)

namespace AtomGeneratedAATWorld

/-- Signature produced from the world's generated law model. -/
def signature (world : AtomGeneratedAATWorld.{u, v}) :
    ArchitectureSignature.ArchitectureSignatureV1 := by
  letI : DecidableEq world.system.Atom := world.atomDecidable
  letI : DecidableRel (GeneratedRelation world.object) :=
    world.relationDecidable
  exact world.lawModel.signatureOfGenerated

/-- Required generated Signature axes are zero for the world's generated model. -/
def RequiredSignatureAxesZero
    (world : AtomGeneratedAATWorld.{u, v}) : Prop :=
  ArchitectureSignature.RequiredSignatureAxesZero world.signature

/-- Static structural core package specialized to the world's generated model. -/
def StaticStructuralCore
    (world : AtomGeneratedAATWorld.{u, v}) : Prop := by
  letI : DecidableEq world.system.Atom := world.atomDecidable
  letI : DecidableRel (GeneratedRelation world.object) :=
    world.relationDecidable
  exact world.lawModel.generatedArchitectureZeroCurvatureTheoremPackage

/-- Generated AATCore observation boundary specialized to the world's model. -/
def GeneratedAATCoreNoObservationDependency
    (world : AtomGeneratedAATWorld.{u, v}) : Prop :=
  world.lawModel.generatedAATCoreNoObservationDependency

/-- Generated AATCore circuit boundary specialized to the world's model. -/
def GeneratedAATCoreCircuitBoundary
    (world : AtomGeneratedAATWorld.{u, v}) : Prop :=
  world.lawModel.generatedAATCoreCircuitBoundary

theorem molecule_not_arbitrary_set
    (world : AtomGeneratedAATWorld.{u, v}) :
    world.object.molecule.notArbitrarySet :=
  world.object.molecule.not_arbitrary_set

theorem generated_lawful
    (world : AtomGeneratedAATWorld.{u, v}) :
    ArchitectureSignature.ArchitectureLawful
      world.lawModel.toArchitectureLawModel :=
  world.lawModel.generatedArchitectureLawful

theorem required_signature_axes_zero
    (world : AtomGeneratedAATWorld.{u, v}) :
    world.RequiredSignatureAxesZero := by
  simp [RequiredSignatureAxesZero, signature]
  letI : DecidableEq world.system.Atom := world.atomDecidable
  letI : DecidableRel (GeneratedRelation world.object) :=
    world.relationDecidable
  exact world.lawModel.generated_requiredSignatureAxesZero

theorem static_structural_core
    (world : AtomGeneratedAATWorld.{u, v}) :
    world.StaticStructuralCore := by
  simp [StaticStructuralCore]
  letI : DecidableEq world.system.Atom := world.atomDecidable
  letI : DecidableRel (GeneratedRelation world.object) :=
    world.relationDecidable
  exact world.lawModel.generatedArchitectureZeroCurvatureTheoremPackage_holds

theorem generated_aat_core_noObservationDependency
    (world : AtomGeneratedAATWorld.{u, v}) :
    world.GeneratedAATCoreNoObservationDependency :=
  world.lawModel.generatedAATCoreNoObservationDependency_recorded

theorem generated_aat_core_circuitBoundary
    (world : AtomGeneratedAATWorld.{u, v}) :
    world.GeneratedAATCoreCircuitBoundary :=
  world.lawModel.generatedAATCoreCircuitBoundary_recorded

end AtomGeneratedAATWorld

/--
Initial top-level suite for the complete formalization effort.

This skeleton intentionally connects only the stable core fields that are
already proved from generated input.  The remaining families are tracked in
`AATImplementationFrontier` so parallel sub-agents know exactly which suite
field they are filling.
-/
structure AATTheoremSuite (world : AtomGeneratedAATWorld.{u, v}) where
  atomShapeCompositionKernel : world.object.molecule.notArbitrarySet
  generatedLawModelLawful :
    ArchitectureSignature.ArchitectureLawful
      world.lawModel.toArchitectureLawModel
  generatedSignatureAxesZero : world.RequiredSignatureAxesZero
  generatedStaticStructuralCore : world.StaticStructuralCore
  generatedAATCoreNoObservationDependency :
    world.GeneratedAATCoreNoObservationDependency
  generatedAATCoreCircuitBoundary :
    world.GeneratedAATCoreCircuitBoundary
  classificationRegistryHasNoBridgeAssumedRows :
    AATReconstructionClassification.TheoremPackageClass.bridgeAssumed ∉
      AATReconstructionClassification.allClassificationClasses
  classificationRegistryHasNoRewriteTargets :
    AATReconstructionClassification.ReconstructionAction.rewriteTarget ∉
      AATReconstructionClassification.allClassificationActions
  classificationRegistrySourceRowsAreAtomGenerated :
    ∀ classAction ∈
      AATReconstructionClassification.allClassificationClassActions,
      classAction.2 =
        AATReconstructionClassification.ReconstructionAction.aatSourceOfTruth ->
        classAction.1 =
          AATReconstructionClassification.TheoremPackageClass.atomGenerated
  classificationRegistryRepresentationRowsAreDownstream :
    ∀ classAction ∈
      AATReconstructionClassification.allClassificationClassActions,
      classAction.1 =
        AATReconstructionClassification.TheoremPackageClass.representationLevel ->
        classAction.2 =
          AATReconstructionClassification.ReconstructionAction.downstreamLibrary

/-- Canonical theorem-family order used by the current frontier. -/
def allAATTheoremFamilies : List AATTheoremFamily :=
  [ .atomShapeCompositionKernel
  , .generatedMoleculeObject
  , .generatedGraphRank
  , .generatedLawSignature
  , .generatedFlatnessCurvature
  , .generatedPathDiagram
  , .generatedFeatureExtension
  , .generatedOperationRepairSynthesis
  , .generatedAnalyticRepresentation
  , .generatedSFTArchSigFieldSig
  , .theoremClassification
  ]

/-- Current complete-formalization work packages after the generated-kernel PR. -/
def currentImplementationFrontier : List AATImplementationFrontier :=
  [ { family := .atomShapeCompositionKernel
      suiteField := "AATTheoremSuite.atomShapeCompositionKernel"
      status := .connected
      existingEntrypoints :=
        ["GeneratedMolecule.not_arbitrary_set",
         "GeneratedMolecule.incompatible_slots_not_generatedMolecule",
         "GeneratedMolecule.missing_required_port_not_generatedMolecule"]
      nextWorkPackage := "Preserve this kernel as a shared prerequisite."
      parallelAllowed := false
      coordinationRequired := true
      docsTarget := "docs/aat/lean_theorem_index.md#atom-generated-algebra-kernel" }
  , { family := .generatedMoleculeObject
      suiteField := "AATTheoremSuite.generatedMoleculeObject"
      status := .parallelReady
      existingEntrypoints :=
        ["GeneratedArchitectureObject",
         "GeneratedArchitectureObject.carrier_atom_primitive",
         "ArchMapGeneratedArchitectureObjectInput.toGeneratedArchitectureObject"]
      nextWorkPackage :=
        "Add suite fields for generated object carriers and ArchMap handoff."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#atom-generated-algebra-kernel" }
  , { family := .generatedGraphRank
      suiteField := "AATTheoremSuite.generatedGraphRank"
      status := .parallelReady
      existingEntrypoints :=
        ["GeneratedRelationAtom",
         "GeneratedRuntimeRelationAtom",
         "GeneratedGraphRank.walkAcyclic",
         "GeneratedRuntimeGraphRank.walkAcyclic"]
      nextWorkPackage :=
        "Add suite fields for relation/runtime edges and rank certificates."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#atom-generated-algebra-kernel" }
  , { family := .generatedLawSignature
      suiteField :=
        "AATTheoremSuite.generatedLawModelLawful / generatedSignatureAxesZero / generatedStaticStructuralCore / generatedAATCoreNoObservationDependency / generatedAATCoreCircuitBoundary"
      status := .connected
      existingEntrypoints :=
        ["GeneratedArchitectureLawModel.generatedArchitectureLawful",
         "GeneratedArchitectureLawModel.generated_requiredSignatureAxesZero",
         "GeneratedArchitectureLawModel.generatedArchitectureZeroCurvatureTheoremPackage_holds",
         "GeneratedArchitectureLawModel.generatedAATCoreNoObservationDependency_recorded",
         "GeneratedArchitectureLawModel.generatedAATCoreCircuitBoundary_recorded"]
      nextWorkPackage :=
        "Preserve the connected generated law / Signature / AATCore bridge fields as later suite families are filled."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#atom-generated-algebra-kernel" }
  , { family := .generatedFlatnessCurvature
      suiteField := "AATTheoremSuite.generatedFlatnessCurvature"
      status := .parallelReady
      existingEntrypoints :=
        ["GeneratedArchitectureLawModel.generatedArchitectureFlatWithin",
         "GeneratedArchitectureLawModel.generatedArchitectureFlat",
         "GeneratedArchitectureObject.generated_shapeCoordinateTotalCurvature_eq_zero"]
      nextWorkPackage :=
        "Add suite fields for generated flatness and curvature."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#atom-generated-algebra-kernel" }
  , { family := .generatedPathDiagram
      suiteField := "AATTheoremSuite.generatedPathDiagram"
      status := .parallelReady
      existingEntrypoints :=
        ["GeneratedArchitecturePath",
         "GeneratedArchitectureDiagram",
         "GeneratedNonFillabilityWitnessFor",
         "Chapter8HomotopySkeleton.generatedPath_preservesInvariant"]
      nextWorkPackage :=
        "Add suite fields for generated path, diagram, and non-fillability."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#chapter-8-homotopy-skeleton-entrypoint" }
  , { family := .generatedFeatureExtension
      suiteField := "AATTheoremSuite.generatedFeatureExtension"
      status := .parallelReady
      existingEntrypoints :=
        ["generatedIdentityFeatureExtension",
         "generatedFeatureExtension_architectureFlatWithin",
         "Chapter9DiagramFilling.generatedSelfSplitExtensionLifting_preservationPackage"]
      nextWorkPackage :=
        "Add suite fields for generated feature extension and lifting bridges."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#chapter-9-diagram-filling-entrypoint" }
  , { family := .generatedOperationRepairSynthesis
      suiteField := "AATTheoremSuite.generatedOperationRepairSynthesis"
      status := .parallelReady
      existingEntrypoints :=
        ["GeneratedOperation.operation_does_not_create_atoms",
         "GeneratedRepairFromProblem.toRepairClearingPackage",
         "GeneratedSynthesisCandidate.toSynthesisSoundnessPackage"]
      nextWorkPackage :=
        "Add suite fields for generated operation, repair, and synthesis."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#chapter-7-theorem-package-entrypoints" }
  , { family := .generatedAnalyticRepresentation
      suiteField := "AATTheoremSuite.generatedAnalyticRepresentation"
      status := .parallelReady
      existingEntrypoints :=
        ["GeneratedArchitectureLawModel.generatedAnalyticRepresentation",
         "generatedRequiredSignatureObstructionValuation",
         "generatedIdentityAnalyticExtensionFormulaPackage"]
      nextWorkPackage :=
        "Add suite fields for generated analytic representation and valuation."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#atom-generated-algebra-kernel" }
  , { family := .generatedSFTArchSigFieldSig
      suiteField := "AATTheoremSuite.generatedSFTArchSigFieldSig"
      status := .parallelReady
      existingEntrypoints :=
        ["GeneratedSFTInput.toAATCoreLocalAlgebraForSFT",
         "GeneratedArchSigAATCoreTransition.sourceBridge",
         "GeneratedFieldSigAATCoreTransitionAnalysis.fieldsig_reads_generated_archsig_transition_as_sft_analysis"]
      nextWorkPackage :=
        "Add suite fields for SFT, ArchSig, and FieldSig handoff."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#atom-generated-algebra-kernel" }
  , { family := .theoremClassification
      suiteField :=
        "AATTheoremSuite.classificationRegistryHasNoBridgeAssumedRows / classificationRegistryHasNoRewriteTargets"
      status := .connected
      existingEntrypoints :=
        ["theorem_package_registry_has_no_bridge_assumed_rows",
         "theorem_package_registry_has_no_rewrite_targets",
         "theorem_package_registry_source_rows_are_atom_generated",
         "theorem_package_registry_representation_rows_are_downstream_libraries"]
      nextWorkPackage :=
        "Keep registry audit synchronized as suite fields are filled."
      parallelAllowed := false
      coordinationRequired := true
      docsTarget := "docs/aat/lean_theorem_index.md#atom-generated-algebra-kernel" }
  ]

def currentImplementationFamilies : List AATTheoremFamily :=
  currentImplementationFrontier.map (fun row => row.family)

theorem currentImplementationFrontier_covers_all_families :
    currentImplementationFamilies = allAATTheoremFamilies := by
  native_decide

theorem connected_frontier_rows_have_existing_entrypoints :
    currentImplementationFrontier.all
      (fun row =>
        if row.status = AATFieldImplementationStatus.connected then
          decide (row.existingEntrypoints ≠ [])
        else
          true) = true := by
  native_decide

theorem parallel_frontier_rows_are_not_core_coordination :
    currentImplementationFrontier.all
      (fun row =>
        if row.parallelAllowed = true then
          decide (row.coordinationRequired = false)
        else
          true) = true := by
  native_decide

/--
The first complete-formalization artifact.

Future PRs should reduce the frontier by adding fields to `AATTheoremSuite` and
replacing `parallelReady` rows with connected theorem fields.
-/
structure AATCompleteFormalization where
  world : AtomGeneratedAATWorld.{u, v}
  theoremSuite : AATTheoremSuite world
  implementationFrontier : List AATImplementationFrontier
  frontierCoversFamilies :
    implementationFrontier.map (fun row => row.family) =
      allAATTheoremFamilies

/-- Initial theorem suite obtained from existing generated law/signature proofs. -/
def initialTheoremSuite
    (world : AtomGeneratedAATWorld.{u, v}) :
    AATTheoremSuite world where
  atomShapeCompositionKernel :=
    world.molecule_not_arbitrary_set
  generatedLawModelLawful :=
    world.generated_lawful
  generatedSignatureAxesZero :=
    world.required_signature_axes_zero
  generatedStaticStructuralCore :=
    world.static_structural_core
  generatedAATCoreNoObservationDependency :=
    world.generated_aat_core_noObservationDependency
  generatedAATCoreCircuitBoundary :=
    world.generated_aat_core_circuitBoundary
  classificationRegistryHasNoBridgeAssumedRows :=
    AATReconstructionClassification.theorem_package_registry_has_no_bridge_assumed_rows
  classificationRegistryHasNoRewriteTargets :=
    AATReconstructionClassification.theorem_package_registry_has_no_rewrite_targets
  classificationRegistrySourceRowsAreAtomGenerated :=
    AATReconstructionClassification.theorem_package_registry_source_rows_are_atom_generated
  classificationRegistryRepresentationRowsAreDownstream :=
    AATReconstructionClassification.theorem_package_registry_representation_rows_are_downstream_libraries

/-- Initial complete-formalization coordination object for any generated world. -/
def initialCompleteFormalization
    (world : AtomGeneratedAATWorld.{u, v}) :
    AATCompleteFormalization where
  world := world
  theoremSuite := initialTheoremSuite world
  implementationFrontier := currentImplementationFrontier
  frontierCoversFamilies := currentImplementationFrontier_covers_all_families

theorem initialCompleteFormalization_frontier_covers_all_families
    (world : AtomGeneratedAATWorld.{u, v}) :
    (initialCompleteFormalization world).implementationFrontier.map
        (fun row => row.family) =
      allAATTheoremFamilies :=
  (initialCompleteFormalization world).frontierCoversFamilies

end AAT
end Formal.Arch
