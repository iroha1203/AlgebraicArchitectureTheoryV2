import Formal.Arch.AAT.GeneratedCurvature
import Formal.Arch.AAT.GeneratedSFT
import Formal.Arch.AAT.TheoremClassification
import Formal.Arch.Evolution.SFTArchSigBoundary
import Formal.Arch.Observation.ArchMapGeneratedHandoff

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
core fields can be stated without passing hand-authored law models.  Runtime
rank is stored as a generated certificate, matching the law model's static
`graphRank`, rather than as a raw acyclicity premise.
-/
structure AtomGeneratedAATWorld where
  system : AtomAxiomSystem.{u, v}
  presentation : AtomShapePresentation system
  object : GeneratedArchitectureObject presentation
  lawModel : GeneratedArchitectureLawModel object
  runtimeGraphRank : GeneratedRuntimeGraphRank object
  atomDecidable : DecidableEq system.Atom
  relationDecidable : DecidableRel (GeneratedRelation object)

/-- Generic ArchMap observed-atom handoff into a generated architecture object. -/
def ArchMapGeneratedObjectHandoff
    (world : AtomGeneratedAATWorld.{u, v}) : Prop :=
  ∀ {Source : Type u} {Evidence : Type v}
    {layer : Observation.ArchMapObservationLayer
      world.system Source Evidence}
    {shapePresentation : AtomShapePresentation world.system}
    {selection : Observation.ArchMapObservedAtomSelection
      layer shapePresentation}
    (input :
      Observation.ArchMapGeneratedArchitectureObjectInput selection),
      ∃ object : GeneratedArchitectureObject shapePresentation,
        object = input.toGeneratedArchitectureObject

/-- Suite field payload for generated object carriers and ArchMap handoff. -/
structure GeneratedMoleculeObjectFields
    (world : AtomGeneratedAATWorld.{u, v}) where
  objectCarrierAtomPrimitive :
    ∀ carrier : GeneratedCarrier world.object,
      world.system.Primitive carrier.val
  archMapHandoffToGeneratedObject :
    ArchMapGeneratedObjectHandoff world

/-- Suite field payload for generated relation/runtime graph rank work. -/
structure GeneratedGraphRankFields
    (world : AtomGeneratedAATWorld.{u, v}) where
  relationAtomGeneratesEdge :
    ∀ {relation source target : GeneratedCarrier world.object},
      GeneratedRelationAtom world.object relation source target ->
        (GeneratedArchGraph world.object).edge source target
  runtimeAtomGeneratesEdge :
    ∀ {interaction source target : GeneratedCarrier world.object},
      GeneratedRuntimeRelationAtom world.object interaction source target ->
        (GeneratedRuntimeGraph world.object).edge source target
  relationGraphRank : GeneratedGraphRank world.object
  relationGraphRankWalkAcyclic :
    WalkAcyclic (GeneratedArchGraph world.object)
  runtimeGraphRank : GeneratedRuntimeGraphRank world.object
  runtimeGraphRankWalkAcyclic :
    WalkAcyclic (GeneratedRuntimeGraph world.object)

/--
Suite field payload for generated flatness and shape-coordinate curvature.

This package is relative to the generated world and its generated measurement
universe.  It does not claim global semantic completeness, extractor
completeness, or safety for unmeasured axes.
-/
structure GeneratedFlatnessCurvatureFields
    (world : AtomGeneratedAATWorld.{u, v}) : Prop where
  architectureFlatWithin :
    ArchitectureFlatWithin world.object.generatedFlatnessModel
      world.object.generatedComponentUniverse
  architectureFlat :
    ArchitectureFlat world.object.generatedFlatnessModel
  shapeCoordinateTotalCurvature_eq_zero :
    totalCurvature generatedAtomShapeCoordinateDistance
      world.object.generatedAtomShapeCoordinateSemantics
      world.object.generatedSemanticDiagrams = 0

/-- Generated SFT input specialized to the decidability evidence carried by a world. -/
abbrev GeneratedSFTInputForWorld
    (world : AtomGeneratedAATWorld.{u, v}) : Type _ :=
  @GeneratedSFTInput world.system world.presentation world.object
    world.atomDecidable world.relationDecidable world.lawModel

/--
Suite field payload for the generated SFT / ArchSig / FieldSig handoff.

This field keeps the boundary directional: generated AAT can be read as an SFT
local algebra premise, ArchSig source bridges are computed from generated law
models, and FieldSig consumes the ArchSig transition as analysis input.  It does
not expose forecast correctness as an AAT theorem.
-/
structure GeneratedSFTArchSigFieldSigFields
    (world : AtomGeneratedAATWorld.{u, v}) where
  sftInputToLocalAlgebra :
    ∀ _input : GeneratedSFTInputForWorld world,
      AATCoreLocalAlgebraForSFT world.lawModel.generatedAATCore
  sftInputLocalAlgebraReadsGenerated :
    ∀ input : GeneratedSFTInputForWorld world,
      (sftInputToLocalAlgebra input).usedAsLocalAlgebra
  archsigTransitionSourceBridge :
    ∀ _transition :
      GeneratedArchSigAATCoreTransition world.lawModel world.lawModel,
      ArchitectureSignature.AATCoreSignatureLawfulnessBridge
        world.lawModel.generatedAATCore world.lawModel.toArchitectureLawModel
  fieldSigReadsArchSigTransitionAsSFTAnalysis :
    ∀ {SemanticExpr : Type v} {SemanticObs : Type v}
      {FieldState : Type u}
      {transition :
        GeneratedArchSigAATCoreTransition world.lawModel world.lawModel}
      {report :
        ArchSigSFTReport
          FieldState
          (GeneratedCarrier world.object)
          (GeneratedCarrier world.object)
          GeneratedObservationCoordinate
          SemanticExpr
          SemanticObs}
      {estimate :
        SoftwareFieldEstimate
          FieldState
          (GeneratedCarrier world.object)
          (GeneratedCarrier world.object)
          GeneratedObservationCoordinate
          SemanticExpr
          SemanticObs}
      {forecast : SFTForecastStatus},
      GeneratedFieldSigAATCoreTransitionAnalysis
        transition report estimate forecast ->
        transition.fieldSigAnalysisBoundary
  fieldSigForecastCorrectnessRemainsBoundary :
    ∀ {SemanticExpr : Type v} {SemanticObs : Type v}
      {FieldState : Type u}
      {transition :
        GeneratedArchSigAATCoreTransition world.lawModel world.lawModel}
      {report :
        ArchSigSFTReport
          FieldState
          (GeneratedCarrier world.object)
          (GeneratedCarrier world.object)
          GeneratedObservationCoordinate
          SemanticExpr
          SemanticObs}
      {estimate :
        SoftwareFieldEstimate
          FieldState
          (GeneratedCarrier world.object)
          (GeneratedCarrier world.object)
          GeneratedObservationCoordinate
          SemanticExpr
          SemanticObs}
      {forecast : SFTForecastStatus},
      GeneratedFieldSigAATCoreTransitionAnalysis
        transition report estimate forecast ->
        forecast.RecordsForecastBoundary

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

/-- Static generated graph rank certificate carried by the world's law model. -/
def generated_graph_rank
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedGraphRank world.object :=
  world.lawModel.graphRank

/-- Runtime generated graph rank certificate carried by the generated world. -/
def generated_runtime_graph_rank
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedRuntimeGraphRank world.object :=
  world.runtimeGraphRank

theorem molecule_not_arbitrary_set
    (world : AtomGeneratedAATWorld.{u, v}) :
    world.object.molecule.notArbitrarySet :=
  world.object.molecule.not_arbitrary_set

theorem generated_object_carriers_atom_primitive
    (world : AtomGeneratedAATWorld.{u, v})
    (carrier : GeneratedCarrier world.object) :
    world.system.Primitive carrier.val :=
  world.object.carrier_atom_primitive carrier

theorem archMap_generated_object_handoff
    (world : AtomGeneratedAATWorld.{u, v}) :
    ArchMapGeneratedObjectHandoff world := by
  intro _Source _Evidence _layer _shapePresentation _selection input
  exact ⟨input.toGeneratedArchitectureObject, rfl⟩

/-- Generated object carrier / ArchMap handoff field derived from generated input. -/
def generated_molecule_object_fields
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedMoleculeObjectFields world where
  objectCarrierAtomPrimitive :=
    world.generated_object_carriers_atom_primitive
  archMapHandoffToGeneratedObject :=
    world.archMap_generated_object_handoff

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

theorem generated_graph_rank_walkAcyclic
    (world : AtomGeneratedAATWorld.{u, v}) :
    WalkAcyclic (GeneratedArchGraph world.object) :=
  world.generated_graph_rank.walkAcyclic

theorem generated_runtime_graph_rank_walkAcyclic
    (world : AtomGeneratedAATWorld.{u, v}) :
    WalkAcyclic (GeneratedRuntimeGraph world.object) :=
  world.generated_runtime_graph_rank.walkAcyclic

/-- Generated relation/runtime graph-rank field derived from generated input. -/
def generated_graph_rank_fields
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedGraphRankFields world where
  relationAtomGeneratesEdge := by
    intro relation _source _target hRelation
    exact ⟨relation, hRelation⟩
  runtimeAtomGeneratesEdge := by
    intro interaction _source _target hInteraction
    exact ⟨interaction, hInteraction⟩
  relationGraphRank := world.generated_graph_rank
  relationGraphRankWalkAcyclic := world.generated_graph_rank_walkAcyclic
  runtimeGraphRank := world.generated_runtime_graph_rank
  runtimeGraphRankWalkAcyclic := world.generated_runtime_graph_rank_walkAcyclic

theorem generated_architecture_flat
    (world : AtomGeneratedAATWorld.{u, v}) :
    ArchitectureFlat world.object.generatedFlatnessModel :=
  world.lawModel.generatedArchitectureFlat

theorem generated_shapeCoordinateTotalCurvature_eq_zero
    (world : AtomGeneratedAATWorld.{u, v}) :
    totalCurvature generatedAtomShapeCoordinateDistance
      world.object.generatedAtomShapeCoordinateSemantics
      world.object.generatedSemanticDiagrams = 0 :=
  world.object.generated_shapeCoordinateTotalCurvature_eq_zero

/-- Generated flatness / curvature field derived from generated entrypoints. -/
def generated_flatness_curvature_fields
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedFlatnessCurvatureFields world where
  architectureFlatWithin :=
    world.lawModel.generatedArchitectureFlatWithin
  architectureFlat :=
    world.generated_architecture_flat
  shapeCoordinateTotalCurvature_eq_zero :=
    world.generated_shapeCoordinateTotalCurvature_eq_zero

/-- Generated SFT input induces the SFT local-algebra boundary for this world. -/
def generated_sft_input_toAATCoreLocalAlgebraForSFT
    (world : AtomGeneratedAATWorld.{u, v})
    (input : GeneratedSFTInputForWorld world) :
    AATCoreLocalAlgebraForSFT world.lawModel.generatedAATCore := by
  letI : DecidableEq world.system.Atom := world.atomDecidable
  letI : DecidableRel (GeneratedRelation world.object) :=
    world.relationDecidable
  exact input.toAATCoreLocalAlgebraForSFT

/-- The generated local-algebra boundary reads generated AAT as SFT input. -/
theorem generated_sft_input_localAlgebra_reads_generated
    (world : AtomGeneratedAATWorld.{u, v})
    (input : GeneratedSFTInputForWorld world) :
    (world.generated_sft_input_toAATCoreLocalAlgebraForSFT
      input).usedAsLocalAlgebra := by
  letI : DecidableEq world.system.Atom := world.atomDecidable
  letI : DecidableRel (GeneratedRelation world.object) :=
    world.relationDecidable
  exact input.localAlgebra_reads_generated_aat

/-- Generated ArchSig source bridge computed from the world's law model. -/
noncomputable def generated_archsig_transition_sourceBridge
    (world : AtomGeneratedAATWorld.{u, v})
    (transition :
      GeneratedArchSigAATCoreTransition world.lawModel world.lawModel) :
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge
      world.lawModel.generatedAATCore world.lawModel.toArchitectureLawModel :=
  transition.sourceBridge

/-- FieldSig reads a generated ArchSig transition only as SFT analysis input. -/
theorem generated_fieldsig_reads_archsig_transition_as_sft_analysis
    (world : AtomGeneratedAATWorld.{u, v})
    {SemanticExpr : Type v} {SemanticObs : Type v}
    {FieldState : Type u}
    {transition :
      GeneratedArchSigAATCoreTransition world.lawModel world.lawModel}
    {report :
      ArchSigSFTReport
        FieldState
        (GeneratedCarrier world.object)
        (GeneratedCarrier world.object)
        GeneratedObservationCoordinate
        SemanticExpr
        SemanticObs}
    {estimate :
      SoftwareFieldEstimate
        FieldState
        (GeneratedCarrier world.object)
        (GeneratedCarrier world.object)
        GeneratedObservationCoordinate
        SemanticExpr
        SemanticObs}
    {forecast : SFTForecastStatus}
    (analysis :
      GeneratedFieldSigAATCoreTransitionAnalysis
        transition report estimate forecast) :
    transition.fieldSigAnalysisBoundary :=
  analysis.fieldsig_reads_generated_archsig_transition_as_sft_analysis

/--
Generated FieldSig handoff keeps forecast correctness outside the AAT theorem
suite and records only the selected forecast boundary.
-/
theorem generated_fieldsig_forecast_correctness_remains_boundary
    (world : AtomGeneratedAATWorld.{u, v})
    {SemanticExpr : Type v} {SemanticObs : Type v}
    {FieldState : Type u}
    {transition :
      GeneratedArchSigAATCoreTransition world.lawModel world.lawModel}
    {report :
      ArchSigSFTReport
        FieldState
        (GeneratedCarrier world.object)
        (GeneratedCarrier world.object)
        GeneratedObservationCoordinate
        SemanticExpr
        SemanticObs}
    {estimate :
      SoftwareFieldEstimate
        FieldState
        (GeneratedCarrier world.object)
        (GeneratedCarrier world.object)
        GeneratedObservationCoordinate
        SemanticExpr
        SemanticObs}
    {forecast : SFTForecastStatus}
    (analysis :
      GeneratedFieldSigAATCoreTransitionAnalysis
        transition report estimate forecast) :
    forecast.RecordsForecastBoundary :=
  analysis.forecast_correctness_remains_boundary

/-- Generated SFT / ArchSig / FieldSig handoff field derived from generated input. -/
noncomputable def generated_sft_archsig_fieldsig_fields
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedSFTArchSigFieldSigFields world where
  sftInputToLocalAlgebra :=
    world.generated_sft_input_toAATCoreLocalAlgebraForSFT
  sftInputLocalAlgebraReadsGenerated :=
    world.generated_sft_input_localAlgebra_reads_generated
  archsigTransitionSourceBridge :=
    world.generated_archsig_transition_sourceBridge
  fieldSigReadsArchSigTransitionAsSFTAnalysis := by
    intro _SemanticExpr _SemanticObs _FieldState _transition
      _report _estimate _forecast analysis
    exact
      world.generated_fieldsig_reads_archsig_transition_as_sft_analysis
        analysis
  fieldSigForecastCorrectnessRemainsBoundary := by
    intro _SemanticExpr _SemanticObs _FieldState _transition
      _report _estimate _forecast analysis
    exact
      world.generated_fieldsig_forecast_correctness_remains_boundary
        analysis

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
  generatedMoleculeObject : GeneratedMoleculeObjectFields world
  generatedLawModelLawful :
    ArchitectureSignature.ArchitectureLawful
      world.lawModel.toArchitectureLawModel
  generatedSignatureAxesZero : world.RequiredSignatureAxesZero
  generatedStaticStructuralCore : world.StaticStructuralCore
  generatedGraphRank : GeneratedGraphRankFields world
  generatedAATCoreNoObservationDependency :
    world.GeneratedAATCoreNoObservationDependency
  generatedAATCoreCircuitBoundary :
    world.GeneratedAATCoreCircuitBoundary
  generatedFlatnessCurvature : GeneratedFlatnessCurvatureFields world
  generatedSFTArchSigFieldSig :
    GeneratedSFTArchSigFieldSigFields world
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
      status := .connected
      existingEntrypoints :=
        ["GeneratedArchitectureObject",
         "GeneratedArchitectureObject.carrier_atom_primitive",
         "ArchMapGeneratedArchitectureObjectInput.toGeneratedArchitectureObject",
         "AtomGeneratedAATWorld.generated_object_carriers_atom_primitive",
         "AtomGeneratedAATWorld.archMap_generated_object_handoff"]
      nextWorkPackage :=
        "Preserve generated object carriers and ArchMap handoff as connected suite fields."
      parallelAllowed := true
      coordinationRequired := false
      docsTarget := "docs/aat/lean_theorem_index.md#atom-generated-algebra-kernel" }
  , { family := .generatedGraphRank
      suiteField := "AATTheoremSuite.generatedGraphRank"
      status := .connected
      existingEntrypoints :=
        ["GeneratedRelationAtom",
         "GeneratedRuntimeRelationAtom",
         "AtomGeneratedAATWorld.generated_graph_rank_walkAcyclic",
         "AtomGeneratedAATWorld.generated_runtime_graph_rank_walkAcyclic",
         "GeneratedGraphRank.walkAcyclic",
         "GeneratedRuntimeGraphRank.walkAcyclic"]
      nextWorkPackage :=
        "Preserve relation/runtime generated rank as a connected suite field."
      parallelAllowed := false
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
      status := .connected
      existingEntrypoints :=
        ["GeneratedArchitectureLawModel.generatedArchitectureFlatWithin",
         "GeneratedArchitectureLawModel.generatedArchitectureFlat",
         "GeneratedArchitectureObject.generated_shapeCoordinateTotalCurvature_eq_zero"]
      nextWorkPackage :=
        "Preserve generated flatness / curvature as a bounded generated-world package."
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
      status := .connected
      existingEntrypoints :=
        ["GeneratedSFTInput.toAATCoreLocalAlgebraForSFT",
         "GeneratedArchSigAATCoreTransition.sourceBridge",
         "GeneratedFieldSigAATCoreTransitionAnalysis.fieldsig_reads_generated_archsig_transition_as_sft_analysis",
         "AtomGeneratedAATWorld.generated_sft_input_toAATCoreLocalAlgebraForSFT",
         "AtomGeneratedAATWorld.generated_archsig_transition_sourceBridge",
         "AtomGeneratedAATWorld.generated_fieldsig_reads_archsig_transition_as_sft_analysis"]
      nextWorkPackage :=
        "Preserve generated SFT / ArchSig / FieldSig handoff as a connected suite field."
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
noncomputable def initialTheoremSuite
    (world : AtomGeneratedAATWorld.{u, v}) :
    AATTheoremSuite world where
  atomShapeCompositionKernel :=
    world.molecule_not_arbitrary_set
  generatedMoleculeObject :=
    world.generated_molecule_object_fields
  generatedLawModelLawful :=
    world.generated_lawful
  generatedSignatureAxesZero :=
    world.required_signature_axes_zero
  generatedStaticStructuralCore :=
    world.static_structural_core
  generatedGraphRank :=
    world.generated_graph_rank_fields
  generatedAATCoreNoObservationDependency :=
    world.generated_aat_core_noObservationDependency
  generatedAATCoreCircuitBoundary :=
    world.generated_aat_core_circuitBoundary
  generatedFlatnessCurvature :=
    world.generated_flatness_curvature_fields
  generatedSFTArchSigFieldSig :=
    world.generated_sft_archsig_fieldsig_fields
  classificationRegistryHasNoBridgeAssumedRows :=
    AATReconstructionClassification.theorem_package_registry_has_no_bridge_assumed_rows
  classificationRegistryHasNoRewriteTargets :=
    AATReconstructionClassification.theorem_package_registry_has_no_rewrite_targets
  classificationRegistrySourceRowsAreAtomGenerated :=
    AATReconstructionClassification.theorem_package_registry_source_rows_are_atom_generated
  classificationRegistryRepresentationRowsAreDownstream :=
    AATReconstructionClassification.theorem_package_registry_representation_rows_are_downstream_libraries

/-- Initial complete-formalization coordination object for any generated world. -/
noncomputable def initialCompleteFormalization
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
