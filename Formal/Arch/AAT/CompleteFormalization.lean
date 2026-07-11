import Formal.Arch.AAT.GeneratedCurvature
import Formal.Arch.AAT.GeneratedDiagram
import Formal.Arch.AAT.GeneratedSFT
import Formal.Arch.AAT.GeneratedAnalyticRepresentation
import Formal.Arch.AAT.GeneratedSignature
import Formal.Arch.AAT.GeneratedSynthesis
import Formal.Arch.AAT.TheoremClassification
import Formal.Arch.Evolution.Chapter8HomotopySkeleton
import Formal.Arch.Evolution.Part4DistanceMeasureGeometry
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
  | generatedDistanceMeasureGeometry
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
  deriving DecidableEq, Repr

namespace AATImplementationFrontier

def HasExistingEntrypoints (row : AATImplementationFrontier) : Prop :=
  row.existingEntrypoints ≠ []

def IsConnected (row : AATImplementationFrontier) : Bool :=
  row.status == AATFieldImplementationStatus.connected

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
Suite field payload for generated paths, diagrams, and selected non-fillability.

The package stays relative to generated paths and explicit observation
difference evidence.  It does not claim that arbitrary diagrams are fillable or
non-fillable.
-/
structure GeneratedPathDiagramFields
    (world : AtomGeneratedAATWorld.{u, v}) where
  pathPreservesInvariant :
    ∀ {I : GeneratedCarrier world.object -> Prop}
      {source target : GeneratedCarrier world.object}
      (path : GeneratedArchitecturePath world.object source target),
      ArchitecturePath.InvariantHolds I source ->
      ArchitecturePath.EveryStepPreserves path I ->
        ArchitecturePath.InvariantHolds I
          (ArchitecturePath.ApplyPath source path)
  reflexiveDiagramFiller :
    ∀ {IndependentSquare :
        (W X Y Z : GeneratedCarrier world.object) ->
          GeneratedArchitectureStep world.object W X ->
          GeneratedArchitectureStep world.object X Z ->
          GeneratedArchitectureStep world.object W Y ->
          GeneratedArchitectureStep world.object Y Z -> Prop}
      {SameExternalContract :
        (X Y : GeneratedCarrier world.object) ->
          GeneratedArchitectureStep world.object X Y ->
          GeneratedArchitectureStep world.object X Y -> Prop}
      {RepairFill :
        (X Y : GeneratedCarrier world.object) ->
          GeneratedArchitecturePath world.object X Y ->
          GeneratedArchitecturePath world.object X Y -> Prop}
      {source target : GeneratedCarrier world.object}
      (path : GeneratedArchitecturePath world.object source target),
        GeneratedDiagramFiller
          (object := world.object)
          IndependentSquare SameExternalContract RepairFill
          (GeneratedArchitectureDiagram.reflexive path)
  nonFillabilityWitness :
    ∀ {α : Type (max u v)}
      {IndependentSquare :
        (W X Y Z : GeneratedCarrier world.object) ->
          GeneratedArchitectureStep world.object W X ->
          GeneratedArchitectureStep world.object X Z ->
          GeneratedArchitectureStep world.object W Y ->
          GeneratedArchitectureStep world.object Y Z -> Prop}
      {SameExternalContract :
        (X Y : GeneratedCarrier world.object) ->
          GeneratedArchitectureStep world.object X Y ->
          GeneratedArchitectureStep world.object X Y -> Prop}
      {RepairFill :
        (X Y : GeneratedCarrier world.object) ->
          GeneratedArchitecturePath world.object X Y ->
          GeneratedArchitecturePath world.object X Y -> Prop}
      {Obs :
        {X Y : GeneratedCarrier world.object} ->
          GeneratedArchitecturePath world.object X Y -> α},
      (∀ {W X Y Z T : GeneratedCarrier world.object}
        (a : GeneratedArchitectureStep world.object W X)
        (b : GeneratedArchitectureStep world.object X Z)
        (c : GeneratedArchitectureStep world.object W Y)
        (d : GeneratedArchitectureStep world.object Y Z)
        (rest : GeneratedArchitecturePath world.object Z T),
          IndependentSquare W X Y Z a b c d ->
            Obs (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
              Obs (ArchitecturePath.cons c (ArchitecturePath.cons d rest))) ->
      (∀ {X Y Z : GeneratedCarrier world.object}
        (s t : GeneratedArchitectureStep world.object X Y)
        (rest : GeneratedArchitecturePath world.object Y Z),
          SameExternalContract X Y s t ->
            Obs (ArchitecturePath.cons s rest) =
              Obs (ArchitecturePath.cons t rest)) ->
      (∀ {X Y Z : GeneratedCarrier world.object}
        {p q : GeneratedArchitecturePath world.object X Y},
        RepairFill X Y p q ->
          (suffix : GeneratedArchitecturePath world.object Y Z) ->
            Obs (ArchitecturePath.append p suffix) =
              Obs (ArchitecturePath.append q suffix)) ->
      (∀ {X Y Z : GeneratedCarrier world.object}
        (step : GeneratedArchitectureStep world.object X Y)
        {p q : GeneratedArchitecturePath world.object Y Z},
          Obs p = Obs q ->
            Obs (ArchitecturePath.cons step p) =
              Obs (ArchitecturePath.cons step q)) ->
      ∀ {source target : GeneratedCarrier world.object}
        {diagram : GeneratedArchitectureDiagram world.object
          (source := source) (target := target)}
        {Witness : Type (max u v)} (witness : Witness),
        Obs diagram.lhs ≠ Obs diagram.rhs ->
          GeneratedNonFillabilityWitnessFor
            (object := world.object)
            IndependentSquare SameExternalContract RepairFill diagram witness

/-- Generated identity feature-extension flatness specialized to the world. -/
def GeneratedFeatureExtensionArchitectureFlatWithin
    (world : AtomGeneratedAATWorld.{u, v}) : Prop :=
  ArchitectureFlatWithin
    world.object.generatedIdentityExtensionFlatnessModel
    world.object.generatedIdentityExtensionComponentUniverse

/-- Generated identity split-extension non-conclusion boundary. -/
def GeneratedFeatureExtensionRecordsNonConclusions
    (world : AtomGeneratedAATWorld.{u, v}) : Prop :=
  SplitFeatureExtensionWithinNonConclusions
    world.object.generatedIdentityStaticSplitFeatureExtension
    world.object.generatedIdentityExtensionComponentUniverse

/--
Generated self-view lifting package under the explicit selected feature-step
and interface compatibility assumptions.
-/
def GeneratedSelfSplitExtensionLiftingPreservationPackage
    (world : AtomGeneratedAATWorld.{u, v}) : Prop :=
  ∀ {featureInvariant coreInvariant : GeneratedCarrier world.object -> Prop}
    (featureStep : SelectedFeatureStep.{u} (GeneratedCarrier world.object)),
    LawfulFeatureStep.{u} featureInvariant featureStep ->
    CompatibleWithInterface.{u, u, u, u, u}
      (Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData
        world.object)
      coreInvariant featureStep ->
    ∃ liftedStep : LiftedExtensionStep.{u} (GeneratedCarrier world.object),
      SplitExtensionLiftingPreservationPackage.{u, u, u, u, u}
        (Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData
          world.object)
        featureInvariant coreInvariant featureStep liftedStep

/--
Generated lifting-failure obstruction bridge.

The conclusion stays relative to the selected no-preservation-package premise;
it does not discharge external semantic obstruction from generated flatness.
-/
def GeneratedSelfLiftingFailureExtensionObstructionBridge
    (world : AtomGeneratedAATWorld.{u, v}) : Prop :=
  ∀ {featureInvariant coreInvariant : GeneratedCarrier world.object -> Prop}
    {featureStep : SelectedFeatureStep.{u} (GeneratedCarrier world.object)},
    LawfulFeatureStep.{u} featureInvariant featureStep ->
    (¬ ∃ liftedStep : LiftedExtensionStep.{u} (GeneratedCarrier world.object),
      SplitExtensionLiftingPreservationPackage.{u, u, u, u, u}
        (Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData
          world.object)
        featureInvariant coreInvariant featureStep liftedStep) ->
    ∃ payload :
      LiftingFailureWitnessPayload.{u, u, u, u, u, u, u}
        (Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData
          world.object)
        featureInvariant coreInvariant featureStep,
      ClassifiedAsLiftingFailure.{u, u, u, u, u}
        (Chapter9DiagramFilling.generatedSelfFeatureExtension world.object)
        world.object.generatedIdentityExtensionComponentUniverse
        (liftingFailureExtensionObstructionWitness.{u, u, u, u, u, u, u}
          (Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData
            world.object)
          payload)

/--
Generated identity architecture-extension formula, with witness coverage kept as
an explicit field rather than hidden behind generated flatness.
-/
def GeneratedIdentityArchitectureExtensionFormulaStructural
    (world : AtomGeneratedAATWorld.{u, v}) : Prop :=
  ∀ {Witness : Type (max u v)}
    (witness :
      Chapter10ArchitectureExtensionFormula.GeneratedExtensionObstructionWitness
        world.object Witness),
    ClassifiedAsInheritedCore
        world.object.generatedIdentityFeatureExtension
        world.object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsFeatureLocal
        world.object.generatedIdentityFeatureExtension
        world.object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsInteraction
        world.object.generatedIdentityFeatureExtension
        world.object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsLiftingFailure
        world.object.generatedIdentityFeatureExtension
        world.object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsFillingFailure
        world.object.generatedIdentityFeatureExtension
        world.object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsComplexityTransfer
        world.object.generatedIdentityFeatureExtension
        world.object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsResidualCoverageGap
        world.object.generatedIdentityFeatureExtension
        world.object.generatedIdentityExtensionComponentUniverse
        witness

/--
Suite field payload for generated feature extension, lifting, obstruction, and
extension-formula work.

The package keeps coverage assumptions and non-conclusion boundaries explicit:
lifting is relative to a selected feature step and interface compatibility, and
lifting-failure obstruction is relative to the selected no-preservation-package
premise.
-/
structure GeneratedFeatureExtensionFields
    (world : AtomGeneratedAATWorld.{u, v}) : Prop where
  architectureFlatWithin :
    GeneratedFeatureExtensionArchitectureFlatWithin world
  recordsNonConclusions :
    GeneratedFeatureExtensionRecordsNonConclusions world
  selfPreservesRequiredInvariants :
    (Chapter9DiagramFilling.generatedSelfFeatureExtension
      world.object).preservesRequiredInvariants
  selfInteractionFactorsThroughDeclaredInterfaces :
    (Chapter9DiagramFilling.generatedSelfFeatureExtension
      world.object).interactionFactorsThroughDeclaredInterfaces
  selfCoverageAssumptions :
    (Chapter9DiagramFilling.generatedSelfFeatureExtension
      world.object).coverageAssumptions
  selfProofObligations :
    (Chapter9DiagramFilling.generatedSelfFeatureExtension
      world.object).proofObligations
  selfSplitExtensionLifting :
    GeneratedSelfSplitExtensionLiftingPreservationPackage world
  selfLiftingFailureObstruction :
    GeneratedSelfLiftingFailureExtensionObstructionBridge world
  identityExtensionFormulaStructural :
    GeneratedIdentityArchitectureExtensionFormulaStructural world

/--
Suite field payload for generated flatness and shape-coordinate curvature.

This package is relative to the generated world and its generated measurement
universe. It records only the flatness and curvature fields carried by that
generated Atom-rooted world.
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

/-- Suite field payload for generated operation / repair / synthesis wrappers. -/
structure GeneratedOperationRepairSynthesisFields
    (world : AtomGeneratedAATWorld.{u, v}) where
  operationDoesNotCreateAtoms :
    ∀ {target : GeneratedArchitectureObject world.presentation},
      GeneratedOperation world.object target ->
        world.system.noToolOutputCreatesAtoms
  repairToRepairClearingPackage :
    ∀ {configuration :
        GeneratedRepairProblemConfiguration world.presentation}
      {target : GeneratedArchitectureObject world.presentation},
      (repair : GeneratedRepairFromProblem configuration target) ->
      (targetModel : GeneratedArchitectureLawModel target) ->
        RepairClearingPackage
          targetModel.generatedAATCore
          (Sum
            (GeneratedRepairProblemConfiguration world.presentation)
            (GeneratedArchitectureObject world.presentation))
          Unit
          (Sum.inl configuration)
          (Sum.inr target)
  synthesisToSynthesisSoundnessPackage :
    ∀ {object : GeneratedArchitectureObject world.presentation},
      (candidate : GeneratedSynthesisCandidate object) ->
        SynthesisSoundnessPackage
          candidate.lawModel.generatedAATCore
          (GeneratedSynthesisCandidate object)

/--
Suite field payload for generated Chapter 11 analytic representation packages.

The payload stores the generated representation, selected obstruction
valuation, and identity formula package as downstream representation artifacts
specialized to the Atom-generated world.  It does not promote a representation
row to an AAT source-of-truth row.
-/
structure GeneratedAnalyticRepresentationFields
    (world : AtomGeneratedAATWorld.{u, v}) where
  analyticRepresentation :
    AnalyticRepresentation
      (GeneratedArchitectureLawModel world.object)
      ArchitectureSignature.ArchitectureSignatureV1
      GeneratedAnalyticWitness
  analyticRepresentationCoverage :
    analyticRepresentation.coverageAssumptions
  requiredSignatureObstructionValuation :
    ObstructionValuation
      (GeneratedArchitectureLawModel world.object)
      GeneratedAnalyticWitness
  obstructionValuationCoverage :
    requiredSignatureObstructionValuation.coverageAssumptions
  identityAnalyticExtensionFormulaPackage :
    Chapter11AnalyticRepresentation.AnalyticExtensionFormulaPackage
      (GeneratedArchitectureLawModel world.object)
      ArchitectureSignature.ArchitectureSignatureV1
      Unit
      GeneratedAnalyticWitness
  identityFormulaHolds :
    identityAnalyticExtensionFormulaPackage.FormulaEquation

/--
Suite field payload for Part IV distance / measure geometry.

The field packages the existing Part IV theorem surfaces as generated-world
theorem accessors.  It keeps distance as a selected diagnostic overlay: it
does not generate atoms, does not treat unmeasured axes as zero, and does not
promote recommendations to repair-correctness theorems.
-/
structure GeneratedDistanceMeasureGeometryFields
    (world : AtomGeneratedAATWorld.{u, v}) where
  unmeasuredNotMeasuredZero :
    ¬ DistanceValue.IsMeasuredZero DistanceValue.unmeasured
  rootGeometry :
    ∀ (_ : AtomShape -> Nat)
      (_ : AtomShape -> Nat)
      (_ : AtomShape -> Nat)
      (_ : AtomShape -> Nat)
      (_ : AtomShape -> String),
      Part4DistanceMeasureGeometry.GeneratedAtomRootGeometryPackage
        (GeneratedCarrier world.object)
        GeneratedAtomFullShapeCoordinate
  rootGeometryRecordsBoundaries :
    ∀ (objectSlotFootprint : AtomShape -> Nat)
      (payloadSlotFootprint : AtomShape -> Nat)
      (valencePortFootprint : AtomShape -> Nat)
      (requiredPortFootprint : AtomShape -> Nat)
      (semanticAnchorName : AtomShape -> String),
      (rootGeometry objectSlotFootprint payloadSlotFootprint
        valencePortFootprint requiredPortFootprint semanticAnchorName)
        |>.RecordsGeneratedBoundaries
  signatureDistanceBundleRecordsMeasurementBoundary :
    ∀ {Axis : Type u} (bundle : SignatureDistanceBundle Axis),
      bundle.coverageAssumptions ->
      bundle.aggregationPolicy ->
      bundle.confidenceBoundary ->
      bundle.unmeasuredAxisPolicy ->
      bundle.nonConclusions ->
        bundle.RecordsMeasurementBoundary
  generatedOperationMappedDistanceRecordsBoundaries :
    ∀ {target : GeneratedArchitectureObject world.presentation}
      (operation : GeneratedOperation world.object target)
      (carrier : GeneratedCarrier world.object),
      (Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence
        operation carrier).RecordsGeneratedBoundaries
  generatedRepairProblemMappedDistanceRecordsBoundaries :
    ∀ {configuration :
        GeneratedRepairProblemConfiguration world.presentation}
      {target : GeneratedArchitectureObject world.presentation}
      (operation : GeneratedRepairProblemOperation configuration target)
      (carrier : GeneratedRepairProblemCarrier configuration),
      (Part4DistanceMeasureGeometry.generatedRepairProblemOperation_mappedDistanceEvidence
        operation carrier).RecordsGeneratedBoundaries
  diagnosticConclusionRecordsNonConclusions :
    ∀ {Axis : Type u} (conclusion : BoundedDiagnosticConclusion Axis),
      conclusion.doesNotConcludeGlobalLawfulness ->
      conclusion.doesNotConcludeGlobalFlatness ->
      conclusion.doesNotConcludeUnmeasuredZero ->
        conclusion.RecordsNonConclusions
  detailedDiagnosticRecordsRecommendationBoundary :
    ∀ {Axis : Type u} {DistanceRef : Type v} {Operation : Type u}
      (conclusion :
        DetailedBoundedDiagnosticConclusion Axis DistanceRef Operation),
      conclusion.recommendationBoundary ->
      conclusion.recommendationsAreNotRepairCorrectnessTheorems ->
        conclusion.RecordsRecommendationBoundary
  generatedFillingPackageRecordsBoundaries :
    ∀ {Diagram : Type u} {Filler : Type v}
      (pkg : Part4DistanceMeasureGeometry.GeneratedFillingCostPackage
        Diagram Filler),
      pkg.generatedDiagramEvidence ->
      pkg.finiteFillerUniverse ->
      pkg.lowerBound.nonConclusions ->
      pkg.persistentNonFillability.selectedScope ->
      pkg.persistentNonFillability.nonConclusions ->
      pkg.nonConclusions ->
        pkg.RecordsGeneratedFillingBoundaries
  generatedCurvatureFillingBridgeRecordsBoundaries :
    ∀ {Axis : Type u} {State : Type v}
      {Diagram : Type u} {Filler : Type v}
      (pkg :
        Part4DistanceMeasureGeometry.GeneratedCurvatureFillingBridge
          Axis State Diagram Filler),
      pkg.generatedCurvatureEvidence ->
      pkg.generatedFillingEvidence ->
      pkg.curvatureTransport.selectedScope ->
      pkg.curvatureTransport.nonConclusions ->
      pkg.fillingPackage.RecordsGeneratedFillingBoundaries ->
      pkg.selectedScope ->
      pkg.nonConclusions ->
        pkg.RecordsGeneratedCurvatureFillingBoundaries
  generatedCurvatureFillingBridgeTargetDecreases :
    ∀ {Axis : Type u} {State : Type v}
      {Diagram : Type u} {Filler : Type v}
      (pkg :
        Part4DistanceMeasureGeometry.GeneratedCurvatureFillingBridge
          Axis State Diagram Filler),
      pkg.curvatureTransport.reading.curvatureMass
          pkg.curvatureTransport.targetAxis pkg.curvatureTransport.after <
        pkg.curvatureTransport.reading.curvatureMass
          pkg.curvatureTransport.targetAxis pkg.curvatureTransport.before
  generatedFiniteHomotopyCostRecordsUniverse :
    ∀ {Path : Type u} {Homotopy : Type v}
      (pkg :
        Part4DistanceMeasureGeometry.GeneratedFiniteHomotopyCost
          Path Homotopy),
      pkg.finiteWitnessUniverse ->
      pkg.selectedScope ->
      pkg.homotopyBound.selectedScope ->
      pkg.homotopyBound.nonConclusions ->
      pkg.nonConclusions ->
        pkg.RecordsFiniteWitnessUniverse
  generatedFiniteDehnBoundRecordsUniverse :
    ∀ {Loop : Type u}
      (pkg : Part4DistanceMeasureGeometry.GeneratedFiniteDehnBound Loop),
      pkg.suppliedCandidateUniverse ->
      pkg.dehnBound.selectedScope ->
      pkg.notUniversalDehnFunction ->
      pkg.dehnBound.nonConclusions ->
      pkg.nonConclusions ->
        pkg.RecordsFiniteUniverse
  generatedRepresentationMetricRecordsBoundaries :
    ∀ {State : Type u} {Analytic : Type v} {Spectral : Type u}
      (pkg :
        Part4DistanceMeasureGeometry.GeneratedRepresentationMetricPackage
          State Analytic Spectral),
      pkg.generatedRepresentationEvidence ->
      pkg.selectedObstructionValuationEvidence ->
      pkg.lipschitzPackage.coverageAssumptions ->
      pkg.lipschitzPackage.witnessCompletenessAssumptions ->
      pkg.spectralPackage.coverageAssumptions ->
      pkg.spectralPackage.witnessCompletenessAssumptions ->
      pkg.zeroPreservationBoundary ->
      pkg.zeroReflectionBoundary ->
      pkg.nonConclusions ->
        pkg.RecordsGeneratedMetricBoundaries
  generatedRepresentationMetricAnalyticDistance_le :
    ∀ {State : Type u} {Analytic : Type v} {Spectral : Type u}
      (pkg :
        Part4DistanceMeasureGeometry.GeneratedRepresentationMetricPackage
          State Analytic Spectral)
      {X Y : State},
      pkg.lipschitzPackage.comparable X Y ->
        pkg.lipschitzPackage.analyticDistance
            (pkg.lipschitzPackage.represent X)
            (pkg.lipschitzPackage.represent Y) ≤
          pkg.lipschitzPackage.lipschitzConstant *
            pkg.lipschitzPackage.structuralDistance X Y

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

/-- Generated analytic representation specialized to the world's law model. -/
noncomputable def generated_analyticRepresentation
    (world : AtomGeneratedAATWorld.{u, v}) :
    AnalyticRepresentation
      (GeneratedArchitectureLawModel world.object)
      ArchitectureSignature.ArchitectureSignatureV1
      GeneratedAnalyticWitness := by
  letI : DecidableEq world.system.Atom := world.atomDecidable
  letI : DecidableRel (GeneratedRelation world.object) :=
    world.relationDecidable
  exact GeneratedArchitectureLawModel.generatedAnalyticRepresentation
    (object := world.object)

/-- Generated selected required-Signature obstruction valuation for the world. -/
noncomputable def generated_requiredSignatureObstructionValuation
    (world : AtomGeneratedAATWorld.{u, v}) :
    ObstructionValuation
      (GeneratedArchitectureLawModel world.object)
      GeneratedAnalyticWitness := by
  letI : DecidableEq world.system.Atom := world.atomDecidable
  letI : DecidableRel (GeneratedRelation world.object) :=
    world.relationDecidable
  exact GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation
    (object := world.object)

/-- Generated identity analytic extension formula package for the world's model. -/
noncomputable def generated_identityAnalyticExtensionFormulaPackage
    (world : AtomGeneratedAATWorld.{u, v}) :
    Chapter11AnalyticRepresentation.AnalyticExtensionFormulaPackage
      (GeneratedArchitectureLawModel world.object)
      ArchitectureSignature.ArchitectureSignatureV1
      Unit
      GeneratedAnalyticWitness := by
  letI : DecidableEq world.system.Atom := world.atomDecidable
  letI : DecidableRel (GeneratedRelation world.object) :=
    world.relationDecidable
  exact
    Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormulaPackage
      world.lawModel

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

/-- Generated analytic representation suite field derived from generated input. -/
noncomputable def generated_analyticRepresentation_fields
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedAnalyticRepresentationFields world where
  analyticRepresentation :=
    world.generated_analyticRepresentation
  analyticRepresentationCoverage := by
    letI : DecidableEq world.system.Atom := world.atomDecidable
    letI : DecidableRel (GeneratedRelation world.object) :=
      world.relationDecidable
    exact
      GeneratedArchitectureLawModel.generatedAnalyticRepresentation_coverageAssumptions
        (object := world.object)
  requiredSignatureObstructionValuation :=
    world.generated_requiredSignatureObstructionValuation
  obstructionValuationCoverage := by
    letI : DecidableEq world.system.Atom := world.atomDecidable
    letI : DecidableRel (GeneratedRelation world.object) :=
      world.relationDecidable
    exact
      GeneratedArchitectureLawModel.generatedRequiredSignatureObstructionValuation_coverageAssumptions
        (object := world.object)
  identityAnalyticExtensionFormulaPackage :=
    world.generated_identityAnalyticExtensionFormulaPackage
  identityFormulaHolds := by
    letI : DecidableEq world.system.Atom := world.atomDecidable
    letI : DecidableRel (GeneratedRelation world.object) :=
      world.relationDecidable
    exact
      Chapter11AnalyticRepresentation.generatedIdentityAnalyticExtensionFormula_formula_holds
        world.lawModel

/-- Generated Part IV distance / measure geometry field derived from generated input. -/
def generated_distance_measure_geometry_fields
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedDistanceMeasureGeometryFields world where
  unmeasuredNotMeasuredZero :=
    Part4DistanceMeasureGeometry.unmeasured_not_measured_zero
  rootGeometry := by
    intro objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName
    exact
      Part4DistanceMeasureGeometry.generatedCarrierFullRootGeometryPackage
        world.object objectSlotFootprint payloadSlotFootprint
        valencePortFootprint requiredPortFootprint semanticAnchorName
  rootGeometryRecordsBoundaries := by
    intro objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName
    exact
      Part4DistanceMeasureGeometry.generatedCarrierFullRootGeometryPackage_recordsBoundaries
        world.object objectSlotFootprint payloadSlotFootprint
        valencePortFootprint requiredPortFootprint semanticAnchorName
  signatureDistanceBundleRecordsMeasurementBoundary := by
    intro _Axis bundle hCoverage hAggregation hConfidence hUnmeasured
      hNonConclusions
    exact
      Part4DistanceMeasureGeometry.signatureDistanceBundle_records_measurementBoundary
        bundle hCoverage hAggregation hConfidence hUnmeasured
        hNonConclusions
  generatedOperationMappedDistanceRecordsBoundaries := by
    intro _target operation carrier
    exact
      Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence_recordsGeneratedBoundaries
        operation carrier
  generatedRepairProblemMappedDistanceRecordsBoundaries := by
    intro _configuration _target operation carrier
    exact
      Part4DistanceMeasureGeometry.generatedRepairProblemOperation_mappedDistanceEvidence_recordsGeneratedBoundaries
        operation carrier
  diagnosticConclusionRecordsNonConclusions := by
    intro _Axis conclusion hLaw hFlat hUnmeasured
    exact
      BoundedDiagnosticConclusion.records_nonConclusions
        conclusion hLaw hFlat hUnmeasured
  detailedDiagnosticRecordsRecommendationBoundary := by
    intro _Axis _DistanceRef _Operation conclusion hBoundary hNotTheorem
    exact
      DetailedBoundedDiagnosticConclusion.records_recommendation_boundary
        conclusion hBoundary hNotTheorem
  generatedFillingPackageRecordsBoundaries := by
    intro _Diagram _Filler pkg hDiagram hFinite hLower hScope
      hPersistent hNonConclusions
    exact
      Part4DistanceMeasureGeometry.generatedFillingCostPackage_recordsGeneratedFillingBoundaries
        pkg hDiagram hFinite hLower hScope hPersistent hNonConclusions
  generatedCurvatureFillingBridgeRecordsBoundaries := by
    intro _Axis _State _Diagram _Filler pkg hCurvature hFilling
      hCurvatureScope hCurvatureNonConclusions hFillingBoundaries
      hSelected hNonConclusions
    exact
      Part4DistanceMeasureGeometry.generatedCurvatureFillingBridge_recordsGeneratedCurvatureFillingBoundaries
        pkg hCurvature hFilling hCurvatureScope hCurvatureNonConclusions
        hFillingBoundaries hSelected hNonConclusions
  generatedCurvatureFillingBridgeTargetDecreases := by
    intro _Axis _State _Diagram _Filler pkg
    exact
      Part4DistanceMeasureGeometry.generatedCurvatureFillingBridge_target_curvature_decreases
        pkg
  generatedFiniteHomotopyCostRecordsUniverse := by
    intro _Path _Homotopy pkg hFinite hSelected hBoundSelected
      hBoundNonConclusions hNonConclusions
    exact
      Part4DistanceMeasureGeometry.generatedFiniteHomotopyCost_recordsFiniteWitnessUniverse
        pkg hFinite hSelected hBoundSelected hBoundNonConclusions
        hNonConclusions
  generatedFiniteDehnBoundRecordsUniverse := by
    intro _Loop pkg hUniverse hSelected hNotUniversal
      hBoundNonConclusions hNonConclusions
    exact
      Part4DistanceMeasureGeometry.generatedFiniteDehnBound_recordsFiniteUniverse
        pkg hUniverse hSelected hNotUniversal hBoundNonConclusions
        hNonConclusions
  generatedRepresentationMetricRecordsBoundaries := by
    intro _State _Analytic _Spectral pkg hRepresentation hValuation
      hLipCoverage hLipWitness hSpectralCoverage hSpectralWitness
      hZeroPreservation hZeroReflection hNonConclusions
    exact
      Part4DistanceMeasureGeometry.generatedRepresentationMetricPackage_recordsGeneratedMetricBoundaries
        pkg hRepresentation hValuation hLipCoverage hLipWitness
        hSpectralCoverage hSpectralWitness hZeroPreservation hZeroReflection
        hNonConclusions
  generatedRepresentationMetricAnalyticDistance_le := by
    intro _State _Analytic _Spectral pkg _X _Y hComparable
    exact
      Part4DistanceMeasureGeometry.generatedRepresentationMetricPackage_analyticDistance_le
        pkg hComparable

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

theorem generated_path_preservesInvariant
    (world : AtomGeneratedAATWorld.{u, v})
    {I : GeneratedCarrier world.object -> Prop}
    {source target : GeneratedCarrier world.object}
    (path : GeneratedArchitecturePath world.object source target)
    (hStart : ArchitecturePath.InvariantHolds I source)
    (hEvery : ArchitecturePath.EveryStepPreserves path I) :
    ArchitecturePath.InvariantHolds I
      (ArchitecturePath.ApplyPath source path) :=
  Chapter8HomotopySkeleton.generatedPath_preservesInvariant
    path hStart hEvery

theorem generated_nonFillabilityWitness
    (world : AtomGeneratedAATWorld.{u, v})
    {α : Type (max u v)}
    {IndependentSquare :
      (W X Y Z : GeneratedCarrier world.object) ->
        GeneratedArchitectureStep world.object W X ->
        GeneratedArchitectureStep world.object X Z ->
        GeneratedArchitectureStep world.object W Y ->
        GeneratedArchitectureStep world.object Y Z -> Prop}
    {SameExternalContract :
      (X Y : GeneratedCarrier world.object) ->
        GeneratedArchitectureStep world.object X Y ->
        GeneratedArchitectureStep world.object X Y -> Prop}
    {RepairFill :
      (X Y : GeneratedCarrier world.object) ->
        GeneratedArchitecturePath world.object X Y ->
        GeneratedArchitecturePath world.object X Y -> Prop}
    {Obs :
      {X Y : GeneratedCarrier world.object} ->
        GeneratedArchitecturePath world.object X Y -> α}
    (hIndependentSquare :
      ∀ {W X Y Z T : GeneratedCarrier world.object}
        (a : GeneratedArchitectureStep world.object W X)
        (b : GeneratedArchitectureStep world.object X Z)
        (c : GeneratedArchitectureStep world.object W Y)
        (d : GeneratedArchitectureStep world.object Y Z)
        (rest : GeneratedArchitecturePath world.object Z T),
          IndependentSquare W X Y Z a b c d ->
            Obs (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
              Obs (ArchitecturePath.cons c (ArchitecturePath.cons d rest)))
    (hSameExternalContract :
      ∀ {X Y Z : GeneratedCarrier world.object}
        (s t : GeneratedArchitectureStep world.object X Y)
        (rest : GeneratedArchitecturePath world.object Y Z),
          SameExternalContract X Y s t ->
            Obs (ArchitecturePath.cons s rest) =
              Obs (ArchitecturePath.cons t rest))
    (hRepairFill :
      ∀ {X Y Z : GeneratedCarrier world.object}
        {p q : GeneratedArchitecturePath world.object X Y},
        RepairFill X Y p q ->
          (suffix : GeneratedArchitecturePath world.object Y Z) ->
            Obs (ArchitecturePath.append p suffix) =
              Obs (ArchitecturePath.append q suffix))
    (hConsContext :
      ∀ {X Y Z : GeneratedCarrier world.object}
        (step : GeneratedArchitectureStep world.object X Y)
        {p q : GeneratedArchitecturePath world.object Y Z},
          Obs p = Obs q ->
            Obs (ArchitecturePath.cons step p) =
              Obs (ArchitecturePath.cons step q))
    {source target : GeneratedCarrier world.object}
    {diagram : GeneratedArchitectureDiagram world.object
      (source := source) (target := target)}
    {Witness : Type (max u v)} (witness : Witness)
    (hDifference : Obs diagram.lhs ≠ Obs diagram.rhs) :
    GeneratedNonFillabilityWitnessFor
      (object := world.object)
      IndependentSquare SameExternalContract RepairFill diagram witness :=
  Chapter8HomotopySkeleton.generatedObservationDifference_nonFillabilityWitnessFor
    hIndependentSquare hSameExternalContract hRepairFill hConsContext
    witness hDifference

/-- Generated path / diagram field derived from generated entrypoints. -/
def generated_path_diagram_fields
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedPathDiagramFields world where
  pathPreservesInvariant :=
    world.generated_path_preservesInvariant
  reflexiveDiagramFiller := by
    intro _IndependentSquare _SameExternalContract _RepairFill
      _source _target path
    exact generatedDiagramFiller_refl path
  nonFillabilityWitness :=
    world.generated_nonFillabilityWitness

theorem generated_featureExtension_architectureFlatWithin
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedFeatureExtensionArchitectureFlatWithin world :=
  world.lawModel.generatedFeatureExtension_architectureFlatWithin

theorem generated_featureExtension_recordsNonConclusions
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedFeatureExtensionRecordsNonConclusions world :=
  world.lawModel.generatedSplitFeatureExtension_recordsNonConclusions

theorem generated_selfFeatureExtension_preservesRequiredInvariants
    (world : AtomGeneratedAATWorld.{u, v}) :
    (Chapter9DiagramFilling.generatedSelfFeatureExtension
      world.object).preservesRequiredInvariants :=
  Chapter9DiagramFilling.generatedSelfFeatureExtension_preservesRequiredInvariants
    world.object

theorem generated_selfFeatureExtension_interactionFactorsThroughDeclaredInterfaces
    (world : AtomGeneratedAATWorld.{u, v}) :
    (Chapter9DiagramFilling.generatedSelfFeatureExtension
      world.object).interactionFactorsThroughDeclaredInterfaces :=
  Chapter9DiagramFilling.generatedSelfFeatureExtension_interactionFactorsThroughDeclaredInterfaces
    world.object

theorem generated_selfFeatureExtension_coverageAssumptions
    (world : AtomGeneratedAATWorld.{u, v}) :
    (Chapter9DiagramFilling.generatedSelfFeatureExtension
      world.object).coverageAssumptions :=
  Chapter9DiagramFilling.generatedSelfFeatureExtension_coverageAssumptions
    world.object

theorem generated_selfFeatureExtension_proofObligations
    (world : AtomGeneratedAATWorld.{u, v}) :
    (Chapter9DiagramFilling.generatedSelfFeatureExtension
      world.object).proofObligations :=
  Chapter9DiagramFilling.generatedSelfFeatureExtension_proofObligations
    world.object

theorem generated_selfSplitExtensionLifting_preservationPackage
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedSelfSplitExtensionLiftingPreservationPackage world := by
  intro _featureInvariant _coreInvariant featureStep hLawfulFeatureStep
    hCompatible
  exact
    Chapter9DiagramFilling.generatedSelfSplitExtensionLifting_preservationPackage
      featureStep hLawfulFeatureStep hCompatible

theorem generated_selfLiftingFailureExtensionObstructionWitnessExists
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedSelfLiftingFailureExtensionObstructionBridge world := by
  intro _featureInvariant _coreInvariant _featureStep hLawfulFeatureStep
    hNoPreservationPackage
  exact
    Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage
      hLawfulFeatureStep hNoPreservationPackage

theorem generated_identityArchitectureExtensionFormula_structural
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedIdentityArchitectureExtensionFormulaStructural world := by
  intro _Witness witness
  exact
    Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_structural
      world.object witness

/-- Generated feature-extension field derived from generated entrypoints. -/
def generated_feature_extension_fields
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedFeatureExtensionFields world where
  architectureFlatWithin :=
    world.generated_featureExtension_architectureFlatWithin
  recordsNonConclusions :=
    world.generated_featureExtension_recordsNonConclusions
  selfPreservesRequiredInvariants :=
    world.generated_selfFeatureExtension_preservesRequiredInvariants
  selfInteractionFactorsThroughDeclaredInterfaces :=
    world.generated_selfFeatureExtension_interactionFactorsThroughDeclaredInterfaces
  selfCoverageAssumptions :=
    world.generated_selfFeatureExtension_coverageAssumptions
  selfProofObligations :=
    world.generated_selfFeatureExtension_proofObligations
  selfSplitExtensionLifting :=
    world.generated_selfSplitExtensionLifting_preservationPackage
  selfLiftingFailureObstruction :=
    world.generated_selfLiftingFailureExtensionObstructionWitnessExists
  identityExtensionFormulaStructural :=
    world.generated_identityArchitectureExtensionFormula_structural

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

/-- Generated operations from the world's object do not create Atom existence. -/
theorem generated_operation_does_not_create_atoms
    (world : AtomGeneratedAATWorld.{u, v})
    {target : GeneratedArchitectureObject world.presentation}
    (operation : GeneratedOperation world.object target) :
    world.system.noToolOutputCreatesAtoms :=
  operation.operation_does_not_create_atoms

/--
Generated repairs from a failed atom configuration expose the pure
repair-clearing package over the generated target model.
-/
def generated_repair_toRepairClearingPackage
    (world : AtomGeneratedAATWorld.{u, v})
    {configuration : GeneratedRepairProblemConfiguration world.presentation}
    {target : GeneratedArchitectureObject world.presentation}
    (repair : GeneratedRepairFromProblem configuration target)
    (targetModel : GeneratedArchitectureLawModel target) :
    RepairClearingPackage
      targetModel.generatedAATCore
      (Sum
        (GeneratedRepairProblemConfiguration world.presentation)
        (GeneratedArchitectureObject world.presentation))
      Unit
      (Sum.inl configuration)
      (Sum.inr target) :=
  repair.toRepairClearingPackage targetModel

/--
Generated synthesis candidates expose the pure synthesis-soundness package over
their generated law model.
-/
def generated_synthesis_toSynthesisSoundnessPackage
    (world : AtomGeneratedAATWorld.{u, v})
    {object : GeneratedArchitectureObject world.presentation}
    (candidate : GeneratedSynthesisCandidate object) :
    SynthesisSoundnessPackage
      candidate.lawModel.generatedAATCore
      (GeneratedSynthesisCandidate object) :=
  candidate.toSynthesisSoundnessPackage

/-- Generated operation / repair / synthesis field derived from generated input. -/
def generated_operation_repair_synthesis_fields
    (world : AtomGeneratedAATWorld.{u, v}) :
    GeneratedOperationRepairSynthesisFields world where
  operationDoesNotCreateAtoms :=
    world.generated_operation_does_not_create_atoms
  repairToRepairClearingPackage :=
    world.generated_repair_toRepairClearingPackage
  synthesisToSynthesisSoundnessPackage :=
    world.generated_synthesis_toSynthesisSoundnessPackage

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
  generatedPathDiagram : GeneratedPathDiagramFields world
  generatedFeatureExtension : GeneratedFeatureExtensionFields world
  generatedOperationRepairSynthesis :
    GeneratedOperationRepairSynthesisFields world
  generatedDistanceMeasureGeometry :
    GeneratedDistanceMeasureGeometryFields world
  generatedAnalyticRepresentation :
    GeneratedAnalyticRepresentationFields world
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
  , .generatedDistanceMeasureGeometry
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
      }
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
      }
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
      }
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
      }
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
      }
  , { family := .generatedPathDiagram
      suiteField := "AATTheoremSuite.generatedPathDiagram"
      status := .connected
      existingEntrypoints :=
        ["GeneratedArchitecturePath",
         "GeneratedArchitectureDiagram",
         "GeneratedNonFillabilityWitnessFor",
         "Chapter8HomotopySkeleton.generatedPath_preservesInvariant",
         "AtomGeneratedAATWorld.generated_path_preservesInvariant",
         "AtomGeneratedAATWorld.generated_nonFillabilityWitness"]
      nextWorkPackage :=
        "Preserve generated path, diagram, and selected non-fillability as connected suite fields."
      parallelAllowed := false
      coordinationRequired := false
      }
  , { family := .generatedFeatureExtension
      suiteField := "AATTheoremSuite.generatedFeatureExtension"
      status := .connected
      existingEntrypoints :=
        ["generatedIdentityFeatureExtension",
         "generatedFeatureExtension_architectureFlatWithin",
         "AtomGeneratedAATWorld.generated_featureExtension_architectureFlatWithin",
         "AtomGeneratedAATWorld.generated_selfSplitExtensionLifting_preservationPackage",
         "Chapter9DiagramFilling.generatedSelfSplitExtensionLifting_preservationPackage",
         "Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage",
         "Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_structural"]
      nextWorkPackage :=
        "Preserve explicit feature-extension coverage assumptions, lifting premises, obstruction bridge, and extension-formula boundary as downstream fields are filled."
      parallelAllowed := false
      coordinationRequired := false
      }
  , { family := .generatedOperationRepairSynthesis
      suiteField := "AATTheoremSuite.generatedOperationRepairSynthesis"
      status := .connected
      existingEntrypoints :=
        ["GeneratedOperation.operation_does_not_create_atoms",
         "GeneratedRepairFromProblem.toRepairClearingPackage",
         "GeneratedSynthesisCandidate.toSynthesisSoundnessPackage",
         "AtomGeneratedAATWorld.generated_operation_does_not_create_atoms",
         "AtomGeneratedAATWorld.generated_repair_toRepairClearingPackage",
         "AtomGeneratedAATWorld.generated_synthesis_toSynthesisSoundnessPackage"]
      nextWorkPackage :=
        "Preserve generated operation, repair, and synthesis as connected suite fields."
      parallelAllowed := true
      coordinationRequired := false
      }
  , { family := .generatedDistanceMeasureGeometry
      suiteField := "AATTheoremSuite.generatedDistanceMeasureGeometry"
      status := .connected
      existingEntrypoints :=
        ["Part4DistanceMeasureGeometry.generatedCarrierFullRootGeometryPackage",
         "Part4DistanceMeasureGeometry.generatedCarrierFullRootGeometryPackage_recordsBoundaries",
         "Part4DistanceMeasureGeometry.signatureDistanceBundle_records_measurementBoundary",
         "Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence_recordsGeneratedBoundaries",
         "Part4DistanceMeasureGeometry.generatedRepairProblemOperation_mappedDistanceEvidence_recordsGeneratedBoundaries",
         "Part4DistanceMeasureGeometry.atomGeneratedDiagnostic_supportingDistances_eq",
         "Part4DistanceMeasureGeometry.generatedCurvatureFillingBridge_recordsGeneratedCurvatureFillingBoundaries",
         "Part4DistanceMeasureGeometry.generatedFiniteHomotopyCost_recordsFiniteWitnessUniverse",
         "Part4DistanceMeasureGeometry.generatedFiniteDehnBound_recordsFiniteUniverse",
         "Part4DistanceMeasureGeometry.generatedRepresentationMetricPackage_recordsGeneratedMetricBoundaries"]
      nextWorkPackage :=
        "Preserve Part IV distance / measure geometry as a connected generated theorem-family field."
      parallelAllowed := false
      coordinationRequired := false
      }
  , { family := .generatedAnalyticRepresentation
      suiteField := "AATTheoremSuite.generatedAnalyticRepresentation"
      status := .connected
      existingEntrypoints :=
        ["GeneratedArchitectureLawModel.generatedAnalyticRepresentation",
         "generatedRequiredSignatureObstructionValuation",
         "generatedIdentityAnalyticExtensionFormulaPackage",
         "AtomGeneratedAATWorld.generated_analyticRepresentation",
         "AtomGeneratedAATWorld.generated_requiredSignatureObstructionValuation",
         "AtomGeneratedAATWorld.generated_identityAnalyticExtensionFormulaPackage"]
      nextWorkPackage :=
        "Preserve generated analytic representation, selected valuation, and identity formula package as connected suite fields."
      parallelAllowed := true
      coordinationRequired := false
      }
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
      }
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
      }
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

theorem currentImplementationFrontier_has_no_parallelReady_rows :
    currentImplementationFrontier.all
      (fun row =>
        decide (row.status ≠ AATFieldImplementationStatus.parallelReady)) =
      true := by
  native_decide

theorem currentImplementationFrontier_all_rows_connected :
    currentImplementationFrontier.all
      AATImplementationFrontier.IsConnected = true := by
  native_decide

/--
The first complete-formalization artifact.

The frontier is retained as the completion ledger.  A complete artifact has no
`parallelReady` rows left; every theorem-family row is connected to a suite
field or coordination guard.
-/
structure AATCompleteFormalization where
  world : AtomGeneratedAATWorld.{u, v}
  theoremSuite : AATTheoremSuite world
  implementationFrontier : List AATImplementationFrontier
  frontierCoversFamilies :
    implementationFrontier.map (fun row => row.family) =
      allAATTheoremFamilies

namespace AATCompleteFormalization

def IsComplete (complete : AATCompleteFormalization.{u, v}) : Prop :=
  complete.implementationFrontier.all
    AATImplementationFrontier.IsConnected = true

end AATCompleteFormalization

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
  generatedPathDiagram :=
    world.generated_path_diagram_fields
  generatedFeatureExtension :=
    world.generated_feature_extension_fields
  generatedOperationRepairSynthesis :=
    world.generated_operation_repair_synthesis_fields
  generatedDistanceMeasureGeometry :=
    world.generated_distance_measure_geometry_fields
  generatedAnalyticRepresentation :=
    world.generated_analyticRepresentation_fields
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

theorem initialCompleteFormalization_is_complete
    (world : AtomGeneratedAATWorld.{u, v}) :
    (initialCompleteFormalization world).IsComplete := by
  exact currentImplementationFrontier_all_rows_connected

end AAT
end Formal.Arch
