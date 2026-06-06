import Formal.Arch.Evolution.Part4DistanceMeasureGeometry
import Formal.Arch.Examples.AtomGeneratedMoleculeExamples
import Formal.Arch.Examples.AtomGeneratedRepairExamples

/-!
Concrete examples for the AAT Part IV distance / measure geometry package.

The examples are intentionally tiny selected scopes.  They exercise the public
entrypoint without claiming real-world metric calibration, solver completeness,
or global repair correctness.
-/

namespace Formal.Arch
namespace AATPart4DistanceExamples

inductive Axis where
  | runtime
  | deployment
  deriving DecidableEq, Repr

inductive ExampleState where
  | source
  | middle
  | target
  deriving DecidableEq, Repr

inductive ExampleOperation where
  | attachGuard
  | rewriteContract
  deriving DecidableEq, Repr

inductive Route where
  | short
  | long
  deriving DecidableEq, Repr

inductive ExampleFiller where
  | selected
  deriving DecidableEq, Repr

inductive ExampleHomotopy where
  | contract
  deriving DecidableEq, Repr

inductive ExampleLoop where
  | boundary
  deriving DecidableEq, Repr

def selectedProfile : DistanceProfile where
  atomWeightPolicy := True
  signatureWeightPolicy := True
  operationCostPolicy := True
  aggregationPolicy := True
  unmeasuredAxisPolicy := True
  lawOverlayBoundary := True
  nonConclusions := True

def selectedScope : SelectedDistanceScope Axis where
  profile := selectedProfile
  measuredAxis := fun axis => axis = Axis.runtime
  unmeasuredAxis := fun axis => axis = Axis.deployment
  selectedCoverage := True
  witnessPolicy := True
  nonConclusions := True

theorem unmeasured_axis_is_not_measured_zero :
    ¬ DistanceValue.IsMeasuredZero DistanceValue.unmeasured :=
  Part4DistanceMeasureGeometry.unmeasured_not_measured_zero

def signatureDistanceBundle : SignatureDistanceBundle Axis where
  profile := selectedProfile
  selectedAxes := [Axis.runtime, Axis.deployment]
  axisDistance := fun
    | Axis.runtime => DistanceValue.measured 3
    | Axis.deployment => DistanceValue.unmeasured
  measuredAxis := fun axis => axis = Axis.runtime
  unmeasuredAxis := fun axis => axis = Axis.deployment
  unavailableAxis := fun _axis => False
  incomparableAxis := fun _axis => False
  coverageAssumptions := True
  aggregationPolicy := True
  confidenceBoundary := True
  unmeasuredAxisPolicy := True
  doesNotConcludeGlobalLawfulness := True
  doesNotConcludeGlobalFlatness := True
  doesNotConcludeUnmeasuredZero := True
  nonConclusions := True

theorem signatureDistanceBundle_runtime_payload :
    signatureDistanceBundle.measuredPayload? Axis.runtime = some 3 :=
  Part4DistanceMeasureGeometry.signatureDistanceBundle_measuredPayload_measured
    signatureDistanceBundle rfl

theorem signatureDistanceBundle_measuredSubtotal_eq_three :
    signatureDistanceBundle.measuredSubtotal = 3 := by
  rfl

theorem signatureDistanceBundle_deployment_not_measuredPayload
    (n : Nat) :
    signatureDistanceBundle.measuredPayload? Axis.deployment ≠ some n :=
  Part4DistanceMeasureGeometry.signatureDistanceBundle_unmeasuredAxis_not_measuredPayload
    signatureDistanceBundle rfl n

theorem signatureDistanceBundle_deployment_not_measuredZero :
    ¬ DistanceValue.IsMeasuredZero
      (signatureDistanceBundle.axisDistance Axis.deployment) :=
  Part4DistanceMeasureGeometry.signatureDistanceBundle_unmeasuredAxis_not_measuredZero
    signatureDistanceBundle rfl

theorem signatureDistanceBundle_records_measurementBoundary :
    signatureDistanceBundle.RecordsMeasurementBoundary :=
  Part4DistanceMeasureGeometry.signatureDistanceBundle_records_measurementBoundary
    signatureDistanceBundle trivial trivial trivial trivial trivial

def diagnosticConclusion : BoundedDiagnosticConclusion Axis where
  scope := selectedScope
  value := fun
    | Axis.runtime => DistanceValue.measured 3
    | Axis.deployment => DistanceValue.unmeasured
  selectedConclusion := True
  doesNotConcludeGlobalLawfulness := True
  doesNotConcludeGlobalFlatness := True
  doesNotConcludeUnmeasuredZero := True

def detailedDiagnostic :
    DetailedBoundedDiagnosticConclusion Axis Axis ExampleOperation where
  base := diagnosticConclusion
  supportingDistances := [Axis.runtime]
  recommendedOperations := [ExampleOperation.attachGuard]
  supportingDistanceScope := True
  recommendationBoundary := True
  recommendationsAreNotRepairCorrectnessTheorems := True
  nonConclusions := True

theorem detailedDiagnostic_records_recommendation_boundary :
    detailedDiagnostic.RecordsRecommendationBoundary :=
  Part4DistanceMeasureGeometry.detailedDiagnostic_records_recommendation_boundary
    detailedDiagnostic trivial trivial

def observation : SignatureObservation ExampleState Nat where
  observe := fun
    | ExampleState.source => 0
    | ExampleState.middle => 2
    | ExampleState.target => 1
  coverageAssumptions := True
  nonConclusions := True

def signatureDistanceSchema :
    SignatureDistanceSchema ExampleState Nat where
  observation := observation
  distance := fun _left _right => 0
  self_zero := by
    intro _sig
    rfl
  triangle := by
    intro _a _b _c
    simp
  measuredScope := True
  nonConclusions := True

def repairStep :
    ArchitectureTransition ExampleState ExampleState.source
      ExampleState.target where
  kind := ArchitectureTransitionKind.repair
  lawful := True
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions := True

def repairPath :
    ArchitectureEvolution ExampleState ExampleState.source
      ExampleState.target :=
  ArchitecturePath.cons repairStep (ArchitecturePath.nil ExampleState.target)

theorem signatureEndpointDistance_le_pathLength :
    signatureDistanceSchema.endpointDistance repairPath ≤
      signatureDistanceSchema.pathLength repairPath :=
  Part4DistanceMeasureGeometry.signatureEndpointDistance_le_pathLength
    signatureDistanceSchema repairPath

theorem signaturePathLength_append_repair_nil :
    signatureDistanceSchema.pathLength
        (ArchitecturePath.append repairPath
          (ArchitecturePath.nil ExampleState.target)) =
      signatureDistanceSchema.pathLength repairPath +
        signatureDistanceSchema.pathLength
          (ArchitecturePath.nil ExampleState.target) :=
  Part4DistanceMeasureGeometry.signaturePathLength_append
    signatureDistanceSchema repairPath
      (ArchitecturePath.nil ExampleState.target)

theorem signatureHiddenExcursion_zero_of_exact_path :
    signatureDistanceSchema.hiddenExcursion repairPath = 0 :=
  Part4DistanceMeasureGeometry.signatureHiddenExcursion_zero_of_endpointDistance_eq_pathLength
    signatureDistanceSchema repairPath rfl

def boundedRepair : BoundedSideEffectRepair ExampleState where
  source := ExampleState.source
  target := ExampleState.target
  targetDistance := fun
    | ExampleState.source => 4
    | ExampleState.middle => 2
    | ExampleState.target => 1
  protectedMovement := fun _ _ => 1
  epsilon := 2
  targetDistanceDecreases := by
    decide
  protectedMovementWithinBound := by
    decide
  nonConclusions := True

theorem boundedRepair_target_decreases :
    boundedRepair.targetDistance boundedRepair.target <
      boundedRepair.targetDistance boundedRepair.source :=
  Part4DistanceMeasureGeometry.boundedSideEffectRepair_targetDistance_decreases
    boundedRepair

def routeCost : Route -> Nat
  | Route.short => 1
  | Route.long => 3

def selectedRoute (_route : Route) : Prop :=
  True

def routeOptimum : SelectedFiniteOptimum Route where
  candidates := [Route.short, Route.long]
  selected := selectedRoute
  cost := routeCost
  optimal := Route.short
  optimal_mem := by simp
  optimal_selected := trivial
  cost_le_of_mem_selected := by
    intro candidate hMem _hSelected
    simp [routeCost] at hMem ⊢
    rcases hMem with hShort | hLong
    · cases hShort
      simp
    · cases hLong
      simp
  nonConclusions := True

theorem routeOptimum_noRouteBelow :
    NoRouteBelow routeOptimum.candidates routeOptimum.selected
      routeOptimum.cost routeOptimum.lowerBound :=
  Part4DistanceMeasureGeometry.noRouteBelow_of_selected_lowerBound
    routeOptimum.lowerBound_for_selected_candidates

def lipschitzRepresentation :
    LipschitzRepresentation ExampleState Nat where
  represent := fun
    | ExampleState.source => 0
    | ExampleState.middle => 1
    | ExampleState.target => 1
  structuralDistance := fun _ _ => 0
  analyticDistance := fun _ _ => 0
  comparable := fun _ _ => True
  lipschitzConstant := 2
  lipschitz := by
    intro _ _ _hComparable
    simp
  coverageAssumptions := True
  witnessCompletenessAssumptions := True
  nonConclusions := True

theorem lipschitzRepresentation_bound :
    lipschitzRepresentation.analyticDistance
        (lipschitzRepresentation.represent ExampleState.source)
        (lipschitzRepresentation.represent ExampleState.target) ≤
      lipschitzRepresentation.lipschitzConstant *
        lipschitzRepresentation.structuralDistance
          ExampleState.source ExampleState.target :=
  Part4DistanceMeasureGeometry.lipschitzRepresentation_analyticDistance_le
    lipschitzRepresentation trivial

def spectralStability :
    SpectralStabilityPackage ExampleState Nat where
  represent := fun
    | ExampleState.source => 0
    | ExampleState.middle => 1
    | ExampleState.target => 1
  structuralDistance := fun _ _ => 0
  spectralDistance := fun _ _ => 0
  source := ExampleState.source
  target := ExampleState.target
  epsilon := 0
  lipschitzConstant := 2
  structuralWithin := by simp
  spectralBound := by simp
  coverageAssumptions := True
  witnessCompletenessAssumptions := True
  nonConclusions := True

theorem spectralStability_bound :
    spectralStability.spectralDistance
        (spectralStability.represent spectralStability.source)
        (spectralStability.represent spectralStability.target) ≤
      spectralStability.lipschitzConstant * spectralStability.epsilon :=
  Part4DistanceMeasureGeometry.spectralStabilityPackage_spectralDistance_le
    spectralStability

def representationMetricPackage :
    Part4DistanceMeasureGeometry.GeneratedRepresentationMetricPackage
      ExampleState Nat Nat where
  lipschitzPackage := lipschitzRepresentation
  spectralPackage := spectralStability
  generatedRepresentationEvidence := True
  selectedObstructionValuationEvidence := True
  zeroPreservationBoundary := True
  zeroReflectionBoundary := True
  nonConclusions := True

theorem representationMetricPackage_recordsBoundaries :
    representationMetricPackage.RecordsGeneratedMetricBoundaries :=
  Part4DistanceMeasureGeometry.generatedRepresentationMetricPackage_recordsGeneratedMetricBoundaries
    representationMetricPackage
    trivial trivial trivial trivial trivial trivial trivial trivial trivial

theorem representationMetricPackage_analytic_bound :
    representationMetricPackage.lipschitzPackage.analyticDistance
        (representationMetricPackage.lipschitzPackage.represent ExampleState.source)
        (representationMetricPackage.lipschitzPackage.represent ExampleState.target) ≤
      representationMetricPackage.lipschitzPackage.lipschitzConstant *
        representationMetricPackage.lipschitzPackage.structuralDistance
          ExampleState.source ExampleState.target :=
  Part4DistanceMeasureGeometry.generatedRepresentationMetricPackage_analyticDistance_le
    representationMetricPackage trivial

theorem representationMetricPackage_spectral_bound :
    representationMetricPackage.spectralPackage.spectralDistance
        (representationMetricPackage.spectralPackage.represent
          representationMetricPackage.spectralPackage.source)
        (representationMetricPackage.spectralPackage.represent
          representationMetricPackage.spectralPackage.target) ≤
      representationMetricPackage.spectralPackage.lipschitzConstant *
        representationMetricPackage.spectralPackage.epsilon :=
  Part4DistanceMeasureGeometry.generatedRepresentationMetricPackage_spectralDistance_le
    representationMetricPackage

def generatedComponentDistanceBridge :=
  Part4DistanceMeasureGeometry.generatedCarrierShapeDistanceBridge
    AtomGeneratedMoleculeExamples.generatedComponentObject

def generatedComponentRootDistanceBundle :=
  Part4DistanceMeasureGeometry.generatedCarrierAtomRootDistanceBundle
    AtomGeneratedMoleculeExamples.generatedComponentObject

def selectedObjectSlotFootprint (_shape : AtomShape) : Nat := 0

def selectedPayloadSlotFootprint (_shape : AtomShape) : Nat := 0

def selectedValencePortFootprint (_shape : AtomShape) : Nat := 0

def selectedRequiredPortFootprint (_shape : AtomShape) : Nat := 0

def selectedSemanticAnchorName (shape : AtomShape) : String :=
  shape.subject.name

def generatedComponentFullRootGeometryPackage :=
  Part4DistanceMeasureGeometry.generatedCarrierFullRootGeometryPackage
    AtomGeneratedMoleculeExamples.generatedComponentObject
    selectedObjectSlotFootprint
    selectedPayloadSlotFootprint
    selectedValencePortFootprint
    selectedRequiredPortFootprint
    selectedSemanticAnchorName

theorem generatedComponentDistanceBridge_unfolds :
    generatedComponentDistanceBridge.generatedDistance
        AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
        AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier =
      AAT.GeneratedAtomShapeCoordinate.mismatchCount
        (generatedComponentDistanceBridge.coordinate
          AtomGeneratedMoleculeExamples.generatedComponentApiCarrier)
        (generatedComponentDistanceBridge.coordinate
          AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier) :=
  Part4DistanceMeasureGeometry.generatedCarrierShapeDistanceBridge_unfolds
    AtomGeneratedMoleculeExamples.generatedComponentObject
    AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
    AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier

theorem generatedComponentRootDistance_layout_eq_one :
    generatedComponentRootDistanceBundle.layoutDistance
        AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
        AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier = 1 :=
  calc
    generatedComponentRootDistanceBundle.layoutDistance
        AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
        AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier =
        AtomGeneratedMoleculeExamples.generatedComponentObject.generatedCarrierShapeDistance
          AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
          AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier := by
      simpa [generatedComponentRootDistanceBundle] using
        (Part4DistanceMeasureGeometry.generatedCarrierRootDistance_layout_eq_generatedCarrierShapeDistance
          AtomGeneratedMoleculeExamples.generatedComponentObject
          AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
          AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier)
    _ = 1 :=
      AtomGeneratedMoleculeExamples.generatedComponentObject_api_database_shapeDistance_eq_one

theorem generatedComponentFullRootGeometryPackage_recordsBoundaries :
    generatedComponentFullRootGeometryPackage.RecordsGeneratedBoundaries :=
  Part4DistanceMeasureGeometry.generatedCarrierFullRootGeometryPackage_recordsBoundaries
    AtomGeneratedMoleculeExamples.generatedComponentObject
    selectedObjectSlotFootprint
    selectedPayloadSlotFootprint
    selectedValencePortFootprint
    selectedRequiredPortFootprint
    selectedSemanticAnchorName

theorem generatedComponentFullRootGeometryPackage_fullDistance_unfolds :
    generatedComponentFullRootGeometryPackage.fullDistance
        AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
        AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier =
      AAT.GeneratedAtomFullShapeCoordinate.fullMismatchCount
        (generatedComponentFullRootGeometryPackage.coordinate
          AtomGeneratedMoleculeExamples.generatedComponentApiCarrier)
        (generatedComponentFullRootGeometryPackage.coordinate
          AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier) :=
  Part4DistanceMeasureGeometry.generatedCarrierFullRootGeometryPackage_fullDistance_eq_coordinateMismatch
    AtomGeneratedMoleculeExamples.generatedComponentObject
    selectedObjectSlotFootprint
    selectedPayloadSlotFootprint
    selectedValencePortFootprint
    selectedRequiredPortFootprint
    selectedSemanticAnchorName
    AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
    AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier

def generatedComponentContextEvidence :=
  Part4DistanceMeasureGeometry.generatedConfigurationContextEvidence
    AtomGeneratedMoleculeExamples.generatedComponentObject
    AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
    AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier
    trivial

theorem generatedComponentContextEvidence_recordsBoundaries :
    generatedComponentContextEvidence.RecordsGeneratedBoundaries :=
  Part4DistanceMeasureGeometry.generatedConfigurationContextEvidence_recordsBoundaries
    AtomGeneratedMoleculeExamples.generatedComponentObject
    AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
    AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier
    trivial

def generatedComponentContextEvidence_pairCompatible :
    CompatibleComposition
      (AtomShapeOf AtomGeneratedMoleculeExamples.componentShapePresentation
        AtomGeneratedMoleculeExamples.generatedComponentApiCarrier.val)
      (AtomShapeOf AtomGeneratedMoleculeExamples.componentShapePresentation
        AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier.val) :=
  Part4DistanceMeasureGeometry.generatedConfigurationContextEvidence_pairCompatible
    AtomGeneratedMoleculeExamples.generatedComponentObject
    AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
    AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier
    trivial
    (by intro h; cases h)

def generatedComponentConfigurationDistanceSchema :=
  Part4DistanceMeasureGeometry.generatedConfigurationDistanceSchema
    (presentation := AtomGeneratedMoleculeExamples.componentShapePresentation)
    (fun object _left _right => object.generatedContextCarriers.length)
    (fun object _left _right => object.generatedContextCarriers.length)
    (by intro _object _left _right; rfl)

def generatedComponentConfigurationDistanceWitness :=
  Part4DistanceMeasureGeometry.generatedConfigurationDistanceWitness
    AtomGeneratedMoleculeExamples.generatedComponentObject
    generatedComponentConfigurationDistanceSchema
    AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
    AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier
    trivial

theorem generatedComponentConfigurationDistanceWitness_recordsScope :
    generatedComponentConfigurationDistanceWitness.RecordsGeneratedScope :=
  Part4DistanceMeasureGeometry.generatedConfigurationDistanceWitness_recordsScope
    AtomGeneratedMoleculeExamples.generatedComponentObject
    generatedComponentConfigurationDistanceSchema
    AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
    AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier
    trivial

theorem generatedComponentConfigurationDistanceWitness_distance_le :
    generatedComponentConfigurationDistanceSchema.distanceIn
        AtomGeneratedMoleculeExamples.generatedComponentObject
        AtomGeneratedMoleculeExamples.generatedComponentApiCarrier.val
        AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier.val ≤
      generatedComponentConfigurationDistanceSchema.suppliedPathCost
        AtomGeneratedMoleculeExamples.generatedComponentObject
        AtomGeneratedMoleculeExamples.generatedComponentApiCarrier.val
        AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier.val :=
  Part4DistanceMeasureGeometry.generatedConfigurationDistanceWitness_distance_le
    AtomGeneratedMoleculeExamples.generatedComponentObject
    generatedComponentConfigurationDistanceSchema
    AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
    AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier
    trivial

theorem generatedComponentConfiguration_samePairDiffers :
    generatedComponentConfigurationDistanceSchema.SamePairDistanceDiffers
      AtomGeneratedMoleculeExamples.generatedApiOnlyObject
      AtomGeneratedMoleculeExamples.generatedComponentObject
      AtomGeneratedMoleculeExamples.ComponentAtom.api
      AtomGeneratedMoleculeExamples.ComponentAtom.api :=
  Part4DistanceMeasureGeometry.generatedConfigurationDistance_samePairDiffers_of_witness
    generatedComponentConfigurationDistanceSchema
    trivial
    trivial
    trivial
    trivial
    (by
      simp [generatedComponentConfigurationDistanceSchema,
        Part4DistanceMeasureGeometry.generatedConfigurationDistanceSchema,
        AAT.GeneratedArchitectureObject.generatedContextCarriers,
        AtomGeneratedMoleculeExamples.generatedApiOnlyObject,
        AtomGeneratedMoleculeExamples.generatedComponentObject])

def generatedComponentContextDistanceSchema :=
  Part4DistanceMeasureGeometry.generatedContextDistanceSchema
    AtomGeneratedMoleculeExamples.generatedComponentObject
    AtomGeneratedMoleculeExamples.generatedComponentObject.generatedCarrierShapeDistance

theorem generatedComponentContext_api_in_selected :
    generatedComponentContextDistanceSchema.inContext
      AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
      AtomGeneratedMoleculeExamples.generatedComponentMolecule :=
  Part4DistanceMeasureGeometry.generatedContextDistanceSchema_in_selectedContext
    AtomGeneratedMoleculeExamples.generatedComponentObject
    AtomGeneratedMoleculeExamples.generatedComponentObject.generatedCarrierShapeDistance
    AtomGeneratedMoleculeExamples.generatedComponentApiCarrier

theorem generatedComponentContext_database_in_selected :
    generatedComponentContextDistanceSchema.inContext
      AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier
      AtomGeneratedMoleculeExamples.generatedComponentMolecule :=
  Part4DistanceMeasureGeometry.generatedContextDistanceSchema_in_selectedContext
    AtomGeneratedMoleculeExamples.generatedComponentObject
    AtomGeneratedMoleculeExamples.generatedComponentObject.generatedCarrierShapeDistance
    AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier

theorem generatedComponentContextDistance_recordsFiniteContext :
    generatedComponentContextDistanceSchema.RecordsFiniteContext :=
  Part4DistanceMeasureGeometry.generatedContextDistanceSchema_recordsFiniteContext
    AtomGeneratedMoleculeExamples.generatedComponentObject
    AtomGeneratedMoleculeExamples.generatedComponentObject.generatedCarrierShapeDistance
    trivial

theorem generatedComponentContextDistance_eq_one :
    generatedComponentContextDistanceSchema.contextDistance
      AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
      AtomGeneratedMoleculeExamples.generatedComponentDatabaseCarrier = 1 :=
  AtomGeneratedMoleculeExamples.generatedComponentObject_api_database_shapeDistance_eq_one

def generatedOperationDistanceEvidence :=
  Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence
    AtomGeneratedMoleculeExamples.generatedApiExpansionOperation
    AtomGeneratedMoleculeExamples.generatedApiOnlyCarrier

theorem generatedOperationDistanceEvidence_targetPrimitive :
    generatedOperationDistanceEvidence.targetPrimitiveBoundary :=
  Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence_targetPrimitive
    AtomGeneratedMoleculeExamples.generatedApiExpansionOperation
    AtomGeneratedMoleculeExamples.generatedApiOnlyCarrier

theorem generatedOperationDistanceEvidence_doesNotCreateAtoms :
    generatedOperationDistanceEvidence.operationDoesNotCreateAtomsBoundary :=
  Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence_doesNotCreateAtoms
    AtomGeneratedMoleculeExamples.generatedApiExpansionOperation
    AtomGeneratedMoleculeExamples.generatedApiOnlyCarrier

theorem generatedOperationDistanceEvidence_recordsBoundaries :
    generatedOperationDistanceEvidence.RecordsGeneratedBoundaries :=
  Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence_recordsGeneratedBoundaries
    AtomGeneratedMoleculeExamples.generatedApiExpansionOperation
    AtomGeneratedMoleculeExamples.generatedApiOnlyCarrier

def generatedRepairProblemDistanceEvidence :=
  Part4DistanceMeasureGeometry.generatedRepairProblemOperation_mappedDistanceEvidence
    AtomGeneratedRepairExamples.missingPortRepairOperation
    AtomGeneratedRepairExamples.missingPortApiCarrier

theorem generatedRepairProblemDistanceEvidence_targetPrimitive :
    generatedRepairProblemDistanceEvidence.targetPrimitiveBoundary :=
  Part4DistanceMeasureGeometry.generatedRepairProblemOperation_mappedDistanceEvidence_targetPrimitive
    AtomGeneratedRepairExamples.missingPortRepairOperation
    AtomGeneratedRepairExamples.missingPortApiCarrier

theorem generatedRepairProblemDistanceEvidence_recordsBoundaries :
    generatedRepairProblemDistanceEvidence.RecordsGeneratedBoundaries :=
  Part4DistanceMeasureGeometry.generatedRepairProblemOperation_mappedDistanceEvidence_recordsGeneratedBoundaries
    AtomGeneratedRepairExamples.missingPortRepairOperation
    AtomGeneratedRepairExamples.missingPortApiCarrier

theorem generatedRepairProblemDistanceEvidence_unmappedPrimitive :
    AtomGeneratedRepairExamples.repairSystem.Primitive
      AtomGeneratedRepairExamples.repairedDatabaseCarrier.val :=
  Part4DistanceMeasureGeometry.generatedRepairProblemOperation_unmapped_target_atom_primitive
    AtomGeneratedRepairExamples.missingPortRepairOperation
    AtomGeneratedRepairExamples.repairedDatabaseCarrier
    AtomGeneratedRepairExamples.generatedMissingPortRepair_database_unmapped

def generatedOperationDiagnostic :=
  Part4DistanceMeasureGeometry.atomGeneratedDistanceDiagnosticConclusion
    diagnosticConclusion
    [generatedOperationDistanceEvidence]
    [AtomGeneratedMoleculeExamples.generatedApiExpansionOperation]
    True
    True
    True
    True
    True

theorem generatedOperationDiagnostic_supportingDistances_eq :
    generatedOperationDiagnostic.conclusion.supportingDistances =
      generatedOperationDiagnostic.atomGeneratedDistances :=
  Part4DistanceMeasureGeometry.atomGeneratedDiagnostic_supportingDistances_eq
    generatedOperationDiagnostic

theorem generatedOperationDiagnostic_recommendedOperations_eq :
    generatedOperationDiagnostic.conclusion.recommendedOperations =
      generatedOperationDiagnostic.atomGeneratedOperations :=
  Part4DistanceMeasureGeometry.atomGeneratedDiagnostic_recommendedOperations_eq
    generatedOperationDiagnostic

theorem generatedOperationDiagnostic_records_generated_boundaries :
    generatedOperationDiagnostic.RecordsGeneratedBoundaries :=
  Part4DistanceMeasureGeometry.AtomGeneratedDistanceDiagnosticConclusion.records_generated_boundaries
    generatedOperationDiagnostic
    trivial
    trivial
    ⟨trivial, trivial⟩
    ⟨trivial, trivial, trivial⟩
    trivial

def generatedOperationRepairDiagnostic :=
  Part4DistanceMeasureGeometry.atomGeneratedDistanceDiagnosticConclusion
    diagnosticConclusion
    [Sum.inl generatedOperationDistanceEvidence,
      Sum.inr generatedRepairProblemDistanceEvidence]
    [ExampleOperation.attachGuard]
    True
    True
    True
    True
    True

def generatedOperationRepairDiagnosticBridge :
    Part4DistanceMeasureGeometry.GeneratedOperationRepairDiagnosticBridge
      (Part4DistanceMeasureGeometry.GeneratedMappedDistanceEvidence
        (AAT.GeneratedCarrier
          AtomGeneratedMoleculeExamples.generatedApiOnlyObject)
        (AAT.GeneratedCarrier
          AtomGeneratedMoleculeExamples.generatedComponentObject)
        AAT.GeneratedAtomShapeCoordinate)
      (Part4DistanceMeasureGeometry.GeneratedMappedDistanceEvidence
        (AAT.GeneratedRepairProblemCarrier
          AtomGeneratedRepairExamples.missingPortConfiguration)
        (AAT.GeneratedCarrier
          AtomGeneratedRepairExamples.repairedGeneratedObject)
        AAT.GeneratedAtomShapeCoordinate)
      Axis
      ExampleOperation where
  operationEvidence := generatedOperationDistanceEvidence
  repairEvidence := generatedRepairProblemDistanceEvidence
  conclusion := generatedOperationRepairDiagnostic
  operationEvidenceRecorded := True
  repairEvidenceRecorded := True
  boundedDiagnosticRecorded := True
  recommendationBoundary := True
  nonConclusions := True

theorem generatedOperationRepairDiagnosticBridge_recordsBoundaries :
    generatedOperationRepairDiagnosticBridge.RecordsGeneratedDiagnosticBoundaries :=
  Part4DistanceMeasureGeometry.generatedOperationRepairDiagnosticBridge_recordsGeneratedDiagnosticBoundaries
    generatedOperationRepairDiagnosticBridge
    trivial
    trivial
    (Part4DistanceMeasureGeometry.AtomGeneratedDistanceDiagnosticConclusion.records_generated_boundaries
      generatedOperationRepairDiagnostic
      trivial
      trivial
      ⟨trivial, trivial⟩
      ⟨trivial, trivial, trivial⟩
      trivial)
    trivial
    trivial
    trivial

def fillingLowerBound : FillingCostLowerBound where
  observationGap := 0
  fillingCost := 0
  lipschitzConstant := 1
  lowerBound := by simp
  nonConclusions := True

def persistentNonFillability : PersistentNonFillability ExampleFiller where
  scale := 0
  candidate := fun _ => False
  fillerCost := fun _ => 0
  noFillerWithinScale := by
    intro _filler hCandidate _hWithin
    cases hCandidate
  selectedScope := True
  nonConclusions := True

def generatedFillingPackage :
    Part4DistanceMeasureGeometry.GeneratedFillingCostPackage
      (AAT.GeneratedArchitectureDiagram
        AtomGeneratedMoleculeExamples.generatedComponentObject
        (source := AtomGeneratedMoleculeExamples.generatedComponentApiCarrier)
        (target := AtomGeneratedMoleculeExamples.generatedComponentApiCarrier))
      ExampleFiller where
  diagram :=
    AtomGeneratedMoleculeExamples.generatedComponentNilDiagram
      AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
  fillers := []
  lowerBound := fillingLowerBound
  persistentNonFillability := persistentNonFillability
  generatedDiagramEvidence := True
  finiteFillerUniverse := True
  nonConclusions := True

theorem generatedFillingPackage_recordsBoundaries :
    generatedFillingPackage.RecordsGeneratedFillingBoundaries :=
  Part4DistanceMeasureGeometry.generatedFillingCostPackage_recordsGeneratedFillingBoundaries
    generatedFillingPackage trivial trivial trivial trivial trivial trivial

theorem generatedFillingPackage_observationGap_le :
    generatedFillingPackage.lowerBound.observationGap ≤
      generatedFillingPackage.lowerBound.lipschitzConstant *
        generatedFillingPackage.lowerBound.fillingCost :=
  Part4DistanceMeasureGeometry.generatedFillingCostPackage_observationGap_le
    generatedFillingPackage

def selectedCurvatureReading :
    SelectedCurvatureReading Axis ExampleState where
  curvatureMass := fun
    | Axis.runtime, ExampleState.source => 1
    | Axis.runtime, ExampleState.middle => 1
    | Axis.runtime, ExampleState.target => 0
    | Axis.deployment, ExampleState.source => 0
    | Axis.deployment, ExampleState.middle => 0
    | Axis.deployment, ExampleState.target => 1
  measuredAxis := fun _axis => True
  selectedScope := True
  nonConclusions := True

def selectedCurvatureTransport :
    CurvatureTransport Axis ExampleState where
  reading := selectedCurvatureReading
  before := ExampleState.source
  after := ExampleState.target
  targetAxis := Axis.runtime
  transportedAxis := Axis.deployment
  targetMeasured := trivial
  transportedMeasured := trivial
  targetDecreases := by decide
  transportedIncreases := by decide
  selectedScope := True
  nonConclusions := True

def generatedCurvatureFillingBridge :
    Part4DistanceMeasureGeometry.GeneratedCurvatureFillingBridge
      Axis
      ExampleState
      (AAT.GeneratedArchitectureDiagram
        AtomGeneratedMoleculeExamples.generatedComponentObject
        (source := AtomGeneratedMoleculeExamples.generatedComponentApiCarrier)
        (target := AtomGeneratedMoleculeExamples.generatedComponentApiCarrier))
      ExampleFiller where
  curvatureTransport := selectedCurvatureTransport
  fillingPackage := generatedFillingPackage
  generatedCurvatureEvidence := True
  generatedFillingEvidence := True
  selectedScope := True
  nonConclusions := True

theorem generatedCurvatureFillingBridge_recordsBoundaries :
    generatedCurvatureFillingBridge.RecordsGeneratedCurvatureFillingBoundaries :=
  Part4DistanceMeasureGeometry.generatedCurvatureFillingBridge_recordsGeneratedCurvatureFillingBoundaries
    generatedCurvatureFillingBridge
    trivial
    trivial
    trivial
    trivial
    generatedFillingPackage_recordsBoundaries
    trivial
    trivial

theorem generatedCurvatureFillingBridge_target_decreases :
    generatedCurvatureFillingBridge.curvatureTransport.reading.curvatureMass
        generatedCurvatureFillingBridge.curvatureTransport.targetAxis
        generatedCurvatureFillingBridge.curvatureTransport.after <
      generatedCurvatureFillingBridge.curvatureTransport.reading.curvatureMass
        generatedCurvatureFillingBridge.curvatureTransport.targetAxis
        generatedCurvatureFillingBridge.curvatureTransport.before :=
  Part4DistanceMeasureGeometry.generatedCurvatureFillingBridge_target_curvature_decreases
    generatedCurvatureFillingBridge

def generatedHomotopyBound : QuantitativeHomotopyBound where
  observationDistance := 0
  homotopyCost := 0
  lipschitzConstant := 1
  bound := by simp
  selectedScope := True
  nonConclusions := True

def generatedFiniteHomotopyPackage :
    Part4DistanceMeasureGeometry.GeneratedFiniteHomotopyCost
      (AAT.GeneratedArchitecturePath
        AtomGeneratedMoleculeExamples.generatedComponentObject
        AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
        AtomGeneratedMoleculeExamples.generatedComponentApiCarrier)
      ExampleHomotopy where
  sourcePath :=
    AtomGeneratedMoleculeExamples.generatedComponentNilPath
      AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
  targetPath :=
    AtomGeneratedMoleculeExamples.generatedComponentNilPath
      AtomGeneratedMoleculeExamples.generatedComponentApiCarrier
  homotopies := [ExampleHomotopy.contract]
  homotopyBound := generatedHomotopyBound
  finiteWitnessUniverse := True
  selectedScope := True
  nonConclusions := True

theorem generatedFiniteHomotopyPackage_recordsUniverse :
    generatedFiniteHomotopyPackage.RecordsFiniteWitnessUniverse :=
  Part4DistanceMeasureGeometry.generatedFiniteHomotopyCost_recordsFiniteWitnessUniverse
    generatedFiniteHomotopyPackage trivial trivial trivial trivial trivial

theorem generatedFiniteHomotopyPackage_observationDistance_le :
    generatedFiniteHomotopyPackage.homotopyBound.observationDistance ≤
      generatedFiniteHomotopyPackage.homotopyBound.lipschitzConstant *
        generatedFiniteHomotopyPackage.homotopyBound.homotopyCost :=
  Part4DistanceMeasureGeometry.generatedFiniteHomotopyCost_observationDistance_le
    generatedFiniteHomotopyPackage

def finiteDehnBound : FiniteDehnBound ExampleLoop where
  candidates := [ExampleLoop.boundary]
  boundaryLength := fun _ => 0
  fillingArea := fun _ => 0
  boundaryLimit := 0
  dehnValue := 0
  upperBound := by
    intro _loop _hMem _hBoundary
    simp
  selectedScope := True
  nonConclusions := True

def generatedFiniteDehnPackage :
    Part4DistanceMeasureGeometry.GeneratedFiniteDehnBound ExampleLoop where
  dehnBound := finiteDehnBound
  suppliedCandidateUniverse := True
  notUniversalDehnFunction := True
  nonConclusions := True

theorem generatedFiniteDehnPackage_recordsUniverse :
    generatedFiniteDehnPackage.RecordsFiniteUniverse :=
  Part4DistanceMeasureGeometry.generatedFiniteDehnBound_recordsFiniteUniverse
    generatedFiniteDehnPackage trivial trivial trivial trivial trivial

theorem generatedFiniteDehnPackage_area_le :
    generatedFiniteDehnPackage.dehnBound.fillingArea ExampleLoop.boundary ≤
      generatedFiniteDehnPackage.dehnBound.dehnValue :=
  Part4DistanceMeasureGeometry.generatedFiniteDehnBound_fillingArea_le_dehnValue
    generatedFiniteDehnPackage
    (by simp [generatedFiniteDehnPackage, finiteDehnBound])
    (by simp [generatedFiniteDehnPackage, finiteDehnBound])

end AATPart4DistanceExamples
end Formal.Arch
