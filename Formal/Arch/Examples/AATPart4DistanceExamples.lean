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

def generatedComponentDistanceBridge :=
  Part4DistanceMeasureGeometry.generatedCarrierShapeDistanceBridge
    AtomGeneratedMoleculeExamples.generatedComponentObject

def generatedComponentRootDistanceBundle :=
  Part4DistanceMeasureGeometry.generatedCarrierAtomRootDistanceBundle
    AtomGeneratedMoleculeExamples.generatedComponentObject

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

end AATPart4DistanceExamples
end Formal.Arch
