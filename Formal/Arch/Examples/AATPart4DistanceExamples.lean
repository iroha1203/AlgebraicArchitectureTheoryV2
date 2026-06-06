import Formal.Arch.Evolution.Part4DistanceMeasureGeometry

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

end AATPart4DistanceExamples
end Formal.Arch
