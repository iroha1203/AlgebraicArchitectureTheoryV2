import Formal.Arch.AAT.GeneratedDistance
import Formal.Arch.AAT.GeneratedOperation
import Formal.Arch.Evolution.DiagramFiller
import Formal.Arch.Evolution.SignatureDynamics
import Formal.Arch.Repair.Repair
import Formal.Arch.Repair.RepairSynthesis
import Formal.Arch.Signature.Curvature
import Formal.Arch.Signature.DistanceGeometry

/-!
AAT Part IV distance, measure, and architecture-geometry theorem package.

This entrypoint records the bounded Lean surfaces corresponding to the Part IV
distance plan.  The package is intentionally scoped to selected diagnostic
profiles, finite paths, generated AtomShape mismatch distances, and explicit
coverage / witness assumptions.
-/

namespace Formal.Arch
namespace Part4DistanceMeasureGeometry

universe u v

/-- Documentation-facing correspondence row for a Part IV package item. -/
structure SchematicCorrespondence where
  designSection : String
  leanEntrypoints : List String
  claimBoundary : String
  deriving DecidableEq, Repr

/-- Part IV candidate surfaces tracked by theorem index and classification. -/
inductive Candidate where
  | distanceFoundation
  | atomConfigurationGeometry
  | signaturePathGeometry
  | operationRepairGeometry
  | curvatureFillingGeometry
  | representationMetric
  | docsClassificationBoundary
  deriving DecidableEq, Repr

namespace Candidate

def designSection : Candidate -> String
  | distanceFoundation =>
      "Part IV.A distance values, profiles, and selected diagnostic scope"
  | atomConfigurationGeometry =>
      "Part IV.B atom / configuration distance schema"
  | signaturePathGeometry =>
      "Part IV.C signature path length, hidden excursion, and margin stability"
  | operationRepairGeometry =>
      "Part IV.D operation cost, distance to flatness, and bounded repair"
  | curvatureFillingGeometry =>
      "Part IV.E curvature mass and filling-cost lower bound"
  | representationMetric =>
      "Part IV.F representation metric and selected-scope faithfulness"
  | docsClassificationBoundary =>
      "Part IV.G theorem index, proof obligations, and classification boundary"

def schematicName : Candidate -> String
  | distanceFoundation => "distanceFoundation"
  | atomConfigurationGeometry => "atomConfigurationGeometry"
  | signaturePathGeometry => "signaturePathGeometry"
  | operationRepairGeometry => "operationRepairGeometry"
  | curvatureFillingGeometry => "curvatureFillingGeometry"
  | representationMetric => "representationMetric"
  | docsClassificationBoundary => "docsClassificationBoundary"

def representativeDeclarations : Candidate -> List String
  | distanceFoundation =>
      [ "DistanceValue"
      , "DistanceProfile"
      , "SelectedDistanceScope"
      , "BoundedDiagnosticConclusion"
      , "DistanceValue.unmeasured_not_measuredZero"
      ]
  | atomConfigurationGeometry =>
      [ "AAT.GeneratedAtomShapeCoordinate.mismatchCount"
      , "AAT.GeneratedArchitectureObject.generatedCarrierShapeDistance"
      , "AAT.GeneratedArchitectureObject.generatedCarrierShapeDistance_eq_coordinate_mismatchCount"
      , "AAT.GeneratedOperation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount"
      ]
  | signaturePathGeometry =>
      [ "SignatureDistanceSchema"
      , "SignatureDistanceSchema.pathLength"
      , "SignatureDistanceSchema.endpointDistance"
      , "SignatureDistanceSchema.hiddenExcursion"
      , "SignatureDistanceSchema.endpointDistance_le_pathLength"
      , "SignatureDistanceSchema.margin_stability"
      ]
  | operationRepairGeometry =>
      [ "OperationCostModel"
      , "OperationPathCost"
      , "DistanceToFlatRegion"
      , "BoundedSideEffectRepair"
      , "BoundedSideEffectRepair.targetDistance_decreases"
      , "RepairStepDecreases"
      ]
  | curvatureFillingGeometry =>
      [ "totalCurvature"
      , "totalWeightedCurvature"
      , "totalWeightedCurvature_eq_zero_iff_forall_measured_DiagramCommutes"
      , "FillingCostLowerBound"
      , "FillingCostLowerBound.observationGap_le_lipschitz_mul_fillingCost"
      ]
  | representationMetric =>
      [ "LipschitzRepresentation"
      , "BiLipschitzRepresentation"
      , "LipschitzRepresentation.analyticDistance_le_lipschitz"
      , "BiLipschitzRepresentation.structuralDistance_le_analyticDistance"
      ]
  | docsClassificationBoundary =>
      [ "Part4DistanceMeasureGeometry.Candidate"
      , "Part4DistanceMeasureGeometry.Candidate.schematicCorrespondence"
      , "AATReconstructionClassification.classifyPart4"
      ]

def claimBoundary : Candidate -> String
  | distanceFoundation =>
      "Unmeasured axes remain distinct from measured zero; no global lawfulness or flatness conclusion is inferred from distance values."
  | atomConfigurationGeometry =>
      "Generated distances are bounded AtomShape-coordinate mismatch counts, not empirical semantic calibration."
  | signaturePathGeometry =>
      "Path-length and margin-stability results are finite-path and selected-scope theorems with explicit preservation assumptions."
  | operationRepairGeometry =>
      "Repair cost and side-effect records show selected decreases / bounds only; they do not prove solver completeness or global termination."
  | curvatureFillingGeometry =>
      "Curvature and filling-cost lower bounds are finite measured-universe packages; no universal Dehn-function completeness is claimed."
  | representationMetric =>
      "Representation faithfulness is relative to comparability, coverage, and witness-completeness assumptions."
  | docsClassificationBoundary =>
      "The index and proof-obligation rows document the bounded Lean package without editing the mathematical Part IV source text."

def schematicCorrespondence (candidate : Candidate) : SchematicCorrespondence where
  designSection := candidate.designSection
  leanEntrypoints := candidate.representativeDeclarations
  claimBoundary := candidate.claimBoundary

def schematicCorrespondences : List SchematicCorrespondence :=
  [ schematicCorrespondence .distanceFoundation
  , schematicCorrespondence .atomConfigurationGeometry
  , schematicCorrespondence .signaturePathGeometry
  , schematicCorrespondence .operationRepairGeometry
  , schematicCorrespondence .curvatureFillingGeometry
  , schematicCorrespondence .representationMetric
  , schematicCorrespondence .docsClassificationBoundary
  ]

def nonConclusionBoundary : Candidate -> String :=
  claimBoundary

def all : List Candidate :=
  [ distanceFoundation
  , atomConfigurationGeometry
  , signaturePathGeometry
  , operationRepairGeometry
  , curvatureFillingGeometry
  , representationMetric
  , docsClassificationBoundary
  ]

end Candidate

theorem unmeasured_not_measured_zero :
    ¬ DistanceValue.IsMeasuredZero DistanceValue.unmeasured :=
  DistanceValue.unmeasured_not_measuredZero

theorem generatedCarrierShapeDistance_eq_coordinate_mismatchCount
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation)
    (left right : AAT.GeneratedCarrier object) :
    object.generatedCarrierShapeDistance left right =
      AAT.GeneratedAtomShapeCoordinate.mismatchCount
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation left.val))
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation right.val)) :=
  AAT.GeneratedArchitectureObject.generatedCarrierShapeDistance_eq_coordinate_mismatchCount
    object left right

theorem generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (carrier : AAT.GeneratedCarrier source) :
    operation.mappedCarrierShapeDistance carrier =
      AAT.GeneratedAtomShapeCoordinate.mismatchCount
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation carrier.val))
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation (operation.atomMap carrier).val)) :=
  AAT.GeneratedOperation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount
    operation carrier

theorem signatureEndpointDistance_le_pathLength
    {State : Type u} {Sig : Type v}
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y) :
    schema.endpointDistance plan ≤ schema.pathLength plan :=
  SignatureDistanceSchema.endpointDistance_le_pathLength schema plan

theorem signature_margin_stability
    {State : Type u} {Sig : Type v}
    (schema : SignatureDistanceSchema State Sig)
    (R : SafeRegion Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (margin : Nat)
    (hStart : StateInSafeRegion schema.observation R X)
    (hWithin : schema.PathLengthWithinMargin plan margin)
    (hPreserves : EveryStepPreservesSafeRegion schema.observation R plan) :
    SignatureTrajectoryInSafeRegion R
      (SignatureTrajectory schema.observation plan) :=
  SignatureDistanceSchema.margin_stability
    schema R plan margin hStart hWithin hPreserves

theorem boundedSideEffectRepair_targetDistance_decreases
    {State : Type u} (repair : BoundedSideEffectRepair State) :
    repair.targetDistance repair.target <
      repair.targetDistance repair.source :=
  repair.targetDistance_decreases

theorem boundedSideEffectRepair_protectedMovement_within_bound
    {State : Type u} (repair : BoundedSideEffectRepair State) :
    repair.protectedMovement repair.source repair.target ≤
      repair.epsilon :=
  repair.protectedMovement_within_bound

theorem fillingCostLowerBound_observationGap_le
    (pkg : FillingCostLowerBound) :
    pkg.observationGap ≤ pkg.lipschitzConstant * pkg.fillingCost :=
  pkg.observationGap_le_lipschitz_mul_fillingCost

theorem lipschitzRepresentation_analyticDistance_le
    {State : Type u} {Analytic : Type v}
    (rep : LipschitzRepresentation State Analytic)
    {X Y : State}
    (hComparable : rep.comparable X Y) :
    rep.analyticDistance (rep.represent X) (rep.represent Y) ≤
      rep.lipschitzConstant * rep.structuralDistance X Y :=
  rep.analyticDistance_le_lipschitz hComparable

theorem biLipschitzRepresentation_structuralDistance_le
    {State : Type u} {Analytic : Type v}
    (rep : BiLipschitzRepresentation State Analytic)
    {X Y : State}
    (hComparable : rep.comparable X Y) :
    rep.lowerConstant * rep.structuralDistance X Y ≤
      rep.analyticDistance (rep.represent X) (rep.represent Y) :=
  rep.structuralDistance_le_analyticDistance hComparable

end Part4DistanceMeasureGeometry
end Formal.Arch
