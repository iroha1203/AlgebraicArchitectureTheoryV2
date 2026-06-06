import Formal.Arch.AAT.GeneratedDistance
import Formal.Arch.AAT.GeneratedOperation
import Formal.Arch.AAT.GeneratedRepair
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
  | distanceAATOverlay
  | atomRootGeometry
  | atomGeneratedRootDistance
  | atomConfigurationGeometry
  | configurationContextGeometry
  | signaturePathGeometry
  | signatureDistanceAggregation
  | finiteWitnessInfimumCore
  | distanceToLawfulnessGeometry
  | metricGaloisCorrespondence
  | operationRepairGeometry
  | atomGeneratedOperationDistance
  | contractiveRepairGeometry
  | curvatureFillingGeometry
  | curvatureTransportGeometry
  | quantitativeHomotopyFillingGeometry
  | representationMetric
  | representationSpectralStability
  | abstractInfimumInterface
  | diagnosticConclusionDetail
  | atomGeneratedDiagnosticConclusion
  | docsClassificationBoundary
  deriving DecidableEq, Repr

namespace Candidate

def designSection : Candidate -> String
  | distanceFoundation =>
      "Part IV.A distance values, profiles, and selected diagnostic scope"
  | distanceAATOverlay =>
      "Part IV.A DistanceAAT / DistanceBundle selected overlay"
  | atomRootGeometry =>
      "Part IV.B root Atom geometry distance bundle"
  | atomGeneratedRootDistance =>
      "Part IV.B Atom-generated root distance package"
  | atomConfigurationGeometry =>
      "Part IV.B atom / configuration distance schema"
  | configurationContextGeometry =>
      "Part IV.B/C configuration-indexed and context distance schema"
  | signaturePathGeometry =>
      "Part IV.C signature path length, hidden excursion, and margin stability"
  | signatureDistanceAggregation =>
      "Part IV.C/I DistanceValue-aware signature distance aggregation"
  | finiteWitnessInfimumCore =>
      "Part IV.C/D/E finite witness, lower-bound, and selected optimum core"
  | distanceToLawfulnessGeometry =>
      "Part IV.D distance to selected lawfulness / flatness region"
  | metricGaloisCorrespondence =>
      "Part IV.D metric operation / invariant correspondence"
  | operationRepairGeometry =>
      "Part IV.D operation cost, distance to flatness, and bounded repair"
  | atomGeneratedOperationDistance =>
      "Part IV.D Atom-generated operation distance package"
  | contractiveRepairGeometry =>
      "Part IV.D finite repair sequence and selected contractive repair"
  | curvatureFillingGeometry =>
      "Part IV.E curvature mass and filling-cost lower bound"
  | curvatureTransportGeometry =>
      "Part IV.E selected curvature transport between measured axes"
  | quantitativeHomotopyFillingGeometry =>
      "Part IV.E finite homotopy, filling, Dehn, and persistent non-fillability"
  | representationMetric =>
      "Part IV.F representation metric and selected-scope faithfulness"
  | representationSpectralStability =>
      "Part IV.F representation / spectral stability"
  | abstractInfimumInterface =>
      "Part IV.G abstract infimum interface over finite witnesses"
  | diagnosticConclusionDetail =>
      "Part IV.H detailed bounded diagnostic conclusion"
  | atomGeneratedDiagnosticConclusion =>
      "Part IV.H Atom-generated distance diagnostic conclusion"
  | docsClassificationBoundary =>
      "Part IV.G theorem index, proof obligations, and classification boundary"

def schematicName : Candidate -> String
  | distanceFoundation => "distanceFoundation"
  | distanceAATOverlay => "distanceAATOverlay"
  | atomRootGeometry => "atomRootGeometry"
  | atomGeneratedRootDistance => "atomGeneratedRootDistance"
  | atomConfigurationGeometry => "atomConfigurationGeometry"
  | configurationContextGeometry => "configurationContextGeometry"
  | signaturePathGeometry => "signaturePathGeometry"
  | signatureDistanceAggregation => "signatureDistanceAggregation"
  | finiteWitnessInfimumCore => "finiteWitnessInfimumCore"
  | distanceToLawfulnessGeometry => "distanceToLawfulnessGeometry"
  | metricGaloisCorrespondence => "metricGaloisCorrespondence"
  | operationRepairGeometry => "operationRepairGeometry"
  | atomGeneratedOperationDistance => "atomGeneratedOperationDistance"
  | contractiveRepairGeometry => "contractiveRepairGeometry"
  | curvatureFillingGeometry => "curvatureFillingGeometry"
  | curvatureTransportGeometry => "curvatureTransportGeometry"
  | quantitativeHomotopyFillingGeometry => "quantitativeHomotopyFillingGeometry"
  | representationMetric => "representationMetric"
  | representationSpectralStability => "representationSpectralStability"
  | abstractInfimumInterface => "abstractInfimumInterface"
  | diagnosticConclusionDetail => "diagnosticConclusionDetail"
  | atomGeneratedDiagnosticConclusion => "atomGeneratedDiagnosticConclusion"
  | docsClassificationBoundary => "docsClassificationBoundary"

def representativeDeclarations : Candidate -> List String
  | distanceFoundation =>
      [ "DistanceValue"
      , "DistanceProfile"
      , "SelectedDistanceScope"
      , "BoundedDiagnosticConclusion"
      , "DistanceValue.unmeasured_not_measuredZero"
      ]
  | distanceAATOverlay =>
      [ "DistanceBundle"
      , "DistanceBundle.RecordsSelectedOverlay"
      , "DistanceBundle.records_selectedOverlay"
      , "DistanceAAT"
      , "DistanceAAT.RecordsOverlayBoundary"
      , "DistanceAAT.distance_does_not_generate_atoms"
      , "DistanceAAT.distance_does_not_replace_aatCore"
      ]
  | atomRootGeometry =>
      [ "AtomRootDistanceBundle"
      , "AtomRootDistanceBundle.layoutDistance"
      , "AtomRootDistanceBundle.layoutDistance_eq_weighted_components"
      , "GeneratedAtomShapeDistanceBridge"
      , "GeneratedAtomShapeDistanceBridge.generatedDistance_eq_coordinateMismatch"
      ]
  | atomGeneratedRootDistance =>
      [ "Part4DistanceMeasureGeometry.generatedCarrierShapeDistanceBridge"
      , "Part4DistanceMeasureGeometry.generatedCarrierAtomRootDistanceBundle"
      , "Part4DistanceMeasureGeometry.generatedCarrierRootDistance_layout_eq_generatedCarrierShapeDistance"
      , "Part4DistanceMeasureGeometry.generatedCarrierShapeDistanceBridge_unfolds"
      , "Part4DistanceMeasureGeometry.generatedCarrierShapeDistanceBridge_recordsRootBoundary"
      ]
  | atomConfigurationGeometry =>
      [ "AAT.GeneratedAtomShapeCoordinate.mismatchCount"
      , "AAT.GeneratedArchitectureObject.generatedCarrierShapeDistance"
      , "AAT.GeneratedArchitectureObject.generatedCarrierShapeDistance_eq_coordinate_mismatchCount"
      , "AAT.GeneratedOperation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount"
      ]
  | configurationContextGeometry =>
      [ "ConfigurationDistanceSchema"
      , "ConfigurationDistanceSchema.distance_le_suppliedPathCost"
      , "ConfigurationDistanceSchema.samePairDistanceDiffers_of_witness"
      , "ContextDistanceSchema"
      , "ContextDistanceSchema.records_finiteContext"
      ]
  | signaturePathGeometry =>
      [ "SignatureDistanceSchema"
      , "SignatureDistanceSchema.pathLength"
      , "SignatureDistanceSchema.endpointDistance"
      , "SignatureDistanceSchema.hiddenExcursion"
      , "SignatureDistanceSchema.hiddenExcursion_eq_pathLength_sub_endpointDistance"
      , "SignatureDistanceSchema.endpointDistance_add_hiddenExcursion_eq_pathLength"
      , "SignatureDistanceSchema.hiddenExcursion_positive_of_endpointDistance_lt_pathLength"
      , "SignatureDistanceSchema.endpointDistance_le_pathLength"
      , "SignatureDistanceSchema.margin_stability"
      ]
  | signatureDistanceAggregation =>
      [ "AxisDistanceReading"
      , "AxisDistanceReading.MeasuredPayload?"
      , "SignatureDistanceBundle"
      , "SignatureDistanceBundle.measuredSubtotal"
      , "SignatureDistanceBundle.measuredPayload?_measured"
      , "SignatureDistanceBundle.unmeasuredAxis_not_measuredPayload"
      , "SignatureDistanceBundle.unmeasuredAxis_not_measuredZero"
      , "Part4DistanceMeasureGeometry.signatureDistanceBundle_measuredSubtotal_eq_selectedAxes"
      , "Part4DistanceMeasureGeometry.signatureDistanceBundle_records_measurementBoundary"
      ]
  | finiteWitnessInfimumCore =>
      [ "FiniteRouteCost"
      , "FiniteFillerCost"
      , "FiniteHomotopyCost"
      , "LowerBoundForSelectedCandidates"
      , "NoRouteBelow"
      , "NoFillerBelow"
      , "NoHomotopyBelow"
      , "SelectedFiniteOptimum"
      , "SelectedFiniteOptimum.lowerBound_for_selected_candidates"
      , "SelectedFiniteOptimum.noCandidateBelow_lowerBound"
      ]
  | distanceToLawfulnessGeometry =>
      [ "SelectedDistanceToRegion"
      , "SelectedDistanceToRegion.region_of_distance_zero"
      , "SelectedDistanceToRegion.distance_zero_of_region"
      , "DistanceToFlatRegion.flat_of_distance_zero"
      ]
  | metricGaloisCorrespondence =>
      [ "MetricOperationAction"
      , "MetricOperationAction.PreservesDistance"
      , "MetricOperationAction.NonExpansive"
      , "MetricOperationAction.Lipschitz"
      , "MetricOperationAction.SelectedMetricGaloisPackage"
      ]
  | operationRepairGeometry =>
      [ "OperationCostModel"
      , "OperationPathCost"
      , "DistanceToFlatRegion"
      , "BoundedSideEffectRepair"
      , "BoundedSideEffectRepair.targetDistance_decreases"
      , "RepairStepDecreases"
      ]
  | atomGeneratedOperationDistance =>
      [ "Part4DistanceMeasureGeometry.GeneratedMappedDistanceEvidence"
      , "Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence"
      , "Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence_unfolds"
      , "Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence_targetPrimitive"
      , "Part4DistanceMeasureGeometry.generatedOperation_mappedDistanceEvidence_recordsGeneratedBoundaries"
      , "Part4DistanceMeasureGeometry.generatedRepairProblemOperation_mappedDistanceEvidence"
      , "Part4DistanceMeasureGeometry.generatedRepairProblemOperation_mappedDistanceEvidence_recordsGeneratedBoundaries"
      , "Part4DistanceMeasureGeometry.generatedRepairProblemOperation_unmapped_target_atom_primitive"
      ]
  | contractiveRepairGeometry =>
      [ "FiniteRepairSequence"
      , "FiniteRepairSequence.AllStepsDecrease"
      , "FiniteRepairSequence.allStepsDecrease"
      , "ContractiveRepairStep"
      , "ContractiveRepairStep.target_contracts"
      ]
  | curvatureFillingGeometry =>
      [ "totalCurvature"
      , "totalWeightedCurvature"
      , "totalWeightedCurvature_eq_zero_iff_forall_measured_DiagramCommutes"
      , "FillingCostLowerBound"
      , "FillingCostLowerBound.observationGap_le_lipschitz_mul_fillingCost"
      ]
  | curvatureTransportGeometry =>
      [ "SelectedCurvatureReading"
      , "CurvatureTransport"
      , "CurvatureTransport.target_curvature_decreases"
      , "CurvatureTransport.transported_curvature_increases"
      ]
  | quantitativeHomotopyFillingGeometry =>
      [ "QuantitativeHomotopyBound"
      , "QuantitativeHomotopyBound.observationDistance_le"
      , "FiniteDehnBound"
      , "FiniteDehnBound.fillingArea_le_dehnValue"
      , "PersistentNonFillability"
      ]
  | representationMetric =>
      [ "LipschitzRepresentation"
      , "BiLipschitzRepresentation"
      , "LipschitzRepresentation.analyticDistance_le_lipschitz"
      , "BiLipschitzRepresentation.structuralDistance_le_analyticDistance"
      ]
  | representationSpectralStability =>
      [ "LipschitzRepresentation.analyticDistance_le_of_structuralDistance_le"
      , "SpectralStabilityPackage"
      , "SpectralStabilityPackage.spectralDistance_le"
      ]
  | abstractInfimumInterface =>
      [ "AbstractInfimumInterface"
      , "AbstractInfimumInterface.lowerBound"
      , "AbstractInfimumInterface.exists_approximatingWitness"
      , "AbstractInfimumInterface.noAbstractCandidateBelow_infimum"
      , "AbstractInfimumInterface.ofSelectedFiniteOptimum"
      ]
  | diagnosticConclusionDetail =>
      [ "DetailedBoundedDiagnosticConclusion"
      , "DetailedBoundedDiagnosticConclusion.MeasuredAxis"
      , "DetailedBoundedDiagnosticConclusion.UnmeasuredAxis"
      , "DetailedBoundedDiagnosticConclusion.records_nonConclusions"
      , "DetailedBoundedDiagnosticConclusion.records_recommendation_boundary"
      ]
  | atomGeneratedDiagnosticConclusion =>
      [ "Part4DistanceMeasureGeometry.AtomGeneratedDistanceDiagnosticConclusion"
      , "Part4DistanceMeasureGeometry.AtomGeneratedDistanceDiagnosticConclusion.records_generated_boundaries"
      , "Part4DistanceMeasureGeometry.atomGeneratedDistanceDiagnosticConclusion"
      , "Part4DistanceMeasureGeometry.atomGeneratedDiagnostic_supportingDistances_eq"
      , "Part4DistanceMeasureGeometry.atomGeneratedDiagnostic_recommendedOperations_eq"
      ]
  | docsClassificationBoundary =>
      [ "Part4DistanceMeasureGeometry.Candidate"
      , "Part4DistanceMeasureGeometry.Candidate.schematicCorrespondence"
      , "AATReconstructionClassification.classifyPart4"
      ]

def claimBoundary : Candidate -> String
  | distanceFoundation =>
      "Unmeasured axes remain distinct from measured zero; no global lawfulness or flatness conclusion is inferred from distance values."
  | distanceAATOverlay =>
      "DistanceAAT is an overlay on an existing AAT core; it does not generate atoms, replace the core, or prove lawfulness from distance alone."
  | atomRootGeometry =>
      "Root Atom geometry records selected fiber, carrier, valence, semantic-anchor, and layout distances without empirical semantic calibration."
  | atomGeneratedRootDistance =>
      "Generated carrier distances instantiate the root Atom geometry bridge from AtomShape coordinates without claiming semantic calibration."
  | atomConfigurationGeometry =>
      "Generated distances are bounded AtomShape-coordinate mismatch counts, not empirical semantic calibration."
  | configurationContextGeometry =>
      "Configuration and context distance schemas use supplied finite witnesses and do not assert global shortest-path or context completeness."
  | signaturePathGeometry =>
      "Path-length and margin-stability results are finite-path and selected-scope theorems with explicit preservation assumptions."
  | signatureDistanceAggregation =>
      "Signature distance aggregation keeps axis-wise DistanceValue status, measured subtotal, coverage, confidence, and unmeasured boundaries without treating non-measured axes as zero."
  | finiteWitnessInfimumCore =>
      "Finite witness and selected optimum rows range only over supplied candidate lists; they do not assert global optimization completeness."
  | distanceToLawfulnessGeometry =>
      "Distance-to-region zero bridges are selected-scope and exactness-assumption relative, not global lawfulness or flatness claims."
  | metricGaloisCorrespondence =>
      "Metric operation / invariant correspondence is selected finite-universe and does not classify every operation."
  | operationRepairGeometry =>
      "Repair cost and side-effect records show selected decreases / bounds only; they do not prove solver completeness or global termination."
  | atomGeneratedOperationDistance =>
      "Generated operation and repair-problem distances expose AtomShape coordinate movement, target primitive evidence, and non-creation boundaries without solver-completeness claims."
  | contractiveRepairGeometry =>
      "Contractive repair is stated for supplied finite sequences or selected steps and does not prove global convergence or solver completeness."
  | curvatureFillingGeometry =>
      "Curvature and filling-cost lower bounds are finite measured-universe packages; no universal Dehn-function completeness is claimed."
  | curvatureTransportGeometry =>
      "Curvature transport compares selected measured axes before and after a supplied operation/read; unmeasured axes are not treated as zero."
  | quantitativeHomotopyFillingGeometry =>
      "Quantitative homotopy, filling, Dehn, and non-fillability rows are finite-candidate packages, not all-path completeness theorems."
  | representationMetric =>
      "Representation faithfulness is relative to comparability, coverage, and witness-completeness assumptions."
  | representationSpectralStability =>
      "Spectral stability is selected-scope Lipschitz control and does not calibrate empirical spectral metrics."
  | abstractInfimumInterface =>
      "The abstract infimum interface records lower-bound and approximation witnesses without computing a global optimizer."
  | diagnosticConclusionDetail =>
      "Detailed diagnostic conclusions keep supporting distances and recommended operations scoped, without proving operation success or global repair."
  | atomGeneratedDiagnosticConclusion =>
      "Atom-generated diagnostic conclusions bundle generated distance evidence and generated operation recommendations without promoting recommendations to repair-correctness theorems."
  | docsClassificationBoundary =>
      "The index and proof-obligation rows document the bounded Lean package without editing the mathematical Part IV source text."

def schematicCorrespondence (candidate : Candidate) : SchematicCorrespondence where
  designSection := candidate.designSection
  leanEntrypoints := candidate.representativeDeclarations
  claimBoundary := candidate.claimBoundary

def schematicCorrespondences : List SchematicCorrespondence :=
  [ schematicCorrespondence .distanceFoundation
  , schematicCorrespondence .distanceAATOverlay
  , schematicCorrespondence .atomRootGeometry
  , schematicCorrespondence .atomGeneratedRootDistance
  , schematicCorrespondence .atomConfigurationGeometry
  , schematicCorrespondence .configurationContextGeometry
  , schematicCorrespondence .signaturePathGeometry
  , schematicCorrespondence .signatureDistanceAggregation
  , schematicCorrespondence .finiteWitnessInfimumCore
  , schematicCorrespondence .distanceToLawfulnessGeometry
  , schematicCorrespondence .metricGaloisCorrespondence
  , schematicCorrespondence .operationRepairGeometry
  , schematicCorrespondence .atomGeneratedOperationDistance
  , schematicCorrespondence .contractiveRepairGeometry
  , schematicCorrespondence .curvatureFillingGeometry
  , schematicCorrespondence .curvatureTransportGeometry
  , schematicCorrespondence .quantitativeHomotopyFillingGeometry
  , schematicCorrespondence .representationMetric
  , schematicCorrespondence .representationSpectralStability
  , schematicCorrespondence .abstractInfimumInterface
  , schematicCorrespondence .diagnosticConclusionDetail
  , schematicCorrespondence .atomGeneratedDiagnosticConclusion
  , schematicCorrespondence .docsClassificationBoundary
  ]

def nonConclusionBoundary : Candidate -> String :=
  claimBoundary

def all : List Candidate :=
  [ distanceFoundation
  , distanceAATOverlay
  , atomRootGeometry
  , atomGeneratedRootDistance
  , atomConfigurationGeometry
  , configurationContextGeometry
  , signaturePathGeometry
  , signatureDistanceAggregation
  , finiteWitnessInfimumCore
  , distanceToLawfulnessGeometry
  , metricGaloisCorrespondence
  , operationRepairGeometry
  , atomGeneratedOperationDistance
  , contractiveRepairGeometry
  , curvatureFillingGeometry
  , curvatureTransportGeometry
  , quantitativeHomotopyFillingGeometry
  , representationMetric
  , representationSpectralStability
  , abstractInfimumInterface
  , diagnosticConclusionDetail
  , atomGeneratedDiagnosticConclusion
  , docsClassificationBoundary
  ]

end Candidate

/--
Generated carrier distance as a concrete Part IV root-distance bridge.

The generated mismatch count is an intrinsic AtomShape-coordinate distance.  It
does not calibrate semantic ontology distance and does not make distance an
Atom generator.
-/
def generatedCarrierShapeDistanceBridge
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation) :
    GeneratedAtomShapeDistanceBridge
      (AAT.GeneratedCarrier object)
      AAT.GeneratedAtomShapeCoordinate where
  coordinate := object.generatedAtomShapeCoordinate
  generatedDistance := object.generatedCarrierShapeDistance
  coordinateMismatch := AAT.GeneratedAtomShapeCoordinate.mismatchCount
  unfoldsToCoordinateMismatch := by
    intro left right
    rfl
  rootDistanceBoundary := True
  nonConclusions := True

/--
Generated carrier distance read as the selected fiber component of a root Atom
distance bundle.
-/
def generatedCarrierAtomRootDistanceBundle
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation) :
    AtomRootDistanceBundle (AAT.GeneratedCarrier object) where
  fiberDistance := object.generatedCarrierShapeDistance
  carrierDistance := fun _ _ => 0
  valenceDistance := fun _ _ => 0
  semanticAnchorDistance := fun _ _ => 0
  fiberWeight := 1
  carrierWeight := 0
  valenceWeight := 0
  semanticWeight := 0
  selectedRootScope := True
  lawOverlayBoundary := True
  semanticDistanceBoundary := True
  nonConclusions := True

theorem generatedCarrierShapeDistanceBridge_unfolds
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation)
    (left right : AAT.GeneratedCarrier object) :
    (generatedCarrierShapeDistanceBridge object).generatedDistance left right =
      AAT.GeneratedAtomShapeCoordinate.mismatchCount
        ((generatedCarrierShapeDistanceBridge object).coordinate left)
        ((generatedCarrierShapeDistanceBridge object).coordinate right) :=
  GeneratedAtomShapeDistanceBridge.generatedDistance_eq_coordinateMismatch
    (generatedCarrierShapeDistanceBridge object) left right

theorem generatedCarrierShapeDistanceBridge_recordsRootBoundary
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation) :
    (generatedCarrierShapeDistanceBridge object).rootDistanceBoundary ∧
      (generatedCarrierShapeDistanceBridge object).nonConclusions :=
  ⟨trivial, trivial⟩

theorem generatedCarrierRootDistance_layout_eq_generatedCarrierShapeDistance
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation)
    (left right : AAT.GeneratedCarrier object) :
    (generatedCarrierAtomRootDistanceBundle object).layoutDistance left right =
      object.generatedCarrierShapeDistance left right := by
  simp [generatedCarrierAtomRootDistanceBundle,
    AtomRootDistanceBundle.layoutDistance]

/--
Part IV evidence for one generated mapped-distance reading.

The source and target carriers can live in different generated surfaces.  The
distance is still a generated AtomShape-coordinate mismatch, and the package
keeps primitive-target and atom-non-creation boundaries with it.
-/
structure GeneratedMappedDistanceEvidence
    (SourceCarrier : Type u) (TargetCarrier : Type v)
    (Coordinate : Type w) where
  source : SourceCarrier
  target : TargetCarrier
  sourceCoordinate : Coordinate
  targetCoordinate : Coordinate
  mappedDistance : Nat
  coordinateMismatch : Coordinate -> Coordinate -> Nat
  unfoldsToCoordinateMismatch :
    mappedDistance = coordinateMismatch sourceCoordinate targetCoordinate
  targetPrimitiveBoundary : Prop
  operationDoesNotCreateAtomsBoundary : Prop
  distanceBoundary : Prop
  doesNotProveSolverCompleteness : Prop
  doesNotProveEmpiricalRepairQuality : Prop
  nonConclusions : Prop

namespace GeneratedMappedDistanceEvidence

variable {SourceCarrier : Type u} {TargetCarrier : Type v}
  {Coordinate : Type w}

theorem mappedDistance_eq_coordinateMismatch
    (evidence :
      GeneratedMappedDistanceEvidence SourceCarrier TargetCarrier Coordinate) :
    evidence.mappedDistance =
      evidence.coordinateMismatch evidence.sourceCoordinate
        evidence.targetCoordinate :=
  evidence.unfoldsToCoordinateMismatch

def RecordsGeneratedBoundaries
    (evidence :
      GeneratedMappedDistanceEvidence SourceCarrier TargetCarrier Coordinate) :
    Prop :=
  evidence.targetPrimitiveBoundary ∧
  evidence.operationDoesNotCreateAtomsBoundary ∧
  evidence.distanceBoundary ∧
  evidence.doesNotProveSolverCompleteness ∧
  evidence.doesNotProveEmpiricalRepairQuality ∧
  evidence.nonConclusions

theorem records_generated_boundaries
    (evidence :
      GeneratedMappedDistanceEvidence SourceCarrier TargetCarrier Coordinate)
    (hTarget : evidence.targetPrimitiveBoundary)
    (hNoCreate : evidence.operationDoesNotCreateAtomsBoundary)
    (hDistance : evidence.distanceBoundary)
    (hNoSolverCompleteness : evidence.doesNotProveSolverCompleteness)
    (hNoEmpiricalQuality : evidence.doesNotProveEmpiricalRepairQuality)
    (hNonConclusions : evidence.nonConclusions) :
    evidence.RecordsGeneratedBoundaries :=
  ⟨hTarget, hNoCreate, hDistance, hNoSolverCompleteness,
    hNoEmpiricalQuality, hNonConclusions⟩

end GeneratedMappedDistanceEvidence

def generatedOperation_mappedDistanceEvidence
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (carrier : AAT.GeneratedCarrier source) :
    GeneratedMappedDistanceEvidence
      (AAT.GeneratedCarrier source)
      (AAT.GeneratedCarrier target)
      AAT.GeneratedAtomShapeCoordinate where
  source := carrier
  target := operation.atomMap carrier
  sourceCoordinate :=
    AAT.GeneratedAtomShapeCoordinate.ofShape
      (AtomShapeOf presentation carrier.val)
  targetCoordinate :=
    AAT.GeneratedAtomShapeCoordinate.ofShape
      (AtomShapeOf presentation (operation.atomMap carrier).val)
  mappedDistance := operation.mappedCarrierShapeDistance carrier
  coordinateMismatch := AAT.GeneratedAtomShapeCoordinate.mismatchCount
  unfoldsToCoordinateMismatch := by
    rfl
  targetPrimitiveBoundary :=
    system.Primitive (operation.atomMap carrier).val
  operationDoesNotCreateAtomsBoundary :=
    system.noToolOutputCreatesAtoms
  distanceBoundary := True
  doesNotProveSolverCompleteness := True
  doesNotProveEmpiricalRepairQuality := True
  nonConclusions := True

theorem generatedOperation_mappedDistanceEvidence_unfolds
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (carrier : AAT.GeneratedCarrier source) :
    (generatedOperation_mappedDistanceEvidence operation carrier).mappedDistance =
      AAT.GeneratedAtomShapeCoordinate.mismatchCount
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation carrier.val))
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation
            (operation.atomMap carrier).val)) :=
  AAT.GeneratedOperation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount
    operation carrier

theorem generatedOperation_mappedDistanceEvidence_targetPrimitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (carrier : AAT.GeneratedCarrier source) :
    (generatedOperation_mappedDistanceEvidence operation carrier).targetPrimitiveBoundary :=
  operation.target_atom_primitive carrier

theorem generatedOperation_mappedDistanceEvidence_doesNotCreateAtoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (carrier : AAT.GeneratedCarrier source) :
    (generatedOperation_mappedDistanceEvidence operation carrier).operationDoesNotCreateAtomsBoundary :=
  operation.operation_does_not_create_atoms

theorem generatedOperation_mappedDistanceEvidence_recordsGeneratedBoundaries
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (carrier : AAT.GeneratedCarrier source) :
    (generatedOperation_mappedDistanceEvidence operation carrier).RecordsGeneratedBoundaries :=
  GeneratedMappedDistanceEvidence.records_generated_boundaries
    (generatedOperation_mappedDistanceEvidence operation carrier)
    (operation.target_atom_primitive carrier)
    operation.operation_does_not_create_atoms
    trivial
    trivial
    trivial
    trivial

theorem generatedOperation_unmapped_target_atom_primitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (targetCarrier : AAT.GeneratedCarrier target)
    (hUnmapped : operation.TargetCarrierUnmapped targetCarrier) :
    system.Primitive targetCarrier.val :=
  operation.unmapped_target_atom_primitive targetCarrier hUnmapped

def generatedRepairProblemOperation_mappedDistanceEvidence
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (operation :
      AAT.GeneratedRepairProblemOperation configuration target)
    (carrier : AAT.GeneratedRepairProblemCarrier configuration) :
    GeneratedMappedDistanceEvidence
      (AAT.GeneratedRepairProblemCarrier configuration)
      (AAT.GeneratedCarrier target)
      AAT.GeneratedAtomShapeCoordinate where
  source := carrier
  target := operation.atomMap carrier
  sourceCoordinate :=
    AAT.GeneratedAtomShapeCoordinate.ofShape
      (AtomShapeOf presentation carrier.val)
  targetCoordinate :=
    AAT.GeneratedAtomShapeCoordinate.ofShape
      (AtomShapeOf presentation (operation.atomMap carrier).val)
  mappedDistance := operation.mappedCarrierShapeDistance carrier
  coordinateMismatch := AAT.GeneratedAtomShapeCoordinate.mismatchCount
  unfoldsToCoordinateMismatch := by
    rfl
  targetPrimitiveBoundary :=
    system.Primitive (operation.atomMap carrier).val
  operationDoesNotCreateAtomsBoundary :=
    system.noToolOutputCreatesAtoms
  distanceBoundary := True
  doesNotProveSolverCompleteness := True
  doesNotProveEmpiricalRepairQuality := True
  nonConclusions := True

theorem generatedRepairProblemOperation_mappedDistanceEvidence_unfolds
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (operation :
      AAT.GeneratedRepairProblemOperation configuration target)
    (carrier : AAT.GeneratedRepairProblemCarrier configuration) :
    (generatedRepairProblemOperation_mappedDistanceEvidence operation carrier).mappedDistance =
      AAT.GeneratedAtomShapeCoordinate.mismatchCount
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation carrier.val))
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation
            (operation.atomMap carrier).val)) :=
  AAT.GeneratedRepairProblemOperation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount
    operation carrier

theorem generatedRepairProblemOperation_mappedDistanceEvidence_targetPrimitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (operation :
      AAT.GeneratedRepairProblemOperation configuration target)
    (carrier : AAT.GeneratedRepairProblemCarrier configuration) :
    (generatedRepairProblemOperation_mappedDistanceEvidence operation carrier).targetPrimitiveBoundary :=
  operation.target_atom_primitive carrier

theorem generatedRepairProblemOperation_mappedDistanceEvidence_doesNotCreateAtoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (operation :
      AAT.GeneratedRepairProblemOperation configuration target)
    (carrier : AAT.GeneratedRepairProblemCarrier configuration) :
    (generatedRepairProblemOperation_mappedDistanceEvidence operation carrier).operationDoesNotCreateAtomsBoundary :=
  operation.operation_does_not_create_atoms

theorem generatedRepairProblemOperation_mappedDistanceEvidence_recordsGeneratedBoundaries
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (operation :
      AAT.GeneratedRepairProblemOperation configuration target)
    (carrier : AAT.GeneratedRepairProblemCarrier configuration) :
    (generatedRepairProblemOperation_mappedDistanceEvidence operation carrier).RecordsGeneratedBoundaries :=
  GeneratedMappedDistanceEvidence.records_generated_boundaries
    (generatedRepairProblemOperation_mappedDistanceEvidence operation carrier)
    (operation.target_atom_primitive carrier)
    operation.operation_does_not_create_atoms
    trivial
    trivial
    trivial
    trivial

theorem generatedRepairProblemOperation_unmapped_target_atom_primitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (operation :
      AAT.GeneratedRepairProblemOperation configuration target)
    (targetCarrier : AAT.GeneratedCarrier target)
    (hUnmapped : operation.TargetCarrierUnmapped targetCarrier) :
    system.Primitive targetCarrier.val :=
  operation.unmapped_target_atom_primitive targetCarrier hUnmapped

/--
Detailed diagnostic package whose support and recommendations are explicitly
recorded as Atom-generated distance / operation evidence.
-/
structure AtomGeneratedDistanceDiagnosticConclusion
    (Axis : Type u) (DistanceRef : Type v) (Operation : Type w) where
  conclusion :
    DetailedBoundedDiagnosticConclusion Axis DistanceRef Operation
  atomGeneratedDistances : List DistanceRef
  atomGeneratedOperations : List Operation
  supportingDistances_eq_atomGenerated :
    conclusion.supportingDistances = atomGeneratedDistances
  recommendedOperations_eq_atomGenerated :
    conclusion.recommendedOperations = atomGeneratedOperations
  atomGeneratedDistanceEvidence : Prop
  atomGeneratedOperationEvidence : Prop
  nonConclusions : Prop

namespace AtomGeneratedDistanceDiagnosticConclusion

variable {Axis : Type u} {DistanceRef : Type v} {Operation : Type w}

def RecordsGeneratedBoundaries
    (pkg :
      AtomGeneratedDistanceDiagnosticConclusion Axis DistanceRef Operation) :
    Prop :=
  pkg.atomGeneratedDistanceEvidence ∧
  pkg.atomGeneratedOperationEvidence ∧
  pkg.conclusion.RecordsRecommendationBoundary ∧
  pkg.conclusion.base.RecordsNonConclusions ∧
  pkg.nonConclusions

theorem records_generated_boundaries
    (pkg :
      AtomGeneratedDistanceDiagnosticConclusion Axis DistanceRef Operation)
    (hDistance : pkg.atomGeneratedDistanceEvidence)
    (hOperation : pkg.atomGeneratedOperationEvidence)
    (hRecommendation : pkg.conclusion.RecordsRecommendationBoundary)
    (hNonConclusionBase : pkg.conclusion.base.RecordsNonConclusions)
    (hNonConclusions : pkg.nonConclusions) :
    pkg.RecordsGeneratedBoundaries :=
  ⟨hDistance, hOperation, hRecommendation,
    hNonConclusionBase, hNonConclusions⟩

theorem supportingDistances_eq
    (pkg :
      AtomGeneratedDistanceDiagnosticConclusion Axis DistanceRef Operation) :
    pkg.conclusion.supportingDistances = pkg.atomGeneratedDistances :=
  pkg.supportingDistances_eq_atomGenerated

theorem recommendedOperations_eq
    (pkg :
      AtomGeneratedDistanceDiagnosticConclusion Axis DistanceRef Operation) :
    pkg.conclusion.recommendedOperations = pkg.atomGeneratedOperations :=
  pkg.recommendedOperations_eq_atomGenerated

end AtomGeneratedDistanceDiagnosticConclusion

def atomGeneratedDistanceDiagnosticConclusion
    {Axis : Type u} {DistanceRef : Type v} {Operation : Type w}
    (base : BoundedDiagnosticConclusion Axis)
    (distances : List DistanceRef)
    (operations : List Operation)
    (atomGeneratedDistanceEvidence : Prop)
    (atomGeneratedOperationEvidence : Prop)
    (recommendationBoundary : Prop)
    (recommendationsAreNotRepairCorrectnessTheorems : Prop)
    (nonConclusions : Prop) :
    AtomGeneratedDistanceDiagnosticConclusion Axis DistanceRef Operation where
  conclusion :=
    { base := base
      supportingDistances := distances
      recommendedOperations := operations
      supportingDistanceScope := atomGeneratedDistanceEvidence
      recommendationBoundary := recommendationBoundary
      recommendationsAreNotRepairCorrectnessTheorems :=
        recommendationsAreNotRepairCorrectnessTheorems
      nonConclusions := nonConclusions }
  atomGeneratedDistances := distances
  atomGeneratedOperations := operations
  supportingDistances_eq_atomGenerated := rfl
  recommendedOperations_eq_atomGenerated := rfl
  atomGeneratedDistanceEvidence := atomGeneratedDistanceEvidence
  atomGeneratedOperationEvidence := atomGeneratedOperationEvidence
  nonConclusions := nonConclusions

theorem atomGeneratedDiagnostic_supportingDistances_eq
    {Axis : Type u} {DistanceRef : Type v} {Operation : Type w}
    (pkg :
      AtomGeneratedDistanceDiagnosticConclusion Axis DistanceRef Operation) :
    pkg.conclusion.supportingDistances = pkg.atomGeneratedDistances :=
  pkg.supportingDistances_eq

theorem atomGeneratedDiagnostic_recommendedOperations_eq
    {Axis : Type u} {DistanceRef : Type v} {Operation : Type w}
    (pkg :
      AtomGeneratedDistanceDiagnosticConclusion Axis DistanceRef Operation) :
    pkg.conclusion.recommendedOperations = pkg.atomGeneratedOperations :=
  pkg.recommendedOperations_eq

theorem unmeasured_not_measured_zero :
    ¬ DistanceValue.IsMeasuredZero DistanceValue.unmeasured :=
  DistanceValue.unmeasured_not_measuredZero

theorem distanceBundle_records_selectedOverlay
    {Axis : Type u} {State : Type v} {Sig : Type u}
    {Operation : Type v} {Generator : Type u} {Analytic : Type v}
    (bundle :
      DistanceBundle Axis State Sig Operation Generator Analytic)
    (hOverlay : bundle.selectedOverlay)
    (hAtoms : bundle.doesNotGenerateAtoms)
    (hCore : bundle.doesNotReplaceAATCore)
    (hLaw : bundle.doesNotProveLawfulnessByDistanceAlone)
    (hNonConclusions : bundle.nonConclusions) :
    bundle.RecordsSelectedOverlay :=
  DistanceBundle.records_selectedOverlay bundle
    hOverlay hAtoms hCore hLaw hNonConclusions

theorem distanceAAT_does_not_generate_atoms
    {Core : Type u} {Axis : Type v} {State : Type u}
    {Sig : Type v} {Operation : Type u} {Generator : Type v}
    {Analytic : Type u}
    (aat : DistanceAAT Core Axis State Sig Operation Generator Analytic)
    (h : aat.distanceBundle.doesNotGenerateAtoms) :
    aat.DistanceDoesNotGenerateAtoms :=
  aat.distance_does_not_generate_atoms h

theorem distanceAAT_does_not_replace_aatCore
    {Core : Type u} {Axis : Type v} {State : Type u}
    {Sig : Type v} {Operation : Type u} {Generator : Type v}
    {Analytic : Type u}
    (aat : DistanceAAT Core Axis State Sig Operation Generator Analytic)
    (h : aat.distanceBundle.doesNotReplaceAATCore) :
    aat.DistanceDoesNotReplaceAATCore :=
  aat.distance_does_not_replace_aatCore h

theorem atomRootDistance_layoutDistance_eq_weighted_components
    {Atom : Type u}
    (bundle : AtomRootDistanceBundle Atom)
    (left right : Atom) :
    bundle.layoutDistance left right =
      bundle.fiberWeight * bundle.fiberDistance left right +
        bundle.carrierWeight * bundle.carrierDistance left right +
        bundle.valenceWeight * bundle.valenceDistance left right +
        bundle.semanticWeight * bundle.semanticAnchorDistance left right :=
  AtomRootDistanceBundle.layoutDistance_eq_weighted_components
    bundle left right

theorem generatedAtomShapeBridge_generatedDistance_eq_coordinateMismatch
    {Atom : Type u} {Coordinate : Type v}
    (bridge : GeneratedAtomShapeDistanceBridge Atom Coordinate)
    (left right : Atom) :
    bridge.generatedDistance left right =
      bridge.coordinateMismatch (bridge.coordinate left)
        (bridge.coordinate right) :=
  bridge.generatedDistance_eq_coordinateMismatch left right

theorem configurationDistance_le_suppliedPathCost
    {Configuration : Type u} {Atom : Type v}
    (schema : ConfigurationDistanceSchema Configuration Atom)
    (configuration : Configuration) (left right : Atom) :
    schema.distanceIn configuration left right ≤
      schema.suppliedPathCost configuration left right :=
  schema.distance_le_suppliedPathCost configuration left right

theorem configurationDistance_samePairDiffers_of_witness
    {Configuration : Type u} {Atom : Type v}
    (schema : ConfigurationDistanceSchema Configuration Atom)
    {leftConfig rightConfig : Configuration}
    {left right : Atom}
    (hDiff :
      schema.distanceIn leftConfig left right ≠
        schema.distanceIn rightConfig left right) :
    schema.SamePairDistanceDiffers leftConfig rightConfig left right :=
  schema.samePairDistanceDiffers_of_witness hDiff

theorem contextDistance_records_finiteContext
    {Atom : Type u} {Molecule : Type v}
    (schema : ContextDistanceSchema Atom Molecule)
    (hFinite : schema.selectedFiniteContext)
    (hNoGlobal : schema.noGlobalContextCompleteness)
    (hNonConclusions : schema.nonConclusions) :
    schema.RecordsFiniteContext :=
  schema.records_finiteContext hFinite hNoGlobal hNonConclusions

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

theorem signatureHiddenExcursion_eq_pathLength_sub_endpointDistance
    {State : Type u} {Sig : Type v}
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y) :
    schema.hiddenExcursion plan =
      schema.pathLength plan - schema.endpointDistance plan :=
  SignatureDistanceSchema.hiddenExcursion_eq_pathLength_sub_endpointDistance
    schema plan

theorem signatureEndpointDistance_add_hiddenExcursion_eq_pathLength
    {State : Type u} {Sig : Type v}
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y) :
    schema.endpointDistance plan + schema.hiddenExcursion plan =
      schema.pathLength plan :=
  SignatureDistanceSchema.endpointDistance_add_hiddenExcursion_eq_pathLength
    schema plan

theorem signatureHiddenExcursion_positive_of_endpointDistance_lt_pathLength
    {State : Type u} {Sig : Type v}
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hVisibleGap : schema.endpointDistance plan < schema.pathLength plan) :
    0 < schema.hiddenExcursion plan :=
  SignatureDistanceSchema.hiddenExcursion_positive_of_endpointDistance_lt_pathLength
    schema plan hVisibleGap

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

theorem signatureDistanceBundle_measuredSubtotal_eq_selectedAxes
    {Axis : Type u}
    (bundle : SignatureDistanceBundle Axis) :
    bundle.measuredSubtotal =
      bundle.measuredSubtotalOf bundle.selectedAxes :=
  SignatureDistanceBundle.measuredSubtotal_eq_selectedAxes bundle

theorem signatureDistanceBundle_measuredPayload_measured
    {Axis : Type u}
    (bundle : SignatureDistanceBundle Axis)
    {axis : Axis} {n : Nat}
    (hValue : bundle.axisDistance axis = DistanceValue.measured n) :
    bundle.measuredPayload? axis = some n :=
  bundle.measuredPayload?_measured hValue

theorem signatureDistanceBundle_unmeasuredAxis_not_measuredPayload
    {Axis : Type u}
    (bundle : SignatureDistanceBundle Axis)
    {axis : Axis}
    (hValue : bundle.axisDistance axis = DistanceValue.unmeasured)
    (n : Nat) :
    bundle.measuredPayload? axis ≠ some n :=
  bundle.unmeasuredAxis_not_measuredPayload hValue n

theorem signatureDistanceBundle_unmeasuredAxis_not_measuredZero
    {Axis : Type u}
    (bundle : SignatureDistanceBundle Axis)
    {axis : Axis}
    (hValue : bundle.axisDistance axis = DistanceValue.unmeasured) :
    ¬ DistanceValue.IsMeasuredZero (bundle.axisDistance axis) :=
  bundle.unmeasuredAxis_not_measuredZero hValue

theorem signatureDistanceBundle_records_measurementBoundary
    {Axis : Type u}
    (bundle : SignatureDistanceBundle Axis)
    (hCoverage : bundle.coverageAssumptions)
    (hAggregation : bundle.aggregationPolicy)
    (hConfidence : bundle.confidenceBoundary)
    (hUnmeasured : bundle.unmeasuredAxisPolicy)
    (hNonConclusions : bundle.nonConclusions) :
    bundle.RecordsMeasurementBoundary :=
  bundle.records_measurementBoundary
    hCoverage hAggregation hConfidence hUnmeasured hNonConclusions

theorem signatureDistanceBundle_records_nonConclusions
    {Axis : Type u}
    (bundle : SignatureDistanceBundle Axis)
    (hLaw : bundle.doesNotConcludeGlobalLawfulness)
    (hFlat : bundle.doesNotConcludeGlobalFlatness)
    (hUnmeasured : bundle.doesNotConcludeUnmeasuredZero)
    (hNonConclusions : bundle.nonConclusions) :
    bundle.RecordsNonConclusions :=
  bundle.records_nonConclusions
    hLaw hFlat hUnmeasured hNonConclusions

theorem selectedFiniteOptimum_lowerBound_for_selected_candidates
    {Candidate : Type u}
    (optimum : SelectedFiniteOptimum Candidate) :
    LowerBoundForSelectedCandidates optimum.candidates optimum.selected
      optimum.cost optimum.lowerBound :=
  optimum.lowerBound_for_selected_candidates

theorem selectedFiniteOptimum_noCandidateBelow_lowerBound
    {Candidate : Type u}
    (optimum : SelectedFiniteOptimum Candidate) :
    NoCandidateBelow optimum.candidates optimum.selected
      optimum.cost optimum.lowerBound :=
  optimum.noCandidateBelow_lowerBound

theorem noRouteBelow_of_selected_lowerBound
    {Route : Type u}
    {routes : List Route}
    {selected : Route -> Prop}
    {cost : Route -> Nat}
    {bound : Nat}
    (hLower : LowerBoundForSelectedCandidates routes selected cost bound) :
    NoRouteBelow routes selected cost bound :=
  Formal.Arch.noRouteBelow_of_lowerBound hLower

theorem noFillerBelow_of_selected_lowerBound
    {Filler : Type u}
    {fillers : List Filler}
    {selected : Filler -> Prop}
    {cost : Filler -> Nat}
    {bound : Nat}
    (hLower : LowerBoundForSelectedCandidates fillers selected cost bound) :
    NoFillerBelow fillers selected cost bound :=
  Formal.Arch.noFillerBelow_of_lowerBound hLower

theorem noHomotopyBelow_of_selected_lowerBound
    {Homotopy : Type u}
    {homotopies : List Homotopy}
    {selected : Homotopy -> Prop}
    {cost : Homotopy -> Nat}
    {bound : Nat}
    (hLower :
      LowerBoundForSelectedCandidates homotopies selected cost bound) :
    NoHomotopyBelow homotopies selected cost bound :=
  Formal.Arch.noHomotopyBelow_of_lowerBound hLower

theorem selectedDistanceToRegion_region_of_distance_zero
    {State : Type u}
    (pkg : SelectedDistanceToRegion State)
    (X : State)
    (hZero : pkg.distanceToRegion X = 0) :
    pkg.region X :=
  pkg.region_of_distance_zero X hZero

theorem selectedDistanceToRegion_distance_zero_of_region
    {State : Type u}
    (pkg : SelectedDistanceToRegion State)
    (hExact : pkg.exactnessAssumptions)
    (X : State)
    (hRegion : pkg.region X) :
    pkg.distanceToRegion X = 0 :=
  pkg.distance_zero_of_region hExact X hRegion

theorem metricGalois_operation_nonExpansive
    {State : Type u} {Operation : Type v}
    {action : MetricOperationAction State Operation}
    (pkg : MetricOperationAction.SelectedMetricGaloisPackage action)
    {operation : Operation}
    (hMem : operation ∈ pkg.operations)
    (hSelected : action.selectedOperation operation) :
    action.NonExpansive operation :=
  pkg.operation_nonExpansive hMem hSelected

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

theorem finiteRepairSequence_allStepsDecrease
    {State : Type u} (sequence : FiniteRepairSequence State) :
    sequence.AllStepsDecrease :=
  sequence.allStepsDecrease

theorem contractiveRepairStep_target_contracts
    {State : Type u} (step : ContractiveRepairStep State) :
    step.denominator * step.targetDistance step.target ≤
      step.numerator * step.targetDistance step.source :=
  step.target_contracts

theorem fillingCostLowerBound_observationGap_le
    (pkg : FillingCostLowerBound) :
    pkg.observationGap ≤ pkg.lipschitzConstant * pkg.fillingCost :=
  pkg.observationGap_le_lipschitz_mul_fillingCost

theorem quantitativeHomotopyBound_observationDistance_le
    (pkg : QuantitativeHomotopyBound) :
    pkg.observationDistance ≤ pkg.lipschitzConstant * pkg.homotopyCost :=
  pkg.observationDistance_le

theorem finiteDehnBound_fillingArea_le
    {Loop : Type u}
    (pkg : FiniteDehnBound Loop)
    {loop : Loop}
    (hMem : loop ∈ pkg.candidates)
    (hBoundary : pkg.boundaryLength loop ≤ pkg.boundaryLimit) :
    pkg.fillingArea loop ≤ pkg.dehnValue :=
  pkg.fillingArea_le_dehnValue hMem hBoundary

theorem persistentNonFillability_no_candidate_filler_within_scale
    {Filler : Type u}
    (pkg : PersistentNonFillability Filler)
    {filler : Filler}
    (hCandidate : pkg.candidate filler)
    (hWithin : pkg.fillerCost filler ≤ pkg.scale) :
    False :=
  pkg.no_candidate_filler_within_scale hCandidate hWithin

theorem curvatureTransport_target_curvature_decreases
    {Axis : Type u} {State : Type v}
    (pkg : CurvatureTransport Axis State) :
    pkg.reading.curvatureMass pkg.targetAxis pkg.after <
      pkg.reading.curvatureMass pkg.targetAxis pkg.before :=
  pkg.target_curvature_decreases

theorem curvatureTransport_transported_curvature_increases
    {Axis : Type u} {State : Type v}
    (pkg : CurvatureTransport Axis State) :
    pkg.reading.curvatureMass pkg.transportedAxis pkg.before <
      pkg.reading.curvatureMass pkg.transportedAxis pkg.after :=
  pkg.transported_curvature_increases

theorem lipschitzRepresentation_analyticDistance_le
    {State : Type u} {Analytic : Type v}
    (rep : LipschitzRepresentation State Analytic)
    {X Y : State}
    (hComparable : rep.comparable X Y) :
    rep.analyticDistance (rep.represent X) (rep.represent Y) ≤
      rep.lipschitzConstant * rep.structuralDistance X Y :=
  rep.analyticDistance_le_lipschitz hComparable

theorem lipschitzRepresentation_analyticDistance_le_of_structuralDistance_le
    {State : Type u} {Analytic : Type v}
    (rep : LipschitzRepresentation State Analytic)
    {X Y : State}
    (hComparable : rep.comparable X Y)
    {epsilon : Nat}
    (hStructural : rep.structuralDistance X Y ≤ epsilon) :
    rep.analyticDistance (rep.represent X) (rep.represent Y) ≤
      rep.lipschitzConstant * epsilon :=
  rep.analyticDistance_le_of_structuralDistance_le
    hComparable hStructural

theorem biLipschitzRepresentation_structuralDistance_le
    {State : Type u} {Analytic : Type v}
    (rep : BiLipschitzRepresentation State Analytic)
    {X Y : State}
    (hComparable : rep.comparable X Y) :
    rep.lowerConstant * rep.structuralDistance X Y ≤
      rep.analyticDistance (rep.represent X) (rep.represent Y) :=
  rep.structuralDistance_le_analyticDistance hComparable

theorem spectralStabilityPackage_spectralDistance_le
    {State : Type u} {Spectral : Type v}
    (pkg : SpectralStabilityPackage State Spectral) :
    pkg.spectralDistance (pkg.represent pkg.source) (pkg.represent pkg.target) ≤
      pkg.lipschitzConstant * pkg.epsilon :=
  pkg.spectralDistance_le

theorem abstractInfimumInterface_lowerBound
    {Candidate : Type u}
    (interface : AbstractInfimumInterface Candidate)
    {candidate : Candidate}
    (hCandidate : interface.candidate candidate) :
    interface.infimumValue ≤ interface.cost candidate :=
  interface.lowerBound hCandidate

theorem abstractInfimumInterface_exists_approximatingWitness
    {Candidate : Type u}
    (interface : AbstractInfimumInterface Candidate)
    (tolerance : Nat) :
    ∃ candidate, interface.candidate candidate ∧
      interface.cost candidate ≤ interface.infimumValue + tolerance :=
  interface.exists_approximatingWitness tolerance

theorem abstractInfimumInterface_noAbstractCandidateBelow_infimum
    {Candidate : Type u}
    (interface : AbstractInfimumInterface Candidate) :
    interface.NoAbstractCandidateBelow :=
  interface.noAbstractCandidateBelow_infimum

theorem detailedDiagnostic_records_nonConclusions
    {Axis : Type u} {DistanceRef : Type v} {Operation : Type u}
    (conclusion :
      DetailedBoundedDiagnosticConclusion Axis DistanceRef Operation)
    (hLaw : conclusion.base.doesNotConcludeGlobalLawfulness)
    (hFlat : conclusion.base.doesNotConcludeGlobalFlatness)
    (hUnmeasured : conclusion.base.doesNotConcludeUnmeasuredZero) :
    conclusion.base.RecordsNonConclusions :=
  conclusion.records_nonConclusions hLaw hFlat hUnmeasured

theorem detailedDiagnostic_records_recommendation_boundary
    {Axis : Type u} {DistanceRef : Type v} {Operation : Type u}
    (conclusion :
      DetailedBoundedDiagnosticConclusion Axis DistanceRef Operation)
    (hBoundary : conclusion.recommendationBoundary)
    (hNotTheorem :
      conclusion.recommendationsAreNotRepairCorrectnessTheorems) :
    conclusion.RecordsRecommendationBoundary :=
  conclusion.records_recommendation_boundary hBoundary hNotTheorem

end Part4DistanceMeasureGeometry
end Formal.Arch
