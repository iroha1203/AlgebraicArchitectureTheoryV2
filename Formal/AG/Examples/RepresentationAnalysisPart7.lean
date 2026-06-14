import Formal.AG.Examples.FiniteModel
import Formal.AG.Cohomology.FiniteExamples
import Formal.AG.RepresentationAnalysis

noncomputable section

namespace AAT.AG
namespace FiniteModel
namespace RepresentationAnalysisPart7

open AAT.AG.RepresentationAnalysis

/-!
Finite witness examples for PRD-7 / R13.

Each example is deliberately selected and finite.  The file checks the Part VII
theorem APIs without adding measurement verdicts or external artifact claims.
-/

/-! ### (a) graph / matrix toy model -/

inductive DAGVertex where
  | a
  | b
deriving DecidableEq, Fintype

inductive DAGEdge where
  | ab
deriving DecidableEq, Fintype

inductive DAGLabel where
  | depends
deriving DecidableEq, Fintype

def dependencyDAG :
    FiniteDirectedGraphTarget DAGVertex DAGEdge DAGLabel where
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  source
    | DAGEdge.ab => DAGVertex.a
  target
    | DAGEdge.ab => DAGVertex.b
  relationLabel
    | DAGEdge.ab => DAGLabel.depends

theorem noWalk_b_to_a :
    ∀ {edges : List DAGEdge},
      ¬ FiniteDirectedGraphTarget.DirectedWalk
        dependencyDAG DAGVertex.b DAGVertex.a edges := by
  intro edges walk
  cases walk with
  | cons e tail hsource hrest =>
      cases e
      cases hsource

theorem dependencyDAG_acyclic :
    FiniteDirectedGraphTarget.Acyclic dependencyDAG := by
  refine ⟨?_⟩
  rintro ⟨start, edges, nonempty, closedWalk⟩
  cases h : edges with
  | nil =>
      exact nonempty h
  | cons e tail =>
      cases closedWalk with
      | nil v =>
          simp at h
      | cons e' tail' hsource hrest =>
          cases e'
          cases hsource
          exact noWalk_b_to_a hrest

def dependencyDAGMatrix :
    MatrixRepresentationTarget DAGVertex DAGEdge DAGLabel :=
  MatrixRepresentationTarget.ofGraph dependencyDAG

theorem dependencyDAG_walkCount_ab_positive :
    0 < matrixWalkCount dependencyDAG 1 DAGVertex.a DAGVertex.b := by
  apply (matrixWalkCount_pos_iff_countedDirectedWalk dependencyDAG 1
    DAGVertex.a DAGVertex.b).mpr
  exact ⟨FiniteDirectedGraphTarget.CountedDirectedWalk.cons
    DAGEdge.ab 0 rfl (FiniteDirectedGraphTarget.CountedDirectedWalk.nil DAGVertex.b)⟩

theorem dependencyDAG_matrixWalkReading_ab :
    (adjacencyMatrixPower dependencyDAG 1) DAGVertex.a DAGVertex.b =
      matrixWalkCount dependencyDAG 1 DAGVertex.a DAGVertex.b :=
  adjacencyMatrixPower_apply_eq_matrixWalkCount dependencyDAG 1 DAGVertex.a DAGVertex.b

theorem dependencyDAG_nilpotent_at_card :
    adjacencyMatrixPower dependencyDAG (Fintype.card DAGVertex) = 0 :=
  adjacencyMatrixPower_eq_zero_at_card_of_acyclic dependencyDAG_acyclic

/-! ### (b) period separation toy model -/

theorem periodSeparation_toy_model :
    PeriodSeparationExample62.family.PeriodSeparation :=
  PeriodSeparationExample62.periodSeparation_theorem6_1

/-! ### (c) pseudo-circle strict period toy model -/

abbrev PseudoCircleEdge :=
  Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge

abbrev PseudoCircleChain := PseudoCircleEdge -> Int

instance : AddCommGroup PseudoCircleChain :=
  Pi.addCommGroup

def pseudoCircleChainComplex : Cohomology.FiniteCechChainComplex where
  Chain _ := PseudoCircleChain
  chainAddCommGroup _ := inferInstance
  boundary _ := 0
  boundary_comp _ _ := rfl

def pseudoCircleCocycle : PseudoCircleChain
  | Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.AB => 1
  | Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.BC => 0
  | Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.CA => 0

def pseudoCircleCycle : PseudoCircleChain
  | Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.AB => 1
  | Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.BC => -1
  | Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.CA => 0

def pseudoCirclePairing (ω γ : PseudoCircleChain) : Int :=
  ω Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.AB *
      γ Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.AB +
    ω Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.BC *
      γ Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.BC +
    ω Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.CA *
      γ Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.CA

def pseudoCircleStrictPeriod : Int :=
  pseudoCirclePairing pseudoCircleCocycle pseudoCircleCycle

abbrev pseudoCircleCechPairing
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain) :
    Cohomology.CechCochainChainPairing K pseudoCircleChainComplex where
  Period := Int
  periodAddCommGroup := inferInstance
  pairing n ω γ := pseudoCirclePairing (cochainReading n ω) γ

def pseudoCircleStrictPeriodRepresentative
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain)
    (ω : K.Cn 1)
    (hω : letI := K.cochainAddCommGroup 2; K.d 1 ω = 0)
    (hclass : K.CoverRelativeHn 1)
    (hrep : RepresentsCohomologyClass K 1 hclass ω) :
    FiniteCechStrictPeriodRepresentative K pseudoCircleChainComplex
      (pseudoCircleCechPairing K cochainReading) where
  degree := 1
  cohomologyClass := hclass
  cocycle := ω
  cocycle_is_cocycle := hω
  representsCohomologyClass := hrep
  cycle := pseudoCircleCycle
  cycle_boundary_zero := rfl
  boundaryCompatible := True
  boundaryCompatible_cert := trivial
  coboundaryCompatible := True
  coboundaryCompatible_cert := trivial

def pseudoCircleStrictPeriodData
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain)
    (ω : K.Cn 1)
    (hω : letI := K.cochainAddCommGroup 2; K.d 1 ω = 0)
    (hclass : K.CoverRelativeHn 1)
    (hrep : RepresentsCohomologyClass K 1 hclass ω)
    {k : Type} [CommRing k] {p : AATSchReadingParameter site k}
    {F : RepresentationFamily p} {X : AATSch p}
    (i : F.Index) : StrictPeriodData F X :=
  (pseudoCircleStrictPeriodRepresentative K cochainReading ω hω hclass hrep).toStrictPeriodData i

theorem pseudoCircle_boundary_comp_zero (γ : pseudoCircleChainComplex.Chain 2) :
    pseudoCircleChainComplex.boundaryOp 0
      (pseudoCircleChainComplex.boundaryOp 1 γ) = 0 :=
  Cohomology.FiniteCechChainComplex.boundary_comp_zero
    pseudoCircleChainComplex 0 γ

theorem pseudoCircle_strictPeriod_eq_one :
    pseudoCircleStrictPeriod = 1 := by
  rfl

theorem pseudoCircle_strictPeriodRepresentative_eq_one
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain)
    (ω : K.Cn 1)
    (hω : letI := K.cochainAddCommGroup 2; K.d 1 ω = 0)
    (hclass : K.CoverRelativeHn 1)
    (hrep : RepresentsCohomologyClass K 1 hclass ω)
    (hread : cochainReading 1 ω = pseudoCircleCocycle) :
    (pseudoCircleStrictPeriodRepresentative K cochainReading ω hω hclass hrep).strictPeriodValue =
      1 := by
  simp [pseudoCircleStrictPeriodRepresentative,
    FiniteCechStrictPeriodRepresentative.strictPeriodValue,
    Cohomology.CechCochainChainPairing.pair,
    pseudoCircleCechPairing, pseudoCirclePairing, hread,
    pseudoCircleCocycle, pseudoCircleCycle]

theorem pseudoCircle_strictPeriodData_reads_representative
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain)
    (ω : K.Cn 1)
    (hω : letI := K.cochainAddCommGroup 2; K.d 1 ω = 0)
    (hclass : K.CoverRelativeHn 1)
    (hrep : RepresentsCohomologyClass K 1 hclass ω)
    {k : Type} [CommRing k] {p : AATSchReadingParameter site k}
    {F : RepresentationFamily p} {X : AATSch p}
    (i : F.Index) :
    (pseudoCircleStrictPeriodData K cochainReading ω hω hclass hrep (F := F) (X := X)
      i).strictObstructionPeriod =
        (pseudoCircleStrictPeriodRepresentative K cochainReading ω hω hclass hrep).strictPeriodValue := by
  rfl

/-! ### shared finite metric context for (d) -/

inductive MarginState where
  | safe
  | boundary
deriving DecidableEq, Fintype

def marginOperationCost : OperationCost object where
  Operation := PUnit
  cost _ := DistanceValue.measured 1
  appliesTo _ _ := True

def marginPathLength : PathLength marginOperationCost where
  Path := PUnit
  startsAt _ := FiniteAtom.componentA
  endsAt _ := FiniteAtom.componentA
  length _ := DistanceValue.measured 1
  operationsMeasuredSeparately := True
  operationsMeasuredSeparately_holds := trivial

def marginHomotopyFillingCost : HomotopyFillingCost object where
  HomotopyBoundary := PUnit
  fillingCost _ := DistanceValue.measured 0
  finiteWitnessBoundary := True
  finiteWitnessBoundary_holds := trivial

abbrev marginOperationDistance : OperationDistanceProfile object where
  operationCost := marginOperationCost
  pathLength := marginPathLength
  homotopyFillingCost := marginHomotopyFillingCost
  GeometryState := MarginState
  operationPath _ _ := PUnit
  pathCost {A} {B} _ :=
    match A, B with
    | MarginState.safe, MarginState.safe => DistanceValue.measured 0
    | MarginState.boundary, MarginState.boundary => DistanceValue.measured 0
    | _, _ => DistanceValue.measured 1
  pathLengthValue _ := DistanceValue.measured 1
  fillingCostValue _ := DistanceValue.measured 0
  distance
    | MarginState.safe, MarginState.safe => DistanceValue.measured 0
    | MarginState.boundary, MarginState.boundary => DistanceValue.measured 0
    | _, _ => DistanceValue.measured 1
  distance_reading := by
    intro A B
    cases A <;> cases B <;> exact ⟨PUnit.unit, rfl⟩

def natInfimumDomain : CostInfimumDomain Nat where
  infimum _ := 0
  isLowerBound _ _ := True
  isGreatestLowerBound _ _ := True
  infimum_isGreatestLowerBound _ := trivial

abbrev marginDistanceToFlatness :
    DistanceToFlatnessProfile marginOperationDistance where
  Cost := Nat
  costDomain := natInfimumDomain
  costToDistanceValue n := DistanceValue.measured n
  FlatCandidate _ := PUnit
  flatState A _ := A
  factorsThroughFlat _ _ := True
  candidateDistance _ _ := 0
  candidateDistance_reads_d_op := by
    intro A candidate
    cases A <;> rfl
  candidateFactorsThroughFlat _ _ := trivial

def marginObstructionMeasure : SelectedObstructionMeasure object where
  ObstructionSupport := PUnit
  IdealSupport := PUnit
  mu_Ob _ := DistanceValue.measured 0
  mu_I _ := DistanceValue.measured 0
  selectedObstructionSupport := Set.univ
  selectedIdealSupport := Set.univ
  muObSupported _ _ := trivial
  muISupported _ _ := trivial

abbrev marginObstructionMass :
    FiniteSupportObstructionMass marginObstructionMeasure MarginState where
  finiteSupport _ := [PUnit.unit]
  supportCoversSelected _ obstruction _ := by
    cases obstruction
    simp
  measuredContribution _ _ := 0
  measuredContribution_eq_zero_of_not_mem _ _ _ := rfl
  finiteSum _ _ := 0
  finiteIntegral _ _ := 0
  mass _ := 0
  mass_eq_finiteSum _ := rfl
  finiteIntegral_eq_finiteSum _ := rfl

abbrev marginDistanceMassContext : DistanceFlatnessMassContext object where
  operationDistance := marginOperationDistance
  distanceToFlatness := marginDistanceToFlatness
  obstructionMeasure := marginObstructionMeasure
  obstructionMass := marginObstructionMass

def marginBoundaryDistance : MarginState -> MarginState -> DistanceValue Nat
  | MarginState.safe, MarginState.boundary => DistanceValue.measured 3
  | MarginState.boundary, MarginState.safe => DistanceValue.measured 3
  | MarginState.safe, MarginState.safe => DistanceValue.measured 0
  | MarginState.boundary, MarginState.boundary => DistanceValue.measured 0

def marginBoundaryDistanceNat : MarginState -> MarginState -> Nat
  | MarginState.safe, MarginState.boundary => 3
  | MarginState.boundary, MarginState.safe => 3
  | MarginState.safe, MarginState.safe => 0
  | MarginState.boundary, MarginState.boundary => 0

abbrev marginProfile : MarginProfile marginDistanceMassContext where
  SafeRegion := {MarginState.safe}
  UnsafeBoundary := {MarginState.boundary}
  boundaryDistance := marginBoundaryDistance
  margin
    | MarginState.safe => DistanceValue.measured 3
    | MarginState.boundary => DistanceValue.measured 0
  margin_reading
    | MarginState.safe => ⟨MarginState.boundary, by simp, rfl⟩
    | MarginState.boundary => ⟨MarginState.boundary, by simp, rfl⟩
  safeRegionMembership A := A = MarginState.safe
  safeRegionMembership_iff_mem A := by
    change (A = MarginState.safe) ↔ A ∈ ({MarginState.safe} : Set MarginState)
    cases A <;> simp

def marginStabilityToyProfile : MarginStabilityProfile marginProfile where
  start := MarginState.safe
  endpoint := MarginState.safe
  pathLength := 1
  endpointDistance := 1
  marginBudget := 3
  marginBudget_reads_margin := rfl
  boundaryDistanceNat := marginBoundaryDistanceNat
  boundaryDistance_reads_nat := by
    intro A B
    change marginBoundaryDistance A B = DistanceValue.measured (marginBoundaryDistanceNat A B)
    cases A <;> cases B <;> rfl
  start_safe := rfl
  endpointDistance_le_pathLength := by omega
  pathLength_lt_margin := by omega
  margin_le_boundaryDistance := by
    intro B hB
    change MarginState at B
    cases B <;> simp [marginBoundaryDistanceNat] at hB ⊢
  triangle_boundaryDistance := by
    intro B hB
    change MarginState at B
    cases B <;> simp [marginBoundaryDistanceNat] at hB ⊢
  boundary_self_distance_zero := by
    intro B hB
    change MarginState at B
    cases B <;> simp [marginBoundaryDistanceNat] at hB ⊢
  safeRegion_avoids_boundary := by
    intro A hsafe hboundary
    change MarginState at A
    cases A <;> simp at hsafe hboundary
  safeRegion_of_avoids_boundary := by
    intro A hboundary
    change MarginState at A
    cases A with
    | safe => rfl
    | boundary =>
        exact False.elim (hboundary (by simp))

/-! ### (d) margin stability toy model -/

theorem marginStability_toy_endpoint_safe :
    marginProfile.safeRegionMembership MarginState.safe :=
  marginStabilityToyProfile.marginStability_endpoint_safe

theorem marginStability_toy_no_boundary_crossing :
    MarginState.safe ∉ marginProfile.UnsafeBoundary :=
  marginStabilityToyProfile.marginStability_no_boundary_crossing

/-! ### (e) observation gap toy model -/

inductive ObservationPath where
  | graph
  | semantic
deriving DecidableEq, Fintype

def observationGapToyProfile : ObservationGapLowerBoundProfile where
  Path := ObservationPath
  Filler := PUnit
  observationGap
    | ObservationPath.graph, ObservationPath.semantic => 2
    | ObservationPath.semantic, ObservationPath.graph => 2
    | _, _ => 0
  loopFromPair _ _ := PUnit
  selectedLoop _ _ := PUnit.unit
  fillerForLoop _ _ _ := PUnit.unit
  fillCost _ := 2
  generatorCost _ := 1
  lipschitzConstant := 2
  lipschitzConstant_pos := by omega
  observationMapLipschitz := by
    intro P Q
    cases P <;> cases Q <;> simp
  generatorCost_le_fillCost := by
    intro P Q
    simp
  quotientLowerBound gap fill := gap ≤ 2 * fill
  quotientLowerBound_holds := by
    intro P Q h
    exact Nat.le_trans h (by simp)

theorem observationGap_toy_lipschitz_bound :
    observationGapToyProfile.observationGap ObservationPath.graph ObservationPath.semantic ≤
      observationGapToyProfile.lipschitzConstant *
        observationGapToyProfile.fillCost
          (observationGapToyProfile.selectedFiller
            ObservationPath.graph ObservationPath.semantic) :=
  observationGapToyProfile.observationGap_le_lipschitz_fillCost
    ObservationPath.graph ObservationPath.semantic

theorem observationGap_toy_quotient_certificate :
    observationGapToyProfile.quotientLowerBound
      (observationGapToyProfile.observationGap ObservationPath.graph ObservationPath.semantic)
      (observationGapToyProfile.fillCost
        (observationGapToyProfile.selectedFiller
          ObservationPath.graph ObservationPath.semantic)) :=
  observationGapToyProfile.quotientLowerBound_certificate
    ObservationPath.graph ObservationPath.semantic

/-! ### (f) detecting representation toy model -/

def toyReadingParameter :
    AATSchReadingParameter.{0, 0, 0, 0, 0} site Int where
  SchemeMorphism _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  AtomLabelReading := PUnit
  LawReading := PUnit
  ObstructionIdealReading := PUnit
  SignatureReading := PUnit
  InterpretationMapReading := PUnit

inductive ToyRepIndex where
  | graph
  | semantic
deriving DecidableEq, Fintype

inductive ToyObstructionClass where
  | zero
  | syncGap
  | semanticGap
deriving DecidableEq, Fintype

def toyTargetCategory : AnalyticTargetCategory PUnit where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

def toyAnalyticRepresentation :
    AnalyticRepresentation toyReadingParameter PUnit where
  targetCategory := toyTargetCategory
  obj _ := PUnit.unit
  map _ := PUnit.unit
  map_id _ := rfl
  map_comp _ := rfl

def toyRepresentationFamily :
    RepresentationFamily toyReadingParameter where
  Index := ToyRepIndex
  Target _ := PUnit
  representation _ := toyAnalyticRepresentation

def toyDetectingFamily :
    UDetectingRepresentationFamily toyRepresentationFamily where
  ObstructionClass := ToyObstructionClass
  analyticZeroReading
    | ToyRepIndex.graph, ToyObstructionClass.zero => True
    | ToyRepIndex.graph, ToyObstructionClass.syncGap => False
    | ToyRepIndex.graph, ToyObstructionClass.semanticGap => True
    | ToyRepIndex.semantic, ToyObstructionClass.zero => True
    | ToyRepIndex.semantic, ToyObstructionClass.syncGap => True
    | ToyRepIndex.semantic, ToyObstructionClass.semanticGap => False
  WitnessZero_U alpha := alpha = ToyObstructionClass.zero
  detects := by
    intro alpha hzero
    cases alpha with
    | zero => rfl
    | syncGap => exact False.elim (hzero ToyRepIndex.graph)
    | semanticGap => exact False.elim (hzero ToyRepIndex.semantic)
  completenessLevel := CompletenessSpectrum.conservative

def toySignatureAxes : SignatureAxes carrier where
  Axis := PUnit
  selected _ := True
  zero _ _ := True

def toyAnalyticReadingContext :
    AnalyticReadingContext.{0, 0, 0, 0, 0, 0} object toyReadingParameter where
  AtomVocabulary := PUnit
  atomVocabularyOf _ := PUnit.unit
  lawUniverse := lawUniverse
  CoverageTopology := PUnit
  selectedCoverage := PUnit.unit
  coefficientSheaf := PUnit
  representationFamily := toyRepresentationFamily
  distanceMassContext := marginDistanceMassContext
  selectedWitnessFamily := PUnit
  selectedWitness := PUnit.unit
  selectedSignatureAxes := toySignatureAxes
  signatureProfile := SignatureReadingProfile.ofSignatureAxes toySignatureAxes
  detectingFamily := toyDetectingFamily
  coverageAdequacy := True
  witnessExactness := True
  axisExactness := True
  coefficientDiscipline := True
  completenessLevel := CompletenessSpectrum.conservative

def toyConservativity :
    RepresentationConservativityUnderAdequacy toyAnalyticReadingContext where
  zeroClass := ToyObstructionClass.zero
  coverageAdequate := trivial
  witnessExact := trivial
  axisExact := trivial
  coefficientDisciplined := trivial
  witnessZero_eq_zero := by
    intro alpha h
    exact h

theorem detectingRepresentation_toy_syncGap_not_all_zero :
    ¬ (∀ i : toyRepresentationFamily.Index,
      toyDetectingFamily.analyticZeroReading i ToyObstructionClass.syncGap) := by
  intro h
  exact h ToyRepIndex.graph

theorem detectingRepresentation_toy_semanticGap_not_all_zero :
    ¬ (∀ i : toyRepresentationFamily.Index,
      toyDetectingFamily.analyticZeroReading i ToyObstructionClass.semanticGap) := by
  intro h
  exact h ToyRepIndex.semantic

theorem detectingRepresentation_toy_all_zero_imp_zero
    (alpha : toyDetectingFamily.ObstructionClass)
    (hzero : ∀ i : toyRepresentationFamily.Index,
      toyDetectingFamily.analyticZeroReading i alpha) :
    alpha = toyConservativity.zeroClass :=
  toyConservativity.representation_conservativity_under_adequacy alpha hzero

theorem detectingRepresentation_toy_zero_conservative :
    ToyObstructionClass.zero = toyConservativity.zeroClass :=
  detectingRepresentation_toy_all_zero_imp_zero ToyObstructionClass.zero (by
    intro i
    cases i <;> trivial)

end RepresentationAnalysisPart7
end FiniteModel
end AAT.AG
