import Formal.AG.Examples.FiniteModel
import Formal.AG.RepresentationAnalysis

noncomputable section

namespace AAT.AG
namespace FiniteModel
namespace RepresentationAnalysisPart7

open AAT.AG.RepresentationAnalysis
open CategoryTheory
open CategoryTheory.Limits
open Opposite

/-!
Finite witness examples for Part VII / R13.

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

theorem dependencyDAG_length_one_walkCount_eq_edgeFiber_card :
    matrixWalkCount dependencyDAG 1 DAGVertex.a DAGVertex.b =
      edgeFiberCard dependencyDAG DAGVertex.a DAGVertex.b :=
  matrixWalkCount_one_eq_edgeFiber_card dependencyDAG DAGVertex.a DAGVertex.b

theorem dependencyDAG_ab_edgeFiber_card :
    edgeFiberCard dependencyDAG DAGVertex.a DAGVertex.b = 1 := by
  have hcard : Fintype.card DAGEdge = 1 := by
    decide
  simpa [edgeFiberCard, dependencyDAG] using hcard

theorem dependencyDAG_nilpotent_at_card :
    adjacencyMatrixPower dependencyDAG (Fintype.card DAGVertex) = 0 :=
  adjacencyMatrixPower_eq_zero_at_card_of_acyclic dependencyDAG_acyclic

/-! ### (b) period separation toy model -/

theorem periodSeparation_toy_model :
    PeriodSeparationExample62.family.PeriodSeparation :=
  PeriodSeparationExample62.periodSeparation_theorem6_1

/-! ### (c) pseudo-circle strict period toy model -/

inductive PseudoCircleVertex where
  | source
  | target
deriving DecidableEq, Fintype

inductive PseudoCircleEdge where
  | sync
  | async
deriving DecidableEq, Fintype

abbrev PseudoCircleChain : Nat -> Type
  | 0 => PseudoCircleVertex -> Int
  | 1 => PseudoCircleEdge -> Int
  | _ + 2 => Int

def pseudoCircleChainAddCommGroup (n : Nat) : AddCommGroup (PseudoCircleChain n) :=
  match n with
  | 0 => Pi.addCommGroup
  | 1 => Pi.addCommGroup
  | _ + 2 => inferInstance

instance (n : Nat) : AddCommGroup (PseudoCircleChain n) :=
  pseudoCircleChainAddCommGroup n

def pseudoCircleBoundaryZero :
    PseudoCircleChain 1 →+ PseudoCircleChain 0 where
  toFun γ
    | PseudoCircleVertex.source => -γ PseudoCircleEdge.sync - γ PseudoCircleEdge.async
    | PseudoCircleVertex.target => γ PseudoCircleEdge.sync + γ PseudoCircleEdge.async
  map_zero' := by
    funext v
    cases v <;> simp
  map_add' := by
    intro γ δ
    funext v
    cases v <;> simp [Pi.add_apply] <;> ring_nf

def pseudoCircleBoundary : (n : Nat) -> PseudoCircleChain (n + 1) →+ PseudoCircleChain n
  | 0 => pseudoCircleBoundaryZero
  | 1 => 0
  | _ + 2 => 0

def pseudoCircleChainComplex : Cohomology.FiniteCechChainComplex where
  Chain := PseudoCircleChain
  chainAddCommGroup := pseudoCircleChainAddCommGroup
  boundary := pseudoCircleBoundary
  boundary_comp := by
    intro n γ
    cases n with
    | zero =>
        funext v
        cases v <;> rfl
    | succ n =>
        cases n <;> rfl

def pseudoCircleSyncChain : PseudoCircleChain 1
  | PseudoCircleEdge.sync => 1
  | PseudoCircleEdge.async => 0

def pseudoCircleAsyncChain : PseudoCircleChain 1
  | PseudoCircleEdge.sync => 0
  | PseudoCircleEdge.async => 1

def pseudoCircleCocycle : PseudoCircleChain 1
  | PseudoCircleEdge.sync => 1
  | PseudoCircleEdge.async => 0

def pseudoCircleCycle : PseudoCircleChain 1 :=
  pseudoCircleSyncChain - pseudoCircleAsyncChain

def pseudoCirclePairing (ω γ : PseudoCircleChain 1) : Int :=
  ω PseudoCircleEdge.sync * γ PseudoCircleEdge.sync +
    ω PseudoCircleEdge.async * γ PseudoCircleEdge.async

def pseudoCircleStrictPeriod : Int :=
  pseudoCirclePairing pseudoCircleCocycle pseudoCircleCycle

abbrev pseudoCircleCechPairing
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain n) :
    Cohomology.CechCochainChainPairing K pseudoCircleChainComplex where
  Period := Int
  periodAddCommGroup := inferInstance
  pairing
    | 1, ω, γ => pseudoCirclePairing (cochainReading 1 ω) γ
    | _, _, _ => 0

def pseudoCircleStrictPeriodRepresentative
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain n)
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
  cycle_boundary_zero := by
    change pseudoCircleChainComplex.boundaryOp 0 pseudoCircleCycle = 0
    funext v
    cases v <;> rfl
  boundaryCompatible := True
  boundaryCompatible_cert := trivial
  coboundaryCompatible := True
  coboundaryCompatible_cert := trivial

def pseudoCircleStrictPeriodData
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain n)
    (ω : K.Cn 1)
    (hω : letI := K.cochainAddCommGroup 2; K.d 1 ω = 0)
    (hclass : K.CoverRelativeHn 1)
    (hrep : RepresentsCohomologyClass K 1 hclass ω)
    {k : Type} [CommRing k] {p : AATSchReadingParameter site k}
    {F : RepresentationFamily p} {X : AATSch p}
    (i : F.Index) : StrictPeriodData F X :=
  (pseudoCircleStrictPeriodRepresentative K cochainReading ω hω hclass hrep).toStrictPeriodData i

theorem pseudoCircle_sync_async_shared_boundary :
    pseudoCircleChainComplex.boundaryOp 0 pseudoCircleSyncChain =
      pseudoCircleChainComplex.boundaryOp 0 pseudoCircleAsyncChain := by
  funext v
  cases v <;> rfl

theorem pseudoCircle_cycle_boundary_zero :
    FiniteCechCycleClosed pseudoCircleChainComplex 1 pseudoCircleCycle := by
  change pseudoCircleChainComplex.boundaryOp 0 pseudoCircleCycle = 0
  funext v
  cases v <;> rfl

theorem pseudoCircle_boundary_comp_zero (γ : pseudoCircleChainComplex.Chain 2) :
    pseudoCircleChainComplex.boundaryOp 0
      (pseudoCircleChainComplex.boundaryOp 1 γ) = 0 :=
  Cohomology.FiniteCechChainComplex.boundary_comp_zero
    pseudoCircleChainComplex 0 γ

theorem pseudoCircle_strictPeriod_eq_one :
    pseudoCircleStrictPeriod = 1 := by
  simp [pseudoCircleStrictPeriod, pseudoCirclePairing, pseudoCircleCocycle,
    pseudoCircleCycle, pseudoCircleSyncChain, pseudoCircleAsyncChain]

theorem pseudoCircle_strictPeriodRepresentative_eq_one
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain n)
    (ω : K.Cn 1)
    (hω : letI := K.cochainAddCommGroup 2; K.d 1 ω = 0)
    (hclass : K.CoverRelativeHn 1)
    (hrep : RepresentsCohomologyClass K 1 hclass ω)
    (hread : cochainReading 1 ω = pseudoCircleCocycle) :
    (pseudoCircleStrictPeriodRepresentative K cochainReading ω hω hclass hrep).strictPeriodValue =
      1 := by
  change pseudoCirclePairing (cochainReading 1 ω) pseudoCircleCycle = 1
  rw [hread]
  exact pseudoCircle_strictPeriod_eq_one

theorem pseudoCircle_strictPeriodData_reads_representative
    {𝒰 : Cohomology.CoverRelativeCechCover site}
    {Ob : Cohomology.ObstructionSheaf site}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (cochainReading : ∀ n : Nat, K.Cn n -> PseudoCircleChain n)
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

def enatInfimumDomain : CostInfimumDomain ℕ∞ :=
  CostInfimumDomain.completeLatticeInfimumDomain

abbrev marginDistanceToFlatness :
    DistanceToFlatnessProfile marginOperationDistance where
  Cost := ℕ∞
  costDomain := enatInfimumDomain
  costToDistanceValue _ := DistanceValue.measured 0
  FlatCandidate _ := PUnit
  flatState A _ := A
  factorsThroughFlat _ _ := True
  candidateDistance _ _ := (0 : ℕ∞)
  candidateDistance_reads_d_op := by
    intro A candidate
    cases A <;> rfl
  candidateFactorsThroughFlat _ _ := trivial

theorem marginDistanceToFlatness_dist_flat_glb (A : marginOperationDistance.GeometryState) :
    marginDistanceToFlatness.costDomain.isGreatestLowerBound
      (marginDistanceToFlatness.candidateDistance A)
      (marginDistanceToFlatness.dist_flat A) :=
  marginDistanceToFlatness.dist_flat_isGreatestLowerBound A

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
  quotientLowerBound gap fill := gap / 2 ≤ fill
  quotientLowerBound_holds := by
    intro P Q h
    rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < 2)]
    exact Nat.le_trans h (by omega)

theorem observationGap_toy_lipschitz_bound :
    observationGapToyProfile.observationGap ObservationPath.graph ObservationPath.semantic ≤
      observationGapToyProfile.lipschitzConstant *
        observationGapToyProfile.fillCost
          (observationGapToyProfile.selectedFiller
            ObservationPath.graph ObservationPath.semantic) :=
  observationGapToyProfile.observationGap_le_lipschitz_fillCost
    ObservationPath.graph ObservationPath.semantic

theorem observationGap_toy_div_lipschitz_lower_bound :
    observationGapToyProfile.observationGap ObservationPath.graph ObservationPath.semantic /
        observationGapToyProfile.lipschitzConstant ≤
      observationGapToyProfile.fillCost
        (observationGapToyProfile.selectedFiller
          ObservationPath.graph ObservationPath.semantic) :=
  observationGapToyProfile.observationGap_div_lipschitz_le_fillCost
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
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  AtomLabelReading := PUnit
  LawReading := PUnit
  ObstructionIdealReading := PUnit
  SignatureReading := PUnit
  InterpretationMapReading := PUnit
  atomLabelsCompatible _ _ _ := True
  lawReadingCompatible _ _ _ := True
  obstructionIdealCompatible _ _ _ := True
  signatureReadingCompatible _ _ _ := True
  interpretationMapCompatible _ _ _ := True
  id_atomLabelsCompatible _ _ := trivial
  id_lawReadingCompatible _ _ := trivial
  id_obstructionIdealCompatible _ _ := trivial
  id_signatureReadingCompatible _ _ := trivial
  id_interpretationMapCompatible _ _ := trivial
  comp_atomLabelsCompatible _ _ := trivial
  comp_lawReadingCompatible _ _ := trivial
  comp_obstructionIdealCompatible _ _ := trivial
  comp_signatureReadingCompatible _ _ := trivial
  comp_interpretationMapCompatible _ _ := trivial

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
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

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
  IsZeroClass alpha := alpha = ToyObstructionClass.zero
  zeroClass_isZero := rfl
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

theorem detectingRepresentation_toy_all_zero_actual_zero
    (alpha : toyDetectingFamily.ObstructionClass)
    (hzero : ∀ i : toyRepresentationFamily.Index,
      toyDetectingFamily.analyticZeroReading i alpha) :
    toyConservativity.IsZeroClass alpha :=
  toyConservativity.representation_zero_under_adequacy alpha hzero

theorem detectingRepresentation_toy_zero_is_actual_zero :
    toyConservativity.IsZeroClass ToyObstructionClass.zero :=
  detectingRepresentation_toy_all_zero_actual_zero ToyObstructionClass.zero (by
    intro i
    cases i <;> trivial)

/-! ### (g) finite synthesis package firing -/

def finiteSynthesisPartI : Site.PartIPrerequisites where
  carrier := carrier
  core := corePackage

def finiteSynthesisGeometry : Site.ArchitectureGeometry finiteSynthesisPartI where
  site := site

abbrev FiniteSynthesisAlgCat :=
  LawAlgebra.AATCommAlgCat.{0, 0} PUnit

noncomputable def finiteSynthesisAlgTerminal : FiniteSynthesisAlgCat :=
  CommRingCat.mkUnder (CommRingCat.of (ULift PUnit)) PUnit

noncomputable def finiteSynthesisAlgPresheaf :
    LawAlgebra.AlgebraValuedAATPresheaf site PUnit :=
  (CategoryTheory.Functor.const site.categoryᵒᵖ).obj finiteSynthesisAlgTerminal

noncomputable def finiteSynthesisAlgSheaf :
    LawAlgebra.LawAlgebraSheaf site PUnit where
  val := finiteSynthesisAlgPresheaf
  cond :=
    CategoryTheory.Presheaf.isSheaf_of_isTerminal site.topology
      (IsTerminal.ofUniqueHom
        (fun _ => Under.homMk (CommRingCat.ofHom {
          toFun := fun _ => PUnit.unit
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl
        }) (by
          ext x
          rfl))
        (by
          intro _Y _f
          ext x
          rfl))

def finiteSynthesisCoordFamily (W : Site.ArchitectureContext object) :
    LawAlgebra.CoordinateFamily W where
  Coord := Empty
  label := Empty.elim
  LocalData := Empty.elim

def finiteSynthesisRelations (W : Site.ArchitectureContext object) :
    LawAlgebra.StructuralRelationFamily (finiteSynthesisCoordFamily W) PUnit where
  Relation := LawAlgebra.FreeTypedCommAlg (finiteSynthesisCoordFamily W) PUnit
  polynomial r := r

theorem finiteSynthesisRelations_JStruct_top (W : Site.ArchitectureContext object) :
    (finiteSynthesisRelations W).JStruct = ⊤ := by
  apply top_unique
  intro q _hq
  rw [LawAlgebra.StructuralRelationFamily.JStruct,
    LawAlgebra.StructuralRelationFamily.RelStruct]
  rw [show Set.range (finiteSynthesisRelations W).polynomial =
      (Set.univ :
        Set (LawAlgebra.FreeTypedCommAlg (finiteSynthesisCoordFamily W) PUnit)) by
    ext p
    constructor
    · intro _h
      exact Set.mem_univ p
    · intro _h
      exact ⟨p, rfl⟩]
  exact Ideal.subset_span (Set.mem_univ q)

def finiteSynthesisRestrictionStable
    {source target : Site.ArchitectureContext object}
    (f : Site.ContextMorphism source target) :
    LawAlgebra.RestrictionStableStructuralRelations
      (finiteSynthesisRelations source) (finiteSynthesisRelations target) f where
  restriction := {
    variableImage := Empty.elim
  }
  maps_JStruct := by
    intro p _hp
    rw [finiteSynthesisRelations_JStruct_top source]
    change _ ∈
      (Set.univ :
        Set (LawAlgebra.FreeTypedCommAlg (finiteSynthesisCoordFamily source) PUnit))
    exact Set.mem_univ _

private theorem finiteSynthesisQuotientTop_eq
    {W : Site.ArchitectureContext object}
    (x y : (finiteSynthesisRelations W).RawAmbientLawAlgebra) :
    x = y := by
  refine Quotient.inductionOn x ?_
  intro p
  refine Quotient.inductionOn y ?_
  intro q
  apply Ideal.Quotient.eq.2
  rw [finiteSynthesisRelations_JStruct_top W]
  change p - q ∈
    (Set.univ : Set (LawAlgebra.FreeTypedCommAlg (finiteSynthesisCoordFamily W) PUnit))
  exact Set.mem_univ _

noncomputable def finiteSynthesisRawAmbient :
    LawAlgebra.RawAmbientPresheafBridge (A := object) PUnit where
  coordFamilySpec := finiteSynthesisCoordFamily
  relationFamily := finiteSynthesisRelations
  restrictionStable := finiteSynthesisRestrictionStable
  identity_law := by
    intro W _id
    ext x
    · exact finiteSynthesisQuotientTop_eq _ _
    · exact Empty.elim x
  composition_law := by
    intro _source _middle _target _f _g _comp
    ext x
    · exact finiteSynthesisQuotientTop_eq _ _
    · exact Empty.elim x

noncomputable def punitRingEquivOfSubsingleton
    (R : Type) [CommRing R] [Subsingleton R] : R ≃+* PUnit where
  toFun _ := PUnit.unit
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv x := by cases x; rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

noncomputable def finiteSynthesisRawAmbientAlgebra :
    LawAlgebra.RawAmbientAlgebraPresheafBridge site PUnit where
  rawAmbient := finiteSynthesisRawAmbient
  rawPresheaf := finiteSynthesisAlgPresheaf
  identifiesObject := by
    intro _W
    exact punitRingEquivOfSubsingleton _
  restriction_naturality := by
    intro _source _target _h _x
    rfl

noncomputable def finiteSynthesisSheafification :
    LawAlgebra.LawAlgebraSheafificationBridge site PUnit where
  raw := finiteSynthesisAlgPresheaf
  plus := finiteSynthesisAlgSheaf
  canonical := 𝟙 finiteSynthesisAlgPresheaf
  isSheafification := by
    intro _F η
    refine ⟨η, ?_, ?_⟩
    · simp
    · intro lift hlift
      simpa using hlift

noncomputable def finiteSynthesisPresentation
    (W : site.category) :
    LawAlgebra.SelectedLawAlgebraPresentation finiteSynthesisSheafification W where
  Generator := PUnit
  Relation := PUnit
  rawGenerator _ := PUnit.unit
  sheafifiedGenerator _ := PUnit.unit
  rawRelation _ := PUnit.unit
  sheafifiedRelation _ := PUnit.unit
  presentsRaw := True
  presentsSheafified := True
  canonical_preserves_generator := by
    intro _g
    rfl
  canonical_preserves_relation := by
    intro _r
    rfl

noncomputable def finiteSynthesisPresentationStable :
    LawAlgebra.PresentationStableAATSite finiteSynthesisSheafification where
  presentation := finiteSynthesisPresentation
  stable := by
    intro _W
    exact ⟨trivial, trivial⟩

noncomputable def finiteSynthesisLawAlgebraSheafPackage :
    LawAlgebra.LawAlgebraSheafPackage site PUnit where
  rawAmbient := finiteSynthesisRawAmbientAlgebra
  sheafification := finiteSynthesisSheafification
  raw_eq := rfl
  presentationStable := finiteSynthesisPresentationStable

noncomputable def finiteSynthesisTypeSheaf : Site.AATSh site where
  val := (CategoryTheory.Functor.const site.categoryᵒᵖ).obj PUnit
  cond :=
    CategoryTheory.Presheaf.isSheaf_of_isTerminal site.topology
      (IsTerminal.ofUniqueHom
        (fun _ => fun _ => PUnit.unit)
        (by
          intro _X f
          funext x
          cases f x
          rfl))

noncomputable def finiteSynthesisAffineChart :
    LawAlgebra.AffineChart.AffineAATChart.{0, 0, 0} PUnit where
  AlgebraCarrier := PUnit
  commRing := inferInstance
  algebra := inferInstance
  spec := {
    Decoration := PUnit
    decoration := PUnit.unit
    obstructionIdeal := ⊥
  }

noncomputable def finiteSynthesisRingedTopos :
    LawAlgebra.Scheme.RingedAATTopos.{0, 0, 0} site PUnit where
  aatSheafObject := finiteSynthesisTypeSheaf
  structureSheaf := finiteSynthesisLawAlgebraSheafPackage
  locallyRingedSpace :=
    LawAlgebra.Scheme.affineChartMathlibSpecLocallyRingedSpace
      PUnit finiteSynthesisAffineChart

noncomputable def finiteSynthesisArchitectureScheme :
    LawAlgebra.Scheme.ArchitectureScheme.{0, 0, 0, 0, 0} site PUnit :=
  LawAlgebra.Scheme.ArchitectureScheme.singleAffineSpec site PUnit
    finiteSynthesisRingedTopos finiteSynthesisAffineChart rfl

noncomputable def finiteSynthesisLawfulSection :
    LawAlgebra.LawfulLocus.LawfulSectionData.{0, 0} PUnit (⊥ : Ideal PUnit) where
  SectionRing := PUnit
  commRing := inferInstance
  pullback := RingHom.id PUnit

def finiteSynthesisCover : Cohomology.CoverRelativeCechCover site where
  base := siteBase
  Index := PUnit
  chart _ := siteBase
  inclusion _ := 𝟙 siteBase
  simplex _ := PUnit
  overlap _ _ := siteBase
  face _ _ _ := PUnit.unit
  faceRestriction _ _ _ := 𝟙 siteBase

def finiteSynthesisObstructionSheaf : Cohomology.ObstructionSheaf site where
  carrier := Site.AATSh.toAATSheaf finiteSynthesisTypeSheaf
  addCommGroup := by
    intro _W
    change AddCommGroup PUnit
    infer_instance
  map_zero := by
    intro _source _target _f
    rfl
  map_add := by
    intro _source _target _f x y
    cases x
    cases y
    rfl

def finiteSynthesisCechComplex :
    Cohomology.CoverRelativeCechComplex finiteSynthesisCover
      finiteSynthesisObstructionSheaf where
  cochainAddCommGroup := by
    intro _n
    change AddCommGroup (PUnit -> PUnit)
    infer_instance
  alternatingFaceCombination := fun _n _faces _σ => PUnit.unit
  differential := by
    intro _n
    change (PUnit -> PUnit) →+ (PUnit -> PUnit)
    exact {
      toFun := fun _ _ => PUnit.unit
      map_zero' := by
        funext _σ
        rfl
      map_add' := by
        intro x y
        funext σ
        cases x σ
        cases y σ
        rfl
    }
  differential_eq_alternatingFaceCombination := by
    intro _n c
    funext σ
    cases c σ
    rfl
  differential_comp := by
    intro _n c
    funext σ
    cases c σ
    rfl

def finiteSynthesisRepairProfile :
    Derived.RepairProfile.RepairComparisonProfile.{0} where
  Section := PUnit
  Geometry := PUnit
  sectionComparison _ _ := True
  geometryComparison _ _ := True
  sectionImproves _ _ := True
  geometryImproves _ _ := True
  section_improves_implies_comparison := by
    intro _s' _s _h
    trivial
  geometry_improves_implies_comparison := by
    intro _X' _X _h
    trivial

def finiteSynthesisStratumParameter :
    SingularityMonodromyStack.StratumReadingParameter site where
  signatureAxes := toySignatureAxes
  Coeff := PUnit
  selectedCoeff := PUnit.unit

noncomputable def finiteSynthesisArchitectureStratum :
    SingularityMonodromyStack.ArchitectureStratum.{0, 0, 0, 0, 0}
      finiteSynthesisStratumParameter PUnit where
  geometry := finiteSynthesisArchitectureScheme
  Point := PUnit
  carrier := Set.univ
  role := SingularityMonodromyStack.StratumRole.component
  label := "finite-synthesis-singleton"
  selectedSubobject := True
  selectedSubobject_cert := trivial
  locallyClosed := True
  locallyClosed_cert := trivial
  decorationCompatible := True
  decorationCompatible_cert := trivial
  readingCompatible := True
  readingCompatible_cert := trivial

def finiteSynthesisReadingParameter :
    AATSchReadingParameter.{0, 0, 0, 0, 0} site PUnit where
  SchemeMorphism _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  AtomLabelReading := PUnit
  LawReading := PUnit
  ObstructionIdealReading := PUnit
  SignatureReading := PUnit
  InterpretationMapReading := PUnit
  atomLabelsCompatible _ _ _ := True
  lawReadingCompatible _ _ _ := True
  obstructionIdealCompatible _ _ _ := True
  signatureReadingCompatible _ _ _ := True
  interpretationMapCompatible _ _ _ := True
  id_atomLabelsCompatible _ _ := trivial
  id_lawReadingCompatible _ _ := trivial
  id_obstructionIdealCompatible _ _ := trivial
  id_signatureReadingCompatible _ _ := trivial
  id_interpretationMapCompatible _ _ := trivial
  comp_atomLabelsCompatible _ _ := trivial
  comp_lawReadingCompatible _ _ := trivial
  comp_obstructionIdealCompatible _ _ := trivial
  comp_signatureReadingCompatible _ _ := trivial
  comp_interpretationMapCompatible _ _ := trivial

def finiteSynthesisAnalyticRepresentation :
    AnalyticRepresentation finiteSynthesisReadingParameter PUnit where
  targetCategory := toyTargetCategory
  obj _ := PUnit.unit
  map _ := PUnit.unit
  map_id _ := rfl
  map_comp _ := rfl

def finiteSynthesisRepresentationFamily :
    RepresentationFamily finiteSynthesisReadingParameter where
  Index := ToyRepIndex
  Target _ := PUnit
  representation _ := finiteSynthesisAnalyticRepresentation

def finiteSynthesisDetectingFamily :
    UDetectingRepresentationFamily finiteSynthesisRepresentationFamily where
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

def finiteSynthesisAnalyticReadingContext :
    AnalyticReadingContext.{0, 0, 0, 0, 0, 0} object
      finiteSynthesisReadingParameter where
  AtomVocabulary := PUnit
  atomVocabularyOf _ := PUnit.unit
  lawUniverse := lawUniverse
  CoverageTopology := PUnit
  selectedCoverage := PUnit.unit
  coefficientSheaf := PUnit
  representationFamily := finiteSynthesisRepresentationFamily
  distanceMassContext := marginDistanceMassContext
  selectedWitnessFamily := PUnit
  selectedWitness := PUnit.unit
  selectedSignatureAxes := toySignatureAxes
  signatureProfile := SignatureReadingProfile.ofSignatureAxes toySignatureAxes
  detectingFamily := finiteSynthesisDetectingFamily
  coverageAdequacy := True
  witnessExactness := True
  axisExactness := True
  coefficientDiscipline := True
  completenessLevel := CompletenessSpectrum.conservative

noncomputable def finiteSynthesisAATSynthesisAssumptions :
    AATSynthesisAssumptions.{0, 0, 0, 0, 0, 0} finiteSynthesisPartI PUnit where
  architectureGeometry := finiteSynthesisGeometry
  ringedAATTopos := finiteSynthesisRingedTopos
  architectureScheme := finiteSynthesisArchitectureScheme
  ringedAATTopos_eq_scheme := rfl
  LawCoordinateAlgebra := PUnit
  lawCoordinateCommRing := inferInstance
  obstructionIdeal := ⊥
  lawfulLocus :=
    LawAlgebra.LawfulLocus.lawfulLocus PUnit (⊥ : Ideal PUnit)
  lawfulLocus_eq := rfl
  lawfulSection := finiteSynthesisLawfulSection
  cover := finiteSynthesisCover
  obstructionSheaf := finiteSynthesisObstructionSheaf
  obstructionCohomology := finiteSynthesisCechComplex
  derivedLawGeometry := finiteSynthesisRepairProfile
  stratumParameter := finiteSynthesisStratumParameter
  singularityMonodromyStack := finiteSynthesisArchitectureStratum
  readingParameter := finiteSynthesisReadingParameter
  representationPeriodMetricAnalysis := finiteSynthesisAnalyticReadingContext

noncomputable def finiteSynthesisAATSynthesisPackage :
    AATSynthesisPackage finiteSynthesisPartI PUnit :=
  finiteSynthesisAATSynthesisAssumptions.toPackage

theorem finiteSynthesisAATSynthesisPackage_eq_toPackage :
    finiteSynthesisAATSynthesisPackage =
      finiteSynthesisAATSynthesisAssumptions.toPackage :=
  rfl

def finiteSynthesis_algebraicGeometricAATSynthesis_fires :=
  algebraicGeometricAATSynthesis finiteSynthesisAATSynthesisAssumptions

end RepresentationAnalysisPart7
end FiniteModel
end AAT.AG
