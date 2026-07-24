import Formal.AG.Examples.FiniteModel
import Formal.AG.Examples.StandardGeometryReferenceModels
import Formal.AG.RepresentationAnalysis

noncomputable section

namespace AAT.AG
namespace FiniteModel
namespace RepresentationAnalysisPart7

open AAT.AG.RepresentationAnalysis
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Classical

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

/-- Vertices of the selected three-object chain used for the length-two firing. -/
inductive LengthTwoWalkVertex where
  | a
  | b
  | c
deriving DecidableEq, Fintype

/-- The two ordered edges of the selected length-two chain. -/
inductive LengthTwoWalkEdge where
  | ab
  | bc
deriving DecidableEq, Fintype

/-- Relation label carried by both selected chain edges. -/
inductive LengthTwoWalkLabel where
  | edge
deriving DecidableEq, Fintype

/-- VII.R13(a): selected three-vertex chain with one length-two walk. -/
def lengthTwoWalkChain :
    FiniteDirectedGraphTarget LengthTwoWalkVertex LengthTwoWalkEdge
      LengthTwoWalkLabel where
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  source
    | .ab => .a
    | .bc => .b
  target
    | .ab => .b
    | .bc => .c
  relationLabel _ := .edge

/-- VII.R13(a): the concrete selected length-two walk `a -> b -> c`. -/
def lengthTwoWalk :
    FiniteDirectedGraphTarget.CountedDirectedWalk lengthTwoWalkChain
      LengthTwoWalkVertex.a LengthTwoWalkVertex.c 2 :=
  .cons LengthTwoWalkEdge.ab 1 rfl
    (.cons LengthTwoWalkEdge.bc 0 rfl (.nil LengthTwoWalkVertex.c))

/-- VII.R13(a): every selected length-two walk in the chain is the concrete walk. -/
def lengthTwoWalkEquivUnit :
    FiniteDirectedGraphTarget.CountedDirectedWalk lengthTwoWalkChain
      LengthTwoWalkVertex.a LengthTwoWalkVertex.c 2 ≃ Unit where
  toFun _ := ()
  invFun _ := lengthTwoWalk
  left_inv w := by
    apply FiniteDirectedGraphTarget.CountedDirectedWalk.edges_injective
    cases w with
    | cons e n hsource tail =>
        cases e with
        | ab =>
            cases tail with
            | cons e' n' hsource' tail' =>
                cases e' with
                | ab => simp [lengthTwoWalkChain] at hsource'
                | bc =>
                    cases tail'
                    rfl
        | bc => simp [lengthTwoWalkChain] at hsource
  right_inv _ := rfl

/-- VII.R13(a): the selected length-two walk type has cardinality one. -/
theorem lengthTwoWalk_card_eq_one :
    Fintype.card
      (FiniteDirectedGraphTarget.CountedDirectedWalk lengthTwoWalkChain
        LengthTwoWalkVertex.a LengthTwoWalkVertex.c 2) = 1 := by
  rw [Fintype.card_congr lengthTwoWalkEquivUnit]
  rfl

/-- VII.R13(a): proposition 3.6 fires at the nontrivial length `n = 2`. -/
theorem lengthTwoWalk_matrixPower_eq_card :
    (adjacencyMatrixPower lengthTwoWalkChain 2)
        LengthTwoWalkVertex.a LengthTwoWalkVertex.c =
      Fintype.card
        (FiniteDirectedGraphTarget.CountedDirectedWalk lengthTwoWalkChain
          LengthTwoWalkVertex.a LengthTwoWalkVertex.c 2) :=
  adjacencyMatrixPower_apply_eq_countedDirectedWalk_card lengthTwoWalkChain 2
    LengthTwoWalkVertex.a LengthTwoWalkVertex.c

/-- VII.R13(a): the length-two adjacency-power entry is exactly one. -/
theorem lengthTwoWalk_matrixPower_eq_one :
    (adjacencyMatrixPower lengthTwoWalkChain 2)
      LengthTwoWalkVertex.a LengthTwoWalkVertex.c = 1 :=
  lengthTwoWalk_matrixPower_eq_card.trans lengthTwoWalk_card_eq_one

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
    {k : Type} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem site k}
    [CategoryTheory.HasSheafify site.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw}
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
    {k : Type} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem site k}
    [CategoryTheory.HasSheafify site.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw}
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

/-- Indices for the graph and semantic detecting representations. -/
inductive ToyRepIndex where
  | graph
  | semantic
deriving DecidableEq, Fintype

/-- Obstruction classes distinguished by the detecting-family fixture. -/
inductive ToyObstructionClass where
  | zero
  | syncGap
  | semanticGap
deriving DecidableEq, Fintype

/--
The minimal derived repair profile used by the synthesis fixture.

Implementation notes: the profile uses `PUnit` because this example only
supplies the independently constructed Part V package field; no additional
repair claim is encoded in the fixture.
-/
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

/--
A two-valued distance-to-flatness profile with a nonzero safe-state reading.

Implementation notes: `Bool` is used to expose both measured one and measured
zero in the firing theorem, instead of reusing the degenerate all-zero profile.
-/
def nondegenerateDistanceToFlatness :
    DistanceToFlatnessProfile marginOperationDistance where
  Cost := Bool
  costDomain := CostInfimumDomain.completeLatticeInfimumDomain
  costToDistanceValue cost :=
    if cost then DistanceValue.measured 1 else DistanceValue.measured 0
  FlatCandidate _ := Unit
  flatState _ _ := MarginState.boundary
  factorsThroughFlat _ _ := True
  candidateDistance state _ :=
    match state with
    | MarginState.safe => true
    | MarginState.boundary => false
  candidateDistance_reads_d_op := by
    intro state candidate
    cases state <;> rfl
  candidateFactorsThroughFlat _ _ := trivial

/-- The existing margin operation distance equipped with the two-valued flatness reading. -/
abbrev nondegenerateDistanceMassContext : DistanceFlatnessMassContext object where
  operationDistance := marginOperationDistance
  distanceToFlatness := nondegenerateDistanceToFlatness
  obstructionMeasure := marginObstructionMeasure
  obstructionMass := marginObstructionMass

/--
Part I prerequisites reused by the finite synthesis fixture.

Implementation notes: the carrier and core come directly from `FiniteModel`,
so this fixture does not construct a second Part I model.
-/
noncomputable def finiteSynthesisPartI : Site.PartIPrerequisites where
  carrier := AAT.AG.FiniteModel.carrier
  core := AAT.AG.FiniteModel.corePackage

/--
Architecture geometry selecting the standard reference site.

Implementation notes: the merged reference site is reused verbatim so the
synthesis example shares the canonical topology and sheafification provenance.
-/
noncomputable def finiteSynthesisGeometry :
    Site.ArchitectureGeometry finiteSynthesisPartI where
  site := AAT.AG.Examples.StandardGeometryReferenceModels.referenceSite

noncomputable local instance finiteSynthesisHasSheafifyInt :
    HasSheafify finiteSynthesisGeometry.site.topology
      (LawAlgebra.AATCommAlgCat Int) := by
  simpa [finiteSynthesisGeometry] using
    AAT.AG.Examples.StandardGeometryReferenceModels.referenceSite_hasSheafifyInt

/-- The canonical raw ambient system reused by the synthesis fixture. -/
abbrev finiteSynthesisRawAmbient :=
  AAT.AG.Examples.StandardGeometryReferenceModels.referenceRaw

/-- The ringed site derived from `finiteSynthesisRawAmbient`. -/
noncomputable abbrev finiteSynthesisRingedTopos :=
  finiteSynthesisRawAmbient.toRingedSite

/-- The canonical standard architecture scheme reused by the fixture. -/
noncomputable abbrev finiteSynthesisArchitectureScheme :=
  AAT.AG.Examples.StandardGeometryReferenceModels.referenceScheme

/--
Unit-valued decorated-Scheme reading parameter for the detecting toy model.

Implementation notes: all readings are `PUnit` because this auxiliary model
tests Functor and detecting-family composition; compatibility is closed by the
unique proofs rather than by storing morphism data.
-/
def toyReadingParameter : AATSchReadingParameter finiteSynthesisRawAmbient where
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

/--
Constant analytic representation into discrete unit objects.

Implementation notes: this is an auxiliary Functor-law fixture; the target is
discrete `PUnit`, so identities and compositions are discharged by subsingleton
equality.
-/
def toyAnalyticRepresentation :
    AnalyticRepresentation toyReadingParameter (Discrete PUnit) where
  obj _ := Discrete.mk PUnit.unit
  map _ := 𝟙 _
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/--
Two-index family generated by `toyAnalyticRepresentation`.

Implementation notes: both indices share the same auxiliary Functor while the
detecting predicate below distinguishes their logical readings.
-/
def toyRepresentationFamily : RepresentationFamily toyReadingParameter where
  Index := ToyRepIndex
  Target _ := CategoryTheory.Cat.of (Discrete PUnit)
  representation _ := toyAnalyticRepresentation

/--
Detecting family separating synchronization and semantic gaps.

Implementation notes: the truth table gives each nonzero obstruction a named
index at which zero-reading fails, providing the concrete conservativity proof.
-/
def toyDetectingFamily : UDetectingRepresentationFamily toyRepresentationFamily where
  ObstructionClass := ToyObstructionClass
  analyticZeroReading
    | .graph, .zero => True
    | .graph, .syncGap => False
    | .graph, .semanticGap => True
    | .semantic, .zero => True
    | .semantic, .syncGap => True
    | .semantic, .semanticGap => False
  WitnessZero_U alpha :=
    alpha = AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.zero
  detects := by
    intro alpha hzero
    cases alpha with
    | zero => rfl
    | syncGap => exact
        (hzero AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.graph).elim
    | semanticGap => exact
        (hzero AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.semantic).elim
  completenessLevel :=
    AAT.AG.RepresentationAnalysis.CompletenessSpectrum.conservative

/--
Single selected signature axis used by the finite analytic contexts.

Implementation notes: the axis is intentionally neutral here because the
example exercises representation detection independently of signature failure.
-/
def toySignatureAxes : SignatureAxes AAT.AG.FiniteModel.carrier where
  Axis := PUnit
  selected _ := True
  zero _ _ := True

/--
Finite analytic reading context assembled from the auxiliary detecting family.

Implementation notes: existing finite-model law, distance, and mass data are
reused; only the representation and detection components are supplied locally.
-/
def toyAnalyticReadingContext :
    AnalyticReadingContext AAT.AG.FiniteModel.object toyReadingParameter where
  AtomVocabulary := PUnit
  atomVocabularyOf _ := PUnit.unit
  lawUniverse := AAT.AG.FiniteModel.lawUniverse
  CoverageTopology := PUnit
  selectedCoverage := PUnit.unit
  coefficientSheaf := PUnit
  representationFamily := toyRepresentationFamily
  distanceMassContext :=
    AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginDistanceMassContext
  selectedWitnessFamily := PUnit
  selectedWitness := PUnit.unit
  selectedSignatureAxes := toySignatureAxes
  signatureProfile :=
    AAT.AG.RepresentationAnalysis.SignatureReadingProfile.ofSignatureAxes toySignatureAxes
  detectingFamily := toyDetectingFamily
  coverageAdequacy := True
  witnessExactness := True
  axisExactness := True
  coefficientDiscipline := True
  completenessLevel :=
    AAT.AG.RepresentationAnalysis.CompletenessSpectrum.conservative

/--
Conservativity certificate for `toyAnalyticReadingContext`.

Implementation notes: zero is the named `ToyObstructionClass.zero`, and the
detecting-family truth table supplies the witness-zero implication.
-/
def toyConservativity :
    RepresentationConservativityUnderAdequacy toyAnalyticReadingContext where
  zeroClass :=
    AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.zero
  IsZeroClass alpha :=
    alpha = AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.zero
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
      toyDetectingFamily.analyticZeroReading i
        AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.syncGap) := by
  intro h
  exact h AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.graph

theorem detectingRepresentation_toy_semanticGap_not_all_zero :
    ¬ (∀ i : toyRepresentationFamily.Index,
      toyDetectingFamily.analyticZeroReading i
        AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.semanticGap) := by
  intro h
  exact h AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.semantic

theorem detectingRepresentation_toy_all_zero_imp_zero
    (alpha : toyDetectingFamily.ObstructionClass)
    (hzero : ∀ i : toyRepresentationFamily.Index,
      toyDetectingFamily.analyticZeroReading i alpha) :
    alpha = toyConservativity.zeroClass :=
  toyConservativity.witnessZero_eq_zero alpha (toyDetectingFamily.detects alpha hzero)

theorem detectingRepresentation_toy_zero_conservative :
    AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.zero =
      toyConservativity.zeroClass :=
  rfl

theorem detectingRepresentation_toy_all_zero_actual_zero
    (alpha : toyDetectingFamily.ObstructionClass)
    (hzero : ∀ i : toyRepresentationFamily.Index,
      toyDetectingFamily.analyticZeroReading i alpha) :
    alpha = AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.zero :=
  toyDetectingFamily.detects alpha hzero

theorem detectingRepresentation_toy_zero_is_actual_zero :
    AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.zero =
      AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.zero :=
  rfl

/--
Reading parameter used by the normalized finite synthesis package.

Implementation notes: it reuses the already validated unit-valued parameter so
the package adds no second compatibility contract.
-/
def finiteSynthesisReadingParameter :
    AATSchReadingParameter finiteSynthesisRawAmbient := toyReadingParameter

/--
Analytic Functor used by the normalized finite synthesis package.

Implementation notes: the Functor is kept as a separately named fixture so the
package's representation family points directly to a canonical Functor value.
-/
def finiteSynthesisAnalyticRepresentation :
    AnalyticRepresentation finiteSynthesisReadingParameter (Discrete PUnit) where
  obj _ := Discrete.mk PUnit.unit
  map _ := 𝟙 _
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/--
Representation family attached to the finite synthesis context.

Implementation notes: both selected indices use the same unit-valued Functor;
their detecting behavior is carried by `finiteSynthesisDetectingFamily`.
-/
def finiteSynthesisRepresentationFamily :
    RepresentationFamily finiteSynthesisReadingParameter where
  Index := ToyRepIndex
  Target _ := CategoryTheory.Cat.of (Discrete PUnit)
  representation _ := finiteSynthesisAnalyticRepresentation

/--
Detecting family attached to `finiteSynthesisRepresentationFamily`.

Implementation notes: the explicit truth table retains the graph/semantic
separation used by the Part VII example after synthesis normalization.
-/
def finiteSynthesisDetectingFamily :
    UDetectingRepresentationFamily finiteSynthesisRepresentationFamily where
  ObstructionClass := ToyObstructionClass
  analyticZeroReading
    | .graph, .zero => True
    | .graph, .syncGap => False
    | .graph, .semanticGap => True
    | .semantic, .zero => True
    | .semantic, .syncGap => True
    | .semantic, .semanticGap => False
  WitnessZero_U alpha :=
    alpha = AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyObstructionClass.zero
  detects := by
    intro alpha hzero
    cases alpha with
    | zero => rfl
    | syncGap => exact
        (hzero AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.graph).elim
    | semanticGap => exact
        (hzero AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.semantic).elim
  completenessLevel :=
    AAT.AG.RepresentationAnalysis.CompletenessSpectrum.conservative

/--
Analytic reading context stored by the normalized synthesis fixture.

Implementation notes: all predecessor components are existing finite-model
values; this definition only assembles them into the canonical context shape.
-/
def finiteSynthesisAnalyticReadingContext :
    AnalyticReadingContext AAT.AG.FiniteModel.object
      finiteSynthesisReadingParameter where
  AtomVocabulary := PUnit
  atomVocabularyOf _ := PUnit.unit
  lawUniverse := AAT.AG.FiniteModel.lawUniverse
  CoverageTopology := PUnit
  selectedCoverage := PUnit.unit
  coefficientSheaf := PUnit
  representationFamily := finiteSynthesisRepresentationFamily
  distanceMassContext :=
    AAT.AG.FiniteModel.RepresentationAnalysisPart7.marginDistanceMassContext
  selectedWitnessFamily := PUnit
  selectedWitness := PUnit.unit
  selectedSignatureAxes := toySignatureAxes
  signatureProfile :=
    AAT.AG.RepresentationAnalysis.SignatureReadingProfile.ofSignatureAxes toySignatureAxes
  detectingFamily := finiteSynthesisDetectingFamily
  coverageAdequacy := True
  witnessExactness := True
  axisExactness := True
  coefficientDiscipline := True
  completenessLevel :=
    AAT.AG.RepresentationAnalysis.CompletenessSpectrum.conservative

/--
Reading parameter whose obstruction decoration is an actual ideal of `Int`.

Implementation notes: equality on ideals is the compatibility law, allowing
the representation output to retain the selected synthesis ideal through
identities and composition.
-/
def nondegenerateSynthesisReadingParameter :
    AATSchReadingParameter finiteSynthesisRawAmbient where
  AtomLabelReading := PUnit
  LawReading := PUnit
  ObstructionIdealReading := Ideal Int
  SignatureReading := PUnit
  InterpretationMapReading := PUnit
  atomLabelsCompatible _ _ _ := True
  lawReadingCompatible _ _ _ := True
  obstructionIdealCompatible _ I J := I = J
  signatureReadingCompatible _ _ _ := True
  interpretationMapCompatible _ _ _ := True
  id_atomLabelsCompatible _ _ := trivial
  id_lawReadingCompatible _ _ := trivial
  id_obstructionIdealCompatible _ _ := rfl
  id_signatureReadingCompatible _ _ := trivial
  id_interpretationMapCompatible _ _ := trivial
  comp_atomLabelsCompatible _ _ := trivial
  comp_lawReadingCompatible _ _ := trivial
  comp_obstructionIdealCompatible hIJ hJK := hIJ.trans hJK
  comp_signatureReadingCompatible _ _ := trivial
  comp_interpretationMapCompatible _ _ := trivial

private def idealAnalyticMap
    {X Y : AATSch nondegenerateSynthesisReadingParameter}
    (f : X ⟶ Y) :
    Discrete.mk X.obstructionIdealReading ⟶
      Discrete.mk Y.obstructionIdealReading :=
  Discrete.eqToHom f.obstructionIdealCompatible

/--
Analytic representation reading the selected `Int` ideal.

Implementation notes: the discrete target turns the compatibility proof into
the unique morphism witnessing equality of the source and target ideal readings.
-/
def idealAnalyticRepresentation :
    AnalyticRepresentation nondegenerateSynthesisReadingParameter
      (Discrete (Ideal Int)) where
  obj X := Discrete.mk X.obstructionIdealReading
  map := idealAnalyticMap
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/--
Representation family generated by `idealAnalyticRepresentation`.

Implementation notes: the two indices share one ideal-valued Functor so the
subsequent detector can test the same selected ideal from either lane.
-/
def idealSynthesisRepresentationFamily :
    RepresentationFamily nondegenerateSynthesisReadingParameter where
  Index := ToyRepIndex
  Target _ := CategoryTheory.Cat.of (Discrete (Ideal Int))
  representation _ := idealAnalyticRepresentation

/--
Detecting family whose zero reading is equality with the bottom ideal.

Implementation notes: detection is witnessed at the graph index, making a
nonzero selected ideal an explicit negative zero-reading example.
-/
def idealSynthesisDetectingFamily :
    UDetectingRepresentationFamily idealSynthesisRepresentationFamily where
  ObstructionClass := Ideal Int
  analyticZeroReading _ I := I = ⊥
  WitnessZero_U I := I = ⊥
  detects := by
    intro _I hzero
    exact hzero AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.graph
  completenessLevel :=
    AAT.AG.RepresentationAnalysis.CompletenessSpectrum.conservative

/--
Canonical decorated scheme carrying a selected obstruction ideal.

Implementation notes: only the ideal decoration varies; the underlying scheme
is the merged standard reference scheme and all other readings are neutral.
-/
noncomputable def nondegenerateDecoratedScheme (I : Ideal Int) :
    AATSch nondegenerateSynthesisReadingParameter where
  scheme := finiteSynthesisArchitectureScheme
  atomLabels := PUnit.unit
  lawReading := PUnit.unit
  obstructionIdealReading := I
  signatureReading := PUnit.unit
  interpretationMapReading := PUnit.unit

/--
Analytic context whose selected witness and representation value are the same ideal.

Implementation notes: the context combines the ideal-valued detecting family
with the nondegenerate distance profile, yielding independent ideal and metric
firing evidence without duplicating canonical geometry.
-/
def nondegenerateSynthesisAnalyticReadingContext (I : Ideal Int) :
    AnalyticReadingContext AAT.AG.FiniteModel.object
      nondegenerateSynthesisReadingParameter where
  AtomVocabulary := AAT.AG.FiniteModel.FiniteAtom
  atomVocabularyOf := id
  lawUniverse := AAT.AG.FiniteModel.lawUniverse
  CoverageTopology := Bool
  selectedCoverage := true
  coefficientSheaf := Bool
  representationFamily := idealSynthesisRepresentationFamily
  distanceMassContext :=
    AAT.AG.FiniteModel.RepresentationAnalysisPart7.nondegenerateDistanceMassContext
  selectedWitnessFamily := Ideal Int
  selectedWitness := I
  selectedSignatureAxes := toySignatureAxes
  signatureProfile :=
    AAT.AG.RepresentationAnalysis.SignatureReadingProfile.ofSignatureAxes toySignatureAxes
  detectingFamily := idealSynthesisDetectingFamily
  coverageAdequacy := True
  witnessExactness := True
  axisExactness := True
  coefficientDiscipline := True
  completenessLevel :=
    AAT.AG.RepresentationAnalysis.CompletenessSpectrum.conservative

/--
Constant terminal `PUnit` sheaf for the finite synthesis example.

Implementation notes: terminality supplies the sheaf condition directly; this
keeps the fixture finite while using the actual `AATSh` API.
-/
noncomputable def finiteSynthesisTypeSheaf :
    Site.AATSh finiteSynthesisGeometry.site where
  val := (CategoryTheory.Functor.const finiteSynthesisGeometry.site.categoryᵒᵖ).obj PUnit
  cond := CategoryTheory.Presheaf.isSheaf_of_isTerminal
    finiteSynthesisGeometry.site.topology
    (IsTerminal.ofUniqueHom
      (fun _ => fun _ => PUnit.unit)
      (by
        intro _X f
        funext q
        cases f q
        rfl))

/--
Singleton cover of the standard reference base context.

Implementation notes: every simplex and overlap is the canonical base context,
which is sufficient for assembling the concrete Čech predecessor field.
-/
def finiteSynthesisCover :
    Cohomology.CoverRelativeCechCover finiteSynthesisGeometry.site where
  base := AAT.AG.Examples.StandardGeometryReferenceModels.baseContext
  Index := PUnit
  chart _ := AAT.AG.Examples.StandardGeometryReferenceModels.baseContext
  inclusion _ := 𝟙 _
  simplex _ := PUnit
  overlap _ _ := AAT.AG.Examples.StandardGeometryReferenceModels.baseContext
  face _ _ _ := PUnit.unit
  faceRestriction _ _ _ := 𝟙 _

/--
Additive obstruction sheaf built from `finiteSynthesisTypeSheaf`.

Implementation notes: the carrier is the actual AAT sheaf conversion, while
the `PUnit` fibers provide the unique additive structure and restriction laws.
-/
def finiteSynthesisObstructionSheaf :
    Cohomology.ObstructionSheaf finiteSynthesisGeometry.site where
  carrier := Site.AATSh.toAATSheaf finiteSynthesisTypeSheaf
  addCommGroup := by
    intro _W
    change AddCommGroup PUnit
    infer_instance
  map_zero := by intro _ _ _; rfl
  map_add := by intro _ _ _ a b; cases a; cases b; rfl

/--
Cover-relative Čech complex for the singleton synthesis cover.

Implementation notes: cochains are `PUnit`-valued and the unique additive map
defines the differential, producing a concrete canonical complex without an
extra wrapper package.
-/
def finiteSynthesisCechComplex :
    Cohomology.CoverRelativeCechComplex finiteSynthesisCover
      finiteSynthesisObstructionSheaf where
  cochainAddCommGroup := by
    intro _n
    change AddCommGroup (PUnit → PUnit)
    infer_instance
  alternatingFaceCombination := fun _ _ _ => PUnit.unit
  differential := by
    intro _n
    change (PUnit → PUnit) →+ (PUnit → PUnit)
    exact {
      toFun := fun _ _ => PUnit.unit
      map_zero' := by funext _; rfl
      map_add' := by intro a b; funext i; cases a i; cases b i; rfl }
  differential_eq_alternatingFaceCombination := by
    intro _ c
    funext i
    cases c i
    rfl
  differential_comp := by
    intro _ c
    funext i
    cases c i
    rfl

/--
Stratum reading parameter for the finite synthesis fixture.

Implementation notes: it reuses `toySignatureAxes` and a unit coefficient,
matching the finite example's selected analytic data.
-/
def finiteSynthesisStratumParameter :
    AAT.AG.SingularityMonodromyStack.StratumReadingParameter
      finiteSynthesisGeometry.site where
  signatureAxes := toySignatureAxes
  Coeff := PUnit
  selectedCoeff := PUnit.unit

/--
Architecture stratum supplied to the normalized synthesis package.

Implementation notes: the raw system and geometry are the canonical reference
values; `PUnit` supplies a concrete inhabited selected stratum for package
assembly rather than a second geometric construction.
-/
noncomputable def finiteSynthesisArchitectureStratum :
    AAT.AG.SingularityMonodromyStack.ArchitectureStratum
      finiteSynthesisStratumParameter Int where
  raw := finiteSynthesisRawAmbient
  geometry := finiteSynthesisArchitectureScheme
  Point := PUnit
  carrier := Set.univ
  role := AAT.AG.SingularityMonodromyStack.StratumRole.component
  label := "r0-final-shadow"
  selectedSubobject := True
  selectedSubobject_cert := trivial
  locallyClosed := True
  locallyClosed_cert := trivial
  decorationCompatible := True
  decorationCompatible_cert := trivial
  readingCompatible := True
  readingCompatible_cert := trivial

/--
Normalized synthesis package assembled from the finite predecessor fixtures.

Implementation notes: each field is an independently named canonical or finite
fixture, and derived site, atlas, ideal, and lawful geometry remain projections
of `AATSynthesisPackage` rather than duplicated fields.
-/
noncomputable def finiteSynthesisAATSynthesisPackage :
    AATSynthesisPackage finiteSynthesisPartI Int finiteSynthesisGeometry
      finiteSynthesisRawAmbient where
  architectureScheme := finiteSynthesisArchitectureScheme
  lawReading :=
    AAT.AG.Examples.StandardGeometryReferenceModels.referenceLegacySiteReading
  lawReadingValid :=
    AAT.AG.Examples.StandardGeometryReferenceModels.referenceLegacySiteReading_valid
  requiredClosed :=
    AAT.AG.Examples.StandardGeometryReferenceModels.referenceLegacySiteReading_requiredClosed
  requiredLawIdealExact :=
    AAT.AG.Examples.StandardGeometryReferenceModels.referenceLegacySiteReading_requiredLawIdealExact
  cover := finiteSynthesisCover
  obstructionSheaf := finiteSynthesisObstructionSheaf
  obstructionCohomology := finiteSynthesisCechComplex
  derivedLawGeometry :=
    AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisRepairProfile
  stratumParameter := finiteSynthesisStratumParameter
  singularityMonodromyStack := finiteSynthesisArchitectureStratum
  readingParameter := finiteSynthesisReadingParameter
  representationPeriodMetricAnalysis := finiteSynthesisAnalyticReadingContext

/--
Synthesis package with nonzero ideal and nonzero safe-state distance evidence.

Implementation notes: it differs from the neutral package only in the
ideal-valued reading parameter and analytic context; all geometry, cohomology,
derived, and stratum provenance remains shared.
-/
noncomputable def nondegenerateSynthesisPackage :
    AATSynthesisPackage finiteSynthesisPartI Int finiteSynthesisGeometry
      finiteSynthesisRawAmbient where
  architectureScheme := finiteSynthesisArchitectureScheme
  lawReading :=
    AAT.AG.Examples.StandardGeometryReferenceModels.referenceLegacySiteReading
  lawReadingValid :=
    AAT.AG.Examples.StandardGeometryReferenceModels.referenceLegacySiteReading_valid
  requiredClosed :=
    AAT.AG.Examples.StandardGeometryReferenceModels.referenceLegacySiteReading_requiredClosed
  requiredLawIdealExact :=
    AAT.AG.Examples.StandardGeometryReferenceModels.referenceLegacySiteReading_requiredLawIdealExact
  cover := finiteSynthesisCover
  obstructionSheaf := finiteSynthesisObstructionSheaf
  obstructionCohomology := finiteSynthesisCechComplex
  derivedLawGeometry :=
    AAT.AG.FiniteModel.RepresentationAnalysisPart7.finiteSynthesisRepairProfile
  stratumParameter := finiteSynthesisStratumParameter
  singularityMonodromyStack := finiteSynthesisArchitectureStratum
  readingParameter := nondegenerateSynthesisReadingParameter
  representationPeriodMetricAnalysis :=
    nondegenerateSynthesisAnalyticReadingContext
      (Ideal.span ({(2 : Int)} : Set Int))

theorem nondegenerateObstructionIdeal_two_mem :
    (2 : Int) ∈
      (show Ideal Int from
        nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness) := by
  change (2 : Int) ∈ Ideal.span ({(2 : Int)} : Set Int)
  exact Ideal.subset_span (by simp)

theorem nondegenerateObstructionIdeal_ne_bot :
    (show Ideal Int from
      nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness) ≠
      (⊥ : Ideal Int) := by
  change Ideal.span ({(2 : Int)} : Set Int) ≠ (⊥ : Ideal Int)
  intro hbot
  have hmem : (2 : Int) ∈ (⊥ : Ideal Int) := by
    rw [← hbot]
    exact Ideal.subset_span (by simp)
  simp at hmem

/-- The safe selected state has actual distance-to-flatness value one. -/
theorem nondegenerateDistance_safe_eq_one :
    nondegenerateDistanceToFlatness.dist_flat_value MarginState.safe =
      DistanceValue.measured 1 := by
  change (if (⨅ _ : Unit, true) then DistanceValue.measured 1
    else DistanceValue.measured 0) = DistanceValue.measured 1
  rw [iInf_const]
  rfl

/-- The selected flat state has actual distance-to-flatness value zero. -/
theorem nondegenerateDistance_boundary_eq_zero :
    nondegenerateDistanceToFlatness.dist_flat_value MarginState.boundary =
      DistanceValue.measured 0 := by
  change (if (⨅ _ : Unit, false) then DistanceValue.measured 1
    else DistanceValue.measured 0) = DistanceValue.measured 0
  rw [iInf_const]
  rfl

/-- The safe state's actual distance-to-flatness value is not measured zero. -/
theorem nondegenerateDistance_safe_ne_zero :
    nondegenerateDistanceToFlatness.dist_flat_value MarginState.safe ≠
      DistanceValue.measured 0 := by
  rw [nondegenerateDistance_safe_eq_one]
  simp

theorem nondegenerateSelectedObstruction_eq_ideal :
    (show Ideal Int from
      nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness) =
      Ideal.span ({(2 : Int)} : Set Int) :=
  rfl

theorem nondegenerateRepresentation_reads_selectedIdeal :
    (((nondegenerateSynthesisPackage.analyticReadingContext.representationFamily).representation
        AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.graph).obj
        (nondegenerateDecoratedScheme
          (show Ideal Int from
            nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness))).as =
      (show Ideal Int from
        nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness) :=
  rfl

theorem nondegenerateSynthesis_evidence :
    finiteSynthesisPartI.architectureObject = object ∧
      (show Ideal Int from
        nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness) ≠
          (⊥ : Ideal Int) ∧
      (show Ideal Int from
        nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness) =
        Ideal.span ({(2 : Int)} : Set Int) ∧
      (((nondegenerateSynthesisPackage.analyticReadingContext.representationFamily).representation
          AAT.AG.FiniteModel.RepresentationAnalysisPart7.ToyRepIndex.graph).obj
          (nondegenerateDecoratedScheme
            (show Ideal Int from
              nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness))).as =
        (show Ideal Int from
          nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness) ∧
      (¬ (nondegenerateSynthesisPackage.analyticReadingContext.detectingFamily).analyticZeroReading
        ToyRepIndex.graph
          nondegenerateSynthesisPackage.analyticReadingContext.selectedWitness) ∧
      (nondegenerateSynthesisPackage.analyticReadingContext.distanceMassContext).distanceToFlatness.dist_flat_value
          MarginState.safe =
        DistanceValue.measured 1 ∧
      (nondegenerateSynthesisPackage.analyticReadingContext.distanceMassContext).distanceToFlatness.dist_flat_value
          MarginState.boundary =
        DistanceValue.measured 0 ∧
      (nondegenerateSynthesisPackage.analyticReadingContext.distanceMassContext).distanceToFlatness.dist_flat_value
          MarginState.safe ≠
        DistanceValue.measured 0 := by
  constructor
  · rfl
  constructor
  · change Ideal.span ({(2 : Int)} : Set Int) ≠ (⊥ : Ideal Int)
    intro hbot
    have hmem : (2 : Int) ∈ (⊥ : Ideal Int) := by
      rw [← hbot]
      exact Ideal.subset_span (by simp)
    simp at hmem
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · change ¬ ((Ideal.span ({(2 : Int)} : Set Int)) = ⊥)
    intro hbot
    have hmem : (2 : Int) ∈ (⊥ : Ideal Int) := by
      rw [← hbot]
      exact Ideal.subset_span (by simp)
    simp at hmem
  constructor
  · change (if (⨅ _ : Unit, true) then DistanceValue.measured 1
      else DistanceValue.measured 0) = DistanceValue.measured 1
    rw [iInf_const]
    rfl
  constructor
  · change (if (⨅ _ : Unit, false) then DistanceValue.measured 1
      else DistanceValue.measured 0) = DistanceValue.measured 0
    rw [iInf_const]
    rfl
  · change (if (⨅ _ : Unit, true) then DistanceValue.measured 1
      else DistanceValue.measured 0) ≠ DistanceValue.measured 0
    rw [iInf_const]
    simp

end RepresentationAnalysisPart7
end FiniteModel
end AAT.AG
