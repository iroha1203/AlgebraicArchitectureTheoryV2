import ResearchLean.AG.TwoPhase.ForestSupport
import Formal.Util.AssertStandardAxioms

/-!
# Finite witnesses for the two-phase obstruction theorem

This module discharges stage E4 of `G-102-aat-two-phase-obstruction`.
It constructs two concrete coefficient complexes from the finite-model doctrine
and its reviewed, non-singleton semantic family.

The first is a two-chart interval whose actual incidence differential carries a
structural chart coordinate to a nonzero semantic edge coordinate, so Condition
E fails.  The second has separate structural and semantic pairs of parallel
edges.  It satisfies Condition E while its structural parallel-edge cycle has a
nonzero standard `H^1` class; its semantic parallel-edge cycle gives an
all-phase class whose image under the canonical semantic quotient map is
nonzero.  The structural support is visibly nonzero and proper.

A separate three-chart structural path fixes a nonvacuous positive instance of
the forest-pruning `Fresh` relation, while a deliberately wrong middle-leaf
ordering supplies its endpoint-collision negative instance.

No phase label, nonzero-class certificate, vanishing result, or injectivity
claim is a field of these examples.  Every differential is the actual endpoint
incidence map of a `FiniteNerveCochainComplex`, and every phase fact is generated
from the E0 dependency profile.
-/

noncomputable section

namespace AAT.AG.TwoPhase

open Cohomology

universe r v

namespace FiniteWitnesses

/-- The finite doctrine already fixed by the E0 dependency-profile witness. -/
abbrev doctrine : ExtractionDoctrine FiniteModel.carrier :=
  FiniteDependencyProfile.doctrine

/-- The reviewed two-element semantic family already fixed at E0. -/
abbrev family : DeclaredSemanticFamily doctrine :=
  FiniteDependencyProfile.family

/-- The concrete structural source--Atom pair used by every E4 example. -/
def structuralPair : ExtractionPair doctrine :=
  (FiniteModel.ExtractionSource.withoutComponentC,
    FiniteModel.FiniteAtom.componentA)

/-- The concrete semantic source--Atom pair used by every E4 example. -/
def semanticPair : ExtractionPair doctrine :=
  (FiniteModel.ExtractionSource.withoutComponentC,
    FiniteModel.FiniteAtom.componentC)

/-- The selected structural pair is derived from extraction invariance. -/
theorem structuralPair_structural : family.Structural structuralPair := by
  simpa [structuralPair] using
    FiniteDependencyProfile.componentA_structural

/-- The selected semantic pair is derived from an actual extraction change. -/
theorem semanticPair_semantic : family.Semantic semanticPair := by
  simpa [semanticPair] using
    FiniteDependencyProfile.componentC_semantic

/-- The selected semantic pair is not structural. -/
theorem semanticPair_not_structural : ¬ family.Structural semanticPair :=
  semanticPair_semantic

/-- The endpoint-incidence linear map on a finite cover nerve. -/
def edgeIncidence (N : CoverNerve.{r}) (k : Type v) [Field k] :
    (N.Chart → k) →ₗ[k] (N.EdgeComponent → k) where
  toFun c edge := c (N.edgeRight edge) - c (N.edgeLeft edge)
  map_add' left right := by
    funext edge
    simp
    abel
  map_smul' scalar c := by
    funext edge
    simp [mul_sub]

/--
The canonical coordinate complex of a finite face-free nerve.

The degree-zero differential is generated from the actual endpoint maps.  The
degree-one differential is zero only because the nerve has no face component.
-/
def noFaceIncidenceComplex
    (N : CoverNerve.{r}) (k : Type v) [Field k]
    [Fintype N.Chart] [Fintype N.EdgeComponent]
    [Fintype N.FaceComponent] [IsEmpty N.FaceComponent] :
    FiniteNerveCochainComplex.{r, v, max r v} N k where
  C0 := N.Chart → k
  C1 := N.EdgeComponent → k
  C2 := N.FaceComponent → k
  d0 := edgeIncidence N k
  d1 := 0
  d1_comp_d0 := by intro; rfl
  zeroCochainCoordinates := LinearEquiv.refl k (N.Chart → k)
  oneCochainCoordinates := LinearEquiv.refl k (N.EdgeComponent → k)
  twoCochainCoordinates := LinearEquiv.refl k (N.FaceComponent → k)
  d0_eq_edgeIncidence := by intros; rfl
  d1_eq_faceIncidence := by
    intro _ face
    exact isEmptyElim face

/-! ## A finite interval where Condition E fails -/

/-- The two actual charts of the Condition-E failure interval. -/
inductive FailureChart where
  | structural
  | semantic
  deriving DecidableEq, Fintype

/-- The actual cross-phase edge of the Condition-E failure interval. -/
inductive FailureEdge where
  | bridge
  deriving DecidableEq, Fintype

/-- A two-chart, one-edge, no-face cover nerve. -/
def conditionEFailureNerve : CoverNerve where
  Chart := FailureChart
  EdgeComponent := FailureEdge
  FaceComponent := Empty
  edgeLeft := fun _ => .structural
  edgeRight := fun _ => .semantic
  faceEdge0 := fun face => isEmptyElim face
  faceEdge1 := fun face => isEmptyElim face
  faceEdge2 := fun face => isEmptyElim face
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := by simp
  faceTripleOverlapComponent_holds := fun face => isEmptyElim face

/-- Finite witness infrastructure inherited from the explicit two-chart failure nerve. -/
instance failureChartFintype : Fintype conditionEFailureNerve.Chart := by
  change Fintype FailureChart
  infer_instance

/-- Finite witness infrastructure inherited from the explicit one-edge failure nerve. -/
instance failureEdgeFintype : Fintype conditionEFailureNerve.EdgeComponent := by
  change Fintype FailureEdge
  infer_instance

/-- Finite witness infrastructure for the failure nerve's empty face type. -/
instance failureFaceFintype : Fintype conditionEFailureNerve.FaceComponent := by
  change Fintype Empty
  infer_instance

/-- The no-face premise supplied by the explicit failure nerve. -/
instance failureFaceIsEmpty : IsEmpty conditionEFailureNerve.FaceComponent := by
  change IsEmpty Empty
  infer_instance

/-- Atom provenance and restriction indices for the failure interval. -/
def conditionEFailureIndexing :
    AtomIndexedNerveData doctrine conditionEFailureNerve where
  ChartBasis := fun _ => PUnit
  EdgeBasis := fun _ => PUnit
  FaceBasis := fun _ => PUnit
  chartBasisFintype := fun _ => inferInstance
  edgeBasisFintype := fun _ => inferInstance
  faceBasisFintype := fun face => isEmptyElim face
  chartPair := fun chart _ =>
    match chart with
    | .structural => structuralPair
    | .semantic => semanticPair
  edgePair := fun _ _ => semanticPair
  facePair := fun face => isEmptyElim face
  edgeLeftIndex := fun _ _ => PUnit.unit
  edgeRightIndex := fun _ _ => PUnit.unit
  faceEdge0Index := fun face => isEmptyElim face
  faceEdge1Index := fun face => isEmptyElim face
  faceEdge2Index := fun face => isEmptyElim face

/-- The actual expanded structural chart coordinate of the failure interval. -/
def failureStructuralChart : conditionEFailureIndexing.expandedNerve.Chart :=
  ⟨FailureChart.structural, PUnit.unit⟩

/-- The actual expanded semantic chart coordinate of the failure interval. -/
def failureSemanticChart : conditionEFailureIndexing.expandedNerve.Chart :=
  ⟨FailureChart.semantic, PUnit.unit⟩

/-- The actual expanded cross-phase edge coordinate of the failure interval. -/
def failureBridgeEdge : conditionEFailureIndexing.expandedNerve.EdgeComponent :=
  ⟨FailureEdge.bridge, PUnit.unit⟩

/-- The concrete reviewed incidence complex on the expanded failure interval. -/
def conditionEFailureAll :
    FiniteNerveCochainComplex conditionEFailureIndexing.expandedNerve (ZMod 2) := by
  let I := conditionEFailureIndexing
  letI : Fintype I.expandedNerve.Chart := I.chartFintype
  letI : Fintype I.expandedNerve.EdgeComponent := I.edgeFintype
  letI : Fintype I.expandedNerve.FaceComponent := I.faceFintype
  letI : IsEmpty I.expandedNerve.FaceComponent :=
    ⟨fun face => isEmptyElim face.1⟩
  exact noFaceIncidenceComplex I.expandedNerve (ZMod 2)

/-- The full Atom-indexed Condition-E failure coefficient complex. -/
def conditionEFailureComplex :
    AtomIndexedCoefficientComplex doctrine family conditionEFailureNerve (ZMod 2) where
  indexing := conditionEFailureIndexing
  all := conditionEFailureAll

/-- The interval's left chart is actually structural. -/
theorem failureLeftPair_structural :
    family.Structural
      (conditionEFailureIndexing.chartPairAt failureStructuralChart) := by
  simpa [conditionEFailureIndexing, failureStructuralChart] using
    structuralPair_structural

/-- The interval's right chart is actually semantic. -/
theorem failureRightPair_semantic :
    family.Semantic
      (conditionEFailureIndexing.chartPairAt failureSemanticChart) := by
  simpa [conditionEFailureIndexing, failureSemanticChart] using
    semanticPair_semantic

/-- The interval's cross-phase edge is actually semantic. -/
theorem failureEdgePair_semantic :
    family.Semantic
      (conditionEFailureIndexing.edgePairAt failureBridgeEdge) := by
  simpa [conditionEFailureIndexing, failureBridgeEdge] using
    semanticPair_semantic

/-- The coordinate vector supported on the actual structural chart. -/
def failureStructuralInput : conditionEFailureComplex.all.C0 :=
  conditionEFailureComplex.all.zeroCochainCoordinates.symm
    (coordinateVector failureStructuralChart)

/-- The selected chart vector belongs to the derived structural support. -/
theorem failureStructuralInput_mem :
    failureStructuralInput ∈ conditionEFailureComplex.structural0 := by
  classical
  rw [conditionEFailureComplex.mem_structural0_iff]
  intro chart hchart
  rcases chart with ⟨chart, basis⟩
  rcases basis with ⟨⟩
  cases chart with
  | structural =>
      exact (hchart (by simpa [conditionEFailureIndexing] using
        failureLeftPair_structural)).elim
  | semantic =>
      change coordinateVector failureStructuralChart failureSemanticChart = 0
      have hne : failureStructuralChart ≠ failureSemanticChart := by
        intro h
        exact FailureChart.noConfusion (congrArg Sigma.fst h)
      simp [coordinateVector, hne]

/-- The actual incidence image has nonzero semantic-edge coordinate. -/
theorem failure_d0_semantic_coordinate :
    conditionEFailureComplex.all.oneCochainCoordinates
        (conditionEFailureComplex.all.d0 failureStructuralInput)
        failureBridgeEdge = 1 := by
  rw [conditionEFailureComplex.d0_coordinate]
  change coordinateVector failureStructuralChart failureSemanticChart -
      coordinateVector failureStructuralChart failureStructuralChart = 1
  have hne : failureStructuralChart ≠ failureSemanticChart := by
    intro h
    exact FailureChart.noConfusion (congrArg Sigma.fst h)
  simp [coordinateVector, hne]

/-- The actual incidence image does not lie in structural degree one. -/
theorem failure_d0_not_mem_structural1 :
    conditionEFailureComplex.all.d0 failureStructuralInput ∉
      conditionEFailureComplex.structural1 := by
  intro hmem
  have hzero :=
    (conditionEFailureComplex.mem_structural1_iff
      (conditionEFailureComplex.all.d0 failureStructuralInput)).1 hmem
      failureBridgeEdge failureEdgePair_semantic
  rw [failure_d0_semantic_coordinate] at hzero
  exact one_ne_zero hzero

/-- Condition E genuinely fails for the finite cross-phase interval. -/
theorem conditionEFailure_not_conditionE :
    ¬ conditionEFailureComplex.ConditionE := by
  intro hE
  exact failure_d0_not_mem_structural1 (hE.1 failureStructuralInput_mem)

/-! ## One proper two-phase parallel-cycle complex -/

/-- Four actual charts, two for each derived phase. -/
inductive TwoPhaseCycleChart where
  | structuralLeft
  | structuralRight
  | semanticLeft
  | semanticRight
  deriving DecidableEq, Fintype

/-- Two parallel structural edges and two parallel semantic edges. -/
inductive TwoPhaseCycleEdge where
  | structuralTop
  | structuralBottom
  | semanticTop
  | semanticBottom
  deriving DecidableEq, Fintype

/-- The phase-separated pair of genuine parallel-edge cycles. -/
def twoPhaseCycleNerve : CoverNerve where
  Chart := TwoPhaseCycleChart
  EdgeComponent := TwoPhaseCycleEdge
  FaceComponent := Empty
  edgeLeft
    | .structuralTop | .structuralBottom => .structuralLeft
    | .semanticTop | .semanticBottom => .semanticLeft
  edgeRight
    | .structuralTop | .structuralBottom => .structuralRight
    | .semanticTop | .semanticBottom => .semanticRight
  faceEdge0 := fun face => isEmptyElim face
  faceEdge1 := fun face => isEmptyElim face
  faceEdge2 := fun face => isEmptyElim face
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := by simp
  faceTripleOverlapComponent_holds := fun face => isEmptyElim face

/-- Finite witness infrastructure inherited from the four-chart cycle nerve. -/
instance twoPhaseCycleChartFintype : Fintype twoPhaseCycleNerve.Chart := by
  change Fintype TwoPhaseCycleChart
  infer_instance

/-- Finite witness infrastructure inherited from the four-edge cycle nerve. -/
instance twoPhaseCycleEdgeFintype : Fintype twoPhaseCycleNerve.EdgeComponent := by
  change Fintype TwoPhaseCycleEdge
  infer_instance

/-- Finite witness infrastructure for the cycle nerve's empty face type. -/
instance twoPhaseCycleFaceFintype : Fintype twoPhaseCycleNerve.FaceComponent := by
  change Fintype Empty
  infer_instance

/-- The no-face premise supplied by the explicit two-phase cycle nerve. -/
instance twoPhaseCycleFaceIsEmpty : IsEmpty twoPhaseCycleNerve.FaceComponent := by
  change IsEmpty Empty
  infer_instance

/-- Atom provenance and restriction indices for the proper two-phase cycle. -/
def twoPhaseCycleIndexing :
    AtomIndexedNerveData doctrine twoPhaseCycleNerve where
  ChartBasis := fun _ => PUnit
  EdgeBasis := fun _ => PUnit
  FaceBasis := fun _ => PUnit
  chartBasisFintype := fun _ => inferInstance
  edgeBasisFintype := fun _ => inferInstance
  faceBasisFintype := fun face => isEmptyElim face
  chartPair := fun chart _ =>
    match chart with
    | .structuralLeft | .structuralRight => structuralPair
    | .semanticLeft | .semanticRight => semanticPair
  edgePair := fun edge _ =>
    match edge with
    | .structuralTop | .structuralBottom => structuralPair
    | .semanticTop | .semanticBottom => semanticPair
  facePair := fun face => isEmptyElim face
  edgeLeftIndex := fun _ _ => PUnit.unit
  edgeRightIndex := fun _ _ => PUnit.unit
  faceEdge0Index := fun face => isEmptyElim face
  faceEdge1Index := fun face => isEmptyElim face
  faceEdge2Index := fun face => isEmptyElim face

/-- The concrete reviewed incidence complex on the expanded two-phase cycle. -/
def twoPhaseCycleAll :
    FiniteNerveCochainComplex twoPhaseCycleIndexing.expandedNerve (ZMod 2) := by
  let I := twoPhaseCycleIndexing
  letI : Fintype I.expandedNerve.Chart := I.chartFintype
  letI : Fintype I.expandedNerve.EdgeComponent := I.edgeFintype
  letI : Fintype I.expandedNerve.FaceComponent := I.faceFintype
  letI : IsEmpty I.expandedNerve.FaceComponent :=
    ⟨fun face => isEmptyElim face.1⟩
  exact noFaceIncidenceComplex I.expandedNerve (ZMod 2)

/-- The full proper two-phase parallel-cycle coefficient complex. -/
def twoPhaseCycleComplex :
    AtomIndexedCoefficientComplex doctrine family twoPhaseCycleNerve (ZMod 2) where
  indexing := twoPhaseCycleIndexing
  all := twoPhaseCycleAll

/-- Expanded structural-left chart coordinate. -/
def structuralLeftChart : twoPhaseCycleIndexing.expandedNerve.Chart :=
  ⟨TwoPhaseCycleChart.structuralLeft, PUnit.unit⟩

/-- Expanded structural-right chart coordinate. -/
def structuralRightChart : twoPhaseCycleIndexing.expandedNerve.Chart :=
  ⟨TwoPhaseCycleChart.structuralRight, PUnit.unit⟩

/-- Expanded semantic-left chart coordinate. -/
def semanticLeftChart : twoPhaseCycleIndexing.expandedNerve.Chart :=
  ⟨TwoPhaseCycleChart.semanticLeft, PUnit.unit⟩

/-- Expanded semantic-right chart coordinate. -/
def semanticRightChart : twoPhaseCycleIndexing.expandedNerve.Chart :=
  ⟨TwoPhaseCycleChart.semanticRight, PUnit.unit⟩

/-- Expanded top structural edge coordinate. -/
def structuralTopEdge : twoPhaseCycleIndexing.expandedNerve.EdgeComponent :=
  ⟨TwoPhaseCycleEdge.structuralTop, PUnit.unit⟩

/-- Expanded bottom structural edge coordinate. -/
def structuralBottomEdge : twoPhaseCycleIndexing.expandedNerve.EdgeComponent :=
  ⟨TwoPhaseCycleEdge.structuralBottom, PUnit.unit⟩

/-- Expanded top semantic edge coordinate. -/
def semanticTopEdge : twoPhaseCycleIndexing.expandedNerve.EdgeComponent :=
  ⟨TwoPhaseCycleEdge.semanticTop, PUnit.unit⟩

/-- Expanded bottom semantic edge coordinate. -/
def semanticBottomEdge : twoPhaseCycleIndexing.expandedNerve.EdgeComponent :=
  ⟨TwoPhaseCycleEdge.semanticBottom, PUnit.unit⟩

/-- The two selected structural charts have actual E0 structural provenance. -/
theorem structuralLeftChart_structural :
    family.Structural
      (twoPhaseCycleIndexing.chartPairAt structuralLeftChart) := by
  simpa [twoPhaseCycleIndexing, structuralLeftChart] using
    structuralPair_structural

/-- The right structural chart inherits structural provenance from `structuralPair`. -/
theorem structuralRightChart_structural :
    family.Structural
      (twoPhaseCycleIndexing.chartPairAt structuralRightChart) := by
  simpa [twoPhaseCycleIndexing, structuralRightChart] using
    structuralPair_structural

/-- The two selected semantic charts have actual E0 semantic provenance. -/
theorem semanticLeftChart_semantic :
    family.Semantic
      (twoPhaseCycleIndexing.chartPairAt semanticLeftChart) := by
  simpa [twoPhaseCycleIndexing, semanticLeftChart] using
    semanticPair_semantic

/-- The right semantic chart inherits semantic provenance from `semanticPair`. -/
theorem semanticRightChart_semantic :
    family.Semantic
      (twoPhaseCycleIndexing.chartPairAt semanticRightChart) := by
  simpa [twoPhaseCycleIndexing, semanticRightChart] using
    semanticPair_semantic

/-- Both structural parallel edges have actual E0 structural provenance. -/
theorem structuralTopEdge_structural :
    family.Structural
      (twoPhaseCycleIndexing.edgePairAt structuralTopEdge) := by
  simpa [twoPhaseCycleIndexing, structuralTopEdge] using
    structuralPair_structural

/-- The bottom structural edge inherits structural provenance from `structuralPair`. -/
theorem structuralBottomEdge_structural :
    family.Structural
      (twoPhaseCycleIndexing.edgePairAt structuralBottomEdge) := by
  simpa [twoPhaseCycleIndexing, structuralBottomEdge] using
    structuralPair_structural

/-- Both semantic parallel edges have actual E0 semantic provenance. -/
theorem semanticTopEdge_semantic :
    family.Semantic
      (twoPhaseCycleIndexing.edgePairAt semanticTopEdge) := by
  simpa [twoPhaseCycleIndexing, semanticTopEdge] using
    semanticPair_semantic

/-- The bottom semantic edge inherits semantic provenance from `semanticPair`. -/
theorem semanticBottomEdge_semantic :
    family.Semantic
      (twoPhaseCycleIndexing.edgePairAt semanticBottomEdge) := by
  simpa [twoPhaseCycleIndexing, semanticBottomEdge] using
    semanticPair_semantic

/-- Both derived phases occur in the actual coefficient basis. -/
theorem twoPhaseCycle_basis_has_both_phases :
    (∃ chart, family.Structural
        (twoPhaseCycleIndexing.chartPairAt chart)) ∧
      (∃ chart, family.Semantic
        (twoPhaseCycleIndexing.chartPairAt chart)) ∧
      (∃ edge, family.Structural
        (twoPhaseCycleIndexing.edgePairAt edge)) ∧
      (∃ edge, family.Semantic
        (twoPhaseCycleIndexing.edgePairAt edge)) :=
  ⟨⟨structuralLeftChart, structuralLeftChart_structural⟩,
    ⟨semanticLeftChart, semanticLeftChart_semantic⟩,
    ⟨structuralTopEdge, structuralTopEdge_structural⟩,
    ⟨semanticTopEdge, semanticTopEdge_semantic⟩⟩

/--
Condition E holds on the proper two-phase cycle.

For structural edges there is no support obligation.  On semantic edges both
endpoint coordinates of a structural zero-cochain vanish, so their actual
incidence difference vanishes.  Degree one is closed because there are no
faces.
-/
theorem twoPhaseCycle_conditionE : twoPhaseCycleComplex.ConditionE := by
  constructor
  · intro c hc
    change twoPhaseCycleComplex.all.d0 c ∈
      twoPhaseCycleComplex.structural1
    rw [twoPhaseCycleComplex.mem_structural1_iff]
    intro edge hedge
    rcases edge with ⟨edge, basis⟩
    rcases basis with ⟨⟩
    cases edge with
    | structuralTop =>
        exact (hedge (by simpa [twoPhaseCycleIndexing] using
          structuralTopEdge_structural)).elim
    | structuralBottom =>
        exact (hedge (by simpa [twoPhaseCycleIndexing] using
          structuralBottomEdge_structural)).elim
    | semanticTop =>
        rw [twoPhaseCycleComplex.d0_coordinate]
        change twoPhaseCycleComplex.all.zeroCochainCoordinates c
              semanticRightChart -
            twoPhaseCycleComplex.all.zeroCochainCoordinates c
              semanticLeftChart = 0
        have hright :=
          (twoPhaseCycleComplex.mem_structural0_iff c).1 hc
            semanticRightChart semanticRightChart_semantic
        have hleft :=
          (twoPhaseCycleComplex.mem_structural0_iff c).1 hc
            semanticLeftChart semanticLeftChart_semantic
        rw [hright, hleft]
        simp
    | semanticBottom =>
        rw [twoPhaseCycleComplex.d0_coordinate]
        change twoPhaseCycleComplex.all.zeroCochainCoordinates c
              semanticRightChart -
            twoPhaseCycleComplex.all.zeroCochainCoordinates c
              semanticLeftChart = 0
        have hright :=
          (twoPhaseCycleComplex.mem_structural0_iff c).1 hc
            semanticRightChart semanticRightChart_semantic
        have hleft :=
          (twoPhaseCycleComplex.mem_structural0_iff c).1 hc
            semanticLeftChart semanticLeftChart_semantic
        rw [hright, hleft]
        simp
  · intro c _hc
    change twoPhaseCycleComplex.all.d1 c ∈
      twoPhaseCycleComplex.structural2
    rw [twoPhaseCycleComplex.mem_structural2_iff]
    intro face
    exact isEmptyElim face.1

/-- Coordinate vector on the structural-left chart. -/
def structuralChartVector : twoPhaseCycleComplex.all.C0 :=
  twoPhaseCycleComplex.all.zeroCochainCoordinates.symm
    (coordinateVector structuralLeftChart)

/-- Coordinate vector on the semantic-left chart. -/
def semanticChartVector : twoPhaseCycleComplex.all.C0 :=
  twoPhaseCycleComplex.all.zeroCochainCoordinates.symm
    (coordinateVector semanticLeftChart)

/-- Coordinate vector on the top structural edge. -/
def structuralEdgeVector : twoPhaseCycleComplex.all.C1 :=
  twoPhaseCycleComplex.all.oneCochainCoordinates.symm
    (coordinateVector structuralTopEdge)

/-- Coordinate vector on the top semantic edge. -/
def semanticEdgeVector : twoPhaseCycleComplex.all.C1 :=
  twoPhaseCycleComplex.all.oneCochainCoordinates.symm
    (coordinateVector semanticTopEdge)

/-- The selected structural chart vector belongs to `F_struct`. -/
theorem structuralChartVector_mem :
    structuralChartVector ∈ twoPhaseCycleComplex.structural0 := by
  classical
  rw [twoPhaseCycleComplex.mem_structural0_iff]
  intro chart hchart
  rcases chart with ⟨chart, basis⟩
  rcases basis with ⟨⟩
  cases chart with
  | structuralLeft =>
      exact (hchart (by simpa [twoPhaseCycleIndexing] using
        structuralLeftChart_structural)).elim
  | structuralRight =>
      change coordinateVector structuralLeftChart structuralRightChart = 0
      have hne : structuralLeftChart ≠ structuralRightChart := by
        intro h
        exact TwoPhaseCycleChart.noConfusion (congrArg Sigma.fst h)
      simp [coordinateVector, hne]
  | semanticLeft =>
      change coordinateVector structuralLeftChart semanticLeftChart = 0
      have hne : structuralLeftChart ≠ semanticLeftChart := by
        intro h
        exact TwoPhaseCycleChart.noConfusion (congrArg Sigma.fst h)
      simp [coordinateVector, hne]
  | semanticRight =>
      change coordinateVector structuralLeftChart semanticRightChart = 0
      have hne : structuralLeftChart ≠ semanticRightChart := by
        intro h
        exact TwoPhaseCycleChart.noConfusion (congrArg Sigma.fst h)
      simp [coordinateVector, hne]

/-- The selected structural edge vector belongs to `F_struct`. -/
theorem structuralEdgeVector_mem :
    structuralEdgeVector ∈ twoPhaseCycleComplex.structural1 := by
  classical
  rw [twoPhaseCycleComplex.mem_structural1_iff]
  intro edge hedge
  rcases edge with ⟨edge, basis⟩
  rcases basis with ⟨⟩
  cases edge with
  | structuralTop =>
      exact (hedge (by simpa [twoPhaseCycleIndexing] using
        structuralTopEdge_structural)).elim
  | structuralBottom =>
      change coordinateVector structuralTopEdge structuralBottomEdge = 0
      have hne : structuralTopEdge ≠ structuralBottomEdge := by
        intro h
        exact TwoPhaseCycleEdge.noConfusion (congrArg Sigma.fst h)
      simp [coordinateVector, hne]
  | semanticTop =>
      change coordinateVector structuralTopEdge semanticTopEdge = 0
      have hne : structuralTopEdge ≠ semanticTopEdge := by
        intro h
        exact TwoPhaseCycleEdge.noConfusion (congrArg Sigma.fst h)
      simp [coordinateVector, hne]
  | semanticBottom =>
      change coordinateVector structuralTopEdge semanticBottomEdge = 0
      have hne : structuralTopEdge ≠ semanticBottomEdge := by
        intro h
        exact TwoPhaseCycleEdge.noConfusion (congrArg Sigma.fst h)
      simp [coordinateVector, hne]

/-- The semantic chart vector lies outside structural support. -/
theorem semanticChartVector_not_mem :
    semanticChartVector ∉ twoPhaseCycleComplex.structural0 := by
  intro hmem
  have hzero := (twoPhaseCycleComplex.mem_structural0_iff semanticChartVector).1
    hmem semanticLeftChart semanticLeftChart_semantic
  have hone : twoPhaseCycleComplex.all.zeroCochainCoordinates
      semanticChartVector semanticLeftChart = 1 := by
    simp [semanticChartVector, coordinateVector]
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- The semantic edge vector lies outside structural support. -/
theorem semanticEdgeVector_not_mem :
    semanticEdgeVector ∉ twoPhaseCycleComplex.structural1 := by
  intro hmem
  have hzero := (twoPhaseCycleComplex.mem_structural1_iff semanticEdgeVector).1
    hmem semanticTopEdge semanticTopEdge_semantic
  have hone : twoPhaseCycleComplex.all.oneCochainCoordinates
      semanticEdgeVector semanticTopEdge = 1 := by
    simp [semanticEdgeVector, coordinateVector]
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- The selected structural chart coordinate is a nonzero cochain. -/
theorem structuralChartVector_ne_zero : structuralChartVector ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg
    (fun c => twoPhaseCycleComplex.all.zeroCochainCoordinates c
      structuralLeftChart) hzero
  simp [structuralChartVector, coordinateVector] at hcoordinate

/-- The selected structural edge coordinate is a nonzero cochain. -/
theorem structuralEdgeVector_ne_zero : structuralEdgeVector ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg
    (fun c => twoPhaseCycleComplex.all.oneCochainCoordinates c
      structuralTopEdge) hzero
  simp [structuralEdgeVector, coordinateVector] at hcoordinate

/-- Structural chart support is nonzero. -/
theorem twoPhaseCycle_structural0_ne_bot :
    twoPhaseCycleComplex.structural0 ≠ ⊥ := by
  intro hbot
  have hmem := structuralChartVector_mem
  rw [hbot] at hmem
  have hzero : structuralChartVector = 0 := by simpa using hmem
  exact structuralChartVector_ne_zero hzero

/-- Structural chart support is proper. -/
theorem twoPhaseCycle_structural0_ne_top :
    twoPhaseCycleComplex.structural0 ≠ ⊤ := by
  intro htop
  apply semanticChartVector_not_mem
  rw [htop]
  exact Submodule.mem_top

/-- Structural edge support is nonzero. -/
theorem twoPhaseCycle_structural1_ne_bot :
    twoPhaseCycleComplex.structural1 ≠ ⊥ := by
  intro hbot
  have hmem := structuralEdgeVector_mem
  rw [hbot] at hmem
  have hzero : structuralEdgeVector = 0 := by simpa using hmem
  exact structuralEdgeVector_ne_zero hzero

/-- Structural edge support is proper. -/
theorem twoPhaseCycle_structural1_ne_top :
    twoPhaseCycleComplex.structural1 ≠ ⊤ := by
  intro htop
  apply semanticEdgeVector_not_mem
  rw [htop]
  exact Submodule.mem_top

/-- Difference of the two actual structural parallel-edge coordinates. -/
def structuralEdgeDifference : twoPhaseCycleComplex.all.C1 →ₗ[ZMod 2] ZMod 2 where
  toFun c :=
    twoPhaseCycleComplex.all.oneCochainCoordinates c structuralTopEdge -
      twoPhaseCycleComplex.all.oneCochainCoordinates c structuralBottomEdge
  map_add' left right := by simp; ring
  map_smul' scalar c := by simp [mul_sub]

/-- Every actual degree-zero boundary has zero structural parallel-edge difference. -/
theorem structuralEdgeDifference_boundary_zero
    (c : twoPhaseCycleComplex.all.C0) :
    structuralEdgeDifference (twoPhaseCycleComplex.all.d0 c) = 0 := by
  rw [show structuralEdgeDifference
      (twoPhaseCycleComplex.all.d0 c) =
        twoPhaseCycleComplex.all.oneCochainCoordinates
              (twoPhaseCycleComplex.all.d0 c) structuralTopEdge -
          twoPhaseCycleComplex.all.oneCochainCoordinates
              (twoPhaseCycleComplex.all.d0 c) structuralBottomEdge by rfl]
  rw [twoPhaseCycleComplex.d0_coordinate,
    twoPhaseCycleComplex.d0_coordinate]
  change
    (twoPhaseCycleComplex.all.zeroCochainCoordinates c structuralRightChart -
        twoPhaseCycleComplex.all.zeroCochainCoordinates c structuralLeftChart) -
      (twoPhaseCycleComplex.all.zeroCochainCoordinates c structuralRightChart -
        twoPhaseCycleComplex.all.zeroCochainCoordinates c structuralLeftChart) = 0
  ring

/-- The selected structural edge cochain in the actual structural subspace. -/
def structuralCochain : twoPhaseCycleComplex.structural1 :=
  ⟨structuralEdgeVector, structuralEdgeVector_mem⟩

/-- The selected structural cochain is a cocycle because the actual nerve has no faces. -/
theorem structuralCochain_cocycle :
    (twoPhaseCycleComplex.structuralComplex twoPhaseCycle_conditionE).d1
        structuralCochain = 0 := by
  apply Subtype.ext
  apply twoPhaseCycleComplex.all.twoCochainCoordinates.injective
  funext face
  exact isEmptyElim face.1

/-- The actual structural parallel-edge cocycle. -/
def structuralCycle :
    LinearMap.ker
      (twoPhaseCycleComplex.structuralComplex twoPhaseCycle_conditionE).d1 :=
  ⟨structuralCochain, structuralCochain_cocycle⟩

/-- Its standard structural `H^1` quotient class. -/
def structuralH1Class :
    (twoPhaseCycleComplex.structuralComplex twoPhaseCycle_conditionE).H1 :=
  (LinearMap.range
    (twoPhaseCycleComplex.structuralComplex
      twoPhaseCycle_conditionE).boundaryToCycles).mkQ structuralCycle

/-- The actual structural cocycle has nonzero parallel-edge difference. -/
theorem structuralEdgeDifference_structuralCycle :
    structuralEdgeDifference structuralCycle.1.1 = 1 := by
  classical
  have hne : structuralTopEdge ≠ structuralBottomEdge := by
    intro h
    exact TwoPhaseCycleEdge.noConfusion (congrArg Sigma.fst h)
  simp [structuralCycle, structuralCochain, structuralEdgeVector,
    structuralEdgeDifference, coordinateVector, hne]

/-- The concrete standard structural `H^1` class is nonzero. -/
theorem structuralH1Class_ne_zero : structuralH1Class ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range
      (twoPhaseCycleComplex.structuralComplex
        twoPhaseCycle_conditionE).boundaryToCycles)).1 hzero
  rcases hmem with ⟨c, hc⟩
  have hdifference := congrArg
    (fun z : LinearMap.ker
        (twoPhaseCycleComplex.structuralComplex
          twoPhaseCycle_conditionE).d1 =>
      structuralEdgeDifference z.1.1) hc
  change structuralEdgeDifference
      (twoPhaseCycleComplex.all.d0 c.1) =
    structuralEdgeDifference structuralCycle.1.1 at hdifference
  rw [structuralEdgeDifference_boundary_zero,
    structuralEdgeDifference_structuralCycle] at hdifference
  exact zero_ne_one hdifference

/-- Condition E does not force structural `H^1` to vanish. -/
theorem twoPhaseCycle_structuralH1_not_zero :
    ¬ (twoPhaseCycleComplex.structuralComplex
      twoPhaseCycle_conditionE).H1Zero := by
  intro hzero
  exact structuralH1Class_ne_zero (hzero structuralH1Class)

/-- The canonical inclusion sends the structural cycle to the all-phase cycle space. -/
def structuralAllCycle : LinearMap.ker twoPhaseCycleComplex.allComplex.d1 :=
  (twoPhaseCycleComplex.inclusion twoPhaseCycle_conditionE).cyclesMap structuralCycle

/-- The structural class transported by the canonical structural inclusion. -/
def structuralAllClass : twoPhaseCycleComplex.allComplex.H1 :=
  twoPhaseCycleComplex.structuralH1Map twoPhaseCycle_conditionE structuralH1Class

/-- The canonical transported class is represented by the same actual edge cochain. -/
theorem structuralAllClass_representation :
    structuralAllClass =
      (LinearMap.range twoPhaseCycleComplex.allComplex.boundaryToCycles).mkQ
        structuralAllCycle :=
  rfl

/-- The transported structural cycle retains its nonzero parallel-edge difference. -/
theorem structuralEdgeDifference_structuralAllCycle :
    structuralEdgeDifference structuralAllCycle.1 = 1 := by
  simpa [structuralAllCycle] using structuralEdgeDifference_structuralCycle

/-- The canonical structural class remains nonzero in all-phase `H^1`. -/
theorem structuralAllClass_ne_zero : structuralAllClass ≠ 0 := by
  intro hzero
  rw [structuralAllClass_representation] at hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range twoPhaseCycleComplex.allComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨c, hc⟩
  have hdifference := congrArg
    (fun z : LinearMap.ker twoPhaseCycleComplex.allComplex.d1 =>
      structuralEdgeDifference z.1) hc
  change structuralEdgeDifference (twoPhaseCycleComplex.all.d0 c) =
    structuralEdgeDifference structuralAllCycle.1 at hdifference
  rw [structuralEdgeDifference_boundary_zero,
    structuralEdgeDifference_structuralAllCycle] at hdifference
  exact zero_ne_one hdifference

/-- The canonical semantic quotient kills the transported structural class. -/
theorem structuralAllClass_semanticImage_zero :
    twoPhaseCycleComplex.standardSemanticH1Map twoPhaseCycle_conditionE
        structuralAllClass = 0 := by
  have hrange : structuralAllClass ∈ LinearMap.range
      (twoPhaseCycleComplex.structuralH1Map twoPhaseCycle_conditionE) :=
    ⟨structuralH1Class, rfl⟩
  apply LinearMap.mem_ker.mp
  rw [LinearMap.exact_iff.mp
    (twoPhaseCycleComplex.h1_middle_exact twoPhaseCycle_conditionE)]
  exact hrange

/-- A nonzero all-phase class missed by the canonical semantic quotient. -/
theorem unconditionalSupport_counterexample :
    ∃ x : twoPhaseCycleComplex.allComplex.H1,
      x ≠ 0 ∧
        twoPhaseCycleComplex.standardSemanticH1Map
          twoPhaseCycle_conditionE x = 0 :=
  ⟨structuralAllClass, structuralAllClass_ne_zero,
    structuralAllClass_semanticImage_zero⟩

/-- Difference of the two actual semantic parallel-edge coordinates. -/
def semanticEdgeDifference : twoPhaseCycleComplex.all.C1 →ₗ[ZMod 2] ZMod 2 where
  toFun c :=
    twoPhaseCycleComplex.all.oneCochainCoordinates c semanticTopEdge -
      twoPhaseCycleComplex.all.oneCochainCoordinates c semanticBottomEdge
  map_add' left right := by simp; ring
  map_smul' scalar c := by simp [mul_sub]

/-- Every actual degree-zero boundary has zero semantic parallel-edge difference. -/
theorem semanticEdgeDifference_boundary_zero
    (c : twoPhaseCycleComplex.all.C0) :
    semanticEdgeDifference (twoPhaseCycleComplex.all.d0 c) = 0 := by
  rw [show semanticEdgeDifference
      (twoPhaseCycleComplex.all.d0 c) =
        twoPhaseCycleComplex.all.oneCochainCoordinates
              (twoPhaseCycleComplex.all.d0 c) semanticTopEdge -
          twoPhaseCycleComplex.all.oneCochainCoordinates
              (twoPhaseCycleComplex.all.d0 c) semanticBottomEdge by rfl]
  rw [twoPhaseCycleComplex.d0_coordinate,
    twoPhaseCycleComplex.d0_coordinate]
  change
    (twoPhaseCycleComplex.all.zeroCochainCoordinates c semanticRightChart -
        twoPhaseCycleComplex.all.zeroCochainCoordinates c semanticLeftChart) -
      (twoPhaseCycleComplex.all.zeroCochainCoordinates c semanticRightChart -
        twoPhaseCycleComplex.all.zeroCochainCoordinates c semanticLeftChart) = 0
  ring

/-- The semantic edge difference vanishes on every structural one-cochain. -/
theorem semanticEdgeDifference_vanishes_on_structural1
    (c : twoPhaseCycleComplex.all.C1)
    (hc : c ∈ twoPhaseCycleComplex.structural1) :
    semanticEdgeDifference c = 0 := by
  have htop := (twoPhaseCycleComplex.mem_structural1_iff c).1 hc
    semanticTopEdge semanticTopEdge_semantic
  have hbottom := (twoPhaseCycleComplex.mem_structural1_iff c).1 hc
    semanticBottomEdge semanticBottomEdge_semantic
  simp [semanticEdgeDifference, htop, hbottom]

/--
The actual semantic parallel-edge difference descends through the canonical
degree-one quotient by structural support.
-/
def semanticQuotientEdgeDifference :
    (twoPhaseCycleComplex.all.C1 ⧸ twoPhaseCycleComplex.structural1) →ₗ[ZMod 2]
      ZMod 2 :=
  twoPhaseCycleComplex.structural1.liftQ semanticEdgeDifference (by
    intro c hc
    change semanticEdgeDifference c = 0
    exact semanticEdgeDifference_vanishes_on_structural1 c hc)

/-- Every semantic-quotient boundary has zero semantic parallel-edge difference. -/
theorem semanticQuotientEdgeDifference_boundary_zero
    (q : (twoPhaseCycleComplex.semanticComplex
      twoPhaseCycle_conditionE).C0) :
    semanticQuotientEdgeDifference
        ((twoPhaseCycleComplex.semanticComplex
          twoPhaseCycle_conditionE).d0 q) = 0 := by
  obtain ⟨c, rfl⟩ := twoPhaseCycleComplex.structural0.mkQ_surjective q
  change semanticQuotientEdgeDifference
      (twoPhaseCycleComplex.structural1.mkQ
        (twoPhaseCycleComplex.all.d0 c)) = 0
  rw [semanticQuotientEdgeDifference, Submodule.mkQ_apply,
    Submodule.liftQ_apply]
  exact semanticEdgeDifference_boundary_zero c

/-- The selected semantic-edge cochain in the all-phase complex. -/
def firingCochain : twoPhaseCycleComplex.allComplex.C1 :=
  semanticEdgeVector

/-- The firing cochain is an actual cocycle because the nerve has no faces. -/
theorem firingCochain_cocycle :
    twoPhaseCycleComplex.allComplex.d1 firingCochain = 0 := by
  apply twoPhaseCycleComplex.all.twoCochainCoordinates.injective
  funext face
  exact isEmptyElim face.1

/-- The actual semantic parallel-edge cocycle in the all-phase complex. -/
def firingCycle : LinearMap.ker twoPhaseCycleComplex.allComplex.d1 :=
  ⟨firingCochain, firingCochain_cocycle⟩

/-- Its standard all-phase `H^1` quotient class. -/
def firingClass : twoPhaseCycleComplex.allComplex.H1 :=
  (LinearMap.range twoPhaseCycleComplex.allComplex.boundaryToCycles).mkQ
    firingCycle

/-- The canonical cochain projection of the firing cycle. -/
def firingSemanticCycle :
    LinearMap.ker
      (twoPhaseCycleComplex.semanticComplex twoPhaseCycle_conditionE).d1 :=
  (twoPhaseCycleComplex.projection twoPhaseCycle_conditionE).cyclesMap
    firingCycle

/-- The canonical projected cycle has nonzero semantic parallel-edge difference. -/
theorem semanticQuotientEdgeDifference_firingSemanticCycle :
    semanticQuotientEdgeDifference firingSemanticCycle.1 = 1 := by
  classical
  change semanticQuotientEdgeDifference
      (twoPhaseCycleComplex.structural1.mkQ semanticEdgeVector) = 1
  rw [semanticQuotientEdgeDifference, Submodule.mkQ_apply,
    Submodule.liftQ_apply]
  have hne : semanticTopEdge ≠ semanticBottomEdge := by
    intro h
    exact TwoPhaseCycleEdge.noConfusion (congrArg Sigma.fst h)
  simp [semanticEdgeDifference, semanticEdgeVector, coordinateVector, hne]

/-- The actual firing class has nonzero image under the canonical semantic quotient. -/
theorem firingSemanticImage_ne_zero :
    twoPhaseCycleComplex.standardSemanticH1Map twoPhaseCycle_conditionE
        firingClass ≠ 0 := by
  intro hzero
  change (LinearMap.range
      (twoPhaseCycleComplex.semanticComplex
        twoPhaseCycle_conditionE).boundaryToCycles).mkQ
        firingSemanticCycle = 0 at hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range
      (twoPhaseCycleComplex.semanticComplex
        twoPhaseCycle_conditionE).boundaryToCycles)).1 hzero
  rcases hmem with ⟨q, hq⟩
  have hdifference := congrArg
    (fun z : LinearMap.ker
        (twoPhaseCycleComplex.semanticComplex
          twoPhaseCycle_conditionE).d1 =>
      semanticQuotientEdgeDifference z.1) hq
  change semanticQuotientEdgeDifference
      ((twoPhaseCycleComplex.semanticComplex
        twoPhaseCycle_conditionE).d0 q) =
    semanticQuotientEdgeDifference firingSemanticCycle.1 at hdifference
  rw [semanticQuotientEdgeDifference_boundary_zero,
    semanticQuotientEdgeDifference_firingSemanticCycle] at hdifference
  exact zero_ne_one hdifference

/-- The firing all-phase `H^1` class itself is nonzero. -/
theorem firingClass_ne_zero : firingClass ≠ 0 := by
  intro hzero
  apply firingSemanticImage_ne_zero
  calc
    twoPhaseCycleComplex.standardSemanticH1Map twoPhaseCycle_conditionE
          firingClass =
        twoPhaseCycleComplex.standardSemanticH1Map
          twoPhaseCycle_conditionE 0 :=
      congrArg
        (fun x => twoPhaseCycleComplex.standardSemanticH1Map
          twoPhaseCycle_conditionE x) hzero
    _ = 0 := LinearMap.map_zero _

/-! ## Nonvacuous positive and negative freshness witnesses -/

/-- Three actual charts forming a two-edge structural path. -/
inductive FreshPathChart where
  | left
  | middle
  | right
  deriving DecidableEq, Fintype

/-- The two consecutive structural edges of the freshness path. -/
inductive FreshPathEdge where
  | leftLeg
  | rightLeg
  deriving DecidableEq, Fintype

/-- A face-free path whose two edges meet only at the middle chart. -/
def freshPathNerve : CoverNerve where
  Chart := FreshPathChart
  EdgeComponent := FreshPathEdge
  FaceComponent := Empty
  edgeLeft
    | .leftLeg => .left
    | .rightLeg => .middle
  edgeRight
    | .leftLeg => .middle
    | .rightLeg => .right
  faceEdge0 := fun face => isEmptyElim face
  faceEdge1 := fun face => isEmptyElim face
  faceEdge2 := fun face => isEmptyElim face
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := by simp
  faceTripleOverlapComponent_holds := fun face => isEmptyElim face

/-- Finite witness infrastructure inherited from the freshness path charts. -/
instance freshPathChartFintype : Fintype freshPathNerve.Chart := by
  change Fintype FreshPathChart
  infer_instance

/-- Finite witness infrastructure inherited from the freshness path edges. -/
instance freshPathEdgeFintype : Fintype freshPathNerve.EdgeComponent := by
  change Fintype FreshPathEdge
  infer_instance

/-- Finite witness infrastructure for the freshness path's empty face type. -/
instance freshPathFaceFintype : Fintype freshPathNerve.FaceComponent := by
  change Fintype Empty
  infer_instance

/-- The no-face premise supplied by the explicit freshness path. -/
instance freshPathFaceIsEmpty : IsEmpty freshPathNerve.FaceComponent := by
  change IsEmpty Empty
  infer_instance

/-- Atom provenance and restriction indices for the all-structural path. -/
def freshPathIndexing : AtomIndexedNerveData doctrine freshPathNerve where
  ChartBasis := fun _ => PUnit
  EdgeBasis := fun _ => PUnit
  FaceBasis := fun _ => PUnit
  chartBasisFintype := fun _ => inferInstance
  edgeBasisFintype := fun _ => inferInstance
  faceBasisFintype := fun face => isEmptyElim face
  chartPair := fun _ _ => structuralPair
  edgePair := fun _ _ => structuralPair
  facePair := fun face => isEmptyElim face
  edgeLeftIndex := fun _ _ => PUnit.unit
  edgeRightIndex := fun _ _ => PUnit.unit
  faceEdge0Index := fun face => isEmptyElim face
  faceEdge1Index := fun face => isEmptyElim face
  faceEdge2Index := fun face => isEmptyElim face

/-- The actual incidence complex on the expanded all-structural path. -/
def freshPathAll :
    FiniteNerveCochainComplex freshPathIndexing.expandedNerve (ZMod 2) := by
  let I := freshPathIndexing
  letI : Fintype I.expandedNerve.Chart := I.chartFintype
  letI : Fintype I.expandedNerve.EdgeComponent := I.edgeFintype
  letI : Fintype I.expandedNerve.FaceComponent := I.faceFintype
  letI : IsEmpty I.expandedNerve.FaceComponent :=
    ⟨fun face => isEmptyElim face.1⟩
  exact noFaceIncidenceComplex I.expandedNerve (ZMod 2)

/-- The Atom-indexed coefficient complex on the all-structural path. -/
def freshPathComplex :
    AtomIndexedCoefficientComplex doctrine family freshPathNerve (ZMod 2) where
  indexing := freshPathIndexing
  all := freshPathAll

/-- Expanded left chart of the freshness path. -/
def freshPathLeftChart : freshPathIndexing.expandedNerve.Chart :=
  ⟨FreshPathChart.left, PUnit.unit⟩

/-- Expanded middle chart of the freshness path. -/
def freshPathMiddleChart : freshPathIndexing.expandedNerve.Chart :=
  ⟨FreshPathChart.middle, PUnit.unit⟩

/-- Expanded right chart of the freshness path. -/
def freshPathRightChart : freshPathIndexing.expandedNerve.Chart :=
  ⟨FreshPathChart.right, PUnit.unit⟩

/-- Expanded left edge of the freshness path. -/
def freshPathLeftEdge : freshPathIndexing.expandedNerve.EdgeComponent :=
  ⟨FreshPathEdge.leftLeg, PUnit.unit⟩

/-- Expanded right edge of the freshness path. -/
def freshPathRightEdge : freshPathIndexing.expandedNerve.EdgeComponent :=
  ⟨FreshPathEdge.rightLeg, PUnit.unit⟩

/-- Every expanded chart of the path has actual E0 structural provenance. -/
theorem freshPath_chart_structural
    (chart : freshPathIndexing.expandedNerve.Chart) :
    family.Structural (freshPathIndexing.chartPairAt chart) := by
  simpa [freshPathIndexing] using structuralPair_structural

/-- Every expanded edge of the path has actual E0 structural provenance. -/
theorem freshPath_edge_structural
    (edge : freshPathIndexing.expandedNerve.EdgeComponent) :
    family.Structural (freshPathIndexing.edgePairAt edge) := by
  simpa [freshPathIndexing] using structuralPair_structural

/-- Condition E holds on the all-structural path. -/
theorem freshPath_conditionE : freshPathComplex.ConditionE := by
  constructor
  · intro c _hc
    change freshPathComplex.all.d0 c ∈ freshPathComplex.structural1
    rw [freshPathComplex.mem_structural1_iff]
    intro edge hedge
    exact (hedge (freshPath_edge_structural edge)).elim
  · intro c _hc
    change freshPathComplex.all.d1 c ∈ freshPathComplex.structural2
    rw [freshPathComplex.mem_structural2_iff]
    intro face
    exact isEmptyElim face.1

/-- The left leaf is pruned from the first edge of the path. -/
def freshPathLeftPruningEntry :
    AtomIndexedCoefficientComplex.StructuralForestPruningEntry
      freshPathComplex where
  edge := freshPathLeftEdge
  leaf := freshPathLeftChart
  leafOnRight := false
  leaf_eq_endpoint := rfl
  leaf_ne_opposite := by
    intro h
    exact FreshPathChart.noConfusion (congrArg Sigma.fst h)
  leaf_structural := fun _hedge =>
    freshPath_chart_structural freshPathLeftChart

/-- The right leaf is pruned from the second edge of the path. -/
def freshPathRightPruningEntry :
    AtomIndexedCoefficientComplex.StructuralForestPruningEntry
      freshPathComplex where
  edge := freshPathRightEdge
  leaf := freshPathRightChart
  leafOnRight := true
  leaf_eq_endpoint := rfl
  leaf_ne_opposite := by
    intro h
    exact FreshPathChart.noConfusion (congrArg Sigma.fst h)
  leaf_structural := fun _hedge =>
    freshPath_chart_structural freshPathRightChart

/-- A deliberately wrong first step that removes the shared middle chart. -/
def freshPathMiddlePruningEntry :
    AtomIndexedCoefficientComplex.StructuralForestPruningEntry
      freshPathComplex where
  edge := freshPathLeftEdge
  leaf := freshPathMiddleChart
  leafOnRight := true
  leaf_eq_endpoint := rfl
  leaf_ne_opposite := by
    intro h
    exact FreshPathChart.noConfusion (congrArg Sigma.fst h)
  leaf_structural := fun _hedge =>
    freshPath_chart_structural freshPathMiddleChart

/-- Pruning the left leaf before the right leaf is a nonvacuous `Fresh` pair. -/
theorem freshPath_left_before_right_fresh :
    AtomIndexedCoefficientComplex.StructuralForestPruningEntry.Fresh
      freshPathLeftPruningEntry freshPathRightPruningEntry := by
  constructor
  · intro h
    exact FreshPathChart.noConfusion (congrArg Sigma.fst h)
  · intro h
    exact FreshPathChart.noConfusion (congrArg Sigma.fst h)

/-- Removing the shared middle chart first fails `Fresh` at the later left endpoint. -/
theorem freshPath_middle_before_right_not_fresh :
    ¬ AtomIndexedCoefficientComplex.StructuralForestPruningEntry.Fresh
      freshPathMiddlePruningEntry freshPathRightPruningEntry := by
  intro h
  exact h.1 rfl

/-- The two-edge path is an actual non-singleton structural pruning order. -/
def freshPathStructuralPruning :
    AtomIndexedCoefficientComplex.StructuralForestPruning
      freshPathComplex freshPath_conditionE where
  entries := [freshPathLeftPruningEntry, freshPathRightPruningEntry]
  all_faceFree_structural_edges := by
    intro edge _hfree _hedge
    rcases edge with ⟨edge, basis⟩
    rcases basis with ⟨⟩
    cases edge with
    | leftLeg => simp [freshPathLeftPruningEntry, freshPathLeftEdge]
    | rightLeg => simp [freshPathRightPruningEntry, freshPathRightEdge]
  leafOrder := by
    simpa using freshPath_left_before_right_fresh
  noTripleFaces := ⟨fun face => isEmptyElim face.1⟩

/-! ## A nonvacuous structural-forest firing regime -/

/-- One structural bridge and a genuine semantic parallel-edge cycle. -/
inductive ForestFiringEdge where
  | structuralBridge
  | semanticTop
  | semanticBottom
  deriving DecidableEq, Fintype

/-- A structural tree disjoint from a semantic cycle. -/
def forestFiringNerve : CoverNerve where
  Chart := TwoPhaseCycleChart
  EdgeComponent := ForestFiringEdge
  FaceComponent := Empty
  edgeLeft
    | .structuralBridge => .structuralLeft
    | .semanticTop | .semanticBottom => .semanticLeft
  edgeRight
    | .structuralBridge => .structuralRight
    | .semanticTop | .semanticBottom => .semanticRight
  faceEdge0 := fun face => isEmptyElim face
  faceEdge1 := fun face => isEmptyElim face
  faceEdge2 := fun face => isEmptyElim face
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := by simp
  faceTripleOverlapComponent_holds := fun face => isEmptyElim face

/-- Finite witness infrastructure inherited from the forest firing chart type. -/
instance forestFiringChartFintype : Fintype forestFiringNerve.Chart := by
  change Fintype TwoPhaseCycleChart
  infer_instance

/-- Finite witness infrastructure inherited from the forest firing edge type. -/
instance forestFiringEdgeFintype : Fintype forestFiringNerve.EdgeComponent := by
  change Fintype ForestFiringEdge
  infer_instance

/-- Finite witness infrastructure for the forest firing nerve's empty face type. -/
instance forestFiringFaceFintype : Fintype forestFiringNerve.FaceComponent := by
  change Fintype Empty
  infer_instance

/-- The no-triple-face premise supplied by the explicit forest firing nerve. -/
instance forestFiringFaceIsEmpty : IsEmpty forestFiringNerve.FaceComponent := by
  change IsEmpty Empty
  infer_instance

/-- Atom provenance for the structural-tree / semantic-cycle witness. -/
def forestFiringIndexing : AtomIndexedNerveData doctrine forestFiringNerve where
  ChartBasis := fun _ => PUnit
  EdgeBasis := fun _ => PUnit
  FaceBasis := fun _ => PUnit
  chartBasisFintype := fun _ => inferInstance
  edgeBasisFintype := fun _ => inferInstance
  faceBasisFintype := fun face => isEmptyElim face
  chartPair := fun chart _ =>
    match chart with
    | .structuralLeft | .structuralRight => structuralPair
    | .semanticLeft | .semanticRight => semanticPair
  edgePair := fun edge _ =>
    match edge with
    | .structuralBridge => structuralPair
    | .semanticTop | .semanticBottom => semanticPair
  facePair := fun face => isEmptyElim face
  edgeLeftIndex := fun _ _ => PUnit.unit
  edgeRightIndex := fun _ _ => PUnit.unit
  faceEdge0Index := fun face => isEmptyElim face
  faceEdge1Index := fun face => isEmptyElim face
  faceEdge2Index := fun face => isEmptyElim face

/-- The actual incidence complex for the structural-tree / semantic-cycle witness. -/
def forestFiringAll :
    FiniteNerveCochainComplex forestFiringIndexing.expandedNerve (ZMod 2) := by
  let I := forestFiringIndexing
  letI : Fintype I.expandedNerve.Chart := I.chartFintype
  letI : Fintype I.expandedNerve.EdgeComponent := I.edgeFintype
  letI : Fintype I.expandedNerve.FaceComponent := I.faceFintype
  letI : IsEmpty I.expandedNerve.FaceComponent :=
    ⟨fun face => isEmptyElim face.1⟩
  exact noFaceIncidenceComplex I.expandedNerve (ZMod 2)

/-- The coefficient complex with a structural forest and a semantic cycle. -/
def forestFiringComplex :
    AtomIndexedCoefficientComplex doctrine family forestFiringNerve (ZMod 2) where
  indexing := forestFiringIndexing
  all := forestFiringAll

/-- Expanded structural-left chart used by the forest firing witness. -/
def forestStructuralLeftChart : forestFiringIndexing.expandedNerve.Chart :=
  ⟨TwoPhaseCycleChart.structuralLeft, PUnit.unit⟩

/-- Expanded structural-right chart used by the forest pruning entry. -/
def forestStructuralRightChart : forestFiringIndexing.expandedNerve.Chart :=
  ⟨TwoPhaseCycleChart.structuralRight, PUnit.unit⟩

/-- Expanded semantic-left chart supporting the retained semantic cycle. -/
def forestSemanticLeftChart : forestFiringIndexing.expandedNerve.Chart :=
  ⟨TwoPhaseCycleChart.semanticLeft, PUnit.unit⟩

/-- Expanded semantic-right chart supporting the retained semantic cycle. -/
def forestSemanticRightChart : forestFiringIndexing.expandedNerve.Chart :=
  ⟨TwoPhaseCycleChart.semanticRight, PUnit.unit⟩

/-- The unique structural bridge covered by the forest pruning order. -/
def forestStructuralEdge : forestFiringIndexing.expandedNerve.EdgeComponent :=
  ⟨ForestFiringEdge.structuralBridge, PUnit.unit⟩

/-- The top semantic edge retained outside structural pruning. -/
def forestSemanticTopEdge : forestFiringIndexing.expandedNerve.EdgeComponent :=
  ⟨ForestFiringEdge.semanticTop, PUnit.unit⟩

/-- The bottom semantic edge retained outside structural pruning. -/
def forestSemanticBottomEdge : forestFiringIndexing.expandedNerve.EdgeComponent :=
  ⟨ForestFiringEdge.semanticBottom, PUnit.unit⟩

/-- The left forest chart has E0 structural provenance. -/
theorem forestStructuralLeftChart_structural :
    family.Structural
      (forestFiringIndexing.chartPairAt forestStructuralLeftChart) := by
  simpa [forestFiringIndexing, forestStructuralLeftChart] using
    structuralPair_structural

/-- The right forest chart has E0 structural provenance. -/
theorem forestStructuralRightChart_structural :
    family.Structural
      (forestFiringIndexing.chartPairAt forestStructuralRightChart) := by
  simpa [forestFiringIndexing, forestStructuralRightChart] using
    structuralPair_structural

/-- The left retained chart has E0 semantic provenance. -/
theorem forestSemanticLeftChart_semantic :
    family.Semantic
      (forestFiringIndexing.chartPairAt forestSemanticLeftChart) := by
  simpa [forestFiringIndexing, forestSemanticLeftChart] using
    semanticPair_semantic

/-- The right retained chart has E0 semantic provenance. -/
theorem forestSemanticRightChart_semantic :
    family.Semantic
      (forestFiringIndexing.chartPairAt forestSemanticRightChart) := by
  simpa [forestFiringIndexing, forestSemanticRightChart] using
    semanticPair_semantic

/-- The pruned bridge has E0 structural provenance. -/
theorem forestStructuralEdge_structural :
    family.Structural
      (forestFiringIndexing.edgePairAt forestStructuralEdge) := by
  simpa [forestFiringIndexing, forestStructuralEdge] using
    structuralPair_structural

/-- The top retained edge has E0 semantic provenance. -/
theorem forestSemanticTopEdge_semantic :
    family.Semantic
      (forestFiringIndexing.edgePairAt forestSemanticTopEdge) := by
  simpa [forestFiringIndexing, forestSemanticTopEdge] using
    semanticPair_semantic

/-- The bottom retained edge has E0 semantic provenance. -/
theorem forestSemanticBottomEdge_semantic :
    family.Semantic
      (forestFiringIndexing.edgePairAt forestSemanticBottomEdge) := by
  simpa [forestFiringIndexing, forestSemanticBottomEdge] using
    semanticPair_semantic

/-- Condition E holds because semantic edges have only semantic endpoints. -/
theorem forestFiring_conditionE : forestFiringComplex.ConditionE := by
  constructor
  · intro c hc
    change forestFiringComplex.all.d0 c ∈ forestFiringComplex.structural1
    rw [forestFiringComplex.mem_structural1_iff]
    intro edge hedge
    rcases edge with ⟨edge, basis⟩
    rcases basis with ⟨⟩
    cases edge with
    | structuralBridge =>
        exact (hedge (by simpa [forestFiringIndexing] using
          forestStructuralEdge_structural)).elim
    | semanticTop =>
        rw [forestFiringComplex.d0_coordinate]
        change forestFiringComplex.all.zeroCochainCoordinates c
              forestSemanticRightChart -
            forestFiringComplex.all.zeroCochainCoordinates c
              forestSemanticLeftChart = 0
        have hright := (forestFiringComplex.mem_structural0_iff c).1 hc
          forestSemanticRightChart forestSemanticRightChart_semantic
        have hleft := (forestFiringComplex.mem_structural0_iff c).1 hc
          forestSemanticLeftChart forestSemanticLeftChart_semantic
        rw [hright, hleft]
        simp
    | semanticBottom =>
        rw [forestFiringComplex.d0_coordinate]
        change forestFiringComplex.all.zeroCochainCoordinates c
              forestSemanticRightChart -
            forestFiringComplex.all.zeroCochainCoordinates c
              forestSemanticLeftChart = 0
        have hright := (forestFiringComplex.mem_structural0_iff c).1 hc
          forestSemanticRightChart forestSemanticRightChart_semantic
        have hleft := (forestFiringComplex.mem_structural0_iff c).1 hc
          forestSemanticLeftChart forestSemanticLeftChart_semantic
        rw [hright, hleft]
        simp
  · intro c _hc
    change forestFiringComplex.all.d1 c ∈ forestFiringComplex.structural2
    rw [forestFiringComplex.mem_structural2_iff]
    intro face
    exact isEmptyElim face.1

/-- The single structural edge with its actual structural leaf endpoint. -/
def forestStructuralPruningEntry :
    AtomIndexedCoefficientComplex.StructuralForestPruningEntry
      forestFiringComplex where
  edge := forestStructuralEdge
  leaf := forestStructuralRightChart
  leafOnRight := true
  leaf_eq_endpoint := rfl
  leaf_ne_opposite := by
    change forestStructuralRightChart ≠ forestStructuralLeftChart
    intro h
    exact TwoPhaseCycleChart.noConfusion (congrArg Sigma.fst h)
  leaf_structural := fun _hedge => forestStructuralRightChart_structural

/-- Actual structural-only pruning; the semantic parallel cycle is deliberately retained. -/
def forestStructuralPruning :
    AtomIndexedCoefficientComplex.StructuralForestPruning
      forestFiringComplex forestFiring_conditionE where
  entries := [forestStructuralPruningEntry]
  all_faceFree_structural_edges := by
    intro edge _hfree hedge
    rcases edge with ⟨edge, basis⟩
    rcases basis with ⟨⟩
    cases edge with
    | structuralBridge => simp [forestStructuralPruningEntry, forestStructuralEdge]
    | semanticTop =>
        exact (forestSemanticTopEdge_semantic hedge).elim
    | semanticBottom =>
        exact (forestSemanticBottomEdge_semantic hedge).elim
  leafOrder := by simp
  noTripleFaces := ⟨fun face => isEmptyElim face.1⟩

/-- The selected semantic edge cochain in the structural-forest witness. -/
def forestFiringCochain : forestFiringComplex.allComplex.C1 :=
  forestFiringComplex.all.oneCochainCoordinates.symm
    (coordinateVector forestSemanticTopEdge)

/-- The selected forest firing cochain is a cocycle because the witness has no faces. -/
theorem forestFiringCochain_cocycle :
    forestFiringComplex.allComplex.d1 forestFiringCochain = 0 := by
  apply forestFiringComplex.all.twoCochainCoordinates.injective
  funext face
  exact isEmptyElim face.1

/-- The kernel element represented by the selected semantic edge cochain. -/
def forestFiringCycle : LinearMap.ker forestFiringComplex.allComplex.d1 :=
  ⟨forestFiringCochain, forestFiringCochain_cocycle⟩

/-- The standard all-phase `H^1` quotient class of `forestFiringCycle`. -/
def forestFiringClass : forestFiringComplex.allComplex.H1 :=
  (LinearMap.range forestFiringComplex.allComplex.boundaryToCycles).mkQ
    forestFiringCycle

/-- Difference of the genuine semantic parallel-edge coordinates. -/
def forestSemanticEdgeDifference :
    forestFiringComplex.all.C1 →ₗ[ZMod 2] ZMod 2 where
  toFun c :=
    forestFiringComplex.all.oneCochainCoordinates c forestSemanticTopEdge -
      forestFiringComplex.all.oneCochainCoordinates c forestSemanticBottomEdge
  map_add' left right := by simp; ring
  map_smul' scalar c := by simp [mul_sub]

/-- The semantic parallel-edge functional annihilates every actual degree-zero boundary. -/
theorem forestSemanticEdgeDifference_boundary_zero
    (c : forestFiringComplex.all.C0) :
    forestSemanticEdgeDifference (forestFiringComplex.all.d0 c) = 0 := by
  rw [show forestSemanticEdgeDifference (forestFiringComplex.all.d0 c) =
      forestFiringComplex.all.oneCochainCoordinates
          (forestFiringComplex.all.d0 c) forestSemanticTopEdge -
        forestFiringComplex.all.oneCochainCoordinates
          (forestFiringComplex.all.d0 c) forestSemanticBottomEdge by rfl]
  rw [forestFiringComplex.d0_coordinate, forestFiringComplex.d0_coordinate]
  change
    (forestFiringComplex.all.zeroCochainCoordinates c forestSemanticRightChart -
        forestFiringComplex.all.zeroCochainCoordinates c forestSemanticLeftChart) -
      (forestFiringComplex.all.zeroCochainCoordinates c forestSemanticRightChart -
        forestFiringComplex.all.zeroCochainCoordinates c forestSemanticLeftChart) = 0
  ring

/-- The semantic parallel-edge functional evaluates to one on the firing cycle. -/
theorem forestSemanticEdgeDifference_firingCycle :
    forestSemanticEdgeDifference forestFiringCycle.1 = 1 := by
  classical
  have hne : forestSemanticTopEdge ≠ forestSemanticBottomEdge := by
    intro h
    exact ForestFiringEdge.noConfusion (congrArg Sigma.fst h)
  simp [forestFiringCycle, forestFiringCochain, forestSemanticEdgeDifference,
    coordinateVector, hne]

/-- The forest firing class is nonzero by the boundary-annihilating edge difference. -/
theorem forestFiringClass_ne_zero : forestFiringClass ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range forestFiringComplex.allComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨c, hc⟩
  have hdifference := congrArg
    (fun z : LinearMap.ker forestFiringComplex.allComplex.d1 =>
      forestSemanticEdgeDifference z.1) hc
  change forestSemanticEdgeDifference (forestFiringComplex.all.d0 c) =
    forestSemanticEdgeDifference forestFiringCycle.1 at hdifference
  rw [forestSemanticEdgeDifference_boundary_zero,
    forestSemanticEdgeDifference_firingCycle] at hdifference
  exact zero_ne_one hdifference

/-- The structural-forest support corollary fires on an actual nonzero all-phase class. -/
theorem forestFiringSemanticImage_ne_zero :
    forestFiringComplex.standardSemanticH1Map forestFiring_conditionE
        forestFiringClass ≠ 0 :=
  forestStructuralPruning.forestNonzeroClass_mapsNonzero
    forestFiringClass forestFiringClass_ne_zero

/-- Finite evidence that the structural-forest regime does not force all-phase `H^1` to vanish. -/
theorem forestSupportRegime_nonvacuous :
    Nonempty (AtomIndexedCoefficientComplex.StructuralForestPruning
      forestFiringComplex forestFiring_conditionE) ∧
      ∃ x : forestFiringComplex.allComplex.H1,
        x ≠ 0 ∧
          forestFiringComplex.standardSemanticH1Map
            forestFiring_conditionE x ≠ 0 :=
  ⟨⟨forestStructuralPruning⟩,
    ⟨forestFiringClass, forestFiringClass_ne_zero,
      forestFiringSemanticImage_ne_zero⟩⟩

/--
The complete finite witness package for E3 anti-vacuity and E4.

The conjunction keeps the required portfolio faces independently inspectable:
actual Condition-E failure, actual structural `H^1` nonvanishing under Condition
E, a nonzero all-phase kernel class refuting unconditional semantic detection,
and nonvacuous classes with nonzero canonical semantic image both generally and
inside the structural-forest regime.
-/
theorem e4FiniteWitnessPackage :
    (¬ conditionEFailureComplex.ConditionE) ∧
      twoPhaseCycleComplex.ConditionE ∧
      ((∃ chart, family.Structural
          (twoPhaseCycleIndexing.chartPairAt chart)) ∧
        (∃ chart, family.Semantic
          (twoPhaseCycleIndexing.chartPairAt chart)) ∧
        (∃ edge, family.Structural
          (twoPhaseCycleIndexing.edgePairAt edge)) ∧
        (∃ edge, family.Semantic
          (twoPhaseCycleIndexing.edgePairAt edge))) ∧
      twoPhaseCycleComplex.structural0 ≠ ⊥ ∧
      twoPhaseCycleComplex.structural0 ≠ ⊤ ∧
      twoPhaseCycleComplex.structural1 ≠ ⊥ ∧
      twoPhaseCycleComplex.structural1 ≠ ⊤ ∧
      (∃ x : (twoPhaseCycleComplex.structuralComplex
        twoPhaseCycle_conditionE).H1, x ≠ 0) ∧
      (∃ x : twoPhaseCycleComplex.allComplex.H1,
        x ≠ 0 ∧
          twoPhaseCycleComplex.standardSemanticH1Map
            twoPhaseCycle_conditionE x = 0) ∧
      (∃ x : twoPhaseCycleComplex.allComplex.H1,
        x ≠ 0 ∧
          twoPhaseCycleComplex.standardSemanticH1Map
            twoPhaseCycle_conditionE x ≠ 0) ∧
      (Nonempty (AtomIndexedCoefficientComplex.StructuralForestPruning
          forestFiringComplex forestFiring_conditionE) ∧
        ∃ x : forestFiringComplex.allComplex.H1,
          x ≠ 0 ∧
            forestFiringComplex.standardSemanticH1Map
              forestFiring_conditionE x ≠ 0) := by
  refine ⟨conditionEFailure_not_conditionE,
    twoPhaseCycle_conditionE, twoPhaseCycle_basis_has_both_phases,
    twoPhaseCycle_structural0_ne_bot, twoPhaseCycle_structural0_ne_top,
    twoPhaseCycle_structural1_ne_bot, twoPhaseCycle_structural1_ne_top,
    ?_, unconditionalSupport_counterexample, ?_, forestSupportRegime_nonvacuous⟩
  · exact ⟨structuralH1Class, structuralH1Class_ne_zero⟩
  · exact ⟨firingClass, firingClass_ne_zero, firingSemanticImage_ne_zero⟩

end FiniteWitnesses

end AAT.AG.TwoPhase

#assert_standard_axioms_only AAT.AG.TwoPhase
