import Formal.Arch.Atomization
import Formal.Arch.Examples.StaticSemanticCounterexample

namespace Formal.Arch

namespace AtomicExamples

inductive Component where
  | core
  | adapter
  deriving DecidableEq, Repr

inductive Edge where
  | directAdapter
  deriving DecidableEq, Repr

inductive Diagram where
  | roundingSquare
  deriving DecidableEq, Repr

def badDirectAdapter : Edge -> Prop
  | .directAdapter => True

def supportDirectAdapter : Support Component Edge Diagram :=
  Support.edge Edge.directAdapter

theorem directAdapter_forbidden_minimal :
    MinimalSupport
      (SingleEdgePolicyViolation (C := Component) (D := Diagram)
        badDirectAdapter Edge.directAdapter)
      supportDirectAdapter := by
  exact singleEdgePolicyViolation_minimal badDirectAdapter trivial

def measuredForbiddenAtom : ArchitectureAtom Component Edge Diagram where
  kind := AtomKind.forbiddenStaticEdge
  axis := Axis.static
  polarity := Polarity.obstruction
  support := supportDirectAdapter
  status := MeasurementStatus.measuredNonzero
  evidenceBoundary := True
  nonConclusions := True

def exampleBoundary :
    AtomizationBoundary Unit Component Edge Diagram where
  requiredAxes := [Axis.static, Axis.coverage]
  selectedAxis := fun axis => axis = Axis.static ∨ axis = Axis.coverage
  atomKindAxis := fun
    | AtomKind.forbiddenStaticEdge => Axis.static
    | AtomKind.coverageGap _ => Axis.coverage
    | _ => Axis.static
  shapePredicate := fun _ kind support =>
    kind = AtomKind.forbiddenStaticEdge ∧
      SingleEdgePolicyViolation (C := Component) (D := Diagram)
        badDirectAdapter Edge.directAdapter support
  coverageGapPredicate := fun _ gap support =>
    gap = CoverageGapKind.missingEvidence ∧ support = Support.diagram Diagram.roundingSquare
  theoremBoundary := True
  coverageAssumptions := True
  exactnessAssumptions := True
  classificationPriorityBoundary := True
  nonConclusions := True

theorem measuredForbiddenAtom_valid :
    ValidAtom exampleBoundary () measuredForbiddenAtom := by
  constructor
  · rfl
  · constructor
    · exact ⟨rfl, directAdapter_forbidden_minimal.1⟩
    · intro T hProper hShape
      exact directAdapter_forbidden_minimal.2 T hProper hShape.2

def exampleCertificate :
    AtomizationCertificate Unit Component Edge Diagram exampleBoundary () where
  atoms := [measuredForbiddenAtom]
  allValid := by
    intro a hMem
    simp [measuredForbiddenAtom] at hMem
    cases hMem
    exact measuredForbiddenAtom_valid
  rejectedCandidateBoundary := True
  coverageGapBoundary := True
  nonConclusions := True

def exampleAtomizer : Atomizer Unit Component Edge Diagram exampleBoundary where
  atomize := fun X => by
    cases X
    exact exampleCertificate
  sound := by
    intro X a hMem
    cases X
    exact exampleCertificate.allValid a hMem
  completenessBoundary := True
  nonConclusions := True

theorem example_atomize_sound :
    ∀ a, a ∈ (exampleAtomizer.atomize ()).atoms ->
      ValidAtom exampleBoundary () a := by
  intro a hMem
  exact atomize_sound exampleAtomizer hMem

theorem example_atomize_sound_measuredForbiddenAtom :
    ValidAtom exampleBoundary () measuredForbiddenAtom := by
  exact example_atomize_sound measuredForbiddenAtom (by simp [exampleAtomizer, exampleCertificate])

def staticSignatureWithForbidden : AtomSignature where
  valuation := {
    count := fun axis =>
      match axis with
      | Axis.static => 1
      | _ => 0
    status := fun axis =>
      match axis with
      | Axis.static => MeasurementStatus.measuredNonzero
      | Axis.coverage => MeasurementStatus.unmeasured
      | _ => MeasurementStatus.measuredZero
    evidenceBoundary := fun _ => True
    nonConclusions := True
  }
  theoremBoundary := True
  coverageBoundary := True
  exactnessBoundary := True
  atomCoverCompleteness := True
  nonConclusions := True

def staticSignatureZero : AtomSignature where
  valuation := {
    count := fun _ => 0
    status := fun
      | Axis.coverage => MeasurementStatus.unmeasured
      | _ => MeasurementStatus.measuredZero
    evidenceBoundary := fun _ => True
    nonConclusions := True
  }
  theoremBoundary := True
  coverageBoundary := True
  exactnessBoundary := True
  atomCoverCompleteness := True
  nonConclusions := True

theorem staticSignatureZero_no_static_bad_atom :
    ¬ HasBadAtomOn staticSignatureZero Axis.static := by
  exact no_hasBadAtomOn_of_signatureZero ⟨rfl, rfl⟩

theorem coverage_unmeasured_not_signatureZero :
    ¬ SignatureZero staticSignatureZero Axis.coverage := by
  intro hZero
  cases hZero.1

def exampleStaticAtomPackage :
    StaticAtomV0Package Component Edge Diagram where
  forbiddenEdgeBad := badDirectAdapter
  boundaryLeakBad := badDirectAdapter
  abstractionLeakBad := badDirectAdapter
  simpleCycleBad := fun _ => False
  rankViolationBad := fun _ => False
  coverageGapBad := fun S => S = Support.diagram Diagram.roundingSquare
  forbiddenEdgeMinimal := by
    intro e hBad
    cases e
    exact singleEdgePolicyViolation_minimal badDirectAdapter hBad
  boundaryLeakMinimal := by
    intro e hBad
    cases e
    exact singleEdgePolicyViolation_minimal badDirectAdapter hBad
  abstractionLeakMinimal := by
    intro e hBad
    cases e
    exact singleEdgePolicyViolation_minimal badDirectAdapter hBad
  simpleCycleMinimal := by
    intro S h
    cases h
  rankViolationMinimal := by
    intro S h
    cases h
  coverageGapMinimal := by
    intro S h
    subst h
    constructor
    · rfl
    · intro T hProper hEq
      subst hEq
      exact hProper.2 (SupportSubset.refl _)
  staticZeroNonConclusion := True
  noMatroidOrUniqueFactorizationConclusion := True

theorem example_forbiddenStaticEdge_minimal :
    MinimalSupport
      (SingleEdgePolicyViolation (C := Component) (D := Diagram)
        exampleStaticAtomPackage.forbiddenEdgeBad Edge.directAdapter)
      (Support.edge Edge.directAdapter) :=
  StaticAtomV0Package.forbiddenStaticEdge_minimal
    exampleStaticAtomPackage trivial

def exampleSolidCleanPackage :
    SolidCleanAtomPackage Component Edge Diagram where
  portAtoms := []
  adapterAtoms := []
  pureRuleAtoms := []
  coordinatorAtoms := []
  fatInterfaceAtoms := []
  lspMismatchAtoms := []
  projectionFailureAtoms := []
  projectionSoundAtomTheorem := True
  lspMismatchAtomTheorem := True
  dipLocalSoundnessTheorem := True
  solidNotGlobalDecomposability := True
  nonConclusions := True

theorem example_solid_not_global_decomposability :
    SolidCleanAtomPackage.solid_not_global_decomposability
      exampleSolidCleanPackage := by
  trivial

def exampleSemanticRuntimePackage :
    SemanticRuntimeAtomPackage Component Edge Diagram where
  runtimeEdgeAtoms := []
  guardAtoms := []
  runtimeExposureAtoms := []
  nonCommutingSquareAtoms := []
  effectLeakAtoms := []
  replayViolationAtoms := []
  compensationGapAtoms := []
  staticZeroNotSemanticZero :=
    StaticFlatWithin StaticSemanticCounterexample.canonicalFlatnessModel
        StaticSemanticCounterexample.repairedUniverse ∧
      ¬ ArchitectureFlat StaticSemanticCounterexample.canonicalFlatnessModel
  runtimeProtectionLocalTheorem := True
  nonCommutingSquareWitnessTheorem := True
  noGlobalOperationalSafetyConclusion := True

theorem example_static_zero_not_semantic_zero :
    SemanticRuntimeAtomPackage.static_zero_not_semantic_zero
      exampleSemanticRuntimePackage := by
  exact StaticSemanticCounterexample.staticFlat_not_architectureFlat

def exampleSafeRegion : AtomSafeRegion Component Edge Diagram where
  forbidden := fun kind => kind = AtomKind.forbiddenStaticEdge
  atoms := []
  safe := by
    intro a hMem
    cases hMem
  boundary := True
  nonConclusions := True

def exampleAtomicSFTBridgePackage :
    AtomicSFTBridgePackage Unit Unit Component Edge Diagram where
  fieldAtoms := fun _ => [measuredForbiddenAtom]
  atomDelta := fun _ _ _ => {
    created := []
    removed := []
    preserved := [measuredForbiddenAtom]
    transformed := []
    hidden := []
    exposed := []
    unknown := []
    forecastBoundary := True
    nonConclusions := True
  }
  atomTrace := fun states => {
    states := states
    deltas := []
    wellTyped := True
    boundary := True
    nonConclusions := True
  }
  safeRegion := exampleSafeRegion
  fieldAtomSound := True
  atomTraceSound := True
  atomSafeSupport := True
  atomConeNarrowingBoundary := True
  fieldUpdateRecordsUnexpectedAtomBoundary := True
  noGlobalFutureSafetyConclusion := True
  noForecastCorrectnessConclusion := True

theorem example_atomicSFT_records_no_global_future_safety :
    AtomicSFTBridgePackage.records_no_global_future_safety
      exampleAtomicSFTBridgePackage := by
  trivial

end AtomicExamples

end Formal.Arch
