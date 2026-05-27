import Formal.Arch.Atomization

namespace Formal.Arch.AtomicExamples

inductive Component where
  | api
  | database
  deriving DecidableEq, Repr

inductive Edge where
  | apiToDatabase
  deriving DecidableEq, Repr

inductive Diagram where
  | writePath
  deriving DecidableEq, Repr

def componentAtom : ArchitectureAtom Component Edge Diagram where
  kind := AtomKind.component
  axis := Axis.static
  support := Support.component Edge Diagram Component.api
  predicate := "component api exists"
  evidenceBoundary := True
  nonConclusions := True

def relationAtom : ArchitectureAtom Component Edge Diagram where
  kind := AtomKind.relation
  axis := Axis.static
  support := Support.edge Component Diagram Edge.apiToDatabase
  predicate := "api depends on database"
  evidenceBoundary := True
  nonConclusions := True

def semanticContractAtom : ArchitectureAtom Component Edge Diagram where
  kind := AtomKind.semantic
  axis := Axis.semantic
  support := Support.diagram Component Edge Diagram.writePath
  predicate := "write path satisfies selected semantic contract"
  evidenceBoundary := True
  nonConclusions := True

theorem primitiveComponentAtom_primitive :
    PrimitiveArchitectureAtom componentAtom := by
  exact primitiveArchitectureAtom_constructive componentAtom

theorem primitiveRelationAtom_primitive :
    PrimitiveArchitectureAtom relationAtom := by
  exact primitiveArchitectureAtom_constructive relationAtom

theorem semanticContractAtom_allowedBy_current :
    semanticContractAtom.AllowedBy AtomGrammarExtensionPolicy.current := by
  exact ArchitectureAtom.allowedBy_current semanticContractAtom

theorem semanticContractAtom_primitive_of_policy :
    PrimitiveArchitectureAtom semanticContractAtom := by
  exact ArchitectureAtom.primitive_of_allowedBy
    semanticContractAtom_allowedBy_current

def selectedAtomUniverse : SelectedAtomUniverse Component Edge Diagram where
  selectedAtom := fun atom =>
    atom = componentAtom ∨ atom = relationAtom ∨ atom = semanticContractAtom
  finiteBoundary := True
  coverageBoundary := True
  exactnessBoundary := True
  nonConclusions := True

def componentMolecule : AtomMolecule Component Edge Diagram where
  atoms := fun atom => atom = componentAtom
  finiteBoundary := True
  nonConclusions := True

def forbiddenEdgeMolecule : AtomMolecule Component Edge Diagram where
  atoms := fun atom => atom = relationAtom
  finiteBoundary := True
  nonConclusions := True

def componentMoleculeWitness :
    FiniteAtomMoleculeWitness selectedAtomUniverse componentMolecule where
  supportedBy := by
    intro atom hAtom
    exact Or.inl hAtom
  moleculeFiniteBoundary := componentMolecule.finiteBoundary
  universeFiniteBoundary := selectedAtomUniverse.finiteBoundary
  nonConclusions := True

def forbiddenEdgeMoleculeWitness :
    FiniteAtomMoleculeWitness selectedAtomUniverse forbiddenEdgeMolecule where
  supportedBy := by
    intro atom hAtom
    exact Or.inr (Or.inl hAtom)
  moleculeFiniteBoundary := forbiddenEdgeMolecule.finiteBoundary
  universeFiniteBoundary := selectedAtomUniverse.finiteBoundary
  nonConclusions := True

def forbiddenEdgeLaw : DesignLaw Component Edge Diagram where
  Bad := fun molecule => molecule.atoms relationAtom
  selectedBoundary := True
  nonConclusions := True

theorem singletonForbiddenMolecule_obstruction :
    ObstructionCircuit forbiddenEdgeLaw forbiddenEdgeMolecule := by
  constructor
  · rfl
  · intro N hProper hBad
    apply hProper.2
    intro atom hAtom
    have hEq : atom = relationAtom := by
      simpa [forbiddenEdgeMolecule] using hAtom
    rw [hEq]
    exact hBad

def selectedForbiddenEdgeUniverse :
    FiniteAtomMoleculeUniverse forbiddenEdgeLaw where
  selected := fun molecule =>
    molecule = forbiddenEdgeMolecule ∨ molecule = componentMolecule
  minimalOf := by
    intro M hSel hBad
    exact
      ⟨forbiddenEdgeMolecule,
        ⟨Or.inl rfl, singletonForbiddenMolecule_obstruction, by
          intro atom hAtom
          have hEq : atom = relationAtom := by
            simpa [forbiddenEdgeMolecule] using hAtom
          rw [hEq]
          exact hBad⟩⟩
  coverageBoundary := True
  exactnessBoundary := True
  nonConclusions := True

theorem selectedForbiddenEdgeUniverse_contains_minimal_bad
    {M : AtomMolecule Component Edge Diagram}
    (hSel : selectedForbiddenEdgeUniverse.selected M)
    (hBad : forbiddenEdgeLaw.Bad M) :
    ∃ N,
      selectedForbiddenEdgeUniverse.selected N ∧
      ObstructionCircuit forbiddenEdgeLaw N ∧
      AtomMoleculeSubset N M := by
  exact selectedForbiddenEdgeUniverse.contains_minimal_bad hSel hBad

def rejectedPrimitiveCandidate : ObservedAtom Component Edge Diagram where
  atom := relationAtom
  observationStatus := ObservationStatus.rejectedCandidate
  measurementStatus := MeasurementStatus.rejectedCandidate
  evidenceRef := "archmap:candidate:rejected"
  sourceBoundary := True
  nonConclusions := True

theorem rejectedPrimitiveCandidate_not_measured :
    ¬ rejectedPrimitiveCandidate.measurementStatus.SupportsMeasurement := by
  exact observedAtom_rejected_not_measured rejectedPrimitiveCandidate rfl

def uncertainPrimitiveCandidate : ObservedAtom Component Edge Diagram where
  atom := relationAtom
  observationStatus := ObservationStatus.uncertainCandidate
  measurementStatus := MeasurementStatus.uncertainCandidate
  evidenceRef := "archmap:candidate:uncertain"
  sourceBoundary := True
  nonConclusions := True

theorem uncertainPrimitiveCandidate_not_measured :
    ¬ uncertainPrimitiveCandidate.measurementStatus.SupportsMeasurement := by
  exact observedAtom_uncertain_not_measured uncertainPrimitiveCandidate rfl

def runtimeObservationGap : ObservationGap Component Edge Diagram where
  expectedKind := AtomKind.runtimeInteraction
  expectedAxis := Axis.runtime
  support := Support.diagram Component Edge Diagram.writePath
  measurementStatus := MeasurementStatus.dynamicBlindSpot
  notMeasuredZero := by
    intro h
    cases h
  sourceBoundary := True
  nonConclusions := True

theorem runtimeObservationGap_not_measuredZero :
    runtimeObservationGap.measurementStatus ≠ MeasurementStatus.measuredZero := by
  exact observationGap_not_measuredZero runtimeObservationGap

def exampleAtomPresentation : AtomPresentation Component Edge Diagram where
  observed := fun observed => observed = rejectedPrimitiveCandidate
  gaps := fun gap => gap = runtimeObservationGap
  promotionBoundary := True
  validationBoundary := True
  rawCandidateBoundary := True
  nonConclusions := True

theorem exampleAtomPresentation_recordsPromotionBoundary :
    exampleAtomPresentation.promotionBoundary := by
  trivial

def exampleAtomSignature : AtomSignature Component Edge Diagram where
  valuation := fun _ => MeasurementStatus.measuredZero
  badOn := fun _ => False
  measuredBoundary := True
  nonConclusions := True

def staticRequiredAxis (axis : Axis) : Prop :=
  axis = Axis.static

def examplePresentedAtomSignature :
    PresentedAtomSignature Component Edge Diagram where
  presentation := exampleAtomPresentation
  signature := exampleAtomSignature
  valuationBoundary := True
  nonConclusions := True

theorem staticSignatureZero_no_static_bad_atom :
    SignatureZero exampleAtomSignature := by
  intro atom hBad
  exact hBad.1

def exampleAtomVanishingBridge :
    AtomVanishingBridge exampleAtomSignature staticRequiredAxis :=
  AtomVanishingBridge.ofSignatureZero staticSignatureZero_no_static_bad_atom

theorem exampleAtomVanishingBridge_no_required_bad_atom
    (atom : ArchitectureAtom Component Edge Diagram)
    (hRequired : RequiredAtomAxis staticRequiredAxis atom) :
    ¬ HasBadAtomOn exampleAtomSignature atom := by
  exact exampleAtomVanishingBridge.no_hasBadAtomOn_of_requiredAxis atom hRequired

def exampleSoftwareField :
    SoftwareField Unit Component Edge Unit Unit Unit where
  state := ()
  architectureProjection :=
    { static :=
        { edge := fun _ _ => False }
      runtime :=
        { edge := fun _ _ => False }
      projection :=
        { expose := fun _ => Edge.apiToDatabase }
      abstractStatic :=
        { edge := fun _ _ => False }
      staticObservation :=
        { observe := fun _ => () }
      boundaryAllowed := fun _ _ => True
      abstractionAllowed := fun _ _ => True
      runtimeAllowed := fun _ _ => True
      semantic :=
        { eval := fun _ => () }
      requiredSemantic := fun _ => False
      measuredSemantic := [] }
  observedSignatureRecord := True
  historyBoundary := True
  operationSupportBoundary := True
  operationPolicyBoundary := True
  constraintEnvironmentBoundary := True
  observationModelBoundary := True
  governanceInterventionBoundary := True
  exogenousArtifactInputBoundary := True
  fieldBoundary := True
  nonConclusions := True

def exampleValidatedFieldAtomPresentation :
    ValidatedFieldAtomPresentation Unit Component Edge Unit Unit Unit Diagram where
  field := exampleSoftwareField
  presentation := exampleAtomPresentation
  rawCandidateExcluded := True
  validationBoundary := True
  nonConclusions := True

theorem example_validatedPresentation_excludes_raw_candidates :
    exampleValidatedFieldAtomPresentation.rawCandidateExcluded := by
  trivial

def exampleAtomDelta : AtomDelta Component Edge Diagram where
  created := fun _ => False
  removed := fun _ => False
  preserved := fun atom => atom = componentAtom
  transformed := fun _ _ => False
  hidden := fun gap => gap = runtimeObservationGap
  exposed := fun observed => observed = rejectedPrimitiveCandidate
  unknown := fun _ => False
  evidenceBoundary := True
  nonConclusions := True

def examplePresentedAtomDelta : PresentedAtomDelta Component Edge Diagram where
  before := exampleAtomPresentation
  after := exampleAtomPresentation
  delta := exampleAtomDelta
  validationBoundary := True
  nonConclusions := True

def exampleAtomTrace : AtomTrace Component Edge Diagram where
  step := fun n delta => n = 0 ∧ delta = examplePresentedAtomDelta
  finiteBoundary := True
  orderingBoundary := True
  nonConclusions := True

def exampleAtomicSFTPresentationBridgePackage :
    AtomicSFTPresentationBridgePackage Unit Component Edge Unit Unit Unit Diagram where
  validatedPresentation := exampleValidatedFieldAtomPresentation
  fieldAtoms := FieldAtomsFromPresentation
    exampleValidatedFieldAtomPresentation.field
    exampleValidatedFieldAtomPresentation.presentation
  fieldAtomsSound := by
    intro atom hAtom
    exact hAtom
  atomTrace := exampleAtomTrace
  rawCandidateExcluded := True
  forecastCorrectnessNonConclusion := True
  globalFutureSafetyNonConclusion := True
  nonConclusions := True

theorem example_atomicSFTPresentation_excludes_raw_candidates :
    exampleAtomicSFTPresentationBridgePackage.rawCandidateExcluded := by
  trivial

theorem example_atomicSFTPresentation_records_no_forecast_correctness :
    exampleAtomicSFTPresentationBridgePackage.forecastCorrectnessNonConclusion := by
  trivial

end Formal.Arch.AtomicExamples
