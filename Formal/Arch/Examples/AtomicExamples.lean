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

inductive Responsibility where
  | apiResponsibility
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

def forbiddenEdgeLawfulnessBridge :
    AtomLawfulnessBridge forbiddenEdgeLaw selectedForbiddenEdgeUniverse.selected where
  badWitnessComplete := by
    intro M hSel hBad
    rcases selectedForbiddenEdgeUniverse.contains_minimal_bad hSel hBad with
      ⟨Ckt, hSelCkt, hCircuit, _hSub⟩
    exact ⟨Ckt, hSelCkt, hCircuit⟩
  circuitBad := by
    intro M _hSel hCircuit
    exact obstructionCircuit_bad hCircuit
  coverageBoundary := True
  exactnessBoundary := True
  nonConclusions := True

theorem forbiddenEdge_lawful_iff_no_required_circuit :
    LawfulWithinAtomConfiguration
        forbiddenEdgeLaw selectedForbiddenEdgeUniverse.selected ↔
      NoRequiredObstructionCircuit
        forbiddenEdgeLaw selectedForbiddenEdgeUniverse.selected := by
  exact forbiddenEdgeLawfulnessBridge.lawful_iff_no_obstructionCircuit

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

def promotedComponentObservation : ObservedAtom Component Edge Diagram where
  atom := componentAtom
  observationStatus := ObservationStatus.observed
  measurementStatus := MeasurementStatus.measuredZero
  evidenceRef := "archmap:promoted:component-api"
  sourceBoundary := True
  nonConclusions := True

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
  observed := fun observed =>
    observed = promotedComponentObservation ∨
      observed = rejectedPrimitiveCandidate
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

def exampleAtomPresentationAATPackage :
    AtomPresentationAATPackage
      exampleAtomPresentation
      forbiddenEdgeLaw
      selectedForbiddenEdgeUniverse.selected
      exampleAtomSignature
      staticRequiredAxis where
  selectedAtoms := fun atom => atom = componentAtom
  selectedGaps := fun gap => gap = runtimeObservationGap
  selectedAtomsSound := by
    intro atom hAtom
    refine ⟨promotedComponentObservation, ?_, ?_, ?_⟩
    · exact Or.inl rfl
    · exact hAtom.symm
    · trivial
  selectedGapsSound := by
    intro gap hGap
    exact hGap
  lawfulnessBridge := forbiddenEdgeLawfulnessBridge
  vanishingBridge := exampleAtomVanishingBridge
  promotionBoundary := trivial
  validationBoundary := trivial
  rawCandidateBoundary := trivial
  nonConclusions := trivial

theorem exampleAtomPresentationAATPackage_reads_selected_atom :
    ∃ observed,
      exampleAtomPresentation.observed observed ∧
      observed.atom = componentAtom ∧
      observed.measurementStatus.SupportsMeasurement := by
  exact
    exampleAtomPresentationAATPackage.selectedAtom_from_presentation rfl

theorem exampleAtomPresentationAATPackage_records_raw_guardrail :
    ¬ AtomPresentationAATPackage.RawCandidateTheoremClaim
      exampleAtomPresentationAATPackage := by
  exact exampleAtomPresentationAATPackage.noRawCandidateTheoremClaim_recorded

def noBadAtomLaw : DesignLaw Component Edge Diagram where
  Bad := fun _ => False
  selectedBoundary := True
  nonConclusions := True

def allSelectedMolecules (_molecule : AtomMolecule Component Edge Diagram) : Prop :=
  True

def noEdgeGraph : ArchGraph Component where
  edge := fun _ _ => False

def identityProjection : InterfaceProjection Component Component where
  expose := id

def observationToUnit : Observation Component Unit where
  observe := fun _ => ()

theorem noBadAtomLaw_lawful :
    LawfulWithinAtomConfiguration noBadAtomLaw allSelectedMolecules := by
  intro M _hRequired hBad
  exact hBad

def noEdgeLayeringAtomArrangement :
    LayeringAtomArrangementLaw noEdgeGraph noBadAtomLaw allSelectedMolecules where
  lawfulnessImpliesStrictLayered := by
    intro _hLawful
    exact ⟨fun _ => 0, by
      intro c d hEdge
      exact False.elim hEdge⟩
  obstructionCircuitBoundary := True
  nonConclusions := True

theorem noEdgeLayeringAtomArrangement_strictLayered :
    StrictLayered noEdgeGraph :=
  noEdgeLayeringAtomArrangement.strictLayered_of_lawful noBadAtomLaw_lawful

theorem noEdgeLayeringAtomArrangement_acyclic :
    Acyclic noEdgeGraph :=
  noEdgeLayeringAtomArrangement.acyclic_of_lawful noBadAtomLaw_lawful

def identityProjectionAtomArrangement :
    ProjectionAtomArrangementLaw
      noEdgeGraph identityProjection noEdgeGraph noBadAtomLaw allSelectedMolecules where
  lawfulnessImpliesProjectionSound := by
    intro _hLawful c d hEdge
    exact False.elim hEdge
  projectionFailureExposesBadMolecule := by
    intro edge hFailure
    exact False.elim hFailure.1
  obstructionCircuitBoundary := True
  nonConclusions := True

theorem identityProjectionAtomArrangement_projectionSound :
    ProjectionSound noEdgeGraph identityProjection noEdgeGraph :=
  identityProjectionAtomArrangement.projectionSound_of_lawful noBadAtomLaw_lawful

theorem identityProjectionAtomArrangement_noProjectionObstruction :
    NoProjectionObstruction noEdgeGraph identityProjection noEdgeGraph :=
  identityProjectionAtomArrangement.noProjectionObstruction_of_lawful
    noBadAtomLaw_lawful

def unitObservationAtomArrangement :
    ObservationAtomArrangementLaw
      observationToUnit Component.api Component.database
      noBadAtomLaw allSelectedMolecules where
  lawfulnessImpliesObservationEquivalence := by
    intro _hLawful
    rfl
  observationBoundary := True
  nonConclusions := True

theorem unitObservationAtomArrangement_equivalent :
    ObservationallyEquivalent
      observationToUnit Component.api Component.database :=
  unitObservationAtomArrangement.observationallyEquivalent_of_lawful
    noBadAtomLaw_lawful

def apiResponsibilityBoundary :
    ResponsibilityBoundary Component Responsibility where
  owns := fun _ role => role = Responsibility.apiResponsibility

def apiResponsibilityRole :
    ResponsibilityRole
      (C := Component) (E := Edge) (D := Diagram) Responsibility where
  role := Responsibility.apiResponsibility
  molecule := componentMolecule
  carriedBy := fun component => component = Component.api
  roleBoundary := True
  nonConclusions := True

theorem apiResponsibilityRole_coherent :
    ResponsibilityMoleculeCoherent
      apiResponsibilityBoundary apiResponsibilityRole := by
  intro component _hCarried
  rfl

theorem selectedApiResponsibility_coherent :
    SRPResponsibilityMoleculeCoherent
      apiResponsibilityBoundary
      (fun role => role = apiResponsibilityRole) := by
  intro role hRole
  rw [hRole]
  exact apiResponsibilityRole_coherent

def apiSRPAtomArrangement :
    SRPAtomArrangementLaw
      noEdgeGraph apiResponsibilityBoundary noBadAtomLaw allSelectedMolecules where
  lawfulnessImpliesBoundaryTotal := by
    intro _hLawful component
    exact ⟨Responsibility.apiResponsibility, rfl⟩
  lawfulnessImpliesBoundaryFunctional := by
    intro _hLawful component r₁ r₂ h₁ h₂
    rw [h₁, h₂]
  lawfulnessImpliesLocalCohesion := by
    intro _hLawful _a _b _r₁ _r₂ hEdge _h₁ _h₂
    exact False.elim hEdge
  responsibilityMoleculeBoundary := True
  nonConclusions := True

theorem apiSRPAtomArrangement_boundaryFunctional :
    apiResponsibilityBoundary.Functional :=
  apiSRPAtomArrangement.boundaryFunctional_of_lawful noBadAtomLaw_lawful

theorem apiSRPAtomArrangement_localCohesion :
    apiResponsibilityBoundary.EdgeCohesive noEdgeGraph :=
  apiSRPAtomArrangement.localCohesion_of_lawful noBadAtomLaw_lawful

def unitOperationSupport : OperationSupport Unit Unit where
  supports := fun _ _ => True
  coverageAssumptions := True
  supportBoundary := True
  nonConclusions := True

def unitStepRelation : StepRelation Unit Unit where
  step := fun _ _ _ => True
  coverageAssumptions := True
  theoremBoundary := True
  nonConclusions := True

def emptyCircuitDelta : CircuitDelta noBadAtomLaw where
  created := fun _ => False
  removed := fun _ => False
  preserved := fun _ => False
  transformed := fun _ _ => False
  createdCircuit := by
    intro molecule hCreated
    exact False.elim hCreated
  removedCircuit := by
    intro molecule hRemoved
    exact False.elim hRemoved
  preservedCircuit := by
    intro molecule hPreserved
    exact False.elim hPreserved
  evidenceBoundary := True
  nonConclusions := True

def emptyCircuitTrace : CircuitTrace noBadAtomLaw where
  step := fun _ delta => delta = emptyCircuitDelta
  finiteBoundary := True
  lawRelativeBoundary := True
  nonConclusions := True

def exampleAtomTraceForecastBoundary :
    AtomTraceForecastBoundary
      unitOperationSupport
      unitStepRelation
      ()
      0
      ()
      (ArchitecturePath.nil ())
      noBadAtomLaw where
  coneMember := ForecastCone.nil_mem ()
  atomTrace :=
    { step := fun _ _ => False
      finiteBoundary := True
      orderingBoundary := True
      nonConclusions := True }
  circuitTrace := emptyCircuitTrace
  atomTraceBoundary := True
  circuitTraceBoundary := True
  governedTraceBoundary := True
  typedBoundaryFailure := False
  governed_or_typedBoundaryFailure := Or.inl trivial
  nonConclusions := True

theorem exampleAtomTraceForecastBoundary_length_le_horizon :
    ArchitecturePath.length
      (@ArchitecturePath.nil Unit
        (SupportedFieldStep unitOperationSupport unitStepRelation) ()) <= 0 :=
  exampleAtomTraceForecastBoundary.length_le_horizon

theorem exampleAtomTraceForecastBoundary_governed_or_typedFailure :
    exampleAtomTraceForecastBoundary.governedTraceBoundary ∨
      exampleAtomTraceForecastBoundary.typedBoundaryFailure :=
  exampleAtomTraceForecastBoundary.governed_or_typedBoundaryFailure

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
