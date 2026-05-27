import Formal.Arch.AtomCoreAAT
import Formal.Arch.Evolution.SFTEnvelope

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

inductive Pattern where
  | repositoryRole
  | simpleLayering
  deriving DecidableEq, Repr

def componentAtom : ArchitectureAtom Component Edge Diagram where
  kind := AtomKind.existence
  axis := Axis.static
  support := Support.component Edge Diagram Component.api
  typedPredicate := AtomPredicate.component Component.api
  typedPredicateKindAligned := rfl
  typedPredicateAxisAligned := rfl
  predicate := "component api exists"
  singleFact := True
  singleFactEvidence := trivial
  predicatePreservation := True
  predicatePreservationEvidence := trivial
  boundaryIndependent := True
  boundaryIndependentEvidence := trivial
  lawIndependent := True
  lawIndependentEvidence := trivial
  evidenceBoundary := True
  nonConclusions := True

def relationAtom : ArchitectureAtom Component Edge Diagram where
  kind := AtomKind.relation
  axis := Axis.static
  support := Support.edge Component Diagram Edge.apiToDatabase
  typedPredicate := AtomPredicate.relation Edge.apiToDatabase
  typedPredicateKindAligned := rfl
  typedPredicateAxisAligned := rfl
  predicate := "api depends on database"
  singleFact := True
  singleFactEvidence := trivial
  predicatePreservation := True
  predicatePreservationEvidence := trivial
  boundaryIndependent := True
  boundaryIndependentEvidence := trivial
  lawIndependent := True
  lawIndependentEvidence := trivial
  evidenceBoundary := True
  nonConclusions := True

def contractSpecificationAtom : ArchitectureAtom Component Edge Diagram where
  kind := AtomKind.contractSpecification
  axis := Axis.specification
  support := Support.diagram Component Edge Diagram.writePath
  typedPredicate :=
    AtomPredicate.contractSpecification Diagram.writePath "selected contract"
  typedPredicateKindAligned := rfl
  typedPredicateAxisAligned := rfl
  predicate := "write path satisfies selected contract"
  singleFact := True
  singleFactEvidence := trivial
  predicatePreservation := True
  predicatePreservationEvidence := trivial
  boundaryIndependent := True
  boundaryIndependentEvidence := trivial
  lawIndependent := True
  lawIndependentEvidence := trivial
  evidenceBoundary := True
  nonConclusions := True

def semanticInterpretationAtom : ArchitectureAtom Component Edge Diagram where
  kind := AtomKind.semanticInterpretation
  axis := Axis.semantic
  support := Support.diagram Component Edge Diagram.writePath
  typedPredicate :=
    AtomPredicate.semanticInterpretation Diagram.writePath "account registration"
  typedPredicateKindAligned := rfl
  typedPredicateAxisAligned := rfl
  predicate := "write path means account registration"
  singleFact := True
  singleFactEvidence := trivial
  predicatePreservation := True
  predicatePreservationEvidence := trivial
  boundaryIndependent := True
  boundaryIndependentEvidence := trivial
  lawIndependent := True
  lawIndependentEvidence := trivial
  evidenceBoundary := True
  nonConclusions := True

theorem primitiveComponentAtom_primitive :
    PrimitiveArchitectureAtom componentAtom := by
  exact primitiveArchitectureAtom_constructive componentAtom

theorem primitiveRelationAtom_primitive :
    PrimitiveArchitectureAtom relationAtom := by
  exact primitiveArchitectureAtom_constructive relationAtom

theorem contractSpecificationAtom_allowedBy_current :
    contractSpecificationAtom.AllowedBy AtomGrammarExtensionPolicy.current := by
  exact ArchitectureAtom.allowedBy_current contractSpecificationAtom

theorem contractSpecificationAtom_primitive_of_policy :
    PrimitiveArchitectureAtom contractSpecificationAtom := by
  exact ArchitectureAtom.primitive_of_allowedBy
    contractSpecificationAtom_allowedBy_current

theorem semanticInterpretationAtom_allowedBy_current :
    semanticInterpretationAtom.AllowedBy AtomGrammarExtensionPolicy.current := by
  exact ArchitectureAtom.allowedBy_current semanticInterpretationAtom

theorem semanticInterpretationAtom_primitive_of_policy :
    PrimitiveArchitectureAtom semanticInterpretationAtom := by
  exact ArchitectureAtom.primitive_of_allowedBy
    semanticInterpretationAtom_allowedBy_current

theorem semanticInterpretationAtom_has_meaning :
    semanticInterpretationAtom.HasSemanticMeaning
      "account registration" := by
  exact ⟨Diagram.writePath, rfl⟩

theorem semanticInterpretationAtom_is_semantic_from_meaning :
    semanticInterpretationAtom.IsSemanticInterpretation := by
  exact ArchitectureAtom.isSemanticInterpretation_of_hasSemanticMeaning
    semanticInterpretationAtom_has_meaning

theorem semanticInterpretationAtom_axis_from_meaning :
    semanticInterpretationAtom.axis = Axis.semantic := by
  exact ArchitectureAtom.semantic_axis_of_hasSemanticMeaning
    semanticInterpretationAtom_has_meaning

theorem componentAtom_ontology_primitive :
    PrimitiveOntologicalAtom componentAtom.ontology := by
  exact ArchitectureAtom.ontology_primitive componentAtom

theorem componentAtom_ontology_boundary_independent :
    componentAtom.ontology.boundaryIndependent := by
  exact ArchitectureAtom.ontology_independent_of_observation_boundary
    componentAtom

theorem componentAtom_observation_boundary_separated :
    componentAtom.observationBoundary.evidenceBoundary := by
  trivial

def selectedAtomUniverse : SelectedAtomUniverse Component Edge Diagram where
  selectedAtom := fun atom =>
    atom = componentAtom ∨
      atom = relationAtom ∨
      atom = contractSpecificationAtom ∨
      atom = semanticInterpretationAtom
  finiteBoundary := True
  coverageBoundary := True
  exactnessBoundary := True
  nonConclusions := True

def componentMolecule : AtomMolecule Component Edge Diagram where
  atoms := fun atom => atom = componentAtom
  finiteBoundary := True
  nonConclusions := True

def semanticMolecule : AtomMolecule Component Edge Diagram where
  atoms := fun atom => atom = semanticInterpretationAtom
  finiteBoundary := True
  nonConclusions := True

theorem semanticMolecule_all_semantic :
    SemanticAtomMolecule semanticMolecule := by
  intro atom hAtom
  rw [hAtom]
  rfl

def repositoryRoleAssignment :
    RoleAssignment Component Edge Diagram Pattern where
  molecule := componentMolecule
  role := Pattern.repositoryRole
  assigned := True
  roleBoundary := True
  nonConclusions := True

def simpleLayeringPattern :
    PatternInterpretation Component Edge Diagram Pattern where
  molecule := componentMolecule
  pattern := Pattern.simpleLayering
  interprets := True
  interpretationBoundary := True
  nonConclusions := True

theorem repositoryRoleAssignment_reads_molecule :
    repositoryRoleAssignment.toMolecule = componentMolecule := by
  rfl

theorem simpleLayeringPattern_reads_molecule :
    simpleLayeringPattern.toMolecule = componentMolecule := by
  rfl

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

def semanticMoleculeWitness :
    FiniteAtomMoleculeWitness selectedAtomUniverse semanticMolecule where
  supportedBy := by
    intro atom hAtom
    exact Or.inr (Or.inr (Or.inr hAtom))
  moleculeFiniteBoundary := semanticMolecule.finiteBoundary
  universeFiniteBoundary := selectedAtomUniverse.finiteBoundary
  nonConclusions := True

def semanticAtomMoleculeWitness :
    SemanticAtomMoleculeWitness selectedAtomUniverse semanticMolecule where
  moleculeWitness := semanticMoleculeWitness
  semanticAtoms := semanticMolecule_all_semantic
  semanticBoundary := True
  nonConclusions := True

theorem semanticAtomMoleculeWitness_selected_and_semantic :
    selectedAtomUniverse.selectedAtom semanticInterpretationAtom ∧
      semanticInterpretationAtom.IsSemanticInterpretation := by
  exact semanticAtomMoleculeWitness.atom_selected_and_semantic rfl

def requiredSemanticMolecule
    (molecule : AtomMolecule Component Edge Diagram) : Prop :=
  molecule = semanticMolecule

def semanticMismatchLaw : DesignLaw Component Edge Diagram where
  Bad := fun molecule => molecule.atoms semanticInterpretationAtom
  selectedBoundary := True
  nonConclusions := True

def semanticArrangementLaw :
    SemanticAtomArrangementLaw semanticMismatchLaw requiredSemanticMolecule where
  requiredSemantic := by
    intro molecule hRequired
    rw [hRequired]
    exact semanticMolecule_all_semantic
  lawBoundary := True
  semanticBoundary := True
  nonConclusions := True

theorem semanticArrangementLaw_atom_is_semantic :
    semanticInterpretationAtom.IsSemanticInterpretation := by
  exact
    semanticArrangementLaw.atom_is_semantic
      (molecule := semanticMolecule)
      rfl
      rfl

theorem singletonSemanticMolecule_obstruction :
    ObstructionCircuit semanticMismatchLaw semanticMolecule := by
  constructor
  · rfl
  · intro N hProper hBad
    apply hProper.2
    intro atom hAtom
    have hEq : atom = semanticInterpretationAtom := by
      simpa [semanticMolecule] using hAtom
    rw [hEq]
    exact hBad

def semanticObstructionCandidate :
    SemanticObstructionCandidate semanticArrangementLaw where
  molecule := semanticMolecule
  required := rfl
  obstruction := singletonSemanticMolecule_obstruction
  evidenceBoundary := True
  nonConclusions := True

theorem semanticObstructionCandidate_bad :
    semanticMismatchLaw.Bad semanticObstructionCandidate.molecule := by
  exact semanticObstructionCandidate.bad

theorem semanticObstructionCandidate_atom_is_semantic :
    semanticInterpretationAtom.IsSemanticInterpretation := by
  exact semanticObstructionCandidate.atom_is_semantic rfl

def semanticNoBadLaw : DesignLaw Component Edge Diagram where
  Bad := fun _molecule => False
  selectedBoundary := True
  nonConclusions := True

def semanticNoBadArrangementLaw :
    SemanticAtomArrangementLaw semanticNoBadLaw requiredSemanticMolecule where
  requiredSemantic := by
    intro molecule hRequired
    rw [hRequired]
    exact semanticMolecule_all_semantic
  lawBoundary := True
  semanticBoundary := True
  nonConclusions := True

theorem semanticNoBadLaw_lawful :
    LawfulWithinAtomConfiguration semanticNoBadLaw requiredSemanticMolecule := by
  intro _molecule _hRequired hBad
  exact hBad

theorem semanticNoBadLaw_no_semantic_obstruction
    (candidate : SemanticObstructionCandidate semanticNoBadArrangementLaw) :
    False := by
  exact SemanticObstructionCandidate.no_candidate_of_lawful
    semanticNoBadLaw_lawful candidate

def forbiddenEdgeLaw : DesignLaw Component Edge Diagram where
  Bad := fun molecule => molecule.atoms relationAtom
  selectedBoundary := True
  nonConclusions := True

def forbiddenEdgeLawSeparation :
    AtomLawSeparation Component Edge Diagram where
  law := forbiddenEdgeLaw
  selectedMolecule := fun molecule =>
    molecule = forbiddenEdgeMolecule ∨ molecule = componentMolecule
  atomsExistBeforeLaw := True
  atomsExistBeforeLawEvidence := trivial
  lawDoesNotCreateAtoms := True
  lawDoesNotCreateAtomsEvidence := trivial
  lawDoesNotChangeAtomExistence := True
  lawDoesNotChangeAtomExistenceEvidence := trivial
  nonConclusions := True

theorem forbiddenEdgeLaw_does_not_create_atoms :
    forbiddenEdgeLawSeparation.lawDoesNotCreateAtoms := by
  exact forbiddenEdgeLawSeparation.law_does_not_create_atoms

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

def pureAATSurface : AATPureTheorySurface Component Edge Diagram where
  atoms := selectedAtomUniverse.selectedAtom
  molecules := selectedForbiddenEdgeUniverse.selected
  moleculeAtomsOnSurface := by
    intro molecule hMolecule atom hAtom
    rcases hMolecule with hForbidden | hComponent
    · have hEq : atom = relationAtom := by
        rw [hForbidden] at hAtom
        simpa [forbiddenEdgeMolecule] using hAtom
      exact Or.inr (Or.inl hEq)
    · have hEq : atom = componentAtom := by
        rw [hComponent] at hAtom
        simpa [componentMolecule] using hAtom
      exact Or.inl hEq
  laws := fun law => law = forbiddenEdgeLaw
  circuits := fun {law} {molecule} _hLaw _hMolecule _hCircuit =>
    law = forbiddenEdgeLaw ∧
      selectedForbiddenEdgeUniverse.selected molecule ∧
      ObstructionCircuit law molecule
  atomCoreBoundary := True
  moleculeBoundary := True
  lawBoundary := True
  patternInterpretationBoundary := True
  noObservationDependency := True
  noObservationDependencyEvidence := trivial
  noSFTDependency := True
  noSFTDependencyEvidence := trivial
  nonConclusions := True

theorem pureAATSurface_independent_of_observation :
    pureAATSurface.noObservationDependency := by
  exact pureAATSurface.independent_of_observation

theorem pureAATSurface_independent_of_sft :
    pureAATSurface.noSFTDependency := by
  exact pureAATSurface.independent_of_sft

def pureAATAtomOntology :
    AtomOntology Component Edge Diagram :=
  pureAATSurface.atomOntology

def pureAATAtomOntologySurface :
    AATAtomOntologySurface Component Edge Diagram :=
  pureAATSurface.atomOntologySurface

theorem pureAATSurface_reads_component_ontology :
    pureAATSurface.atomOntology.atoms componentAtom.ontology := by
  exact pureAATSurface.selected_atom_reads_ontology (Or.inl rfl)

theorem pureAATSurface_component_ontology_primitive :
    PrimitiveOntologicalAtom componentAtom.ontology := by
  exact pureAATSurface.selected_atom_ontology_is_primitive (Or.inl rfl)

theorem pureAATOntologySurface_independent_of_observation :
    pureAATAtomOntologySurface.noObservationDependency := by
  exact pureAATAtomOntologySurface.independent_of_observation

theorem pureAATOntologySurface_molecule_atom_reads_ontology :
    pureAATAtomOntologySurface.ontology.atoms componentAtom.ontology := by
  exact
    pureAATAtomOntologySurface.selected_molecule_atoms_read_ontology
      (molecule := componentMolecule)
      (Or.inr rfl)
      rfl

def semanticAATSurface : AATPureTheorySurface Component Edge Diagram where
  atoms := selectedAtomUniverse.selectedAtom
  molecules := requiredSemanticMolecule
  moleculeAtomsOnSurface := by
    intro molecule hMolecule atom hAtom
    have hEq : atom = semanticInterpretationAtom := by
      rw [hMolecule] at hAtom
      simpa [semanticMolecule] using hAtom
    exact Or.inr (Or.inr (Or.inr hEq))
  laws := fun law => law = semanticNoBadLaw
  circuits := fun {law} {molecule} hLaw hMolecule hCircuit =>
    law = semanticNoBadLaw ∧
      requiredSemanticMolecule molecule ∧
      ObstructionCircuit law molecule
  atomCoreBoundary := True
  moleculeBoundary := True
  lawBoundary := True
  patternInterpretationBoundary := True
  noObservationDependency := True
  noObservationDependencyEvidence := trivial
  noSFTDependency := True
  noSFTDependencyEvidence := trivial
  nonConclusions := True

theorem semanticAATSurface_semantic_law_selected :
    semanticAATSurface.laws semanticNoBadLaw := by
  rfl

theorem semanticAATSurface_semantic_required_molecule :
    semanticAATSurface.molecules semanticMolecule := by
  rfl

theorem semanticAATSurface_semantic_atom_on_surface :
    semanticAATSurface.atoms semanticInterpretationAtom ∧
      semanticInterpretationAtom.IsSemanticInterpretation := by
  exact
    semanticAATSurface.semantic_atom_of_selected_semantic_molecule
      (molecule := semanticMolecule)
      ⟨rfl, semanticMolecule_all_semantic⟩
      rfl

def semanticLawSeparation :
    AtomLawSeparation Component Edge Diagram where
  law := semanticNoBadLaw
  selectedMolecule := requiredSemanticMolecule
  atomsExistBeforeLaw := True
  atomsExistBeforeLawEvidence := trivial
  lawDoesNotCreateAtoms := True
  lawDoesNotCreateAtomsEvidence := trivial
  lawDoesNotChangeAtomExistence := True
  lawDoesNotChangeAtomExistenceEvidence := trivial
  nonConclusions := True

def semanticPureAtomCore :
    AtomAxiomatizedPureAAT Component Edge Diagram where
  surface := semanticAATSurface
  lawSeparation := by
    intro _law _hLaw
    exact semanticLawSeparation
  lawSeparationMatches := by
    intro law hLaw
    exact hLaw.symm
  lawEvaluatesSurfaceMolecules := by
    intro _law _hLaw _molecule hMolecule
    exact hMolecule
  circuitClosure := by
    intro _law _molecule hLaw hMolecule hCircuit
    exact ⟨hLaw, hMolecule, hCircuit⟩
  noArchitectureSignatureDependency := True
  noArchitectureSignatureDependencyEvidence := trivial
  atomAxiomBoundary := True
  moleculeAxiomBoundary := True
  lawAxiomBoundary := True
  circuitAxiomBoundary := True
  pureTheoryBoundary := True
  nonConclusions := True

theorem semanticPureAtomCore_semantic_atom_on_surface :
    semanticPureAtomCore.surface.atoms semanticInterpretationAtom ∧
      semanticInterpretationAtom.IsSemanticInterpretation := by
  exact
    AtomAxiomatizedPureAAT.selected_semantic_molecule_atom_on_surface_and_semantic
      semanticPureAtomCore
      (molecule := semanticMolecule)
      ⟨rfl, semanticMolecule_all_semantic⟩
      rfl

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

theorem rejectedPrimitiveCandidate_observes_ontology_not_existence :
    rejectedPrimitiveCandidate.observedOntology.boundaryIndependent := by
  exact rejectedPrimitiveCandidate.observes_boundary_free_ontology

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

theorem runtimeObservationGap_no_atom_existence_claim :
    ¬ runtimeObservationGap.AtomExistenceClaim := by
  exact runtimeObservationGap.no_atom_existence_claim

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

def allSelectedMolecules (molecule : AtomMolecule Component Edge Diagram) : Prop :=
  AtomMoleculeSupportedBy selectedAtomUniverse molecule

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

def identityLSPAtomArrangement :
    LSPAtomArrangementLaw
      identityProjection observationToUnit noBadAtomLaw allSelectedMolecules where
  lawfulnessImpliesLSPCompatible := by
    intro _hLawful _x _y _hSame
    rfl
  lspFailureExposesBadMolecule := by
    intro pair hFailure
    exact False.elim (hFailure.2 rfl)
  observationBoundary := True
  nonConclusions := True

theorem identityLSPAtomArrangement_lspCompatible :
    LSPCompatible identityProjection observationToUnit :=
  identityLSPAtomArrangement.lspCompatible_of_lawful noBadAtomLaw_lawful

theorem identityLSPAtomArrangement_noLSPObstruction :
    NoLSPObstruction identityProjection observationToUnit :=
  identityLSPAtomArrangement.noLSPObstruction_of_lawful noBadAtomLaw_lawful

def allowAllBoundaryPolicyAtomArrangement :
    EdgePolicyAtomArrangementLaw
      noEdgeGraph (fun _ _ => True) noBadAtomLaw allSelectedMolecules where
  lawfulnessImpliesPolicySound := by
    intro _hLawful _c _d _hEdge
    trivial
  policyViolationExposesBadMolecule := by
    intro _pair _hEdge hNotAllowed
    exact False.elim (hNotAllowed trivial)
  policyBoundary := True
  nonConclusions := True

def allowAllAbstractionPolicyAtomArrangement :
    EdgePolicyAtomArrangementLaw
      noEdgeGraph (fun _ _ => True) noBadAtomLaw allSelectedMolecules where
  lawfulnessImpliesPolicySound := by
    intro _hLawful _c _d _hEdge
    trivial
  policyViolationExposesBadMolecule := by
    intro _pair _hEdge hNotAllowed
    exact False.elim (hNotAllowed trivial)
  policyBoundary := True
  nonConclusions := True

theorem allowAllBoundaryPolicyAtomArrangement_policySound :
    ∀ {c d : Component}, noEdgeGraph.edge c d -> True :=
  allowAllBoundaryPolicyAtomArrangement.policySound_of_lawful
    noBadAtomLaw_lawful

theorem allowAllAbstractionPolicyAtomArrangement_noViolation :
    ∀ pair : Component × Component,
      ¬ (noEdgeGraph.edge pair.1 pair.2 ∧ ¬ True) :=
  allowAllAbstractionPolicyAtomArrangement.noPolicyViolation_of_lawful
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

def exampleAATLocalAlgebraForSFT :
    AATLocalAlgebraForSFT Component Edge Diagram where
  aatSurface := pureAATSurface
  usedAsLocalAlgebra := True
  usedAsLocalAlgebraEvidence := trivial
  sftDoesNotRedefineAtoms := True
  sftDoesNotRedefineAtomsEvidence := trivial
  sftDoesNotRedefineAAT := True
  sftDoesNotRedefineAATEvidence := trivial
  noForecastCorrectnessFromAATAlone := True
  noForecastCorrectnessFromAATAloneEvidence := trivial
  nonConclusions := True

theorem exampleAATLocalAlgebra_no_forecast_correctness :
    exampleAATLocalAlgebraForSFT.noForecastCorrectnessFromAATAlone := by
  exact
    exampleAATLocalAlgebraForSFT
      |>.aat_alone_does_not_prove_forecast_correctness

def exampleForecastRecord :
    ForecastRecord unitOperationSupport unitStepRelation () 0 where
  target := ()
  path := ArchitecturePath.nil ()
  coneMember := ForecastCone.nil_mem ()
  forecastBoundary := True
  nonConclusions := True

def exampleConeFamily :
    ConeFamily unitOperationSupport unitStepRelation () 0 where
  records := [exampleForecastRecord]
  nonempty := by
    simp
  familyBoundary := True
  unknownRemainder := True
  nonConclusions := True

def exampleEnvelopeObservationBoundary : ObservationBoundary Unit where
  pathClassesVisible := True
  affectedRegionsVisible := True
  comparableAxes := True
  observedProjectionBoundary := True
  missingBoundary := True
  theoremBoundary := True
  unknownRemainder := True
  nonConclusions := True

def exampleConsequenceEnvelope :
    ConsequenceEnvelope unitOperationSupport unitStepRelation () 0 where
  selectedConeCount := 1
  pathClasses := True
  affectedRegions := True
  comparableAxes := True
  axisDeltaRanges := True
  obstructionCandidates := True
  missingBoundaryItems := True
  theoremBoundaryItems := True
  unknownRemainder := True
  forecastBoundary := True
  nonConclusions := True
  projectionBoundary := True

def exampleEnvelopeProjection :
    EnvelopeProjection
      exampleConeFamily
      exampleEnvelopeObservationBoundary
      exampleConsequenceEnvelope where
  recordsSelectedConeCount := by
    rfl
  preservesPathClasses := by
    intro h
    exact h
  preservesAffectedRegions := by
    intro h
    exact h
  preservesComparableAxes := by
    intro h
    exact h
  preservesMissingBoundary := by
    intro h
    exact h
  preservesTheoremBoundary := by
    intro h
    exact h
  preservesFamilyUnknownRemainder := by
    intro h
    exact h
  preservesBoundaryUnknownRemainder := by
    intro h
    exact h
  preservesForecastNonConclusions := by
    intro _h
    trivial
  preservesBoundaryNonConclusions := by
    intro h
    exact h
  recordsForecastBoundary := trivial
  recordsProjectionBoundary := trivial
  recordsNonConclusions := trivial

def exampleAATPremisedConsequenceEnvelope :
    AATPremisedConsequenceEnvelope
      exampleAATLocalAlgebraForSFT
      exampleAtomTraceForecastBoundary
      exampleConeFamily
      exampleEnvelopeObservationBoundary
      exampleConsequenceEnvelope where
  projection := exampleEnvelopeProjection
  readsAATLocalAlgebra := trivial
  atomTraceBoundary := trivial
  circuitTraceBoundary := trivial
  forecastConeBoundary := ForecastCone.nil_mem ()
  noForecastCorrectnessFromAAT := trivial
  traceRecordsNoForecastCorrectness :=
    exampleAtomTraceForecastBoundary.records_no_forecast_correctness
  envelopeForecastBoundary := trivial
  envelopeProjectionBoundary := trivial
  nonConclusions := trivial

theorem exampleAATPremisedEnvelope_records_boundaries :
    exampleConsequenceEnvelope.RecordsForecastBoundary ∧
      exampleConsequenceEnvelope.RecordsProjectionBoundary ∧
      exampleConsequenceEnvelope.RecordsNonConclusions :=
  exampleAATPremisedConsequenceEnvelope.records_envelope_boundaries

theorem exampleAATPremisedEnvelope_no_forecast_correctness :
    exampleAATLocalAlgebraForSFT.noForecastCorrectnessFromAATAlone ∧
      ¬ AtomTraceForecastBoundary.ForecastCorrectnessClaim
        exampleAtomTraceForecastBoundary :=
  exampleAATPremisedConsequenceEnvelope
    |>.aat_premise_does_not_prove_forecast_correctness

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

def exampleSemanticDelta : SemanticDelta Component Edge Diagram where
  created := fun atom => atom = semanticInterpretationAtom
  removed := fun _ => False
  preserved := fun atom => atom = semanticInterpretationAtom
  transformed := fun _ _ => False
  createdSemantic := by
    intro atom hAtom
    rw [hAtom]
    rfl
  removedSemantic := by
    intro _atom hAtom
    exact False.elim hAtom
  preservedSemantic := by
    intro atom hAtom
    rw [hAtom]
    rfl
  transformedSemantic := by
    intro _before _after hTransform
    exact False.elim hTransform
  evidenceBoundary := True
  nonConclusions := True

theorem exampleSemanticDelta_created_is_semantic :
    semanticInterpretationAtom.IsSemanticInterpretation := by
  exact exampleSemanticDelta.created_is_semantic rfl

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
