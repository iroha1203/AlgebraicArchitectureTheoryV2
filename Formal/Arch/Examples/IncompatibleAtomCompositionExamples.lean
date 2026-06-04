import Formal.Arch.AAT.GeneratedGraph
import Formal.Arch.Observation.AtomPresentation

namespace Formal.Arch.IncompatibleAtomCompositionExamples

inductive ExampleAtom where
  | isolated
  | incompatible
  deriving DecidableEq, Repr

def exampleKind (_atom : ExampleAtom) : AtomKind :=
  AtomKind.existence

def exampleAxis (_atom : ExampleAtom) : Axis :=
  Axis.static

def exampleSystem : AtomAxiomSystem where
  Atom := ExampleAtom
  Predicate := AtomKind
  kind := exampleKind
  axis := exampleAxis
  predicate := exampleKind
  predicateKind := fun kind => kind
  predicateAxis := fun _ => Axis.static
  predicateKindAligned := by
    intro atom
    rfl
  predicateAxisAligned := by
    intro atom
    cases atom <;> rfl
  singleFact := fun _ => True
  singleFactEvidence := fun _ => trivial
  predicatePreserving := fun _ => True
  predicatePreservingEvidence := fun _ => trivial
  boundaryIndependent := fun _ => True
  boundaryIndependentEvidence := fun _ => trivial
  lawIndependent := fun _ => True
  lawIndependentEvidence := fun _ => trivial
  noObservationBoundaryCreatesAtoms := True
  noObservationBoundaryCreatesAtomsEvidence := trivial
  noLawCreatesAtoms := True
  noLawCreatesAtomsEvidence := trivial
  noToolOutputCreatesAtoms := True
  noToolOutputCreatesAtomsEvidence := trivial
  noSFTEventCreatesAtoms := True
  noSFTEventCreatesAtomsEvidence := trivial
  openTaxonomyBoundary := True

def rejectingPort : AtomPort where
  name := "rejecting"
  kind := AtomPortKind.subject
  family := AtomKind.existence
  axis := Axis.static
  required := True
  acceptsFamily := fun _ => False
  acceptsAxis := fun _ => True

def incompatiblePort : AtomPort where
  name := "incompatible"
  kind := AtomPortKind.subject
  family := AtomKind.existence
  axis := Axis.static
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def rejectingValence : AtomValence where
  ports := fun port => port = rejectingPort
  requiredPort := fun port => port = rejectingPort
  requiredPortHasPort := by
    intro port hRequired
    exact hRequired
  hasPort := ⟨rejectingPort, rfl⟩

def incompatibleValence : AtomValence where
  ports := fun port => port = incompatiblePort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨incompatiblePort, rfl⟩

def exampleShape (atom : ExampleAtom) : AtomShape where
  family := AtomKind.existence
  axis := Axis.static
  subject := { name := match atom with
    | ExampleAtom.isolated => "isolated"
    | ExampleAtom.incompatible => "incompatible" }
  predicate := "component"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := AtomDirection.neutral
  arity := 1
  valence := match atom with
    | ExampleAtom.isolated => rejectingValence
    | ExampleAtom.incompatible => incompatibleValence
  singleFactShape := True
  singleFactShapeEvidence := trivial

def exampleShapePresentation :
    AtomShapePresentation exampleSystem where
  shapeOf := exampleShape
  shapeKindAligned := by
    intro atom
    cases atom <;> rfl
  shapeAxisAligned := by
    intro atom
    cases atom <;> rfl
  shapeSingleFact := by
    intro _ _
    trivial

theorem rejecting_incompatible_ports_do_not_bind :
    ¬ PortCompatible rejectingPort incompatiblePort := by
  intro hCompatible
  exact hCompatible.2.1

theorem rejecting_shape_not_compatible :
    CompatibleComposition
      (AtomShapeOf exampleShapePresentation ExampleAtom.isolated)
      (AtomShapeOf exampleShapePresentation ExampleAtom.incompatible) ->
        False := by
  exact CompatibleComposition.no_compatible_port_not_compatible
    (by
      intro leftPort rightPort hLeft hRight hCompatible
      subst leftPort
      subst rightPort
      exact rejecting_incompatible_ports_do_not_bind hCompatible)

theorem incompatible_pair_not_generated_molecule
    (molecule : AAT.GeneratedMolecule exampleShapePresentation)
    (hIsolated : molecule.atoms ExampleAtom.isolated)
    (hIncompatible : molecule.atoms ExampleAtom.incompatible) :
    False := by
  exact molecule.incompatible_slots_not_generatedMolecule
    hIsolated
    hIncompatible
    (by intro h; cases h)
    rejecting_shape_not_compatible

theorem missing_required_port_not_generated_molecule
    (molecule : AAT.GeneratedMolecule exampleShapePresentation)
    (hIsolated : molecule.atoms ExampleAtom.isolated)
    (hOnlyIsolated :
      ∀ atom, molecule.atoms atom -> atom = ExampleAtom.isolated) :
    False := by
  exact molecule.missing_required_port_not_generatedMolecule
    hIsolated
    (by rfl)
    (by
      intro hMatch
      rcases hMatch with
        ⟨other, _otherPort, hOther, hDistinct, _hOtherPort, _hCompatible⟩
      exact hDistinct (hOnlyIsolated other hOther))

inductive EndpointAtom where
  | relationOnly
  | endpoint
  deriving DecidableEq, Repr

def endpointKind : EndpointAtom -> AtomKind
  | EndpointAtom.relationOnly => AtomKind.relation
  | EndpointAtom.endpoint => AtomKind.existence

def endpointAxis (_atom : EndpointAtom) : Axis :=
  Axis.static

def endpointSystem : AtomAxiomSystem where
  Atom := EndpointAtom
  Predicate := AtomKind
  kind := endpointKind
  axis := endpointAxis
  predicate := endpointKind
  predicateKind := fun kind => kind
  predicateAxis := fun _ => Axis.static
  predicateKindAligned := by
    intro atom
    rfl
  predicateAxisAligned := by
    intro atom
    cases atom <;> rfl
  singleFact := fun _ => True
  singleFactEvidence := fun _ => trivial
  predicatePreserving := fun _ => True
  predicatePreservingEvidence := fun _ => trivial
  boundaryIndependent := fun _ => True
  boundaryIndependentEvidence := fun _ => trivial
  lawIndependent := fun _ => True
  lawIndependentEvidence := fun _ => trivial
  noObservationBoundaryCreatesAtoms := True
  noObservationBoundaryCreatesAtomsEvidence := trivial
  noLawCreatesAtoms := True
  noLawCreatesAtomsEvidence := trivial
  noToolOutputCreatesAtoms := True
  noToolOutputCreatesAtomsEvidence := trivial
  noSFTEventCreatesAtoms := True
  noSFTEventCreatesAtomsEvidence := trivial
  openTaxonomyBoundary := True

def endpointPort : AtomPort where
  name := "endpoint-compatible"
  kind := AtomPortKind.subject
  family := AtomKind.existence
  axis := Axis.static
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def endpointValence : AtomValence where
  ports := fun port => port = endpointPort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨endpointPort, rfl⟩

def endpointShape (atom : EndpointAtom) : AtomShape where
  family := endpointKind atom
  axis := Axis.static
  subject := { name := match atom with
    | EndpointAtom.relationOnly => "relation-only"
    | EndpointAtom.endpoint => "endpoint" }
  predicate := match atom with
    | EndpointAtom.relationOnly => "relation"
    | EndpointAtom.endpoint => "component"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := AtomDirection.neutral
  arity := 1
  valence := endpointValence
  singleFactShape := True
  singleFactShapeEvidence := trivial

def endpointShapePresentation :
    AtomShapePresentation endpointSystem where
  shapeOf := endpointShape
  shapeKindAligned := by
    intro atom
    cases atom <;> rfl
  shapeAxisAligned := by
    intro atom
    cases atom <;> rfl
  shapeSingleFact := by
    intro _ _
    trivial

def endpointSelectedAtoms : EndpointAtom -> Prop
  | EndpointAtom.relationOnly => True
  | EndpointAtom.endpoint => True

def endpointComposition :
    CompatibleComposition
      (AtomShapeOf endpointShapePresentation EndpointAtom.relationOnly)
      (AtomShapeOf endpointShapePresentation EndpointAtom.endpoint) where
  leftPort := endpointPort
  rightPort := endpointPort
  leftHasPort := rfl
  rightHasPort := rfl
  portsCompatible := by
    exact ⟨rfl, trivial, trivial, trivial, trivial⟩
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent : ("relation" : String) ≠ "component" := by
      decide
    exact False.elim (hDifferent hPredicate)

def endpointCompositionSymm :
    CompatibleComposition
      (AtomShapeOf endpointShapePresentation EndpointAtom.endpoint)
      (AtomShapeOf endpointShapePresentation EndpointAtom.relationOnly) where
  leftPort := endpointPort
  rightPort := endpointPort
  leftHasPort := rfl
  rightHasPort := rfl
  portsCompatible := by
    exact ⟨rfl, trivial, trivial, trivial, trivial⟩
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent : ("component" : String) ≠ "relation" := by
      decide
    exact False.elim (hDifferent hPredicate)

def endpointCompositionGraph :
    AAT.CompositionGraph endpointShapePresentation endpointSelectedAtoms where
  compatiblePairs := by
    intro left right _hLeft _hRight hDistinct
    cases left
    · cases right
      · exact False.elim (hDistinct rfl)
      · exact endpointComposition
    · cases right
      · exact endpointCompositionSymm
      · exact False.elim (hDistinct rfl)
  graphBoundary := True

def endpointGeneratedMolecule :
    AAT.GeneratedMolecule endpointShapePresentation where
  atoms := endpointSelectedAtoms
  finiteConfiguration := True
  atomsPrimitive := by
    intro atom _
    exact endpointSystem.primitive atom
  compositionGraph := endpointCompositionGraph
  requiredPortsMatched := by
    intro _ _ _ hRequired
    cases hRequired

def endpointGeneratedObject :
    AAT.GeneratedArchitectureObject endpointShapePresentation where
  molecule := endpointGeneratedMolecule
  carrierList :=
    [ ⟨EndpointAtom.relationOnly, by trivial⟩
    , ⟨EndpointAtom.endpoint, by trivial⟩
    ]
  carrierListNodup := by
    simp
  carrierListCovers := by
    intro carrier
    cases carrier with
    | mk atom _hAtom =>
        cases atom <;> simp
  objectBoundary := True

def endpointCarrier :
    AAT.GeneratedCarrier endpointGeneratedObject :=
  ⟨EndpointAtom.endpoint, by trivial⟩

def handAuthoredEndpointGraph :
    ArchGraph (AAT.GeneratedCarrier endpointGeneratedObject) where
  edge := fun _ _ => True

theorem relation_atom_without_second_endpoint_not_generated_edge :
    ¬ (AAT.GeneratedArchGraph endpointGeneratedObject).edge
      endpointCarrier endpointCarrier := by
  intro hEdge
  exact
    (AAT.GeneratedArchGraph.generated_graph_edge_requires_distinct_endpoints
      endpointGeneratedObject hEdge) rfl

theorem hand_authored_graph_edge_not_atom_generated_edge :
    handAuthoredEndpointGraph.edge endpointCarrier endpointCarrier ∧
      ¬ (AAT.GeneratedArchGraph endpointGeneratedObject).edge
        endpointCarrier endpointCarrier := by
  exact ⟨trivial, relation_atom_without_second_endpoint_not_generated_edge⟩

inductive EffectOnlyAtom where
  | effectOnly
  deriving DecidableEq, Repr

def effectOnlySystem : AtomAxiomSystem where
  Atom := EffectOnlyAtom
  Predicate := AtomKind
  kind := fun _ => AtomKind.effect
  axis := fun _ => Axis.semantic
  predicate := fun _ => AtomKind.effect
  predicateKind := fun kind => kind
  predicateAxis := fun _ => Axis.semantic
  predicateKindAligned := by
    intro atom
    cases atom
    rfl
  predicateAxisAligned := by
    intro atom
    cases atom
    rfl
  singleFact := fun _ => True
  singleFactEvidence := fun _ => trivial
  predicatePreserving := fun _ => True
  predicatePreservingEvidence := fun _ => trivial
  boundaryIndependent := fun _ => True
  boundaryIndependentEvidence := fun _ => trivial
  lawIndependent := fun _ => True
  lawIndependentEvidence := fun _ => trivial
  noObservationBoundaryCreatesAtoms := True
  noObservationBoundaryCreatesAtomsEvidence := trivial
  noLawCreatesAtoms := True
  noLawCreatesAtomsEvidence := trivial
  noToolOutputCreatesAtoms := True
  noToolOutputCreatesAtomsEvidence := trivial
  noSFTEventCreatesAtoms := True
  noSFTEventCreatesAtomsEvidence := trivial
  openTaxonomyBoundary := True

def effectOnlyShape (_atom : EffectOnlyAtom) : AtomShape where
  family := AtomKind.effect
  axis := Axis.semantic
  subject := { name := "effect-only" }
  predicate := "effect"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := AtomDirection.outgoing
  arity := 1
  valence := endpointValence
  singleFactShape := True
  singleFactShapeEvidence := trivial

def effectOnlyShapePresentation :
    AtomShapePresentation effectOnlySystem where
  shapeOf := effectOnlyShape
  shapeKindAligned := by
    intro atom
    cases atom
    rfl
  shapeAxisAligned := by
    intro atom
    cases atom
    rfl
  shapeSingleFact := by
    intro _ _
    trivial

def effectOnlyGeneratedMolecule :
    AAT.GeneratedMolecule effectOnlyShapePresentation where
  atoms := fun _ => True
  finiteConfiguration := True
  atomsPrimitive := by
    intro atom _
    exact effectOnlySystem.primitive atom
  compositionGraph :=
    { compatiblePairs := by
        intro left right _ _ hDistinct
        cases left
        cases right
        exact False.elim (hDistinct rfl)
      graphBoundary := True }
  requiredPortsMatched := by
    intro _ _ _ hRequired
    cases hRequired

def effectOnlyGeneratedObject :
    AAT.GeneratedArchitectureObject effectOnlyShapePresentation where
  molecule := effectOnlyGeneratedMolecule
  carrierList := [ ⟨EffectOnlyAtom.effectOnly, by trivial⟩ ]
  carrierListNodup := by
    simp
  carrierListCovers := by
    intro carrier
    cases carrier with
    | mk atom _hAtom =>
        cases atom
        simp
  objectBoundary := True

def effectOnlyCarrier :
    AAT.GeneratedCarrier effectOnlyGeneratedObject :=
  ⟨EffectOnlyAtom.effectOnly, by trivial⟩

theorem effect_atom_without_authority_not_law_satisfied :
    ¬ AAT.GeneratedArchitectureObject.GeneratedAuthorityEffectLawSatisfied
      effectOnlyGeneratedObject effectOnlyCarrier := by
  exact
    AAT.GeneratedArchitectureObject.no_authority_policy_not_generated_authority_effect_law_satisfied
      effectOnlyGeneratedObject effectOnlyCarrier
      (by
        intro authority hAuthority
        cases authority.val
        cases hAuthority)

inductive CapabilityOnlyAtom where
  | capabilityOnly
  deriving DecidableEq, Repr

def capabilityOnlySystem : AtomAxiomSystem where
  Atom := CapabilityOnlyAtom
  Predicate := AtomKind
  kind := fun _ => AtomKind.capability
  axis := fun _ => Axis.static
  predicate := fun _ => AtomKind.capability
  predicateKind := fun kind => kind
  predicateAxis := fun _ => Axis.static
  predicateKindAligned := by
    intro atom
    cases atom
    rfl
  predicateAxisAligned := by
    intro atom
    cases atom
    rfl
  singleFact := fun _ => True
  singleFactEvidence := fun _ => trivial
  predicatePreserving := fun _ => True
  predicatePreservingEvidence := fun _ => trivial
  boundaryIndependent := fun _ => True
  boundaryIndependentEvidence := fun _ => trivial
  lawIndependent := fun _ => True
  lawIndependentEvidence := fun _ => trivial
  noObservationBoundaryCreatesAtoms := True
  noObservationBoundaryCreatesAtomsEvidence := trivial
  noLawCreatesAtoms := True
  noLawCreatesAtomsEvidence := trivial
  noToolOutputCreatesAtoms := True
  noToolOutputCreatesAtomsEvidence := trivial
  noSFTEventCreatesAtoms := True
  noSFTEventCreatesAtomsEvidence := trivial
  openTaxonomyBoundary := True

def capabilityOnlyRequiredDataStatePort : AtomPort where
  name := "capability-only-required-data-state"
  kind := AtomPortKind.payload
  family := AtomKind.capability
  axis := Axis.static
  required := True
  acceptsFamily := fun kind => kind = AtomKind.dataState
  acceptsAxis := fun axis => axis = Axis.dataflow

def capabilityOnlyValence : AtomValence where
  ports := fun port => port = capabilityOnlyRequiredDataStatePort
  requiredPort := fun port => port = capabilityOnlyRequiredDataStatePort
  requiredPortHasPort := by
    intro _ hRequired
    exact hRequired
  hasPort := ⟨capabilityOnlyRequiredDataStatePort, rfl⟩

def capabilityOnlyShape (_atom : CapabilityOnlyAtom) : AtomShape where
  family := AtomKind.capability
  axis := Axis.static
  subject := { name := "capability-only" }
  predicate := "capability"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := AtomDirection.outgoing
  arity := 1
  valence := capabilityOnlyValence
  singleFactShape := True
  singleFactShapeEvidence := trivial

def capabilityOnlyShapePresentation :
    AtomShapePresentation capabilityOnlySystem where
  shapeOf := capabilityOnlyShape
  shapeKindAligned := by
    intro atom
    cases atom
    rfl
  shapeAxisAligned := by
    intro atom
    cases atom
    rfl
  shapeSingleFact := by
    intro _ _
    trivial

theorem capability_atom_without_data_state_not_generated_molecule
    (molecule : AAT.GeneratedMolecule capabilityOnlyShapePresentation)
    (hCapability : molecule.atoms CapabilityOnlyAtom.capabilityOnly)
    (hOnlyCapability :
      ∀ atom,
        molecule.atoms atom -> atom = CapabilityOnlyAtom.capabilityOnly) :
    False := by
  exact molecule.missing_required_port_not_generatedMolecule
    hCapability
    (by rfl)
    (by
      intro hMatch
      rcases hMatch with
        ⟨other, _otherPort, hOther, hDistinct, _hOtherPort,
          _hCompatible⟩
      exact hDistinct (hOnlyCapability other hOther))

inductive SemanticOnlyAtom where
  | semanticOnly
  deriving DecidableEq, Repr

def semanticOnlySystem : AtomAxiomSystem where
  Atom := SemanticOnlyAtom
  Predicate := AtomKind
  kind := fun _ => AtomKind.semanticInterpretation
  axis := fun _ => Axis.semantic
  predicate := fun _ => AtomKind.semanticInterpretation
  predicateKind := fun kind => kind
  predicateAxis := fun _ => Axis.semantic
  predicateKindAligned := by
    intro atom
    cases atom
    rfl
  predicateAxisAligned := by
    intro atom
    cases atom
    rfl
  singleFact := fun _ => True
  singleFactEvidence := fun _ => trivial
  predicatePreserving := fun _ => True
  predicatePreservingEvidence := fun _ => trivial
  boundaryIndependent := fun _ => True
  boundaryIndependentEvidence := fun _ => trivial
  lawIndependent := fun _ => True
  lawIndependentEvidence := fun _ => trivial
  noObservationBoundaryCreatesAtoms := True
  noObservationBoundaryCreatesAtomsEvidence := trivial
  noLawCreatesAtoms := True
  noLawCreatesAtomsEvidence := trivial
  noToolOutputCreatesAtoms := True
  noToolOutputCreatesAtomsEvidence := trivial
  noSFTEventCreatesAtoms := True
  noSFTEventCreatesAtomsEvidence := trivial
  openTaxonomyBoundary := True

def semanticOnlyRequiredContractPort : AtomPort where
  name := "semantic-only-required-contract"
  kind := AtomPortKind.contract
  family := AtomKind.semanticInterpretation
  axis := Axis.semantic
  required := True
  acceptsFamily := fun kind => kind = AtomKind.contractSpecification
  acceptsAxis := fun axis => axis = Axis.specification

def semanticOnlyValence : AtomValence where
  ports := fun port => port = semanticOnlyRequiredContractPort
  requiredPort := fun port => port = semanticOnlyRequiredContractPort
  requiredPortHasPort := by
    intro _ hRequired
    exact hRequired
  hasPort := ⟨semanticOnlyRequiredContractPort, rfl⟩

def semanticOnlyShape (_atom : SemanticOnlyAtom) : AtomShape where
  family := AtomKind.semanticInterpretation
  axis := Axis.semantic
  subject := { name := "semantic-only" }
  predicate := "semantic-interpretation"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := AtomDirection.outgoing
  arity := 1
  valence := semanticOnlyValence
  singleFactShape := True
  singleFactShapeEvidence := trivial

def semanticOnlyShapePresentation :
    AtomShapePresentation semanticOnlySystem where
  shapeOf := semanticOnlyShape
  shapeKindAligned := by
    intro atom
    cases atom
    rfl
  shapeAxisAligned := by
    intro atom
    cases atom
    rfl
  shapeSingleFact := by
    intro _ _
    trivial

theorem semantic_atom_without_contract_not_generated_molecule
    (molecule : AAT.GeneratedMolecule semanticOnlyShapePresentation)
    (hSemantic : molecule.atoms SemanticOnlyAtom.semanticOnly)
    (hOnlySemantic :
      ∀ atom, molecule.atoms atom -> atom = SemanticOnlyAtom.semanticOnly) :
    False := by
  exact molecule.missing_required_port_not_generatedMolecule
    hSemantic
    (by rfl)
    (by
      intro hMatch
      rcases hMatch with
        ⟨other, _otherPort, hOther, hDistinct, _hOtherPort,
          _hCompatible⟩
      exact hDistinct (hOnlySemantic other hOther))

def concernHintCandidate :
    Observation.RawAtomCandidate exampleSystem String where
  predicate := AtomKind.relation
  evidence := "concern-only"
  candidateBoundary := True
  notAtomTruthBoundary := True
  nonConclusions := True

def concernHintMolecule : AAT.Molecule exampleSystem where
  atoms := fun _ => False
  finiteConfiguration := True
  nonConclusions := True

def concernHintLaw : AAT.DesignLaw exampleSystem where
  Bad := fun _ => False
  evaluationBoundary := True
  nonConclusions := True

theorem concern_hint_is_raw_candidate :
    Observation.RawAtomCandidate.Status =
      Observation.AtomObservationStatus.rawCandidate := by
  rfl

theorem concern_hint_does_not_create_atoms :
    exampleSystem.noObservationBoundaryCreatesAtoms := by
  exact concernHintCandidate.does_not_create_atoms

theorem concern_hint_not_obstruction_circuit :
    ¬ AAT.ObstructionCircuit concernHintLaw concernHintMolecule := by
  intro hCircuit
  exact AAT.obstructionCircuit_bad hCircuit

def missingConcernObservation :
    Observation.AtomObservationGap exampleSystem String where
  evidence := "missing-concern"
  gapBoundary := True
  doesNotImplyAtomAbsence := True
  doesNotImplyAtomAbsenceEvidence := trivial
  nonConclusions := True

def concernAtomPresentation :
    Observation.AtomPresentation exampleSystem String where
  rawCandidate := fun candidate => candidate = concernHintCandidate
  observed := fun _ => False
  validated := fun _ => False
  rejected := fun _ => False
  uncertain := fun candidate => candidate = concernHintCandidate
  missing := fun gap => gap = missingConcernObservation
  validationBoundary := True
  rawCandidateIsNotAtomTruth := True
  rawCandidateIsNotAtomTruthEvidence := trivial
  rejectedIsNotMeasuredZero := True
  rejectedIsNotMeasuredZeroEvidence := trivial
  uncertainIsNotMeasuredZero := True
  uncertainIsNotMeasuredZeroEvidence := trivial
  missingIsNotMeasuredZero := True
  missingIsNotMeasuredZeroEvidence := trivial
  missingIsNotAtomAbsence := True
  missingIsNotAtomAbsenceEvidence := trivial
  nonConclusions := True

theorem observation_gap_is_not_measured_zero :
    concernAtomPresentation.missingIsNotMeasuredZero := by
  exact concernAtomPresentation.missing_is_not_measured_zero

theorem observation_gap_is_not_atom_absence :
    concernAtomPresentation.missingIsNotAtomAbsence := by
  exact concernAtomPresentation.missing_is_not_atom_absence

end Formal.Arch.IncompatibleAtomCompositionExamples
