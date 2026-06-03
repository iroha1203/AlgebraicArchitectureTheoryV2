import Formal.Arch.Observation.ArchMapGeneratedHandoff
import Formal.Arch.Examples.AtomFoundationExamples

namespace Formal.Arch.ArchMapObservationExamples

open Formal.Arch.AtomFoundationExamples

def rawApiCandidate :
    Observation.RawAtomCandidate exampleAtomAxiomSystem String where
  predicate := examplePredicate ExampleAtom.apiComponent
  evidence := "src/API"
  candidateBoundary := True
  notAtomTruthBoundary := True
  nonConclusions := True

def observedApiAtom :
    Observation.ObservedAtom exampleAtomAxiomSystem String where
  atom := ExampleAtom.apiComponent
  evidence := "src/API"
  observationBoundary := True
  observedStatus := Observation.AtomObservationStatus.observed
  statusBoundary := True
  nonConclusions := True

def missingApiObservation :
    Observation.AtomObservationGap exampleAtomAxiomSystem String where
  evidence := "src/missing"
  gapBoundary := True
  doesNotImplyAtomAbsence := True
  doesNotImplyAtomAbsenceEvidence := trivial
  nonConclusions := True

def exampleAtomPresentation :
    Observation.AtomPresentation exampleAtomAxiomSystem String where
  rawCandidate := fun candidate => candidate = rawApiCandidate
  observed := fun observed => observed = observedApiAtom
  validated := fun _ => False
  rejected := fun _ => False
  uncertain := fun _ => False
  missing := fun gap => gap = missingApiObservation
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

def exampleArchMapObservationLayer :
    Observation.ArchMapObservationLayer
      exampleAtomAxiomSystem Unit String where
  presentation := exampleAtomPresentation
  selectedSource := fun _ => True
  observesAtoms := True
  observesAtomsEvidence := trivial
  archMapDoesNotCreateAtomsEvidence :=
    exampleAtomAxiomSystem.observation_boundary_does_not_create_atoms
  archMapDoesNotDefineAAT := True
  archMapDoesNotDefineAATEvidence := trivial
  rawCandidateBoundary := True
  validationBoundary := True
  coverageBoundary := True
  exactnessBoundary := True
  nonConclusions := True

theorem rawCandidate_does_not_create_atoms :
    exampleAtomAxiomSystem.noObservationBoundaryCreatesAtoms := by
  exact rawApiCandidate.does_not_create_atoms

theorem observedAtom_is_primitive :
    exampleAtomAxiomSystem.Primitive ExampleAtom.apiComponent := by
  exact observedApiAtom.atom_primitive

theorem gap_does_not_imply_atom_absence :
    missingApiObservation.doesNotImplyAtomAbsence := by
  exact missingApiObservation.gap_does_not_imply_atom_absence

theorem presentation_raw_candidate_is_not_atom_truth :
    exampleAtomPresentation.rawCandidateIsNotAtomTruth := by
  exact exampleAtomPresentation.raw_candidate_is_not_atom_truth

theorem presentation_missing_is_not_atom_absence :
    exampleAtomPresentation.missingIsNotAtomAbsence := by
  exact exampleAtomPresentation.missing_is_not_atom_absence

theorem presentation_missing_is_not_measured_zero :
    exampleAtomPresentation.missingIsNotMeasuredZero := by
  exact exampleAtomPresentation.missing_is_not_measured_zero

theorem archMap_observes_atoms :
    exampleArchMapObservationLayer.observesAtoms := by
  exact exampleArchMapObservationLayer.observes_atoms

theorem archMap_does_not_create_atoms :
    exampleAtomAxiomSystem.noObservationBoundaryCreatesAtoms := by
  exact exampleArchMapObservationLayer.archmap_does_not_create_atoms

theorem archMap_does_not_define_aat :
    exampleArchMapObservationLayer.archMapDoesNotDefineAAT := by
  exact exampleArchMapObservationLayer.archmap_does_not_define_aat

theorem archMap_missing_is_not_measured_zero :
    exampleArchMapObservationLayer.presentation.missingIsNotMeasuredZero := by
  exact exampleArchMapObservationLayer.missing_is_not_measured_zero

def observedApiPort : AtomPort where
  name := "observed-api"
  kind := AtomPortKind.subject
  family := AtomKind.existence
  axis := Axis.static
  required := False
  acceptsFamily := fun kind => kind = AtomKind.existence
  acceptsAxis := fun axis => axis = Axis.static

def observedApiValence : AtomValence where
  ports := fun port => port = observedApiPort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨observedApiPort, rfl⟩

def observedApiShape (_atom : ExampleAtom) : AtomShape where
  family := AtomKind.existence
  axis := Axis.static
  subject := { name := "api" }
  predicate := "component"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := AtomDirection.neutral
  arity := 1
  valence := observedApiValence
  singleFactShape := True
  singleFactShapeEvidence := trivial

def observedApiShapePresentation :
    AtomShapePresentation exampleAtomAxiomSystem where
  shapeOf := observedApiShape
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

def selectedObservedApiAtoms : ExampleAtom -> Prop
  | ExampleAtom.apiComponent => True

def observedApiCompositionGraph :
    AAT.CompositionGraph
      observedApiShapePresentation selectedObservedApiAtoms where
  compatiblePairs := by
    intro left right _hLeft _hRight hDistinct
    cases left
    cases right
    exact False.elim (hDistinct rfl)
  graphBoundary := True

def observedApiArchMapSelection :
    Observation.ArchMapObservedAtomSelection
      exampleArchMapObservationLayer observedApiShapePresentation where
  atoms := selectedObservedApiAtoms
  observedAtomEvidence := by
    intro atom hAtom
    cases atom
    exact ⟨observedApiAtom, rfl, rfl⟩
  finiteConfiguration := True
  compositionGraph := observedApiCompositionGraph
  requiredPortsMatched := by
    intro atom _port _hAtom hRequired
    cases atom
    cases hRequired
  notArbitrarySet := True
  notArbitrarySetEvidence := trivial

def observedApiGeneratedMolecule :
    AAT.GeneratedMolecule observedApiShapePresentation :=
  observedApiArchMapSelection.toGeneratedMolecule

theorem archMap_observed_atom_handoff_to_generated_molecule :
    observedApiGeneratedMolecule.atoms ExampleAtom.apiComponent := by
  trivial

theorem archMap_observed_atom_handoff_keeps_observation_evidence :
    ∃ observed : Observation.ObservedAtom exampleAtomAxiomSystem String,
      exampleArchMapObservationLayer.presentation.observed observed ∧
        observed.atom = ExampleAtom.apiComponent := by
  exact
    observedApiArchMapSelection.toGeneratedMolecule_atom_observed
      (by trivial)

def observedApiGeneratedObjectInput :
    Observation.ArchMapGeneratedArchitectureObjectInput
      observedApiArchMapSelection where
  carrierList := [⟨ExampleAtom.apiComponent, by trivial⟩]
  carrierListNodup := by
    simp
  carrierListCovers := by
    intro carrier
    cases carrier with
    | mk atom _hAtom =>
        cases atom
        simp
  objectBoundary := True

def observedApiGeneratedObject :
    AAT.GeneratedArchitectureObject observedApiShapePresentation :=
  observedApiGeneratedObjectInput.toGeneratedArchitectureObject

theorem archMap_observed_atom_handoff_to_generated_object :
    ∃ carrier : AAT.GeneratedCarrier observedApiGeneratedObject,
      carrier.val = ExampleAtom.apiComponent := by
  exact ⟨⟨ExampleAtom.apiComponent, by trivial⟩, rfl⟩

theorem archMap_generated_object_carrier_remains_observed
    (carrier : AAT.GeneratedCarrier observedApiGeneratedObject) :
    ∃ observed : Observation.ObservedAtom exampleAtomAxiomSystem String,
      exampleArchMapObservationLayer.presentation.observed observed ∧
        observed.atom = carrier.val := by
  exact
    observedApiGeneratedObjectInput.toGeneratedArchitectureObject_carrier_observed
      carrier

end Formal.Arch.ArchMapObservationExamples
