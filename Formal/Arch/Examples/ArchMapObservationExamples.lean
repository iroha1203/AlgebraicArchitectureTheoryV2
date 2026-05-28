import Formal.Arch.Observation.ArchMap
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

theorem archMap_observes_atoms :
    exampleArchMapObservationLayer.observesAtoms := by
  exact exampleArchMapObservationLayer.observes_atoms

theorem archMap_does_not_create_atoms :
    exampleAtomAxiomSystem.noObservationBoundaryCreatesAtoms := by
  exact exampleArchMapObservationLayer.archmap_does_not_create_atoms

theorem archMap_does_not_define_aat :
    exampleArchMapObservationLayer.archMapDoesNotDefineAAT := by
  exact exampleArchMapObservationLayer.archmap_does_not_define_aat

end Formal.Arch.ArchMapObservationExamples
