import Formal.Arch.AAT.Core

namespace Formal.Arch
namespace Observation

universe u v e

/-- Observation-side status for an atom candidate or observation. -/
inductive AtomObservationStatus where
  | rawCandidate
  | observed
  | validated
  | rejected
  | uncertain
  | missing
  deriving DecidableEq, Repr

/--
Raw observation-side candidate.

A raw candidate carries a predicate-shaped observation and evidence, but is not
an atom truth and is not part of the pure AAT core.
-/
structure RawAtomCandidate (system : AtomAxiomSystem.{u, v})
    (Evidence : Type e) where
  predicate : system.Predicate
  evidence : Evidence
  candidateBoundary : Prop
  notAtomTruthBoundary : Prop
  nonConclusions : Prop

namespace RawAtomCandidate

/-- Raw candidates do not create atoms in the root axiom system. -/
theorem does_not_create_atoms {system : AtomAxiomSystem.{u, v}}
    {Evidence : Type e}
    (_candidate : RawAtomCandidate system Evidence) :
    system.noObservationBoundaryCreatesAtoms :=
  system.observation_boundary_does_not_create_atoms

/-- Raw candidate status is kept distinct from validated observation. -/
def Status : AtomObservationStatus :=
  AtomObservationStatus.rawCandidate

end RawAtomCandidate

/-- An observed atom is an observation of an already-existing atom. -/
structure ObservedAtom (system : AtomAxiomSystem.{u, v})
    (Evidence : Type e) where
  atom : system.Atom
  evidence : Evidence
  observationBoundary : Prop
  observedStatus : AtomObservationStatus
  statusBoundary : Prop
  nonConclusions : Prop

namespace ObservedAtom

/-- Observing an atom does not create that atom. -/
theorem observation_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {Evidence : Type e}
    (_observed : ObservedAtom system Evidence) :
    system.noObservationBoundaryCreatesAtoms :=
  system.observation_boundary_does_not_create_atoms

/-- Observed atoms remain primitive atoms of the root axiom system. -/
theorem atom_primitive
    {system : AtomAxiomSystem.{u, v}}
    {Evidence : Type e}
    (observed : ObservedAtom system Evidence) :
    system.Primitive observed.atom :=
  system.primitive observed.atom

end ObservedAtom

/--
Observation gap.

Missing observation is not an atom absence theorem.  It only records that the
selected observation layer did not see or validate an atom.
-/
structure AtomObservationGap (system : AtomAxiomSystem.{u, v})
    (Evidence : Type e) where
  evidence : Evidence
  gapBoundary : Prop
  doesNotImplyAtomAbsence : Prop
  doesNotImplyAtomAbsenceEvidence : doesNotImplyAtomAbsence
  nonConclusions : Prop

namespace AtomObservationGap

/-- An observation gap does not imply atom absence. -/
theorem gap_does_not_imply_atom_absence
    {system : AtomAxiomSystem.{u, v}}
    {Evidence : Type e}
    (gap : AtomObservationGap system Evidence) :
    gap.doesNotImplyAtomAbsence :=
  gap.doesNotImplyAtomAbsenceEvidence

end AtomObservationGap

/--
Observation-side atom presentation.

This is outside the pure AAT core.  It separates raw candidates, observed
atoms, rejected candidates, uncertain candidates, and missing observations.
-/
structure AtomPresentation (system : AtomAxiomSystem.{u, v})
    (Evidence : Type e) where
  rawCandidate : RawAtomCandidate system Evidence -> Prop
  observed : ObservedAtom system Evidence -> Prop
  validated : ObservedAtom system Evidence -> Prop
  rejected : RawAtomCandidate system Evidence -> Prop
  uncertain : RawAtomCandidate system Evidence -> Prop
  missing : AtomObservationGap system Evidence -> Prop
  validationBoundary : Prop
  rawCandidateIsNotAtomTruth : Prop
  rawCandidateIsNotAtomTruthEvidence : rawCandidateIsNotAtomTruth
  rejectedIsNotMeasuredZero : Prop
  rejectedIsNotMeasuredZeroEvidence : rejectedIsNotMeasuredZero
  uncertainIsNotMeasuredZero : Prop
  uncertainIsNotMeasuredZeroEvidence : uncertainIsNotMeasuredZero
  missingIsNotMeasuredZero : Prop
  missingIsNotMeasuredZeroEvidence : missingIsNotMeasuredZero
  missingIsNotAtomAbsence : Prop
  missingIsNotAtomAbsenceEvidence : missingIsNotAtomAbsence
  nonConclusions : Prop

namespace AtomPresentation

/-- Raw candidates are not promoted to atom truth by the presentation alone. -/
theorem raw_candidate_is_not_atom_truth
    {system : AtomAxiomSystem.{u, v}}
    {Evidence : Type e}
    (presentation : AtomPresentation system Evidence) :
    presentation.rawCandidateIsNotAtomTruth :=
  presentation.rawCandidateIsNotAtomTruthEvidence

/-- Rejected candidates are not measured-zero atoms. -/
theorem rejected_is_not_measured_zero
    {system : AtomAxiomSystem.{u, v}}
    {Evidence : Type e}
    (presentation : AtomPresentation system Evidence) :
    presentation.rejectedIsNotMeasuredZero :=
  presentation.rejectedIsNotMeasuredZeroEvidence

/-- Uncertain candidates are not measured-zero atoms. -/
theorem uncertain_is_not_measured_zero
    {system : AtomAxiomSystem.{u, v}}
    {Evidence : Type e}
    (presentation : AtomPresentation system Evidence) :
    presentation.uncertainIsNotMeasuredZero :=
  presentation.uncertainIsNotMeasuredZeroEvidence

/-- Missing observations are not measured-zero atoms. -/
theorem missing_is_not_measured_zero
    {system : AtomAxiomSystem.{u, v}}
    {Evidence : Type e}
    (presentation : AtomPresentation system Evidence) :
    presentation.missingIsNotMeasuredZero :=
  presentation.missingIsNotMeasuredZeroEvidence

/-- Missing observation is not atom absence. -/
theorem missing_is_not_atom_absence
    {system : AtomAxiomSystem.{u, v}}
    {Evidence : Type e}
    (presentation : AtomPresentation system Evidence) :
    presentation.missingIsNotAtomAbsence :=
  presentation.missingIsNotAtomAbsenceEvidence

end AtomPresentation

end Observation
end Formal.Arch
