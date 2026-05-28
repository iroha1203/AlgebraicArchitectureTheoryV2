import Formal.Arch.Observation.AtomPresentation

namespace Formal.Arch
namespace Observation

universe u v s e

/--
ArchMap as an observation layer over an Atom axiom system.

ArchMap observes atoms and presents candidates.  It does not define AAT and
does not create atom existence.
-/
structure ArchMapObservationLayer
    (system : AtomAxiomSystem.{u, v})
    (Source : Type s) (Evidence : Type e) where
  presentation : AtomPresentation system Evidence
  selectedSource : Source -> Prop
  observesAtoms : Prop
  observesAtomsEvidence : observesAtoms
  archMapDoesNotCreateAtomsEvidence :
    system.noObservationBoundaryCreatesAtoms
  archMapDoesNotDefineAAT : Prop
  archMapDoesNotDefineAATEvidence : archMapDoesNotDefineAAT
  rawCandidateBoundary : Prop
  validationBoundary : Prop
  coverageBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

namespace ArchMapObservationLayer

/-- ArchMap observes atoms. -/
theorem observes_atoms
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    (layer : ArchMapObservationLayer system Source Evidence) :
    layer.observesAtoms :=
  layer.observesAtomsEvidence

/-- ArchMap observation does not create atoms. -/
theorem archmap_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    (layer : ArchMapObservationLayer system Source Evidence) :
    system.noObservationBoundaryCreatesAtoms :=
  layer.archMapDoesNotCreateAtomsEvidence

/-- ArchMap does not define AAT. -/
theorem archmap_does_not_define_aat
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    (layer : ArchMapObservationLayer system Source Evidence) :
    layer.archMapDoesNotDefineAAT :=
  layer.archMapDoesNotDefineAATEvidence

/-- Raw candidates in an ArchMap presentation are not atom truth by themselves. -/
theorem raw_candidate_is_not_atom_truth
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    (layer : ArchMapObservationLayer system Source Evidence) :
    layer.presentation.rawCandidateIsNotAtomTruth :=
  layer.presentation.raw_candidate_is_not_atom_truth

/-- Missing observations in an ArchMap presentation are not atom absence. -/
theorem missing_is_not_atom_absence
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    (layer : ArchMapObservationLayer system Source Evidence) :
    layer.presentation.missingIsNotAtomAbsence :=
  layer.presentation.missing_is_not_atom_absence

end ArchMapObservationLayer

end Observation
end Formal.Arch
