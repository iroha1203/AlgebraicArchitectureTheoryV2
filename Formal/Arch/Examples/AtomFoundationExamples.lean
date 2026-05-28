import Formal.Arch.Atom.Foundation

namespace Formal.Arch.AtomFoundationExamples

inductive Component where
  | api
  deriving DecidableEq, Repr

inductive Edge where
  | apiToDatabase
  deriving DecidableEq, Repr

inductive Diagram where
  | writePath
  deriving DecidableEq, Repr

inductive ExampleAtom where
  | apiComponent
  deriving DecidableEq, Repr

def examplePredicate :
    ExampleAtom -> AtomPredicate Component Edge Diagram
  | ExampleAtom.apiComponent => AtomPredicate.component Component.api

/--
Minimal positive example of the pure Atom axiom root.

The atom system supplies an atom as a primitive typed fact. It carries no
support, evidence boundary, observation status, tool output, or SFT event field.
-/
def exampleAtomAxiomSystem : AtomAxiomSystem where
  Atom := ExampleAtom
  Predicate := AtomPredicate Component Edge Diagram
  kind := fun atom => (examplePredicate atom).kind
  axis := fun atom => (examplePredicate atom).axis
  predicate := examplePredicate
  predicateKind := AtomPredicate.kind
  predicateAxis := AtomPredicate.axis
  predicateKindAligned := by
    intro atom
    rfl
  predicateAxisAligned := by
    intro atom
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

theorem exampleAtomAxiomSystem_atom_primitive :
    exampleAtomAxiomSystem.Primitive ExampleAtom.apiComponent := by
  exact exampleAtomAxiomSystem.primitive ExampleAtom.apiComponent

theorem exampleAAT_begins_from_atom_axioms :
    (exampleAtomAxiomSystem : AATFromAtomAxioms).Primitive
      ExampleAtom.apiComponent := by
  exact AATFromAtomAxioms.begins_from_atom_axioms
    exampleAtomAxiomSystem ExampleAtom.apiComponent

theorem exampleAtomAxiomSystem_boundary_independent :
    exampleAtomAxiomSystem.boundaryIndependent ExampleAtom.apiComponent := by
  exact exampleAtomAxiomSystem.boundary_independent
    ExampleAtom.apiComponent

theorem exampleAtomAxiomSystem_law_independent :
    exampleAtomAxiomSystem.lawIndependent ExampleAtom.apiComponent := by
  exact exampleAtomAxiomSystem.law_independent
    ExampleAtom.apiComponent

theorem exampleAtomAxiomSystem_observation_boundary_does_not_create_atoms :
    exampleAtomAxiomSystem.noObservationBoundaryCreatesAtoms := by
  exact exampleAtomAxiomSystem.observation_boundary_does_not_create_atoms

theorem exampleAtomAxiomSystem_tool_output_does_not_create_atoms :
    exampleAtomAxiomSystem.noToolOutputCreatesAtoms := by
  exact exampleAtomAxiomSystem.tool_output_does_not_create_atoms

end Formal.Arch.AtomFoundationExamples
