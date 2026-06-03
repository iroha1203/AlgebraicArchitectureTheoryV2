import Formal.Arch.AAT.GeneratedMolecule

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

end Formal.Arch.IncompatibleAtomCompositionExamples
