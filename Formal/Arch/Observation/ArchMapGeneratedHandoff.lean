import Formal.Arch.Observation.ArchMap
import Formal.Arch.AAT.GeneratedObject

namespace Formal.Arch
namespace Observation

universe u v s e

/--
Observed ArchMap atoms selected for the Atom-generated algebra handoff.

This is the positive counterpart to the observation-boundary theorems:
ArchMap still does not create atoms or define AAT, but once an atom is observed
as an existing atom, the selected observed atoms can be passed to the generated
molecule kernel together with shape and compatibility evidence.
-/
structure ArchMapObservedAtomSelection
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    (layer : ArchMapObservationLayer system Source Evidence)
    (shapePresentation : AtomShapePresentation system) where
  atoms : system.Atom -> Prop
  observedAtomEvidence :
    ∀ atom, atoms atom ->
      ∃ observed : ObservedAtom system Evidence,
        layer.presentation.observed observed ∧ observed.atom = atom
  finiteConfiguration : Prop
  compositionGraph : AAT.CompositionGraph shapePresentation atoms
  requiredPortsMatched :
    AAT.RequiredPortsMatched shapePresentation atoms
  notArbitrarySet : Prop
  notArbitrarySetEvidence : notArbitrarySet

namespace ArchMapObservedAtomSelection

/-- Selected handoff atoms are backed by ArchMap observed-atom evidence. -/
theorem selected_atoms_observed
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    (selection : ArchMapObservedAtomSelection layer shapePresentation)
    {atom : system.Atom}
    (hAtom : selection.atoms atom) :
    ∃ observed : ObservedAtom system Evidence,
      layer.presentation.observed observed ∧ observed.atom = atom :=
  selection.observedAtomEvidence atom hAtom

/-- Observed handoff atoms are still primitive atoms of the root system. -/
theorem selected_atoms_primitive
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    (selection : ArchMapObservedAtomSelection layer shapePresentation)
    {atom : system.Atom}
    (hAtom : selection.atoms atom) :
    system.Primitive atom := by
  rcases selection.selected_atoms_observed hAtom with
    ⟨observed, _hObserved, hObservedAtom⟩
  rw [← hObservedAtom]
  exact observed.atom_primitive

/--
Build the generated molecule from observed atoms plus shape, composition, and
required-port evidence.  The ArchMap layer supplies observation evidence; the
AAT generated molecule still requires the AtomShape composition certificate.
-/
def toGeneratedMolecule
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    (selection : ArchMapObservedAtomSelection layer shapePresentation) :
    AAT.GeneratedMolecule shapePresentation where
  atoms := selection.atoms
  finiteConfiguration := selection.finiteConfiguration
  atomsPrimitive := by
    intro atom hAtom
    exact selection.selected_atoms_primitive hAtom
  compositionGraph := selection.compositionGraph
  requiredPortsMatched := selection.requiredPortsMatched
  notArbitrarySet := selection.notArbitrarySet
  notArbitrarySetEvidence := selection.notArbitrarySetEvidence

/-- The generated molecule handoff keeps the same selected atom predicate. -/
theorem toGeneratedMolecule_atoms
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    (selection : ArchMapObservedAtomSelection layer shapePresentation)
    {atom : system.Atom} :
    (selection.toGeneratedMolecule).atoms atom = selection.atoms atom :=
  rfl

/-- Generated molecule handoff atoms remain observed by ArchMap. -/
theorem toGeneratedMolecule_atom_observed
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    (selection : ArchMapObservedAtomSelection layer shapePresentation)
    {atom : system.Atom}
    (hAtom : selection.toGeneratedMolecule.atoms atom) :
    ∃ observed : ObservedAtom system Evidence,
      layer.presentation.observed observed ∧ observed.atom = atom :=
  selection.selected_atoms_observed hAtom

/-- The ArchMap handoff preserves the boundary that observation does not create atoms. -/
theorem toGeneratedMolecule_observation_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    (_selection : ArchMapObservedAtomSelection layer shapePresentation) :
    system.noObservationBoundaryCreatesAtoms :=
  layer.archmap_does_not_create_atoms

end ArchMapObservedAtomSelection

/--
Finite carrier evidence for turning an ArchMap observed-atom molecule handoff
into a generated architecture object.
-/
structure ArchMapGeneratedArchitectureObjectInput
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    (selection : ArchMapObservedAtomSelection layer shapePresentation) where
  carrierList : List { atom : system.Atom // selection.atoms atom }
  carrierListNodup : carrierList.Nodup
  carrierListCovers :
    ∀ carrier : { atom : system.Atom // selection.atoms atom },
      carrier ∈ carrierList
  objectBoundary : Prop

namespace ArchMapGeneratedArchitectureObjectInput

/-- Build the generated architecture object from the observed-atom handoff. -/
def toGeneratedArchitectureObject
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    {selection : ArchMapObservedAtomSelection layer shapePresentation}
    (input : ArchMapGeneratedArchitectureObjectInput selection) :
    AAT.GeneratedArchitectureObject shapePresentation where
  molecule := selection.toGeneratedMolecule
  carrierList := input.carrierList
  carrierListNodup := input.carrierListNodup
  carrierListCovers := input.carrierListCovers
  objectBoundary := input.objectBoundary

/-- Carriers of the generated object remain backed by observed atoms. -/
theorem toGeneratedArchitectureObject_carrier_observed
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    {selection : ArchMapObservedAtomSelection layer shapePresentation}
    (input : ArchMapGeneratedArchitectureObjectInput selection)
    (carrier : AAT.GeneratedCarrier input.toGeneratedArchitectureObject) :
    ∃ observed : ObservedAtom system Evidence,
      layer.presentation.observed observed ∧ observed.atom = carrier.val :=
  selection.selected_atoms_observed carrier.property

/-- Object construction preserves the observation-does-not-create-atoms boundary. -/
theorem toGeneratedArchitectureObject_observation_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {Source : Type s} {Evidence : Type e}
    {layer : ArchMapObservationLayer system Source Evidence}
    {shapePresentation : AtomShapePresentation system}
    {selection : ArchMapObservedAtomSelection layer shapePresentation}
    (_input : ArchMapGeneratedArchitectureObjectInput selection) :
    system.noObservationBoundaryCreatesAtoms :=
  layer.archmap_does_not_create_atoms

end ArchMapGeneratedArchitectureObjectInput

end Observation
end Formal.Arch
