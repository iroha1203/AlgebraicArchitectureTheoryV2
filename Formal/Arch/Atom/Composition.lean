import Formal.Arch.Atom.Shape

namespace Formal.Arch

/-- Object slots are compatible when the receiving predicates accept each coordinate. -/
def SlotCompatible (left right : AtomObjectSlot) : Prop :=
  left.acceptsFamily right.family ∧
  right.acceptsFamily left.family ∧
  left.acceptsAxis right.axis ∧
  right.acceptsAxis left.axis

/-- Payload slots are compatible when the receiving predicates accept each coordinate. -/
def PayloadSlotCompatible (left right : AtomPayloadSlot) : Prop :=
  left.acceptsFamily right.family ∧
  right.acceptsFamily left.family ∧
  left.acceptsAxis right.axis ∧
  right.acceptsAxis left.axis

/--
Predicate labels may coincide only when their typed coordinates agree.

This prevents a composition from silently merging two same-named predicates with
different atom families or axes.
-/
def PredicateSlotCompatible (left right : AtomShape) : Prop :=
  left.predicate = right.predicate ->
    left.family = right.family ∧ left.axis = right.axis

/--
Compatible binary composition of atom shapes.

The composition is witnessed by a compatible port pair and by slot/predicate
compatibility. A generated molecule uses this predicate pairwise, so arbitrary
sets of atoms cannot be promoted to generated molecules.
-/
structure CompatibleComposition (left right : AtomShape) where
  leftPort : AtomPort
  rightPort : AtomPort
  leftHasPort : left.valence.ports leftPort
  rightHasPort : right.valence.ports rightPort
  portsCompatible : PortCompatible leftPort rightPort
  objectSlotsCompatible :
    ∀ leftSlot rightSlot,
      left.objectSlots leftSlot ->
      right.objectSlots rightSlot ->
        SlotCompatible leftSlot rightSlot
  payloadSlotsCompatible :
    ∀ leftSlot rightSlot,
      left.payloadSlots leftSlot ->
      right.payloadSlots rightSlot ->
        PayloadSlotCompatible leftSlot rightSlot
  predicateSlotsCompatible :
    PredicateSlotCompatible left right

namespace CompatibleComposition

/-- A compatible composition always exposes at least one compatible port pair. -/
theorem has_port_pair {left right : AtomShape}
    (composition : CompatibleComposition left right) :
    ∃ leftPort rightPort,
      left.valence.ports leftPort ∧
      right.valence.ports rightPort ∧
      PortCompatible leftPort rightPort := by
  exact
    ⟨composition.leftPort, composition.rightPort,
      composition.leftHasPort, composition.rightHasPort,
      composition.portsCompatible⟩

/-- If no declared port pair can bind, the two shapes cannot compose. -/
theorem no_compatible_port_not_compatible {left right : AtomShape}
    (hNoPort :
      ∀ leftPort rightPort,
        left.valence.ports leftPort ->
        right.valence.ports rightPort ->
          ¬ PortCompatible leftPort rightPort) :
    CompatibleComposition left right -> False := by
  intro composition
  exact hNoPort
    composition.leftPort
    composition.rightPort
    composition.leftHasPort
    composition.rightHasPort
    composition.portsCompatible

/-- An incompatible object-slot pair rejects the composition. -/
theorem incompatible_slots_not_compatible {left right : AtomShape}
    {leftSlot rightSlot : AtomObjectSlot}
    (hLeft : left.objectSlots leftSlot)
    (hRight : right.objectSlots rightSlot)
    (hIncompatible : ¬ SlotCompatible leftSlot rightSlot) :
    CompatibleComposition left right -> False := by
  intro composition
  exact hIncompatible
    (composition.objectSlotsCompatible leftSlot rightSlot hLeft hRight)

end CompatibleComposition

end Formal.Arch
