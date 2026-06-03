import Formal.Arch.Atom.Foundation

namespace Formal.Arch

/-- Port roles used by Atom valence. -/
inductive AtomPortKind where
  | subject
  | relationSource
  | relationTarget
  | runtimeSource
  | runtimeTarget
  | object
  | payload
  | authority
  | effect
  | contract
  deriving DecidableEq, Repr

/--
A port is an attach point in an atom's intrinsic shape.

The `accepts*` predicates describe which neighboring atom coordinates may bind
to this port. This is part of the atom's shape, not observation metadata.
-/
structure AtomPort where
  name : String
  kind : AtomPortKind
  family : AtomKind
  axis : Axis
  required : Prop
  acceptsFamily : AtomKind -> Prop
  acceptsAxis : Axis -> Prop

/--
Valence is the port surface exposed by an atom shape.

Required ports are internal shape obligations. A generated molecule must later
show that required ports are matched by compatible neighboring atoms.
-/
structure AtomValence where
  ports : AtomPort -> Prop
  requiredPort : AtomPort -> Prop
  requiredPortHasPort : ∀ port, requiredPort port -> ports port
  hasPort : ∃ port, ports port

namespace AtomValence

/-- Required ports are part of the atom's declared port surface. -/
theorem required_port_has_port (valence : AtomValence)
    {port : AtomPort} (hRequired : valence.requiredPort port) :
    valence.ports port :=
  valence.requiredPortHasPort port hRequired

end AtomValence

/-- Two ports can bind when their roles match and their coordinates accept each other. -/
def PortCompatible (left right : AtomPort) : Prop :=
  left.kind = right.kind ∧
  left.acceptsFamily right.family ∧
  right.acceptsFamily left.family ∧
  left.acceptsAxis right.axis ∧
  right.acceptsAxis left.axis

namespace PortCompatible

/-- Port compatibility is symmetric. -/
theorem symm {left right : AtomPort}
    (h : PortCompatible left right) : PortCompatible right left := by
  exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩

end PortCompatible

end Formal.Arch
