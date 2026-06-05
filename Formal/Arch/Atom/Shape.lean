import Formal.Arch.Atom.Valence

namespace Formal.Arch

universe u v

/-- Subject coordinate of a primitive architectural fact. -/
structure AtomSubject where
  name : String

/-- Object slot coordinate carried by an atom shape. -/
structure AtomObjectSlot where
  name : String
  family : AtomKind
  axis : Axis
  required : Prop
  acceptsFamily : AtomKind -> Prop
  acceptsAxis : Axis -> Prop

/-- Payload slot coordinate carried by an atom shape. -/
structure AtomPayloadSlot where
  name : String
  family : AtomKind
  axis : Axis
  required : Prop
  acceptsFamily : AtomKind -> Prop
  acceptsAxis : Axis -> Prop

/-- Direction of an atom's architectural assertion. -/
inductive AtomDirection where
  | neutral
  | incoming
  | outgoing
  | bidirectional
  deriving DecidableEq, Repr

/--
Intrinsic shape of a primitive atom.

Source references, confidence, and measurement provenance are not fields here.
The fields below are the typed fact shape from which AAT composition is allowed
to start.
-/
structure AtomShape where
  family : AtomKind
  axis : Axis
  subject : AtomSubject
  predicate : String
  objectSlots : AtomObjectSlot -> Prop
  payloadSlots : AtomPayloadSlot -> Prop
  direction : AtomDirection
  arity : Nat
  valence : AtomValence
  singleFactShape : Prop
  singleFactShapeEvidence : singleFactShape

/--
Shape presentation for an atom root system.

The presentation upgrades the current thin atom root into shaped generators
without changing atom existence. It is the first bridge from `AtomAxiomSystem`
to Atom-generated algebra.
-/
structure AtomShapePresentation (system : AtomAxiomSystem.{u, v}) where
  shapeOf : system.Atom -> AtomShape
  shapeKindAligned :
    ∀ atom, (shapeOf atom).family = system.kind atom
  shapeAxisAligned :
    ∀ atom, (shapeOf atom).axis = system.axis atom
  shapeSingleFact :
    ∀ atom, (shapeOf atom).singleFactShape -> system.singleFact atom

/-- Canonical spelling for the shape carried by an atom under a presentation. -/
def AtomShapeOf {system : AtomAxiomSystem.{u, v}}
    (presentation : AtomShapePresentation system)
    (atom : system.Atom) : AtomShape :=
  presentation.shapeOf atom

namespace AtomShapePresentation

/-- The presented shape keeps the atom family fixed. -/
theorem shape_kind_aligned {system : AtomAxiomSystem.{u, v}}
    (presentation : AtomShapePresentation system)
    (atom : system.Atom) :
    (AtomShapeOf presentation atom).family = system.kind atom :=
  presentation.shapeKindAligned atom

/-- The presented shape keeps the atom axis fixed. -/
theorem shape_axis_aligned {system : AtomAxiomSystem.{u, v}}
    (presentation : AtomShapePresentation system)
    (atom : system.Atom) :
    (AtomShapeOf presentation atom).axis = system.axis atom :=
  presentation.shapeAxisAligned atom

/-- A shaped atom is still a single primitive architectural fact. -/
theorem shape_single_fact {system : AtomAxiomSystem.{u, v}}
    (presentation : AtomShapePresentation system)
    (atom : system.Atom) :
    system.singleFact atom :=
  presentation.shapeSingleFact atom
    (AtomShapeOf presentation atom).singleFactShapeEvidence

end AtomShapePresentation

end Formal.Arch
