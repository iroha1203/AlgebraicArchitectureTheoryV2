namespace Formal.Arch

universe u v w

/--
Atom axes are coordinates used to organize primitive architectural facts.

Axes help later AAT / ArchSig readings select views over already-existing
atoms. They are not observation boundaries, scores, theorem discharges, or
extractor completeness claims.
-/
inductive Axis where
  | static
  | semantic
  | specification
  | runtime
  | boundary
  | dataflow
  | governance
  | evolution
  | policy
  deriving DecidableEq, Repr

/--
Core atom families selected for the boundary-free Atom foundation.

This is the initial Lean-facing grammar for primitive typed architectural
facts. It is not a claim that the taxonomy is globally complete. Obstructions,
observation artifacts, roles, patterns, repairs, and SFT deltas are separate
structures, not atom kinds.
-/
inductive AtomKind where
  | existence
  | relation
  | capability
  | dataState
  | effect
  | boundaryAuthority
  | contractSpecification
  | semanticInterpretation
  | runtimeInteraction
  deriving DecidableEq, Repr

namespace AtomKind

/--
In the current Atom Core every `AtomKind` constructor in this file is primitive.

This predicate is intentionally small: it records the current Lean-facing atom
grammar, not a claim that the taxonomy is globally complete.
-/
def IsPrimitive (_kind : AtomKind) : Prop := True

theorem isPrimitive (kind : AtomKind) : kind.IsPrimitive := by
  trivial

end AtomKind

/--
Lean-facing policy for extending the atom grammar.

The policy records which currently declared `AtomKind` / `Axis` coordinates are
allowed in a selected presentation and keeps that extension boundary separate
from derived witnesses such as obstruction circuits, observation gaps, repair
steps, and SFT forecasts.
-/
structure AtomGrammarExtensionPolicy where
  permittedKind : AtomKind -> Prop
  permittedAxis : Axis -> Prop
  primitiveKindBoundary :
    ∀ kind, permittedKind kind -> kind.IsPrimitive
  openGrammarBoundary : Prop
  derivedWitnessesSeparated : Prop
  toolingSchemaBoundary : Prop
  noGlobalTaxonomyCompleteness : Prop

namespace AtomGrammarExtensionPolicy

/-- The current policy permits all atom kinds and axes declared in this file. -/
def current : AtomGrammarExtensionPolicy where
  permittedKind := fun _ => True
  permittedAxis := fun _ => True
  primitiveKindBoundary := fun kind _ => AtomKind.isPrimitive kind
  openGrammarBoundary := True
  derivedWitnessesSeparated := True
  toolingSchemaBoundary := True
  noGlobalTaxonomyCompleteness := True

theorem current_permits_kind (kind : AtomKind) :
    current.permittedKind kind := by
  trivial

theorem current_permits_axis (axis : Axis) :
    current.permittedAxis axis := by
  trivial

theorem primitive_of_permitted
    (policy : AtomGrammarExtensionPolicy) {kind : AtomKind}
    (h : policy.permittedKind kind) :
    kind.IsPrimitive :=
  policy.primitiveKindBoundary kind h

theorem current_permittedKind_isPrimitive (kind : AtomKind) :
    kind.IsPrimitive :=
  primitive_of_permitted current (current_permits_kind kind)

end AtomGrammarExtensionPolicy

/--
Machine-readable predicate grammar for primitive atoms.

The human-readable predicate string used by reports remains only a label.
`AtomPredicate` is the Lean-facing predicate constructor that records which
primitive fact shape is being asserted.
-/
inductive AtomPredicate (C : Type u) (E : Type v) (D : Type w) where
  | component (component : C)
  | relation (edge : E)
  | capability (subject : C) (capability : String)
  | dataState (diagram : D) (state : String)
  | effect (diagram : D) (effect : String)
  | boundaryAuthority (subject : C) (authority : String)
  | contractSpecification (diagram : D) (contract : String)
  | semanticInterpretation (diagram : D) (meaning : String)
  | runtimeInteraction (edge : E) (interaction : String)
  | custom (kind : AtomKind) (axis : Axis) (name : String)

namespace AtomPredicate

/-- The atom family determined by a typed predicate constructor. -/
def kind {C : Type u} {E : Type v} {D : Type w} :
    AtomPredicate C E D -> AtomKind
  | component _ => AtomKind.existence
  | relation _ => AtomKind.relation
  | capability _ _ => AtomKind.capability
  | dataState _ _ => AtomKind.dataState
  | effect _ _ => AtomKind.effect
  | boundaryAuthority _ _ => AtomKind.boundaryAuthority
  | contractSpecification _ _ => AtomKind.contractSpecification
  | semanticInterpretation _ _ => AtomKind.semanticInterpretation
  | runtimeInteraction _ _ => AtomKind.runtimeInteraction
  | custom kind _ _ => kind

/-- The atom axis determined by a typed predicate constructor. -/
def axis {C : Type u} {E : Type v} {D : Type w} :
    AtomPredicate C E D -> Axis
  | component _ => Axis.static
  | relation _ => Axis.static
  | capability _ _ => Axis.static
  | dataState _ _ => Axis.dataflow
  | effect _ _ => Axis.semantic
  | boundaryAuthority _ _ => Axis.boundary
  | contractSpecification _ _ => Axis.specification
  | semanticInterpretation _ _ => Axis.semantic
  | runtimeInteraction _ _ => Axis.runtime
  | custom _ axis _ => axis

end AtomPredicate

/--
Atom axiom system for pure AAT.

This is the root object AAT begins from. It supplies atoms as primitive typed
architectural facts before any observation boundary, selected design law, tool
output, ArchMap candidate, ArchSig validation, or SFT event is attached.
-/
structure AtomAxiomSystem where
  Atom : Type u
  Predicate : Type v
  kind : Atom -> AtomKind
  axis : Atom -> Axis
  predicate : Atom -> Predicate
  predicateKind : Predicate -> AtomKind
  predicateAxis : Predicate -> Axis
  predicateKindAligned :
    ∀ atom, predicateKind (predicate atom) = kind atom
  predicateAxisAligned :
    ∀ atom, predicateAxis (predicate atom) = axis atom
  singleFact : Atom -> Prop
  singleFactEvidence : ∀ atom, singleFact atom
  predicatePreserving : Atom -> Prop
  predicatePreservingEvidence : ∀ atom, predicatePreserving atom
  boundaryIndependent : Atom -> Prop
  boundaryIndependentEvidence : ∀ atom, boundaryIndependent atom
  lawIndependent : Atom -> Prop
  lawIndependentEvidence : ∀ atom, lawIndependent atom
  noObservationBoundaryCreatesAtoms : Prop
  noObservationBoundaryCreatesAtomsEvidence :
    noObservationBoundaryCreatesAtoms
  noLawCreatesAtoms : Prop
  noLawCreatesAtomsEvidence : noLawCreatesAtoms
  noToolOutputCreatesAtoms : Prop
  noToolOutputCreatesAtomsEvidence : noToolOutputCreatesAtoms
  noSFTEventCreatesAtoms : Prop
  noSFTEventCreatesAtomsEvidence : noSFTEventCreatesAtoms
  openTaxonomyBoundary : Prop

namespace AtomAxiomSystem

/-- Predicate spelling for primitive atoms in an axiom system. -/
def Primitive (system : AtomAxiomSystem) (atom : system.Atom) : Prop :=
  (system.kind atom).IsPrimitive ∧
  system.singleFact atom ∧
  system.predicatePreserving atom ∧
  system.boundaryIndependent atom ∧
  system.lawIndependent atom

/-- Every atom supplied by an `AtomAxiomSystem` satisfies the primitive criteria. -/
theorem primitive (system : AtomAxiomSystem) (atom : system.Atom) :
    system.Primitive atom := by
  exact
    ⟨AtomKind.isPrimitive (system.kind atom),
      system.singleFactEvidence atom,
      system.predicatePreservingEvidence atom,
      system.boundaryIndependentEvidence atom,
      system.lawIndependentEvidence atom⟩

/-- A pure atom's predicate determines its atom family. -/
theorem predicate_kind (system : AtomAxiomSystem) (atom : system.Atom) :
    system.predicateKind (system.predicate atom) = system.kind atom :=
  system.predicateKindAligned atom

/-- A pure atom's predicate determines its axis. -/
theorem predicate_axis (system : AtomAxiomSystem) (atom : system.Atom) :
    system.predicateAxis (system.predicate atom) = system.axis atom :=
  system.predicateAxisAligned atom

/-- Atoms in the axiom system are single typed facts. -/
theorem single_fact (system : AtomAxiomSystem) (atom : system.Atom) :
    system.singleFact atom :=
  (system.primitive atom).2.1

/-- Atoms in the axiom system preserve their predicate when read as atomic. -/
theorem predicate_preserving (system : AtomAxiomSystem) (atom : system.Atom) :
    system.predicatePreserving atom :=
  (system.primitive atom).2.2.1

/-- Atom existence is independent of observation boundaries. -/
theorem boundary_independent (system : AtomAxiomSystem) (atom : system.Atom) :
    system.boundaryIndependent atom :=
  (system.primitive atom).2.2.2.1

/-- Atom existence is independent of selected design laws. -/
theorem law_independent (system : AtomAxiomSystem) (atom : system.Atom) :
    system.lawIndependent atom :=
  (system.primitive atom).2.2.2.2

/-- Observation boundaries do not create atoms for this axiom system. -/
theorem observation_boundary_does_not_create_atoms
    (system : AtomAxiomSystem) :
    system.noObservationBoundaryCreatesAtoms :=
  system.noObservationBoundaryCreatesAtomsEvidence

/-- Design laws do not create atoms for this axiom system. -/
theorem law_does_not_create_atoms
    (system : AtomAxiomSystem) :
    system.noLawCreatesAtoms :=
  system.noLawCreatesAtomsEvidence

/-- Tool output does not create atoms for this axiom system. -/
theorem tool_output_does_not_create_atoms
    (system : AtomAxiomSystem) :
    system.noToolOutputCreatesAtoms :=
  system.noToolOutputCreatesAtomsEvidence

/-- SFT events do not create atoms for this axiom system. -/
theorem sft_event_does_not_create_atoms
    (system : AtomAxiomSystem) :
    system.noSFTEventCreatesAtoms :=
  system.noSFTEventCreatesAtomsEvidence

end AtomAxiomSystem

/--
Naming alias for the pure AAT root: AAT starts from an `AtomAxiomSystem`.

Later AAT core structures should be parameterized by this object, not by
observation or presentation records.
-/
abbrev AATFromAtomAxioms := AtomAxiomSystem

namespace AATFromAtomAxioms

/-- AAT's root atoms are supplied by the atom axiom system. -/
theorem begins_from_atom_axioms
    (system : AATFromAtomAxioms) (atom : system.Atom) :
    system.Primitive atom :=
  system.primitive atom

/-- AAT's root is independent of observation boundaries. -/
theorem independent_of_observation_boundary
    (system : AATFromAtomAxioms) :
    system.noObservationBoundaryCreatesAtoms :=
  system.observation_boundary_does_not_create_atoms

/-- AAT's root is independent of selected design laws. -/
theorem independent_of_law
    (system : AATFromAtomAxioms) :
    system.noLawCreatesAtoms :=
  system.law_does_not_create_atoms

end AATFromAtomAxioms

end Formal.Arch
