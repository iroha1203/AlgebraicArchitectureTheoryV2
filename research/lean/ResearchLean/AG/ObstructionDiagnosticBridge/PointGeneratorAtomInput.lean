import ResearchLean.AG.ObstructionDiagnosticBridge.PointAtomLawInput
import Formal.AG.Atom.ArchitectureObject
import Formal.Util.AssertStandardAxioms

/-!
# Combined point and primitive-generator Atom input

This module places the selected eight geometric points and the four primitive
Law occurrences in one actual `AtomCarrier`.  Generator atoms retain their
source, Law index, and evaluated Law value in the Atom coordinates.  The
architecture relation between generator atoms is exactly the two-edge
presentation from Cycle 14; point atoms do not acquire presentation edges.

This is the Atom-provenance layer only.  Contexts and coverage for the combined
carrier are constructed separately, so this module does not claim that the
Cycle 12 point-only site has already become the final G-125 site.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge
namespace PointGeneratorAtomInput

open SelectedFiniteGeometry
open PointAtomLawInput

/-- The two kinds of Atom in the selected combined input. -/
inductive AtomKind where
  | point
  | generator
  deriving DecidableEq

/-- A point subject or a primitive-generator source subject. -/
abbrev Subject := Point ⊕ PointAtomActualNerve.Source

/-- No predicate for points; the declared Law index for generators. -/
abbrev Predicate := Option laws.Law

/-- No value for points; the evaluated Law value for generators. -/
abbrev Payload := Unit ⊕ Bool

/-- The combined Atom type for geometry and primitive Law occurrences. -/
abbrev Atom := Point ⊕ PrimitiveGenerator laws

/-- Actual carrier containing both selected point and generator Atoms. -/
def carrier : AtomCarrier where
  AtomKind := AtomKind
  Axis := Unit
  Subject := Subject
  Predicate := Predicate
  Payload := Payload
  Atom := Atom
  kind
    | .inl _ => .point
    | .inr _ => .generator
  axis := fun _ => ()
  subject
    | .inl point => .inl point
    | .inr generator => .inr generator.2
  predicate
    | .inl _ => none
    | .inr generator => some generator.1
  payload
    | .inl _ => .inl ()
    | .inr generator => .inr (laws.eval generator.1 generator.2)

/-- Embed one selected geometric point as an actual Atom. -/
def pointAtom (point : Point) : carrier.Atom :=
  .inl point

/-- Embed one primitive Law occurrence as an actual Atom. -/
def generatorAtom (generator : PrimitiveGenerator laws) : carrier.Atom :=
  .inr generator

/-- Architecture object containing every selected point and generator Atom. -/
def object : ArchitectureObject carrier where
  configuration := {
    family := ⟨fun _ => True⟩
    relation := fun left right =>
      match left, right with
      | .inr leftGenerator, .inr rightGenerator =>
          presentation.relation leftGenerator rightGenerator
      | _, _ => False
    identification := fun _ _ => False
  }
  StructureMaps := Unit
  SelectedQuantities := Unit
  structureMaps := ()
  selectedQuantities := ()

/-- Every selected point Atom belongs to the architecture family. -/
@[simp]
theorem pointAtom_mem_family (point : Point) :
    object.configuration.family.mem (pointAtom point) :=
  trivial

/-- Every selected primitive-generator Atom belongs to the architecture family. -/
@[simp]
theorem generatorAtom_mem_family (generator : PrimitiveGenerator laws) :
    object.configuration.family.mem (generatorAtom generator) :=
  trivial

/-- Generator subjects retain the source occurrence used by the presentation. -/
@[simp]
theorem generatorAtom_subject (generator : PrimitiveGenerator laws) :
    carrier.subject (generatorAtom generator) = .inr generator.2 :=
  rfl

/-- Generator predicates retain the declared Law index. -/
@[simp]
theorem generatorAtom_predicate (generator : PrimitiveGenerator laws) :
    carrier.predicate (generatorAtom generator) = some generator.1 :=
  rfl

/-- Generator payloads retain the actual evaluated Law value. -/
@[simp]
theorem generatorAtom_payload (generator : PrimitiveGenerator laws) :
    carrier.payload (generatorAtom generator) =
      .inr (laws.eval generator.1 generator.2) :=
  rfl

/-- The architecture relation on generator Atoms is exactly the selected presentation. -/
@[simp]
theorem generatorAtom_relation_iff
    (left right : PrimitiveGenerator laws) :
    object.configuration.relation (generatorAtom left) (generatorAtom right) ↔
      presentation.relation left right :=
  Iff.rfl

/-- Point Atoms carry no primitive-generator relation edges. -/
@[simp]
theorem pointAtom_not_related_left
    (point : Point) (atom : carrier.Atom) :
    ¬ object.configuration.relation (pointAtom point) atom := by
  cases atom <;> simp [object, pointAtom]

/-- Point Atoms carry no primitive-generator relation edges. -/
@[simp]
theorem pointAtom_not_related_right
    (atom : carrier.Atom) (point : Point) :
    ¬ object.configuration.relation atom (pointAtom point) := by
  cases atom <;> simp [object, pointAtom]

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.PointGeneratorAtomInput

end PointGeneratorAtomInput
end AAT.AG.ObstructionDiagnosticBridge
