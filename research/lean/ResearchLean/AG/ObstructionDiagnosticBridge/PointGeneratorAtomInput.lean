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

## Implementation notes

This is the Cycle 15 realization of the combined Atom input from the Issue
#4791 paper design, section 10.  A sum is used for both the Atom type and the
tagged coordinates because it preserves the already selected point and
primitive-generator data without copying either into a new certificate type.
The architecture relation delegates directly to the Cycle 14 presentation on
the generator summand; defining a second relation from Law-value equality would
lose the primitive-edge provenance established there.  Point support contexts
and coverage are deliberately not copied from the point-only carrier: their
transport to this larger carrier is the next proof obligation and must establish
the site and continuity laws rather than store them as fields here.
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

/-- Cycle 15's combined Atom input for the paper design, section 10.

This is the principal carrier definition.  Its tagged coordinates retain the
predecessor point and generator data rather than replacing them with a
proof-oriented certificate.
-/
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

/-- Architecture object containing every selected point and generator Atom.

This is the principal Cycle 15 realization API: the family is the full selected
finite input, while the relation reuses the Cycle 14 primitive presentation.
It intentionally supplies no combined-site or continuity certificate.
-/
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

/-- Membership API for the point summand of the Cycle 15 full selected family. -/
@[simp]
theorem pointAtom_mem_family (point : Point) :
    object.configuration.family.mem (pointAtom point) :=
  trivial

/-- Membership API for the generator summand of the Cycle 15 full selected family. -/
@[simp]
theorem generatorAtom_mem_family (generator : PrimitiveGenerator laws) :
    object.configuration.family.mem (generatorAtom generator) :=
  trivial

/-- Projection API showing that a generator Atom retains its Cycle 14 source. -/
@[simp]
theorem generatorAtom_subject (generator : PrimitiveGenerator laws) :
    carrier.subject (generatorAtom generator) = .inr generator.2 :=
  rfl

/-- Projection API showing that a generator Atom retains its declared Law index. -/
@[simp]
theorem generatorAtom_predicate (generator : PrimitiveGenerator laws) :
    carrier.predicate (generatorAtom generator) = some generator.1 :=
  rfl

/-- Projection API showing that a generator Atom retains its evaluated Law value. -/
@[simp]
theorem generatorAtom_payload (generator : PrimitiveGenerator laws) :
    carrier.payload (generatorAtom generator) =
      .inr (laws.eval generator.1 generator.2) :=
  rfl

/-- Comparison API identifying the generator relation with the Cycle 14 presentation. -/
@[simp]
theorem generatorAtom_relation_iff
    (left right : PrimitiveGenerator laws) :
    object.configuration.relation (generatorAtom left) (generatorAtom right) ↔
      presentation.relation left right :=
  Iff.rfl

/-- Boundary API excluding point-originating edges from the primitive presentation. -/
@[simp]
theorem pointAtom_not_related_left
    (point : Point) (atom : carrier.Atom) :
    ¬ object.configuration.relation (pointAtom point) atom := by
  cases atom <;> simp [object, pointAtom]

/-- Boundary API excluding point-targeting edges from the primitive presentation. -/
@[simp]
theorem pointAtom_not_related_right
    (atom : carrier.Atom) (point : Point) :
    ¬ object.configuration.relation atom (pointAtom point) := by
  cases atom <;> simp [object, pointAtom]

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.PointGeneratorAtomInput

end PointGeneratorAtomInput
end AAT.AG.ObstructionDiagnosticBridge
