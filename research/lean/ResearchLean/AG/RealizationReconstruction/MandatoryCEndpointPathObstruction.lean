import ResearchLean.AG.RealizationReconstruction.MandatoryCEndomorphismEmbeddingObstruction
import Mathlib.CategoryTheory.PathCategory.Basic
import Formal.Util.AssertStandardAxioms

/-!
# An endpoint-typed free-path candidate for mandatory C

This module constructs a genuine multiobject free path category over every
existing tagged primitive role.  Operation references retain their exact
architecture-object endpoints; object references are loops at their objects;
Atom and extraction-source references are loops at a named parameter root.
Paths are serialized by their exact edge references, so parallel primitives
are not collapsed to a vertex list.

The construction refutes this concrete endpoint-typed free-path candidate by
supplying Cycle 17's endomorphism embedding.  The parameter root is a syntax
vertex, not a semantic architecture object.  Its chosen placement of Atom and
Source references, and the absence of quotient relations or additional legal
parameter roles, prevent promotion to the final G-123 presentation.

## Implementation notes

A named `parameterRoot` is used instead of `Option.none` so that the auxiliary
syntax vertex cannot be mistaken for missing semantic data.  Atom and Source
references have no architecture-object endpoints in the fixed primitive
declaration, so this candidate places them as root loops; placing each at every
architecture object would introduce an additional occurrence parameter whose
source provenance has not yet been constructed.  Object references are loops
at their exact objects, while Operation references use their existing dependent
source and target without transport or endpoint erasure.

Mathlib's `Quiver.Path.toList` was rejected because it records vertices and its
injectivity API assumes subsingleton hom-types, which would collapse parallel
primitive edges.  `taggedPrimitivePathReferences` instead records each exact
edge value.  A custom path category was also unnecessary: `CategoryTheory.Paths`
already supplies identity, composition, and their laws independently of any
semantic decoder.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open RealizationComparisonIdempotents

/-- Vertices of the concrete endpoint-typed candidate. -/
inductive TaggedPrimitiveVertex where
  | parameterRoot
  | architecture (object : ArchitectureObject FiniteModel.carrier)

/-- Exact syntactic endpoints of every existing mandatory tagged primitive. -/
def taggedPrimitiveEndpoints :
    TaggedPrimitiveReference → TaggedPrimitiveVertex × TaggedPrimitiveVertex
  | .atom _ => (.parameterRoot, .parameterRoot)
  | .source _ => (.parameterRoot, .parameterRoot)
  | .object object => (.architecture object, .architecture object)
  | .operation (source := source) (target := target) _ =>
      (.architecture source, .architecture target)

/-- An edge is an exact primitive reference together with its endpoint typing
derivation.  Distinct parallel references remain distinct edges. -/
abbrev TaggedPrimitiveEdge (source target : TaggedPrimitiveVertex) :=
  { reference : TaggedPrimitiveReference //
    taggedPrimitiveEndpoints reference = (source, target) }

/-- The typed primitive edges form the hom-types of the candidate quiver. -/
instance : Quiver TaggedPrimitiveVertex where
  Hom := TaggedPrimitiveEdge

/-- The actual multiobject free path category of the typed primitive quiver. -/
abbrev TaggedPrimitivePathPresentation := Paths TaggedPrimitiveVertex

/-- Serialize a typed path by its exact primitive edges, most recent edge
first.  Endpoint proofs are erased, but no primitive value is erased. -/
def taggedPrimitivePathReferences {source : TaggedPrimitiveVertex} :
    ∀ {target : TaggedPrimitiveVertex},
      Quiver.Path source target → List TaggedPrimitiveReference
  | _, .nil => []
  | _, .cons path edge => edge.1 :: taggedPrimitivePathReferences path

/-- Exact edge-reference serialization is injective for fixed endpoints. -/
theorem taggedPrimitivePathReferences_injective
    {source target : TaggedPrimitiveVertex} :
    Function.Injective
      (taggedPrimitivePathReferences :
        Quiver.Path source target → List TaggedPrimitiveReference) := by
  intro first
  induction first with
  | nil =>
      intro second equality
      cases second with
      | nil => rfl
      | cons path edge => simp [taggedPrimitivePathReferences] at equality
  | @cons middle target path edge ih =>
      intro second equality
      cases second with
      | nil => simp [taggedPrimitivePathReferences] at equality
      | @cons otherMiddle _ otherPath otherEdge =>
          simp only [taggedPrimitivePathReferences, List.cons.injEq] at equality
          rcases equality with ⟨edgeValueEquality, pathListEquality⟩
          have middleEquality : middle = otherMiddle := by
            have endpointEquality :
                (middle, target) = (otherMiddle, target) :=
              edge.property.symm.trans
                ((congrArg taggedPrimitiveEndpoints edgeValueEquality).trans
                  otherEdge.property)
            exact congrArg Prod.fst endpointEquality
          subst otherMiddle
          have pathEquality := ih pathListEquality
          subst otherPath
          have edgeEquality : edge = otherEdge :=
            Subtype.ext edgeValueEquality
          subst otherEdge
          rfl

/-- Each endomorphism path has a constructed injective serialization into
finite tagged primitive lists. -/
def taggedPrimitivePathEndomorphismEmbedding
    (object : TaggedPrimitivePathPresentation) :
    (object ⟶ object) ↪ List TaggedPrimitiveReference :=
  ⟨taggedPrimitivePathReferences,
    taggedPrimitivePathReferences_injective⟩

/-- The concrete endpoint-typed free-path candidate cannot decode fully and
retract-generate the independent mandatory-C semantic category. -/
theorem taggedPrimitivePathPresentation_not_full_and_retractGenerated
    (F : TaggedPrimitivePathPresentation ⥤
      CanonicalNormalizationAdmissiblePackage FiniteModel.carrier) :
    ¬ (F.Full ∧ RetractGeneratedBy F) :=
  not_full_and_retractGenerated_of_endomorphismEmbedding F
    taggedPrimitivePathEndomorphismEmbedding

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
