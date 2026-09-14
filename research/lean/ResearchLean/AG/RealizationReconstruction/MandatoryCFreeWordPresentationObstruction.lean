import ResearchLean.AG.RealizationReconstruction.MandatoryCPrimitiveAlphabet
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.CategoryTheory.SingleObj
import Formal.Util.AssertStandardAxioms

/-!
# The free-word presentation over the full tagged primitive alphabet

Cycle 14 left its `listGenerated` premise abstract.  This module constructs
the maximally permissive finite-word category on the complete existing tagged
primitive alphabet and discharges that premise for the constructed category.
Its morphisms are arbitrary finite primitive words, with the empty word as
identity and word concatenation as composition.

The resulting theorem says that no decoder from this actual free-word
presentation into the independent mandatory-C admissible-package category can
be both full and retract-generating.  It refutes this concrete presentation
candidate.  It does not identify the admissible-package category with the
final `R_Theta`, nor does it refute a syntax with additional source-provenanced
parameter families not present in the existing tagged primitive declaration.

## Implementation notes

`CategoryTheory.SingleObj` is used because `FreeMonoid TaggedPrimitiveReference`
is definitionally the finite-list type and carries the free monoid structure:
the category laws are inherited from the empty word and concatenation rather
than accepted as certificates.
The one-object grammar is deliberately more permissive than an endpoint-typed
subgrammar, so it does not discard a word merely because adjacent primitive
endpoints fail to match.  Adding a completed semantic endomorphism as a new
letter was rejected because that would move the required reconstruction into
the input alphabet.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open RealizationComparisonIdempotents

/-- Finite words over every actual primitive role of the mandatory tagged
branch.  Each letter retains the provenance and endpoints fixed in Cycle 14. -/
abbrev TaggedPrimitiveWord := FreeMonoid TaggedPrimitiveReference

/-- The concrete free-word presentation category.  It is defined before and
independently of any decoder into the semantic admissible-package category. -/
abbrev TaggedPrimitiveWordPresentation := SingleObj TaggedPrimitiveWord

/-- The sole object of the free-word presentation. -/
abbrev taggedPrimitiveWordObject : TaggedPrimitiveWordPresentation :=
  SingleObj.star TaggedPrimitiveWord

/-- Read a finite primitive word as an actual endomorphism of any object of
the single-object presentation category.  This is definitionally the identity
function on words, not a semantic decoder or a completed map reference. -/
def taggedPrimitiveWordEndomorphismDecoder
    (p : TaggedPrimitiveWordPresentation) :
    TaggedPrimitiveWord → (p ⟶ p) :=
  id

/-- Every presentation endomorphism is represented by its identical finite
primitive word.  Thus Cycle 14's generation premise is constructed for this
actual category rather than received as a theorem argument. -/
theorem taggedPrimitiveWordEndomorphismDecoder_surjective
    (p : TaggedPrimitiveWordPresentation) :
    Function.Surjective (taggedPrimitiveWordEndomorphismDecoder p) :=
  Function.surjective_id

/-- The categorical identity of the free-word presentation is the empty
primitive word. -/
@[simp] theorem taggedPrimitiveWordPresentation_id
    (p : TaggedPrimitiveWordPresentation) :
    (𝟙 p : p ⟶ p) = ([] : TaggedPrimitiveWord) :=
  rfl

/-- Composition of two displayed primitive words is their concatenation in
the `gf = g o f` order fixed by the GOAL. -/
@[simp] theorem taggedPrimitiveWordPresentation_comp
    (first second : TaggedPrimitiveWord) :
    SingleObj.toEnd TaggedPrimitiveWord first ≫
        SingleObj.toEnd TaggedPrimitiveWord second =
      SingleObj.toEnd TaggedPrimitiveWord (second * first) :=
  rfl

/-- Cycle 15 no-go for the constructed free-word category.  Any functor from
this actual finite primitive syntax into the independent mandatory-C category
fails at least one of fullness and retract generation.  The proof constructs
Cycle 14's list-generation witness from the identity word decoder. -/
theorem taggedPrimitiveWordPresentation_not_full_and_retractGenerated
    (F : TaggedPrimitiveWordPresentation ⥤
      CanonicalNormalizationAdmissiblePackage FiniteModel.carrier) :
    ¬ (F.Full ∧ RetractGeneratedBy F) :=
  not_full_and_retractGenerated_of_listPrimitiveGeneratedEndomorphisms F
    (fun p => ⟨taggedPrimitiveWordEndomorphismDecoder p,
      taggedPrimitiveWordEndomorphismDecoder_surjective p⟩)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
