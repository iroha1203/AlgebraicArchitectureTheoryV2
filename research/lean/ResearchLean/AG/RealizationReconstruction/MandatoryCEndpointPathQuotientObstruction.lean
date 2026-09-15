import ResearchLean.AG.RealizationReconstruction.MandatoryCEndpointPathObstruction
import Mathlib.CategoryTheory.Quotient
import Formal.Util.AssertStandardAxioms

/-!
# Relation quotients of the endpoint-typed path candidate

Cycle 18 constructed the actual multiobject free path category whose edges
retain every existing tagged primitive and the exact endpoints of operation
references.  This module quotients that category by an arbitrary family of
hom-relations.  Mathlib closes those relations under composition and forms the
resulting quotient category independently of any semantic decoder.

Every quotient morphism has a representative path.  Combining that quotient
representative with Cycle 18's exact-reference serialization and Cycle 17's
constructed list decoder yields, at every quotient object, a surjection from
finite tagged primitive lists onto its endomorphisms.  Consequently no functor
from any such quotient into the independent mandatory-C semantic category is
both full and retract-generating.

This result covers arbitrary relations on the concrete Cycle 18 path grammar,
but it does not certify that an arbitrary relation is the source-derived legal
congruence required by final `D_Theta`.  It also does not exhaust additional
source-provenanced parameter roles, change the candidate placement of Atom and
Source loops, or establish final `Sigma`, `D_Theta`, or `R_Theta` membership.

## Implementation notes

The decoder is the composite of the already constructed raw-path decoder and
the canonical quotient functor.  Surjectivity is proved by quotient induction,
so no representative, normalization, completed semantic morphism, or
surjectivity certificate is stored in the presentation.  An arbitrary
`CategoryTheory.HomRel` is deliberately accepted at the syntactic layer;
Mathlib's quotient construction supplies the composition closure and category
laws.  This maximizes the relation freedom of this candidate while keeping the
relation fixed before the arbitrary semantic functor below.

Defining the relation as equality after a completed semantic decoder would be
circular for G-123 and is not a licensed final application of this theorem.
Likewise, quotient fullness is used only to represent syntactic quotient
morphisms; it is not the fullness conclusion demanded of the semantic functor.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open RealizationComparisonIdempotents

/-- The quotient of the endpoint-typed path candidate by a supplied family of
relations on its typed hom-sets. -/
abbrev TaggedPrimitivePathQuotientPresentation
    (relations : HomRel TaggedPrimitivePathPresentation) :=
  CategoryTheory.Quotient relations

/-- Decode a finite tagged primitive list to a raw endomorphism path using the
Cycle 18 embedding, then send that path to its canonical quotient class. -/
noncomputable def taggedPrimitivePathQuotientEndomorphismDecoder
    (relations : HomRel TaggedPrimitivePathPresentation)
    (object : TaggedPrimitivePathQuotientPresentation relations) :
    List TaggedPrimitiveReference → (object ⟶ object) :=
  fun references =>
    (CategoryTheory.Quotient.functor relations).map
      (taggedPrimitiveListDecoderOfEndomorphismEmbedding object.as
        (taggedPrimitivePathEndomorphismEmbedding object.as) references)

/-- Every quotient endomorphism has a raw endpoint-typed path representative,
and every such path is decoded from a finite exact-reference list. -/
theorem taggedPrimitivePathQuotientEndomorphismDecoder_surjective
    (relations : HomRel TaggedPrimitivePathPresentation)
    (object : TaggedPrimitivePathQuotientPresentation relations) :
    Function.Surjective
      (taggedPrimitivePathQuotientEndomorphismDecoder relations object) := by
  intro quotientPath
  obtain ⟨rawPath, rawPath_eq⟩ :=
    (CategoryTheory.Quotient.full_functor relations).map_surjective quotientPath
  obtain ⟨references, references_eq⟩ :=
    taggedPrimitiveListDecoderOfEndomorphismEmbedding_surjective object.as
      (taggedPrimitivePathEndomorphismEmbedding object.as) rawPath
  refine ⟨references, ?_⟩
  simp only [taggedPrimitivePathQuotientEndomorphismDecoder, references_eq]
  exact rawPath_eq

/-- No relation quotient of the concrete endpoint-typed path candidate admits
a functor into the independent mandatory-C category that is simultaneously
full and retract-generating. -/
theorem taggedPrimitivePathQuotientPresentation_not_full_and_retractGenerated
    (relations : HomRel TaggedPrimitivePathPresentation)
    (F : CategoryTheory.Functor
      (TaggedPrimitivePathQuotientPresentation relations)
      (CanonicalNormalizationAdmissiblePackage FiniteModel.carrier)) :
    ¬ (F.Full ∧ RetractGeneratedBy F) :=
  not_full_and_retractGenerated_of_listPrimitiveGeneratedEndomorphisms F
    (fun object =>
      ⟨taggedPrimitivePathQuotientEndomorphismDecoder relations object,
        taggedPrimitivePathQuotientEndomorphismDecoder_surjective relations object⟩)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
