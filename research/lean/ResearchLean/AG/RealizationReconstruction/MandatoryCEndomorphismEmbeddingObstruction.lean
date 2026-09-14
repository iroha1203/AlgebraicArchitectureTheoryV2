import ResearchLean.AG.RealizationReconstruction.MandatoryCPrimitiveAlphabet
import Formal.Util.AssertStandardAxioms

/-!
# Transfer from endpoint-typed endomorphism encodings

The preceding mandatory-C obstruction expects, at every presentation object,
a surjection from finite tagged primitive lists onto the endomorphism type.
This module derives that premise from the opposite-facing datum normally
produced by a typed serialization: an injection of every endomorphism into
finite tagged primitive lists.

The result applies to arbitrary multiobject categories and therefore isolates
the remaining syntax obligation precisely.  It does not construct the
endpoint-typed serialization, certify the provenance of its tokens, or place
the mandatory-C source-choice family in final `R_Theta`.

## Implementation notes

`Function.invFun` is used only after an actual injective serialization has
been supplied.  Its left-inverse theorem constructs a surjection back onto
the original endomorphism type.  Accepting an arbitrary injection is suitable
for this general transfer lemma, but the G-123 application must construct each
injection from the fixed finite syntax and may not store it as a presentation
certificate or encode a completed semantic morphism as one list token.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open RealizationComparisonIdempotents

universe uP vP

/-- Decode tagged primitive lists by the inverse of a proved injective
serialization of one presentation endomorphism type. -/
noncomputable def taggedPrimitiveListDecoderOfEndomorphismEmbedding
    {P : Type uP} [Category.{vP} P] (p : P)
    (encode : (p ⟶ p) ↪ List TaggedPrimitiveReference) :
    List TaggedPrimitiveReference → (p ⟶ p) :=
  by
    letI : Nonempty (p ⟶ p) := ⟨𝟙 p⟩
    exact Function.invFun encode

/-- The decoder constructed from an injective endomorphism serialization is
surjective.  This is the cardinal-direction conversion consumed below. -/
theorem taggedPrimitiveListDecoderOfEndomorphismEmbedding_surjective
    {P : Type uP} [Category.{vP} P] (p : P)
    (encode : (p ⟶ p) ↪ List TaggedPrimitiveReference) :
    Function.Surjective
      (taggedPrimitiveListDecoderOfEndomorphismEmbedding p encode) :=
  by
    letI : Nonempty (p ⟶ p) := ⟨𝟙 p⟩
    exact Function.invFun_surjective encode.injective

/-- Multiobject mandatory-C transfer.  If every endomorphism type of an
arbitrary presentation category has an injective finite tagged-primitive
serialization, then no functor into the independent mandatory-C category is
both full and retract-generating. -/
theorem not_full_and_retractGenerated_of_endomorphismEmbedding
    {P : Type uP} [Category.{vP} P]
    (F : P ⥤ CanonicalNormalizationAdmissiblePackage FiniteModel.carrier)
    (encode : ∀ p : P, (p ⟶ p) ↪ List TaggedPrimitiveReference) :
    ¬ (F.Full ∧ RetractGeneratedBy F) :=
  not_full_and_retractGenerated_of_listPrimitiveGeneratedEndomorphisms F
    (fun p =>
      ⟨taggedPrimitiveListDecoderOfEndomorphismEmbedding p (encode p),
        taggedPrimitiveListDecoderOfEndomorphismEmbedding_surjective p (encode p)⟩)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
