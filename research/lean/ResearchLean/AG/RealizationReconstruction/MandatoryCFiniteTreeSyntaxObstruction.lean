import ResearchLean.AG.RealizationReconstruction.MandatoryCPrimitiveAlphabet
import Mathlib.Data.Tree.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Formal.Util.AssertStandardAxioms

/-!
# Mandatory-C obstruction for recursive finite-tree syntax

The earlier mandatory-C obstruction covers words, quotients of words, and
endpoint-typed paths over the complete tagged primitive alphabet.  A finite
term grammar can also use nested constructors.  This module treats the more
permissive binary-tree carrier whose internal-node payload may contain any
tagged primitive reference.

The tree is serialized independently of every semantic decoder.  Each node
records the length of its left serialization, so the two subtrees and every
primitive payload can be recovered.  Cardinal reindexing then proves that all
such finite trees still have no more information than the complete primitive
alphabet itself.  Consequently tree-generated presentation endomorphisms
cannot support a decoder that is both full and retract-generating into the
independent mandatory-C category.

This rules out recursive finite constructor shape as an escape from the
Cycle-14 obstruction.  It does not prove that every parameter-relative syntax
allowed by G-123 embeds in this tree type: an additional primitive parameter
family must still be shown to carry no completed semantic map and to satisfy the
same provenance bound before the result can support a fixed-target stop.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct
open RealizationComparisonIdempotents

noncomputable section

universe u uP vP

/-- Prefix serialization of a finite binary term tree.  `none` is the empty
tree token.  A node stores its primitive payload and the length of the left
subtree code before the two subtree codes. -/
def taggedPrimitiveFiniteTreeCode {A : Type u} :
    Tree A → List (Option (A × Nat))
  | .nil => [none]
  | .node primitive left right =>
      some (primitive, (taggedPrimitiveFiniteTreeCode left).length) ::
        taggedPrimitiveFiniteTreeCode left ++
        taggedPrimitiveFiniteTreeCode right

/-- The explicit finite-tree serialization loses neither constructor shape
nor primitive payload.  The stored left-code length fixes the concatenation
boundary before the induction hypotheses recover both subtrees. -/
theorem taggedPrimitiveFiniteTreeCode_injective {A : Type u} :
    Function.Injective (taggedPrimitiveFiniteTreeCode (A := A)) := by
  intro first
  induction first with
  | nil =>
      intro second equality
      cases second with
      | nil => rfl
      | node primitive left right =>
          simp [taggedPrimitiveFiniteTreeCode] at equality
  | node primitive left right leftIH rightIH =>
      intro second equality
      cases second with
      | nil =>
          simp [taggedPrimitiveFiniteTreeCode] at equality
      | node primitive' left' right' =>
          change some (primitive, (taggedPrimitiveFiniteTreeCode left).length) ::
                (taggedPrimitiveFiniteTreeCode left ++
                  taggedPrimitiveFiniteTreeCode right) =
              some (primitive', (taggedPrimitiveFiniteTreeCode left').length) ::
                (taggedPrimitiveFiniteTreeCode left' ++
                  taggedPrimitiveFiniteTreeCode right') at equality
          have consEquality := List.cons.inj equality
          have nodeEquality := Option.some.inj consEquality.1
          have primitiveEquality : primitive = primitive' :=
            congrArg Prod.fst nodeEquality
          have lengthEquality :
              (taggedPrimitiveFiniteTreeCode left).length =
                (taggedPrimitiveFiniteTreeCode left').length :=
            congrArg Prod.snd nodeEquality
          have tailsEquality :
              taggedPrimitiveFiniteTreeCode left ++
                  taggedPrimitiveFiniteTreeCode right =
                taggedPrimitiveFiniteTreeCode left' ++
                  taggedPrimitiveFiniteTreeCode right' :=
            consEquality.2
          have leftCodeEquality :
              taggedPrimitiveFiniteTreeCode left =
                taggedPrimitiveFiniteTreeCode left' := by
            calc
              taggedPrimitiveFiniteTreeCode left =
                  (taggedPrimitiveFiniteTreeCode left ++
                    taggedPrimitiveFiniteTreeCode right).take
                      (taggedPrimitiveFiniteTreeCode left).length := by simp
              _ = (taggedPrimitiveFiniteTreeCode left' ++
                    taggedPrimitiveFiniteTreeCode right').take
                      (taggedPrimitiveFiniteTreeCode left).length :=
                    congrArg _ tailsEquality
              _ = taggedPrimitiveFiniteTreeCode left' := by
                    rw [lengthEquality]
                    simp
          have leftEquality : left = left' := leftIH leftCodeEquality
          rw [leftCodeEquality] at tailsEquality
          have rightCodeEquality :
              taggedPrimitiveFiniteTreeCode right =
                taggedPrimitiveFiniteTreeCode right' :=
            List.append_cancel_left tailsEquality
          have rightEquality : right = right' := rightIH rightCodeEquality
          cases primitiveEquality
          cases leftEquality
          cases rightEquality
          rfl

/-- The complete tagged primitive alphabet is infinite because it contains an
injective copy of every mandatory-C architecture object. -/
noncomputable instance taggedPrimitiveReferenceInfinite :
    Infinite TaggedPrimitiveReference :=
  Infinite.of_injective TaggedPrimitiveReference.object (by
    intro first second equality
    cases equality
    rfl)

/-- Finite serialization tokens, including natural subtree lengths, embed
back into the complete primitive alphabet.  This is a cardinal consequence of
the preceding constructed infinitude, not an added semantic reference. -/
noncomputable def taggedPrimitiveFiniteTreeTokenListEmbedding :
    List (Option (TaggedPrimitiveReference × Nat)) ↪
      TaggedPrimitiveReference :=
  Classical.choice ((Cardinal.lift_mk_le.{0}).mp (by simp))

/-- Every recursive finite primitive tree embeds in one primitive-reference
index through the explicit injective serialization. -/
noncomputable def taggedPrimitiveFiniteTreeEmbedding :
    Tree TaggedPrimitiveReference ↪ TaggedPrimitiveReference :=
  (Function.Embedding.mk
      (taggedPrimitiveFiniteTreeCode (A := TaggedPrimitiveReference))
      (taggedPrimitiveFiniteTreeCode_injective
        (A := TaggedPrimitiveReference))).trans
    taggedPrimitiveFiniteTreeTokenListEmbedding

/-- Reindex primitive references onto all finite primitive trees by inverse of
the proved tree embedding. -/
noncomputable def taggedPrimitiveFiniteTreeEnumeration :
    TaggedPrimitiveReference → Tree TaggedPrimitiveReference :=
  Function.invFun taggedPrimitiveFiniteTreeEmbedding

/-- The tree enumeration reaches every finite primitive tree. -/
theorem taggedPrimitiveFiniteTreeEnumeration_surjective :
    Function.Surjective taggedPrimitiveFiniteTreeEnumeration :=
  (Function.leftInverse_invFun taggedPrimitiveFiniteTreeEmbedding.injective).surjective

/-- Read the first primitive reference in a list, using one fixed authored
object reference only for the empty list.  Singleton lists prove surjectivity. -/
def firstTaggedPrimitiveReference :
    List TaggedPrimitiveReference → TaggedPrimitiveReference
  | [] => .object FiniteModel.object
  | first :: _ => first

/-- Every primitive reference is the first element of its singleton list. -/
theorem firstTaggedPrimitiveReference_surjective :
    Function.Surjective firstTaggedPrimitiveReference := by
  intro reference
  exact ⟨[reference], rfl⟩

/-- Finite primitive lists therefore enumerate all recursive finite primitive
trees without using a semantic decoder. -/
noncomputable def listTaggedPrimitiveFiniteTreeEnumeration :
    List TaggedPrimitiveReference → Tree TaggedPrimitiveReference :=
  taggedPrimitiveFiniteTreeEnumeration ∘ firstTaggedPrimitiveReference

/-- Surjectivity of the list-to-tree enumeration is the composition of the
two independently proved provenance maps. -/
theorem listTaggedPrimitiveFiniteTreeEnumeration_surjective :
    Function.Surjective listTaggedPrimitiveFiniteTreeEnumeration :=
  taggedPrimitiveFiniteTreeEnumeration_surjective.comp
    firstTaggedPrimitiveReference_surjective

/-- No decoder from recursive finite trees over the complete tagged primitive
alphabet reaches every mandatory-C admissible endomorphism. -/
theorem taggedSourceChoiceAdmissibleEndomorphisms_not_finiteTreeEnumerable
    (decode : Tree TaggedPrimitiveReference →
      (taggedUniformFlipPackage ⟶ taggedUniformFlipPackage)) :
    ¬ Function.Surjective decode := by
  intro decodeSurjective
  exact taggedSourceChoiceAdmissibleEndomorphisms_not_listPrimitiveEnumerable
    (decode ∘ listTaggedPrimitiveFiniteTreeEnumeration)
    (decodeSurjective.comp listTaggedPrimitiveFiniteTreeEnumeration_surjective)

/-- Any code type proved to be generated by recursive finite primitive trees
also fails to enumerate all mandatory-C admissible endomorphisms. -/
theorem taggedSourceChoiceAdmissibleEndomorphisms_not_finiteTreeGenerated
    {Code : Type*}
    (ofTree : Tree TaggedPrimitiveReference → Code)
    (ofTreeSurjective : Function.Surjective ofTree)
    (decode : Code →
      (taggedUniformFlipPackage ⟶ taggedUniformFlipPackage)) :
    ¬ Function.Surjective decode := by
  intro decodeSurjective
  exact taggedSourceChoiceAdmissibleEndomorphisms_not_finiteTreeEnumerable
    (decode ∘ ofTree) (decodeSurjective.comp ofTreeSurjective)

/-- Multiobject mandatory-C obstruction for a presentation whose every
endomorphism is generated by recursive finite trees over the complete tagged
primitive alphabet.  The tree-generation premise remains a syntax provenance
obligation; it is not a semantic fullness or retract certificate. -/
theorem not_full_and_retractGenerated_of_finiteTreeGeneratedEndomorphisms
    {P : Type uP} [Category.{vP} P]
    (F : P ⥤ CanonicalNormalizationAdmissiblePackage FiniteModel.carrier)
    (treeGenerated : ∀ p : P,
      ∃ decode : Tree TaggedPrimitiveReference → (p ⟶ p),
        Function.Surjective decode) :
    ¬ (F.Full ∧ RetractGeneratedBy F) :=
  not_full_and_retractGenerated_of_listPrimitiveGeneratedEndomorphisms F
    (fun p => by
      obtain ⟨decode, decodeSurjective⟩ := treeGenerated p
      exact ⟨decode ∘ listTaggedPrimitiveFiniteTreeEnumeration,
        decodeSurjective.comp listTaggedPrimitiveFiniteTreeEnumeration_surjective⟩)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
