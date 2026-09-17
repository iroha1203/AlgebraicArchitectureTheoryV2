import ResearchLean.AG.RealizationReconstruction.MandatoryCFiniteTreeSyntaxObstruction
import Formal.Util.AssertStandardAxioms

/-!
# Mandatory-C obstruction for every provenance-bounded primitive extension

Cycle 185 used the complete current tagged alphabet itself.  This module
allows an arbitrary higher-level primitive family `A`, provided its individual
values have a proved injective provenance encoding into that alphabet.  The
encoding is lifted to tree tokens and finite trees before the mandatory-C
Cantor obstruction is applied.

Thus adding finitely nested constructors or new primitive roles does not evade
the obstruction when each new payload carries no more information than one
existing source primitive.  The embedding premise is deliberately left
visible: final G-123 use must construct it for every allowed role.  A family
that cannot satisfy it requires separate scrutiny for a forbidden completed
morphism or equivalent whole-map payload.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open RealizationComparisonIdempotents

noncomputable section

universe uP vP

/-- Lift a primitive provenance embedding to the structural tokens used by
the injective finite-tree serialization. -/
def boundedPrimitiveTreeTokenEmbedding {A : Type 1}
    (embed : A ↪ TaggedPrimitiveReference) :
    Option (A × Nat) ↪ Option (TaggedPrimitiveReference × Nat) where
  toFun
    | none => none
    | some (value, length) => some (embed value, length)
  inj' := by
    intro first second equality
    cases first with
    | none =>
        cases second <;> simp_all
    | some first =>
        cases second with
        | none => simp_all
        | some second =>
            simp only [Option.some.injEq, Prod.mk.injEq] at equality
            obtain ⟨valueEquality, lengthEquality⟩ := equality
            cases first with
            | mk firstValue firstLength =>
                cases second with
                | mk secondValue secondLength =>
                    simp only at valueEquality lengthEquality ⊢
                    have originalValueEquality := embed.injective valueEquality
                    cases originalValueEquality
                    cases lengthEquality
                    rfl

/-- Map finite token lists pointwise along a primitive provenance embedding. -/
def boundedPrimitiveTreeTokenListEmbedding {A : Type 1}
    (embed : A ↪ TaggedPrimitiveReference) :
    List (Option (A × Nat)) ↪
      List (Option (TaggedPrimitiveReference × Nat)) where
  toFun := List.map (boundedPrimitiveTreeTokenEmbedding embed)
  inj' := by
    intro first
    induction first with
    | nil =>
        intro second equality
        cases second <;> simp_all
    | cons head tail tailIH =>
        intro second equality
        cases second with
        | nil => simp_all
        | cons head' tail' =>
            simp only [List.map_cons, List.cons.injEq] at equality
            obtain ⟨headEquality, tailEquality⟩ := equality
            have originalHeadEquality :=
              (boundedPrimitiveTreeTokenEmbedding embed).injective headEquality
            have originalTailEquality := tailIH tailEquality
            cases originalHeadEquality
            cases originalTailEquality
            rfl

/-- Every finite tree over a provenance-bounded primitive family embeds into
the complete tagged primitive alphabet. -/
def boundedPrimitiveFiniteTreeEmbedding {A : Type 1}
    (embed : A ↪ TaggedPrimitiveReference) :
    Tree A ↪ TaggedPrimitiveReference :=
  (Function.Embedding.mk
      (taggedPrimitiveFiniteTreeCode (A := A))
      (taggedPrimitiveFiniteTreeCode_injective (A := A))).trans
    ((boundedPrimitiveTreeTokenListEmbedding embed).trans
      taggedPrimitiveFiniteTreeTokenListEmbedding)

/-- Finite tagged-reference lists enumerate every tree over a bounded
primitive family, by inverse of the constructed tree embedding. -/
def boundedPrimitiveFiniteTreeEnumeration {A : Type 1}
    (embed : A ↪ TaggedPrimitiveReference) :
    List TaggedPrimitiveReference → Tree A :=
  Function.invFun (boundedPrimitiveFiniteTreeEmbedding embed) ∘
    firstTaggedPrimitiveReference

/-- The bounded-family tree enumeration is surjective. -/
theorem boundedPrimitiveFiniteTreeEnumeration_surjective {A : Type 1}
    (embed : A ↪ TaggedPrimitiveReference) :
    Function.Surjective (boundedPrimitiveFiniteTreeEnumeration embed) :=
  (Function.leftInverse_invFun
      (boundedPrimitiveFiniteTreeEmbedding embed).injective).surjective.comp
    firstTaggedPrimitiveReference_surjective

/-- No decoder from finite trees over any provenance-bounded primitive family
reaches all mandatory-C admissible endomorphisms. -/
theorem taggedSourceChoiceAdmissibleEndomorphisms_not_boundedPrimitiveTreeEnumerable
    {A : Type 1} (embed : A ↪ TaggedPrimitiveReference)
    (decode : Tree A →
      (taggedUniformFlipPackage ⟶ taggedUniformFlipPackage)) :
    ¬ Function.Surjective decode := by
  intro decodeSurjective
  exact taggedSourceChoiceAdmissibleEndomorphisms_not_listPrimitiveEnumerable
    (decode ∘ boundedPrimitiveFiniteTreeEnumeration embed)
    (decodeSurjective.comp
      (boundedPrimitiveFiniteTreeEnumeration_surjective embed))

/-- A presentation with endomorphisms generated by finite trees over one
provenance-bounded primitive family cannot decode both fully and
retract-generatingly into the mandatory-C category. -/
theorem
    not_full_and_retractGenerated_of_boundedPrimitiveTreeGeneratedEndomorphisms
    {A : Type 1} (embed : A ↪ TaggedPrimitiveReference)
    {P : Type uP} [Category.{vP} P]
    (F : P ⥤ CanonicalNormalizationAdmissiblePackage FiniteModel.carrier)
    (treeGenerated : ∀ p : P,
      ∃ decode : Tree A → (p ⟶ p), Function.Surjective decode) :
    ¬ (F.Full ∧ RetractGeneratedBy F) :=
  not_full_and_retractGenerated_of_listPrimitiveGeneratedEndomorphisms F
    (fun p => by
      obtain ⟨decode, decodeSurjective⟩ := treeGenerated p
      exact ⟨decode ∘ boundedPrimitiveFiniteTreeEnumeration embed,
        decodeSurjective.comp
          (boundedPrimitiveFiniteTreeEnumeration_surjective embed)⟩)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end


end AAT.AG.RealizationReconstruction
