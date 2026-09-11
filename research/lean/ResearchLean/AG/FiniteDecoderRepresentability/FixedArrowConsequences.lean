import ResearchLean.AG.FiniteDecoderRepresentability.FixedArrowClassification
import Formal.Util.AssertStandardAxioms

/-!
# Infinite-carrier consequences and decoder faithfulness

This module completes G-121(C).  It identifies the normalized default equation
with equality of the continuous extensions at infinity, proves that semantic
extraction exactness supplies that equation on an infinite Atom carrier, and
therefore reduces fixed-arrow representability to finite permutation support.
It also proves faithfulness of the finite-code realization directly from the
decoded-equality quotient used for its morphisms.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open CategoryTheory AtomFoundation DoctrineFiberProduct OnePoint

variable {U : AtomCarrier.{u}}

/--
G-121(C) topological reading of the authored default condition: it is exactly
equality of the two canonical continuous extensions at the point at infinity.
-/
theorem normalizedExtractionCode_defaultValue_eq_iff_apply_infty_eq
    [DecidableEq U.Atom] (source target : FiniteInstanceCode U)
    (sourceInput : source.doctrine.Source)
    (targetInput : target.doctrine.Source)
    (equiv : Equiv.Perm U.Atom) :
    (normalizedExtractionCode target targetInput).defaultValue =
        (normalizedExtractionCode source sourceInput).defaultValue ↔
      atomPredicateCodeToContinuousMap
          (normalizedExtractionCode target targetInput) ∞ =
        atomPredicateCodeToContinuousMap
          ((normalizedExtractionCode source sourceInput).transport equiv) ∞ := by
  simp only [atomPredicateCodeToContinuousMap_apply_infty,
    atomPredicateCode_transport_defaultValue]

/--
Every semantic arrow makes the target normalized extraction table and the
transported source table agree at each actual Atom.  This is the finite-point
part of the fixed-arrow classification and uses no support assumption.
-/
theorem normalizedExtractionCode_evaluationEq_transport
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic)
    (input : source.doctrine.Source) :
    atomPredicateCodeEvaluationEq
      (normalizedExtractionCode target (hom.doctrineHom.sourceMap input))
      ((normalizedExtractionCode source input).transport
        hom.doctrineHom.atomEquiv) := by
  intro atom
  have hexact := hom.doctrineHom.extraction_iff input
    (hom.doctrineHom.atomEquiv.symm atom)
  change
    source.doctrine.toDoctrine.extracts input
        (hom.doctrineHom.atomEquiv.symm atom) ↔
      target.doctrine.toDoctrine.extracts
        (hom.doctrineHom.sourceMap input)
        (hom.doctrineHom.atomEquiv
          (hom.doctrineHom.atomEquiv.symm atom)) at hexact
  rw [FiniteDoctrineCode.toDoctrine_extracts_iff,
    FiniteDoctrineCode.toDoctrine_extracts_iff,
    hom.doctrineHom.atomEquiv.apply_symm_apply] at hexact
  have hexact' :
      (normalizedExtractionCode source input).eval
          (hom.doctrineHom.atomEquiv.symm atom) = true ↔
        (normalizedExtractionCode target
          (hom.doctrineHom.sourceMap input)).eval atom = true := by
    simpa only [AtomPredicateCode.Holds,
      normalizedExtractionCode_eval] using hexact
  have htransport :
      ((normalizedExtractionCode source input).transport
        hom.doctrineHom.atomEquiv).eval atom =
      (normalizedExtractionCode source input).eval
        (hom.doctrineHom.atomEquiv.symm atom) := by
    conv_lhs =>
      rw [← hom.doctrineHom.atomEquiv.apply_symm_apply atom]
    rw [AtomPredicateCode.eval_transport]
  apply Bool.eq_iff_iff.mpr
  rw [htransport]
  exact hexact'.symm

/--
On an infinite Atom carrier, semantic extraction exactness determines the raw
finite-exception table, hence automatically preserves normalized defaults.
-/
theorem normalizedExtractionCode_defaultValue_eq_of_infinite
    [DecidableEq U.Atom] [Infinite U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic)
    (input : source.doctrine.Source) :
    (normalizedExtractionCode target
        (hom.doctrineHom.sourceMap input)).defaultValue =
      (normalizedExtractionCode source input).defaultValue := by
  have hcode :
      normalizedExtractionCode target (hom.doctrineHom.sourceMap input) =
        (normalizedExtractionCode source input).transport
          hom.doctrineHom.atomEquiv :=
    atomPredicateCode_eq_of_evaluationEq_of_infinite
      (normalizedExtractionCode_evaluationEq_transport hom input)
  have hdefault := congrArg AtomPredicateCode.defaultValue hcode
  simpa only [atomPredicateCode_transport_defaultValue] using hdefault

/--
G-121(C) infinite-carrier fixed-presentation classification: semantic
representability is equivalent to finite actual permutation support alone.
-/
theorem exists_fixedPresentation_decode_iff_of_infinite
    [DecidableEq U.Atom] [Infinite U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic) :
    (∃ presentation : CartPresentationBetween source target,
      typedPresentationToSemantic presentation = hom) ↔
      (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite := by
  rw [exists_fixedPresentation_decode_iff]
  constructor
  · exact And.left
  · intro hfinite
    exact ⟨hfinite, normalizedExtractionCode_defaultValue_eq_of_infinite hom⟩

/--
G-121(C) infinite-carrier decoder-image classification: a fixed semantic arrow
lies in the `D₀` image exactly when its actual Atom permutation has finite support.
-/
theorem exists_finiteCodeCartHom_map_iff_of_infinite
    [DecidableEq U.Atom] [Infinite U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic) :
    (∃ codeHom : FiniteCodeCartHom source target,
      finiteCodeCartRealization.map codeHom = hom) ↔
      (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite := by
  rw [exists_finiteCodeCartHom_map_iff]
  constructor
  · exact And.left
  · intro hfinite
    exact ⟨hfinite, normalizedExtractionCode_defaultValue_eq_of_infinite hom⟩

/--
The `D₀` realization reflects equality of fixed-endpoint arrows because the
morphism quotient relation is definitionally equality of their decoded arrows.
-/
theorem finiteCodeCartRealization_map_injective
    [DecidableEq U.Atom] {source target : FiniteCodeCartCategory U}
    (first second : source ⟶ target)
    (hmap : finiteCodeCartRealization.map first =
      finiteCodeCartRealization.map second) :
    first = second := by
  refine Quotient.inductionOn₂ first second ?_ hmap
  intro firstPresentation secondPresentation hdecode
  exact Quotient.sound hdecode

/-- G-121(C): the finite-code realization is faithful for every Atom carrier. -/
instance finiteCodeCartRealization_faithful [DecidableEq U.Atom] :
    (finiteCodeCartRealization (U := U)).Faithful where
  map_injective hmap := finiteCodeCartRealization_map_injective _ _ hmap

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
