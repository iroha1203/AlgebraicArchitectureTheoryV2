import ResearchLean.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence
import Formal.Util.AssertStandardAxioms

/-!
# Exact kernel of canonical normalization on tagged source choices

Cycle 32 exhibited two distinct source choices with the same canonically
left-normalized package map.  This module classifies that information loss
exactly.  Precomposing a choice with canonical object normalization is an
idempotent retraction onto the normalization-invariant choices, and two
left-normalized actual package maps agree exactly when their retracted choices
agree.  Restricting to invariant choices therefore restores faithfulness.

## Implementation notes

The classification is stated through actual `PackageTotalHom` equality and
the existing tagged-identity-operation readback.  It is not defined as a
quotient or as a certificate carried by a local value.  The retracted choice
will serve as the finite-local datum for normalized source-choice maps in a
later generated-subcategory normal-form construction.
-/

namespace AAT.AG.LocalSemanticReconstruction

open AtomFoundation DoctrineFiberProduct
open AAT.AG.RealizationReconstruction

namespace TagChangeNormalizedChoiceKernel

noncomputable section

open TagChangeKaroubiReconstruction

/-- Restrict a source choice to the canonical-normalization image. -/
def normalizeChoice (choice : Choice) : Choice :=
  fun source => choice (canonicalObjectNormalization taggedOperationPackage source)

/-- A normalized choice is constant along canonical-normalization fibers. -/
theorem normalizeChoice_invariant (choice : Choice) :
    NormalizationInvariant (normalizeChoice choice) := by
  intro source
  simp only [normalizeChoice]
  rw [canonicalObjectNormalization_idempotent]

/-- Canonical restriction is idempotent. -/
@[simp] theorem normalizeChoice_idempotent (choice : Choice) :
    normalizeChoice (normalizeChoice choice) = normalizeChoice choice := by
  funext source
  exact normalizeChoice_invariant choice source

/-- Invariant choices are exactly the fixed points of canonical restriction. -/
theorem normalizeChoice_eq_iff (choice : Choice) :
    normalizeChoice choice = choice ↔ NormalizationInvariant choice := by
  constructor
  · intro equality source
    exact congrFun equality source
  · intro invariant
    funext source
    exact invariant source

/-- The type of choices fixed by canonical normalization. -/
abbrev InvariantChoice := { choice : Choice // NormalizationInvariant choice }

/-- Canonical restriction lands in the normalization-invariant choices. -/
def toInvariantChoice (choice : Choice) : InvariantChoice :=
  ⟨normalizeChoice choice, normalizeChoice_invariant choice⟩

/-- Canonical restriction is a retraction onto invariant choices. -/
@[simp] theorem toInvariantChoice_retract (choice : InvariantChoice) :
    toInvariantChoice choice.1 = choice := by
  apply Subtype.ext
  exact (normalizeChoice_eq_iff choice.1).2 choice.2

/-- Left normalization depends only on the canonically restricted choice. -/
theorem normalization_comp_sourceChoice_eq_normalized (choice : Choice) :
    (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal choice) =
      (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal (normalizeChoice choice)) := by
  apply canonicalNormalization_comp_taggedSourceChoiceTotal_eq_of_normalized
  intro source
  simp only [normalizeChoice]
  rw [canonicalObjectNormalization_idempotent]

/-- Tagged-identity-operation readback of a left-normalized actual package map
is exactly canonical restriction of its source choice. -/
theorem readTaggedSourceChoice_normalization_comp (choice : Choice) :
    readTaggedSourceChoice
        ((canonicalObjectNormalizationTotal taggedOperationPackage
          taggedOperationPackage_admissible).comp
            (taggedSourceChoiceTotal choice)) =
      normalizeChoice choice := by
  funext source
  dsimp only [readTaggedSourceChoice, PackageTotalHom.comp,
    taggedSourceChoiceTotal, taggedSourceChoiceUpper,
    canonicalObjectNormalizationTotal, canonicalObjectNormalizationUpper,
    SignedExactCoreReadingHom.comp, normalizeChoice]
  let sourceEquality :=
    finiteCanonicalObjectNormalization_admissible.operation_type_eq source source
  have admissibleEquality :
      taggedOperationPackage_admissible.operation_type_eq source source =
        congrArg (fun operationType => operationType × Bool) sourceEquality :=
    Subsingleton.elim _ _
  rw [admissibleEquality]
  have castTag := cast_operation_snd sourceEquality
    (taggedIdentityOperation source)
  rw [castTag]
  cases normalizedValue :
      choice (canonicalObjectNormalization taggedOperationPackage source) <;>
    simp [taggedIdentityOperation]

/-- Exact collision classification: two canonically left-normalized actual
package maps agree exactly when their restricted choices agree. -/
theorem normalization_comp_sourceChoice_eq_iff
    (first second : Choice) :
    (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal first) =
      (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal second) ↔
        normalizeChoice first = normalizeChoice second := by
  constructor
  · intro equality
    have readEquality := congrArg readTaggedSourceChoice equality
    simpa only [readTaggedSourceChoice_normalization_comp] using readEquality
  · intro equality
    apply canonicalNormalization_comp_taggedSourceChoiceTotal_eq_of_normalized
    intro source
    exact congrFun equality source

/-- On normalization-invariant choices, the canonical normalized-image map is
faithful. -/
theorem invariant_normalizedImage_injective :
    Function.Injective
      (fun choice : InvariantChoice =>
        (canonicalObjectNormalizationTotal taggedOperationPackage
            taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal choice.1)) := by
  intro first second equality
  apply Subtype.ext
  have normalizedEquality :=
    (normalization_comp_sourceChoice_eq_iff first.1 second.1).1 equality
  rw [(normalizeChoice_eq_iff first.1).2 first.2,
    (normalizeChoice_eq_iff second.1).2 second.2] at normalizedEquality
  exact normalizedEquality

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel

end


end TagChangeNormalizedChoiceKernel

end AAT.AG.LocalSemanticReconstruction
