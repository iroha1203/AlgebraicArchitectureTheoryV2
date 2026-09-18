import ResearchLean.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence
import ResearchLean.AG.DoctrineFiberProduct.CanonicalObjectNormalizationAPI
import Formal.Util.AssertStandardAxioms

/-!
# Information loss under normalization of the tagged source-choice family

The uniform flip commutes with canonical normalization, but an arbitrary
source-indexed choice need not: precomposition reads the choice at the
normalized source, whereas postcomposition reads it at the original source.
This module records the exact invariance condition, proves it sufficient, and
constructs an actual source choice violating it from the noninjective object
normalization.

The normalization functor can still send every source-choice automorphism to
an automorphism of the normalized Karoubi object: Karoubi morphisms require a
sandwich equation, not commutation.  What fails is faithfulness on the full
source-choice family.  A choice supported at an object moved by normalization
is distinct from the constant-false choice, but their left-normalized package
maps coincide.  Thus this particular normalized-image route cannot recover
the full family required by G-124.  This is a blocker for that route, not a
refutation of fixed G-124 or of every possible single-object presentation.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct
open AAT.AG.RealizationReconstruction

namespace TagChangeKaroubiReconstruction

noncomputable section

/-- Boolean source choices indexing the actual tagged package endomorphism
family. -/
abbrev Choice := TagChange.GlobalTagChange TagChange.TaggedArchitectureIndex

/-- Casting a tagged operation along an equality of its untagged operation
type leaves the Boolean tag unchanged. -/
@[simp] theorem cast_operation_snd
    {alpha beta : Type} (equality : alpha = beta) (operation : alpha × Bool) :
    (cast (congrArg (fun operationType => operationType × Bool) equality)
      operation).2 = operation.2 := by
  cases equality
  rfl

/-- Pointwise choices whose raw source-choice maps commute with canonical
normalization are exactly those constant along the normalization map. -/
def NormalizationInvariant (choice : Choice) : Prop :=
  ∀ source,
    choice (canonicalObjectNormalization taggedOperationPackage source) =
      choice source

/-- Constant choices are concrete inhabitants of the normalization-invariant
predicate. -/
theorem normalizationInvariant_const (value : Bool) :
    NormalizationInvariant (fun _ => value) := by
  intro source
  rfl

/-- Normalization-invariant source choices commute with canonical
normalization as actual package morphisms. -/
theorem taggedSourceChoiceTotal_commutes_normalization
    (choice : Choice) (invariant : NormalizationInvariant choice) :
    (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal choice) =
      (taggedSourceChoiceTotal choice).comp
        (canonicalObjectNormalizationTotal taggedOperationPackage
          taggedOperationPackage_admissible) := by
  apply PackageTotalHom.ext
  · rfl
  · apply SignedExactCoreReadingHom.ext
    · rfl
    · rfl
    · rfl

    · apply Function.hfunext rfl
      intro source source' hsource
      cases hsource
      apply Function.hfunext rfl
      intro target target' htarget
      cases htarget
      apply Function.hfunext rfl
      intro operation operation' hoperation
      cases hoperation
      apply heq_of_eq
      dsimp only [PackageTotalHom.comp, taggedSourceChoiceTotal,
        taggedSourceChoiceUpper, canonicalObjectNormalizationTotal,
        canonicalObjectNormalizationUpper, SignedExactCoreReadingHom.comp]
      rw [invariant source]
      let sourceEquality :=
        finiteCanonicalObjectNormalization_admissible.operation_type_eq
          source target
      have admissibleEquality :
          taggedOperationPackage_admissible.operation_type_eq source target =
            congrArg (fun operationType => operationType × Bool) sourceEquality :=
        Subsingleton.elim _ _
      rw [admissibleEquality]
      cases choice source
      · rfl
      · exact (taggedOperationCast_uniformFlip sourceEquality operation).symm
    · rfl
    · rfl
    · rfl

/-- Conversely, actual package-level commutation forces the choice to be
constant along canonical-normalization fibers. -/
theorem normalizationInvariant_of_commutes
    (choice : Choice)
    (commutes :
      (canonicalObjectNormalizationTotal taggedOperationPackage
          taggedOperationPackage_admissible).comp
            (taggedSourceChoiceTotal choice) =
        (taggedSourceChoiceTotal choice).comp
          (canonicalObjectNormalizationTotal taggedOperationPackage
            taggedOperationPackage_admissible)) :
    NormalizationInvariant choice := by
  intro source
  have tagEquality := congrArg
    (fun total : PackageTotalHom taggedOperationPackage taggedOperationPackage =>
      (total.upper.operationMap (taggedIdentityOperation source)).2)
    commutes
  dsimp only [PackageTotalHom.comp, taggedSourceChoiceTotal,
    taggedSourceChoiceUpper, canonicalObjectNormalizationTotal,
    canonicalObjectNormalizationUpper, SignedExactCoreReadingHom.comp] at tagEquality
  let sourceEquality :=
    finiteCanonicalObjectNormalization_admissible.operation_type_eq source source
  have admissibleEquality :
      taggedOperationPackage_admissible.operation_type_eq source source =
        congrArg (fun operationType => operationType × Bool) sourceEquality :=
    Subsingleton.elim _ _
  rw [admissibleEquality] at tagEquality
  have leftCast := cast_operation_snd sourceEquality
    (taggedIdentityOperation source)
  have rightCast := cast_operation_snd sourceEquality
    ((taggedIdentityOperation source).1,
      if choice source then !(taggedIdentityOperation source).2
      else (taggedIdentityOperation source).2)
  rw [leftCast, rightCast] at tagEquality
  cases normalizedValue :
      choice (canonicalObjectNormalization taggedOperationPackage source) <;>
    cases sourceValue : choice source <;>
      simp [normalizedValue, sourceValue, taggedIdentityOperation] at tagEquality ⊢

/-- The tagged package's canonical object normalization is noninjective on the
actual architecture-object carrier. -/
theorem taggedCanonicalNormalization_not_injective :
    ¬ Function.Injective
      (canonicalObjectNormalization taggedOperationPackage) := by
  intro injective
  apply finiteAxisFoldUnitObject_ne_boolObject
  apply injective
  apply canonicalObjectNormalization_eq_of_configuration_eq
  rw [finiteAxisFoldUnitObject_configuration,
    finiteAxisFoldBoolObject_configuration]

/-- Therefore at least one actual source is moved by canonical normalization. -/
theorem exists_source_moved_by_normalization :
    ∃ source : TagChange.TaggedArchitectureIndex,
      canonicalObjectNormalization taggedOperationPackage source ≠ source := by
  by_contra noSource
  simp only [not_exists, not_not] at noSource
  apply taggedCanonicalNormalization_not_injective
  intro first second equality
  rw [noSource first, noSource second] at equality
  exact equality

/-- A moved source determines a concrete Boolean choice that is true exactly
at its normalized image. -/
noncomputable def separatingChoice
    (source : TagChange.TaggedArchitectureIndex) : Choice := by
  classical
  exact fun candidate =>
    if candidate = canonicalObjectNormalization taggedOperationPackage source
    then true else false

/-- The separating choice is not normalization-invariant at any moved source. -/
theorem separatingChoice_not_invariant
    {source : TagChange.TaggedArchitectureIndex}
    (moved : canonicalObjectNormalization taggedOperationPackage source ≠ source) :
    ¬ NormalizationInvariant (separatingChoice source) := by
  intro invariant
  have atSource := invariant source
  simp [separatingChoice, Ne.symm moved] at atSource

/-- A source moved by an idempotent normalization cannot itself lie in the
image of that normalization. -/
theorem moved_source_not_in_normalization_image
    {source : TagChange.TaggedArchitectureIndex}
    (moved : canonicalObjectNormalization taggedOperationPackage source ≠ source)
    (candidate : TagChange.TaggedArchitectureIndex) :
    canonicalObjectNormalization taggedOperationPackage candidate ≠ source := by
  intro equality
  apply moved
  calc
    canonicalObjectNormalization taggedOperationPackage source =
        canonicalObjectNormalization taggedOperationPackage
          (canonicalObjectNormalization taggedOperationPackage candidate) :=
      congrArg (canonicalObjectNormalization taggedOperationPackage) equality.symm
    _ = canonicalObjectNormalization taggedOperationPackage candidate :=
      canonicalObjectNormalization_idempotent taggedOperationPackage candidate
    _ = source := equality

/-- Left normalization sees a source choice only on normalized sources. -/
theorem canonicalNormalization_comp_taggedSourceChoiceTotal_eq_of_normalized
    (first second : Choice)
    (equalOnNormalized : ∀ source,
      first (canonicalObjectNormalization taggedOperationPackage source) =
        second (canonicalObjectNormalization taggedOperationPackage source)) :
    (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal first) =
      (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal second) := by
  apply PackageTotalHom.ext
  · rfl
  · apply SignedExactCoreReadingHom.ext
    · rfl
    · rfl
    · rfl
    · apply Function.hfunext rfl
      intro source source' hsource
      cases hsource
      apply Function.hfunext rfl
      intro target target' htarget
      cases htarget
      apply Function.hfunext rfl
      intro operation operation' hoperation
      cases hoperation
      apply heq_of_eq
      dsimp only [PackageTotalHom.comp, taggedSourceChoiceTotal,
        taggedSourceChoiceUpper, canonicalObjectNormalizationTotal,
        canonicalObjectNormalizationUpper, SignedExactCoreReadingHom.comp]
      rw [equalOnNormalized source]
    · rfl
    · rfl
    · rfl

/-- The canonical left-normalization map is not injective on the actual full
source-choice family.  A choice supported at a moved source disappears after
normalization, while it remains distinct before normalization. -/
theorem canonicalNormalization_sourceChoice_map_not_injective :
    ¬ Function.Injective
      (fun choice : Choice =>
        (canonicalObjectNormalizationTotal taggedOperationPackage
            taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal choice)) := by
  classical
  obtain ⟨source, moved⟩ := exists_source_moved_by_normalization
  let supported : Choice := fun candidate => if candidate = source then true else false
  let zero : Choice := fun _ => false
  have normalizedEquality : ∀ candidate,
      supported (canonicalObjectNormalization taggedOperationPackage candidate) =
        zero (canonicalObjectNormalization taggedOperationPackage candidate) := by
    intro candidate
    simp [supported, zero, moved_source_not_in_normalization_image moved candidate]
  have imageEquality :=
    canonicalNormalization_comp_taggedSourceChoiceTotal_eq_of_normalized
      supported zero normalizedEquality
  intro injective
  have choiceEquality := injective imageEquality
  have atSource := congrFun choiceEquality source
  simp [supported, zero] at atSource

/-- Hence an actual member of the full source-choice family fails to commute
with canonical normalization.  This rules out using the raw source-choice
maps themselves as centralizing representatives; the preceding noninjectivity
theorem is the separate obstruction to faithful recovery after normalization. -/
theorem exists_sourceChoice_not_commuting_normalization :
    ∃ choice : Choice,
      (canonicalObjectNormalizationTotal taggedOperationPackage
          taggedOperationPackage_admissible).comp
            (taggedSourceChoiceTotal choice) ≠
        (taggedSourceChoiceTotal choice).comp
          (canonicalObjectNormalizationTotal taggedOperationPackage
            taggedOperationPackage_admissible) := by
  obtain ⟨source, moved⟩ := exists_source_moved_by_normalization
  refine ⟨separatingChoice source, ?_⟩
  intro commutes
  exact separatingChoice_not_invariant moved
    (normalizationInvariant_of_commutes (separatingChoice source) commutes)

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction

end


end TagChangeKaroubiReconstruction

end AAT.AG.LocalSemanticReconstruction
