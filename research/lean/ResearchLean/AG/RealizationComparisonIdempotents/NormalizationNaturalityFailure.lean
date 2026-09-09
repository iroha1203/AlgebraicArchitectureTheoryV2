import ResearchLean.AG.RealizationComparisonIdempotents.NormalizationProjection
import ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorModificationCounterexample

/-!
# One-sided naturality and the canonical retraction failure

This file constructs G-119(D)'s natural inclusion from the canonically
normalized Karoubi objects to the raw Karoubi embedding.  Its naturality is
exactly the one-sided absorption theorem proved in D1.

The objectwise reverse maps split that inclusion, but their naturality at a
raw morphism is equivalent to the opposite two-sided exchange equation and to
the existing operation-coherence predicate.  The fixed G-117 tagged endpoint
flip is placed in the same admissible category and refutes that naturality;
the original Bool evaluations are retained as explicit computational evidence.

## Implementation notes

Both directions use mathlib's `Karoubi.decompId_i` and `Karoubi.decompId_p`.
The reverse maps are deliberately not packaged as a natural transformation:
doing so would assume precisely the universal equation refuted below.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.RealizationComparisonIdempotents

open AtomFoundation DoctrineFiberProduct

universe u

/-- The raw Karoubi embedding `J : C ⥤ Kar(C)`, whose object projector is the
identity rather than the canonical normalization. -/
noncomputable def rawPackageKaroubiInclusion (U : AtomCarrier.{u}) :
    CanonicalNormalizationAdmissiblePackage U ⥤
      Karoubi (CanonicalNormalizationAdmissiblePackage U) :=
  toKaroubi _

/-- G-119(D)'s natural transformation `i : KN ⟶ J`.  Its component at `P`
has raw map `e_P`; D1 absorption supplies naturality for every raw morphism. -/
noncomputable def normalizedPackageInclusion (U : AtomCarrier.{u}) :
    packageNormalizationFunctor U ⋙ normalizedPackageKaroubiFunctor U ⟶
      rawPackageKaroubiInclusion U :=
  { app := fun P =>
      Karoubi.decompId_i (normalizedPackageKaroubiObject P)
    naturality := by
      intro P Q f
      apply Karoubi.Hom.ext
      exact canonicalPackageNormalization_absorption f }

/-- Normalization rule: the raw map of the inclusion component `i_P` is the
canonical idempotent `e_P`. -/
@[simp]
theorem normalizedPackageInclusion_app_f
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    ((normalizedPackageInclusion U).app P).f =
      canonicalPackageNormalization P :=
  rfl

/-- The objectwise reverse map `p_P : J(P) ⟶ KN(P)`, with raw map `e_P`.
This family is not asserted to be natural. -/
noncomputable def normalizedPackageRetractionApp
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    (rawPackageKaroubiInclusion U).obj P ⟶
      (normalizedPackageKaroubiFunctor U).obj
        ((packageNormalizationFunctor U).obj P) :=
  Karoubi.decompId_p (normalizedPackageKaroubiObject P)

/-- Normalization rule: the raw map of the objectwise retraction `p_P` is the
same canonical idempotent `e_P`. -/
@[simp]
theorem normalizedPackageRetractionApp_f
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    (normalizedPackageRetractionApp P).f = canonicalPackageNormalization P :=
  rfl

/-- The objectwise reverse map splits the inclusion: in Lean composition
order `i_P ≫ p_P = 𝟙_{KN(P)}`, the fixed target's `p_P i_P = 1`. -/
@[simp]
theorem normalizedPackageInclusion_retraction
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    (normalizedPackageInclusion U).app P ≫ normalizedPackageRetractionApp P =
      𝟙 ((normalizedPackageKaroubiFunctor U).obj
        ((packageNormalizationFunctor U).obj P)) := by
  apply Karoubi.Hom.ext
  exact canonicalPackageNormalization_idem P

/-- Naturality of the objectwise reverse family at a chosen raw morphism.
Keeping this as a proposition, rather than a structure field, makes the
failed universal obligation explicit. -/
def NormalizedPackageRetractionNaturalAt
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (f : P ⟶ Q) : Prop :=
  (rawPackageKaroubiInclusion U).map f ≫ normalizedPackageRetractionApp Q =
    normalizedPackageRetractionApp P ≫
      (packageNormalizationFunctor U ⋙
        normalizedPackageKaroubiFunctor U).map f

/-- Retraction naturality at `f` is equivalent to the opposite exchange
equation `f ≫ e_Q = e_P ≫ f`.  Source idempotence removes the extra `e_P`
introduced by `N(f)`. -/
theorem normalizedPackageRetractionNaturalAt_iff
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (f : P ⟶ Q) :
    NormalizedPackageRetractionNaturalAt f ↔
      f ≫ canonicalPackageNormalization Q =
        canonicalPackageNormalization P ≫ f := by
  constructor
  · intro h
    have raw := congrArg (fun k => k.f) h
    change f ≫ canonicalPackageNormalization Q =
      canonicalPackageNormalization P ≫
        (canonicalPackageNormalization P ≫ f) at raw
    simpa only [← Category.assoc, canonicalPackageNormalization_idem] using raw
  · intro h
    apply Karoubi.Hom.ext
    change f ≫ canonicalPackageNormalization Q =
      canonicalPackageNormalization P ≫
        (canonicalPackageNormalization P ≫ f)
    simpa only [← Category.assoc, canonicalPackageNormalization_idem] using h

/-- The opposite package-level exchange equation is equivalent to the exact
operation-map coherence isolated by G-117.  No coherence premise is added to
the morphism type. -/
theorem canonicalPackageNormalization_natural_iff_operationCoherent
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (f : P ⟶ Q) :
    (f ≫ canonicalPackageNormalization Q =
        canonicalPackageNormalization P ≫ f) ↔
      CanonicalNormalizationOperationCoherent
        f.hom P.property Q.property := by
  constructor
  · intro h
    apply (canonicalObjectNormalizationTotal_natural_iff_operationCoherent
      f.hom P.property Q.property).mp
    exact congrArg (fun k => k.hom) h
  · intro h
    apply ObjectProperty.hom_ext
    exact (canonicalObjectNormalizationTotal_natural_iff_operationCoherent
      f.hom P.property Q.property).mpr h

/-- Consequently, objectwise retraction naturality at `f` holds exactly when
the existing operation-coherence condition holds for its raw total map. -/
theorem normalizedPackageRetractionNaturalAt_iff_operationCoherent
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (f : P ⟶ Q) :
    NormalizedPackageRetractionNaturalAt f ↔
      CanonicalNormalizationOperationCoherent
        f.hom P.property Q.property :=
  (normalizedPackageRetractionNaturalAt_iff f).trans
    (canonicalPackageNormalization_natural_iff_operationCoherent f)

/-- The fixed G-117 tagged package as an object of the same admissible
full subcategory `C` used throughout G-119(D). -/
noncomputable def taggedCanonicalNormalizationPackage :
    CanonicalNormalizationAdmissiblePackage FiniteModel.carrier :=
  ⟨taggedOperationPackage, taggedOperationPackage_admissible⟩

/-- The fixed G-117 endpoint flip as an actual raw morphism of `C`. -/
noncomputable def taggedCanonicalNormalizationFlip :
    taggedCanonicalNormalizationPackage ⟶
      taggedCanonicalNormalizationPackage :=
  ObjectProperty.homMk taggedEndpointFlipTotal

/-- D1 absorption holds for the tagged endpoint flip in the same category. -/
theorem taggedCanonicalNormalization_absorption :
    canonicalPackageNormalization taggedCanonicalNormalizationPackage ≫
        taggedCanonicalNormalizationFlip ≫
          canonicalPackageNormalization taggedCanonicalNormalizationPackage =
      canonicalPackageNormalization taggedCanonicalNormalizationPackage ≫
        taggedCanonicalNormalizationFlip :=
  canonicalPackageNormalization_absorption taggedCanonicalNormalizationFlip

/-- The natural inclusion `i` satisfies its naturality square at the tagged
endpoint flip, as it does at every raw morphism. -/
theorem taggedCanonicalNormalization_inclusion_naturality :
    (packageNormalizationFunctor _ ⋙ normalizedPackageKaroubiFunctor _).map
          taggedCanonicalNormalizationFlip ≫
        (normalizedPackageInclusion _).app taggedCanonicalNormalizationPackage =
      (normalizedPackageInclusion _).app taggedCanonicalNormalizationPackage ≫
        (rawPackageKaroubiInclusion _).map
          taggedCanonicalNormalizationFlip :=
  (normalizedPackageInclusion _).naturality
    taggedCanonicalNormalizationFlip

/-- The tagged endpoint flip fails the opposite exchange equation in `C`,
using the existing G-117 total-morphism inequality. -/
theorem taggedCanonicalNormalization_not_natural :
    taggedCanonicalNormalizationFlip ≫
        canonicalPackageNormalization taggedCanonicalNormalizationPackage ≠
      canonicalPackageNormalization taggedCanonicalNormalizationPackage ≫
        taggedCanonicalNormalizationFlip := by
  intro h
  exact taggedEndpointFlip_not_natural (congrArg (fun k => k.hom) h)

/-- Hence the objectwise reverse family `p` is not natural at the fixed tagged
endpoint flip. -/
theorem taggedCanonicalNormalization_retraction_not_natural :
    ¬ NormalizedPackageRetractionNaturalAt
      taggedCanonicalNormalizationFlip := by
  intro h
  exact taggedCanonicalNormalization_not_natural
    ((normalizedPackageRetractionNaturalAt_iff
      taggedCanonicalNormalizationFlip).mp h)

/-- The original Bool witness remains `false` after normalizing first and
then applying the tagged endpoint flip. -/
theorem taggedCanonicalNormalization_normalize_then_flip_snd :
    ((((canonicalPackageNormalization taggedCanonicalNormalizationPackage ≫
      taggedCanonicalNormalizationFlip).hom.upper.operationMap
        taggedBoolOperation)).2 = false) :=
  taggedLeftComposite_snd

/-- The original Bool witness becomes `true` after applying the tagged
endpoint flip first and then normalizing. -/
theorem taggedCanonicalNormalization_flip_then_normalize_snd :
    ((((taggedCanonicalNormalizationFlip ≫
      canonicalPackageNormalization taggedCanonicalNormalizationPackage).hom.upper.operationMap
        taggedBoolOperation)).2 = true) :=
  taggedRightComposite_snd

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
