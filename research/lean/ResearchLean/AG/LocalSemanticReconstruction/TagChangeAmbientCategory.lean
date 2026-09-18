import ResearchLean.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Tagged source choices in the ambient admissible-package category

Cycle 32 shows that applying canonical normalization before reading a source
choice loses information.  This module therefore keeps the actual tagged
package before taking its Karoubi image.  Every source choice is placed as an
automorphism of the accepted admissible package, while canonical normalization
is retained as an endomorphism of that same object.

The resulting faithful family is an ambient checkpoint for G-124(A) and E1.
It does not claim that all morphisms of the admissible-package category have
already been reconstructed from finite local data, and it is not the final
common realization category for all four required families.

## Implementation notes

The construction uses the accepted full admissible-package category, whose
morphisms carry no extra commutation certificate.  Keeping the source-choice
maps before applying the canonical normalized-image map preserves their actual
readback injectivity.  The alternative of first applying that map is rejected
here because Cycle 32 proves that it identifies distinct source choices.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct
open AAT.AG.RealizationComparisonIdempotents
open AAT.AG.RealizationReconstruction

namespace TagChangeAmbientCategory

noncomputable section

/-- The actual tagged package, as an object of the full category of packages
carrying canonical-normalization admissibility. -/
abbrev TaggedPackage :
    CanonicalNormalizationAdmissiblePackage FiniteModel.carrier :=
  taggedUniformFlipPackage

/-- An arbitrary source choice as an actual endomorphism of the tagged
admissible package. -/
noncomputable def sourceChoiceMorphism
    (choice : TagChangeKaroubiReconstruction.Choice) :
    TaggedPackage ⟶ TaggedPackage :=
  ObjectProperty.homMk (taggedSourceChoiceTotal choice)

/-- The neutral source choice is the identity ambient package morphism. -/
@[simp] theorem sourceChoiceMorphism_false :
    sourceChoiceMorphism (fun _ => false) = 𝟙 TaggedPackage := by
  apply ObjectProperty.hom_ext
  exact congrArg
    (fun morphism : ExplicitExactGeometryHom
      taggedOperationGeometryPackage taggedOperationGeometryPackage =>
        morphism.base)
    taggedSourceChoiceExplicitExactGeometryMorphism_false

/-- Ambient package composition is pointwise xor on source choices. -/
@[simp] theorem sourceChoiceMorphism_comp
    (first second : TagChangeKaroubiReconstruction.Choice) :
    sourceChoiceMorphism (fun source => Bool.xor (first source) (second source)) =
      sourceChoiceMorphism first ≫ sourceChoiceMorphism second := by
  apply ObjectProperty.hom_ext
  exact congrArg
    (fun morphism : ExplicitExactGeometryHom
      taggedOperationGeometryPackage taggedOperationGeometryPackage =>
        morphism.base)
    (taggedSourceChoiceExplicitExactGeometryMorphism_comp first second)

/-- Every actual source choice is an involutive automorphism of the tagged
admissible package. -/
noncomputable def sourceChoiceAut
    (choice : TagChangeKaroubiReconstruction.Choice) :
    Aut TaggedPackage where
  hom := sourceChoiceMorphism choice
  inv := sourceChoiceMorphism choice
  hom_inv_id := by
    calc
      _ = sourceChoiceMorphism
          (fun source => Bool.xor (choice source) (choice source)) :=
        (sourceChoiceMorphism_comp choice choice).symm
      _ = sourceChoiceMorphism (fun _ => false) := by
        congr 1
        funext source
        exact Bool.xor_self (choice source)
      _ = 𝟙 TaggedPackage := sourceChoiceMorphism_false
  inv_hom_id := by
    calc
      _ = sourceChoiceMorphism
          (fun source => Bool.xor (choice source) (choice source)) :=
        (sourceChoiceMorphism_comp choice choice).symm
      _ = sourceChoiceMorphism (fun _ => false) := by
        congr 1
        funext source
        exact Bool.xor_self (choice source)
      _ = 𝟙 TaggedPackage := sourceChoiceMorphism_false

/-- Distinct source choices remain distinct before canonical normalization in
the ambient admissible-package category. -/
theorem sourceChoiceAut_injective : Function.Injective sourceChoiceAut := by
  intro first second equality
  apply taggedSourceChoiceTotal_injective
  exact congrArg (fun automorphism => automorphism.hom.hom) equality

/-- The full pointwise `C₂`-power maps homomorphically and faithfully to the
actual ambient automorphism group. -/
noncomputable def sourceChoiceAutHom :
    Multiplicative TagChangeKaroubiReconstruction.Choice →*
      Aut TaggedPackage where
  toFun choice := sourceChoiceAut choice.toAdd
  map_one' := by
    apply Iso.ext
    exact sourceChoiceMorphism_false
  map_mul' first second := by
    apply Iso.ext
    change sourceChoiceMorphism
        (fun source => Bool.xor (first.toAdd source) (second.toAdd source)) =
      sourceChoiceMorphism second.toAdd ≫ sourceChoiceMorphism first.toAdd
    rw [← sourceChoiceMorphism_comp]
    congr 1
    funext source
    exact Bool.xor_comm (first.toAdd source) (second.toAdd source)

/-- The ambient source-choice group homomorphism is injective. -/
theorem sourceChoiceAutHom_injective : Function.Injective sourceChoiceAutHom := by
  intro first second equality
  apply Multiplicative.ext
  apply sourceChoiceAut_injective
  exact equality

/-- The actual source-choice subgroup inside the ambient admissible-package
automorphism group. -/
noncomputable def sourceChoiceSubgroup : Subgroup (Aut TaggedPackage) :=
  sourceChoiceAutHom.range

/-- The pointwise source-choice group is exactly its faithful ambient image. -/
noncomputable def sourceChoiceGroupEquiv :
    Multiplicative TagChangeKaroubiReconstruction.Choice ≃*
      sourceChoiceSubgroup :=
  MonoidHom.ofInjective sourceChoiceAutHom_injective

/-- Canonical normalization remains an actual endomorphism of the same tagged
package; it is not applied as a quotient to the source-choice family. -/
noncomputable def normalization : TaggedPackage ⟶ TaggedPackage :=
  canonicalPackageNormalization TaggedPackage

/-- The constant-true ambient source choice is the accepted uniform flip. -/
@[simp] theorem sourceChoiceMorphism_true :
    sourceChoiceMorphism (fun _ => true) = taggedUniformFlipMorphism := by
  apply ObjectProperty.hom_ext
  exact taggedSourceChoiceAut_true_hom_base

/-- The accepted uniform flip has order two in the ambient category. -/
theorem sourceChoiceMorphism_true_square :
    sourceChoiceMorphism (fun _ => true) ≫
        sourceChoiceMorphism (fun _ => true) =
      𝟙 TaggedPackage := by
  rw [sourceChoiceMorphism_true]
  exact taggedUniformFlipMorphism_square

/-- The accepted uniform flip commutes with ambient canonical normalization. -/
theorem sourceChoiceMorphism_true_commutes_normalization :
    normalization ≫ sourceChoiceMorphism (fun _ => true) =
      sourceChoiceMorphism (fun _ => true) ≫ normalization := by
  rw [sourceChoiceMorphism_true]
  exact taggedUniformFlipMorphism_commutes_normalization

/-- Normalization followed by the accepted uniform flip is not normalization
itself in the ambient category. -/
theorem normalization_comp_sourceChoiceMorphism_true_ne_normalization :
    normalization ≫ sourceChoiceMorphism (fun _ => true) ≠ normalization := by
  rw [sourceChoiceMorphism_true]
  intro equality
  apply taggedNormalizationThenUniformFlip_ne_normalization
  exact congrArg (fun morphism => morphism.hom) equality

/-- The accepted conventional-order equation `et ≠ e` holds directly in the
ambient category; commutation transports the preceding `te ≠ e` witness. -/
theorem sourceChoiceMorphism_true_comp_normalization_ne_normalization :
    sourceChoiceMorphism (fun _ => true) ≫ normalization ≠ normalization := by
  intro equality
  apply normalization_comp_sourceChoiceMorphism_true_ne_normalization
  rw [sourceChoiceMorphism_true_commutes_normalization]
  exact equality

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory

end

end TagChangeAmbientCategory

end AAT.AG.LocalSemanticReconstruction
