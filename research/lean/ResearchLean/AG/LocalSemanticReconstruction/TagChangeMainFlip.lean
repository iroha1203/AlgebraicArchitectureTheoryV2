import ResearchLean.AG.LocalSemanticReconstruction.TagChangeMainRecovery
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryRewrite
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeGroupLaw
import Formal.Util.AssertStandardAxioms

/-! Uniform tagged flip and normalization inside the same main local Hom.

Implementation notes: both `t` and `e` are images under the fixed main
reading of existing native morphisms. This keeps the flip, normalization, and
the coherent-family map `J` in one Hom rather than introducing another
presentation of the tagged action. -/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory RealizationReconstruction
open IndependentAATPrimitiveReconstruction

namespace TagChangeMainFlip

/-- The explicit-geometry parameter shared with the main coherent-family map. -/
private abbrev TagParameter : Parameter.{0, 0} :=
  .geometry FiniteModel.carrier IndependentGeometryHomPrimitive.Mode.explicit

/-- The native object whose main local endomorphisms contain both operations. -/
private noncomputable abbrev X : NativeCategory TagParameter := taggedNativeObject

/-- The image of the uniform native source-choice flip in the main local Hom. -/
noncomputable def t : (reading TagParameter).obj X ⟶ (reading TagParameter).obj X :=
  (reading TagParameter).map (taggedSourceChoiceNativeHom (fun _ => true))

/-- The image of native tagged normalization in the same main local Hom. -/
noncomputable def e : (reading TagParameter).obj X ⟶ (reading TagParameter).obj X :=
  (reading TagParameter).map taggedNormalizationNativeHom

/-- The uniform flip is the member of the same coherent-family section map
used for every tagged source choice. -/
theorem t_eq_J_true :
    t = TagChangeMainRecovery.J (TagChange.read (fun _ => true)) := by
  rw [TagChangeMainRecovery.J_eq_read_assembled]
  simp [t]

/-- The uniform native flip is involutive before applying the main reading. -/
theorem native_t_square :
    taggedSourceChoiceNativeHom (fun _ => true) ≫
        taggedSourceChoiceNativeHom (fun _ => true) = 𝟙 X := by
  apply ULift.ext
  change taggedSourceChoiceExplicitExactGeometryMorphism (fun _ => true) ≫
      taggedSourceChoiceExplicitExactGeometryMorphism (fun _ => true) =
    𝟙 taggedOperationExplicitExactGeometryObject
  calc
    _ = taggedSourceChoiceExplicitExactGeometryMorphism
        (fun source => Bool.xor true true) :=
          (taggedSourceChoiceExplicitExactGeometryMorphism_comp
            (fun _ => true) (fun _ => true)).symm
    _ = taggedSourceChoiceExplicitExactGeometryMorphism (fun _ => false) := by
      congr 1
    _ = _ := taggedSourceChoiceExplicitExactGeometryMorphism_false

/-- Native normalization commutes with the uniform flip; the normalized
uniform choice stays uniform. -/
theorem native_e_commutes_t :
    taggedNormalizationNativeHom ≫ taggedSourceChoiceNativeHom (fun _ => true) =
      taggedSourceChoiceNativeHom (fun _ => true) ≫ taggedNormalizationNativeHom := by
  have hnormalize :
      TagChangeNormalizedChoiceKernel.normalizeChoice (fun _ => true) =
        (fun _ => true) := by
    funext source
    rfl
  change TagChangeCanonicalNormalizationGeometry.closedFamilyTaggedNormalization ≫
      closedFamilyTaggedSourceChoice (fun _ => true) =
    closedFamilyTaggedSourceChoice (fun _ => true) ≫
      TagChangeCanonicalNormalizationGeometry.closedFamilyTaggedNormalization
  simpa only [hnormalize] using
    TagChangeCanonicalNormalizationGeometryRewrite.closedFamilyTaggedNormalization_comp_sourceChoice_rewrite
      (fun _ => true)

/-- Native normalization still distinguishes composition with the uniform
flip, witnessed by the underlying explicit geometry morphism. -/
theorem native_e_comp_t_ne_e :
    taggedNormalizationNativeHom ≫ taggedSourceChoiceNativeHom (fun _ => true) ≠
      taggedNormalizationNativeHom := by
  intro equality
  have baseEquality := congrArg (fun morphism : X ⟶ X => morphism.down.base) equality
  apply taggedNormalizationThenUniformFlip_ne_normalization
  simpa only [taggedSourceChoiceExplicitExactGeometryHom_uniformFlip_base,
    TagChangeCanonicalNormalizationGeometry.normalizationExplicitExactGeometryHom_base] using
    baseEquality

/-- Involutivity of the uniform flip in the main local Hom. -/
theorem t_square : t ≫ t = 𝟙 ((reading TagParameter).obj X) := by
  simp only [t, ← Functor.map_comp, native_t_square]
  exact (reading TagParameter).map_id X

/-- Commutation of normalization and the uniform flip in the main local Hom. -/
theorem e_commutes_t : e ≫ t = t ≫ e := by
  simp only [e, t, ← Functor.map_comp, native_e_commutes_t]

/-- The main local Hom retains the native distinction between normalization
and normalization followed by the uniform flip. -/
theorem e_comp_t_ne_e : e ≫ t ≠ e := by
  intro equality
  have h := congrArg (assembleHom TagParameter) equality
  apply native_e_comp_t_ne_e
  simpa only [e, t, ← Functor.map_comp, assembleHom_read] using h

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeMainFlip

end TagChangeMainFlip

end AAT.AG.LocalSemanticReconstruction
