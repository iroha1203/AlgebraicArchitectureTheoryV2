import ResearchLean.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryRewrite
import Formal.Util.AssertStandardAxioms

/-!
# Generated tagged normal forms on the common exact-geometry surface

Cycles 39--41 constructed the source-choice and normalization generators in
the common tagged `FamilyRealization` fiber and proved their exact-geometry
laws.  This module evaluates the accepted two-constructor `NormalForm` on that
surface, proves its multiplication table, and identifies its faithful image
with the accepted package-level generated submonoid.

This is a common-global bridge for the generated tagged branch.  It does not
yet construct the common local-reading category or a primitive finite reading
for arbitrary common-fiber morphisms.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct
open AAT.AG.RealizationReconstruction

namespace TagChangeExactGeometryNormalForm

noncomputable section

open TagChangeCanonicalNormalizationGeometry
open TagChangeCanonicalNormalizationGeometryLaws
open TagChangeCanonicalNormalizationGeometryRewrite
open TagChangeGeneratedNormalForm
open TagChangeKaroubiReconstruction
open TagChangeNormalizedChoiceKernel

/-- Interpret an accepted generated normal form as an actual endomorphism in
the common tagged exact-geometry fiber. -/
noncomputable def evaluate : NormalForm →
    End (FamilyRealization.taggedOperation :
      FamilyRealization (ClosedFamilyParameter.taggedOperation :
        ClosedFamilyParameter.{0, 0}))
  | .raw choice => closedFamilyTaggedSourceChoice choice
  | .normalized choice =>
      closedFamilyTaggedSourceChoice choice ≫ closedFamilyTaggedNormalization

/-- Forgetting an exact-geometry normal form to its package base recovers the
accepted package-level normal-form evaluation exactly. -/
@[simp] theorem evaluate_base (form : NormalForm) :
    (evaluate form).down.base =
      (TagChangeGeneratedNormalForm.evaluate form).hom := by
  cases form <;> rfl

/-- Source-choice composition in the common tagged fiber is pointwise xor. -/
@[simp] theorem closedFamilyTaggedSourceChoice_comp
    (first second : Choice) :
    closedFamilyTaggedSourceChoice
        (fun source => Bool.xor (first source) (second source)) =
      closedFamilyTaggedSourceChoice first ≫
        closedFamilyTaggedSourceChoice second := by
  apply ULift.ext
  exact taggedSourceChoiceExplicitExactGeometryMorphism_comp first second

/-- The false source choice is the identity of the common tagged fiber. -/
@[simp] theorem closedFamilyTaggedSourceChoice_false :
    closedFamilyTaggedSourceChoice (fun _ => false) =
      𝟙 (FamilyRealization.taggedOperation :
        FamilyRealization (ClosedFamilyParameter.taggedOperation :
          ClosedFamilyParameter.{0, 0})) := by
  apply ULift.ext
  exact taggedSourceChoiceExplicitExactGeometryMorphism_false

/-- Exact-geometry evaluation respects the accepted four-case multiplication
table for generated normal forms. -/
theorem evaluate_multiply (first second : NormalForm) :
    evaluate (multiply first second) = evaluate first ≫ evaluate second := by
  cases first with
  | raw first =>
      cases second with
      | raw second =>
          exact closedFamilyTaggedSourceChoice_comp first second
      | normalized second =>
          change closedFamilyTaggedSourceChoice _ ≫
              closedFamilyTaggedNormalization =
            closedFamilyTaggedSourceChoice first ≫
              (closedFamilyTaggedSourceChoice second ≫
                closedFamilyTaggedNormalization)
          rw [← Category.assoc, ← closedFamilyTaggedSourceChoice_comp]
  | normalized first =>
      cases second with
      | raw second =>
          change closedFamilyTaggedSourceChoice _ ≫
              closedFamilyTaggedNormalization =
            (closedFamilyTaggedSourceChoice first ≫
              closedFamilyTaggedNormalization) ≫
                closedFamilyTaggedSourceChoice second
          rw [Category.assoc,
            closedFamilyTaggedNormalization_comp_sourceChoice_rewrite,
            ← Category.assoc, ← closedFamilyTaggedSourceChoice_comp]
      | normalized second =>
          change closedFamilyTaggedSourceChoice _ ≫
              closedFamilyTaggedNormalization =
            (closedFamilyTaggedSourceChoice first ≫
              closedFamilyTaggedNormalization) ≫
                (closedFamilyTaggedSourceChoice second ≫
                  closedFamilyTaggedNormalization)
          symm
          calc
            (closedFamilyTaggedSourceChoice first ≫
                closedFamilyTaggedNormalization) ≫
                  (closedFamilyTaggedSourceChoice second ≫
                    closedFamilyTaggedNormalization) =
              ((closedFamilyTaggedSourceChoice first ≫
                  closedFamilyTaggedNormalization) ≫
                    closedFamilyTaggedSourceChoice second) ≫
                      closedFamilyTaggedNormalization :=
                (Category.assoc _ _ _).symm
            _ = (closedFamilyTaggedSourceChoice first ≫
                (closedFamilyTaggedNormalization ≫
                  closedFamilyTaggedSourceChoice second)) ≫
                    closedFamilyTaggedNormalization := by
              exact congrArg
                (fun morphism => morphism ≫ closedFamilyTaggedNormalization)
                (Category.assoc _ _ _)
            _ = (closedFamilyTaggedSourceChoice first ≫
                (closedFamilyTaggedSourceChoice (normalizeChoice second) ≫
                  closedFamilyTaggedNormalization)) ≫
                    closedFamilyTaggedNormalization := by
              rw [closedFamilyTaggedNormalization_comp_sourceChoice_rewrite]
            _ = ((closedFamilyTaggedSourceChoice first ≫
                closedFamilyTaggedSourceChoice (normalizeChoice second)) ≫
                  closedFamilyTaggedNormalization) ≫
                    closedFamilyTaggedNormalization := by
              rw [← Category.assoc]
            _ = (closedFamilyTaggedSourceChoice first ≫
                closedFamilyTaggedSourceChoice (normalizeChoice second)) ≫
                  (closedFamilyTaggedNormalization ≫
                    closedFamilyTaggedNormalization) := by
              rw [Category.assoc]
            _ = (closedFamilyTaggedSourceChoice first ≫
                closedFamilyTaggedSourceChoice (normalizeChoice second)) ≫
                  closedFamilyTaggedNormalization := by
              rw [closedFamilyTaggedNormalization_idempotent]
            _ = closedFamilyTaggedSourceChoice _ ≫
                closedFamilyTaggedNormalization := by
              rw [← closedFamilyTaggedSourceChoice_comp]

/-- Exact-geometry evaluation is faithful because its primitive package-base
readback is the accepted faithful package evaluation. -/
theorem evaluate_injective : Function.Injective evaluate := by
  intro first second equality
  apply TagChangeGeneratedNormalForm.evaluate_injective
  have baseEquality := congrArg (fun morphism => morphism.down.base) equality
  apply ObjectProperty.hom_ext
  simpa only [evaluate_base] using baseEquality

/-- Exact-geometry evaluation as a faithful monoid homomorphism. -/
noncomputable def evaluationHom : NormalForm →*
    End (FamilyRealization.taggedOperation :
      FamilyRealization (ClosedFamilyParameter.taggedOperation :
        ClosedFamilyParameter.{0, 0})) where
  toFun := evaluate
  map_one' := closedFamilyTaggedSourceChoice_false
  map_mul' first second := by
    change evaluate (multiply second first) = evaluate second ≫ evaluate first
    exact evaluate_multiply second first

/-- The actual common-fiber submonoid represented by exact-geometry normal
forms. -/
noncomputable def representedSubmonoid :
    Submonoid
      (End (FamilyRealization.taggedOperation :
        FamilyRealization (ClosedFamilyParameter.taggedOperation :
          ClosedFamilyParameter.{0, 0}))) :=
  MonoidHom.mrange evaluationHom

/-- Generated normal forms are exactly their faithful common-fiber image. -/
noncomputable def normalFormMulEquivRepresented :
    NormalForm ≃* representedSubmonoid :=
  MulEquiv.ofBijective evaluationHom.mrangeRestrict
    ⟨by
      intro first second equality
      apply evaluate_injective
      exact congrArg Subtype.val equality,
    evaluationHom.mrangeRestrict_surjective⟩

/-- The common exact-geometry image is canonically equivalent to the accepted
package-level generated submonoid through their shared normal form. -/
noncomputable def representedMulEquivPackageGenerated :
    representedSubmonoid ≃*
      TagChangeGeneratedNormalForm.actualGeneratedSubmonoid :=
  normalFormMulEquivRepresented.symm.trans
    TagChangeGeneratedNormalForm.normalFormMulEquivGenerated

/-- The bridge sends every exact evaluated normal form to the accepted package
generated element represented by the same normal form. -/
@[simp] theorem representedMulEquivPackageGenerated_on_normalForm
    (form : NormalForm) :
    representedMulEquivPackageGenerated
        (normalFormMulEquivRepresented form) =
      TagChangeGeneratedNormalForm.normalFormMulEquivGenerated form :=
  by
    change TagChangeGeneratedNormalForm.normalFormMulEquivGenerated
        (normalFormMulEquivRepresented.symm
          (normalFormMulEquivRepresented form)) =
      TagChangeGeneratedNormalForm.normalFormMulEquivGenerated form
    rw [MulEquiv.symm_apply_apply]

/-- Primitive package-base readback agrees on both sides of the generated
submonoid bridge. -/
@[simp] theorem represented_normalForm_base
    (form : NormalForm) :
    ((normalFormMulEquivRepresented form : representedSubmonoid).1).down.base =
      ((TagChangeGeneratedNormalForm.normalFormMulEquivGenerated form :
        TagChangeGeneratedNormalForm.actualGeneratedSubmonoid).1).hom := by
  change (evaluate form).down.base =
    (TagChangeGeneratedNormalForm.evaluate form).hom
  exact evaluate_base form

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm

end

end TagChangeExactGeometryNormalForm

end AAT.AG.LocalSemanticReconstruction
