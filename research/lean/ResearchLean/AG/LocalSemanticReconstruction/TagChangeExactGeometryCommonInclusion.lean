import ResearchLean.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel
import Formal.Util.AssertStandardAxioms

/-!
# Inclusion of the generated exact branch into the common realization family

The represented exact one-object category of Cycle 43 is already a submonoid
of the tagged Hom in the common four-branch realization family.  This module
makes that relationship categorical: its sole object is sent to the tagged
family realization, and every represented Hom is sent to its actual common
exact-geometry Hom.

The functor is faithful and preserves the previously accepted normal-form
evaluation definitionally.  It does not claim fullness onto every tagged Hom,
assemble arbitrary local objects, or add reconstruction results for the other
three branches.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

namespace TagChangeExactGeometryCommonInclusion

noncomputable section

open TagChangeExactGeometryNormalForm
open TagChangeExactGeometryLocalModel

/-- The Cycle 43 represented exact category included in the tagged fiber of
the common realization family. -/
noncomputable def inclusion :
    GlobalCategory ⥤
      FamilyRealization
        (ClosedFamilyParameter.taggedOperation :
          ClosedFamilyParameter.{0, 0}) where
  obj _ := .taggedOperation
  map morphism := morphism.1
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Both endpoints of every represented exact Hom are the actual tagged
realization in the common family. -/
@[simp] theorem inclusion_obj (X : GlobalCategory) :
    inclusion.obj X =
      (FamilyRealization.taggedOperation :
        FamilyRealization
          (ClosedFamilyParameter.taggedOperation :
            ClosedFamilyParameter.{0, 0})) :=
  rfl

/-- Inclusion forgets only submonoid membership and retains the complete
exact-geometry Hom. -/
@[simp] theorem inclusion_map {X Y : GlobalCategory} (morphism : X ⟶ Y) :
    inclusion.map morphism = morphism.1 :=
  rfl

/-- The common-family inclusion preserves the accepted exact evaluation of
every generated normal form. -/
@[simp] theorem inclusion_map_normalForm
    (form : TagChangeGeneratedNormalForm.NormalForm) :
    inclusion.map
        (X := SingleObj.star ExactRepresentedSubmonoid)
        (Y := SingleObj.star ExactRepresentedSubmonoid)
        (normalFormMulEquivRepresented form :
          (SingleObj.star ExactRepresentedSubmonoid ⟶
            SingleObj.star ExactRepresentedSubmonoid)) =
      TagChangeExactGeometryNormalForm.evaluate form :=
  rfl

/-- Distinct represented exact morphisms remain distinct after entering the
common tagged fiber. -/
theorem inclusion_faithful : inclusion.Faithful where
  map_injective := by
    intro X Y first second equality
    exact Subtype.ext equality

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryCommonInclusion

end

end TagChangeExactGeometryCommonInclusion

end AAT.AG.LocalSemanticReconstruction
