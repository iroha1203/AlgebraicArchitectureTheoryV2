import Mathlib.CategoryTheory.SingleObj
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel
import Formal.Util.AssertStandardAxioms

/-!
# Finite-local reading of the common exact-geometry image

Cycle 42 identified the faithful image of generated normal forms inside the
common tagged exact-geometry fiber.  This module reads that image directly
from its primitive package base and identifies it with the accepted finite
local-section monoid.  The monoid equivalence is then delooped to a
one-object category equivalence.

This is the common-global generated branch only.  It does not assemble
arbitrary objects of the fixed G-124 local category or integrate the four
source, target, composition, and identity families.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct
open AAT.AG.RealizationReconstruction

namespace TagChangeExactGeometryLocalModel

noncomputable section

open TagChangeExactGeometryNormalForm
open TagChangeGeneratedLocalModel
open TagChangeGeneratedNormalForm
open TagChangeKaroubiReconstruction

/-- The Cycle 42 common exact image, named locally to distinguish it from the
earlier package-level represented submonoid. -/
abbrev ExactRepresentedSubmonoid :=
  TagChangeExactGeometryNormalForm.representedSubmonoid

/-- The common exact-geometry image is the finite-local section monoid. -/
noncomputable def representedMulEquivLocalSection :
    ExactRepresentedSubmonoid ≃* LocalSection :=
  representedMulEquivPackageGenerated.trans
    actualGeneratedMulEquivLocalSection

/-- The exact-to-local equivalence sends an evaluated normal form to its
accepted finite-local reading. -/
@[simp] theorem representedMulEquivLocalSection_on_normalForm
    (form : NormalForm) :
    representedMulEquivLocalSection
        (normalFormMulEquivRepresented form) = read form := by
  change actualGeneratedMulEquivLocalSection
      (representedMulEquivPackageGenerated
        (normalFormMulEquivRepresented form)) = read form
  rw [representedMulEquivPackageGenerated_on_normalForm]
  change normalFormMulEquivLocalSection
      (normalFormMulEquivGenerated.symm
        (normalFormMulEquivGenerated form)) = read form
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Every represented exact morphism has the same primitive package base as
its package-generated bridge image. -/
theorem represented_base (morphism : ExactRepresentedSubmonoid) :
    morphism.1.down.base =
      ((representedMulEquivPackageGenerated morphism :
        actualGeneratedSubmonoid).1).hom := by
  let form := normalFormMulEquivRepresented.symm morphism
  have formEquality : normalFormMulEquivRepresented form = morphism :=
    normalFormMulEquivRepresented.apply_symm_apply morphism
  rw [← formEquality]
  rw [representedMulEquivPackageGenerated_on_normalForm]
  exact represented_normalForm_base form

/-- Read the source choice directly from a represented exact morphism's
primitive package base. -/
noncomputable def readExactChoice
    (morphism : ExactRepresentedSubmonoid) : Choice :=
  readTaggedSourceChoice morphism.1.down.base

/-- Read the normalization bit directly from the primitive upper object map
of a represented exact morphism. -/
noncomputable def readExactNormalizedFlag
    (morphism : ExactRepresentedSubmonoid) : Bool := by
  classical
  exact if morphism.1.down.base.upper.objectMap flagWitness = flagWitness then
    false
  else
    true

/-- Direct exact source-choice readback agrees with the accepted package
readback after the bridge. -/
theorem readExactChoice_eq_package
    (morphism : ExactRepresentedSubmonoid) :
    readExactChoice morphism =
      readActualChoice (representedMulEquivPackageGenerated morphism) := by
  unfold readExactChoice readActualChoice
  rw [represented_base]

/-- Direct exact normalization readback agrees with the accepted package
readback after the bridge. -/
theorem readExactNormalizedFlag_eq_package
    (morphism : ExactRepresentedSubmonoid) :
    readExactNormalizedFlag morphism =
      readActualNormalizedFlag
        (representedMulEquivPackageGenerated morphism) := by
  classical
  unfold readExactNormalizedFlag readActualNormalizedFlag
    primitiveNormalizationFlag
  rw [represented_base]

/-- The local normalization bit is read directly from the exact morphism's
primitive upper object map. -/
theorem representedMulEquivLocalSection_normalized
    (morphism : ExactRepresentedSubmonoid) :
    (representedMulEquivLocalSection morphism).normalized =
      readExactNormalizedFlag morphism := by
  change
    (actualGeneratedMulEquivLocalSection
      (representedMulEquivPackageGenerated morphism)).normalized = _
  rw [actualGeneratedMulEquivLocalSection_normalized]
  exact (readExactNormalizedFlag_eq_package morphism).symm

/-- Every finite table is read directly from the exact morphism's primitive
operation map. -/
theorem representedMulEquivLocalSection_value
    (morphism : ExactRepresentedSubmonoid) (S : Finset Index) :
    (representedMulEquivLocalSection morphism).family.value S =
      TagChange.LocalTagTable.read (readExactChoice morphism) S := by
  change
    (actualGeneratedMulEquivLocalSection
      (representedMulEquivPackageGenerated morphism)).family.value S = _
  rw [actualGeneratedMulEquivLocalSection_value]
  exact congrArg (fun choice => TagChange.LocalTagTable.read choice S)
    (readExactChoice_eq_package morphism).symm

/-- The complete finite local value is the primitive flag/table readback from
the represented exact morphism. -/
theorem representedMulEquivLocalSection_localValue
    (morphism : ExactRepresentedSubmonoid) (S : Finset Index) :
    value (representedMulEquivLocalSection morphism) S =
      (readExactNormalizedFlag morphism,
        TagChange.LocalTagTable.read (readExactChoice morphism)
          (normalizationClosure S)) := by
  apply Prod.ext
  · exact representedMulEquivLocalSection_normalized morphism
  · change
      (representedMulEquivLocalSection morphism).family.value
          (normalizationClosure S) = _
    exact representedMulEquivLocalSection_value morphism
      (normalizationClosure S)

/-- The represented exact image as a one-object category. -/
abbrev GlobalCategory := SingleObj ExactRepresentedSubmonoid

/-- The accepted finite-local section monoid as a one-object category. -/
abbrev LocalCategory := SingleObj LocalSection

/-- Primitive finite-local Hom reading of represented exact morphisms. -/
noncomputable def reading : GlobalCategory ⥤ LocalCategory :=
  SingleObj.mapHom ExactRepresentedSubmonoid LocalSection
    representedMulEquivLocalSection.toMonoidHom

/-- Every categorical Hom value is the direct primitive exact readback at the
specified finite index. -/
theorem reading_map_value {X Y : GlobalCategory} (morphism : X ⟶ Y)
    (S : Finset Index) :
    value (reading.map morphism) S =
      (readExactNormalizedFlag morphism,
        TagChange.LocalTagTable.read (readExactChoice morphism)
          (normalizationClosure S)) :=
  representedMulEquivLocalSection_localValue morphism S

/-- Primitive Hom reading separates represented exact morphisms. -/
theorem morphism_separates {X Y : GlobalCategory} :
    Function.Injective
      (reading.map : (X ⟶ Y) → (reading.obj X ⟶ reading.obj Y)) :=
  representedMulEquivLocalSection.injective

/-- Every finite-local Hom assembles to a represented exact morphism. -/
theorem morphism_assembles {X Y : GlobalCategory} :
    Function.Surjective
      (reading.map : (X ⟶ Y) → (reading.obj X ⟶ reading.obj Y)) :=
  representedMulEquivLocalSection.surjective

/-- Essential-image witness for the sole object of the generated exact
branch.  This is not arbitrary-object assembly for fixed G-124 B. -/
theorem object_assembles (Z : LocalCategory) :
    ∃ X : GlobalCategory, Nonempty (reading.obj X ≅ Z) := by
  exact ⟨SingleObj.star ExactRepresentedSubmonoid,
    ⟨eqToIso (Subsingleton.elim _ _)⟩⟩

/-- The represented common exact category is equivalent to its finite-local
section category. -/
noncomputable def equivalence : GlobalCategory ≌ LocalCategory :=
  representedMulEquivLocalSection.toSingleObjEquiv

/-- The equivalence's forward functor is primitive exact reading. -/
@[simp] theorem equivalence_functor : equivalence.functor = reading :=
  rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel

end

end TagChangeExactGeometryLocalModel

end AAT.AG.LocalSemanticReconstruction
