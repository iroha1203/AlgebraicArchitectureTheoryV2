import ResearchLean.AG.RealizationReconstruction.AATClosedFamilySignature
import ResearchLean.AG.RealizationComparisonIdempotents.NormalizationCategory

/-!
# The fixed uniform-flip Karoubi witness for G-123(C)

This file completes the package-level part of the fixed G-123(C) witness.  The
single uniform Boolean-tag flip from `AATClosedFamilySignature` is involutive
on the entire G-117 tagged package, commutes with canonical normalization, and
is not the normalization itself.  Consequently normalization followed by the
uniform flip is a nonidentity automorphism of the actual Karoubi object
`(P,e)`.

The fixed-point functor forgets operation maps and therefore identifies `e`
and `et`; direct evaluation at the original `taggedBoolOperation` separates
their underlying package maps.  The latter is not yet the common
operation-preserving realization required by G-123(A), so that final bridge is
kept as a later obligation rather than encoded in this module.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.RealizationReconstruction

open AtomFoundation DoctrineFiberProduct
open RealizationComparisonIdempotents

/-- Casting the endpoint-dependent first component of a tagged operation
commutes with the endpoint-independent Boolean flip. -/
theorem taggedOperationCast_uniformFlip
    {alpha beta : Type} (equality : alpha = beta) (operation : alpha × Bool) :
    cast (congrArg (fun operationType => operationType × Bool) equality)
        (operation.1, !operation.2) =
      ((cast (congrArg (fun operationType => operationType × Bool) equality)
          operation).1,
        !(cast (congrArg (fun operationType => operationType × Bool) equality)
          operation).2) := by
  cases equality
  rfl

/-- The uniform flip is an involution as a morphism of the complete fixed
package, not merely pointwise on one selected operation. -/
theorem taggedUniformFlipTotal_square :
    taggedUniformFlipTotal.comp taggedUniformFlipTotal =
      PackageTotalHom.id taggedOperationPackage := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · apply SignedExactCoreReadingHom.ext
    · apply Equiv.ext
      intro atom
      rfl
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
      exact heq_of_eq (taggedUniformFlipAction_involutive operation)
    · rfl
    · rfl
    · rfl

/-- The uniform flip commutes with the canonical normalization on the complete
fixed package.  In contrast with the old endpoint-dependent flip, the same
Boolean action is used at every source and target. -/
theorem taggedUniformFlipTotal_commutes_normalization :
    (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp taggedUniformFlipTotal =
      taggedUniformFlipTotal.comp
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
      let sourceEquality :=
        finiteCanonicalObjectNormalization_admissible.operation_type_eq
          source target
      have admissibleEquality :
          taggedOperationPackage_admissible.operation_type_eq source target =
            congrArg (fun operationType => operationType × Bool) sourceEquality :=
        Subsingleton.elim _ _
      change taggedUniformFlipAction
          (cast (taggedOperationPackage_admissible.operation_type_eq source target)
            operation) =
        cast (taggedOperationPackage_admissible.operation_type_eq source target)
          (taggedUniformFlipAction operation)
      rw [admissibleEquality]
      exact (taggedOperationCast_uniformFlip sourceEquality operation).symm
    · rfl
    · rfl
    · rfl

/-- Normalization followed by the uniform flip changes the original test tag
from `false` to `true`. -/
theorem taggedNormalizationThenUniformFlip_snd :
    (((canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp
          taggedUniformFlipTotal).upper.operationMap taggedBoolOperation).2 = true := by
  change Bool.not ((canonicalObjectNormalizationTotal taggedOperationPackage
    taggedOperationPackage_admissible).upper.operationMap taggedBoolOperation).2 = true
  rw [taggedCanonicalNormalizationOperation_snd]
  rfl

/-- Canonical normalization alone preserves the original false tag. -/
theorem taggedNormalization_snd :
    ((canonicalObjectNormalizationTotal taggedOperationPackage
      taggedOperationPackage_admissible).upper.operationMap taggedBoolOperation).2 = false := by
  rw [taggedCanonicalNormalizationOperation_snd]
  rfl

/-- Evaluation of the operation-preserving reader at the original Boolean
test operation. -/
noncomputable def taggedOperationReader
    (f : PackageTotalHom taggedOperationPackage taggedOperationPackage) : Bool :=
  (f.upper.operationMap taggedBoolOperation).2

/-- The fixed composite `et` is not the Karoubi identity `e`, evaluated at the
card-mandated `taggedBoolOperation` with initial tag `false`. -/
theorem taggedNormalizationThenUniformFlip_ne_normalization :
    (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp taggedUniformFlipTotal ≠
      canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible := by
  intro equality
  have tagEquality := congrArg taggedOperationReader equality
  simp only [taggedOperationReader] at tagEquality
  rw [taggedNormalizationThenUniformFlip_snd, taggedNormalization_snd] at tagEquality
  contradiction

/-- A second operation at the unit-decorated endpoint is used only to prove
that the uniform action is not the old endpoint-dependent action. -/
noncomputable def taggedUnitOperation :
    taggedOperationPackage.reading.operationReading.Op
      finiteAxisFoldUnitObject finiteAxisFoldUnitObject := by
  refine ⟨?_, false⟩
  change ConfigurationHom
    (transportArchitectureObject
      finiteModelDoctrineFromFixture.atomEquiv.symm finiteAxisFoldUnitObject).configuration
    (transportArchitectureObject
      finiteModelDoctrineFromFixture.atomEquiv.symm finiteAxisFoldUnitObject).configuration
  exact ConfigurationHom.id _

/-- The new action is genuinely uniform and therefore differs from the old
endpoint-dependent flip away from the Boolean-decorated endpoint. -/
theorem taggedUniformFlipTotal_ne_endpointFlipTotal :
    taggedUniformFlipTotal ≠ taggedEndpointFlipTotal := by
  classical
  intro equality
  have tagEquality := congrArg
    (fun f : PackageTotalHom taggedOperationPackage taggedOperationPackage =>
      (f.upper.operationMap taggedUnitOperation).2) equality
  change true = (if finiteAxisFoldUnitObject = finiteAxisFoldBoolObject then
    true else false) at tagEquality
  simp [finiteAxisFoldUnitObject_ne_boolObject] at tagEquality

/-- The fixed tagged package as the admissible object used by the Karoubi
construction. -/
noncomputable def taggedUniformFlipPackage :
    CanonicalNormalizationAdmissiblePackage FiniteModel.carrier :=
  ⟨taggedOperationPackage, taggedOperationPackage_admissible⟩

/-- The uniform flip as an actual morphism in the same full admissible package
category used to form the Karoubi completion. -/
noncomputable def taggedUniformFlipMorphism :
    taggedUniformFlipPackage ⟶ taggedUniformFlipPackage :=
  ObjectProperty.homMk taggedUniformFlipTotal

/-- The canonical normalized Karoubi object `(P,e)` for the fixed package. -/
noncomputable abbrev taggedUniformFlipKaroubiObject :=
  normalizedPackageKaroubiObject taggedUniformFlipPackage

/-- The composite `et`, packaged as a Karoubi endomorphism.  Its sandwich law
is proved from the general normalization absorption theorem. -/
noncomputable def taggedNormalizationThenUniformFlipKaroubiHom :
    taggedUniformFlipKaroubiObject ⟶ taggedUniformFlipKaroubiObject where
  f := canonicalPackageNormalization taggedUniformFlipPackage ≫
    taggedUniformFlipMorphism
  comm := by
    change canonicalPackageNormalization taggedUniformFlipPackage ≫
        (canonicalPackageNormalization taggedUniformFlipPackage ≫
          taggedUniformFlipMorphism) ≫
          canonicalPackageNormalization taggedUniformFlipPackage =
      canonicalPackageNormalization taggedUniformFlipPackage ≫
        taggedUniformFlipMorphism
    simpa only [← Category.assoc, canonicalPackageNormalization_idem] using
      (canonicalPackageNormalization_absorption taggedUniformFlipMorphism)

/-- The raw admissible-package morphism underlying the `et` Karoubi
endomorphism is the package-level composite already evaluated above. -/
theorem taggedNormalizationThenUniformFlipKaroubiHom_f_hom :
    taggedNormalizationThenUniformFlipKaroubiHom.f.hom =
      (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp taggedUniformFlipTotal :=
  rfl

/-- The `et` Karoubi endomorphism is not the identity, whose underlying raw
map is the canonical idempotent `e`. -/
theorem taggedNormalizationThenUniformFlipKaroubiHom_ne_id :
    taggedNormalizationThenUniformFlipKaroubiHom ≠
      𝟙 taggedUniformFlipKaroubiObject := by
  intro equality
  have rawEquality := congrArg (fun f => f.f.hom) equality
  exact taggedNormalizationThenUniformFlip_ne_normalization rawEquality

/-- The uniform flip remains an involution in the admissible full
subcategory. -/
theorem taggedUniformFlipMorphism_square :
    taggedUniformFlipMorphism ≫ taggedUniformFlipMorphism =
      𝟙 taggedUniformFlipPackage := by
  apply ObjectProperty.hom_ext
  exact taggedUniformFlipTotal_square

/-- The package-level commutation theorem inside the admissible full
subcategory. -/
theorem taggedUniformFlipMorphism_commutes_normalization :
    canonicalPackageNormalization taggedUniformFlipPackage ≫
        taggedUniformFlipMorphism =
      taggedUniformFlipMorphism ≫
        canonicalPackageNormalization taggedUniformFlipPackage := by
  apply ObjectProperty.hom_ext
  exact taggedUniformFlipTotal_commutes_normalization

/-- The `et` Karoubi endomorphism is involutive, hence an automorphism of the
actual normalized Karoubi object. -/
noncomputable def taggedNormalizationThenUniformFlipKaroubiAut :
    Aut taggedUniformFlipKaroubiObject where
  hom := taggedNormalizationThenUniformFlipKaroubiHom
  inv := taggedNormalizationThenUniformFlipKaroubiHom
  hom_inv_id := by
    apply Karoubi.Hom.ext
    change (canonicalPackageNormalization taggedUniformFlipPackage ≫
        taggedUniformFlipMorphism) ≫
        (canonicalPackageNormalization taggedUniformFlipPackage ≫
          taggedUniformFlipMorphism) =
      canonicalPackageNormalization taggedUniformFlipPackage
    calc
      _ = canonicalPackageNormalization taggedUniformFlipPackage ≫
          (taggedUniformFlipMorphism ≫
            canonicalPackageNormalization taggedUniformFlipPackage) ≫
              taggedUniformFlipMorphism := by simp only [Category.assoc]
      _ = canonicalPackageNormalization taggedUniformFlipPackage ≫
          (canonicalPackageNormalization taggedUniformFlipPackage ≫
            taggedUniformFlipMorphism) ≫ taggedUniformFlipMorphism := by
            rw [← taggedUniformFlipMorphism_commutes_normalization]
      _ = (canonicalPackageNormalization taggedUniformFlipPackage ≫
          canonicalPackageNormalization taggedUniformFlipPackage) ≫
            (taggedUniformFlipMorphism ≫ taggedUniformFlipMorphism) := by
            simp only [Category.assoc]
      _ = canonicalPackageNormalization taggedUniformFlipPackage := by
            rw [canonicalPackageNormalization_idem,
              taggedUniformFlipMorphism_square, Category.comp_id]
  inv_hom_id := by
    apply Karoubi.Hom.ext
    change (canonicalPackageNormalization taggedUniformFlipPackage ≫
        taggedUniformFlipMorphism) ≫
        (canonicalPackageNormalization taggedUniformFlipPackage ≫
          taggedUniformFlipMorphism) =
      canonicalPackageNormalization taggedUniformFlipPackage
    calc
      _ = canonicalPackageNormalization taggedUniformFlipPackage ≫
          (taggedUniformFlipMorphism ≫
            canonicalPackageNormalization taggedUniformFlipPackage) ≫
              taggedUniformFlipMorphism := by simp only [Category.assoc]
      _ = canonicalPackageNormalization taggedUniformFlipPackage ≫
          (canonicalPackageNormalization taggedUniformFlipPackage ≫
            taggedUniformFlipMorphism) ≫ taggedUniformFlipMorphism := by
            rw [← taggedUniformFlipMorphism_commutes_normalization]
      _ = (canonicalPackageNormalization taggedUniformFlipPackage ≫
          canonicalPackageNormalization taggedUniformFlipPackage) ≫
            (taggedUniformFlipMorphism ≫ taggedUniformFlipMorphism) := by
            simp only [Category.assoc]
      _ = canonicalPackageNormalization taggedUniformFlipPackage := by
            rw [canonicalPackageNormalization_idem,
              taggedUniformFlipMorphism_square, Category.comp_id]

/-- Fixed architecture objects of an arbitrary Karoubi object in the
admissible package category.  Only the object map of the idempotent is read;
operations are deliberately absent from the codomain. -/
def FixedArchitectureObject {U : AtomCarrier.{u}}
    (X : Karoubi (CanonicalNormalizationAdmissiblePackage U)) :=
  { object : ArchitectureObject U // X.p.hom.upper.objectMap object = object }

/-- The actual object-fixed-point reader.  A Karoubi sandwich morphism sends a
fixed object to a fixed object because its defining equation is
`p ≫ f ≫ q = f`. -/
noncomputable def fixedArchitectureObjectFunctor (U : AtomCarrier.{u}) :
    Karoubi (CanonicalNormalizationAdmissiblePackage U) ⥤ Type (u + 1) where
  obj X := FixedArchitectureObject X
  map := fun {X Y} f object =>
    ⟨f.f.hom.upper.objectMap object.1, by
      have totalEquality := congrArg (fun k => k.hom) f.comm
      have objectMapEquality := congrArg (fun k => k.upper.objectMap) totalEquality
      have pointEquality := congrFun objectMapEquality object.1
      change Y.p.hom.upper.objectMap
          (f.f.hom.upper.objectMap (X.p.hom.upper.objectMap object.1)) =
        f.f.hom.upper.objectMap object.1 at pointEquality
      rw [object.property] at pointEquality
      exact pointEquality⟩
  map_id X := by
    funext object
    apply Subtype.ext
    exact object.property
  map_comp f g := by
    funext object
    rfl

/-- The actual fixed-point functor identifies the nonidentity `et` Karoubi
morphism with the Karoubi identity on the fixed tagged object. -/
theorem fixedArchitectureObjectFunctor_identifies_uniform_flip :
    (fixedArchitectureObjectFunctor FiniteModel.carrier).map
        taggedNormalizationThenUniformFlipKaroubiHom =
      (fixedArchitectureObjectFunctor FiniteModel.carrier).map
        (𝟙 taggedUniformFlipKaroubiObject) := by
  funext object
  apply Subtype.ext
  rfl

/-- A concrete failure of faithfulness for the object-fixed-point functor:
the two source morphisms are distinct but their images coincide. -/
theorem fixedArchitectureObjectFunctor_not_injective_at_tagged :
    ¬ Function.Injective
      (fun f : taggedUniformFlipKaroubiObject ⟶
          taggedUniformFlipKaroubiObject =>
        (fixedArchitectureObjectFunctor FiniteModel.carrier).map f) := by
  intro injective
  exact taggedNormalizationThenUniformFlipKaroubiHom_ne_id
    (injective fixedArchitectureObjectFunctor_identifies_uniform_flip)

/-- Direct operation evaluation distinguishes the same two raw package maps.
This is the package-level separation used by `et ≠ e`; connection to G-123(A)'s
operation-preserving realization remains a later proof obligation. -/
theorem taggedOperationReader_distinguishes_uniform_flip :
    taggedOperationReader
        ((canonicalObjectNormalizationTotal taggedOperationPackage
          taggedOperationPackage_admissible).comp taggedUniformFlipTotal) ≠
      taggedOperationReader
        (canonicalObjectNormalizationTotal taggedOperationPackage
          taggedOperationPackage_admissible) := by
  rw [show taggedOperationReader
        ((canonicalObjectNormalizationTotal taggedOperationPackage
          taggedOperationPackage_admissible).comp taggedUniformFlipTotal) = true from
      taggedNormalizationThenUniformFlip_snd]
  rw [show taggedOperationReader
        (canonicalObjectNormalizationTotal taggedOperationPackage
          taggedOperationPackage_admissible) = false from taggedNormalization_snd]
  decide

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
