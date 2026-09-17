import ResearchLean.AG.RealizationReconstruction.MandatoryCExplicitExactGeometryObstruction
import Formal.Util.AssertStandardAxioms

/-!
# Group laws for the tagged source-choice family

This file identifies the neutral member and composition law of the concrete
source-choice endomorphisms used by the G-124 local reconstruction checkpoint.
The statements concern the actual explicit exact geometry category, rather
than a function-level proxy.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation
open AAT.AG.RealizationReconstruction

/-- The constant-false source choice is the categorical identity of the fixed
tagged explicit exact geometry object. -/
@[simp] theorem taggedSourceChoiceExplicitExactGeometryMorphism_false :
    taggedSourceChoiceExplicitExactGeometryMorphism (fun _ => false) =
      (𝟙 taggedOperationExplicitExactGeometryObject) := by
  change taggedSourceChoiceExplicitExactGeometryHom (fun _ => false) =
    ExplicitExactGeometryHom.id taggedOperationGeometryPackage
  apply ExplicitExactGeometryHom.ext
  · apply PackageTotalHom.ext
    · rfl
    · apply SignedExactCoreReadingHom.ext
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  · rfl
  · rfl
  · rfl

/-- Composition of source-choice morphisms is pointwise exclusive-or of the
two choices.  This is an equality of actual morphisms in the explicit exact
geometry category. -/
@[simp] theorem taggedSourceChoiceExplicitExactGeometryMorphism_comp
    (first second : ArchitectureObject FiniteModel.carrier → Bool) :
    taggedSourceChoiceExplicitExactGeometryMorphism
        (fun source => Bool.xor (first source) (second source)) =
      taggedSourceChoiceExplicitExactGeometryMorphism first ≫
        taggedSourceChoiceExplicitExactGeometryMorphism second := by
  change taggedSourceChoiceExplicitExactGeometryHom _ =
    ExplicitExactGeometryHom.comp
      (taggedSourceChoiceExplicitExactGeometryHom first)
      (taggedSourceChoiceExplicitExactGeometryHom second)
  apply ExplicitExactGeometryHom.ext
  · apply PackageTotalHom.ext
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
        apply heq_of_eq
        change
          (operation.1,
              if Bool.xor (first source) (second source) then !operation.2
              else operation.2) =
            (operation.1,
              if second source then
                !(if first source then !operation.2 else operation.2)
              else if first source then !operation.2 else operation.2)
        cases first source <;> cases second source <;>
          cases operation.2 <;> rfl
      · rfl
      · rfl
      · rfl
  · apply RingHom.ext
    intro coefficient
    rfl
  · apply RawAmbientRestrictionSystemExactMapAgainst.hext
    · rfl
    · apply RingHom.ext
      intro coefficient
      rfl
    · apply heq_of_eq
      funext W
      apply CoordinateFamilyExactEquiv.ext
      · apply Equiv.ext
        intro coordinate
        rfl
      · apply heq_of_eq
        funext coordinate
        apply Equiv.ext
        intro datum
        rfl
    · apply heq_of_eq
      funext W
      apply StructuralRelationFamilyExactEquiv.ext
      apply Equiv.ext
      intro relation
      rfl
  · apply heq_of_eq
    apply ExplicitRealizationTransportSupply.ext
    · intro W V g
      rfl
    · intro W
      apply Equiv.ext
      intro support
      rfl
    · intro W
      apply Equiv.ext
      intro axis
      rfl
    · intro W
      apply Equiv.ext
      intro observable
      rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
