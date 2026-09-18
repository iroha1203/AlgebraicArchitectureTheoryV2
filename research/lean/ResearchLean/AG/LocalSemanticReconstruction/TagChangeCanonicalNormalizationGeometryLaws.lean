import ResearchLean.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometry
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel
import Formal.Util.AssertStandardAxioms

/-!
# Exact-geometry laws for canonical tagged normalization

Cycle 39 placed canonical tagged normalization in the common tagged
`FamilyRealization` fiber.  This module proves its first two generation laws
there as equalities of actual exact-geometry morphisms: idempotence and the
canonical restriction law for arbitrary source choices.

The proofs compare every computational component of
`ExplicitExactGeometryHom`; package-level equality alone is not used as the
conclusion.  This does not yet identify the full generated image or construct
the common local-reading category.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open AAT.AG.RealizationReconstruction

namespace TagChangeCanonicalNormalizationGeometryLaws

noncomputable section

open TagChangeCanonicalNormalizationGeometry
open TagChangeNormalizedChoiceKernel

/-- Heterogeneous extensionality for explicit realization supplies whose
equation transports are propositionally the same. -/
theorem taggedExplicitRealizationSupply_hext
    {firstAtom secondAtom :
      FiniteModel.carrier.Atom ≃ FiniteModel.carrier.Atom}
    {firstObject secondObject :
      ArchitectureObject FiniteModel.carrier →
        ArchitectureObject FiniteModel.carrier}
    {firstTransport : EquationSystemExactTransport
      taggedOperationPackage.algebra.equationSystem
      taggedOperationPackage.algebra.equationSystem firstAtom firstObject}
    {secondTransport : EquationSystemExactTransport
      taggedOperationPackage.algebra.equationSystem
      taggedOperationPackage.algebra.equationSystem secondAtom secondObject}
    (hatom : firstAtom = secondAtom)
    (hobject : firstObject = secondObject)
    (htransport : HEq firstTransport secondTransport)
    {first : EquationExplicitRealizationSupply firstTransport}
    {second : EquationExplicitRealizationSupply secondTransport}
    (hcontext : ∀ {W V : Site.ContextCategoryObject
        taggedOperationPackage.algebra.contextPreorder}
      (morphism : Site.ContextMorphism W.ctx V.ctx),
      HEq (first.contextMorphism morphism)
        (second.contextMorphism morphism))
    (hsupport : ∀ W support,
      HEq (first.supportEquiv W support) (second.supportEquiv W support))
    (haxis : ∀ W axis,
      HEq (first.axisEquiv W axis) (second.axisEquiv W axis))
    (hobservable : ∀ W observable,
      HEq (first.observableEquiv W observable)
        (second.observableEquiv W observable)) :
    HEq first second := by
  cases hatom
  cases hobject
  cases htransport
  have context_eq : @first.contextMorphism = @second.contextMorphism := by
    funext W V morphism
    exact eq_of_heq (hcontext morphism)
  have support_eq : first.supportEquiv = second.supportEquiv := by
    funext W
    apply Equiv.ext
    intro support
    exact eq_of_heq (hsupport W support)
  have axis_eq : first.axisEquiv = second.axisEquiv := by
    funext W
    apply Equiv.ext
    intro axis
    exact eq_of_heq (haxis W axis)
  have observable_eq : first.observableEquiv = second.observableEquiv := by
    funext W
    apply Equiv.ext
    intro observable
    exact eq_of_heq (hobservable W observable)
  cases first
  cases second
  cases context_eq
  cases support_eq
  cases axis_eq
  cases observable_eq
  rfl

/-- Canonical tagged normalization is idempotent in the common tagged fiber,
as an equality of actual exact-geometry morphisms. -/
@[simp] theorem closedFamilyTaggedNormalization_idempotent :
    closedFamilyTaggedNormalization ≫ closedFamilyTaggedNormalization =
      closedFamilyTaggedNormalization := by
  apply ULift.ext
  change ExplicitExactGeometryHom.comp
      normalizationExplicitExactGeometryHom
      normalizationExplicitExactGeometryHom =
    normalizationExplicitExactGeometryHom
  have base_idempotent :
      (ExplicitExactGeometryHom.comp
        normalizationExplicitExactGeometryHom
        normalizationExplicitExactGeometryHom).base =
      normalizationExplicitExactGeometryHom.base :=
    canonicalObjectNormalizationTotal_comp taggedOperationPackage
      taggedOperationPackage_admissible
  apply ExplicitExactGeometryHom.ext
  · exact base_idempotent
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
  · apply taggedExplicitRealizationSupply_hext
    · apply Equiv.ext
      intro atom
      rfl
    · funext object
      exact canonicalObjectNormalization_idempotent
        taggedOperationPackage object
    · change HEq
        ((canonicalObjectNormalizationEquationTransport
          taggedOperationPackage taggedOperationPackage_admissible).comp
            (canonicalObjectNormalizationEquationTransport
              taggedOperationPackage taggedOperationPackage_admissible))
        (canonicalObjectNormalizationEquationTransport
          taggedOperationPackage taggedOperationPackage_admissible)
      exact canonicalObjectNormalizationEquationTransport_comp_heq
        taggedOperationPackage taggedOperationPackage_admissible
    · intro W V morphism
      rfl
    · intro W support
      rfl
    · intro W axis
      rfl
    · intro W observable
      rfl

/-- Left composition by canonical normalization depends only on the
canonically restricted source choice, now at the common exact-geometry Hom
level rather than only after reading the package base. -/
theorem closedFamilyTaggedNormalization_comp_sourceChoice
    (choice : TagChangeKaroubiReconstruction.Choice) :
    closedFamilyTaggedNormalization ≫ closedFamilyTaggedSourceChoice choice =
      closedFamilyTaggedNormalization ≫
        closedFamilyTaggedSourceChoice (normalizeChoice choice) := by
  apply ULift.ext
  change ExplicitExactGeometryHom.comp
      normalizationExplicitExactGeometryHom
      (taggedSourceChoiceExplicitExactGeometryHom choice) =
    ExplicitExactGeometryHom.comp
      normalizationExplicitExactGeometryHom
      (taggedSourceChoiceExplicitExactGeometryHom (normalizeChoice choice))
  have base_normalized :
      (ExplicitExactGeometryHom.comp
        normalizationExplicitExactGeometryHom
        (taggedSourceChoiceExplicitExactGeometryHom choice)).base =
      (ExplicitExactGeometryHom.comp
        normalizationExplicitExactGeometryHom
        (taggedSourceChoiceExplicitExactGeometryHom
          (normalizeChoice choice))).base :=
    normalization_comp_sourceChoice_eq_normalized choice
  apply ExplicitExactGeometryHom.ext
  · exact base_normalized
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
  · apply taggedExplicitRealizationSupply_hext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · rfl
    · intro W V morphism
      rfl
    · intro W support
      rfl
    · intro W axis
      rfl
    · intro W observable
      rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryLaws

end

end TagChangeCanonicalNormalizationGeometryLaws

end AAT.AG.LocalSemanticReconstruction
