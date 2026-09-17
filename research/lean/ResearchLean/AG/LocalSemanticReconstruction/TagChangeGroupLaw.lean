import ResearchLean.AG.RealizationReconstruction.MandatoryCExplicitExactGeometryObstruction
import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.Group.Subgroup.Ker

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

/-- A source choice gives an actual automorphism: its inverse is the same
tag-change morphism because pointwise exclusive-or is self-cancelling. -/
noncomputable def taggedSourceChoiceAut
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    Aut taggedOperationExplicitExactGeometryObject where
  hom := taggedSourceChoiceExplicitExactGeometryMorphism choice
  inv := taggedSourceChoiceExplicitExactGeometryMorphism choice
  hom_inv_id := by
    calc
      _ = taggedSourceChoiceExplicitExactGeometryMorphism
          (fun source => Bool.xor (choice source) (choice source)) :=
        (taggedSourceChoiceExplicitExactGeometryMorphism_comp choice choice).symm
      _ = taggedSourceChoiceExplicitExactGeometryMorphism (fun _ => false) := by
        congr 1
        funext source
        exact Bool.xor_self (choice source)
      _ = 𝟙 taggedOperationExplicitExactGeometryObject :=
        taggedSourceChoiceExplicitExactGeometryMorphism_false
  inv_hom_id := by
    calc
      _ = taggedSourceChoiceExplicitExactGeometryMorphism
          (fun source => Bool.xor (choice source) (choice source)) :=
        (taggedSourceChoiceExplicitExactGeometryMorphism_comp choice choice).symm
      _ = taggedSourceChoiceExplicitExactGeometryMorphism (fun _ => false) := by
        congr 1
        funext source
        exact Bool.xor_self (choice source)
      _ = 𝟙 taggedOperationExplicitExactGeometryObject :=
        taggedSourceChoiceExplicitExactGeometryMorphism_false

/-- Distinct source choices give distinct actual automorphisms. -/
theorem taggedSourceChoiceAut_injective :
    Function.Injective taggedSourceChoiceAut := by
  intro first second equality
  apply taggedSourceChoiceExplicitExactGeometryMorphism_injective
  exact congrArg Iso.hom equality

/-- The pointwise `C₂`-power maps homomorphically to the actual automorphism
group.  `Multiplicative` turns the additive xor law on Bool-valued functions
into the group multiplication used by `Aut`. -/
noncomputable def taggedSourceChoiceAutHom :
    Multiplicative (ArchitectureObject FiniteModel.carrier → Bool) →*
      Aut taggedOperationExplicitExactGeometryObject where
  toFun choice := taggedSourceChoiceAut choice.toAdd
  map_one' := by
    apply Iso.ext
    exact taggedSourceChoiceExplicitExactGeometryMorphism_false
  map_mul' first second := by
    apply Iso.ext
    change taggedSourceChoiceExplicitExactGeometryMorphism
        (fun source => Bool.xor (first.toAdd source) (second.toAdd source)) =
      taggedSourceChoiceExplicitExactGeometryMorphism second.toAdd ≫
        taggedSourceChoiceExplicitExactGeometryMorphism first.toAdd
    rw [← taggedSourceChoiceExplicitExactGeometryMorphism_comp]
    congr 1
    funext source
    exact Bool.xor_comm (first.toAdd source) (second.toAdd source)

/-- The source-choice group homomorphism is faithful. -/
theorem taggedSourceChoiceAutHom_injective :
    Function.Injective taggedSourceChoiceAutHom := by
  intro first second equality
  apply Multiplicative.ext
  apply taggedSourceChoiceAut_injective
  exact equality

/-- The actual subgroup of exact-geometry automorphisms realized by arbitrary
source-indexed Boolean tag changes. -/
noncomputable def taggedSourceChoiceAutSubgroup :
    Subgroup (Aut taggedOperationExplicitExactGeometryObject) :=
  taggedSourceChoiceAutHom.range

/-- The pointwise `C₂`-power is the actual source-choice automorphism subgroup,
as a group rather than merely as a bijection of underlying functions. -/
noncomputable def taggedSourceChoiceGroupEquiv :
    Multiplicative (ArchitectureObject FiniteModel.carrier → Bool) ≃*
      taggedSourceChoiceAutSubgroup :=
  MonoidHom.ofInjective taggedSourceChoiceAutHom_injective

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
