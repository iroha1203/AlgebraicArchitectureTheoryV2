import ResearchLean.AG.RealizationComparisonIdempotents.FunctorNaturality
import Mathlib.CategoryTheory.Core

/-!
# Reversible changes as the maximal subgroupoid

This file constructs G-119(A3).  Reversible representation changes form the
core of `Arrow (Karoubi E)`: all comparison objects are retained, while a
morphism is exactly an isomorphism of comparison objects.

## Implementation notes

Mathlib's `CategoryTheory.Core` is the canonical maximal subgroupoid and is
used directly.  A full subcategory on only invertible comparison arrows would
drop noninvertible comparisons from the object type, contrary to the fixed
target.  The object-surjectivity theorem below records that no invertibility
condition is imposed on a comparison object.  The factorization theorem records
the universal maximality property for every groupoid-valued source functor.
-/

open CategoryTheory CategoryTheory.Idempotents

universe v₁ v₂ u₁ u₂

namespace AAT.AG.RealizationComparisonIdempotents

variable (E : Type u₁) [Category.{v₁} E]

/-- The comparison category `M(E) = Arrow (Karoubi E)`. -/
abbrev RealizationComparisonCategory := Arrow (Karoubi E)

/-- G-119(A3): the category of reversible representation changes. -/
abbrev ReversibleRepresentationChanges := Core (RealizationComparisonCategory E)

/-- The faithful inclusion of reversible changes into all comparison changes. -/
def reversibleRepresentationInclusion :
    ReversibleRepresentationChanges E ⥤ RealizationComparisonCategory E :=
  Core.inclusion _

/-- Normalization rule: inclusion retains the underlying comparison object. -/
@[simp]
theorem reversibleRepresentationInclusion_obj
    (P : ReversibleRepresentationChanges E) :
    (reversibleRepresentationInclusion E).obj P = P.of :=
  rfl

/-- Normalization rule: inclusion sends a core morphism to its isomorphism hom. -/
@[simp]
theorem reversibleRepresentationInclusion_map
    {P Q : ReversibleRepresentationChanges E} (f : P ⟶ Q) :
    (reversibleRepresentationInclusion E).map f = f.iso.hom :=
  rfl

/-- Every comparison object belongs to the maximal subgroupoid, independently
of whether its comparison arrow is invertible. -/
theorem reversibleRepresentationInclusion_obj_surjective :
    Function.Surjective (reversibleRepresentationInclusion E).obj := by
  intro P
  exact ⟨⟨P⟩, rfl⟩

/-- Morphisms in the maximal subgroupoid are exactly isomorphisms between the
same objects in the comparison category. -/
def reversibleRepresentationHomEquiv
    (P Q : ReversibleRepresentationChanges E) :
    (P ⟶ Q) ≃ (P.of ≅ Q.of) where
  toFun f := f.iso
  invFun e := ⟨e⟩
  left_inv f := by cases f; rfl
  right_inv e := rfl

/-- Normalization rule exposing the isomorphism represented by a core morphism. -/
@[simp]
theorem reversibleRepresentationHomEquiv_apply
    (P Q : ReversibleRepresentationChanges E) (f : P ⟶ Q) :
    reversibleRepresentationHomEquiv E P Q f = f.iso :=
  rfl

variable {E}
variable {G : Type u₂} [Groupoid.{v₂} G]

/-- Every functor from a groupoid into the comparison category factors through
the reversible representation changes. -/
def reversibleRepresentationLift
    (F : G ⥤ RealizationComparisonCategory E) :
    G ⥤ ReversibleRepresentationChanges E :=
  Core.functorToCore F

/-- Normalization rule: the maximal-subgroupoid lift retains every object. -/
@[simp]
theorem reversibleRepresentationLift_obj
    (F : G ⥤ RealizationComparisonCategory E) (X : G) :
    ((reversibleRepresentationLift F).obj X).of = F.obj X :=
  rfl

/-- Normalization rule: the lifted morphism represents the original mapped
morphism as the hom of an isomorphism. -/
@[simp]
theorem reversibleRepresentationLift_map_iso_hom
    (F : G ⥤ RealizationComparisonCategory E) {X Y : G} (f : X ⟶ Y) :
    ((reversibleRepresentationLift F).map f).iso.hom = F.map f :=
  rfl

/-- The groupoid lift followed by inclusion is the original functor. -/
theorem reversibleRepresentationLift_comp_inclusion
    (F : G ⥤ RealizationComparisonCategory E) :
    reversibleRepresentationLift F ⋙ reversibleRepresentationInclusion E = F :=
  rfl

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
