import Formal.SHIGURE.Part1.StructureCategory
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The semantic category and forgetting added Laws

## Implementation notes

Proposition 2.3 is about extending a written family of required Laws.
Each old Law must occur in the new family, which allows the declarations to
be renamed or repeated. Mere semantic implication would also allow replacing
the written Laws by unrelated syntax, while requiring a map of distinct
Law names would distinguish repeated copies.
-/

universe u

namespace SHIGURE

open CategoryTheory

/-- The predicate cutting out the full subcategory of models of a theory. -/
def Theory.modelProperty (T : Theory.{u}) : ObjectProperty (Structure T.signature) := T.Holds

/-- The semantic category is the full subcategory of structures satisfying the required Laws. -/
abbrev Model (T : Theory.{u}) : Type (u + 1) := T.modelProperty.FullSubcategory

/-- Two model arrows are equal when their maps on all carriers agree. -/
theorem Model.hom_ext {T : Theory.{u}} {A B : Model T} {f g : A ⟶ B}
    (same : ∀ s x, f.hom.onSort s x = g.hom.onSort s x) : f = g :=
  ObjectProperty.hom_ext T.modelProperty (StructureMap.ext same)

/-- The identity of the full model subcategory fixes every carrier element. -/
@[simp] theorem Model.id_apply {T : Theory.{u}} (A : Model T)
    (s : T.signature.SortType) (x : A.obj.carrier s) :
    (InducedCategory.Hom.hom (𝟙 A)).onSort s x = x :=
  Structure.id_apply A.obj s x

/-- The carrier maps of a composite in the full model category compose componentwise. -/
theorem Model.comp_apply {T : Theory.{u}} {A B C : Model T} (f : A ⟶ B) (g : B ⟶ C)
    (s : T.signature.SortType) (x : A.obj.carrier s) :
    (f ≫ g).hom.onSort s x = g.hom.onSort s (f.hom.onSort s x) := by
  rw [ObjectProperty.FullSubcategory.comp_hom]
  exact Structure.comp_apply f.hom g.hom s x

/-- A possibly larger family of required Laws on the original signature. -/
structure LawExtension (T : Theory.{u}) where
  /-- Names in the extended required family. -/
  LawName : Type u
  /-- Each required Law on the original signature. -/
  law : LawName → Law T.signature
  /-- Every old written Law appears in the extended family, as in Proposition 2.3. -/
  includes (name : T.LawName) : ∃ larger, law larger = T.law name

namespace LawExtension

variable {T : Theory.{u}}

/-- The larger theory has the same signature and the extended family of required Laws. -/
def theory (extension : LawExtension T) : Theory.{u} :=
  ⟨T.signature, extension.LawName, extension.law⟩

/-- A model of the extended theory also satisfies every original Law. -/
theorem model_le (extension : LawExtension T) :
    extension.theory.modelProperty ≤ T.modelProperty := by
  intro A model name
  obtain ⟨larger, equalLaw⟩ := extension.includes name
  rw [← equalLaw]
  exact model larger

/-- Proposition 2.3: forget the added model condition using mathlib's full inclusion. -/
def forget (extension : LawExtension T) : Model extension.theory ⥤ Model T :=
  ObjectProperty.ιOfLE extension.model_le

/-- The inclusion between two full model subcategories is full. -/
instance forgetFull (extension : LawExtension T) : extension.forget.Full :=
  ObjectProperty.full_ιOfLE extension.model_le

/-- The forgetful inclusion retains the underlying model arrow. -/
instance forgetFaithful (extension : LawExtension T) : extension.forget.Faithful :=
  ObjectProperty.faithful_ιOfLE extension.model_le

/-- The functor leaves the underlying structure unchanged. -/
theorem forget_obj (extension : LawExtension T) (A : Model extension.theory) :
    (extension.forget.obj A).obj = A.obj :=
  rfl

end LawExtension

end SHIGURE
