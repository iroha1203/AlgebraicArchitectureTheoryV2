import Formal.SHIGURE.Part1.ContextMorphisms
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The contravariant category of models on declaration contexts

A model is a structure in the context satisfying its retained required Laws.
The full subcategory keeps all structure-preserving maps. The morphisms of
contexts are inclusions, so restrictions form an ordinary functor into Cat.
-/

universe u

namespace SHIGURE
namespace DeclarationContext

open CategoryTheory

variable {P : PrimitivePresentation.{u}} {U V W : DeclarationContext P}

/-- A structure models the required Laws of the restricted presentation. -/
def ModelCondition (U : DeclarationContext P) : ObjectProperty (ContextStructure U) :=
  fun A => ∀ name : U.scopedTheory.LawName,
    A.evaluation.satisfies (U.scopedTheory.law name) (Declaration.lawBody_subset_of_mem name.property)

/-- The category of models of the restricted presentation includes all its structural arrows. -/
abbrev Models (U : DeclarationContext P) := (ModelCondition U).FullSubcategory

namespace Models

/-- A model gives satisfaction of every retained required Law. -/
theorem satisfies_required (A : Models U) (name : U.scopedTheory.LawName) :
    A.obj.evaluation.satisfies (U.scopedTheory.law name) (Declaration.lawBody_subset_of_mem name.property) :=
  A.property name

/-- Restricting a model keeps the required Laws that belong to the smaller presentation. -/
noncomputable def restrict (A : Models U) (inside : V ≤ U) : Models V :=
  ⟨A.obj.restrict inside, fun name =>
    (A.obj.restrict_satisfies_iff inside (V.scopedTheory.law name)
      (Declaration.lawBody_subset_of_mem name.property)).2
      (A.satisfies_required ⟨name.val, inside name.property⟩)⟩

/-- The underlying structure of a restricted model is the associated structure reduct. -/
theorem restrict_obj (A : Models U) (inside : V ≤ U) : (A.restrict inside).obj = A.obj.restrict inside :=
  rfl

/-- A model is recovered after restricting to its original context. -/
theorem restrict_id (A : Models U) : A.restrict (le_refl U) = A :=
  ObjectProperty.FullSubcategory.ext A.obj.restrict_id

/-- Restricting a model in two steps is strictly equal to restricting it in one step. -/
theorem restrict_comp (A : Models U) (inside : V ≤ U) (smaller : W ≤ V) :
    (A.restrict inside).restrict smaller = A.restrict (smaller.trans inside) :=
  ObjectProperty.FullSubcategory.ext (A.obj.restrict_comp inside smaller)

/-- A categorical model arrow has the usual retained carrier function. -/
abbrev onSort {A B : Models U} (f : A ⟶ B) := (show ContextStructure.Hom A.obj B.obj from f.hom).onSort

/-- Packaging a structure arrow as a model arrow retains its carrier function. -/
theorem onSort_homMk {A B : Models U} (f : ContextStructure.Hom A.obj B.obj)
    (s : P.signature.SortType) (kept : Declaration.sort s ∈ U.declarations) (x : A.obj.carrier s) :
    onSort (ObjectProperty.homMk f : A ⟶ B) s kept x = f.onSort s kept x :=
  rfl

/-- The model identity is the identity at each retained sort. -/
@[simp] theorem id_onSort (A : Models U) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ U.declarations) (x : A.obj.carrier s) : onSort (𝟙 A) s kept x = x :=
  rfl

/-- Cartesian components of a model composite compose as functions. -/
@[simp] theorem comp_onSort {A B C : Models U} (f : A ⟶ B) (g : B ⟶ C) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ U.declarations) (x : A.obj.carrier s) :
    onSort (f ≫ g) s kept x = onSort g s kept (onSort f s kept x) :=
  rfl

/-- Equality transport on a model arrow induces the corresponding carrier transport. -/
theorem eqToHom_onSort {A B : Models U} (same : A = B) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ U.declarations) (x : A.obj.carrier s) :
    onSort (eqToHom same) s kept x = cast (congrArg (fun A => A.obj.carrier s) same) x := by
  subst B
  rfl

/-- Model arrow equality is determined by all retained carrier functions. -/
@[ext] theorem hom_ext {A B : Models U} {f g : A ⟶ B}
    (same : ∀ s kept x, onSort f s kept x = onSort g s kept x) : f = g :=
  ObjectProperty.hom_ext _ (ContextStructure.Hom.ext same)

end Models

/-- Equation (3.1): apply the same declaration restriction to model objects and arrows. -/
noncomputable def res (inside : V ≤ U) : Models U ⥤ Models V where
  obj A := A.restrict inside
  map f := ObjectProperty.homMk ((ContextStructure.restrictFunctor inside).map f.hom)
  map_id A := ObjectProperty.hom_ext _ ((ContextStructure.restrictFunctor inside).map_id A.obj)
  map_comp f g := ObjectProperty.hom_ext _ ((ContextStructure.restrictFunctor inside).map_comp f.hom g.hom)

/-- On objects the model restriction is the corresponding reduct. -/
@[simp] theorem res_obj (inside : V ≤ U) (A : Models U) : (res inside).obj A = A.restrict inside :=
  rfl

/-- The structure map underlying a restricted model arrow is its structure reduct. -/
theorem res_map (inside : V ≤ U) {A B : Models U} (f : A ⟶ B) :
    ((res inside).map f).hom = (ContextStructure.restrictFunctor inside).map f.hom :=
  rfl

/-- Restricting a model arrow transports each retained component along its carrier equalities. -/
theorem res_onSort (inside : V ≤ U) {A B : Models U} (f : A ⟶ B) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ V.declarations) (x : (A.restrict inside).obj.carrier s) :
    Models.onSort ((res inside).map f) s keep x =
      cast (B.obj.restrict_carrier inside keep).symm
        (Models.onSort f s (inside keep) (selectedMap V A.obj.carrier s keep x)) :=
  rfl

/-- The model restriction for the identity inclusion is strictly the identity functor. -/
theorem res_id : res (le_refl U) = 𝟭 (Models U) := by
  refine Functor.ext (fun A => A.restrict_id) ?_
  intro A B f
  apply Models.hom_ext
  intro s kept x
  simp only [res_onSort, selectedMap_apply, Models.comp_onSort, Models.eqToHom_onSort, Functor.id_map]

/-- Model reducts compose strictly along successive inclusions. -/
theorem res_comp (inside : V ≤ U) (smaller : W ≤ V) :
    res inside ⋙ res smaller = res (smaller.trans inside) := by
  refine Functor.ext (fun A => A.restrict_comp inside smaller) ?_
  intro A B f
  apply Models.hom_ext
  intro s kept x
  simp only [Functor.comp_map, res_onSort, selectedMap_apply, Models.comp_onSort, Models.eqToHom_onSort, cast_cast]

/-- The presheaf of model categories takes every declaration inclusion to the corresponding reduct. -/
noncomputable def modelPresheaf (P : PrimitivePresentation.{u}) :
    (DeclarationContext P)ᵒᵖ ⥤ Cat.{u, u + 1} where
  obj U := Cat.of (Models (Opposite.unop U))
  map f := (res (leOfHom f.unop)).toCatHom
  map_id _ := congrArg Functor.toCatHom res_id
  map_comp f g := congrArg Functor.toCatHom (res_comp (leOfHom f.unop) (leOfHom g.unop)).symm

end DeclarationContext
end SHIGURE
