import Formal.SHIGURE.Part1.Models
import Formal.SHIGURE.Part1.SelectedPresentation

/-! # Models with fixed data

## Implementation notes

The fixed reduct is a structure equality. Arrow components on the designated sorts
are identities transported along the two endpoint carrier equalities.
-/

universe u

namespace SHIGURE

open CategoryTheory

/-- A closed inclusion of signatures preserves all arities and embeds each family of names. -/
def SignatureNames.IsInclusion {S T : Signature.{u}} (n : SignatureNames S T) : Prop :=
  Function.Injective n.onSort ∧ Function.Injective n.onTotal ∧ Function.Injective n.onRel ∧
    Function.Injective n.onPartial ∧ Function.Injective n.onQuantity

/-- A closed named subsignature of an ambient signature. -/
abbrev Subsignature (S T : Signature.{u}) := { n : SignatureNames S T // n.IsInclusion }

/-- A model whose restriction to the specified subsignature is the specified structure. -/
structure FixedModel (T : Theory.{u}) {S : Signature.{u}}
    (names : Subsignature S T.signature) (data : Structure S) where
  model : Model T
  fixed : names.val.restrict model.obj = data

namespace FixedModel

variable {T : Theory.{u}} {S : Signature.{u}} {names : Subsignature S T.signature} {data : Structure S}

/-- Each fixed sort has the prescribed carrier. -/
theorem carrier_eq (A : FixedModel T names data) (s : S.SortType) :
    A.model.obj.carrier (names.val.onSort s) = data.carrier s :=
  congrArg (fun X => X.carrier s) A.fixed

/-- A fixed-data map is the identity on every prescribed carrier, after identifying the two carriers. -/
structure Hom (A B : FixedModel T names data) where
  modelHom : A.model ⟶ B.model
  fixes (s : S.SortType) (x : A.model.obj.carrier (names.val.onSort s)) :
    modelHom.hom.onSort (names.val.onSort s) x = cast ((A.carrier_eq s).trans (B.carrier_eq s).symm) x

namespace Hom

variable {A B C D : FixedModel T names data}

/-- A map with fixed carriers is determined by its underlying model map. -/
@[ext] theorem ext {f g : Hom A B} (same : f.modelHom = g.modelHom) : f = g := by
  cases f
  cases g
  cases same
  rfl

/-- Identity fixes every prescribed carrier. -/
def id (A : FixedModel T names data) : Hom A A :=
  ⟨𝟙 A.model, fun _ _ => rfl⟩

/-- Two maps fixing the prescribed carriers have a composite that fixes the same carriers. -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  modelHom := f.modelHom ≫ g.modelHom
  fixes s x := by
    rw [Model.comp_apply, f.fixes, g.fixes, cast_cast]

end Hom

/-- The category of models with a common fixed restriction. -/
instance category : Category.{u} (FixedModel T names data) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp f.modelHom)
  comp_id f := Hom.ext (Category.comp_id f.modelHom)
  assoc f g h := Hom.ext (Category.assoc f.modelHom g.modelHom h.modelHom)

/-- Forget that the structure and all arrows fix the chosen reduct. -/
def forget : FixedModel T names data ⥤ Model T where
  obj A := A.model
  map f := (show Hom _ _ from f).modelHom

instance : (forget (T := T) (names := names) (data := data)).Faithful where
  map_injective := Hom.ext

end FixedModel

end SHIGURE
