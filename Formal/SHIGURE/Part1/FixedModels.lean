import Formal.SHIGURE.Part1.Models
import Formal.SHIGURE.Part1.SelectedPresentation
import Mathlib.CategoryTheory.Widesubcategory

/-! # Models with fixed data

## Implementation notes

Definition 2.2 specifies an actual fixed reduct. A chosen isomorphism would also
admit models with different reducts and make the fixed arrow condition depend on
the chosen identifications. The structure equality here determines how to
transport the identity components between carriers.

The induced category retains each fixed object and its underlying model arrow.
The mathlib wide subcategory construction then restricts those arrows by the
condition on the designated sorts.
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

/-- A fixed model map restricts to the identity on every designated carrier. -/
def FixesCarriers (A B : FixedModel T names data) (f : A.model ⟶ B.model) : Prop :=
  ∀ s (x : A.model.obj.carrier (names.val.onSort s)),
    f.hom.onSort (names.val.onSort s) x = cast ((A.carrier_eq s).trans (B.carrier_eq s).symm) x

private abbrev Ambient :=
  InducedCategory (Model T) (FixedModel.model (T := T) (names := names) (data := data))

private def condition : MorphismProperty (Ambient (T := T) (names := names) (data := data)) :=
  fun A B f => FixesCarriers A B f.hom

/-- Identities and composition in the induced category fix the designated carriers. -/
private instance condition_multiplicative :
    (condition (T := T) (names := names) (data := data)).IsMultiplicative where
  id_mem _ := fun _ _ => rfl
  comp_mem {A B C} f g hf hg := by
    intro s x
    change (f.hom ≫ g.hom).hom.onSort (names.val.onSort s) x =
      cast ((A.carrier_eq s).trans (C.carrier_eq s).symm) x
    rw [Model.comp_apply, hf s, hg s, cast_cast]

private def includeAmbient (A : FixedModel T names data) :
    Ambient (T := T) (names := names) (data := data) := A

/-- The category of models with a common fixed reduct, using mathlib's wide subcategory. -/
instance category : Category.{u} (FixedModel T names data) :=
  InducedWideCategory.category includeAmbient condition

/-- An arrow in the fixed-data category. -/
abbrev Hom (A B : FixedModel T names data) := A ⟶ B

namespace Hom

variable {A B : FixedModel T names data}

/-- A model map fixing the specified carriers is an arrow of the fixed-data category. -/
def mk (f : A.model ⟶ B.model) (fixes : FixesCarriers A B f) : Hom A B :=
  ⟨InducedCategory.homMk f, fixes⟩

/-- Forget the carrier-fixing evidence on a map. -/
def modelHom (f : Hom A B) : A.model ⟶ B.model :=
  f.val.hom

/-- The component on every fixed sort is the transported identity. -/
theorem fixes (f : Hom A B) : FixesCarriers A B f.modelHom :=
  f.property

/-- A map with fixed carriers is determined by its underlying model map. -/
@[ext] theorem ext {f g : Hom A B} (same : f.modelHom = g.modelHom) : f = g :=
  Subtype.ext (InducedCategory.hom_ext same)

end Hom

/-- The inclusion into the full semantic category forgets the extra carrier conditions. -/
def forget : FixedModel T names data ⥤ Model T where
  obj A := A.model
  map f := (show Hom _ _ from f).modelHom

/-- Two arrows of the fixed-data category with the same underlying model arrow coincide. -/
instance forgetFaithful : (forget (T := T) (names := names) (data := data)).Faithful where
  map_injective := Hom.ext

end FixedModel

end SHIGURE
