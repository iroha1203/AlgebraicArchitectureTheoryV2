import Formal.SHIGURE.Part1.CoefficientReading
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Semantic categories for coefficient realization modes

The four rules of Definition 4.1 specify allowable carrier maps, primitive
structures and their preservation, change of coefficients, and the
interpretation of Laws. The morphisms of the semantic category are the
carrier maps satisfying the preservation conditions of equation (2.1).

## Implementation notes

The category is constructed from the preservation predicate on a tuple of
carrier arrows. Supplying an independent category and a map from its arrows
to point functions would allow missing preservation maps and duplicate
representatives. Keeping the actual carrier arrows also retains all
components of a sheaf map.
-/

open CategoryTheory

universe u v w t

namespace SHIGURE

/-- The primitive structures, allowed carrier arrows and their preservation condition. -/
structure StructureRule {S : Type u} (C : S → Cat.{v, w}) (Object : Type t) where
  /-- The carrier object at every sort. -/
  carrier (A : Object) (s : S) : C s
  /-- The simultaneous preservation conditions on a family of allowed carrier arrows. -/
  preserves {A B : Object} (f : ∀ s, carrier A s ⟶ carrier B s) : Prop
  /-- The identity family satisfies the preservation conditions. -/
  preserves_id (A : Object) : preserves (fun s => 𝟙 (carrier A s))
  /-- The composite of two preserving families preserves the structure. -/
  preserves_comp {A B D : Object} {f : ∀ s, carrier A s ⟶ carrier B s}
    {g : ∀ s, carrier B s ⟶ carrier D s} :
    preserves f → preserves g → preserves (fun s => f s ≫ g s)

namespace StructureRule

variable {S : Type u} {C : S → Cat.{v, w}} {Object : Type t}

/-- The category of primitive structures before imposing the required Laws. -/
def Category (_rule : StructureRule C Object) : Type t := Object

/-- Take every preserving family of the allowable carrier arrows as a morphism. -/
instance category (rule : StructureRule C Object) : CategoryTheory.Category.{max u v} rule.Category where
  Hom A B := {f : ∀ s, rule.carrier A s ⟶ rule.carrier B s // rule.preserves f}
  id A := ⟨fun s => 𝟙 (rule.carrier A s), rule.preserves_id A⟩
  comp f g := ⟨fun s => f.val s ≫ g.val s, rule.preserves_comp f.property g.property⟩
  id_comp _ := Subtype.ext (funext fun _ => CategoryTheory.Category.id_comp _)
  comp_id _ := Subtype.ext (funext fun _ => CategoryTheory.Category.comp_id _)
  assoc _ _ _ := Subtype.ext (funext fun _ => CategoryTheory.Category.assoc _ _ _)

/-- The arrow equivalence records exactly which carrier families are included. -/
def homEquiv (rule : StructureRule C Object) (A B : rule.Category) :
    (A ⟶ B) ≃ {f : ∀ s, rule.carrier A s ⟶ rule.carrier B s // rule.preserves f} :=
  Equiv.refl _

end StructureRule

/-- A coefficient realization mode for a theory and a chosen coefficient base. -/
structure CoefficientRealizationMode (base : CoefficientRing.{u}) (T : Theory.{u}) where
  /-- The raw primitive structures at each coefficient algebra. -/
  Object (R : CoefficientAlgebra base) : Type t
  /-- The allowable carriers and their allowable maps by sort. -/
  Carrier (R : CoefficientAlgebra base) (s : T.signature.SortType) : Cat.{v, w}
  /-- The structure-preservation test for families of allowable maps. -/
  rule (R : CoefficientAlgebra base) : StructureRule (Carrier R) (Object R)
  /-- The structures admitted by the mode, independently of the Law test. -/
  admissible (R : CoefficientAlgebra base) : Object R → Prop
  /-- Native inputs and their state sets. -/
  Native : Type (u + 1)
  nativeStates (A : Native) (s : T.signature.SortType) : Type u
  /-- Designated state sets of the realization for each sort. -/
  States (R : CoefficientAlgebra base) (A : Object R) (s : T.signature.SortType) : Type u
  /-- The rule for realizing a native input at the chosen coefficients. -/
  realizeNative (R : CoefficientAlgebra base) : Native → Object R
  /-- The correspondence of native and realized states. -/
  nativePoints (R : CoefficientAlgebra base) (A : Native) (s : T.signature.SortType) :
    nativeStates A s → States R (realizeNative R A) s
  /-- Transport the primitive structure along a coefficient map. -/
  change {R : CoefficientAlgebra base} {S : CoefficientRing.{u}} (f : R.scalars.Hom S) :
    Object R → Object (R.extend f)
  /-- The state map induced by the change of coefficients. -/
  changePoints {R : CoefficientAlgebra base} {S : CoefficientRing.{u}} (f : R.scalars.Hom S)
    (A : Object R) (s : T.signature.SortType) :
    States R A s → States (R.extend f) (change f A) s
  /-- Interpretation of each required Law of the selected theory. -/
  holds (R : CoefficientAlgebra base) (A : Object R) (name : T.LawName) : Prop

namespace CoefficientRealizationMode

variable {base : CoefficientRing.{u}} {T : Theory.{u}}
variable (mode : CoefficientRealizationMode.{u, v, w, t} base T)

/-- Semantic objects satisfy the admissibility condition and all required Laws. -/
def modelProperty (R : CoefficientAlgebra base) : ObjectProperty (mode.rule R).Category :=
  fun A => mode.admissible R A ∧ ∀ name : T.LawName, mode.holds R A name

/-- The semantic category of Definition 4.1 at a fixed coefficient algebra. -/
abbrev Models (R : CoefficientAlgebra base) :=
  (mode.modelProperty R).FullSubcategory

end CoefficientRealizationMode

end SHIGURE
