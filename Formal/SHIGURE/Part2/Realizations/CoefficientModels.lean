import Formal.SHIGURE.Part1.CoefficientReading
import Formal.SHIGURE.Part2.Realizations.StructureRules
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Semantic categories for coefficient realization modes

The four rules of Definition 4.1 specify allowable carrier maps, primitive
structures and their preservation, change of coefficients, and the
interpretation of Laws. The morphisms of the semantic category are the
carrier maps satisfying the preservation conditions of equation (2.1).

## Implementation notes

The category is constructed from the primitive diagrams on a tuple of
carrier arrows. Supplying an independent category and a map from its arrows
to point functions would allow missing preservation maps and duplicate
representatives. Keeping the actual carrier arrows also retains all
components of a sheaf map.
-/

open CategoryTheory

universe u v w t

namespace SHIGURE

/-- The written required Laws and the primitive signature they use. -/
structure RealizationTheory where
  /-- The primitive symbols of the chosen presentation. -/
  signature : Signature.{u}
  /-- The required declarations. -/
  LawName : Type u
  /-- The syntax in which the Laws are written. -/
  Statement : Type u
  /-- The actual written statement of each declaration. -/
  law : LawName → Statement

/-- The set-based presentation already carries its written positive sequents. -/
def RealizationTheory.ofTheory (T : Theory.{u}) : RealizationTheory.{u} where
  signature := T.signature
  LawName := T.LawName
  Statement := Law T.signature
  law := T.law

/-- A coefficient realization mode for a theory and a chosen coefficient base. -/
structure CoefficientRealizationMode (base : CoefficientRing.{u}) (T : RealizationTheory.{u}) where
  /-- The raw primitive structures at each coefficient algebra. -/
  Object (R : CoefficientAlgebra base) : Type t
  /-- The allowable carriers and their allowable maps. -/
  Carrier (R : CoefficientAlgebra base) : Cat.{v, w}
  /-- The interpreted primitives, whose diagrams determine the semantic arrows. -/
  rule (R : CoefficientAlgebra base) : StructureRule T.signature (Carrier R) (Object R)
  /-- The structures admitted by the mode, independently of the Law test. -/
  admissible (R : CoefficientAlgebra base) : Object R → Prop
  /-- Native inputs and their state sets. -/
  Native : Type (u + 1)
  /-- The original states at each sort, which are the input to the native point map. -/
  nativeStates (A : Native) (s : T.signature.SortType) : Type u
  /-- The object representing a designated point of a realized carrier. -/
  pointCarrier (R : CoefficientAlgebra base) (s : T.signature.SortType) : Carrier R
  /-- The rule for realizing a native input at the chosen coefficients. -/
  realizeNative (R : CoefficientAlgebra base) : Native → Object R
  /-- The correspondence of native and realized states. -/
  nativePoints (R : CoefficientAlgebra base) (A : Native) (s : T.signature.SortType) :
    nativeStates A s → (pointCarrier R s ⟶ (rule R).carrier (realizeNative R A) s)
  /-- Transport the primitive structure along a coefficient map. -/
  change {R : CoefficientAlgebra base} {S : CoefficientRing.{u}} (f : R.scalars.Hom S) :
    Object R → Object (R.extend f)
  /-- The state map induced by the change of coefficients. -/
  changePoints {R : CoefficientAlgebra base} {S : CoefficientRing.{u}} (f : R.scalars.Hom S)
    (A : Object R) (s : T.signature.SortType) :
    (pointCarrier R s ⟶ (rule R).carrier A s) →
      (pointCarrier (R.extend f) s ⟶ (rule (R.extend f)).carrier (change f A) s)
  /-- Interpretation of each required Law of the selected theory. -/
  holds (R : CoefficientAlgebra base) (A : Object R) (statement : T.Statement) : Prop

namespace CoefficientRealizationMode

variable {base : CoefficientRing.{u}} {T : RealizationTheory.{u}}
variable (mode : CoefficientRealizationMode.{u, v, w, t} base T)

/-- Designated points are actual maps to the realized carrier. -/
abbrev Points (R : CoefficientAlgebra base) (A : mode.Object R) (s : T.signature.SortType) :=
  mode.pointCarrier R s ⟶ (mode.rule R).carrier A s

/-- A structural morphism maps designated points by composition with its carrier arrow. -/
def mapPoints {R : CoefficientAlgebra base} {A B : (mode.rule R).Category}
    (f : A ⟶ B) (s : T.signature.SortType) : mode.Points R A s → mode.Points R B s :=
  fun p => p ≫ f.val s

/-- The carrier identity fixes every point. -/
@[simp]
theorem mapPoints_id {R : CoefficientAlgebra base} (A : (mode.rule R).Category)
    (s : T.signature.SortType) (p : mode.Points R A s) : mode.mapPoints (𝟙 A) s p = p :=
  Category.comp_id _

/-- The action on points respects composition of carrier maps. -/
theorem mapPoints_comp {R : CoefficientAlgebra base} {A B D : (mode.rule R).Category}
    (f : A ⟶ B) (g : B ⟶ D) (s : T.signature.SortType) (p : mode.Points R A s) :
    mode.mapPoints (f ≫ g) s p = mode.mapPoints g s (mode.mapPoints f s p) :=
  (Category.assoc p (f.val s) (g.val s)).symm

/-- Semantic objects satisfy the admissibility condition and all required Laws. -/
def modelProperty (R : CoefficientAlgebra base) : ObjectProperty (mode.rule R).Category :=
  fun A => mode.admissible R A ∧ ∀ name : T.LawName, mode.holds R A (T.law name)

/-- The semantic category of Definition 4.1 at a fixed coefficient algebra. -/
abbrev Models (R : CoefficientAlgebra base) :=
  (mode.modelProperty R).FullSubcategory

end CoefficientRealizationMode

end SHIGURE
