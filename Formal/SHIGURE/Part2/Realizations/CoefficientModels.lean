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
  /-- The test object used to realize a native state of this sort. -/
  nativePointSource (R : CoefficientAlgebra base) (s : T.signature.SortType) : (rule R).Ambient
  /-- The rule for realizing a native input at the chosen coefficients. -/
  realizeNative (R : CoefficientAlgebra base) : Native → Object R
  /-- The correspondence of native and realized states. -/
  nativePoints (R : CoefficientAlgebra base) (A : Native) (s : T.signature.SortType) :
    nativeStates A s → (nativePointSource R s ⟶ (rule R).view.obj ((rule R).carrier (realizeNative R A) s))
  /-- Transport the primitive structure along a coefficient map. -/
  change {R : CoefficientAlgebra base} {S : CoefficientRing.{u}} (f : R.scalars.Hom S) :
    Object R → Object (R.extend f)
  /-- The change of coefficients on points read from the native-state test objects. -/
  changePoints {R : CoefficientAlgebra base} {S : CoefficientRing.{u}} (f : R.scalars.Hom S)
    (A : Object R) (s : T.signature.SortType) :
    (nativePointSource R s ⟶ (rule R).view.obj ((rule R).carrier A s)) →
      (nativePointSource (R.extend f) s ⟶
        (rule (R.extend f)).view.obj ((rule (R.extend f)).carrier (change f A) s))
  /-- Interpretation of each required Law of the selected theory. -/
  holds (R : CoefficientAlgebra base) (A : Object R) (statement : T.Statement) : Prop

namespace CoefficientRealizationMode

variable {base : CoefficientRing.{u}} {T : RealizationTheory.{u}}
variable (mode : CoefficientRealizationMode base T)

/-- A designated point is a map from the point object representing the mode's unit. -/
abbrev Points (R : CoefficientAlgebra base) (A : mode.Object R) (s : T.signature.SortType) :=
  (mode.rule R).pointObject ⟶ (mode.rule R).view.obj ((mode.rule R).carrier A s)

/-- Read a nullary total operation as a point of its declared output sort. -/
def nullaryPoint (R : CoefficientAlgebra base) (A : mode.Object R) (op : T.signature.Total)
    (h : (T.signature.totalArity op).inputs = []) : mode.Points R A (T.signature.totalArity op).output :=
  let rule := mode.rule R
  (rule.nullaryInputIso (rule.carrier A)).hom ≫
    eqToHom (congrArg (fun Γ => (rule.input Γ).obj (rule.carrier A)) h.symm) ≫ rule.total A op

/-- For a nullary total operation, its square commutes precisely when the designated point is preserved. -/
theorem nullaryPoint_preservation_iff {R : CoefficientAlgebra base} {A B : mode.Object R}
    (f : ∀ s, (mode.rule R).carrier A s ⟶ (mode.rule R).carrier B s) (op : T.signature.Total)
    (h : (T.signature.totalArity op).inputs = []) :
    let rule := mode.rule R
    rule.total A op ≫ rule.view.map (f _) = (rule.input _).map f ≫ rule.total B op ↔
      mode.nullaryPoint R A op h ≫ rule.view.map (f _) = mode.nullaryPoint R B op h := by
  let rule := mode.rule R
  let transport := fun X : mode.Object R =>
    eqToHom (congrArg (fun Γ => (rule.input Γ).obj (rule.carrier X)) h.symm)
  have natural : transport A ≫ (rule.input (T.signature.totalArity op).inputs).map f =
      (rule.input []).map f ≫ transport B :=
    (eqToHom_naturality (fun Γ => (rule.input Γ).map f) h.symm).symm
  have compare : ((rule.nullaryInputIso (rule.carrier A)).hom ≫ transport A) ≫
        (rule.input (T.signature.totalArity op).inputs).map f =
      (rule.nullaryInputIso (rule.carrier B)).hom ≫ transport B := by
    rw [Category.assoc, natural, ← Category.assoc, rule.nullaryInputIso_natural]
  change (_ = _) ↔ (_ = _)
  rw [← cancel_epi ((rule.nullaryInputIso (rule.carrier A)).hom ≫ transport A)]
  rw [← Category.assoc _ ((rule.input (T.signature.totalArity op).inputs).map f), compare]
  simp only [nullaryPoint, Category.assoc, transport]
  exact Iff.rfl

/-- A structural morphism maps designated points by composition with its carrier arrow. -/
def mapPoints {R : CoefficientAlgebra base} {A B : (mode.rule R).Category}
    (f : A ⟶ B) (s : T.signature.SortType) : mode.Points R A s → mode.Points R B s :=
  fun p => p ≫ (mode.rule R).view.map (f.val s)

/-- The carrier identity fixes every point. -/
@[simp]
theorem mapPoints_id {R : CoefficientAlgebra base} (A : (mode.rule R).Category)
    (s : T.signature.SortType) (p : mode.Points R A s) : mode.mapPoints (𝟙 A) s p = p := by
  change p ≫ (mode.rule R).view.map (𝟙 _) = p
  exact (congrArg (fun f => p ≫ f) ((mode.rule R).view.map_id _)).trans (Category.comp_id _)

/-- The action on points respects composition of carrier maps. -/
theorem mapPoints_comp {R : CoefficientAlgebra base} {A B D : (mode.rule R).Category}
    (f : A ⟶ B) (g : B ⟶ D) (s : T.signature.SortType) (p : mode.Points R A s) :
    mode.mapPoints (f ≫ g) s p = mode.mapPoints g s (mode.mapPoints f s p) := by
  change p ≫ (mode.rule R).view.map (f.val s ≫ g.val s) =
    (p ≫ (mode.rule R).view.map (f.val s)) ≫ (mode.rule R).view.map (g.val s)
  rw [Functor.map_comp, Category.assoc]

/-- Semantic objects satisfy the admissibility condition and all required Laws. -/
def modelProperty (R : CoefficientAlgebra base) : ObjectProperty (mode.rule R).Category :=
  fun A => mode.admissible R A ∧ ∀ name : T.LawName, mode.holds R A (T.law name)

/-- The semantic category of Definition 4.1 at a fixed coefficient algebra. -/
abbrev Models (R : CoefficientAlgebra base) :=
  (mode.modelProperty R).FullSubcategory

end CoefficientRealizationMode

end SHIGURE
