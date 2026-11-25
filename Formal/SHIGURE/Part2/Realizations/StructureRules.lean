import Formal.SHIGURE.Part1.Signature
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# Primitive structure rules and their maps

A realization represents each primitive by an actual arrow or a monomorphism
in its carrier category. Its input functors specify how carrier maps act on
tuples of the chosen mode. The morphisms are precisely the families obeying
the commutativity and factorization equations of (2.1).

## Implementation notes

The carrier category specifies the allowed maps of states. A faithful
functor displays those maps in the category where primitive diagrams are
formed. For example, permutations may be the allowed maps even though the
inputs of operations and the states of points are formed in sets. A mode
constructs its typed product from the declared positions. An interpreted input
can identify tuples, provided a natural epimorphism presents it from the full
product. The copying and tensor modes use Cartesian and tensor products.
A mode can also compare its inputs with tuples of generalized points. The tuple comparison
makes carrier maps act on every entry and requires the resulting tuples to
determine arrows out of the input object. Comparing after restriction along
a test map gives the same tuple as restricting each entry before comparison.
The point object represents the empty input. Each mode also specifies
how it reads native points of a carrier.
-/

open CategoryTheory
open scoped MonoidalCategory

universe u v w t h d hp dp

namespace SHIGURE

/-- The primitive data and the allowable carrier maps of a structure mode. -/
structure StructureRule (sig : Signature.{u}) (C : Cat.{v, w}) (Object : Type t) where
  /-- The object realizing each carrier sort. -/
  carrier : Object → sig.SortType → C
  /-- The category in which primitive operations and their inputs are displayed. -/
  Ambient : Cat.{h, d}
  /-- Display each allowed carrier object and its allowed arrows in the ambient category. -/
  view : C ⥤ Ambient
  /-- The displayed action determines the original allowable carrier arrow. -/
  view_faithful : view.Faithful
  /-- The chosen representation of input objects and input maps. -/
  input (Γ : List sig.SortType) : (sig.SortType → C) ⥤ Ambient
  /-- The combination of carriers at precisely the variable positions of an arity. -/
  positionalInput (Γ : List sig.SortType) : (((s : sig.SortType) × Var Γ s) → C) ⥤ Ambient
  /-- Identify the chosen input representation with the combination of the declared arguments. -/
  inputIso (Γ : List sig.SortType) :
    input Γ ≅ Pi.comap (fun _ : sig.SortType => C) (fun i : (s : sig.SortType) × Var Γ s => i.1) ⋙
      positionalInput Γ
  /-- A single input is naturally the carrier of its declared sort. -/
  unaryIso (s : sig.SortType) : input [s] ≅ Pi.eval (fun _ : sig.SortType => C) s ⋙ view
  /-- The mode's product of independently specified entries. -/
  monoidal : MonoidalCategory Ambient
  /-- The full typed product before identifying any input tuples. -/
  fullInput (Γ : List sig.SortType) : (sig.SortType → C) ⥤ Ambient
  /-- The full product at the empty arity is the unit of the mode. -/
  fullInput_nil :
    letI := monoidal
    fullInput [] ≅ (Functor.const (sig.SortType → C)).obj (𝟙_ Ambient)
  /-- A further position in the full product attaches its declared carrier. -/
  fullInput_cons (s : sig.SortType) (Γ : List sig.SortType) :
    letI := monoidal
    fullInput (s :: Γ) ≅ ((Pi.eval (fun _ : sig.SortType => C) s ⋙ view).prod' (fullInput Γ)) ⋙
      MonoidalCategory.tensor Ambient
  /-- Interpret the full typed product of a nonempty arity in the chosen presentation. -/
  positiveInputComparison (s : sig.SortType) (Γ : List sig.SortType) : fullInput (s :: Γ) ⟶ input (s :: Γ)
  /-- The interpreted input is presented by the full typed product. -/
  positiveInputComparison_epi (s : sig.SortType) (Γ : List sig.SortType) (A : sig.SortType → C) :
    Epi ((positiveInputComparison s Γ).app A)
  /-- The source object for a nullary primitive value. -/
  pointObject : Ambient
  /-- The point source represents the actual unit of the mode. -/
  pointUnit :
    letI := monoidal
    pointObject ≅ 𝟙_ Ambient
  /-- The empty arity has the same point object at every carrier family. -/
  nullaryInput : (Functor.const (sig.SortType → C)).obj pointObject ≅ input []
  /-- A total operation from its entire input object. -/
  total (A : Object) (f : sig.Total) : (input (sig.totalArity f).inputs).obj (carrier A) ⟶
    view.obj (carrier A (sig.totalArity f).output)
  /-- A relation as a subobject of its input object. -/
  relation (A : Object) (r : sig.Rel) :
    MonoOver ((input (sig.relInputs r)).obj (carrier A))
  /-- The specified domain of a partial operation. -/
  domain (A : Object) (p : sig.Partial) :
    MonoOver ((input (sig.partialArity p).inputs).obj (carrier A))
  /-- The partial operation on its specified domain. -/
  partialValue (A : Object) (p : sig.Partial) :
    (domain A p : Ambient) ⟶ view.obj (carrier A (sig.partialArity p).output)
  /-- The map reading a quantity. -/
  quantity (A : Object) (q : sig.Quantity) : (input (sig.quantityArity q).inputs).obj (carrier A) ⟶
    view.obj (carrier A (sig.quantityArity q).output)

/-- A pointwise interpretation of inputs for modes that use generalized tuples. -/
structure StructureInputPoints {sig : Signature.{u}} {C : Cat.{v, w}} {Object : Type t}
    (rule : StructureRule sig C Object) where
  /-- Test objects and the actual restrictions between their generalized points. -/
  Probe : Cat.{hp, dp}
  /-- Represent the tests and restrictions in the diagram category. -/
  probe : Probe ⥤ rule.Ambient
  /-- Map a tuple of the declared entries into the interpreted input. -/
  tuplePoint (P : Probe) (Γ : List sig.SortType) (A : sig.SortType → C) :
    (∀ i : (s : sig.SortType) × Var Γ s, probe.obj P ⟶ rule.view.obj (A i.1)) →
      (probe.obj P ⟶ (rule.input Γ).obj A)
  /-- Applying the input map computes the comparison of the changed entries. -/
  tuplePoint_map (P : Probe) (Γ : List sig.SortType) {A B : sig.SortType → C} (f : A ⟶ B)
    (p : ∀ i : (s : sig.SortType) × Var Γ s, probe.obj P ⟶ rule.view.obj (A i.1)) :
    tuplePoint P Γ A p ≫ (rule.input Γ).map f = tuplePoint P Γ B (fun i => p i ≫ rule.view.map (f i.1))
  /-- Building a tuple commutes with restricting every entry along the same probe map. -/
  tuplePoint_restrict {P Q : Probe} (g : Q ⟶ P) (Γ : List sig.SortType) (A : sig.SortType → C)
    (p : ∀ i : (s : sig.SortType) × Var Γ s, probe.obj P ⟶ rule.view.obj (A i.1)) :
    tuplePoint Q Γ A (fun i => probe.map g ≫ p i) = probe.map g ≫ tuplePoint P Γ A p
  /-- Generalized tuples determine an arrow out of the interpreted input object. -/
  tuplePoint_ext (Γ : List sig.SortType) (A : sig.SortType → C) {Y : rule.Ambient}
    {f g : (rule.input Γ).obj A ⟶ Y} :
    (∀ (P : Probe) (p : ∀ i : (s : sig.SortType) × Var Γ s, probe.obj P ⟶ rule.view.obj (A i.1)),
      tuplePoint P Γ A p ≫ f = tuplePoint P Γ A p ≫ g) → f = g

namespace StructureRule

variable {sig : Signature.{u}} {C : Cat.{v, w}} {Object : Type t}
variable (rule : StructureRule sig C Object)

private def emptyInputComparison : rule.fullInput [] ≅ rule.input [] :=
  letI := rule.monoidal
  rule.fullInput_nil ≪≫ (Functor.const (sig.SortType → C)).mapIso rule.pointUnit.symm ≪≫ rule.nullaryInput

/-- The full typed product presents the interpreted input at every arity. -/
def inputComparison : (Γ : List sig.SortType) → rule.fullInput Γ ⟶ rule.input Γ
  | [] => rule.emptyInputComparison.hom
  | s :: Γ => rule.positiveInputComparison s Γ

/-- The full input comparison determines any arrow out of the interpreted input. -/
theorem inputComparison_epi (Γ : List sig.SortType) (A : sig.SortType → C) :
    Epi ((rule.inputComparison Γ).app A) := by
  cases Γ with
  | nil =>
    change Epi (rule.emptyInputComparison.app A).hom
    infer_instance
  | cons s Γ => exact rule.positiveInputComparison_epi s Γ A

/-- On an input, changing carriers is the combination of just the declared argument maps. -/
theorem input_map_positions (Γ : List sig.SortType) {A B : sig.SortType → C} (f : A ⟶ B) :
    (rule.input Γ).map f ≫ (rule.inputIso Γ).hom.app B =
      (rule.inputIso Γ).hom.app A ≫ (rule.positionalInput Γ).map (fun i => f i.1) :=
  (rule.inputIso Γ).hom.naturality f

/-- Changes in undeclared arguments cannot change the input map. -/
theorem input_map_positions_congr (Γ : List sig.SortType) {A B : sig.SortType → C} {f g : A ⟶ B}
    (h : ∀ i : (s : sig.SortType) × Var Γ s, f i.1 = g i.1) :
    (rule.input Γ).map f = (rule.input Γ).map g := by
  apply (cancel_mono ((rule.inputIso Γ).hom.app B)).mp
  simp only [rule.input_map_positions, funext h]

/-- In a unary operation, the input map is the specified map of its single sort. -/
theorem input_map_unary (s : sig.SortType) {A B : sig.SortType → C} (f : A ⟶ B) :
    (rule.input [s]).map f ≫ (rule.unaryIso s).hom.app B = (rule.unaryIso s).hom.app A ≫ rule.view.map (f s) :=
  (rule.unaryIso s).hom.naturality f

/-- Unary input maps are equal exactly when the displayed carrier maps are equal. -/
theorem input_map_unary_eq_iff (s : sig.SortType) {A B : sig.SortType → C} (f g : A ⟶ B) :
    (rule.input [s]).map f = (rule.input [s]).map g ↔ f s = g s := by
  constructor
  · intro h
    letI := rule.view_faithful
    apply rule.view.map_injective
    apply (cancel_epi ((rule.unaryIso s).hom.app A)).mp
    rw [← rule.input_map_unary, ← rule.input_map_unary, h]
  · intro h
    apply (cancel_mono ((rule.unaryIso s).hom.app B)).mp
    simp only [rule.input_map_unary, h]

/-- Identify the empty input with the point object. -/
def nullaryInputIso (A : sig.SortType → C) : rule.pointObject ≅ (rule.input []).obj A :=
  rule.nullaryInput.app A

/-- Changing the carriers fixes the unique empty tuple. -/
theorem nullaryInputIso_natural {A B : sig.SortType → C} (f : A ⟶ B) :
    (rule.nullaryInputIso A).hom ≫ (rule.input []).map f = (rule.nullaryInputIso B).hom := by
  have h := rule.nullaryInput.hom.naturality f
  change 𝟙 rule.pointObject ≫ rule.nullaryInput.hom.app B =
    rule.nullaryInput.hom.app A ≫ (rule.input []).map f at h
  rw [Category.id_comp] at h
  exact h.symm

/-- A square for a nullary primitive is exactly preservation of its specified point. -/
theorem nullary_square_iff {A B : sig.SortType → C} (f : A ⟶ B)
    {X Y : rule.Ambient} (p : (rule.input []).obj A ⟶ X) (q : (rule.input []).obj B ⟶ Y) (g : X ⟶ Y) :
    p ≫ g = (rule.input []).map f ≫ q ↔
      (rule.nullaryInputIso A).hom ≫ p ≫ g = (rule.nullaryInputIso B).hom ≫ q := by
  rw [← cancel_epi ((rule.nullaryInputIso A).hom), ← Category.assoc _ ((rule.input []).map f),
    rule.nullaryInputIso_natural]

/-- Assemble every declared point in the full product, including the empty tuple. -/
def fullInputPoint (A : sig.SortType → C) : (Γ : List sig.SortType) →
    (∀ i : (s : sig.SortType) × Var Γ s, rule.pointObject ⟶ rule.view.obj (A i.1)) →
      (rule.pointObject ⟶ (rule.fullInput Γ).obj A)
  | [], _ => by
    letI := rule.monoidal
    exact rule.pointUnit.hom ≫ rule.fullInput_nil.inv.app A
  | s :: Γ, p => by
    letI := rule.monoidal
    exact (ρ_ rule.pointObject).inv ≫
      (p ⟨s, .here⟩ ⊗ₘ (rule.pointUnit.inv ≫ fullInputPoint A Γ (fun i => p ⟨i.1, .there i.2⟩))) ≫
        (rule.fullInput_cons s Γ).inv.app A

/-- Evaluating a total primitive on any tuple of points produces a point of its output sort. -/
def totalAtTuple (A : Object) (op : sig.Total)
    (p : ∀ i : (s : sig.SortType) × Var (sig.totalArity op).inputs s,
      rule.pointObject ⟶ rule.view.obj (rule.carrier A i.1)) :
    rule.pointObject ⟶ rule.view.obj (rule.carrier A (sig.totalArity op).output) :=
  rule.fullInputPoint (rule.carrier A) (sig.totalArity op).inputs p ≫
    (rule.inputComparison (sig.totalArity op).inputs).app (rule.carrier A) ≫ rule.total A op

/-- The represented full input determines each operation square. -/
theorem total_preservation_iff_onFullInput {A B : Object}
    (f : ∀ s, rule.carrier A s ⟶ rule.carrier B s) (op : sig.Total) :
    let Γ := (sig.totalArity op).inputs
    let α := rule.inputComparison Γ
    (rule.total A op ≫ rule.view.map (f _) = (rule.input Γ).map f ≫ rule.total B op) ↔
      α.app (rule.carrier A) ≫ rule.total A op ≫ rule.view.map (f _) =
        (rule.fullInput Γ).map f ≫ α.app (rule.carrier B) ≫ rule.total B op := by
  intro Γ α
  letI := rule.inputComparison_epi Γ (rule.carrier A)
  rw [← cancel_epi (α.app (rule.carrier A)), ← Category.assoc _ ((rule.input Γ).map f),
    ← α.naturality, Category.assoc]

/-- The operation square agrees with the square on every tuple of generalized points. -/
theorem total_preservation_iff_onTuples (tests : StructureInputPoints rule) {A B : Object}
    (f : ∀ s, rule.carrier A s ⟶ rule.carrier B s) (op : sig.Total) :
    let Γ := (sig.totalArity op).inputs
    (rule.total A op ≫ rule.view.map (f _) = (rule.input Γ).map f ≫ rule.total B op) ↔
      ∀ (P : tests.Probe)
        (p : ∀ i : (s : sig.SortType) × Var Γ s, tests.probe.obj P ⟶ rule.view.obj (rule.carrier A i.1)),
        tests.tuplePoint P Γ (rule.carrier A) p ≫ rule.total A op ≫ rule.view.map (f _) =
          tests.tuplePoint P Γ (rule.carrier B) (fun i => p i ≫ rule.view.map (f i.1)) ≫ rule.total B op := by
  intro Γ
  constructor
  · intro h P p
    rw [h, ← Category.assoc, tests.tuplePoint_map]
  · intro h
    apply tests.tuplePoint_ext Γ (rule.carrier A)
    intro P p
    rw [← Category.assoc _ ((rule.input Γ).map f), tests.tuplePoint_map]
    exact h P p

/-- All the preservation conditions of equation (2.1) for the interpreted primitive diagrams. -/
structure Preserves {A B : Object} (f : ∀ s, rule.carrier A s ⟶ rule.carrier B s) : Prop where
  /-- The total maps commute with the carrier maps on their inputs and outputs. -/
  total (op : sig.Total) : rule.total A op ≫ rule.view.map (f _) =
    (rule.input (sig.totalArity op).inputs).map f ≫ rule.total B op
  /-- A map takes the source relation into the target relation. -/
  relation (r : sig.Rel) : ∃ h : (rule.relation A r : rule.Ambient) ⟶ (rule.relation B r : rule.Ambient),
    h ≫ (rule.relation B r).arrow =
      (rule.relation A r).arrow ≫ (rule.input (sig.relInputs r)).map f
  /-- The partial operation commutes on the factorization through the target domain. -/
  partialOp (p : sig.Partial) : ∃ h : (rule.domain A p : rule.Ambient) ⟶ (rule.domain B p : rule.Ambient),
    h ≫ (rule.domain B p).arrow =
      (rule.domain A p).arrow ≫ (rule.input (sig.partialArity p).inputs).map f ∧
    h ≫ rule.partialValue B p = rule.partialValue A p ≫ rule.view.map (f _)
  /-- The quantity maps commute with the carrier maps. -/
  quantity (q : sig.Quantity) : rule.quantity A q ≫ rule.view.map (f _) =
    (rule.input (sig.quantityArity q).inputs).map f ≫ rule.quantity B q

/-- The identity obeys every primitive preservation condition. -/
theorem preserves_id (A : Object) : rule.Preserves (fun s => 𝟙 (rule.carrier A s)) where
  total op := by
    change rule.total A op ≫ rule.view.map (𝟙 _) = (rule.input _).map (𝟙 (rule.carrier A)) ≫ rule.total A op
    simp
  relation r := by
    refine ⟨𝟙 _, ?_⟩
    change 𝟙 _ ≫ (rule.relation A r).arrow =
      (rule.relation A r).arrow ≫ (rule.input _).map (𝟙 (rule.carrier A))
    simp
  partialOp p := by
    refine ⟨𝟙 _, ?_, by simp⟩
    change 𝟙 _ ≫ (rule.domain A p).arrow =
      (rule.domain A p).arrow ≫ (rule.input _).map (𝟙 (rule.carrier A))
    simp
  quantity q := by
    change rule.quantity A q ≫ rule.view.map (𝟙 _) = (rule.input _).map (𝟙 (rule.carrier A)) ≫ rule.quantity A q
    simp

/-- Preservation is closed under composing the actual carrier maps. -/
theorem preserves_comp {A B D : Object} {f : ∀ s, rule.carrier A s ⟶ rule.carrier B s}
    {g : ∀ s, rule.carrier B s ⟶ rule.carrier D s} (hf : rule.Preserves f) (hg : rule.Preserves g) :
    rule.Preserves (fun s => f s ≫ g s) where
  total op := by
    change rule.total A op ≫ rule.view.map (f _ ≫ g _) = (rule.input _).map (f ≫ g) ≫ rule.total D op
    rw [rule.view.map_comp, ← Category.assoc, hf.total, Category.assoc, hg.total, Functor.map_comp, Category.assoc]
  relation r := by
    obtain ⟨a, ha⟩ := hf.relation r
    obtain ⟨b, hb⟩ := hg.relation r
    refine ⟨a ≫ b, ?_⟩
    change (a ≫ b) ≫ (rule.relation D r).arrow =
      (rule.relation A r).arrow ≫ (rule.input _).map (f ≫ g)
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, Functor.map_comp]
  partialOp p := by
    obtain ⟨a, ha, hva⟩ := hf.partialOp p
    obtain ⟨b, hb, hvb⟩ := hg.partialOp p
    refine ⟨a ≫ b, ?_, ?_⟩
    · change (a ≫ b) ≫ (rule.domain D p).arrow =
        (rule.domain A p).arrow ≫ (rule.input _).map (f ≫ g)
      rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, Functor.map_comp]
    · rw [Category.assoc, hvb, ← Category.assoc, hva, Category.assoc, rule.view.map_comp]
  quantity q := by
    change rule.quantity A q ≫ rule.view.map (f _ ≫ g _) = (rule.input _).map (f ≫ g) ≫ rule.quantity D q
    rw [rule.view.map_comp, ← Category.assoc, hf.quantity, Category.assoc, hg.quantity, Functor.map_comp, Category.assoc]

/-- The category of primitive structures before imposing the required Laws. -/
def Category (_rule : StructureRule sig C Object) : Type t := Object

/-- The morphisms are all the carrier families preserving the primitive diagrams. -/
instance category : CategoryTheory.Category.{max u v} rule.Category where
  Hom A B := {f : ∀ s, rule.carrier A s ⟶ rule.carrier B s // rule.Preserves f}
  id A := ⟨fun s => 𝟙 (rule.carrier A s), rule.preserves_id A⟩
  comp f g := ⟨fun s => f.val s ≫ g.val s, rule.preserves_comp f.property g.property⟩
  id_comp _ := Subtype.ext (funext fun _ => CategoryTheory.Category.id_comp _)
  comp_id _ := Subtype.ext (funext fun _ => CategoryTheory.Category.comp_id _)
  assoc _ _ _ := Subtype.ext (funext fun _ => CategoryTheory.Category.assoc _ _ _)

/-- The arrow equivalence exhibits the full set of preserving carrier maps. -/
def homEquiv (A B : rule.Category) :
    (A ⟶ B) ≃ {f : ∀ s, rule.carrier A s ⟶ rule.carrier B s // rule.Preserves f} :=
  Equiv.refl _

end StructureRule

end SHIGURE
