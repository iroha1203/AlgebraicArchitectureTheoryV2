import Formal.SHIGURE.Part1.Signature
import Mathlib.CategoryTheory.Category.Cat
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
constructs its inputs from the declared positions. The copying and tensor
modes supply their respective comparisons with Cartesian and tensor products.
-/

open CategoryTheory

universe u v w t h d

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

namespace StructureRule

variable {sig : Signature.{u}} {C : Cat.{v, w}} {Object : Type t}
variable (rule : StructureRule sig C Object)

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
