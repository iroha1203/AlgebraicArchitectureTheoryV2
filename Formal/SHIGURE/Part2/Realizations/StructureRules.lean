import Formal.SHIGURE.Part1.Signature
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Primitive structure rules and their maps

A realization represents each primitive by an actual arrow or a monomorphism
in its carrier category. Its input functors specify how carrier maps act on
tuples of the chosen mode. The morphisms are precisely the families obeying
the commutativity and factorization equations of (2.1).
-/

open CategoryTheory

universe u v w t

namespace SHIGURE

/-- A represented subobject with its monic inclusion. -/
structure RealizedSubobject {C : Type w} [Category.{v} C] (X : C) where
  /-- An object representing the subobject. -/
  obj : C
  /-- The inclusion in the input object. -/
  inclusion : obj ⟶ X
  /-- The inclusion is monic. -/
  mono_inclusion : Mono inclusion

/-- The primitive data and the allowable carrier maps of a structure mode. -/
structure StructureRule (sig : Signature.{u}) (C : Cat.{v, w}) (Object : Type t) where
  /-- The object realizing each carrier sort. -/
  carrier : Object → sig.SortType → C
  /-- The input objects, functorial in the entire family of carrier maps. -/
  input (Γ : List sig.SortType) : (sig.SortType → C) ⥤ C
  /-- A total operation from its entire input object. -/
  total (A : Object) (f : sig.Total) : (input (sig.totalArity f).inputs).obj (carrier A) ⟶
    carrier A (sig.totalArity f).output
  /-- A relation as a subobject of its input object. -/
  relation (A : Object) (r : sig.Rel) :
    RealizedSubobject ((input (sig.relInputs r)).obj (carrier A))
  /-- The specified domain of a partial operation. -/
  domain (A : Object) (p : sig.Partial) :
    RealizedSubobject ((input (sig.partialArity p).inputs).obj (carrier A))
  /-- The partial operation on its specified domain. -/
  partialValue (A : Object) (p : sig.Partial) :
    (domain A p).obj ⟶ carrier A (sig.partialArity p).output
  /-- The map reading a quantity. -/
  quantity (A : Object) (q : sig.Quantity) : (input (sig.quantityArity q).inputs).obj (carrier A) ⟶
    carrier A (sig.quantityArity q).output

namespace StructureRule

variable {sig : Signature.{u}} {C : Cat.{v, w}} {Object : Type t}
variable (rule : StructureRule sig C Object)

/-- All the preservation conditions of equation (2.1) for the interpreted primitive diagrams. -/
structure Preserves {A B : Object} (f : ∀ s, rule.carrier A s ⟶ rule.carrier B s) : Prop where
  /-- The total maps commute with the carrier maps on their inputs and outputs. -/
  total (op : sig.Total) : rule.total A op ≫ f _ =
    (rule.input (sig.totalArity op).inputs).map f ≫ rule.total B op
  /-- A map takes the source relation into the target relation. -/
  relation (r : sig.Rel) : ∃ h : (rule.relation A r).obj ⟶ (rule.relation B r).obj,
    h ≫ (rule.relation B r).inclusion =
      (rule.relation A r).inclusion ≫ (rule.input (sig.relInputs r)).map f
  /-- The partial operation commutes on the factorization through the target domain. -/
  partialOp (p : sig.Partial) : ∃ h : (rule.domain A p).obj ⟶ (rule.domain B p).obj,
    h ≫ (rule.domain B p).inclusion =
      (rule.domain A p).inclusion ≫ (rule.input (sig.partialArity p).inputs).map f ∧
    h ≫ rule.partialValue B p = rule.partialValue A p ≫ f _
  /-- The quantity maps commute with the carrier maps. -/
  quantity (q : sig.Quantity) : rule.quantity A q ≫ f _ =
    (rule.input (sig.quantityArity q).inputs).map f ≫ rule.quantity B q

/-- The identity obeys every primitive preservation condition. -/
theorem preserves_id (A : Object) : rule.Preserves (fun s => 𝟙 (rule.carrier A s)) where
  total op := by
    change rule.total A op ≫ 𝟙 _ = (rule.input _).map (𝟙 (rule.carrier A)) ≫ rule.total A op
    simp
  relation r := by
    refine ⟨𝟙 _, ?_⟩
    change 𝟙 _ ≫ (rule.relation A r).inclusion =
      (rule.relation A r).inclusion ≫ (rule.input _).map (𝟙 (rule.carrier A))
    simp
  partialOp p := by
    refine ⟨𝟙 _, ?_, by simp⟩
    change 𝟙 _ ≫ (rule.domain A p).inclusion =
      (rule.domain A p).inclusion ≫ (rule.input _).map (𝟙 (rule.carrier A))
    simp
  quantity q := by
    change rule.quantity A q ≫ 𝟙 _ = (rule.input _).map (𝟙 (rule.carrier A)) ≫ rule.quantity A q
    simp

/-- Preservation is closed under composing the actual carrier maps. -/
theorem preserves_comp {A B D : Object} {f : ∀ s, rule.carrier A s ⟶ rule.carrier B s}
    {g : ∀ s, rule.carrier B s ⟶ rule.carrier D s} (hf : rule.Preserves f) (hg : rule.Preserves g) :
    rule.Preserves (fun s => f s ≫ g s) where
  total op := by
    change rule.total A op ≫ (f _ ≫ g _) = (rule.input _).map (f ≫ g) ≫ rule.total D op
    rw [← Category.assoc, hf.total, Category.assoc, hg.total, Functor.map_comp, Category.assoc]
  relation r := by
    obtain ⟨a, ha⟩ := hf.relation r
    obtain ⟨b, hb⟩ := hg.relation r
    refine ⟨a ≫ b, ?_⟩
    change (a ≫ b) ≫ (rule.relation D r).inclusion =
      (rule.relation A r).inclusion ≫ (rule.input _).map (f ≫ g)
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, Functor.map_comp]
  partialOp p := by
    obtain ⟨a, ha, hva⟩ := hf.partialOp p
    obtain ⟨b, hb, hvb⟩ := hg.partialOp p
    refine ⟨a ≫ b, ?_, ?_⟩
    · change (a ≫ b) ≫ (rule.domain D p).inclusion =
        (rule.domain A p).inclusion ≫ (rule.input _).map (f ≫ g)
      rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, Functor.map_comp]
    · rw [Category.assoc, hvb, ← Category.assoc, hva, Category.assoc]
  quantity q := by
    change rule.quantity A q ≫ (f _ ≫ g _) = (rule.input _).map (f ≫ g) ≫ rule.quantity D q
    rw [← Category.assoc, hf.quantity, Category.assoc, hg.quantity, Functor.map_comp, Category.assoc]

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
