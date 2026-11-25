import Formal.SHIGURE.Part2.Realizations.SheafStructures

/-!
# Structure preservation for sheaves

The morphisms for Definition 4.1 are maps of the carrier sheaves. They
commute with total maps and quantities, factor through the target relation
and domain subsheaves, and commute with partial maps on those domains.
-/

open CategoryTheory

universe u v w

noncomputable section

namespace SHIGURE.SheafStructure

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable {sig : Signature.{u}}

/-- A tuple of sheaf morphisms that preserves the primitive interpretations. -/
structure Hom (A B : SheafStructure sig J) where
  /-- The map of carrier sheaves at each sort. -/
  onSort : ∀ s, A.carrier s ⟶ B.carrier s
  /-- The map commutes with each total operation. -/
  preservesTotal (op : sig.Total) :
    A.total op ≫ onSort _ = sheafTupleMap onSort _ ≫ B.total op
  /-- The relations take satisfying tuples to satisfying tuples. -/
  preservesRelation (r : sig.Rel) :
    (A.relation r).carrier ≤ ((B.relation r).preimage (sheafTupleMap onSort _)).carrier
  /-- The input map sends the domain of a partial operation into the target domain. -/
  preservesDomain (p : sig.Partial) :
    (A.partialDomain p).carrier ≤ ((B.partialDomain p).preimage (sheafTupleMap onSort _)).carrier
  /-- On the domain subsheaf the map commutes with the partial operation. -/
  preservesPartial (p : sig.Partial) :
    A.partialValue p ≫ onSort _ =
      SheafPredicate.mapAlong (sheafTupleMap onSort _) (preservesDomain p) ≫ B.partialValue p
  /-- The map commutes with each marked quantity. -/
  preservesQuantity (q : sig.Quantity) :
    A.quantity q ≫ onSort _ = sheafTupleMap onSort _ ≫ B.quantity q

namespace Hom

variable {A B D : SheafStructure sig J}

/-- A structure morphism is determined by the maps on its carrier sheaves. -/
@[ext]
theorem ext {f g : Hom A B} (h : f.onSort = g.onSort) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity carrier maps preserve every interpretation. -/
def id (A : SheafStructure sig J) : Hom A A where
  onSort s := 𝟙 (A.carrier s)
  preservesTotal _ := by simp
  preservesRelation r := by simpa only [sheafTupleMap_id] using SheafPredicate.respects_id (A.relation r)
  preservesDomain p := by simpa only [sheafTupleMap_id] using SheafPredicate.respects_id (A.partialDomain p)
  preservesPartial _ := by simp
  preservesQuantity _ := by simp

/-- Composition of carrier maps preserves the primitive structure, including factorization through domains. -/
def comp (f : Hom A B) (g : Hom B D) : Hom A D where
  onSort s := f.onSort s ≫ g.onSort s
  preservesTotal op := by
    rw [← Category.assoc, f.preservesTotal, Category.assoc, g.preservesTotal,
      sheafTupleMap_comp, Category.assoc]
  preservesRelation r := by
    rw [sheafTupleMap_comp]
    exact SheafPredicate.respects_comp (f.preservesRelation r) (g.preservesRelation r)
  preservesDomain p := by
    rw [sheafTupleMap_comp]
    exact SheafPredicate.respects_comp (f.preservesDomain p) (g.preservesDomain p)
  preservesPartial p := by
    rw [← Category.assoc, f.preservesPartial, Category.assoc, g.preservesPartial,
      ← Category.assoc, ← SheafPredicate.mapAlong_comp]
    congr 1
  preservesQuantity q := by
    rw [← Category.assoc, f.preservesQuantity, Category.assoc, g.preservesQuantity,
      sheafTupleMap_comp, Category.assoc]

end Hom

/-- Primitive sheaf structures and their preservation maps form a category. -/
instance : Category (SheafStructure sig J) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (funext fun s => Category.id_comp (f.onSort s))
  comp_id f := Hom.ext (funext fun s => Category.comp_id (f.onSort s))
  assoc f g h := Hom.ext (funext fun s => Category.assoc (f.onSort s) (g.onSort s) (h.onSort s))

end SHIGURE.SheafStructure
