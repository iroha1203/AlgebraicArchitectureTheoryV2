namespace Formal.Arch.Category

universe u v

/-- Minimal small category used by the V2 formalization. -/
structure SmallCategory where
  Obj : Type u
  Hom : Obj → Obj → Sort v
  id : {X : Obj} → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp id f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f id = f
  assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

namespace SmallCategory

/-- Discrete category on a type. -/
def discrete (α : Type u) : SmallCategory where
  Obj := α
  Hom := fun X Y => X = Y
  id := rfl
  comp := fun f g => f.trans g
  id_comp := by intro X Y f; cases f; rfl
  comp_id := by intro X Y f; cases f; rfl
  assoc := by intro W X Y Z f g h; cases f; cases g; cases h; rfl

end SmallCategory

end Formal.Arch.Category

