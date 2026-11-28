import Formal.SHIGURE.Part2.Schemes.Effective.CompositePull
import Formal.SHIGURE.Part2.Schemes.Effective.TestComparison

/-! # Component comparison after pulling a solution back -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X Y Z : Scheme.{u}} {cover : FppfCover.{u,v} X}
  {D : FppfModuleDescentData cover} {g : Y ⟶ X}
  (L : EffectiveLocalSolution D g) (h : Z ⟶ Y)

namespace EffectiveLocalSolution

private theorem pullComponent_square (i : cover.I₀) :
    ((cover.pullback₁ (h ≫ g)).f i ≫ h) ≫ g =
      cover.pullbackHom (h ≫ g) i ≫ cover.f i := by
  rw [Category.assoc, cover.pullbackHom_map]

/-- The comparison on each actual component of the composite pullback. -/
def pullComponentIso (i : cover.I₀) :
    (Q.map ((cover.pullback₁ (h ≫ g)).f i).op.toLoc).toFunctor.obj
        ((Q.map h.op.toLoc).toFunctor.obj L.module) ≅
      (Q.map (cover.pullbackHom (h ≫ g) i).op.toLoc).toFunctor.obj (D.obj i) :=
  let p := (cover.pullback₁ (h ≫ g)).f i
  let q := cover.pullbackHom (h ≫ g) i
  let c := Cat.Hom.toNatIso (Q.mapComp' h.op.toLoc p.op.toLoc (p ≫ h).op.toLoc rfl)
  (c.app L.module).symm ≪≫ L.testIso (p ≫ h) q (pullComponent_square h i)

variable {W : Scheme.{u}} {i : cover.I₀}
  (j : W ⟶ (cover.pullback₁ (h ≫ g)).X i) (a : W ⟶ Z) (b : W ⟶ cover.X i)
  (ja : j ≫ (cover.pullback₁ (h ≫ g)).f i = a)
  (jb : j ≫ cover.pullbackHom (h ≫ g) i = b)

include ja jb in
private theorem pullComponent_test_square : (a ≫ h) ≫ g = b ≫ cover.f i := by
  calc
    (a ≫ h) ≫ g = a ≫ (h ≫ g) := Category.assoc a h g
    _ = (j ≫ (cover.pullback₁ (h ≫ g)).f i) ≫ (h ≫ g) :=
      congrArg (fun z => z ≫ (h ≫ g)) ja.symm
    _ = j ≫ ((cover.pullback₁ (h ≫ g)).f i ≫ (h ≫ g)) := Category.assoc _ _ _
    _ = j ≫ (cover.pullbackHom (h ≫ g) i ≫ cover.f i) :=
      congrArg (j ≫ ·) (cover.pullbackHom_map (h ≫ g) i).symm
    _ = (j ≫ cover.pullbackHom (h ≫ g) i) ≫ cover.f i := (Category.assoc _ _ _).symm
    _ = b ≫ cover.f i := congrArg (· ≫ cover.f i) jb

set_option maxHeartbeats 500000 in
/-- Each component comparison restricts to the original solution's test
comparison, with the canonical comparison for the composite source. -/
theorem pullComponentIso_pull :
    pullHom (F := Q) (M₁ := (Q.map h.op.toLoc).toFunctor.obj L.module) (M₂ := D.obj i)
      (f₁ := (cover.pullback₁ (h ≫ g)).f i) (f₂ := cover.pullbackHom (h ≫ g) i)
      (L.pullComponentIso h i).hom j a b ja jb =
      (Q.mapComp' h.op.toLoc a.op.toLoc (a ≫ h).op.toLoc rfl).inv.toNatTrans.app L.module ≫
        L.testHom (a ≫ h) b (pullComponent_test_square h j a b ja jb) := by
  let p := (cover.pullback₁ (h ≫ g)).f i
  let q := cover.pullbackHom (h ≫ g) i
  let v := (Q.mapComp' h.op.toLoc a.op.toLoc (a ≫ h).op.toLoc rfl).inv.toNatTrans.app L.module
  have hp : j ≫ (p ≫ h) = a ≫ h := by rw [← Category.assoc, ja]
  have pull := pullHom_composite_source_along (F := Q) h p q j L.module (D.obj i)
    (L.testHom (p ≫ h) q (pullComponent_square h i)) a b ja jb
  have test := L.testHom_pull (p ≫ h) q (pullComponent_square h i) j
    (a ≫ h) b hp jb (pullComponent_test_square h j a b ja jb)
  exact pull.trans (congrArg (fun arrow => v ≫ arrow) test)

end EffectiveLocalSolution

end

end SHIGURE.SchemeDescent
