import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.Ring.Limits

/-! # The module of a sheaf of algebras

A map from the structure sheaf gives an algebra on each ring of sections.
Its restrictions preserve the structure maps and hence define a sheaf
of modules over the same scheme.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules

noncomputable section

universe u

variable {X : Scheme.{u}}

private def algebraModuleAt (C : Under X.sheaf) (U : X.Opensᵒᵖ) :
    ModuleCat.{u} (X.ringCatSheaf.val.obj U) := by
  change ModuleCat.{u} (X.presheaf.obj U)
  letI : Algebra (X.presheaf.obj U) (C.right.val.obj U) := (C.hom.val.app U).hom.toAlgebra
  exact ModuleCat.of (X.presheaf.obj U) (C.right.val.obj U)

private def algebraModuleMap (C : Under X.sheaf) {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    algebraModuleAt C U ⟶
      (ModuleCat.restrictScalars (X.ringCatSheaf.val.map i).hom).obj (algebraModuleAt C V) :=
  ModuleCat.ofHom (X := algebraModuleAt C U)
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.val.map i).hom).obj (algebraModuleAt C V))
    { (C.right.val.map i).hom.toAddMonoidHom with
      map_smul' := fun r x => by
        let aU : X.presheaf.obj U ⟶ C.right.val.obj U := C.hom.val.app U
        let aV : X.presheaf.obj V ⟶ C.right.val.obj V := C.hom.val.app V
        let r' : X.presheaf.obj U := r
        let x' : C.right.val.obj U := x
        change C.right.val.map i (aU r' * x') =
          aV (X.presheaf.map i r') * C.right.val.map i x'
        rw [map_mul]
        have equal := congrArg (fun f : X.presheaf.obj U ⟶ C.right.val.obj V => f r')
          (C.hom.val.naturality i)
        exact congrArg (fun y : C.right.val.obj V => y * C.right.val.map i x') equal.symm }

private def algebraModulePresheaf (C : Under X.sheaf) : X.PresheafOfModules where
  obj := algebraModuleAt C
  map := algebraModuleMap C
  map_id U := by
    ext x
    change C.right.val.map (𝟙 U) x = x
    rw [C.right.val.map_id]
    rfl
  map_comp f g := by
    ext x
    change C.right.val.map (f ≫ g) x = C.right.val.map g (C.right.val.map f x)
    rw [C.right.val.map_comp]
    rfl

/-- The algebra's underlying module sheaf uses its actual rings, restriction
maps, and structure morphism on every open.
This is the module underlying the algebra in Lemma B.7. The given structure morphism supplies
the scalar action and the restriction squares. -/
def algebraUnderlyingModule (C : Under X.sheaf) : X.Modules where
  val := algebraModulePresheaf C
  isSheaf := by
    let F := forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} Ab.{u}
    change TopCat.Presheaf.IsSheaf (C.right.val ⋙ F)
    exact ((sheafCompose _ F).obj C.right).cond

end

end SHIGURE.SchemeDescent
