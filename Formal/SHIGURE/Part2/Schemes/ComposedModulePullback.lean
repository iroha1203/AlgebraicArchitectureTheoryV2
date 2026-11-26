import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Module pullback along specified composites -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules

noncomputable section

universe u

variable {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y) (c : Z ⟶ X) (equal : b ≫ a = c)

/-- Compare the iterated module pullback with the specified composite morphism. -/
def pullbackCompositionFor : pullback a ⋙ pullback b ≅ pullback c :=
  (pullbackCongr equal.symm ≪≫ (pullbackComp b a).symm).symm

/-- The forward comparison follows ordinary composition and then the equality. -/
theorem pullbackCompositionFor_hom_app (M : X.Modules) :
    (pullbackCompositionFor a b c equal).hom.app M =
      (pullbackComp b a).hom.app M ≫ (pullbackCongr equal).hom.app M := by
  subst c
  rfl

/-- The inverse comparison first reads the equality in the reverse direction. -/
theorem pullbackCompositionFor_inv_app (M : X.Modules) :
    (pullbackCompositionFor a b c equal).inv.app M =
      (pullbackCongr equal.symm).hom.app M ≫ (pullbackComp b a).inv.app M := rfl

end

end SHIGURE.SchemeDescent
