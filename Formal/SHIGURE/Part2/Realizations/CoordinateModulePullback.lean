import Formal.SHIGURE.Part2.Realizations.CoordinateModuleSheaf
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Pullback of the actual finite coordinate sheaves -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem preimageOpens_final : (Opens.map f.base).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro U
    exact ⟨⊤, ⟨homOfLE (by simp)⟩⟩
  · intro U V a b
    exact ⟨V, 𝟙 V, congrArg (· ≫ (Opens.map f.base).map (𝟙 V)) (Subsingleton.elim a b)⟩

/-- The inverse image of the finite coordinate sheaf has the same coordinates
over the new structure sheaf. This is the actual module pullback. -/
def coordinateModulePullbackIso (n : ℕ) :
    (Scheme.Modules.pullback f).obj (coordinateModuleSheaf Y n) ≅ coordinateModuleSheaf X n := by
  letI : (Opens.map f.base).Final := preimageOpens_final f
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  exact PreservesProduct.iso (Scheme.Modules.pullback f) (fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf) ≪≫
    Pi.mapIso (fun _ => asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom))

end

end SHIGURE.RealizationFamilies
