import Formal.SHIGURE.Part2.Schemes.QuasiCoherentModules
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Coordinate sheaves on arbitrary test schemes -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable (X : Scheme.{u}) (n : ℕ)

private abbrev structureModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The standard free sheaf of rank `n` is the finite product of copies
of the actual structure sheaf as a module. -/
def coordinateModuleSheaf : X.Modules :=
  ∏ᶜ (fun _ : Fin n => structureModule X)

private abbrev evaluate (U : X.Opensᵒᵖ) :=
  SheafOfModules.evaluation X.ringCatSheaf U

/-- Sections on an arbitrary open of the actual coordinate sheaf are its
coordinate tuples in the ring of sections. -/
def coordinateModuleSectionIso (U : X.Opensᵒᵖ) :
    (coordinateModuleSheaf X n).val.obj U ≅
      ModuleCat.of (X.sheaf.val.obj U) (Fin n → X.sheaf.val.obj U) :=
  PreservesProduct.iso (evaluate X U) (fun _ : Fin n => structureModule X) ≪≫
    ModuleCat.piIsoPi (fun _ : Fin n => (evaluate X U).obj (structureModule X))

/-- Each coordinate of the section is its actual projection as a sheaf map. -/
theorem coordinateModuleSectionIso_apply (U : X.Opensᵒᵖ)
    (x : (coordinateModuleSheaf X n).val.obj U) (i : Fin n) :
    (coordinateModuleSectionIso X n U).hom x i =
      (Pi.π (fun _ : Fin n => structureModule X) i).val.app U x := by
  let A := fun _ : Fin n => structureModule X
  let F := evaluate X U
  let p := ModuleCat.ofHom (LinearMap.proj i : (Fin n → X.sheaf.val.obj U) →ₗ[X.sheaf.val.obj U]
    X.sheaf.val.obj U)
  have coordinates : (coordinateModuleSectionIso X n U).hom ≫ p =
      F.map (Pi.π A i) := by
    rw [coordinateModuleSectionIso, Iso.trans_hom, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
      PreservesProduct.iso_hom, piComparison_comp_π]
  exact congrArg (fun m => m x) coordinates

/-- The coordinates restrict through the original structure ring maps. -/
theorem coordinateModuleSectionIso_restrict {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (x : (coordinateModuleSheaf X n).val.obj U) (i : Fin n) :
    (coordinateModuleSectionIso X n V).hom ((coordinateModuleSheaf X n).val.map f x) i =
      (X.sheaf.val.map f).hom ((coordinateModuleSectionIso X n U).hom x i) := by
  rw [coordinateModuleSectionIso_apply, coordinateModuleSectionIso_apply]
  exact PresheafOfModules.naturality_apply (Pi.π (fun _ : Fin n => structureModule X) i).val f x

end

end SHIGURE.RealizationFamilies
