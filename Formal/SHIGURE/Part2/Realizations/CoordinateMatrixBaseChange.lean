import Formal.SHIGURE.Part2.Realizations.CoordinateBasisPullback
import Formal.SHIGURE.Part2.Realizations.CoordinateModuleMatrix
import Formal.SHIGURE.Part2.Realizations.CoordinateMultilinearSheaf

/-! # The actual pullback of a matrix map on standard free sheaves -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite Module

noncomputable section

universe u

private abbrev topOpen (T : Scheme.{u}) : T.Opensᵒᵖ := op (⊤ : T.Opens)

private theorem unitColumn_basis (T : Scheme.{u}) (n : ℕ) (U : T.Opensᵒᵖ) (j : Fin n) :
    coordinateModuleUnitColumn T n U j = coordinateModuleSectionBasis T n U j := by
  unfold coordinateModuleSectionBasis
  rw [Basis.map_apply, Pi.basisFun_apply]
  rfl

private theorem freeModuleHom_ext (T : Scheme.{u}) (n : ℕ)
    {P : T.Modules} {f g : coordinateModuleSheaf T n ⟶ P}
    (h : ∀ j : Fin n, f.val.app (topOpen T) (coordinateModuleUnitColumn T n (topOpen T) j) =
      g.val.app (topOpen T) (coordinateModuleUnitColumn T n (topOpen T) j)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply (coordinateModuleSectionBasis T n U).ext
  intro j
  let k : topOpen T ⟶ U := (homOfLE (le_top (a := U.unop))).op
  let x := coordinateModuleUnitColumn T n (topOpen T) j
  let y := coordinateModuleSectionBasis T n U j
  have restricted : (coordinateModuleSheaf T n).val.map k x = y := by
    dsimp only [x, y]
    rw [unitColumn_basis, coordinateModuleSectionBasis_restrict]
  have left := (congrArg (f.val.app U) restricted).symm.trans
    (PresheafOfModules.naturality_apply f.val k x)
  have right := (congrArg (g.val.app U) restricted).symm.trans
    (PresheafOfModules.naturality_apply g.val k x)
  exact left.trans ((congrArg (P.val.map k) (h j)).trans right.symm)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (m n : ℕ)

/-- Under the actual pullback comparisons of the two carriers, a sheaf map
has the matrix obtained by applying the actual structure-ring map entry by entry. -/
theorem coordinateModuleMatrix_pullback
    (a : coordinateModuleSheaf Y m ⟶ coordinateModuleSheaf Y n) :
    (Scheme.Modules.pullback f).map a ≫ (coordinateModulePullbackIso f n).hom =
      (coordinateModulePullbackIso f m).hom ≫
        coordinateModuleMatrixHom X m n ((coordinateModuleMatrixRead Y m n a).map f.appTop.hom) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let p := (coordinateModulePullbackIso f n).hom
  let q := (coordinateModulePullbackIso f m).hom
  let T := coordinateModuleMatrixRead Y m n a
  let b := coordinateModuleMatrixHom X m n (T.map f.appTop.hom)
  let P := Scheme.Modules.pushforward f
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  apply freeModuleHom_ext Y m
  intro j
  let U := topOpen Y
  let V := topOpen X
  let x := coordinateModuleUnitColumn Y m U j
  let y := coordinateModuleUnitColumn X m V j
  have input : (adj.homEquiv _ _ q).val.app U x = y := by
    classical
    apply (coordinateModuleSectionIso X m V).toLinearEquiv.injective
    funext i
    change (coordinateModuleSectionIso X m V).hom ((adj.homEquiv _ _ q).val.app U x) i =
      (coordinateModuleSectionIso X m V).hom y i
    have v := coordinateAdjunct_top_apply f m x i
    change _ = f.appTop.hom ((coordinateModuleSectionIso Y m U).hom x i) at v
    rw [v]
    dsimp only [x, y]
    rw [coordinateModuleUnitColumn_coordinates, coordinateModuleUnitColumn_coordinates]
    simp [Pi.single_apply]
  change (adj.homEquiv _ _ p).val.app U (a.val.app U x) =
    b.val.app V ((adj.homEquiv _ _ q).val.app U x)
  rw [input]
  apply (coordinateModuleSectionIso X n V).toLinearEquiv.injective
  funext i
  have left := coordinateAdjunct_top_apply f n (a.val.app U x) i
  have right : (coordinateModuleSectionIso X n V).hom (b.val.app V y) i =
      f.appTop.hom (T i j) := by
    have evaluated := congrArg (fun A => A i j)
      (coordinateModuleMatrixRead_hom X m n (T.map f.appTop.hom))
    exact evaluated
  exact left.trans right.symm

end

end SHIGURE.RealizationFamilies
