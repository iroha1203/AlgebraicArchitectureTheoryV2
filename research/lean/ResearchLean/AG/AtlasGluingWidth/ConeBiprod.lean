import ResearchLean.AG.AtlasGluingWidth.PairComplex
import ResearchLean.AG.AtlasDefectComposition.ConeCoordinates
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.ModuleCat.Biproducts

import Formal.Util.AssertStandardAxioms
/-! # 同じ二領域比較の標準錐と二つの錐の直和

Implementation notes: 標準錐の実制限射を作り、全整数次数の座標交換で全単射を示す。
-/
noncomputable section
open CategoryTheory Limits HomologicalComplex CochainComplex
namespace AAT.AG.AtlasGluingWidth
namespace ConeBiprod
open AAT.AG.TwoPhase AAT.AG.AtlasDefectComposition AAT.AG.AtlasGluingWidth
universe u
variable {C D E F : ThreeCochainComplex.{0,u} ℚ}
variable (f : ThreeCochainComplex.Hom C E) (g : ThreeCochainComplex.Hom D F)

/-- 二領域比較の標準錐から第一領域の標準錐への制限。 -/
def left : comparisonCone (StandardRow.pairHom f g) ⟶ comparisonCone f :=
  mappingCone.map _ _ (zeroExtensionMap (PairComplex.fst C D))
    (zeroExtensionMap (PairComplex.fst E F)) (PairComplex.map_fst f g)

/-- 二領域比較の標準錐から第二領域の標準錐への制限。 -/
def right : comparisonCone (StandardRow.pairHom f g) ⟶ comparisonCone g :=
  mappingCone.map _ _ (zeroExtensionMap (PairComplex.snd C D))
    (zeroExtensionMap (PairComplex.snd E F)) (PairComplex.map_snd f g)

/-- 同じ二つの制限から標準複体の実biproductへ移す。 -/
def split : comparisonCone (StandardRow.pairHom f g) ⟶ comparisonCone f ⊞ comparisonCone g :=
  biprod.lift (left f g) (right f g)

/-- fine/sourceの二領域座標を、元の領域ごとの積へ並べ替える。 -/
def shuffle (V W X Y : Type u) [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y] :
    ((V × W) × (X × Y)) ≃ₗ[ℚ] ((V × X) × (W × Y)) where
  toFun z := ((z.1.1,z.2.1),(z.1.2,z.2.2))
  invFun z := ((z.1.1,z.2.1),(z.1.2,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 二領域比較の標準錐の各整数次数を二つの標準錐の積座標へ同定する。 -/
def degreeEquiv (m : ℤ) : (comparisonCone (StandardRow.pairHom f g)).X m ≃ₗ[ℚ]
    ((comparisonCone f).X m × (comparisonCone g).X m) :=
  (coneCoordinateEquiv (zeroExtensionMap (StandardRow.pairHom f g)) m).trans
    (((PairComplex.degreeEquiv E F m).prodCongr (PairComplex.degreeEquiv C D (m+1))).trans
      ((shuffle _ _ _ _).trans
        ((coneCoordinateEquiv (zeroExtensionMap f) m).symm.prodCongr
          (coneCoordinateEquiv (zeroExtensionMap g) m).symm)))

/-- 座標同定の第一成分は同じ標準錐制限。 -/
theorem degreeEquiv_left (m : ℤ) (x : (comparisonCone (StandardRow.pairHom f g)).X m) :
    (degreeEquiv f g m x).1 = (left f g).f m x := by
  apply (coneCoordinateEquiv (zeroExtensionMap f) m).injective
  change (coneCoordinateEquiv (zeroExtensionMap f) m)
      ((coneCoordinateEquiv (zeroExtensionMap f) m).symm
        (((PairComplex.degreeEquiv E F m)
          (coneCoordinateEquiv (zeroExtensionMap (StandardRow.pairHom f g)) m x).1).1,
        ((PairComplex.degreeEquiv C D (m+1))
          (coneCoordinateEquiv (zeroExtensionMap (StandardRow.pairHom f g)) m x).2).1)) = _
  rw [LinearEquiv.apply_symm_apply]
  erw [coneCoordinateEquiv_map]
  exact Prod.ext (PairComplex.degreeEquiv_fst E F m _).symm
    (PairComplex.degreeEquiv_fst C D (m+1) _).symm

/-- 座標同定の第二成分は同じ標準錐制限。 -/
theorem degreeEquiv_right (m : ℤ) (x : (comparisonCone (StandardRow.pairHom f g)).X m) :
    (degreeEquiv f g m x).2 = (right f g).f m x := by
  apply (coneCoordinateEquiv (zeroExtensionMap g) m).injective
  change (coneCoordinateEquiv (zeroExtensionMap g) m)
      ((coneCoordinateEquiv (zeroExtensionMap g) m).symm
        (((PairComplex.degreeEquiv E F m)
          (coneCoordinateEquiv (zeroExtensionMap (StandardRow.pairHom f g)) m x).1).2,
        ((PairComplex.degreeEquiv C D (m+1))
          (coneCoordinateEquiv (zeroExtensionMap (StandardRow.pairHom f g)) m x).2).2)) = _
  rw [LinearEquiv.apply_symm_apply]
  erw [coneCoordinateEquiv_map]
  exact Prod.ext (PairComplex.degreeEquiv_snd E F m _).symm
    (PairComplex.degreeEquiv_snd C D (m+1) _).symm

/-- 実標準biproductの各次数を通常の二つの加群の積へ読む。 -/
def biprodDegreeEquiv (m : ℤ) : (comparisonCone f ⊞ comparisonCone g).X m ≃ₗ[ℚ]
    ((comparisonCone f).X m × (comparisonCone g).X m) :=
  ((biprodXIso (comparisonCone f) (comparisonCone g) m) ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv

/-- 実biproductの積座標の第一成分は標準projection。 -/
theorem biprodDegreeEquiv_fst (m : ℤ) (z : (comparisonCone f ⊞ comparisonCone g).X m) :
    (biprodDegreeEquiv f g m z).1 = (biprod.fst : comparisonCone f ⊞ comparisonCone g ⟶ _).f m z := by
  have h : (biprodDegreeEquiv f g m).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.fst ℚ ((comparisonCone f).X m) ((comparisonCone g).X m)) =
      (biprod.fst : comparisonCone f ⊞ comparisonCone g ⟶ _).f m := by
    change ((biprodXIso (comparisonCone f) (comparisonCone g) m).hom ≫
      (ModuleCat.biprodIsoProd (R := ℚ) ((comparisonCone f).X m) ((comparisonCone g).X m)).hom) ≫ _ = _
    rw [Category.assoc, ← ModuleCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc, biprodXIso_hom_fst]
  exact congrArg (fun t => t z) h

/-- 実biproductの積座標の第二成分は標準projection。 -/
theorem biprodDegreeEquiv_snd (m : ℤ) (z : (comparisonCone f ⊞ comparisonCone g).X m) :
    (biprodDegreeEquiv f g m z).2 = (biprod.snd : comparisonCone f ⊞ comparisonCone g ⟶ _).f m z := by
  have h : (biprodDegreeEquiv f g m).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.snd ℚ ((comparisonCone f).X m) ((comparisonCone g).X m)) =
      (biprod.snd : comparisonCone f ⊞ comparisonCone g ⟶ _).f m := by
    change ((biprodXIso (comparisonCone f) (comparisonCone g) m).hom ≫
      (ModuleCat.biprodIsoProd (R := ℚ) ((comparisonCone f).X m) ((comparisonCone g).X m)).hom) ≫ _ = _
    rw [Category.assoc, ← ModuleCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc, biprodXIso_hom_snd]
  exact congrArg (fun t => t z) h

/-- 実標準直和への射は、同じ整数次数の領域別錐座標を保つ。 -/
theorem split_coordinate (m : ℤ) (x : (comparisonCone (StandardRow.pairHom f g)).X m) :
    biprodDegreeEquiv f g m ((split f g).f m x) = degreeEquiv f g m x := by
  apply Prod.ext
  · rw [biprodDegreeEquiv_fst, degreeEquiv_left]
    exact congrArg (fun t => t x) (biprod_lift_fst_f (left f g) (right f g) m)
  · rw [biprodDegreeEquiv_snd, degreeEquiv_right]
    exact congrArg (fun t => t x) (biprod_lift_snd_f (left f g) (right f g) m)

/-- 実標準直和への射は全次数の座標全単射から複体同型となる。 -/
instance split_isIso : IsIso (split f g) := by
  haveI : ∀ m : ℤ, IsIso ((split f g).f m) := by
    intro m
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have h : (split f g).f m = ModuleCat.ofHom
        ((degreeEquiv f g m).trans (biprodDegreeEquiv f g m).symm).toLinearMap := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (biprodDegreeEquiv f g m).injective
      rw [split_coordinate]
      exact ((biprodDegreeEquiv f g m).apply_symm_apply _).symm
    rw [h]
    exact ((degreeEquiv f g m).trans (biprodDegreeEquiv f g m).symm).bijective
  exact HomologicalComplex.Hom.isIso_of_components _
/-- 二領域比較の標準錐と、同じ二領域の標準錐直和との全複体同型。 -/
def iso : comparisonCone (StandardRow.pairHom f g) ≅ comparisonCone f ⊞ comparisonCone g :=
  asIso (split f g)
/-- 全複体同型からの第一projectionは同じ標準錐制限。 -/
@[simp] theorem iso_hom_fst : (iso f g).hom ≫ biprod.fst = left f g :=
  biprod.lift_fst _ _
/-- 全複体同型からの第二projectionは同じ標準錐制限。 -/
@[simp] theorem iso_hom_snd : (iso f g).hom ≫ biprod.snd = right f g :=
  biprod.lift_snd _ _
end ConeBiprod
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
