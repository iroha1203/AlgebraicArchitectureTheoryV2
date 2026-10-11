import ResearchLean.AG.AtlasGluingWidth.MayerVietoris
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
/-! # 二領域H¹の同じ射を保持する積同型

GOAL C／設計 exact-sequence §3–4。原始cellRowの二領域積を標準biproductに同定し、
全整数次数のhomologyを両領域homologyの積へ移す。各射影の同定により差制限と比較を保持する。
Implementation notes: mathlibのadditive homologyFunctorとmapBiprodを使う。
同次元の任意同型を選ぶ案は元の二つの制限射を保持しないため退けた。
一般hf/hgは方向仮定で、原始適用では局所J零とG-133 oldH1Equiv_naturalから放電する。
-/
noncomputable section
open CategoryTheory Limits HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.PairHomology
open AAT.AG.AtlasGluingWidth AAT.AG.AtlasDefectComposition AAT.AG.TwoPhase
universe u
variable (K L : CochainComplex (ModuleCat.{u} ℚ) ℤ)
/-- 標準biproductの次数成分を実積へ移す線形同型。 -/
def degreeEquiv (m : ℤ) : (K ⊞ L).X m ≃ₗ[ℚ] (K.X m × L.X m) :=
  ((biprodXIso K L m) ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
/-- 次数同型の第一射影は元のbiproduct射影。 -/
theorem degreeEquiv_fst (m : ℤ) (z : (K ⊞ L).X m) :
    (degreeEquiv K L m z).1 = (biprod.fst : K ⊞ L ⟶ K).f m z := by
  have h : (degreeEquiv K L m).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.fst ℚ (K.X m) (L.X m)) =
      (biprod.fst : K ⊞ L ⟶ K).f m := by
    change ((biprodXIso K L m).hom ≫
      (ModuleCat.biprodIsoProd (R := ℚ) (K.X m) (L.X m)).hom) ≫ _ = _
    rw [Category.assoc, ← ModuleCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc, biprodXIso_hom_fst]
  exact congrArg (fun t => t z) h
/-- 次数同型の第二射影は元のbiproduct射影。 -/
theorem degreeEquiv_snd (m : ℤ) (z : (K ⊞ L).X m) :
    (degreeEquiv K L m z).2 = (biprod.snd : K ⊞ L ⟶ L).f m z := by
  have h : (degreeEquiv K L m).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.snd ℚ (K.X m) (L.X m)) =
      (biprod.snd : K ⊞ L ⟶ L).f m := by
    change ((biprodXIso K L m).hom ≫
      (ModuleCat.biprodIsoProd (R := ℚ) (K.X m) (L.X m)).hom) ≫ _ = _
    rw [Category.assoc, ← ModuleCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc, biprodXIso_hom_snd]
  exact congrArg (fun t => t z) h

variable (C D : ThreeCochainComplex.{0,u} ℚ)
/-- 同じ二つの三項射影から生成する標準biproduct射。 -/
def split : zeroExtension (pairComplex C D) ⟶ zeroExtension C ⊞ zeroExtension D :=
  biprod.lift (zeroExtensionMap (PairComplex.fst C D)) (zeroExtensionMap (PairComplex.snd C D))
/-- 全整数次数のsplitはPairComplexの同じ成分同型を読む。 -/
theorem split_coordinate (m : ℤ) (z : (zeroExtension (pairComplex C D)).X m) :
    degreeEquiv (zeroExtension C) (zeroExtension D) m ((split C D).f m z) =
      PairComplex.degreeEquiv C D m z := by
  apply Prod.ext
  · rw [degreeEquiv_fst, ← PairComplex.degreeEquiv_fst]
    exact congrArg (fun t => t z) (biprod_lift_fst_f (zeroExtensionMap (PairComplex.fst C D)) (zeroExtensionMap (PairComplex.snd C D)) m)
  · rw [degreeEquiv_snd, ← PairComplex.degreeEquiv_snd]
    exact congrArg (fun t => t z) (biprod_lift_snd_f (zeroExtensionMap (PairComplex.fst C D)) (zeroExtensionMap (PairComplex.snd C D)) m)
/-- 元の各次数の積同型からsplitの同型性を生成する。 -/
instance split_isIso : IsIso (split C D) := by
  haveI : ∀ m : ℤ, IsIso ((split C D).f m) := by
    intro m
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have h : (split C D).f m = ModuleCat.ofHom
        ((PairComplex.degreeEquiv C D m).trans (degreeEquiv (zeroExtension C) (zeroExtension D) m).symm).toLinearMap := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (degreeEquiv (zeroExtension C) (zeroExtension D) m).injective
      rw [split_coordinate]
      exact ((degreeEquiv (zeroExtension C) (zeroExtension D) m).apply_symm_apply _).symm
    rw [h]
    exact ((PairComplex.degreeEquiv C D m).trans (degreeEquiv (zeroExtension C) (zeroExtension D) m).symm).bijective
  exact HomologicalComplex.Hom.isIso_of_components _
/-- 実二領域複体と標準biproductとの同型。 -/
def iso : zeroExtension (pairComplex C D) ≅ zeroExtension C ⊞ zeroExtension D := asIso (split C D)
/-- 同じhomologyFunctorから全次数の二領域homology積同型を生成する。 -/
def homologyIso (m : ℤ) : (zeroExtension (pairComplex C D)).homology m ≅
    ModuleCat.of ℚ ((zeroExtension C).homology m × (zeroExtension D).homology m) := by
  letI := preservesBinaryBiproducts_of_preservesBiproducts
    (homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) m)
  exact ((homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) m).mapIso (iso C D)) ≪≫
    (homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) m).mapBiprod (zeroExtension C) (zeroExtension D) ≪≫
    ModuleCat.biprodIsoProd _ _

/-- homology積同型の第一射影は元の第一制限射。 -/
theorem homologyIso_fst (m : ℤ) : (homologyIso C D m).hom ≫
    ModuleCat.ofHom (LinearMap.fst ℚ ((zeroExtension C).homology m) ((zeroExtension D).homology m)) =
      homologyMap (zeroExtensionMap (PairComplex.fst C D)) m := by
  let H := homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) m
  letI := preservesBinaryBiproducts_of_preservesBiproducts H
  change ((H.map (split C D) ≫ (H.mapBiprod (zeroExtension C) (zeroExtension D)).hom) ≫
    (ModuleCat.biprodIsoProd (R := ℚ) _ _).hom) ≫ _ = _
  rw [Category.assoc, ← ModuleCat.biprodIsoProd_inv_comp_fst]
  erw [Iso.hom_inv_id_assoc]
  rw [Category.assoc, Functor.mapBiprod_hom]
  erw [biprod.lift_fst]
  rw [← H.map_comp]
  exact congrArg H.map (biprod.lift_fst _ _)
/-- homology積同型の第二射影は元の第二制限射。 -/
theorem homologyIso_snd (m : ℤ) : (homologyIso C D m).hom ≫
    ModuleCat.ofHom (LinearMap.snd ℚ ((zeroExtension C).homology m) ((zeroExtension D).homology m)) =
      homologyMap (zeroExtensionMap (PairComplex.snd C D)) m := by
  let H := homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) m
  letI := preservesBinaryBiproducts_of_preservesBiproducts H
  change ((H.map (split C D) ≫ (H.mapBiprod (zeroExtension C) (zeroExtension D)).hom) ≫
    (ModuleCat.biprodIsoProd (R := ℚ) _ _).hom) ≫ _ = _
  rw [Category.assoc, ← ModuleCat.biprodIsoProd_inv_comp_snd]
  erw [Iso.hom_inv_id_assoc]
  rw [Category.assoc, Functor.mapBiprod_hom]
  erw [biprod.lift_snd]
  rw [← H.map_comp]
  exact congrArg H.map (biprod.lift_snd _ _)
/-- 標準homology積同型の実線形同型。 -/
def homologyEquiv (m : ℤ) := (homologyIso C D m).toLinearEquiv
/-- 積同型の全元で第一の元homology射を保持する。 -/
@[simp] theorem homologyEquiv_fst (m : ℤ) (x : (zeroExtension (pairComplex C D)).homology m) :
    (homologyEquiv C D m x).1 = homologyMap (zeroExtensionMap (PairComplex.fst C D)) m x :=
  congrArg (fun f => f x) (homologyIso_fst C D m)
/-- 積同型の全元で第二の元homology射を保持する。 -/
@[simp] theorem homologyEquiv_snd (m : ℤ) (x : (zeroExtension (pairComplex C D)).homology m) :
    (homologyEquiv C D m x).2 = homologyMap (zeroExtensionMap (PairComplex.snd C D)) m x :=
  congrArg (fun f => f x) (homologyIso_snd C D m)
variable {C D} {E F : ThreeCochainComplex.{0,u} ℚ}
variable (f : ThreeCochainComplex.Hom C E) (g : ThreeCochainComplex.Hom D F)
/-- 二領域積の実比較は同じ二つのhomology比較と可換。 -/
theorem homologyMap_pair (m : ℤ) (x : (zeroExtension (pairComplex C D)).homology m) :
    homologyEquiv E F m (homologyMap (zeroExtensionMap (StandardRow.pairHom f g)) m x) =
      (homologyMap (zeroExtensionMap f) m (homologyEquiv C D m x).1,
       homologyMap (zeroExtensionMap g) m (homologyEquiv C D m x).2) := by
  apply Prod.ext
  · rw [homologyEquiv_fst, homologyEquiv_fst]
    have h := congrArg (fun t => homologyMap t m) (PairComplex.map_fst f g)
    dsimp only at h
    rw [homologyMap_comp, homologyMap_comp] at h
    exact congrArg (fun t => t x) h
  · rw [homologyEquiv_snd, homologyEquiv_snd]
    have h := congrArg (fun t => homologyMap t m) (PairComplex.map_snd f g)
    dsimp only at h
    rw [homologyMap_comp, homologyMap_comp] at h
    exact congrArg (fun t => t x) h
/-- 各局所比較が全単射なら同じ二領域比較も全単射。一般仮定は原始適用で局所J零から放電する。 -/
theorem homologyMap_pair_bijective (m : ℤ)
    (hf : Function.Bijective (homologyMap (zeroExtensionMap f) m))
    (hg : Function.Bijective (homologyMap (zeroExtensionMap g) m)) :
    Function.Bijective (homologyMap (zeroExtensionMap (StandardRow.pairHom f g)) m) := by
  let ef := LinearEquiv.ofBijective (homologyMap (zeroExtensionMap f) m).hom hf
  let eg := LinearEquiv.ofBijective (homologyMap (zeroExtensionMap g) m).hom hg
  let e := (homologyEquiv C D m).trans ((ef.prodCongr eg).trans (homologyEquiv E F m).symm)
  have h : ∀ x, e x = homologyMap (zeroExtensionMap (StandardRow.pairHom f g)) m x := by
    intro x
    apply (homologyEquiv E F m).injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact (homologyMap_pair f g m x).symm
  simpa only [Function.Bijective, Function.Injective, Function.Surjective, h] using e.bijective

/-- G-133の同じH¹比較の自然性により既存商と標準H¹の全単射性を同定する。 -/
theorem oldH1_bijective_iff (f : ThreeCochainComplex.Hom C E) :
    Function.Bijective f.h1Map ↔ Function.Bijective (homologyMap (zeroExtensionMap f) (1:ℤ)) :=
  LinearConjugation.bijective_iff f.h1Map (homologyMap (zeroExtensionMap f) 1).hom
    (oldH1Equiv C) (oldH1Equiv E) (oldH1Equiv_natural f)
end AAT.AG.AtlasGluingWidth.PairHomology

#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
