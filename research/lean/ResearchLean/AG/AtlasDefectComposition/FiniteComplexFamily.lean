import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Formal.Util.AssertStandardAxioms
/-! # 有限複体族の元を保持する標準直和

全次数で成分微分を持つ有限関数複体を作り、標準biproductへ同定する。
添字型のuniverseを下げずに有限性から直和を扱う。


Implementation notes: 各次数の実加群族を積で構成し、projectionのlimit性から有限直和と同定する。homologyには同じprojectionを通す。発生ラベルのuniverseをType 0へ縮める経路は使わない。
-/
noncomputable section
open CategoryTheory Limits HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
namespace FiniteComplexFamily
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
universe v w
variable {J : Type v}
variable (F G : J → CochainComplex (ModuleCat.{max v w} ℚ) ℤ)
/-- 全次数の成分微分を持つ有限族複体。 -/
def complex : CochainComplex (ModuleCat.{max v w} ℚ) ℤ :=
  CochainComplex.of (fun m => ModuleCat.of ℚ ((j : J) → (F j).X m))
    (fun m => ModuleCat.ofHom (LinearMap.pi fun j =>
      ((F j).d m (m+1)).hom.comp (LinearMap.proj j))) (by
        intro m
        ext x j
        simpa only [ModuleCat.hom_comp,ModuleCat.hom_ofHom,LinearMap.comp_apply,
          LinearMap.pi_apply,LinearMap.proj_apply,ModuleCat.hom_zero,LinearMap.zero_apply,Pi.zero_apply] using
          congrArg (fun f => f.hom (x j)) ((F j).d_comp_d m (m+1) (m+1+1)))
/-- 各実成分が零なら、有限族の同じ次数も零加群である。 -/
instance degreeSubsingleton (m : ℤ) [∀ j, Subsingleton ((F j).X m)] :
    Subsingleton ((complex F).X m) := by
  change Subsingleton ((j : J) → (F j).X m)
  infer_instance
/-- 隣接微分は元の各成分微分を評価する。 -/
@[simp] theorem d_apply (m : ℤ) (x : (complex F).X m) (j : J) :
    (complex F).d m (m+1) x j = (F j).d m (m+1) (x j) := by
  rw [show (complex F).d m (m+1) = _ from CochainComplex.of_d _ _ _ m]
  rfl
/-- 各成分への射は実座標の評価である。 -/
def projection (j : J) : complex F ⟶ F j where
  f m := ModuleCat.ofHom (LinearMap.proj j)
  comm' m n h := by
    change m+1=n at h
    subst n
    ext x
    exact (d_apply F m x j).symm
/-- 有限族の実射を成分ごとに作用させる。 -/
def map (φ : ∀ j, F j ⟶ G j) : complex F ⟶ complex G where
  f m := ModuleCat.ofHom (LinearMap.pi fun j => (φ j).f m |>.hom.comp (LinearMap.proj j))
  comm' m n h := by
    change m+1=n at h
    subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    simpa only [complex,CochainComplex.of_d,ModuleCat.hom_comp,ModuleCat.hom_ofHom,
      LinearMap.comp_apply,LinearMap.pi_apply,LinearMap.proj_apply] using
      congrArg (fun f => f.hom (x j)) ((φ j).comm m (m+1))
/-- 族射の各次数・各元・各添字の評価。 -/
@[simp] theorem map_apply (φ : ∀ j, F j ⟶ G j) (m : ℤ) (x : (complex F).X m) (j : J) :
    (map F G φ).f m x j = (φ j).f m (x j) := rfl
/-- 族射と成分射影は元のchain mapで可換である。 -/
theorem map_projection (φ : ∀ j, F j ⟶ G j) (j : J) :
    map F G φ ≫ projection G j = projection F j ≫ φ j := by ext m x; rfl
/-- 同じ族の恒等射は実族複体の恒等射である。 -/
theorem map_id : map F F (fun j => 𝟙 (F j)) = 𝟙 (complex F) := by
  ext m x
  funext j
  rfl
/-- 実族射は成分の合成を保つ。 -/
theorem map_comp {H : J → CochainComplex (ModuleCat.{max v w} ℚ) ℤ}
    (φ : ∀ j, F j ⟶ G j) (ψ : ∀ j, G j ⟶ H j) :
    map F H (fun j => φ j ≫ ψ j) = map F G φ ≫ map G H ψ := by
  ext m x
  funext j
  rfl
/-- 全成分の実複体同型は、実族複体の同型を構成する。 -/
def iso (e : ∀ j, F j ≅ G j) : complex F ≅ complex G where
  hom := map F G (fun j => (e j).hom)
  inv := map G F (fun j => (e j).inv)
  hom_inv_id := by
    rw [← map_comp]
    simpa only [Iso.hom_inv_id] using map_id F
  inv_hom_id := by
    rw [← map_comp]
    simpa only [Iso.inv_hom_id] using map_id G

/-- 実成分射影から作る標準product cone。 -/
def fan : Fan F := Fan.mk (complex F) (projection F)
/-- 実有限族複体は圏論的productの普遍性を満たす。 -/
def fanIsLimit : IsLimit (fan F) where
  lift s :=
    { f m := ModuleCat.ofHom (LinearMap.pi fun j => (s.π.app ⟨j⟩).f m |>.hom)
      comm' m n h := by
        change m+1=n at h
        subst n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext j
        simpa only [fan,Fan.mk_pt,complex,CochainComplex.of_d,ModuleCat.hom_comp,
          ModuleCat.hom_ofHom,LinearMap.comp_apply,LinearMap.pi_apply] using
          congrArg (fun f => f.hom x) ((s.π.app ⟨j⟩).comm m (m+1)) }
  fac s j := by ext m x; rfl
  uniq s f h := by
    apply HomologicalComplex.Hom.ext
    funext m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    exact congrArg (fun g => g.f m x) (h ⟨j⟩)
/-- 元を保持した族複体と標準productの同型。 -/
def productIso : complex F ≅ ∏ᶜ F := (limit.isoLimitCone ⟨fan F,fanIsLimit F⟩).symm
variable [Fintype J]
/-- 各実成分の有限次元性から有限族の各次数の有限次元性を導く。 -/
instance degreeFiniteDimensional (m : ℤ) [∀ j, FiniteDimensional ℚ ((F j).X m)] :
    FiniteDimensional ℚ ((complex F).X m) := by
  change FiniteDimensional ℚ ((j : J) → (F j).X m)
  infer_instance
/-- 元を保持した族複体と標準有限biproductの同型。 -/
def directSumIso : complex F ≅ ⨁ F := productIso F ≪≫ (biproduct.isoProduct F).symm
/-- 直和同型の成分は元の射影そのものである。 -/
theorem directSumIso_projection (j : J) :
    (directSumIso F).hom ≫ biproduct.π F j = projection F j := by
  simp only [directSumIso,Iso.trans_hom,Iso.symm_hom]
  rw [Category.assoc,biproduct.isoProduct_inv,biproduct.lift_π]
  exact limit.isoLimitCone_inv_π ⟨fan F,fanIsLimit F⟩ (Discrete.mk j)
/-- 有限直和同型は同じ独立成分比較のbiproduct mapと可換である。 -/
theorem directSumIso_natural (φ : ∀ j, F j ⟶ G j) :
    map F G φ ≫ (directSumIso G).hom = (directSumIso F).hom ≫ biproduct.map φ := by
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc,biproduct.map_π]
  rw [directSumIso_projection,map_projection]
  rw [← Category.assoc,directSumIso_projection]

/-- 加法的関手は任意universeの有限族の標準直和を保持する。 -/
def additivePreservesFamily {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (T : C ⥤ D) [T.Additive] (X : J → C) :
    PreservesBiproduct X T where
  preserves hb := ⟨isBilimitOfTotal _ (by
    simp_rw [Functor.mapBicone_π,Functor.mapBicone_ι,← T.map_comp]
    erw [← T.map_sum,← T.map_id,IsBilimit.total hb])⟩
/-- 標準homologyの全次数を標準成分productへ同定する。 -/
def homologyIso (m : ℤ) : (complex F).homology m ≅
    ModuleCat.of ℚ ((j : J) → (F j).homology m) := by
  let T := homologyFunctor (ModuleCat.{max v w} ℚ) (ComplexShape.up ℤ) m
  letI := additivePreservesFamily T F
  exact T.mapIso (directSumIso F) ≪≫
    IsLimit.conePointUniqueUpToIso
      (isBilimitOfPreserves T (biproduct.isBilimit F)).isLimit
      (ModuleCat.productConeIsLimit (fun j => (F j).homology m))
/-- homology同型は各実成分射影が誘導する射を保持する。 -/
theorem homologyIso_projection (m : ℤ) (j : J) :
    (homologyIso F m).hom ≫ ModuleCat.ofHom (LinearMap.proj j) =
      homologyMap (projection F j) m := by
  let T := homologyFunctor (ModuleCat.{max v w} ℚ) (ComplexShape.up ℤ) m
  letI := additivePreservesFamily T F
  simp only [homologyIso,Iso.trans_hom]
  rw [Category.assoc]
  erw [IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk j)]
  change T.map (directSumIso F).hom ≫ T.map (biproduct.π F j) = _
  rw [← T.map_comp,directSumIso_projection]
  rfl
/-- 標準homologyを各成分homologyの有限族へ読む線形同型。 -/
def homologyEquiv (m : ℤ) : (complex F).homology m ≃ₗ[ℚ]
    ((j : J) → (F j).homology m) := (homologyIso F m).toLinearEquiv
/-- 線形表示の各成分も実成分射影の標準homology mapである。 -/
@[simp] theorem homologyEquiv_component (m : ℤ) (x : (complex F).homology m) (j : J) :
    homologyEquiv F m x j = homologyMap (projection F j) m x := by
  simpa only [homologyEquiv,ModuleCat.hom_comp,LinearMap.comp_apply,
    ModuleCat.hom_ofHom,LinearMap.proj_apply] using
    congrArg (fun f => f.hom x) (homologyIso_projection F m j)
/-- 全mで、族比較の標準homologyは実成分比較と可換である。 -/
theorem homologyEquiv_natural (φ : ∀ j, F j ⟶ G j) (m : ℤ)
    (x : (complex F).homology m) (j : J) :
    homologyEquiv G m (homologyMap (map F G φ) m x) j =
      homologyMap (φ j) m (homologyEquiv F m x j) := by
  rw [homologyEquiv_component,homologyEquiv_component]
  have h := congrArg (fun (f : complex F ⟶ G j) => (homologyMap f m) x) (map_projection F G φ j)
  simpa only [homologyMap_comp,ModuleCat.comp_apply] using h
end FiniteComplexFamily
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
