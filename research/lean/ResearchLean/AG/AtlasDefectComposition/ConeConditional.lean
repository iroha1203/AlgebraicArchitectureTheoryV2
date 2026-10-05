import ResearchLean.AG.AtlasDefectComposition.ConeEndDegrees
import ResearchLean.AG.AtlasDefectComposition.ComparisonHomology
import ResearchLean.AG.AtlasDefectComposition.ShortExactFiveConditions
import Formal.Util.AssertStandardAxioms
/-! # 標準錐の条件付き同型とその必要十分条件

標準短完全列の指定包含・射影そのものが同型になる条件を全次数で判定する。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
universe w
variable {F G : CochainComplex (ModuleCat.{w} ℚ) ℤ} (φ : F ⟶ G)
/-- 錐から次比較の核への指定射は、同次数homology比較の全射性と同値に同型である。 -/
theorem coneKernelProjection_bijective_iff (m : ℤ) :
    Function.Bijective (coneKernelProjection φ m) ↔
      Function.Surjective (HomologicalComplex.homologyMap φ m).hom :=
  ShortExactFive.projection_bijective_iff _ _ _ _
    (cone_target_exact φ m) (cone_middle_exact φ m) (cone_source_exact φ m)
/-- 実余核から標準錐への指定包含は、次homology比較の単射性と同値に同型である。 -/
theorem coneCokernelInclusion_bijective_iff (m : ℤ) :
    Function.Bijective (coneCokernelInclusion φ m) ↔
      Function.Injective (HomologicalComplex.homologyMap φ (m+1)).hom :=
  ShortExactFive.inclusion_bijective_iff _ _ _ _
    (cone_target_exact φ m) (cone_middle_exact φ m) (cone_source_exact φ m)
/-- 同次数homology比較が全射なら、指定射影が標準錐と次核の線形同型を作る。 -/
def coneKernelProjectionEquiv (m : ℤ)
    (hs : Function.Surjective (HomologicalComplex.homologyMap φ m).hom) :
    (mappingCone φ).homology m ≃ₗ[ℚ]
      LinearMap.ker (HomologicalComplex.homologyMap φ (m+1)).hom :=
  LinearEquiv.ofBijective (coneKernelProjection φ m)
    ((coneKernelProjection_bijective_iff φ m).mpr hs)
/-- 次homology比較が単射なら、指定包含が実余核と標準錐の線形同型を作る。 -/
def coneCokernelInclusionEquiv (m : ℤ)
    (hi : Function.Injective (HomologicalComplex.homologyMap φ (m+1)).hom) :
    (G.homology m ⧸ LinearMap.range (HomologicalComplex.homologyMap φ m).hom) ≃ₗ[ℚ]
      (mappingCone φ).homology m :=
  LinearEquiv.ofBijective (coneCokernelInclusion φ m)
    ((coneCokernelInclusion_bijective_iff φ m).mpr hi)
/-- 条件付き核同型は指定された連結射の核制限そのものである。 -/
@[simp] theorem coneKernelProjectionEquiv_apply (m : ℤ)
    (hs : Function.Surjective (HomologicalComplex.homologyMap φ m).hom)
    (x : (mappingCone φ).homology m) :
    coneKernelProjectionEquiv φ m hs x = coneKernelProjection φ m x := rfl
/-- 条件付き余核同型は指定された余核包含そのものである。 -/
@[simp] theorem coneCokernelInclusionEquiv_apply (m : ℤ)
    (hi : Function.Injective (HomologicalComplex.homologyMap φ (m+1)).hom)
    (x : G.homology m ⧸ LinearMap.range (HomologicalComplex.homologyMap φ m).hom) :
    coneCokernelInclusionEquiv φ m hi x = coneCokernelInclusion φ m x := rfl
/-- 実余核の零性は元の線形比較の全射性と同値である。 -/
theorem cokernel_zero_iff_surjective {A B : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] [FiniteDimensional ℚ B] (f : A →ₗ[ℚ] B) :
    Module.finrank ℚ (B ⧸ LinearMap.range f)=0 ↔ Function.Surjective f := by
  rw [Module.finrank_zero_iff,Submodule.Quotient.subsingleton_iff,LinearMap.range_eq_top]
/-- 実核の零性は元の線形比較の単射性と同値である。 -/
theorem kernel_zero_iff_injective {A B : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] [FiniteDimensional ℚ A] (f : A →ₗ[ℚ] B) :
    Module.finrank ℚ (LinearMap.ker f)=0 ↔ Function.Injective f := by
  rw [Submodule.finrank_eq_zero,LinearMap.ker_eq_bot]

variable {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ} (f : TwoPhase.ThreeCochainComplex.Hom C D)
/-- Cの次数0追加項の零性は、実標準H⁰比較の全射性と同値である。 -/
theorem comparison_H0_cokernel_zero_iff :
    Module.finrank ℚ ((zeroExtension D).homology 0 ⧸
      LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom)=0 ↔
    Function.Surjective (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom :=
  cokernel_zero_iff_surjective _
/-- Cの次数1追加項の零性は、実標準H²比較の単射性と同値である。 -/
theorem comparison_H2_kernel_zero_iff :
    Module.finrank ℚ (LinearMap.ker
      (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom)=0 ↔
    Function.Injective (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom :=
  kernel_zero_iff_injective _
/-- H⁰比較全射の下で、指定錐射影を既存H¹比較の実核へ接続する。 -/
def comparisonConeH0KernelEquiv
    (hs : Function.Surjective (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom) :
    (comparisonCone f).homology 0 ≃ₗ[ℚ] LinearMap.ker f.h1Map :=
  (coneKernelProjectionEquiv (zeroExtensionMap f) 0 hs).trans (standardH1KernelEquiv f).symm
/-- H²比較単射の下で、既存H¹比較の実余核を指定錐包含へ接続する。 -/
def comparisonConeH1CokernelEquiv
    (hi : Function.Injective (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom) :
    (D.H1 ⧸ LinearMap.range f.h1Map) ≃ₗ[ℚ] (comparisonCone f).homology 1 :=
  (standardH1CokernelEquiv f).trans (coneCokernelInclusionEquiv (zeroExtensionMap f) 1 hi)
/-- 条件付き次数0同型の元は指定射影を既存H¹核へ移したものである。 -/
@[simp] theorem comparisonConeH0KernelEquiv_apply
    (hs : Function.Surjective (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom)
    (x : (comparisonCone f).homology 0) :
    comparisonConeH0KernelEquiv f hs x =
      (standardH1KernelEquiv f).symm (coneKernelProjection (zeroExtensionMap f) 0 x) := rfl
/-- 条件付き次数1同型の元は既存H¹余核を指定包含へ移したものである。 -/
@[simp] theorem comparisonConeH1CokernelEquiv_apply
    (hi : Function.Injective (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom)
    (x : D.H1 ⧸ LinearMap.range f.h1Map) :
    comparisonConeH1CokernelEquiv f hi x =
      coneCokernelInclusion (zeroExtensionMap f) 1 (standardH1CokernelEquiv f x) := rfl
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
