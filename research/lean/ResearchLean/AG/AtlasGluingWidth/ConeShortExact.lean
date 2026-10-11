import ResearchLean.AG.AtlasDefectComposition.ConeCoordinates
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence

import Formal.Util.AssertStandardAxioms
/-! # 標準mappingConeの二行図式からの短完全列

Implementation notes: fineの次数mとcoarseの次数m+1の完全性を標準錐座標で組み合わせる。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth
namespace ConeRow
open CochainComplex AAT.AG.AtlasDefectComposition
universe u
variable (R S : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)) (v : R ⟶ S)

/-- 二行図式の左二列の標準錐射。 -/
def inc := mappingCone.map v.τ₁ v.τ₂ R.f S.f v.comm₁₂
/-- 二行図式の右二列の標準錐射。 -/
def diff := mappingCone.map v.τ₂ v.τ₃ R.g S.g v.comm₂₃

/-- 錐包含はfineのmとcoarseのm+1へ同じ二行の包含を作用させる。 -/
theorem inc_coordinate (m : ℤ) (x : (mappingCone v.τ₁).X m) :
    coneCoordinateEquiv v.τ₂ m ((inc R S v).f m x) =
      (S.f.f m (coneCoordinateEquiv v.τ₁ m x).1,
        R.f.f (m+1) (coneCoordinateEquiv v.τ₁ m x).2) :=
  coneCoordinateEquiv_map _ _ _ _ _ _ _
/-- 錐差制限もfineのmとcoarseのm+1の同じ差制限を使う。 -/
theorem diff_coordinate (m : ℤ) (x : (mappingCone v.τ₂).X m) :
    coneCoordinateEquiv v.τ₃ m ((diff R S v).f m x) =
      (S.g.f m (coneCoordinateEquiv v.τ₂ m x).1,
        R.g.f (m+1) (coneCoordinateEquiv v.τ₂ m x).2) :=
  coneCoordinateEquiv_map _ _ _ _ _ _ _
/-- 原始二行の合成零を両錐座標へ適用する。 -/
theorem inc_diff : inc R S v ≫ diff R S v = 0 := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (coneCoordinateEquiv v.τ₃ m).injective
  simp only [inc, diff, ModuleCat.comp_apply, HomologicalComplex.comp_f,
    HomologicalComplex.zero_f,
    ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  rw [coneCoordinateEquiv_map, coneCoordinateEquiv_map]
  apply Prod.ext
  · have hz := congrArg (fun f : S.X₁ ⟶ S.X₃ => f.f m) S.zero
    have := congrArg (fun f => f (coneCoordinateEquiv v.τ₁ m x).1) hz
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
      ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using this
  · have hz := congrArg (fun f : R.X₁ ⟶ R.X₃ => f.f (m+1)) R.zero
    have := congrArg (fun f => f (coneCoordinateEquiv v.τ₁ m x).2) hz
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
      ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using this

/-- 同じ二行図式から得る標準錐の短複体。 -/
def row : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk (inc R S v) (diff R S v) (inc_diff R S v)

variable (hR : R.ShortExact) (hS : S.ShortExact)
include hR hS in
/-- fineのmとcoarseのm+1のSESから全整数次数の標準錐SESを導く。 -/
theorem row_shortExact : (row R S v).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro m
  have hr := (shortExact_iff_degreewise_shortExact R).mp hR (m+1)
  have hs := (shortExact_iff_degreewise_shortExact S).mp hS m
  have ir : Function.Injective (R.f.f (m+1)) := (ModuleCat.mono_iff_injective _).mp hr.mono_f
  have is : Function.Injective (S.f.f m) := (ModuleCat.mono_iff_injective _).mp hs.mono_f
  have sr : Function.Surjective (R.g.f (m+1)) := (ModuleCat.epi_iff_surjective _).mp hr.epi_g
  have ss : Function.Surjective (S.g.f m) := (ModuleCat.epi_iff_surjective _).mp hs.epi_g
  have er : Function.Exact (R.f.f (m+1)) (R.g.f (m+1)) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hr.exact
  have es : Function.Exact (S.f.f m) (S.g.f m) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hs.exact
  have hi : Function.Injective ((inc R S v).f m) := by
    intro x y hxy
    apply (coneCoordinateEquiv v.τ₁ m).injective
    have hxy' := congrArg (coneCoordinateEquiv v.τ₂ m) hxy
    simp only [inc, coneCoordinateEquiv_map] at hxy'
    exact Prod.ext (is (congrArg Prod.fst hxy')) (ir (congrArg Prod.snd hxy'))
  have hp : Function.Surjective ((diff R S v).f m) := by
    intro z
    obtain ⟨y,hy⟩ := ss (coneCoordinateEquiv v.τ₃ m z).1
    obtain ⟨x,hx⟩ := sr (coneCoordinateEquiv v.τ₃ m z).2
    refine ⟨(coneCoordinateEquiv v.τ₂ m).symm (y,x), ?_⟩
    apply (coneCoordinateEquiv v.τ₃ m).injective
    simp only [diff, coneCoordinateEquiv_map, LinearEquiv.apply_symm_apply]
    exact Prod.ext hy hx
  have he : Function.Exact ((inc R S v).f m) ((diff R S v).f m) := by
    intro z
    constructor
    · intro hz
      have hz' := congrArg (coneCoordinateEquiv v.τ₃ m) hz
      simp only [diff, coneCoordinateEquiv_map, map_zero] at hz'
      obtain ⟨y,hy⟩ := (es (coneCoordinateEquiv v.τ₂ m z).1).mp (congrArg Prod.fst hz')
      obtain ⟨x,hx⟩ := (er (coneCoordinateEquiv v.τ₂ m z).2).mp (congrArg Prod.snd hz')
      refine ⟨(coneCoordinateEquiv v.τ₁ m).symm (y,x), ?_⟩
      apply (coneCoordinateEquiv v.τ₂ m).injective
      simp only [inc, coneCoordinateEquiv_map, LinearEquiv.apply_symm_apply]
      exact Prod.ext hy hx
    · rintro ⟨x,rfl⟩
      have hz := congrArg (fun f => f.f m x) (inc_diff R S v)
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
        ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hz
  exact { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr he
          mono_f := (ModuleCat.mono_iff_injective _).mpr hi
          epi_g := (ModuleCat.epi_iff_surjective _).mpr hp }
end ConeRow
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
