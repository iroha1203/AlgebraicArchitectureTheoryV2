import ResearchLean.AG.AtlasDefectComposition.ConeEndDegrees
import ResearchLean.AG.AtlasDefectComposition.HomologyDimensions
import ResearchLean.AG.AtlasDefectComposition.ComparisonHomology
import Formal.Util.AssertStandardAxioms
/-! # 標準錐の有限次元計算

端の零性、標準short homologyの像次元、実長完全列だけから数値寄与を計算する。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
universe w
/-- 標準ModuleCat短複体の実境界像次元は元のfirst射の像次元である。 -/
theorem shortComplex_boundary_rank (S : ShortComplex (ModuleCat.{w} ℚ)) :
    Module.finrank ℚ (LinearMap.range S.moduleCatToCycles) =
      Module.finrank ℚ (LinearMap.range S.f.hom) :=
  finrank_range_codRestrict S.f.hom _ S.moduleCat_zero_apply
/-- 有限次元の標準短複体のhomologyと前後の像次元の加法式。 -/
theorem shortComplex_homology_dimension (S : ShortComplex (ModuleCat.{w} ℚ))
    [FiniteDimensional ℚ S.X₂] :
    Module.finrank ℚ S.homology + Module.finrank ℚ (LinearMap.range S.f.hom) +
      Module.finrank ℚ (LinearMap.range S.g.hom) = Module.finrank ℚ S.X₂ := by
  have hh := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank ℚ S.homology = Module.finrank ℚ
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at hh
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)
  have hr := S.g.hom.finrank_range_add_finrank_ker
  rw [←hh,shortComplex_boundary_rank] at hq
  omega
/-- 任意の整数次数でhomologyと隣接二微分のrankが次数空間へ加算される。 -/
theorem complex_homology_dimension (K : CochainComplex (ModuleCat.{w} ℚ) ℤ)
    (m : ℤ) [FiniteDimensional ℚ (K.X m)] :
    Module.finrank ℚ (K.homology m) +
      Module.finrank ℚ (LinearMap.range (K.d (m-1) m).hom) +
      Module.finrank ℚ (LinearMap.range (K.d m (m+1)).hom) =
        Module.finrank ℚ (K.X m) := by
  let e := K.homologyIsoSc' (m-1) m (m+1) (by simp) (by simp)
  letI : FiniteDimensional ℚ (K.sc' (m-1) m (m+1)).X₂ := by
    change FiniteDimensional ℚ (K.X m)
    infer_instance
  have h := shortComplex_homology_dimension (K.sc' (m-1) m (m+1))
  rw [← e.toLinearEquiv.finrank_eq] at h
  exact h
/-- 同じ次数の空間が零対象なら標準complexのhomologyも零対象である。 -/
theorem complex_homology_isZero (K : CochainComplex (ModuleCat.{w} ℚ) ℤ)
    (m : ℤ) (hm : CategoryTheory.Limits.IsZero (K.X m)) :
    CategoryTheory.Limits.IsZero (K.homology m) :=
  (K.sc m).isZero_homology_of_isZero_X₂ hm
/-- 三項比較の錐の四次数外のhomologyは零対象である。 -/
theorem comparisonCone_homology_isZero
    {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ} (f : TwoPhase.ThreeCochainComplex.Hom C D)
    (m : ℤ) (hneg : m ≠ -1) (h0 : m ≠ 0) (h1 : m ≠ 1) (h2 : m ≠ 2) :
    CategoryTheory.Limits.IsZero ((comparisonCone f).homology m) :=
  complex_homology_isZero _ _ (comparisonCone_isZero f m hneg h0 h1 h2)
/-- 三項比較の標準錐homology次元を実homology比較の二欠損成分へ接続する。 -/
theorem comparisonCone_dimension_defect
    {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ} (f : TwoPhase.ThreeCochainComplex.Hom C D)
    (m : ℤ) :
    Module.finrank ℚ ((comparisonCone f).homology m) =
      (ResolutionInvariance.blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap f) m).hom).2 +
      (ResolutionInvariance.blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap f) (m+1)).hom).1 := by
  rw [blockDefect_cokernel_dimension,blockDefect_kernel_dimension]
  exact cone_homology_dimension (zeroExtensionMap f) m
/-- 三項比較の標準錐の次数-1次元は次数0比較の第一欠損成分である。 -/
theorem comparisonCone_dimension_minus_one
    {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ} (f : TwoPhase.ThreeCochainComplex.Hom C D) :
    Module.finrank ℚ ((comparisonCone f).homology (-1)) =
      (ResolutionInvariance.blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom).1 := by
  rw [blockDefect_kernel_dimension]
  exact (comparisonConeHMinusOneEquiv f).finrank_eq
/-- 三項比較の標準錐の次数2次元は次数2比較の第二欠損成分である。 -/
theorem comparisonCone_dimension_two
    {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ} (f : TwoPhase.ThreeCochainComplex.Hom C D) :
    Module.finrank ℚ ((comparisonCone f).homology 2) =
      (ResolutionInvariance.blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom).2 := by
  rw [blockDefect_cokernel_dimension]
  exact (comparisonConeHTwoEquiv f).finrank_eq

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
