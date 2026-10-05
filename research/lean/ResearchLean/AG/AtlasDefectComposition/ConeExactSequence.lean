import ResearchLean.AG.AtlasDefectComposition.ConeHomologySequence
import ResearchLean.AG.AtlasDefectComposition.ConeCoordinates
import ResearchLean.AG.AtlasDefectComposition.ShortExactFive
import Formal.Util.AssertStandardAxioms

/-! # 標準錐の次数別短完全列

G-133 Cの全整数mにおける余核/錐homology/次核を、標準長完全列から構成する。

Implementation notes: 余核と核は実homology mapのliteral quotient/submoduleとする。
ShortExactFiveの完全性の方向仮定は標準錐の三つの完全性定理で放電し、
標準ModuleCat ShortExactへ接続する。追加の次数寄与を零とは仮定しない。
-/
noncomputable section
open CategoryTheory Limits HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
universe w
variable {F G : CochainComplex (ModuleCat.{w} ℚ) ℤ} (φ : F ⟶ G)

/-- Cの全次数における実余核から標準錐homologyへの包含。 -/
def coneCokernelInclusion (m : ℤ) :
    (G.homology m ⧸ LinearMap.range (HomologicalComplex.homologyMap φ m).hom) →ₗ[ℚ]
      (mappingCone φ).homology m :=
  ShortExactFive.inclusion _ _ (cone_target_exact φ m)

/-- Cの全次数における標準錐homologyから次比較の核への射。 -/
def coneKernelProjection (m : ℤ) :
    (mappingCone φ).homology m →ₗ[ℚ] LinearMap.ker (HomologicalComplex.homologyMap φ (m+1)).hom :=
  ShortExactFive.projection _ _ (cone_source_exact φ m)

/-- 余核包含はすべての実homology代表元で標準錐包含を読む。 -/
@[simp] theorem coneCokernelInclusion_mk (m : ℤ) (y : G.homology m) :
    coneCokernelInclusion φ m
      ((LinearMap.range (HomologicalComplex.homologyMap φ m).hom).mkQ y) =
    HomologicalComplex.homologyMap (mappingCone.inr φ) m y :=
  ShortExactFive.inclusion_mk _ _ _ _

/-- 核への射の実値は標準連結射に一致する。 -/
@[simp] theorem coneKernelProjection_val (m : ℤ) (y : (mappingCone φ).homology m) :
    (coneKernelProjection φ m y).val = coneConnecting φ m y := rfl

/-- 標準錐の余核包含は全次数で単射である。 -/
theorem coneCokernelInclusion_injective (m : ℤ) : Function.Injective (coneCokernelInclusion φ m) :=
  ShortExactFive.inclusion_injective _ _ _

/-- 標準長完全列から得る短列の中間完全性。 -/
theorem cone_short_function_exact (m : ℤ) :
    Function.Exact (coneCokernelInclusion φ m) (coneKernelProjection φ m) :=
  ShortExactFive.exact _ _ _ _ (cone_target_exact φ m) (cone_middle_exact φ m)
    (cone_source_exact φ m)

/-- 標準錐から次比較の核への射は全次数で全射である。 -/
theorem coneKernelProjection_surjective (m : ℤ) : Function.Surjective (coneKernelProjection φ m) :=
  ShortExactFive.projection_surjective _ _ _

/-- Cの短完全列を標準ModuleCat短複体として構成する。 -/
def coneShortComplex (m : ℤ) : ShortComplex (ModuleCat.{w} ℚ) :=
  ShortComplex.moduleCatMk (coneCokernelInclusion φ m) (coneKernelProjection φ m) (by
    apply LinearMap.ext
    intro x
    exact (cone_short_function_exact φ m (coneCokernelInclusion φ m x)).mpr ⟨x,rfl⟩)

/-- 全整数mの余核/標準錐homology/次核は標準ShortExactを満たす。 -/
theorem cone_short_exact (m : ℤ) : (coneShortComplex φ m).ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (cone_short_function_exact φ m)
  mono_f := (ModuleCat.mono_iff_injective _).mpr (coneCokernelInclusion_injective φ m)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (coneKernelProjection_surjective φ m)

/-- 有限次元の短複体中間項は標準homologyの有限次元性を与える。 -/
instance moduleCatHomologyFiniteDimensional (S : ShortComplex (ModuleCat.{w} ℚ))
    [FiniteDimensional ℚ S.X₂] : FiniteDimensional ℚ S.homology := by
  let e : S.homology ≃ₗ[ℚ] LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles :=
    S.moduleCatHomologyIso.toLinearEquiv
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- 標準complexの同じ次数の有限次元性をhomologyへ移す。 -/
instance cochainHomologyFiniteDimensional (K : CochainComplex (ModuleCat.{w} ℚ) ℤ) (m : ℤ)
    [FiniteDimensional ℚ (K.X m)] : FiniteDimensional ℚ (K.homology m) := by
  letI : FiniteDimensional ℚ (K.sc m).X₂ := by
    change FiniteDimensional ℚ (K.X m)
    infer_instance
  exact moduleCatHomologyFiniteDimensional (K.sc m)

/-- 全次数の短完全列は余核寄与と次核寄与の次元加法式を与える。 -/
theorem cone_homology_dimension (m : ℤ) [FiniteDimensional ℚ ((mappingCone φ).X m)] :
    Module.finrank ℚ ((mappingCone φ).homology m) =
      Module.finrank ℚ (G.homology m ⧸ LinearMap.range (HomologicalComplex.homologyMap φ m).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap φ (m+1)).hom) :=
  ShortExactFive.dimension _ _ _ _ (cone_target_exact φ m) (cone_middle_exact φ m)
    (cone_source_exact φ m)

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
