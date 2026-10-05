import ResearchLean.AG.AtlasDefectComposition.ConeExactSequence
import Formal.Util.AssertStandardAxioms
/-! # 三項比較の錐の端次数

零延長の次数外の零性と標準長完全列から、端の核・余核同型と
次数0/1の二寄与を得る。他次数の寄与を一般仮定では消さない。
-/
noncomputable section
open CategoryTheory Limits HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
open TwoPhase
universe w
variable {C D : ThreeCochainComplex.{0,w} ℚ} (f : ThreeCochainComplex.Hom C D)
/-- 比較錐の次数-1 homologyは元の次数0比較の実核と同型である。 -/
def comparisonConeHMinusOneEquiv : (comparisonCone f).homology (-1) ≃ₗ[ℚ]
    LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom := by
  letI : Subsingleton ((zeroExtension D).homology (-1)) :=
    ModuleCat.subsingleton_of_isZero
      (zeroExtension_homology_isZero D (-1) (by decide) (by decide) (by decide))
  exact ShortExactFive.middleEquivKernel _ _ _
    (cone_middle_exact (zeroExtensionMap f) (-1))
    (cone_source_exact (zeroExtensionMap f) (-1))
/-- 比較錐の次数2 homologyは元の次数2比較の実余核と同型である。 -/
def comparisonConeHTwoEquiv : (comparisonCone f).homology 2 ≃ₗ[ℚ]
    ((zeroExtension D).homology 2 ⧸
      LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom) := by
  letI : Subsingleton ((zeroExtension C).homology (2+1)) :=
    ModuleCat.subsingleton_of_isZero
      (zeroExtension_homology_isZero C (2+1) (by decide) (by decide) (by decide))
  exact (ShortExactFive.cokernelEquivMiddle _ _ _
    (cone_target_exact (zeroExtensionMap f) 2) (cone_middle_exact (zeroExtensionMap f) 2)).symm
/-- Cの次数0の二寄与式を三項の実比較へ適用する。 -/
theorem comparisonCone_dimension_zero :
    Module.finrank ℚ ((comparisonCone f).homology 0) =
      Module.finrank ℚ ((zeroExtension D).homology 0 ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom) +
      Module.finrank ℚ (LinearMap.ker
        (HomologicalComplex.homologyMap (zeroExtensionMap f) 1).hom) :=
  cone_homology_dimension (zeroExtensionMap f) 0
/-- Cの次数1の二寄与式を三項の実比較へ適用する。 -/
theorem comparisonCone_dimension_one :
    Module.finrank ℚ ((comparisonCone f).homology 1) =
      Module.finrank ℚ ((zeroExtension D).homology 1 ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap f) 1).hom) +
      Module.finrank ℚ (LinearMap.ker
        (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom) :=
  cone_homology_dimension (zeroExtensionMap f) 1
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
