import ResearchLean.AG.AtlasDefectComposition.EndpointNaturality
import ResearchLean.AG.AtlasDefectComposition.ConeExactSequence
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import ResearchLean.AG.UniformInvariance.DefectSemantics
import Formal.Util.AssertStandardAxioms
/-! # 既存比較の核・余核と標準homology

元のH¹欠損を変更せず、標準錐短完全列のH¹項へ両方向に同定する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open TwoPhase ResolutionInvariance
universe w
variable {C D : ThreeCochainComplex.{0,w} ℚ} (f : ThreeCochainComplex.Hom C D)
/-- 標準H¹比較の実核は既存H¹比較の実核と元を保つ同型を持つ。 -/
def standardH1KernelEquiv : LinearMap.ker f.h1Map ≃ₗ[ℚ]
    LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap f) 1).hom :=
  LinearConjugation.kernelEquiv _ _ (oldH1Equiv C) (oldH1Equiv D)
    (oldH1Equiv_natural f)
/-- 標準H¹比較の実余核は既存H¹比較の実余核と代表元を保つ同型を持つ。 -/
def standardH1CokernelEquiv : (D.H1 ⧸ LinearMap.range f.h1Map) ≃ₗ[ℚ]
    ((zeroExtension D).homology 1 ⧸
      LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap f) 1).hom) :=
  LinearConjugation.cokernelEquiv _ _ (oldH1Equiv C) (oldH1Equiv D)
    (oldH1Equiv_natural f)
/-- 標準H⁰比較の単射・全射の双方は元の次数0核射のそれらと同値である。 -/
theorem standardH0_bijective_iff :
    Function.Bijective (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom ↔
      Function.Bijective (oldH0Map f) :=
  (LinearConjugation.bijective_iff _ _ (oldH0Equiv C) (oldH0Equiv D)
    (oldH0Equiv_natural f)).symm
/-- 標準H²比較の単射・全射の双方は元の終端商射のそれらと同値である。 -/
theorem standardH2_bijective_iff :
    Function.Bijective (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom ↔
      Function.Bijective (oldH2Map f) :=
  (LinearConjugation.bijective_iff _ _ (oldH2Equiv C) (oldH2Equiv D)
    (oldH2Equiv_natural f)).symm
/-- 標準homology H¹での欠損は既存blockDefectの二成分に一致する。 -/
theorem standardH1_defect :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap f) 1).hom =
      blockDefect f.h1Map := by
  have hr := LinearConjugation.range_dimension f.h1Map
    (HomologicalComplex.homologyMap (zeroExtensionMap f) 1).hom
    (oldH1Equiv C) (oldH1Equiv D) (oldH1Equiv_natural f)
  rw [blockDefect_eq_finrank_sub_range,blockDefect_eq_finrank_sub_range,
    ← (oldH1Equiv C).finrank_eq,← (oldH1Equiv D).finrank_eq,← hr]
/-- blockDefectの第一成分を実核次元として読む公開API。 -/
theorem blockDefect_kernel_dimension {A B : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (g : A →ₗ[ℚ] B) : (blockDefect g).1 = Module.finrank ℚ (LinearMap.ker g) := by
  rw [blockDefect_eq_finrank_sub_range]
  dsimp only
  have h := g.finrank_range_add_finrank_ker
  omega
/-- blockDefectの第二成分を実余核次元として読む公開API。 -/
theorem blockDefect_cokernel_dimension {A B : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (g : A →ₗ[ℚ] B) : (blockDefect g).2 = Module.finrank ℚ (B ⧸ LinearMap.range g) := by
  rw [blockDefect_eq_finrank_sub_range]
  dsimp only
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range g)
  omega

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
