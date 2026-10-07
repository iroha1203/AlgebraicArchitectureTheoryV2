import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationChainSplit
import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationEndpoints
import ResearchLean.AG.AtlasDefectComposition.CochainEquivalence
import Formal.Util.AssertStandardAxioms

/-! # 非選択面の複製は同じ支持複体

## Implementation notes

fresh面が選択されないことを原始台から排除し、全選択面が旧面であると証明する。
選択Fを仮定した分解を無条件化せず、同じr/s全三成分を使う。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent) (A : Set q.Target)
variable (hF : ¬ ∃ t, t ∈ N.faceSupport F ∧ t ∈ A)
include hF in
/-- 面Fが非選択ならfine選択面は全て旧面である。 -/
theorem oldFace_foldFace_absent (f : (supported N F).FaceInTargetSubset A) :
    oldFace N F A (foldFace N F A f) = f := by
  rcases f with ⟨f,hf⟩
  rcases f with f | x
  · rfl
  · cases x
    exact False.elim (hF hf)
include hF in
/-- 非選択成分で原始chain二射は右逆でもある。 -/
theorem chainS2_chainR2_absent : (chainS2 N F A).comp (chainR2 N F A) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro f a
  simp only [LinearMap.comp_apply, chainR2_single, chainS2_single,
    oldFace_foldFace_absent N F A hF, Finsupp.smul_single, smul_eq_mul, mul_one, LinearMap.id_apply]
/-- 非選択次数2chainの同値。低次恒等と微分可換を合わせK′=K。 -/
def absentChainEquiv : K2 (supported N F) A ≃ₗ[ℚ] K2 N A :=
  LinearEquiv.ofLinear (chainR2 N F A) (chainS2 N F A)
    (chainR2_chainS2 N F A) (chainS2_chainR2_absent N F A hF)
/-- 非選択chain同値の正方向は実原始fold。 -/
@[simp] theorem absentChainEquiv_toLinearMap : (absentChainEquiv N F A hF).toLinearMap =
    chainR2 N F A := rfl
include hF in
/-- 非選択成分の同じ生成cochain二射はfine側でも全三成分恒等。 -/
theorem reverse_subset_comp_absent : cochainComp (reverseSubsetHom N F A) (subsetHom N F A) =
    cochainId ((supported N F).targetSubsetComplex A) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    simp only [cochainComp_f0, subsetHom_f0, reverseSubsetHom_f0, cochainId_f0]
  · apply LinearMap.ext; intro z
    simp only [cochainComp_f1, subsetHom_f1, reverseSubsetHom_f1, cochainId_f1]
  · apply LinearMap.ext; intro z
    funext f
    simp only [cochainComp_f2, subsetHom_f2, reverseSubsetHom_f2,
      oldFace_foldFace_absent N F A hF, cochainId_f2]
/-- 非選択成分で同じ生成比較は全三成分同値。 -/
def absentCochainEquiv : ThreeCochainComplex.CochainEquiv (N.targetSubsetComplex A)
    ((supported N F).targetSubsetComplex A) where
  e0 := LinearEquiv.refl ℚ _
  e1 := LinearEquiv.refl ℚ _
  e2 := LinearEquiv.ofLinear (subsetHom N F A).f2 (reverseSubsetHom N F A).f2
    (by
      have h := congrArg ThreeCochainComplex.Hom.f2 (reverse_subset_comp_absent N F A hF)
      exact h)
    (by
      have h := congrArg ThreeCochainComplex.Hom.f2 (subset_reverse_comp N F A)
      exact h)
  comm0 := by
    intro z
    simpa only [subsetHom_f0, subsetHom_f1, LinearEquiv.refl_apply] using (subsetHom N F A).comm0 z
  comm1 := by
    intro z
    exact (subsetHom N F A).comm1 z
/-- 全三成分同値の正方向は独立生成した同じ実subset射。 -/
theorem absentCochainEquiv_toHom : (absentCochainEquiv N F A hF).toHom = subsetHom N F A := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    exact (subsetHom_f0 N F A z).symm
  · apply LinearMap.ext; intro z
    exact (subsetHom_f1 N F A z).symm
  · rfl
/-- 非選択成分の同じ標準零延長比較は全整数次数で同型。 -/
def absentZeroExtensionIso : zeroExtension (N.targetSubsetComplex A) ≅
    zeroExtension ((supported N F).targetSubsetComplex A) :=
  cochainEquivZeroExtensionIso (absentCochainEquiv N F A hF)
/-- 標準同型の順射も同じ比較。 -/
theorem absentZeroExtensionIso_hom : (absentZeroExtensionIso N F A hF).hom =
    zeroExtensionMap (subsetHom N F A) := by
  rw [absentZeroExtensionIso, cochainEquivZeroExtensionIso_hom, absentCochainEquiv_toHom]
include hF in
/-- 全整数次数同型の順射は同じ実homology射。 -/
theorem absent_homology_bijective (n : ℤ) : Function.Bijective
    (homologyMap (zeroExtensionMap (subsetHom N F A)) n) := by
  rw [← absentZeroExtensionIso_hom N F A hF, ← homologyMapIso_hom]
  exact (homologyMapIso (absentZeroExtensionIso N F A hF) n).toLinearEquiv.bijective
end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
