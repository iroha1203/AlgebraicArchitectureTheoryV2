import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationDegreeTwo
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import Formal.Util.AssertStandardAxioms

/-! # 面複製の同じ実H⁰同型とH²単射

## Implementation notes

原始sectionの双対を左逆として用い、実核・実終端商で証明する。
標準homologyへは既存の自然性で接続し、次元比較には依存しない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent) (A : Set q.Target)
/-- 同じ生成cochain二射は旧側で全三成分が恒等へ合成する。 -/
theorem subset_reverse_comp : cochainComp (subsetHom N F A) (reverseSubsetHom N F A) =
    cochainId (N.targetSubsetComplex A) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    simp only [cochainComp_f0, subsetHom_f0, reverseSubsetHom_f0, cochainId_f0]
  · apply LinearMap.ext; intro z
    simp only [cochainComp_f1, subsetHom_f1, reverseSubsetHom_f1, cochainId_f1]
  · apply LinearMap.ext; intro z
    funext f
    simp only [cochainComp_f2, reverseSubsetHom_f2, subsetHom_f2_old, cochainId_f2]
/-- 同じ実H⁰二射の左逆。 -/
theorem reverse_oldH0_comp : (oldH0Map (reverseSubsetHom N F A)).comp
    (oldH0Map (subsetHom N F A)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply, oldH0Map_val, subsetHom_f0, reverseSubsetHom_f0, LinearMap.id_apply]
/-- 同じ実H⁰二射の右逆。 -/
theorem oldH0_reverse_comp : (oldH0Map (subsetHom N F A)).comp
    (oldH0Map (reverseSubsetHom N F A)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply, oldH0Map_val, subsetHom_f0, reverseSubsetHom_f0, LinearMap.id_apply]
/-- 全Aで実次数0核の同じ生成写像は線形同値。 -/
def subsetH0Equiv : LinearMap.ker (N.targetSubsetComplex A).d0 ≃ₗ[ℚ]
    LinearMap.ker ((supported N F).targetSubsetComplex A).d0 :=
  LinearEquiv.ofLinear (oldH0Map (subsetHom N F A)) (oldH0Map (reverseSubsetHom N F A))
    (oldH0_reverse_comp N F A) (reverse_oldH0_comp N F A)
/-- 同値の正方向は同じ実核射。 -/
@[simp] theorem subsetH0Equiv_toLinearMap : (subsetH0Equiv N F A).toLinearMap =
    oldH0Map (subsetHom N F A) := rfl
/-- 同じ実H²二射の左逆。 -/
theorem reverse_oldH2_comp : (oldH2Map (reverseSubsetHom N F A)).comp
    (oldH2Map (subsetHom N F A)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    apply congrArg (LinearMap.range (N.targetSubsetComplex A).d1).mkQ
    funext f
    rw [reverseSubsetHom_f2, subsetHom_f2_old]
/-- 全Aで同じ実H²比較は単射。 -/
theorem oldH2_injective : Function.Injective (oldH2Map (subsetHom N F A)) := by
  intro x y h
  have he := congrArg (oldH2Map (reverseSubsetHom N F A)) h
  have hi := LinearMap.congr_fun (reverse_oldH2_comp N F A)
  exact (hi x).symm.trans (he.trans (hi y))
/-- 同じ標準H⁰の線形同値。 -/
def subsetStandardH0Equiv : (zeroExtension (N.targetSubsetComplex A)).homology 0 ≃ₗ[ℚ]
    (zeroExtension ((supported N F).targetSubsetComplex A)).homology 0 :=
  (oldH0Equiv (N.targetSubsetComplex A)).symm.trans
    ((subsetH0Equiv N F A).trans (oldH0Equiv ((supported N F).targetSubsetComplex A)))
/-- 標準同値は同じ実生成零延長射を読む。 -/
theorem subsetStandardH0Equiv_apply (x : (zeroExtension (N.targetSubsetComplex A)).homology 0) :
    subsetStandardH0Equiv N F A x = homologyMap (zeroExtensionMap (subsetHom N F A)) 0 x := by
  have h := oldH0Equiv_natural (subsetHom N F A) ((oldH0Equiv (N.targetSubsetComplex A)).symm x)
  simpa only [subsetStandardH0Equiv, LinearEquiv.trans_apply, subsetH0Equiv, LinearEquiv.ofLinear_apply,
    LinearEquiv.apply_symm_apply] using h
/-- 同じ標準H⁰比較はbijective。 -/
theorem subsetStandardH0_bijective : Function.Bijective
    (homologyMap (zeroExtensionMap (subsetHom N F A)) 0) := by
  have he : ⇑(subsetStandardH0Equiv N F A) = ⇑(homologyMap (zeroExtensionMap (subsetHom N F A)) 0) :=
    funext (subsetStandardH0Equiv_apply N F A)
  rw [← he]
  exact (subsetStandardH0Equiv N F A).bijective
/-- 同じ標準H²比較は単射。 -/
theorem subsetStandardH2_injective : Function.Injective
    (homologyMap (zeroExtensionMap (subsetHom N F A)) 2) := by
  intro x y h
  obtain ⟨a,rfl⟩ := (oldH2Equiv (N.targetSubsetComplex A)).surjective x
  obtain ⟨b,rfl⟩ := (oldH2Equiv (N.targetSubsetComplex A)).surjective y
  rw [← oldH2Equiv_natural, ← oldH2Equiv_natural] at h
  exact congrArg (oldH2Equiv (N.targetSubsetComplex A))
    (oldH2_injective N F A ((oldH2Equiv ((supported N F).targetSubsetComplex A)).injective h))
end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
