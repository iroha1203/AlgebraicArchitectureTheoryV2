import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationDegreeTwo
import ResearchLean.AG.FaceRelationSubdivision.EndCokernel
import ResearchLean.AG.AtlasDefectComposition.ConeEndDegrees
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import Formal.Util.AssertStandardAxioms

/-!
# 面複製の実H²余核と同じ標準錐

## Implementation notes

原始differenceの核・全射と実次数2像の二重商を接続する。
標準H²へはG-133の実Hom自然性を使い、同じ実錐へは端次数完全列を使う。
H¹保存を全次数同値とする方式は、ここで得られる非零余核に反するため採らない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent) (A : Set q.Target)
variable (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A)

/-- 原始差による実次数2像の商はℚ。 -/
def degreeTwoQuotientEquiv :
    (((supported N F).targetSubsetComplex A).C2 ⧸ LinearMap.range (subsetHom N F A).f2) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ (difference_kernel N F A hF).symm).trans
    ((difference N F A hF).quotKerEquivOfSurjective (difference_surjective N F A hF))
/-- 実次数2像の商同定は原始差を評価する。 -/
@[simp] theorem degreeTwoQuotientEquiv_mk (z : ((supported N F).targetSubsetComplex A).C2) :
    degreeTwoQuotientEquiv N F A hF ((LinearMap.range (subsetHom N F A).f2).mkQ z) =
      difference N F A hF z := rfl
/-- 同じ実H²比較の余核は、Fが選択されればℚ。 -/
def oldH2CokernelEquiv :
    (((((supported N F).targetSubsetComplex A).C2 ⧸ LinearMap.range ((supported N F).targetSubsetComplex A).d1))
      ⧸ LinearMap.range (oldH2Map (subsetHom N F A))) ≃ₗ[ℚ] ℚ :=
  (endCokernelEquiv (subsetHom N F A) (differential_range_le N F A)).trans
    (degreeTwoQuotientEquiv N F A hF)
/-- 実H²余核への代表元の値は同じ原始差。 -/
@[simp] theorem oldH2CokernelEquiv_mk (z : ((supported N F).targetSubsetComplex A).C2) :
    oldH2CokernelEquiv N F A hF ((LinearMap.range (oldH2Map (subsetHom N F A))).mkQ
      ((LinearMap.range ((supported N F).targetSubsetComplex A).d1).mkQ z)) = difference N F A hF z := by
  simp only [oldH2CokernelEquiv, LinearEquiv.trans_apply, endCokernelEquiv_mk, degreeTwoQuotientEquiv_mk]
include hF in
/-- fresh面単独1は同じ実H²余核で1を与える。 -/
theorem freshOnly_cokernel_nonzero :
    (LinearMap.range (oldH2Map (subsetHom N F A))).mkQ
      ((LinearMap.range ((supported N F).targetSubsetComplex A).d1).mkQ (freshOnly N F A 1)) ≠ 0 := by
  intro hz
  have he := congrArg (oldH2CokernelEquiv N F A hF) hz
  rw [oldH2CokernelEquiv_mk, difference_freshOnly, map_zero] at he
  exact one_ne_zero he
/-- 実旧H²射と標準H²射の自然性による実余核同定。 -/
def standardH2CokernelOldEquiv :
    ((zeroExtension ((supported N F).targetSubsetComplex A)).homology 2 ⧸
      LinearMap.range (homologyMap (zeroExtensionMap (subsetHom N F A)) 2).hom) ≃ₗ[ℚ]
    (((((supported N F).targetSubsetComplex A).C2 ⧸ LinearMap.range ((supported N F).targetSubsetComplex A).d1))
      ⧸ LinearMap.range (oldH2Map (subsetHom N F A))) :=
  (LinearConjugation.cokernelEquiv (oldH2Map (subsetHom N F A))
    (homologyMap (zeroExtensionMap (subsetHom N F A)) 2).hom
    (oldH2Equiv (N.targetSubsetComplex A)) (oldH2Equiv ((supported N F).targetSubsetComplex A))
    (oldH2Equiv_natural (subsetHom N F A))).symm
/-- 同じ標準H²比較の実余核はℚ。 -/
def standardH2CokernelEquiv :
    ((zeroExtension ((supported N F).targetSubsetComplex A)).homology 2 ⧸
      LinearMap.range (homologyMap (zeroExtensionMap (subsetHom N F A)) 2).hom) ≃ₗ[ℚ] ℚ :=
  (standardH2CokernelOldEquiv N F A).trans (oldH2CokernelEquiv N F A hF)
/-- 同じ実生成比較の標準錐H²はℚ。 -/
def coneH2Equiv : (comparisonCone (subsetHom N F A)).homology 2 ≃ₗ[ℚ] ℚ :=
  (comparisonConeHTwoEquiv (subsetHom N F A)).trans (standardH2CokernelEquiv N F A hF)

end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
