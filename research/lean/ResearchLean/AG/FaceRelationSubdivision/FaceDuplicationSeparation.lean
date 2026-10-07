import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationHomology
import ResearchLean.AG.FaceRelationSubdivision.HomotopyDiagnostics
import Formal.Util.AssertStandardAxioms

/-!
# 面複製はH¹を保ち全次数同値を与えない

## Implementation notes

同じ標準H²比較の非零余核から全射性を退ける。
原始collapseを別の非同値射へ取り替える方法は使わず、その同じ射のhomotopy同値を排除する。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent) (A : Set q.Target)
variable (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A)
include hF in
/-- 選択面を複製した同じ標準H²比較は全射でない。 -/
theorem standardH2_not_surjective :
    ¬ Function.Surjective (homologyMap (zeroExtensionMap (subsetHom N F A)) 2).hom := by
  intro hs
  letI : Subsingleton ((zeroExtension ((supported N F).targetSubsetComplex A)).homology 2 ⧸
      LinearMap.range (homologyMap (zeroExtensionMap (subsetHom N F A)) 2).hom) :=
    Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hs)
  have hz : (standardH2CokernelEquiv N F A hF).symm 1 = 0 := Subsingleton.elim _ _
  have he := congrArg (standardH2CokernelEquiv N F A hF) hz
  rw [LinearEquiv.apply_symm_apply, map_zero] at he
  exact one_ne_zero he
include hF in
/-- 同じ実比較を正方向に持つ標準鎖ホモトピー同値は存在しない。 -/
theorem not_homotopy_equivalence :
    ¬ ∃ E : HomotopyEquiv (zeroExtension (N.targetSubsetComplex A))
        (zeroExtension ((supported N F).targetSubsetComplex A)),
      E.hom = zeroExtensionMap (subsetHom N F A) := by
  rintro ⟨E, he⟩
  have hb := (E.toHomologyIso 2).toLinearEquiv.bijective.2
  apply standardH2_not_surjective N F A hF
  exact he ▸ hb
end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
