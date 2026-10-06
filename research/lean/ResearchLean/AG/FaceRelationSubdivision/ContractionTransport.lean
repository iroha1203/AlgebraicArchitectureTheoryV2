import ResearchLean.AG.FaceRelationSubdivision.PresentationInverse
import Formal.Util.AssertStandardAxioms

/-!
# 原始収縮の支持セル表示への移送

## Implementation notes

この一般補題の入力は既に生成した収縮と支持chain表示同型であり、基本操作の入力ではない。
各逆patternへの適用では前者を正操作constructor、後者を復元表示constructorから作る。
同じr/s/hを明示的に共役し、同型存在だけから保存結論を推測する案を採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace SubsetChainContraction
variable {B M N : TargetSupportedNerve.{u, u} q} {A : Set q.Target}

/-- 三次数の支持基底同型で、同じ原始r/s/hを元の表示へ移す。 -/
def renameFine (C : SubsetChainContraction B M A A)
    (e0 : K0 M A ≃ₗ[ℚ] K0 N A) (e1 : K1 M A ≃ₗ[ℚ] K1 N A)
    (e2 : K2 M A ≃ₗ[ℚ] K2 N A)
    (he01 : (chainD1 N A).comp e1.toLinearMap = e0.toLinearMap.comp (chainD1 M A))
    (he12 : (chainD2 N A).comp e2.toLinearMap = e1.toLinearMap.comp (chainD2 M A)) :
    SubsetChainContraction B N A A where
  r0 := C.r0.comp e0.symm.toLinearMap
  r1 := C.r1.comp e1.symm.toLinearMap
  r2 := C.r2.comp e2.symm.toLinearMap
  s0 := e0.toLinearMap.comp C.s0
  s1 := e1.toLinearMap.comp C.s1
  s2 := e2.toLinearMap.comp C.s2
  h0 := e1.toLinearMap.comp (C.h0.comp e0.symm.toLinearMap)
  h1 := e2.toLinearMap.comp (C.h1.comp e1.symm.toLinearMap)
  r_comm01 := by
    apply LinearMap.ext
    intro x
    exact (LinearMap.congr_fun C.r_comm01 (e1.symm x)).trans
      (congrArg C.r0 (LinearMap.congr_fun (CellPresentationEquiv.inverse_comm e0 e1 _ _ he01) x))
  r_comm12 := by
    apply LinearMap.ext
    intro x
    exact (LinearMap.congr_fun C.r_comm12 (e2.symm x)).trans
      (congrArg C.r1 (LinearMap.congr_fun (CellPresentationEquiv.inverse_comm e1 e2 _ _ he12) x))
  s_comm01 := by
    apply LinearMap.ext
    intro x
    exact (LinearMap.congr_fun he01 (C.s1 x)).trans
      (congrArg e0 (LinearMap.congr_fun C.s_comm01 x))
  s_comm12 := by
    apply LinearMap.ext
    intro x
    exact (LinearMap.congr_fun he12 (C.s2 x)).trans
      (congrArg e1 (LinearMap.congr_fun C.s_comm12 x))
  rs0 := by
    apply LinearMap.ext
    intro x
    change C.r0 (e0.symm (e0 (C.s0 x))) = x
    rw [e0.symm_apply_apply]
    exact LinearMap.congr_fun C.rs0 x
  rs1 := by
    apply LinearMap.ext
    intro x
    change C.r1 (e1.symm (e1 (C.s1 x))) = x
    rw [e1.symm_apply_apply]
    exact LinearMap.congr_fun C.rs1 x
  rs2 := by
    apply LinearMap.ext
    intro x
    change C.r2 (e2.symm (e2 (C.s2 x))) = x
    rw [e2.symm_apply_apply]
    exact LinearMap.congr_fun C.rs2 x
  sr_h0 := by
    apply LinearMap.ext
    intro x
    change e0 (C.s0 (C.r0 (e0.symm x))) +
      chainD1 N A (e1 (C.h0 (e0.symm x))) = x
    have hcomm := LinearMap.congr_fun he01 (C.h0 (e0.symm x))
    change chainD1 N A (e1 (C.h0 (e0.symm x))) = e0 (chainD1 M A (C.h0 (e0.symm x))) at hcomm
    rw [hcomm, ← map_add]
    exact (congrArg e0 (LinearMap.congr_fun C.sr_h0 (e0.symm x))).trans (e0.apply_symm_apply x)
  sr_h1 := by
    apply LinearMap.ext
    intro x
    change e1 (C.s1 (C.r1 (e1.symm x))) +
      chainD2 N A (e2 (C.h1 (e1.symm x))) + e1 (C.h0 (e0.symm (chainD1 N A x))) = x
    have hinv := LinearMap.congr_fun (CellPresentationEquiv.inverse_comm e0 e1 _ _ he01) x
    change chainD1 M A (e1.symm x) = e0.symm (chainD1 N A x) at hinv
    have hcomm := LinearMap.congr_fun he12 (C.h1 (e1.symm x))
    change chainD2 N A (e2 (C.h1 (e1.symm x))) = e1 (chainD2 M A (C.h1 (e1.symm x))) at hcomm
    rw [hcomm, ← hinv, ← map_add, ← map_add]
    exact (congrArg e1 (LinearMap.congr_fun C.sr_h1 (e1.symm x))).trans (e1.apply_symm_apply x)
  sr_h2 := by
    apply LinearMap.ext
    intro x
    change e2 (C.s2 (C.r2 (e2.symm x))) + e2 (C.h1 (e1.symm (chainD2 N A x))) = x
    have hinv := LinearMap.congr_fun (CellPresentationEquiv.inverse_comm e1 e2 _ _ he12) x
    change chainD2 M A (e2.symm x) = e1.symm (chainD2 N A x) at hinv
    rw [← hinv, ← map_add]
    exact (congrArg e2 (LinearMap.congr_fun C.sr_h2 (e2.symm x))).trans (e2.apply_symm_apply x)

/-- 同じ表示共役rの双対は、元rHomと逆表示の双対の実合成である。 -/
theorem renameFine_rHom (C : SubsetChainContraction B M A A)
    (e0 : K0 M A ≃ₗ[ℚ] K0 N A) (e1 : K1 M A ≃ₗ[ℚ] K1 N A)
    (e2 : K2 M A ≃ₗ[ℚ] K2 N A)
    (he01 : (chainD1 N A).comp e1.toLinearMap = e0.toLinearMap.comp (chainD1 M A))
    (he12 : (chainD2 N A).comp e2.toLinearMap = e1.toLinearMap.comp (chainD2 M A)) :
    (C.renameFine e0 e1 e2 he01 he12).rHom = cochainComp C.rHom
      (dualSubsetHom A A e0.symm.toLinearMap e1.symm.toLinearMap e2.symm.toLinearMap
        (CellPresentationEquiv.inverse_comm e0 e1 _ _ he01)
        (CellPresentationEquiv.inverse_comm e1 e2 _ _ he12)) := by
  apply cochain_ext
  · exact dualCellMap_comp e0.symm.toLinearMap C.r0
  · exact dualCellMap_comp e1.symm.toLinearMap C.r1
  · exact dualCellMap_comp e2.symm.toLinearMap C.r2

end SubsetChainContraction
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
