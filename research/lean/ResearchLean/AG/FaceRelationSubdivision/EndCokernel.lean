import ResearchLean.AG.AtlasDefectComposition.EndpointNaturality
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms

/-!
# 三項実H²比較の二重商

## Implementation notes

終端微分像が比較像に入るという方向仮定を持つ一般補助。
面複製への適用では同じ生成比較のcomm1と次数1恒等からこの仮定を放電する。
実H²射を別の抽象写像に置き換える方法は採らず、元のHomの像を使う。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open TwoPhase AtlasDefectComposition
universe w
variable {C D : ThreeCochainComplex.{0,w} ℚ} (f : ThreeCochainComplex.Hom C D)
variable (h : LinearMap.range D.d1 ≤ LinearMap.range f.f2)
/-- 同じ実H²比較の余核を、実次数2像によるcochain商へ送る。 -/
def endCokernelEquiv :
    ((D.C2 ⧸ LinearMap.range D.d1) ⧸ LinearMap.range (oldH2Map f)) ≃ₗ[ℚ]
      (D.C2 ⧸ LinearMap.range f.f2) :=
  (Submodule.quotEquivOfEq _ _ (range_oldH2Map f)).trans
    (Submodule.quotientQuotientEquivQuotient (LinearMap.range D.d1) (LinearMap.range f.f2) h)
/-- 二重商同定は同じcochain代表元を保つ。 -/
@[simp] theorem endCokernelEquiv_mk (z : D.C2) :
    endCokernelEquiv f h ((LinearMap.range (oldH2Map f)).mkQ ((LinearMap.range D.d1).mkQ z)) =
      (LinearMap.range f.f2).mkQ z := by
  simp only [endCokernelEquiv, LinearEquiv.trans_apply]
  rfl
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
