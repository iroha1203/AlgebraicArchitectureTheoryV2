import ResearchLean.AG.FaceRelationSubdivision.ElementaryDiagnostics
import Formal.Util.AssertStandardAxioms

/-!
# 保持 loop 上での実細分 period

## Implementation notes

一般橋渡しでは旧商の period 評価を方向仮定とする。
指定例ではその仮定を原始微分と実商から放電し、同じ s の単一基底像で細 period を読む。
細側の期待 period を比較入力に置く方式は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q) (l : LawValueLabel laws)
/-- 同じ実比較の生成逆から読む細 period。 -/
def subdivisionFinePeriod (P : (N.lawValueBlockComplex laws ha l).H1 ≃ₗ[ℚ] ℚ) :=
  (EdgeSubdivision.blockOldH1Iso N e laws ha l).toLinearEquiv.symm.trans P
/-- 保持旧辺の同じ単一基底像から生成される fine block 座標。 -/
def retainedBlockCoordinate (k : N.EdgeBlockCoordinate laws ha l) (hk : k.val.cell≠e) :=
  (EdgeSubdivision.s1 N e).lawBlockCoordinate laws ha l k (Sum.inl ⟨k.val.cell,hk⟩)
    (by rw [EdgeSubdivision.s1_retained_basis N e ⟨k.val.cell,hk⟩]; simp)
omit [Fintype Source] in
/-- 同じ生成座標は保持辺の原始名を持つ。 -/
@[simp] theorem retainedBlockCoordinate_cell (k) (hk) :
    (retainedBlockCoordinate N e laws ha l k hk).val.cell=Sum.inl ⟨k.val.cell,hk⟩ :=
  SupportedBasisMap.lawBlockCoordinate_cell _ _ _ _ _ _ _
/-- 旧 period が k 値を読むなら、細 period は同じ実代表の保持 k 値を読む。 -/
theorem subdivisionFinePeriod_mk (P : (N.lawValueBlockComplex laws ha l).H1 ≃ₗ[ℚ] ℚ)
    (k : N.EdgeBlockCoordinate laws ha l) (hk : k.val.cell≠e)
    (hp : ∀ z : LinearMap.ker (N.lawValueBlockComplex laws ha l).d1,
      P ((LinearMap.range (N.lawValueBlockComplex laws ha l).boundaryToCycles).mkQ z)=z.val k)
    (z : LinearMap.ker ((EdgeSubdivision.supported N e).lawValueBlockComplex laws ha l).d1) :
    subdivisionFinePeriod N e laws ha l P
      ((LinearMap.range ((EdgeSubdivision.supported N e).lawValueBlockComplex laws ha l).boundaryToCycles).mkQ z)=
        z.val (retainedBlockCoordinate N e laws ha l k hk) := by
  have hi : ∀ x, (EdgeSubdivision.blockOldH1Iso N e laws ha l).toLinearEquiv.symm x=
      (EdgeSubdivision.blockS N e laws ha l).h1Map x := by
    intro x
    exact congrArg (fun f => f x) (EdgeSubdivision.blockOldH1Iso_inv N e laws ha l)
  rw [subdivisionFinePeriod,LinearEquiv.trans_apply,hi,ThreeCochainComplex.Hom.h1Map_mk,hp,
    ThreeCochainComplex.Hom.cyclesMap_apply,EdgeSubdivision.blockS_f1]
  exact SupportedBasisMap.lawBlockDual_apply_single _ _ _ _ _ _ _
    (EdgeSubdivision.s1_retained_basis N e ⟨k.val.cell,hk⟩)
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
