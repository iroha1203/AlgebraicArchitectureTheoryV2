import ResearchLean.AG.FaceRelationSubdivision.WitnessOnePeriodMaps
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import Formal.Util.AssertStandardAxioms
/-!
# W1 の同じ実核と追加余核類

## Implementation notes

原始 period で得た実可換式を使って実比較の核・余核を運ぶ。
第二 period の商を具体的な e2 単独類で評価し、次元一致だけの代替を採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
/-- 評価の結果に用いる座標包含。 -/
def periodInjection : ℚ →ₗ[ℚ] (ℚ × ℚ) where
  toFun x := (x,0)
  map_add' _ _ := by apply Prod.ext <;> simp
  map_smul' _ _ := by apply Prod.ext <;> simp
/-- 座標包含の公開式。 -/
@[simp] theorem periodInjection_apply (x : ℚ) : periodInjection x=(x,0) := rfl
/-- 追加 period を読む座標射影。 -/
def extraProjection : (ℚ × ℚ) →ₗ[ℚ] ℚ where
  toFun x := x.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 追加 period 射影の公開式。 -/
@[simp] theorem extraProjection_apply (x : ℚ × ℚ) : extraProjection x=x.2 := rfl
/-- 原始比較の座標包含は単射。 -/
theorem periodInjection_injective : Function.Injective periodInjection := fun _ _ h => congrArg Prod.fst h
/-- 追加 period 零の対は座標包含の実像と一致する。 -/
theorem extraProjection_kernel : LinearMap.ker extraProjection = LinearMap.range periodInjection := by
  ext x
  constructor
  · intro hx
    exact ⟨x.1,Prod.ext rfl hx.symm⟩
  · rintro ⟨a,rfl⟩
    rfl
/-- 追加 period は e2 単独座標から全射。 -/
theorem extraProjection_surjective : Function.Surjective extraProjection := fun a => ⟨(0,a),rfl⟩
/-- 評価された包含の余核を追加 period で同定する。 -/
def injectionCokernel : ((ℚ × ℚ) ⧸ LinearMap.range periodInjection) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ extraProjection_kernel.symm).trans
    (extraProjection.quotKerEquivOfSurjective extraProjection_surjective)
/-- 座標余核の代表元は第二 period を読む。 -/
@[simp] theorem injectionCokernel_mk (x : ℚ × ℚ) : injectionCokernel ((LinearMap.range periodInjection).mkQ x)=x.2 := rfl
/-- 同じ実 minus block 比較の余核は追加 period により ℚ。 -/
def minusBlockCokernel (l : LawValueLabel laws) :
    ((minus.lawValueBlockComplex laws fineAdequate l).H1 ⧸ LinearMap.range (minusBlockHom l).h1Map) ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.cokernelEquiv (minusBlockHom l).h1Map periodInjection
    (oldBlockPeriod l) (minusBlockPeriod l) (minus_block_injection l)).trans injectionCokernel
/-- 実 minus 余核の代表元は同じ第二 period を読む。 -/
@[simp] theorem minusBlockCokernel_mk (l : LawValueLabel laws) (x : (minus.lawValueBlockComplex laws fineAdequate l).H1) :
    minusBlockCokernel l ((LinearMap.range (minusBlockHom l).h1Map).mkQ x)=(minusBlockPeriod l x).2 := by
  simp only [minusBlockCokernel,LinearEquiv.trans_apply,LinearConjugation.cokernelEquiv_mk,injectionCokernel_mk]
/-- 同じ e2 単独1は実余核で非零。 -/
theorem minus_extra_cokernel_nonzero (l : LawValueLabel laws) :
    (LinearMap.range (minusBlockHom l).h1Map).mkQ (minusBlockExtra l) ≠ 0 := by
  intro hz
  have he := congrArg (minusBlockCokernel l) hz
  rw [minusBlockCokernel_mk,minusBlockExtra_period,map_zero] at he
  exact one_ne_zero he
/-- 同じ実 plus block 比較は単射。 -/
theorem plus_block_injective (l : LawValueLabel laws) : Function.Injective (plusBlockHom l).h1Map := by
  intro x y h
  apply (oldBlockPeriod l).injective
  exact (plus_block_identity l x).symm.trans ((congrArg (plusBlockPeriod l) h).trans (plus_block_identity l y))
/-- 同じ実 plus block 比較は全射。 -/
theorem plus_block_surjective (l : LawValueLabel laws) : Function.Surjective (plusBlockHom l).h1Map := by
  intro y
  refine ⟨(oldBlockPeriod l).symm (plusBlockPeriod l y),?_⟩
  apply (plusBlockPeriod l).injective
  rw [plus_block_identity,LinearEquiv.apply_symm_apply]
/-- 同じ実 minus block 比較は単射。 -/
theorem minus_block_injective (l : LawValueLabel laws) : Function.Injective (minusBlockHom l).h1Map := by
  intro x y h
  apply (oldBlockPeriod l).injective
  exact congrArg Prod.fst ((minus_block_injection l x).symm.trans
    ((congrArg (minusBlockPeriod l) h).trans (minus_block_injection l y)))
/-- plus の実核は零加群。 -/
theorem plus_kernel_subsingleton (l : LawValueLabel laws) : Subsingleton (LinearMap.ker (plusBlockHom l).h1Map) := by
  constructor
  intro x y
  apply Subtype.ext
  exact plus_block_injective l (x.property.trans y.property.symm)
/-- plus の実余核も零加群。 -/
theorem plus_cokernel_subsingleton (l : LawValueLabel laws) :
    Subsingleton ((plus.lawValueBlockComplex laws fineAdequate l).H1 ⧸ LinearMap.range (plusBlockHom l).h1Map) := by
  rw [LinearMap.range_eq_top.mpr (plus_block_surjective l)]
  infer_instance
/-- minus の実核も零加群。 -/
theorem minus_kernel_subsingleton (l : LawValueLabel laws) : Subsingleton (LinearMap.ker (minusBlockHom l).h1Map) := by
  constructor
  intro x y
  apply Subtype.ext
  exact minus_block_injective l (x.property.trans y.property.symm)
end AAT.AG.FaceRelationSubdivision.WitnessOne
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessOne
