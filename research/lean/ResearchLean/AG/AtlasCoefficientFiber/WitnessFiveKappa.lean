import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveFiber
import ResearchLean.AG.AtlasCoefficientFiber.FiveTermSequence

/-!
# G-135 W5：同原混在閉路からのκ・κ*の両逆

## Implementation notes

原Dの可逆性と原a/B/V零からrawκの単射と全射を証明する。
期待κ同型を引数へ移す案は混在適合の構成を未放電にするため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open WitnessCommon WitnessFullSupport

/-- 原rawκの単射性はD両逆と実V零から生成する。 -/
theorem rawKappa_injective (A : Set Bool) : Function.Injective (rawKappa M A) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro y hy
  obtain ⟨v,hv⟩ := (rawKappa_eq_zero_iff M A y).mp hy
  apply Subtype.ext
  change y.1 = 0
  apply (mixedVerticalBoundary_bijective A).1
  rw [map_zero,← hv,verticalBoundary_zero,LinearMap.zero_apply]
/-- 原rawκの全射性は同D逆像を実B核に持ち上げて生成する。 -/
theorem rawKappa_surjective (A : Set Bool) : Function.Surjective (rawKappa M A) := by
  intro t
  obtain ⟨z,rfl⟩ := (LinearMap.range (verticalBoundaryToCycles M A)).mkQ_surjective t
  obtain ⟨y,hy⟩ := (mixedVerticalBoundary_bijective A).2 z.1
  let yc : mixedCycles M A := ⟨y,by rw [LinearMap.mem_ker,mixedHorizontalBoundary_zero]; rfl⟩
  refine ⟨yc,?_⟩
  rw [rawKappa_apply]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rw [mixedCycleToVertical_val]
  exact hy
/-- 同原rawκの両逆は全Aで証明される。 -/
def rawKappaEquiv (A : Set Bool) : mixedCycles M A ≃ₗ[ℚ] VerticalHomology M A :=
  LinearEquiv.ofBijective (rawKappa M A) ⟨rawKappa_injective A,rawKappa_surjective A⟩
/-- 両逆の実射は元rawκそのもの。 -/
@[simp] theorem rawKappaEquiv_toLinearMap (A : Set Bool) : (rawKappaEquiv A).toLinearMap = rawKappa M A := rfl
/-- 設計の全Φ chain表示の実κも同じ両逆を持つ。 -/
def kappaEquiv (A : Set Bool) : mixedCycles M A ≃ₗ[ℚ] ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) :=
  (rawKappaEquiv A).trans (verticalHomologyPhiEquiv M A)
/-- 全Φ表示での両逆は独立原κと同じ射。 -/
@[simp] theorem kappaEquiv_toLinearMap (A : Set Bool) : (kappaEquiv A).toLinearMap = kappa M A := rfl
/-- 同κの双対と原Φ双対から実κ*の両逆を生成。 -/
def kappaStarEquiv (A : Set Bool) :
    ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) ≃ₗ[ℚ] Module.Dual ℚ (mixedCycles M A) :=
  (phiCohomologyVerticalDualEquiv M A).trans (rawKappaEquiv A).dualMap
/-- 出力両逆はliteralκ*の実写像を保持する。 -/
@[simp] theorem kappaStarEquiv_toLinearMap (A : Set Bool) : (kappaStarEquiv A).toLinearMap = kappaStar M A :=
  (kappaStar_raw M A).symm
/-- literalRの零性は実κ*の単射性から生成する。 -/
theorem R_zero (A : Set Bool) : R M A = ⊥ := by
  rw [fiberR_eq_ker,← kappaStarEquiv_toLinearMap]
  exact LinearMap.ker_eq_bot.mpr (kappaStarEquiv A).injective
/-- 同literalRは全Aで零空間。全Φそのものは非空Aで零ではない。 -/
theorem R_subsingleton (A : Set Bool) : Subsingleton (R M A) := by
  rw [R_zero]; infer_instance
/-- 同じ標準連結射τはliteralR零から全Aで零。 -/
theorem tau_zero (A : Set Bool) : connectingTau M A = 0 := by
  letI := R_subsingleton A
  apply LinearMap.ext; intro x
  rw [Subsingleton.elim x 0,map_zero]; rfl
/-- 正しいfiber列の元評価H¹は全Aで可逆。 -/
theorem evaluation_bijective (A : Set Bool) : Function.Bijective (evaluationH1 M A) := by
  constructor
  · exact evaluationH1_injective M A
  · intro y
    apply (fiveTerm_exact_at_fineH1 M A y).mp
    letI := R_subsingleton A
    exact Subsingleton.elim _ _

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.rawKappa_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.rawKappa_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.rawKappaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.rawKappaEquiv_toLinearMap
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kappaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kappaEquiv_toLinearMap
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kappaStarEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kappaStarEquiv_toLinearMap
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.R_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.evaluation_bijective
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
