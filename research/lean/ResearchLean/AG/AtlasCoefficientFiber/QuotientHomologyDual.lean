import ResearchLean.AG.AtlasCoefficientFiber.QuotientHorizontalHomology
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# G-135 B：原商二次閉路と実P二次homologyの双対

同じε双対と原商微分の核を用いる。

## Implementation notes

実εとliteral K′/Lの双対同型を使い、P₂の代表を実商閉路に評価する。
次にその核が原Pのd¹像であることから商同型を生成する。期待するH²のrankを
入力する案は、代表の全射性と核の逆包含を放電しないため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じ実εのP₂汎関数を原商二次閉路へ制限する。 -/
def pushforwardSecondCycleEvaluation : (pushforwardComplex M A).C2 →ₗ[ℚ]
    Module.Dual ℚ (QuotientSecondCycles M A) :=
  (QuotientSecondCycles M A).dualRestrict.comp (evaluationQuotientDual2 M A).toLinearMap

/-- 原商二次閉路での値は同じ実ε双対。 -/
@[simp] theorem pushforwardSecondCycleEvaluation_apply (p : (pushforwardComplex M A).C2)
    (x : QuotientSecondCycles M A) :
    pushforwardSecondCycleEvaluation M A p x = evaluationQuotientDual2 M A p x.1 := rfl

/-- 体上の制限全射性と実ε同型から全二次閉路汎関数を生成する。 -/
theorem pushforwardSecondCycleEvaluation_surjective :
    Function.Surjective (pushforwardSecondCycleEvaluation M A) :=
  (Subspace.dualRestrict_surjective (W := QuotientSecondCycles M A)).comp
    (evaluationQuotientDual2 M A).surjective

/-- 原商二次閉路に消える実P₂cochainは、同じ実P微分の像である。 -/
theorem pushforwardSecondCycleEvaluation_ker :
    LinearMap.ker (pushforwardSecondCycleEvaluation M A) =
      LinearMap.range (pushforwardComplex M A).d1 := by
  ext p
  constructor
  · intro hp
    have ha : evaluationQuotientDual2 M A p ∈
        (LinearMap.ker (quotientBoundary2 M A)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      exact LinearMap.congr_fun hp (⟨x, hx⟩ : QuotientSecondCycles M A)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ha
    obtain ⟨w, hw⟩ := ha
    obtain ⟨v, hv⟩ := (evaluationQuotientDual1 M A).surjective w
    refine ⟨v, (evaluationQuotientDual2 M A).injective ?_⟩
    rw [evaluationQuotientDual_comm1, hv]
    exact hw
  · rintro ⟨v, rfl⟩
    apply LinearMap.ext
    intro x
    rw [pushforwardSecondCycleEvaluation_apply, evaluationQuotientDual_comm1,
      quotientDualComplex_d1_apply, show quotientBoundary2 M A x.1 = 0 from x.2,
      map_zero, LinearMap.zero_apply]

/-- 実P₂の微分像商と同じ原商二次閉路双対の両方向同型。 -/
def pushforwardSecondHomologyDualEquiv :
    ((pushforwardComplex M A).C2 ⧸ LinearMap.range (pushforwardComplex M A).d1) ≃ₗ[ℚ]
      Module.Dual ℚ (QuotientSecondCycles M A) :=
  (Submodule.quotEquivOfEq _ _ (pushforwardSecondCycleEvaluation_ker M A).symm).trans
    ((pushforwardSecondCycleEvaluation M A).quotKerEquivOfSurjective
      (pushforwardSecondCycleEvaluation_surjective M A))

/-- 二次homology双対同型は同じ実ε代表の評価を返す。 -/
@[simp] theorem pushforwardSecondHomologyDualEquiv_mk (p : (pushforwardComplex M A).C2)
    (x : QuotientSecondCycles M A) :
    pushforwardSecondHomologyDualEquiv M A (Submodule.Quotient.mk p) x =
      evaluationQuotientDual2 M A p x.1 := rfl

/-- 標準H²Pを、原水平商閉路の双対へ同定する。 -/
def pushforwardStandardH2HorizontalDualEquiv :
    (zeroExtension (pushforwardComplex M A)).homology (2 : ℤ) ≃ₗ[ℚ]
      Module.Dual ℚ (HorizontalFaceCycles M A) :=
  (oldH2Equiv (pushforwardComplex M A)).symm.trans
    ((pushforwardSecondHomologyDualEquiv M A).trans
      (quotientSecondCyclesEquiv M A).symm.dualMap)

/-- 標準H²代表の水平閉路での値は同じ元商代表へのε評価。 -/
@[simp] theorem pushforwardStandardH2HorizontalDualEquiv_mk (p : (pushforwardComplex M A).C2)
    (x : HorizontalFaceCycles M A) :
    pushforwardStandardH2HorizontalDualEquiv M A
      (oldH2Equiv (pushforwardComplex M A) (Submodule.Quotient.mk p)) x =
        evaluationQuotientDual2 M A p ((quotientSecondCyclesEquiv M A).symm x).1 := by
  simp only [pushforwardStandardH2HorizontalDualEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.dualMap_apply,
    pushforwardSecondHomologyDualEquiv_mk]

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardSecondCycleEvaluation
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardSecondCycleEvaluation_apply
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardSecondCycleEvaluation_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardSecondCycleEvaluation_ker
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardSecondHomologyDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardSecondHomologyDualEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardStandardH2HorizontalDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardStandardH2HorizontalDualEquiv_mk
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
