import ResearchLean.AG.AtlasCoefficientFiber.TransgressionRepresentatives
import ResearchLean.AG.AtlasCoefficientFiber.ConnectingEvaluation
import ResearchLean.AG.AtlasCoefficientFiber.QuotientHomologyDual

/-!
# G-135 B：同じ原商の連結写像とτの双対同定

同じε代表の評価とBy=Hxの実補正から、標準δを鎖連結写像へ照合する。

## Implementation notes

Rと原垂直関係商の双対は既存のκ余核同型と双対写像の合成で接続する。
τの値を先にβHとして定義する案は、標準短完全列のδとの一致を失うため採用しない。
全Rの原補正生成を使い、標準δの代表評価から同じ鎖連結写像の双対性を証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 指定Rを同じ原垂直関係商の双対へ移す。 -/
def fiberRelationsDualEquiv : R M A ≃ₗ[ℚ]
    Module.Dual ℚ (verticalCycles M A ⧸ verticalRelations M A) :=
  (fiberRRawEquiv M A).trans ((rawKappaCokernelDualEquiv M A).symm.trans
    (rawKappaCokernelEquiv M A).symm.dualMap)

/-- 指定Rの関係商評価は同じ原垂直homology値。 -/
@[simp] theorem fiberRelationsDualEquiv_mk (r : R M A) (x : verticalCycles M A) :
    fiberRelationsDualEquiv M A r (Submodule.Quotient.mk x) =
      (fiberRRawEquiv M A r).1 (Submodule.Quotient.mk x) := by
  change (rawKappaCokernelDualEquiv M A).symm (fiberRRawEquiv M A r)
    ((rawKappaCokernelEquiv M A).symm (Submodule.Quotient.mk x)) = _
  have hx : (rawKappaCokernelEquiv M A).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.Quotient.mk x) := by
    apply (rawKappaCokernelEquiv M A).injective
    rw [LinearEquiv.apply_symm_apply, rawKappaCokernelEquiv_mk]
  rw [hx]
  have hh := rawKappaCokernelDualEquiv_apply M A
    ((rawKappaCokernelDualEquiv M A).symm (fiberRRawEquiv M A r)) (Submodule.Quotient.mk x)
  simpa only [LinearEquiv.apply_symm_apply] using hh.symm

/-- 原補正付き代表の関係商双対座標は実降下汎関数。 -/
theorem fiberRelationsDualEquiv_corrected (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    fiberRelationsDualEquiv M A (correctedFiberClass M A z β hβ) =
      correctedRelationsFunctional M A z β hβ := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [fiberRelationsDualEquiv_mk, correctedFiberClass_raw, verticalCocycleClass_mk,
      correctedRelationsFunctional_mk]

/-- 同じ標準δ代表は原水平閉路上でβHを評価する。 -/
theorem connectingTau_horizontal_evaluation (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (x : HorizontalFaceCycles M A) :
    pushforwardStandardH2HorizontalDualEquiv M A
      (connectingTau M A (correctedFiberClass M A z β hβ)) x =
        β (horizontalFaceBoundary M A x.1) := by
  rw [connectingTau_correctedFiberClass, pushforwardStandardH2HorizontalDualEquiv_mk,
    quotientSecondCyclesEquiv_symm_val, quotientFaceEquiv_symm_apply]
  change evaluationQuotientDual2 M A (correctedPushforwardCochain M A z β hβ)
    ((degenerateL2 M A).mkQ (horizontalFaceInclusion M A x.1)) = _
  rw [evaluationQuotientDual2_mk, correctedPushforwardCochain_spec,
    correctedEdgeCochain_d1_horizontal]

/-- 指定R上の標準τは、原By=Hxから作る[-Dy]写像の双対そのもの。 -/
theorem connectingTau_chain_duality (r : R M A) :
    pushforwardStandardH2HorizontalDualEquiv M A (connectingTau M A r) =
      (horizontalChainConnecting M A).dualMap (fiberRelationsDualEquiv M A r) := by
  obtain ⟨z, β, hβ, rfl⟩ := fiberClass_has_correction M A r
  apply LinearMap.ext
  intro x
  rw [connectingTau_horizontal_evaluation, LinearMap.dualMap_apply,
    fiberRelationsDualEquiv_corrected, correctedRelationsFunctional_horizontalChainConnecting]

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.fiberRelationsDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.fiberRelationsDualEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.fiberRelationsDualEquiv_corrected
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_horizontal_evaluation
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_chain_duality
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
