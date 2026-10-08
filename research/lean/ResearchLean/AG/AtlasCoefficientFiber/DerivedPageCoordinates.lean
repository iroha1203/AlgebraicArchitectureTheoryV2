import ResearchLean.AG.AtlasCoefficientFiber.FirstPageFiber
import ResearchLean.AG.AtlasCoefficientFiber.FirstPageRow
import ResearchLean.AG.AtlasCoefficientFiber.TransgressionRepresentatives

/-!
# G-135 B：独立E₂座標と原τ比較

## Implementation notes

E₂核・商とd₂は原exact couple側で先に生成済みである。座標同型は実counitの
E₁座標を商へ降ろす。補正代表は任意のRから生成し、同じF¹ coboundaryでliftの
差を消す。τをd₂の定義に使う案は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原E₁座標は同じ第一微分像をPの実第二微分像へ移す。 -/
theorem derivedHorizontal_range_coordinates :
    (LinearMap.range (secondCoupleK M A 1)).map (firstRowCoordinates2 M A).symm.toLinearMap =
      LinearMap.range (pushforwardComplex M A).d1 := by
  ext p
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    obtain ⟨v, rfl⟩ := (firstRowCoordinates1 M A).surjective x
    rw [firstRow_secondDifferential]
    change (firstRowCoordinates2 M A).symm ((firstRowCoordinates2 M A) _) ∈ _
    rw [LinearEquiv.symm_apply_apply]
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    refine ⟨secondCoupleK M A 1 (firstRowCoordinates1 M A v), ⟨_, rfl⟩, ?_⟩
    rw [firstRow_secondDifferential]
    exact LinearEquiv.symm_apply_apply _ _

/-- 独立E₂(2,0)の実商を同じ原H²Pへ移す両方向同型。 -/
def derivedHorizontalH2Equiv : DerivedHorizontalPage M A ≃ₗ[ℚ]
    (zeroExtension (pushforwardComplex M A)).homology (2 : ℤ) :=
  (Submodule.Quotient.equiv _ _ (firstRowCoordinates2 M A).symm
    (derivedHorizontal_range_coordinates M A)).trans (oldH2Equiv (pushforwardComplex M A))

/-- E₂商座標は同じ原P₂代表を保存する。 -/
@[simp] theorem derivedHorizontalH2Equiv_mk (p : (pushforwardComplex M A).C2) :
    derivedHorizontalH2Equiv M A (Submodule.Quotient.mk (firstRowCoordinates2 M A p)) =
      oldH2Equiv (pushforwardComplex M A) (Submodule.Quotient.mk p) := by
  simp only [derivedHorizontalH2Equiv, LinearEquiv.trans_apply,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  change oldH2Equiv _ (Submodule.Quotient.mk ((firstRowCoordinates2 M A).symm ((firstRowCoordinates2 M A) p))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- 原水平補正を加えた辺値は同じF¹延長との差分。 -/
theorem correctedEdgeCochain_sub (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) :
    correctedEdgeCochain M A z β - correctedEdgeCochain M A z 0 =
      (horizontalCochainLift M A β).1 := by
  apply (freeDualEquiv _).injective
  rw [map_sub, correctedEdgeCochain_dual, correctedEdgeCochain_dual]
  rw [horizontalCochainLift_dual]
  apply LinearMap.ext
  intro x
  rw [LinearMap.sub_apply, correctedEdgeFunctional_apply, correctedEdgeFunctional_apply,
    LinearMap.zero_apply, LinearMap.comp_apply, add_zero, add_sub_cancel_left]

/-- 原補正F²類は同じF¹ k値を持ち上げる。差は実F¹微分像。 -/
theorem correctedDerivedLift (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    secondCoupleI M A 2 (firstRowCoordinates2 M A (correctedPushforwardCochain M A z β hβ)) =
      firstCoupleK M A 1 (oldH1Equiv (firstGradedComplex M A) (Submodule.Quotient.mk z)) := by
  rw [firstRowCoordinates2_apply, secondCoupleI_apply, ← oldH2Equiv_natural,
    firstCoupleK_representative]
  apply congrArg (oldH2Equiv (firstFiltrationComplex M A))
  have hm : oldH2Map (secondFiltrationInclusion M A)
      (Submodule.Quotient.mk (secondFiltrationEvaluation2 M A (correctedPushforwardCochain M A z β hβ))) =
        Submodule.Quotient.mk ((secondFiltrationInclusion M A).f2
          (secondFiltrationEvaluation2 M A (correctedPushforwardCochain M A z β hβ))) :=
    oldH2Map_mk _ _
  rw [hm, Submodule.Quotient.eq]
  refine ⟨horizontalCochainLift M A β, ?_⟩
  apply Subtype.ext
  rw [Submodule.coe_sub, firstFiltrationDifferential_val, secondFiltrationInclusion_f2_val,
    secondFiltrationEvaluation2_val, firstFiberLiftDifferential_val,
    correctedPushforwardCochain_spec, ← map_sub, correctedEdgeCochain_sub]

/-- 原R補正代表の独立E₂核座標は同じgr⁰代表。 -/
theorem derivedFiberREquiv_corrected (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    ((derivedFiberREquiv M A).symm (correctedFiberClass M A z β hβ)).1 =
      oldH1Equiv (firstGradedComplex M A) (Submodule.Quotient.mk z) := by
  apply (firstGradedHomologyFiberEquiv M A).injective
  rw [firstGradedHomologyFiberEquiv_mk]
  rw [← derivedFiberREquiv_val, LinearEquiv.apply_symm_apply]
  apply (phiCohomologyVerticalDualEquiv M A).injective
  rw [LinearEquiv.apply_symm_apply, ← fiberRRawEquiv_val, correctedFiberClass_raw]

/-- 独立exact couple d₂は全R・全Aで原τと同じ符号・同じ商類を返す。 -/
theorem derivedSecondDifferential_tau (r : R M A) :
    derivedHorizontalH2Equiv M A
      (derivedSecondDifferential M A ((derivedFiberREquiv M A).symm r)) = connectingTau M A r := by
  obtain ⟨z, β, hβ, rfl⟩ := fiberClass_has_correction M A r
  rw [derivedSecondDifferential_apply M A _
    (firstRowCoordinates2 M A (correctedPushforwardCochain M A z β hβ)) (by
      rw [derivedFiberREquiv_corrected]
      exact correctedDerivedLift M A z β hβ), derivedHorizontalH2Equiv_mk,
    connectingTau_correctedFiberClass]

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.derivedHorizontal_range_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.derivedHorizontalH2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.derivedHorizontalH2Equiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeCochain_sub
#print axioms AAT.AG.AtlasCoefficientFiber.correctedDerivedLift
#print axioms AAT.AG.AtlasCoefficientFiber.derivedFiberREquiv_corrected
#print axioms AAT.AG.AtlasCoefficientFiber.derivedSecondDifferential_tau
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
