import ResearchLean.AG.AtlasCoefficientFiber.LowExactCouple
import ResearchLean.AG.AtlasCoefficientFiber.ThreeShortExactConnecting
import ResearchLean.AG.AtlasCoefficientFiber.CochainRepresentatives
import ResearchLean.AG.AtlasDefectComposition.EndpointNaturality

/-!
# G-135 B：E₁のfiber項と同じ原κ*微分

## Implementation notes

E₁の二つの項は実gradedの標準homologyから作り、原代表評価を保存する双対同型を
通して全Φ H¹とker Bの双対へ移す。d₁は実j∘kから生成済みであり、標準δ_eqで
原zDを読むことでκ*との一致を証明する。κ*をd₁の定義に使う案は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- E₁(0,1)の実標準homologyを同じ全Φ H¹へ移す。 -/
def firstGradedHomologyFiberEquiv : (zeroExtension (firstGradedComplex M A)).homology (1 : ℤ) ≃ₗ[ℚ]
    ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) :=
  (oldH1Equiv (firstGradedComplex M A)).symm.trans
    ((chainHomologyDualEquiv (verticalEdgeBoundary M A) (verticalBoundary M A)
      (verticalEdgeBoundary_comp_verticalBoundary M A)).trans
        (phiCohomologyVerticalDualEquiv M A).symm)

/-- 全Φ座標は原閉cochainの同じ垂直homology評価を読む。 -/
theorem firstGradedHomologyFiberEquiv_mk (z : VerticalCocycles M A) :
    firstGradedHomologyFiberEquiv M A
      (oldH1Equiv (firstGradedComplex M A) (Submodule.Quotient.mk z)) =
      (phiCohomologyVerticalDualEquiv M A).symm (verticalCocycleClass M A z) := by
  simp only [firstGradedHomologyFiberEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  congr 1

/-- E₁(1,1)の実標準homologyを同じker B双対へ移す。 -/
def secondGradedHomologyDualEquiv : (zeroExtension (secondGradedComplex M A)).homology (2 : ℤ) ≃ₗ[ℚ]
    Module.Dual ℚ (mixedCycles M A) :=
  (oldH2Equiv (secondGradedComplex M A)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (LinearMap.range_dualMap_eq_dualAnnihilator_ker
      (mixedHorizontalBoundary M A))).trans (Subspace.quotAnnihilatorEquiv (mixedCycles M A)))

/-- 第二graded双対同型は原混在閉路上の同じ評価を保つ。 -/
@[simp] theorem secondGradedHomologyDualEquiv_mk
    (γ : Module.Dual ℚ (MixedFace M A →₀ ℚ)) (y : mixedCycles M A) :
    secondGradedHomologyDualEquiv M A
      (oldH2Equiv (secondGradedComplex M A) (Submodule.Quotient.mk γ)) y = γ y.1 := by
  simp only [secondGradedHomologyDualEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Submodule.quotEquivOfEq_mk, Subspace.quotAnnihilatorEquiv_apply]
  rfl

/-- 原垂直閉cochainを水平補正零で細cochainへ持ち上げると、同じ垂直値へ戻る。 -/
theorem verticalRestriction1_corrected (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) :
    verticalRestriction1 M A (correctedEdgeCochain M A z β) = z := by
  apply LinearMap.ext
  intro x
  rw [verticalRestriction1_apply, correctedEdgeCochain_dual, correctedEdgeFunctional_vertical]

/-- 原zの水平補正零持ち上げの微分はF¹に入る。 -/
def firstFiberLiftDifferential (z : VerticalCocycles M A) : (firstFiltrationComplex M A).C2 :=
  ⟨(Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1 (correctedEdgeCochain M A z.1 0), by
    rw [LinearMap.mem_ker, verticalRestriction_comm1, verticalRestriction1_corrected, z.2]⟩

/-- 原F¹ lift微分は同じ細cochain微分の値。 -/
@[simp] theorem firstFiberLiftDifferential_val (z : VerticalCocycles M A) :
    (firstFiberLiftDifferential M A z).1 =
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1 (correctedEdgeCochain M A z.1 0) := rfl

/-- 同じ第一graded標準δは原lift微分のF¹類を返す。 -/
theorem firstCoupleK_representative (z : VerticalCocycles M A) :
    firstCoupleK M A 1 (oldH1Equiv (firstGradedComplex M A) (Submodule.Quotient.mk z)) =
      oldH2Equiv (firstFiltrationComplex M A) (Submodule.Quotient.mk (firstFiberLiftDifferential M A z)) := by
  rw [firstCoupleK_apply]
  exact threeShortExact_connecting_representative
    (firstFiltrationInclusion M A) (firstGradedProjection M A)
    (firstGraded_standard_zero M A) (firstGraded_shortExact M A) z
    (correctedEdgeCochain M A z.1 0) (firstFiberLiftDifferential M A z)
    (verticalRestriction1_corrected M A z.1 0) rfl

/-- そのF¹微分を原混在面へ制限すると同じzDになる。 -/
theorem mixedRestriction2_firstFiberLift (z : VerticalCocycles M A) :
    mixedRestriction2 M A (firstFiberLiftDifferential M A z) =
      (mixedVerticalBoundary M A).dualMap z.1 := by
  apply LinearMap.ext
  intro y
  rw [mixedRestriction2_apply, firstFiberLiftDifferential_val, correctedEdgeCochain_d1_mixed,
    LinearMap.zero_apply, add_zero]
  rfl

/-- 原j∘k微分の代表は同じzDのgr¹類。 -/
theorem firstPageDifferential_representative (z : VerticalCocycles M A) :
    firstPageDifferential M A 1 (oldH1Equiv (firstGradedComplex M A) (Submodule.Quotient.mk z)) =
      oldH2Equiv (secondGradedComplex M A) (Submodule.Quotient.mk ((mixedVerticalBoundary M A).dualMap z.1)) := by
  rw [firstPageDifferential_apply, firstCoupleK_representative]
  change secondCoupleJ M A 2 _ = _
  rw [secondCoupleJ_apply, ← oldH2Equiv_natural]
  have hm : oldH2Map (secondGradedProjection M A) (Submodule.Quotient.mk (firstFiberLiftDifferential M A z)) =
      Submodule.Quotient.mk ((secondGradedProjection M A).f2 (firstFiberLiftDifferential M A z)) :=
    oldH2Map_mk (secondGradedProjection M A) (firstFiberLiftDifferential M A z)
  rw [hm, secondGradedProjection_f2, mixedRestriction2_firstFiberLift]

/-- 実d₁を原Φ/ker B座標へ移すとκ*そのもの。全代表で一致する。 -/
theorem firstPageDifferential_kappaStar
    (x : (zeroExtension (firstGradedComplex M A)).homology (1 : ℤ)) :
    secondGradedHomologyDualEquiv M A (firstPageDifferential M A 1 x) =
      kappaStar M A (firstGradedHomologyFiberEquiv M A x) := by
  obtain ⟨q, rfl⟩ := (oldH1Equiv (firstGradedComplex M A)).surjective x
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
    rw [firstPageDifferential_representative, firstGradedHomologyFiberEquiv_mk]
    apply LinearMap.ext
    intro y
    rw [secondGradedHomologyDualEquiv_mk, kappaStar_raw, LinearMap.comp_apply]
    change z.1 (mixedVerticalBoundary M A y.1) =
      (phiCohomologyVerticalDualEquiv M A
        ((phiCohomologyVerticalDualEquiv M A).symm (verticalCocycleClass M A z)))
          (rawKappa M A y)
    rw [LinearEquiv.apply_symm_apply]
    exact (verticalCocycleClass_kappa M A z y).symm

/-- 独立E₂(0,1)核を同じ原κ*核Rへ移す両方向同型。 -/
def derivedFiberREquiv : DerivedFiberPage M A ≃ₗ[ℚ] R M A where
  toFun x := ⟨firstGradedHomologyFiberEquiv M A x.1, by
    rw [LinearMap.mem_ker, ← firstPageDifferential_kappaStar, x.2, map_zero]⟩
  invFun r := ⟨(firstGradedHomologyFiberEquiv M A).symm r.1, by
    apply (secondGradedHomologyDualEquiv M A).injective
    rw [firstPageDifferential_kappaStar, LinearEquiv.apply_symm_apply, r.2, map_zero]⟩
  left_inv x := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ _
  right_inv r := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext; exact map_smul _ _ _

/-- 独立derived核のR座標は同じ全Φ座標。 -/
@[simp] theorem derivedFiberREquiv_val (x : DerivedFiberPage M A) :
    (derivedFiberREquiv M A x).1 = firstGradedHomologyFiberEquiv M A x.1 := rfl

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedHomologyFiberEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedHomologyFiberEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedHomologyDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedHomologyDualEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction1_corrected
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiberLiftDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiberLiftDifferential_val
#print axioms AAT.AG.AtlasCoefficientFiber.firstCoupleK_representative
#print axioms AAT.AG.AtlasCoefficientFiber.mixedRestriction2_firstFiberLift
#print axioms AAT.AG.AtlasCoefficientFiber.firstPageDifferential_representative
#print axioms AAT.AG.AtlasCoefficientFiber.firstPageDifferential_kappaStar
#print axioms AAT.AG.AtlasCoefficientFiber.derivedFiberREquiv
#print axioms AAT.AG.AtlasCoefficientFiber.derivedFiberREquiv_val
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
