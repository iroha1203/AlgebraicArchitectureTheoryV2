import ResearchLean.AG.AtlasCoefficientFiber.LowExactCouple
import ResearchLean.AG.AtlasCoefficientFiber.ThreeShortExactConnecting
import ResearchLean.AG.AtlasDefectComposition.EndpointNaturality

/-!
# G-135 B：E₁ q=0行の実Kan P座標

## Implementation notes

座標射は独立生成済みPの実counit評価から作る。各逆像は原annihilatorと
counit像の一致から生成する。任意のP行を後から定義する案は採用しない。
標準graded homologyへの接続は同じ核・商・零延長同型で行う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- P₀評価は原垂直辺微分双対の核に入る。 -/
def firstRowZeroMap : (pushforwardComplex M A).C0 →ₗ[ℚ] LinearMap.ker (firstGradedComplex M A).d0 :=
  ((freeDualEquiv _).toLinearMap.comp (evaluation0 M A)).codRestrict _ (fun p => by
    apply LinearMap.ext
    intro x
    have hx : chainD1 Nf (comparisonFactor qc qf h ⁻¹' A) (verticalEdgeInclusion M A x) ∈ degenerateL0 M A :=
      (mem_degenerateL0 M A _).mpr ⟨x, rfl⟩
    exact LinearMap.congr_fun (restriction0_evaluation0 M A p) ⟨_, hx⟩)

/-- P₀座標は同じ原chart評価値。 -/
@[simp] theorem firstRowZeroMap_val (p : (pushforwardComplex M A).C0) :
    (firstRowZeroMap M A p).1 = freeDualEquiv _ (evaluation0 M A p) := rfl

/-- 原chart評価の単射性がP₀座標の単射性を与える。 -/
theorem firstRowZeroMap_injective : Function.Injective (firstRowZeroMap M A) := by
  intro p q hpq
  apply evaluation0_injective M A
  apply (freeDualEquiv _).injective
  exact congrArg (fun z : LinearMap.ker (firstGradedComplex M A).d0 => z.1) hpq

/-- 原L₀像条件とcounit像の一致がP₀座標の全射性を生成する。 -/
theorem firstRowZeroMap_surjective : Function.Surjective (firstRowZeroMap M A) := by
  intro z
  let w := (freeDualEquiv _).symm z.1
  have hw : restriction0 M A w = 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, hv⟩ := (mem_degenerateL0 M A x.1).mp x.2
    rw [restriction0_apply, LinearEquiv.apply_symm_apply, ← hv]
    exact LinearMap.congr_fun z.2 v
  have hi : w ∈ LinearMap.range (evaluation0 M A) := by
    rw [evaluation0_range_eq_ker]
    exact hw
  obtain ⟨p, hp⟩ := hi
  refine ⟨p, ?_⟩
  apply Subtype.ext
  rw [firstRowZeroMap_val, hp]
  exact LinearEquiv.apply_symm_apply _ _

/-- E₁(0,0)の元核を実P₀へ同定するcounit座標。 -/
def firstRowZeroEquiv : (pushforwardComplex M A).C0 ≃ₗ[ℚ] LinearMap.ker (firstGradedComplex M A).d0 :=
  LinearEquiv.ofBijective (firstRowZeroMap M A) ⟨firstRowZeroMap_injective M A, firstRowZeroMap_surjective M A⟩

/-- P₁評価は原垂直辺をannihilateしF¹に入る。 -/
def firstFiltrationEvaluation1 : (pushforwardComplex M A).C1 →ₗ[ℚ] (firstFiltrationComplex M A).C1 :=
  (evaluation1 M A).codRestrict _ (fun p => by
    apply LinearMap.ext
    intro x
    have hx : verticalEdgeInclusion M A x ∈ degenerateL1 M A := verticalEdge_range_le_L1 M A ⟨x, rfl⟩
    exact LinearMap.congr_fun (restriction1_evaluation1 M A p) ⟨_, hx⟩)

/-- F¹のP₁評価は同じ実ε₁。 -/
@[simp] theorem firstFiltrationEvaluation1_val (p : (pushforwardComplex M A).C1) :
    (firstFiltrationEvaluation1 M A p).1 = evaluation1 M A p := rfl

/-- 同じε₂の値は原none面空間をannihilateしF²に入る。 -/
def secondFiltrationEvaluation2 : (pushforwardComplex M A).C2 →ₗ[ℚ] (secondFiltrationComplex M A).C2 :=
  (evaluation2 M A).codRestrict _ (restriction2_evaluation2 M A)

/-- F²のP₂評価は同じ実ε₂。 -/
@[simp] theorem secondFiltrationEvaluation2_val (p : (pushforwardComplex M A).C2) :
    (secondFiltrationEvaluation2 M A p).1 = evaluation2 M A p := rfl

/-- 原ε微分の可換式は同じF¹/F²部分空間でも成立。 -/
theorem firstFiltrationEvaluation1_d1 (p : (pushforwardComplex M A).C1) :
    (firstFiltrationComplex M A).d1 (firstFiltrationEvaluation1 M A p) =
      (secondFiltrationInclusion M A).f2 (secondFiltrationEvaluation2 M A ((pushforwardComplex M A).d1 p)) := by
  apply Subtype.ext
  rw [firstFiltrationDifferential_val, firstFiltrationEvaluation1_val,
    secondFiltrationInclusion_f2_val, secondFiltrationEvaluation2_val]
  exact (evaluation_comm1 M A p).symm

/-- P₁の水平評価は原B双対の核へ入る。 -/
def firstRowOneMap : (pushforwardComplex M A).C1 →ₗ[ℚ] LinearMap.ker (secondGradedComplex M A).d1 :=
  ((horizontalRestriction1 M A).comp (firstFiltrationEvaluation1 M A)).codRestrict _ (fun p => by
    rw [LinearMap.mem_ker]
    change (mixedHorizontalBoundary M A).dualMap (horizontalRestriction1 M A (firstFiltrationEvaluation1 M A p)) = 0
    rw [← mixedRestriction_comm1, firstFiltrationEvaluation1_d1]
    exact mixedRestriction2_second M A _)

/-- P₁座標は同じ原水平評価。 -/
@[simp] theorem firstRowOneMap_val (p : (pushforwardComplex M A).C1) :
    (firstRowOneMap M A p).1 = horizontalRestriction1 M A (firstFiltrationEvaluation1 M A p) := rfl

/-- 水平制限と原ε₁の単射性がP₁座標の単射性を生成する。 -/
theorem firstRowOneMap_injective : Function.Injective (firstRowOneMap M A) := by
  intro p q hpq
  apply evaluation1_injective M A
  have he : firstFiltrationEvaluation1 M A p = firstFiltrationEvaluation1 M A q :=
    horizontalRestriction1_injective M A (congrArg (fun z : LinearMap.ker (secondGradedComplex M A).d1 => z.1) hpq)
  exact congrArg (fun z : (firstFiltrationComplex M A).C1 => z.1) he

/-- 閉水平値を原辺へ延長してL₁をannihilateし、実P₁原像を生成する。 -/
theorem firstRowOneMap_surjective : Function.Surjective (firstRowOneMap M A) := by
  intro β
  let w := horizontalCochainLift M A β.1
  have hw : restriction1 M A w.1 = 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, m, he⟩ := (mem_degenerateL1 M A x.1).mp x.2
    rw [restriction1_apply, ← he, map_add]
    have hv := LinearMap.congr_fun w.2 v
    change freeDualEquiv _ w.1 (verticalEdgeInclusion M A v) = 0 at hv
    rw [hv, zero_add, ← mixedBoundary_recombination M A m, map_add]
    have hd := LinearMap.congr_fun w.2 (mixedVerticalBoundary M A m)
    change freeDualEquiv _ w.1 (verticalEdgeInclusion M A (mixedVerticalBoundary M A m)) = 0 at hd
    rw [hd, zero_add, ← horizontalRestriction1_apply, horizontalCochainLift_spec]
    exact LinearMap.congr_fun β.2 m
  have hi : w.1 ∈ LinearMap.range (evaluation1 M A) := by
    rw [evaluation1_range_eq_ker]
    exact hw
  obtain ⟨p, hp⟩ := hi
  refine ⟨p, ?_⟩
  apply Subtype.ext
  rw [firstRowOneMap_val]
  have he : firstFiltrationEvaluation1 M A p = w := Subtype.ext hp
  rw [he]
  exact horizontalCochainLift_spec M A β.1

/-- 原E₁(1,0)の閉水平核は同じP₁と両方向に同型。 -/
def firstRowOneEquiv : (pushforwardComplex M A).C1 ≃ₗ[ℚ] LinearMap.ker (secondGradedComplex M A).d1 :=
  LinearEquiv.ofBijective (firstRowOneMap M A) ⟨firstRowOneMap_injective M A, firstRowOneMap_surjective M A⟩

/-- P₂のF²評価は原ε₂の単射性を保つ。 -/
theorem secondFiltrationEvaluation2_injective : Function.Injective (secondFiltrationEvaluation2 M A) := by
  intro p q hpq
  apply evaluation2_injective M A
  exact congrArg (fun z : (secondFiltrationComplex M A).C2 => z.1) hpq

/-- P₂のF²評価は原none面annihilatorの全体へ全射。 -/
theorem secondFiltrationEvaluation2_surjective : Function.Surjective (secondFiltrationEvaluation2 M A) := by
  intro z
  obtain ⟨p, hp⟩ := evaluation2_preimage_of_restriction_zero M A z.1 z.2
  exact ⟨p, Subtype.ext hp⟩

/-- 原E₁(2,0)の元F²₂は同じP₂と両方向に同型。 -/
def secondFiltrationEvaluation2Equiv : (pushforwardComplex M A).C2 ≃ₗ[ℚ] (secondFiltrationComplex M A).C2 :=
  LinearEquiv.ofBijective (secondFiltrationEvaluation2 M A)
    ⟨secondFiltrationEvaluation2_injective M A, secondFiltrationEvaluation2_surjective M A⟩

/-- gr¹の0次微分は零加群からなので、一次coboundary像は零。 -/
theorem secondGraded_boundaryToCycles_range_zero :
    LinearMap.range (secondGradedComplex M A).boundaryToCycles = ⊥ := by
  have hh : (secondGradedComplex M A).boundaryToCycles = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [ThreeCochainComplex.boundaryToCycles_apply]
    rfl
  rw [hh, LinearMap.range_zero]

/-- E₁(0,0)の標準homology座標は原P₀核評価から生成する。 -/
def firstRowCoordinates0 : (pushforwardComplex M A).C0 ≃ₗ[ℚ]
    (zeroExtension (firstGradedComplex M A)).homology (0 : ℤ) :=
  (firstRowZeroEquiv M A).trans (oldH0Equiv (firstGradedComplex M A))

/-- E₁(1,0)の標準homology座標は原P₁閉値から生成する。 -/
def firstRowCoordinates1 : (pushforwardComplex M A).C1 ≃ₗ[ℚ]
    (zeroExtension (secondGradedComplex M A)).homology (1 : ℤ) :=
  (firstRowOneEquiv M A).trans
    (((LinearMap.range (secondGradedComplex M A).boundaryToCycles).quotEquivOfEqBot
      (secondGraded_boundaryToCycles_range_zero M A)).symm.trans (oldH1Equiv (secondGradedComplex M A)))

/-- E₁(2,0)の標準homology座標は原P₂値から生成する。 -/
def firstRowCoordinates2 : (pushforwardComplex M A).C2 ≃ₗ[ℚ]
    (zeroExtension (secondFiltrationComplex M A)).homology (2 : ℤ) :=
  (secondFiltrationEvaluation2Equiv M A).trans
    (((LinearMap.range (secondFiltrationComplex M A).d1).quotEquivOfEqBot (by
      change LinearMap.range (0 : PUnit.{u+1} →ₗ[ℚ] _) = ⊥
      exact LinearMap.range_zero)).symm.trans (oldH2Equiv (secondFiltrationComplex M A)))

/-- 第一行0次の座標は同じ原閉chart核値。 -/
@[simp] theorem firstRowCoordinates0_apply (p : (pushforwardComplex M A).C0) :
    firstRowCoordinates0 M A p = oldH0Equiv (firstGradedComplex M A) (firstRowZeroMap M A p) := rfl

/-- 原Pの第一微分評価はF¹の閉辺値。 -/
def firstRowZeroLiftDifferential (p : (pushforwardComplex M A).C0) :
    LinearMap.ker (firstFiltrationComplex M A).d1 :=
  ⟨firstFiltrationEvaluation1 M A ((pushforwardComplex M A).d0 p), by
    rw [LinearMap.mem_ker, firstFiltrationEvaluation1_d1,
      (pushforwardComplex M A).d1_comp_d0, map_zero, map_zero]⟩

/-- 原P₀持ち上げの細微分は同じ閉F¹辺値。 -/
theorem firstRowZeroLift_spec (p : (pushforwardComplex M A).C0) :
    (firstFiltrationInclusion M A).f1 (firstRowZeroLiftDifferential M A p).1 =
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d0 (evaluation0 M A p) := by
  change evaluation1 M A ((pushforwardComplex M A).d0 p) = _
  exact evaluation_comm0 M A p

/-- 第零列の原標準δは同じP第一微分のF¹類。 -/
theorem firstRowZero_connecting (p : (pushforwardComplex M A).C0) :
    firstCoupleK M A 0 (firstRowCoordinates0 M A p) =
      oldH1Equiv (firstFiltrationComplex M A) (Submodule.Quotient.mk (firstRowZeroLiftDifferential M A p)) := by
  rw [firstRowCoordinates0_apply, firstCoupleK_apply]
  exact threeShortExact_connecting_representative_zero
    (firstFiltrationInclusion M A) (firstGradedProjection M A)
    (firstGraded_standard_zero M A) (firstGraded_shortExact M A)
    (firstRowZeroMap M A p) (evaluation0 M A p) (firstRowZeroLiftDifferential M A p)
    rfl (firstRowZeroLift_spec M A p)

/-- 第一行1次の座標は同じ元閉水平値のhomology類。 -/
@[simp] theorem firstRowCoordinates1_apply (p : (pushforwardComplex M A).C1) :
    firstRowCoordinates1 M A p = oldH1Equiv (secondGradedComplex M A)
      (Submodule.Quotient.mk (firstRowOneMap M A p)) := rfl

/-- 第一行2次の座標は同じ元F²面値のhomology類。 -/
@[simp] theorem firstRowCoordinates2_apply (p : (pushforwardComplex M A).C2) :
    firstRowCoordinates2 M A p = oldH2Equiv (secondFiltrationComplex M A)
      (Submodule.Quotient.mk (secondFiltrationEvaluation2 M A p)) := rfl

/-- 実E₁の第一列δは同じ原P第二微分へ同定される。 -/
theorem firstRow_secondDifferential (p : (pushforwardComplex M A).C1) :
    secondCoupleK M A 1 (firstRowCoordinates1 M A p) =
      firstRowCoordinates2 M A ((pushforwardComplex M A).d1 p) := by
  rw [firstRowCoordinates1_apply, firstRowCoordinates2_apply, secondCoupleK_apply]
  apply threeShortExact_connecting_representative
    (secondFiltrationInclusion M A) (secondGradedProjection M A)
    (secondGraded_standard_zero M A) (secondGraded_shortExact M A)
    (firstRowOneMap M A p) (firstFiltrationEvaluation1 M A p)
    (secondFiltrationEvaluation2 M A ((pushforwardComplex M A).d1 p))
  · rfl
  · exact (firstFiltrationEvaluation1_d1 M A p).symm

/-- 実E₁の第零列j∘kは同じ原P第一微分へ同定される。 -/
theorem firstRow_firstDifferential (p : (pushforwardComplex M A).C0) :
    firstPageDifferential M A 0 (firstRowCoordinates0 M A p) =
      firstRowCoordinates1 M A ((pushforwardComplex M A).d0 p) := by
  rw [firstPageDifferential_apply, firstRowZero_connecting]
  change secondCoupleJ M A 1 _ = _
  rw [secondCoupleJ_apply, ← oldH1Equiv_natural, firstRowCoordinates1_apply]
  have hm : (secondGradedProjection M A).h1Map
      (Submodule.Quotient.mk (firstRowZeroLiftDifferential M A p)) =
      Submodule.Quotient.mk ((secondGradedProjection M A).cyclesMap (firstRowZeroLiftDifferential M A p)) :=
    (secondGradedProjection M A).h1Map_mk _
  rw [hm]
  apply congrArg (oldH1Equiv (secondGradedComplex M A))
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rfl

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.firstRowZeroMap
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowZeroMap_val
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowZeroMap_injective
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowZeroMap_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowZeroEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationEvaluation1
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationEvaluation1_val
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationEvaluation2
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationEvaluation2_val
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationEvaluation1_d1
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowOneMap
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowOneMap_val
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowOneMap_injective
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowOneMap_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowOneEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationEvaluation2_injective
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationEvaluation2_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationEvaluation2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.secondGraded_boundaryToCycles_range_zero
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowCoordinates0
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowCoordinates1
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowCoordinates2
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowCoordinates0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowZeroLiftDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowZeroLift_spec
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowZero_connecting
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowCoordinates1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.firstRowCoordinates2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.firstRow_secondDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.firstRow_firstDifferential
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
