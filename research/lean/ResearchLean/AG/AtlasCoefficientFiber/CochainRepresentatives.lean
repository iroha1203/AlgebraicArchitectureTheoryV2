import ResearchLean.AG.AtlasCoefficientFiber.FiberCohomology
import ResearchLean.AG.AtlasCoefficientFiber.QuotientDual

/-!
# G-135 B：原垂直cocycleと水平補正の生成

原Vの双対核を使う。R条件から水平βの存在をdualMapの像定理で導く。

## Implementation notes

κのDy代表式と実homology評価を使ってR条件をker Bのannihilationへ戻す。
水平補正は期待する完全性から仮定せず、原Bの双対像から生成する。
持ち上げは元K′の二射影に対する汎関数の和である。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原垂直Vに消える閉cochain。 -/
abbrev VerticalCocycles := LinearMap.ker (verticalBoundary M A).dualMap

/-- 原垂直homology上の閉cochainの実代表評価。 -/
def verticalCocycleClass : VerticalCocycles M A →ₗ[ℚ] Module.Dual ℚ (VerticalHomology M A) :=
  cocycleHomologyEvaluation (verticalEdgeBoundary M A) (verticalBoundary M A)
    (verticalEdgeBoundary_comp_verticalBoundary M A)

/-- 垂直代表のhomology評価は同じcochain値を読む。 -/
@[simp] theorem verticalCocycleClass_mk (z : VerticalCocycles M A) (x : verticalCycles M A) :
    verticalCocycleClass M A z (Submodule.Quotient.mk x) = z.1 x.1 :=
  cocycleHomologyEvaluation_mk _ _ _ z x

/-- κに対する垂直代表の評価は同じ原Dyの値。 -/
@[simp] theorem verticalCocycleClass_kappa (z : VerticalCocycles M A) (y : mixedCycles M A) :
    verticalCocycleClass M A z (rawKappa M A y) = z.1 (mixedVerticalBoundary M A y.1) := by
  rw [rawKappa_apply, verticalCocycleClass_mk, mixedCycleToVertical_val]

/-- Rへの所属条件は原ker B上のzD零性に必要十分。 -/
theorem verticalCocycleClass_rawR_iff (z : VerticalCocycles M A) :
    verticalCocycleClass M A z ∈ LinearMap.ker (rawKappa M A).dualMap ↔
      ∀ y : mixedCycles M A, z.1 (mixedVerticalBoundary M A y.1) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hz y
    simpa only [LinearMap.dualMap_apply, verticalCocycleClass_kappa, LinearMap.zero_apply]
      using LinearMap.congr_fun hz y
  · intro hz
    apply LinearMap.ext
    intro y
    rw [LinearMap.dualMap_apply, verticalCocycleClass_kappa, LinearMap.zero_apply, hz y]

/-- R条件から原Bの水平補正βB=-zDを生成する。 -/
theorem horizontalCorrection_exists (z : VerticalCocycles M A)
    (hz : verticalCocycleClass M A z ∈ LinearMap.ker (rawKappa M A).dualMap) :
    ∃ β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ),
      (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1 := by
  have hz' := (verticalCocycleClass_rawR_iff M A z).mp hz
  have hm : -(mixedVerticalBoundary M A).dualMap z.1 ∈
      (LinearMap.ker (mixedHorizontalBoundary M A)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    simp only [LinearMap.neg_apply, LinearMap.dualMap_apply, hz' ⟨y, hy⟩, neg_zero]
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hm
  exact hm

/-- 水平補正を持つ垂直代表は実κ双対核へ戻る。 -/
theorem verticalCocycleClass_rawR_of_correction (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    verticalCocycleClass M A z ∈ LinearMap.ker (rawKappa M A).dualMap := by
  apply (verticalCocycleClass_rawR_iff M A z).mpr
  intro y
  have hh := LinearMap.congr_fun hβ y.1
  rw [LinearMap.dualMap_apply, LinearMap.neg_apply, LinearMap.dualMap_apply,
    show mixedHorizontalBoundary M A y.1 = 0 from y.2, map_zero] at hh
  exact neg_eq_zero.mp hh.symm

/-- 同じ原垂直代表と補正から指定全Φ上Rへ移す。 -/
def correctedFiberClass (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) : R M A :=
  (fiberRRawEquiv M A).symm
    ⟨verticalCocycleClass M A z, verticalCocycleClass_rawR_of_correction M A z β hβ⟩

/-- Rの原垂直表示は同じ代表評価である。 -/
@[simp] theorem correctedFiberClass_raw (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    (fiberRRawEquiv M A (correctedFiberClass M A z β hβ)).1 = verticalCocycleClass M A z := by
  exact congrArg Subtype.val ((fiberRRawEquiv M A).apply_symm_apply _)

/-- 原垂直homologyの全汎関数は原V閉cochainから生成される。 -/
theorem verticalCocycleClass_surjective : Function.Surjective (verticalCocycleClass M A) :=
  cocycleHomologyEvaluation_surjective _ _ _

/-- 指定Rの全類を、原垂直代表と原Bの水平補正から生成する。 -/
theorem fiberClass_has_correction (r : R M A) :
    ∃ (z : VerticalCocycles M A) (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
      (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1),
      correctedFiberClass M A z β hβ = r := by
  obtain ⟨z, hz⟩ := verticalCocycleClass_surjective M A (fiberRRawEquiv M A r).1
  have hr : verticalCocycleClass M A z ∈ LinearMap.ker (rawKappa M A).dualMap := by
    rw [hz]
    exact (fiberRRawEquiv M A r).2
  obtain ⟨β, hβ⟩ := horizontalCorrection_exists M A z hr
  refine ⟨z, β, hβ, (fiberRRawEquiv M A).injective ?_⟩
  apply Subtype.ext
  rw [correctedFiberClass_raw, hz]

/-- 元K′の二blockの値から持ち上げ汎関数を作る。 -/
def correctedEdgeFunctional (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) :
    Module.Dual ℚ (K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :=
  z.comp (verticalEdgeProjection M A) + β.comp (horizontalEdgeProjection M A)

/-- 持ち上げ汎関数は元二blockの係数で評価する。 -/
@[simp] theorem correctedEdgeFunctional_apply (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    correctedEdgeFunctional M A z β x = z (verticalEdgeProjection M A x) +
      β (horizontalEdgeProjection M A x) := rfl

/-- 元垂直包含への値はzそのもの。 -/
@[simp] theorem correctedEdgeFunctional_vertical (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) (x : VerticalEdge M A →₀ ℚ) :
    correctedEdgeFunctional M A z β (verticalEdgeInclusion M A x) = z x := by
  rw [correctedEdgeFunctional_apply, verticalEdgeProjection_inclusion,
    horizontalEdgeProjection_vertical, map_zero, add_zero]

/-- 元水平包含への値はβそのもの。 -/
@[simp] theorem correctedEdgeFunctional_horizontal (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) (x : HorizontalEdge M A →₀ ℚ) :
    correctedEdgeFunctional M A z β (horizontalEdgeInclusion M A x) = β x := by
  rw [correctedEdgeFunctional_apply, verticalEdgeProjection_horizontal,
    horizontalEdgeProjection_inclusion, map_zero, zero_add]

/-- 元支持cochainの名前付き辺値へ同じ汎関数を戻す。 -/
def correctedEdgeCochain (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) :
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1 :=
  (freeDualEquiv _).symm (correctedEdgeFunctional M A z β)

/-- 自由双対同型で戻すと同じ持ち上げ汎関数。 -/
@[simp] theorem correctedEdgeCochain_dual (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) :
    freeDualEquiv _ (correctedEdgeCochain M A z β) = correctedEdgeFunctional M A z β :=
  (freeDualEquiv _).apply_symm_apply _

/-- 同じ細微分を実原chain上で評価する所有API。 -/
theorem correctedEdgeCochain_d1_eval (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    freeDualEquiv _ ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1
      (correctedEdgeCochain M A z β)) x =
      correctedEdgeFunctional M A z β (chainD2 Nf _ x) := by
  calc
    _ = freeDualEquiv _ (correctedEdgeCochain M A z β) (chainD2 Nf _ x) :=
      (chainD2_dual Nf _ (correctedEdgeCochain M A z β) x).symm
    _ = _ := by rw [correctedEdgeCochain_dual]

/-- 持ち上げの垂直面微分は同じzV。 -/
theorem correctedEdgeCochain_d1_vertical (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) (x : VerticalFace M A →₀ ℚ) :
    freeDualEquiv _ ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1
      (correctedEdgeCochain M A z β)) (verticalFaceInclusion M A x) =
      z (verticalBoundary M A x) := by
  rw [correctedEdgeCochain_d1_eval]
  have he := LinearMap.congr_fun (verticalBoundary_inclusion M A) x
  simp only [LinearMap.comp_apply] at he
  rw [← he, correctedEdgeFunctional_vertical]

/-- 持ち上げの混在面微分は同じzD+βB。 -/
theorem correctedEdgeCochain_d1_mixed (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) (x : MixedFace M A →₀ ℚ) :
    freeDualEquiv _ ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1
      (correctedEdgeCochain M A z β)) (mixedFaceInclusion M A x) =
      z (mixedVerticalBoundary M A x) + β (mixedHorizontalBoundary M A x) := by
  rw [correctedEdgeCochain_d1_eval, ← mixedBoundary_recombination, map_add,
    correctedEdgeFunctional_vertical, correctedEdgeFunctional_horizontal]

/-- 持ち上げのmapped面微分は同じβH。 -/
theorem correctedEdgeCochain_d1_horizontal (z : Module.Dual ℚ (VerticalEdge M A →₀ ℚ))
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) (x : HorizontalFace M A →₀ ℚ) :
    freeDualEquiv _ ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1
      (correctedEdgeCochain M A z β)) (horizontalFaceInclusion M A x) =
      β (horizontalFaceBoundary M A x) := by
  rw [correctedEdgeCochain_d1_eval]
  have he := LinearMap.congr_fun (horizontalFaceBoundary_inclusion M A) x
  simp only [LinearMap.comp_apply] at he
  rw [← he, correctedEdgeFunctional_horizontal]

/-- 原V閉性と水平補正から、微分が元の全L₂をannihilateする。 -/
theorem correctedEdgeCochain_d1_degenerate (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (x : degenerateL2 M A) :
    freeDualEquiv _ ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1
      (correctedEdgeCochain M A z.1 β)) x.1 = 0 := by
  have hx : x.1 ∈ LinearMap.range (verticalFaceInclusion M A) ⊔
      LinearMap.range (mixedFaceInclusion M A) := by
    rw [← degenerateL2_vertical_mixed]
    exact x.2
  obtain ⟨v, ⟨f, hf⟩, m, ⟨g, hg⟩, he⟩ := Submodule.mem_sup.mp hx
  have he' : verticalFaceInclusion M A f + mixedFaceInclusion M A g = x.1 := by
    simpa only [← hf, ← hg] using he
  rw [← he', map_add, correctedEdgeCochain_d1_vertical, correctedEdgeCochain_d1_mixed]
  have hz := LinearMap.congr_fun z.2 f
  have hb := LinearMap.congr_fun hβ g
  simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at hz
  simp only [LinearMap.dualMap_apply, LinearMap.neg_apply] at hb
  rw [hz, hb, add_neg_cancel, add_zero]

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.VerticalCocycles
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCocycleClass
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCocycleClass_mk
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCocycleClass_kappa
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCocycleClass_rawR_iff
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalCorrection_exists
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCocycleClass_rawR_of_correction
#print axioms AAT.AG.AtlasCoefficientFiber.correctedFiberClass
#print axioms AAT.AG.AtlasCoefficientFiber.correctedFiberClass_raw
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCocycleClass_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.fiberClass_has_correction
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeFunctional
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeFunctional_apply
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeFunctional_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeFunctional_horizontal
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeCochain
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeCochain_dual
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeCochain_d1_eval
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeCochain_d1_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeCochain_d1_mixed
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeCochain_d1_horizontal
#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeCochain_d1_degenerate
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
