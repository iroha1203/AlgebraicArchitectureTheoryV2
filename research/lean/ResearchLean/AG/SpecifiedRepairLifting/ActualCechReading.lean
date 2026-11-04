import ResearchLean.AG.SpecifiedRepairLifting.ActualCechLifting
/-! # 元の reading 射から指定補正の可換平方を生成する

Implementation notes: 実 Čech 側は既存の次数0・1の pullback を使い、
次数2以上の空添字に対する一意な射を用いる。診断側は独立に生成された
generatedComparisonHom の全成分を使う。平方を追加certificateとして受け取らず、
既存の座標自然性から証明して C の一般輸送へ接続する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.SpecifiedRepairLifting
open Cohomology TwoPhase ObstructionDiagnosticBridge CanonicalResolution ResolutionInvariance
open GeneratorPresentation
universe u

section DiagnosticMap
variable {K L : ThreeCochainComplex.{0,u} ℚ}
/-- 元の診断 cochain 射の三成分を加法的に忘却する。 -/
def diagnosticMapDegree (f : ThreeCochainComplex.Hom K L) :
    (n : ℕ) → diagnosticObject K n ⟶ diagnosticObject L n
  | 0 => ModuleCat.ofHom f.f0.toAddMonoidHom.toIntLinearMap
  | 1 => ModuleCat.ofHom f.f1.toAddMonoidHom.toIntLinearMap
  | 2 => ModuleCat.ofHom f.f2.toAddMonoidHom.toIntLinearMap
  | _+3 => 0
/-- 元の診断射の二可換式から全次数の可換性を生成する。 -/
theorem diagnosticMapDegree_comm (f : ThreeCochainComplex.Hom K L) (n : ℕ) :
    diagnosticMapDegree f n ≫ diagnosticDifferential L n =
      diagnosticDifferential K n ≫ diagnosticMapDegree f (n+1) := by
  rcases n with _ | _ | n
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (f.comm0 a).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (f.comm1 a).symm
  · simp only [diagnosticDifferential, Limits.comp_zero, Limits.zero_comp]
/-- 同じ診断射の非負零延長。 -/
def diagnosticNativeMap (f : ThreeCochainComplex.Hom K L) : diagnosticNative K ⟶ diagnosticNative L :=
  CochainComplex.ofHom _ _ _ _ _ _ (diagnosticMapDegree f) (diagnosticMapDegree_comm f)
/-- 元の診断 H¹ 射は標準 H¹ 射と同じ全代表で可換。 -/
theorem diagnosticNativeMap_h1 (f : ThreeCochainComplex.Hom K L) (x : K.H1) :
    homologyMap (diagnosticNativeMap f) 1 (diagnosticH1Equiv K x) =
      diagnosticH1Equiv L (f.h1Map x) := by
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.boundaryToCycles) x
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  change ShortComplex.homologyMap ((shortComplexFunctor _ _ 1).map (diagnosticNativeMap f))
    (moduleCycleClass _ (diagnosticCycleEquiv K z)) =
      moduleCycleClass _ (diagnosticCycleEquiv L (f.cyclesMap z))
  rw [moduleCycleClass_naturality]
  congr 1
end DiagnosticMap

variable {Source : Type u} [Fintype Source] {q r : Reading Source} {hqr : q.CoarserThan r}
variable {laws : FiniteLawFamily Source} {D : TargetSupportedNerve q} {E : TargetSupportedNerve r}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A} {G : ContextOpenSupport S}
variable [IsEmpty D.nerve.FaceComponent] [IsEmpty E.nerve.FaceComponent]
variable (P : GeneratorPresentation laws) (V : FaceEmptyAATCechCover D G) (W : FaceEmptyAATCechCover E G)
variable (M : TargetSupportedNerveMorphism q r hqr D E)
variable (ha : laws.Adequate q) (hb : laws.Adequate r)
/-- 元の実 reading pullback を全次数へ拡張する。 -/
def actualReadingDegree : (n : ℕ) → cechObject (P.faceEmptyCechComplex V) n ⟶
    cechObject (P.faceEmptyCechComplex W) n
  | 0 => ModuleCat.ofHom (P.actualCechPullback0 (coarseCover := V) (fineCover := W) M).toIntLinearMap
  | 1 => ModuleCat.ofHom (P.actualCechPullback1 (coarseCover := V) (fineCover := W) M).toIntLinearMap
  | _+2 => 0
omit [Fintype Source] in
/-- 元の face-empty Čech の高次微分は実際に零射である。 -/
theorem actualCechDifferential_succ (n : ℕ) : cechDifferential (P.faceEmptyCechComplex V) (n+1) = 0 := rfl
omit [Fintype Source] in
/-- 元の reading 可換式から実 Čech 射の全次数条件を放電する。 -/
theorem actualReadingDegree_comm (n : ℕ) :
    actualReadingDegree P V W M n ≫ cechDifferential (P.faceEmptyCechComplex W) n =
      cechDifferential (P.faceEmptyCechComplex V) n ≫ actualReadingDegree P V W M (n+1) := by
  rcases n with _ | n
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (P.actualCechPullback_comm0 (coarseCover := V) (fineCover := W) M a).symm
  · rw [actualCechDifferential_succ, actualCechDifferential_succ, Limits.comp_zero, Limits.zero_comp]
/-- 同じ全次数 Čech 群の間の元の reading 射。 -/
def actualReadingMap : cechNative (P.faceEmptyCechComplex V) ⟶ cechNative (P.faceEmptyCechComplex W) :=
  CochainComplex.ofHom _ _ _ _ _ _ (actualReadingDegree P V W M) (actualReadingDegree_comm P V W M)
omit [Fintype Source] in
/-- 元の実 reading H¹ 射との全代表における一致。 -/
theorem actualReadingMap_h1 (x : (P.faceEmptyCechComplex V).AdditiveCechH1) :
    homologyMap (actualReadingMap P V W M) 1 (cechH1Equiv _ x) =
      cechH1Equiv _ (P.actualCechRefinementH1Map (coarseCover := V) (fineCover := W) M x) := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective ((P.faceEmptyCechComplex V).CechCoboundarySubgroupSucc 0) x
  change ShortComplex.homologyMap ((shortComplexFunctor _ _ 1).map (actualReadingMap P V W M))
    (moduleCycleClass _ (cechCycleEquiv _ z)) =
      moduleCycleClass _ (cechCycleEquiv _ (P.actualCechPullbackCycles (coarseCover := V) (fineCover := W) M z))
  rw [moduleCycleClass_naturality]
  congr 1
omit [Fintype Source] in
/-- 実係数比較の零次自然性を元の座標同定から生成する。 -/
theorem actualCoefficient0_reading (a : (P.faceEmptyCechComplex V).Cn 0) :
    P.actualCechCoefficientCochain0 W hb (P.actualCechPullback0 (coarseCover := V) (fineCover := W) M a) =
      M.generatedPullback0 laws ha hb (P.actualCechCoefficientCochain0 V ha a) := by
  change P.coefficientCochain0 E hb
    ((P.faceEmptyCechCochain0Equiv W) ((P.faceEmptyCechCochain0Equiv W).symm
      (P.presentationPullback0 M (P.faceEmptyCechCochain0Equiv V a)))) = _
  rw [AddEquiv.apply_symm_apply]
  exact P.coefficientCochain0_presentationPullback M ha hb _
/-- 元の reading と独立診断 reading が同じ実比較の可換平方を与える。 -/
theorem actualReading_square :
    actualComparison P V ha ≫ diagnosticNativeMap (M.generatedComparisonHom laws ha hb) =
      actualReadingMap P V W M ≫ actualComparison P W hb := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rcases n with _ | _ | _ | n
  · exact (actualCoefficient0_reading P V W M ha hb a).symm
  · exact (P.actualCechCoefficient1_pullback_naturality (coarseCover := V) (fineCover := W) M ha hb a).symm
  · funext c
    exact isEmptyElim c.cell
  · rfl

/-- 同じ元の transition と localState を既存 reading 射で輸送する。 -/
def actualReadingData (x : ActualCechAffineLocalData P V) : ActualCechAffineLocalData P W where
  transition := P.actualCechPullback1 (coarseCover := V) (fineCover := W) M x.transition
  localState := P.actualCechPullback0 (coarseCover := V) (fineCover := W) M x.localState
omit [Fintype Source] in
/-- 独立に輸送した局所データの mismatch は元の mismatch の pullback。 -/
theorem actualReadingData_mismatch (x : ActualCechAffineLocalData P V) :
    (actualReadingData P V W M x).actualMismatch =
      (actualReadingMap P V W M).f 1 x.actualMismatch := by
  change P.actualCechPullback1 M x.transition +
    (P.faceEmptyCechComplex W).d 0 (P.actualCechPullback0 M x.localState) =
      P.actualCechPullback1 M (x.transition + (P.faceEmptyCechComplex V).d 0 x.localState)
  rw [map_add, P.actualCechPullback_comm0]
/-- 同じ指定診断補正は reading 平方で適合性を保つ。 -/
theorem actualReading_compatible (x : ActualCechAffineLocalData P V)
    (b : D.ChartCoordinate laws ha → ℚ)
    (he : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    E.lawGeneratedD0 laws hb (M.generatedPullback0 laws ha hb b) =
      (actualReadingData P V W M x).diagnosticMismatch hb := by
  rw [← (actualReadingData P V W M x).actual_cech_coefficient_actual_mismatch_eq_diagnostic_mismatch]
  rw [actualReadingData_mismatch]
  change E.lawGeneratedD0 laws hb (M.generatedPullback0 laws ha hb b) =
    P.actualCechCoefficientCochain1 W hb (P.actualCechPullback1 M x.actualMismatch)
  have hc := M.generatedPullback_comm0 laws ha hb b
  change M.generatedPullback1 laws ha hb (D.lawGeneratedD0 laws ha b) =
    E.lawGeneratedD0 laws hb (M.generatedPullback0 laws ha hb b) at hc
  rw [← hc, he, ← x.actual_cech_coefficient_actual_mismatch_eq_diagnostic_mismatch ha]
  exact (P.actualCechCoefficient1_pullback_naturality (coarseCover := V) (fineCover := W) M ha hb _).symm
/-- C の同じ平方から、輸送した局所データの厳密持ち上げを生成する。 -/
def actualReadingLift (x : ActualCechAffineLocalData P V)
    (b : D.ChartCoordinate laws ha → ℚ) (a : ActualLift P V ha x b) :
    ActualLift P W hb (actualReadingData P V W M x) (M.generatedPullback0 laws ha hb b) := by
  have a' := squareLiftMap (actualComparison P V ha) (actualComparison P W hb)
    (actualReadingMap P V W M) (diagnosticNativeMap (M.generatedComparisonHom laws ha hb))
    (actualReading_square P V W M ha hb) a
  refine ⟨a'.val, ?_, a'.property.2⟩
  rw [actualReadingData_mismatch]
  exact a'.property.1
/-- 輸送した厳密持ち上げの値は既存零次 pullback そのもの。 -/
theorem actualReadingLift_val (x : ActualCechAffineLocalData P V)
    (b : D.ChartCoordinate laws ha → ℚ) (a : ActualLift P V ha x b) :
    (actualReadingLift P V W M ha hb x b a).val =
      P.actualCechPullback0 (coarseCover := V) (fineCover := W) M a.val := rfl
/-- C の同じ標準錐写像は、輸送した局所データと指定補正の障害を結ぶ。 -/
theorem actualReading_obstruction (x : ActualCechAffineLocalData P V)
    (b : D.ChartCoordinate laws ha → ℚ)
    (he : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    squareObstructionMap (actualComparison P V ha) (actualComparison P W hb)
      (actualReadingMap P V W M) (diagnosticNativeMap (M.generatedComparisonHom laws ha hb))
      (actualReading_square P V W M ha hb) (actualObstruction P V ha x b he) =
    actualObstruction P W hb (actualReadingData P V W M x) (M.generatedPullback0 laws ha hb b)
      (actualReading_compatible P V W M ha hb x b he) := by
  simp only [actualObstruction_eq_nonnegativeObstruction]
  rw [obstruction_naturality]
  congr 1
  exact (actualReadingData_mismatch P V W M x).symm

/-- 元補正の輸送と新しい側で選び直した補正は同じ残差類を与える。 -/
theorem actualReading_residual (x : ActualCechAffineLocalData P V)
    (b : D.ChartCoordinate laws ha → ℚ)
    (he : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha)
    (a₀ : (P.faceEmptyCechComplex V).Cn 0)
    (h₀ : (P.faceEmptyCechComplex V).d 0 a₀ = x.actualMismatch)
    (a₁ : (P.faceEmptyCechComplex W).Cn 0)
    (h₁ : (P.faceEmptyCechComplex W).d 0 a₁ = (actualReadingData P V W M x).actualMismatch) :
    squareCokernelMap (actualComparison P V ha) (actualComparison P W hb)
      (actualReadingMap P V W M) (diagnosticNativeMap (M.generatedComparisonHom laws ha hb))
      (actualReading_square P V W M ha hb) (actualResidual P V ha x b a₀ h₀ he) =
    actualResidual P W hb (actualReadingData P V W M x) (M.generatedPullback0 laws ha hb b) a₁ h₁
      (actualReading_compatible P V W M ha hb x b he) := by
  simp only [actualResidual_eq_residualClass]
  simp only [actualReadingData_mismatch]
  exact (residualClass_naturality (actualComparison P V ha) (actualComparison P W hb)
    (actualReadingMap P V W M) (diagnosticNativeMap (M.generatedComparisonHom laws ha hb))
    (actualReading_square P V W M ha hb) x.actualMismatch b a₀
    (by rw [cechNative_d]; exact h₀) (actualMismatch_compatible P V ha x b he)).trans
      (residualClass_independent _ _ _ _ _ _ _ _)
end AAT.AG.SpecifiedRepairLifting

#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticMapDegree
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticMapDegree_comm
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticNativeMap
#print axioms AAT.AG.SpecifiedRepairLifting.diagnosticNativeMap_h1
#print axioms AAT.AG.SpecifiedRepairLifting.actualReadingDegree
#print axioms AAT.AG.SpecifiedRepairLifting.actualCechDifferential_succ
#print axioms AAT.AG.SpecifiedRepairLifting.actualReadingDegree_comm
#print axioms AAT.AG.SpecifiedRepairLifting.actualReadingMap
#print axioms AAT.AG.SpecifiedRepairLifting.actualReadingMap_h1
#print axioms AAT.AG.SpecifiedRepairLifting.actualCoefficient0_reading
#print axioms AAT.AG.SpecifiedRepairLifting.actualReading_square
#print axioms AAT.AG.SpecifiedRepairLifting.actualReadingData
#print axioms AAT.AG.SpecifiedRepairLifting.actualReadingData_mismatch
#print axioms AAT.AG.SpecifiedRepairLifting.actualReading_compatible
#print axioms AAT.AG.SpecifiedRepairLifting.actualReadingLift
#print axioms AAT.AG.SpecifiedRepairLifting.actualReadingLift_val
#print axioms AAT.AG.SpecifiedRepairLifting.actualReading_obstruction
#print axioms AAT.AG.SpecifiedRepairLifting.actualReading_residual
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting
