import ResearchLean.AG.AtlasDefectComposition.WitnessOneDirect
import ResearchLean.AG.AtlasDefectComposition.FullSupportGraph
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms

/-! # W1の実H¹とperiod商

指定されたセル表の微分の像はperiod写像の核とちょうど一致する。
これを同じ入力から生成した既存Law block H¹へ移す。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase

/-- 指定三角形のperiod。 -/
def trianglePeriod : (Fin 3 → ℚ) →ₗ[ℚ] ℚ where
  toFun z := z 0 - z 1 + z 2
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

/-- 指定二三角形の、両閉路のperiod。 -/
def twoTrianglePeriods : (Fin 6 → ℚ) →ₗ[ℚ] ℚ × ℚ where
  toFun z := (z 0 - z 1 + z 2, z 3 - z 4 + z 5)
  map_add' _ _ := by ext <;> simp <;> ring
  map_smul' _ _ := by ext <;> simp <;> ring

/-- 指定三角形の微分像はperiod核と一致する。 -/
theorem trianglePeriod_kernel :
    LinearMap.ker trianglePeriod = LinearMap.range (graphDifference triangle) := by
  ext z
  constructor
  · intro hz
    have hp : z 0 - z 1 + z 2 = 0 := hz
    refine ⟨![0, z 0, z 1], ?_⟩
    funext e
    rw [graphDifference_apply]
    fin_cases e <;> simp
    linarith
  · rintro ⟨c, rfl⟩
    change graphDifference triangle c 0 - graphDifference triangle c 1 +
      graphDifference triangle c 2 = 0
    rw [graphDifference_apply, graphDifference_apply, graphDifference_apply]
    simp

/-- 指定二三角形の微分像は二period核と一致する。 -/
theorem twoTrianglePeriods_kernel :
    LinearMap.ker twoTrianglePeriods = LinearMap.range (graphDifference twoTriangles) := by
  ext z
  constructor
  · intro hz
    have hp₀ : z 0 - z 1 + z 2 = 0 := congrArg Prod.fst hz
    have hp₁ : z 3 - z 4 + z 5 = 0 := congrArg Prod.snd hz
    refine ⟨![0, z 0, z 1, z 3, z 4], ?_⟩
    funext e
    rw [graphDifference_apply]
    fin_cases e <;> simp <;> linarith
  · rintro ⟨c, rfl⟩
    apply Prod.ext
    · change graphDifference twoTriangles c 0 - graphDifference twoTriangles c 1 +
        graphDifference twoTriangles c 2 = 0
      rw [graphDifference_apply, graphDifference_apply, graphDifference_apply]
      simp
    · change graphDifference twoTriangles c 3 - graphDifference twoTriangles c 4 +
        graphDifference twoTriangles c 5 = 0
      rw [graphDifference_apply, graphDifference_apply, graphDifference_apply]
      simp

/-- 三角形periodは辺12のcochainにより任意の有理値を実現する。 -/
theorem trianglePeriod_surjective : Function.Surjective trianglePeriod := by
  intro x; exact ⟨![0, 0, x], by simp [trianglePeriod]⟩

/-- 二periodは辺12と34のcochainで独立に実現する。 -/
theorem twoTrianglePeriods_surjective : Function.Surjective twoTrianglePeriods := by
  intro x; exact ⟨![0, 0, x.1, 0, 0, x.2], by ext <;> simp [twoTrianglePeriods]⟩

/-- 三角形の名付き辺cochain商からperiodへの同型。 -/
def triangleQuotientPeriod :
    ((Fin 3 → ℚ) ⧸ LinearMap.range (graphDifference triangle)) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ trianglePeriod_kernel.symm).trans
    (trianglePeriod.quotKerEquivOfSurjective trianglePeriod_surjective)

/-- 二三角形の名付き辺cochain商から二periodへの同型。 -/
def twoTriangleQuotientPeriods :
    ((Fin 6 → ℚ) ⧸ LinearMap.range (graphDifference twoTriangles)) ≃ₗ[ℚ] ℚ × ℚ :=
  (Submodule.quotEquivOfEq _ _ twoTrianglePeriods_kernel.symm).trans
    (twoTrianglePeriods.quotKerEquivOfSurjective twoTrianglePeriods_surjective)

/-- 三角形商同型の全代表元での評価。 -/
@[simp] theorem triangleQuotientPeriod_mk (z : Fin 3 → ℚ) :
    triangleQuotientPeriod ((LinearMap.range (graphDifference triangle)).mkQ z) =
      trianglePeriod z := rfl

/-- 二三角形商同型の全代表元での評価。 -/
@[simp] theorem twoTriangleQuotientPeriods_mk (z : Fin 6 → ℚ) :
    twoTriangleQuotientPeriods ((LinearMap.range (graphDifference twoTriangles)).mkQ z) =
      twoTrianglePeriods z := rfl

/-- W1の粗側の実Law block H¹は一つのperiodで同定される。 -/
def h1Period₀ (label : LawValueLabel laws) :
    (N₀.lawValueBlockComplex laws adequate₀ label).H1 ≃ₗ[ℚ] ℚ :=
  (fullBlockGraphH1Equiv N₀ laws adequate₀ chartSupport_univ₀ edgeSupport_univ₀ label).trans
    triangleQuotientPeriod

/-- W1の中間実Law block H¹は二つのperiodで同定される。 -/
def h1Periods₁ (label : LawValueLabel laws) :
    (N₁.lawValueBlockComplex laws adequate₁ label).H1 ≃ₗ[ℚ] ℚ × ℚ :=
  (fullBlockGraphH1Equiv N₁ laws adequate₁ chartSupport_univ₁ edgeSupport_univ₁ label).trans
    twoTriangleQuotientPeriods

/-- W1の細側の実Law block H¹は同じ第一periodで同定される。 -/
def h1Period₂ (label : LawValueLabel laws) :
    (N₂.lawValueBlockComplex laws adequate₂ label).H1 ≃ₗ[ℚ] ℚ :=
  (fullBlockGraphH1Equiv N₂ laws adequate₂ chartSupport_univ₂ edgeSupport_univ₂ label).trans
    triangleQuotientPeriod

/-- 粗側period同型の既存H¹商代表元での評価。 -/
@[simp] theorem h1Period₀_mk (label : LawValueLabel laws)
    (z : LinearMap.ker (N₀.lawValueBlockComplex laws adequate₀ label).d1) :
    h1Period₀ label ((LinearMap.range (N₀.lawValueBlockComplex laws adequate₀ label).boundaryToCycles).mkQ z) =
      trianglePeriod (fullBlockCochainEquiv laws q₀ adequate₀ N₀.edgeSupport edgeSupport_univ₀ label z.val) := rfl

/-- 中間period同型の既存H¹商代表元での評価。 -/
@[simp] theorem h1Periods₁_mk (label : LawValueLabel laws)
    (z : LinearMap.ker (N₁.lawValueBlockComplex laws adequate₁ label).d1) :
    h1Periods₁ label ((LinearMap.range (N₁.lawValueBlockComplex laws adequate₁ label).boundaryToCycles).mkQ z) =
      twoTrianglePeriods (fullBlockCochainEquiv laws q₁ adequate₁ N₁.edgeSupport edgeSupport_univ₁ label z.val) := rfl

/-- 細側period同型の既存H¹商代表元での評価。 -/
@[simp] theorem h1Period₂_mk (label : LawValueLabel laws)
    (z : LinearMap.ker (N₂.lawValueBlockComplex laws adequate₂ label).d1) :
    h1Period₂ label ((LinearMap.range (N₂.lawValueBlockComplex laws adequate₂ label).boundaryToCycles).mkQ z) =
      trianglePeriod (fullBlockCochainEquiv laws q₂ adequate₂ N₂.edgeSupport edgeSupport_univ₂ label z.val) := rfl

/-- W1の各ラベルの粗H¹次元。 -/
theorem h1_dimension₀ (label : LawValueLabel laws) :
    Module.finrank ℚ (N₀.lawValueBlockComplex laws adequate₀ label).H1 = 1 := by
  rw [(h1Period₀ label).finrank_eq]; simp

/-- W1の各ラベルの中間H¹次元。 -/
theorem h1_dimension₁ (label : LawValueLabel laws) :
    Module.finrank ℚ (N₁.lawValueBlockComplex laws adequate₁ label).H1 = 2 := by
  rw [(h1Periods₁ label).finrank_eq]; simp [Module.finrank_prod]

/-- W1の各ラベルの細H¹次元。 -/
theorem h1_dimension₂ (label : LawValueLabel laws) :
    Module.finrank ℚ (N₂.lawValueBlockComplex laws adequate₂ label).H1 = 1 := by
  rw [(h1Period₂ label).finrank_eq]; simp

end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
