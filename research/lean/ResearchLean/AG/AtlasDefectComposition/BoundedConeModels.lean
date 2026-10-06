import ResearchLean.AG.AtlasDefectComposition.FiniteConeFiltration
import Formal.Util.AssertStandardAxioms
/-! # 有限段モデルの有限次元性と次数範囲

Implementation notes: 各次数の有限次元性と零対象は元の diagram から導く。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
open scoped ZeroObject
namespace AAT.AG.AtlasDefectComposition.MappingCylinder
universe w
variable {K L : CochainComplex (ModuleCat.{w} ℚ) ℤ} (φ : K ⟶ L)
/-- 元の三つの次数が零ならモデルの同じ次数も零対象である。 -/
theorem degree_isZero (m : ℤ) (hK : IsZero (K.X m))
    (hK' : IsZero (K.X (m+1))) (hL : IsZero (L.X m)) : IsZero ((model φ).X m) := by
  apply IsZero.of_iso _ (HomologicalComplex.biprodXIso (mappingCone (𝟙 K)) L m)
  apply (biprod_isZero_iff _ _).mpr
  exact ⟨(mappingCone.isZero_X_iff (𝟙 K) m).mpr ⟨hK',hK⟩,hL⟩
end MappingCylinder
namespace ConeTower
universe w
variable (C : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ)
/-- 元の全次数が有限次元なら実累積錐も全次数で有限次元である。 -/
theorem coneFiniteDimensional (hfd : ∀ i m, FiniteDimensional ℚ ((C.obj i).X m)) (i : ℕ) (m : ℤ) :
    FiniteDimensional ℚ ((cone C i).X m) := by
  letI := hfd 0 (m+1)
  letI := hfd i m
  exact coneDegreeFiniteDimensional _ _
/-- 各モデルの全次数は元の有限次元性から帰納的に有限次元となる。 -/
theorem modelFiniteDimensional (hfd : ∀ i m, FiniteDimensional ℚ ((C.obj i).X m)) (i : ℕ) (m : ℤ) :
    FiniteDimensional ℚ ((model C i).X m) := by
  induction i generalizing m with
  | zero =>
    have h₀ : IsZero ((model C 0).X m) :=
      Functor.map_isZero (HomologicalComplex.eval _ _ m) (isZero_zero _)
    letI := ModuleCat.subsingleton_of_isZero h₀
    infer_instance
  | succ i ih =>
    letI := ih m
    letI := ih (m+1)
    letI := coneFiniteDimensional C hfd (i+1) m
    exact MappingCylinder.degreeFiniteDimensional (modelArrow C i) m
/-- 三項の原始 diagram の実累積錐の次数範囲。 -/
theorem coneBounded (hz : ∀ i m, m < 0 ∨ 2 < m → IsZero ((C.obj i).X m))
    (i : ℕ) (m : ℤ) (hm : m < -1 ∨ 2 < m) : IsZero ((cone C i).X m) := by
  exact (mappingCone.isZero_X_iff _ m).mpr
    ⟨hz 0 (m+1) (by omega),hz i m (by omega)⟩
/-- 第 i 段モデルは次数 −i から 2 に収まる有限複体である。 -/
theorem modelBounded (hz : ∀ i m, m < 0 ∨ 2 < m → IsZero ((C.obj i).X m))
    (i : ℕ) (m : ℤ) (hm : m < -(i : ℤ) ∨ 2 < m) : IsZero ((model C i).X m) := by
  induction i generalizing m with
  | zero => exact Functor.map_isZero (HomologicalComplex.eval _ _ m) (isZero_zero _)
  | succ i ih =>
    exact MappingCylinder.degree_isZero (modelArrow C i) m
      (ih m (by omega)) (ih (m+1) (by omega)) (coneBounded C hz (i+1) m (by omega))
end ConeTower
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
