import ResearchLean.AG.AtlasCoefficientFiber.PushforwardUnit

/-!
# G-135 A：右Kan counitの有理評価

## Implementation notes

同じpointwise右KanのcounitをULiftの有理係数へ同定し、細セルの評価を作る。
評価を実比較uの因子化等号から選ぶ案は、評価とunitの独立生成を失うため採らない。
対象等号で輸送した評価の自然性も、標準counitの自然性から証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory
universe u
variable {J K : Type u} [Category.{u} J] [Category.{u} K]

/-- counitから独立に生成する、細セルでの有理線形評価。 -/
def coefficientEvaluation (φ : J ⥤ K) (j : J) :
    (coefficientPushforward φ).obj (φ.obj j) →ₗ[ℚ] ℚ :=
  (ULift.moduleEquiv : ULift.{u} ℚ ≃ₗ[ℚ] ℚ).toLinearMap.comp
    ((coefficientCounit φ).app j).hom
/-- 有理評価は標準counitのULift値のdownである。 -/
theorem coefficientEvaluation_apply (φ : J ⥤ K) (j : J)
    (x : (coefficientPushforward φ).obj (φ.obj j)) :
    coefficientEvaluation φ j x = ((coefficientCounit φ).app j x).down := rfl
/-- 同じ右Kanの係数射と細incidenceに対する評価の可換性。 -/
theorem coefficientEvaluation_naturality (φ : J ⥤ K) {i j : J} (f : i ⟶ j)
    (x : (coefficientPushforward φ).obj (φ.obj i)) :
    coefficientEvaluation φ j ((coefficientPushforward φ).map (φ.map f) x) =
      coefficientEvaluation φ i x := by
  have h := (coefficientCounit φ).naturality f
  have hx := congrArg (fun m : (coefficientPushforward φ).obj (φ.obj i) ⟶ RationalObject =>
    (m x).down) h
  simpa [coefficientEvaluation_apply, constantRational_map] using hx

/-- 成分上の定数写像を細セルで評価すると元の有理数を返す。 -/
theorem coefficientEvaluation_constant (φ : J ⥤ K) (j : J) (q : ℚ) :
    coefficientEvaluation φ j (coefficientConstant φ (φ.obj j) q) = q := by
  rw [coefficientEvaluation_apply, coefficientCounit_eval, coefficientConstant_eval]
/-- carrier対象等号の輸送を含む細セル評価。 -/
def coefficientEvaluationAt (φ : J ⥤ K) (j : J) {k : K} (hj : φ.obj j = k) :
    (coefficientPushforward φ).obj k →ₗ[ℚ] ℚ :=
  (coefficientEvaluation φ j).comp ((coefficientPushforward φ).map (eqToHom hj.symm)).hom

/-- 原始incidenceのcarrier等号に沿う評価の自然性。可換等号の証明は適用側の義務。 -/
theorem coefficientEvaluationAt_naturality (φ : J ⥤ K) {i j : J} (f : i ⟶ j)
    {k l : K} (hi : φ.obj i = k) (hj : φ.obj j = l) (b : k ⟶ l)
    (hb : φ.map f ≫ eqToHom hj = eqToHom hi ≫ b)
    (x : (coefficientPushforward φ).obj k) :
    coefficientEvaluationAt φ j hj ((coefficientPushforward φ).map b x) =
      coefficientEvaluationAt φ i hi x := by
  cases hi
  cases hj
  have hb' : φ.map f = b := by simpa using hb
  subst b
  simpa [coefficientEvaluationAt] using coefficientEvaluation_naturality φ f x

/-- 対象輸送を含む評価でも定数写像の値は元の有理数である。 -/
theorem coefficientEvaluationAt_constant (φ : J ⥤ K) (j : J) {k : K}
    (hj : φ.obj j = k) (q : ℚ) :
    coefficientEvaluationAt φ j hj (coefficientConstant φ k q) = q := by
  cases hj
  simpa [coefficientEvaluationAt] using coefficientEvaluation_constant φ j q

/-- carrier等号で輸送したcounit評価は、同じ恒等輸送comma対象の成分評価である。 -/
theorem coefficientEvaluationAt_cellIso (φ : J ⥤ K) (j : J) {k : K}
    (hj : φ.obj j = k) (z : (coefficientPushforward φ).obj k) :
    coefficientEvaluationAt φ j hj z =
      ((coefficientCellIso φ k).hom z
        (CategoryTheory.ConnectedComponents.mk (StructuredArrow.mk (eqToHom hj.symm)))).down := by
  cases hj
  simpa [coefficientEvaluationAt, coefficientEvaluation_apply] using
    congrArg ULift.down (coefficientCounit_eval φ j z)

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientEvaluation
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientEvaluation_apply
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientEvaluation_naturality
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientEvaluation_constant
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientEvaluationAt
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientEvaluationAt_naturality
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientEvaluationAt_constant
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientEvaluationAt_cellIso
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
