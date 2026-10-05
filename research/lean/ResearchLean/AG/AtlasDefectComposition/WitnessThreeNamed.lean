import ResearchLean.AG.AtlasDefectComposition.WitnessThreeRanks
import ResearchLean.AG.AtlasDefectComposition.NamedComparison
import ResearchLean.AG.AtlasDefectComposition.EndpointNaturality
import Formal.Util.AssertStandardAxioms
/-! # W3の実生成比較の名付きセル評価

同じSource/Law/台/セルから生成したblock比較を全三成分同型で移し、
指定されたchart・辺・面表の出力を読む。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessThree
open CanonicalResolution ResolutionInvariance TwoPhase
/-- W3aの粗実blockと孤立一chartの成分同型。 -/
def eqA₀ := fullBlockNamedEquivalence A₀ laws adequate₀ (fun _ => rfl)
  (fullSupport_edge A₀ (fun _ => rfl)) (fullSupport_face A₀ (fun _ => rfl)) label
/-- W3aの細実blockと孤立二chartの成分同型。 -/
def eqA₁ := fullBlockNamedEquivalence A₁ laws adequate₁ (fun _ => rfl)
  (fullSupport_edge A₁ (fun _ => rfl)) (fullSupport_face A₁ (fun _ => rfl)) label
/-- W3bの粗実blockと四面体表面の成分同型。 -/
def eqB₀ := fullBlockNamedEquivalence B₀ laws adequate₀ (fun _ => rfl)
  (fullSupport_edge B₀ (fun _ => rfl)) (fullSupport_face B₀ (fun _ => rfl)) label
/-- W3bの細実blockと充填三角形の成分同型。 -/
def eqB₁ := fullBlockNamedEquivalence B₁ laws adequate₁ (fun _ => rfl)
  (fullSupport_edge B₁ (fun _ => rfl)) (fullSupport_face B₁ (fun _ => rfl)) label
/-- W3aの実生成比較の名付き三成分への移送。 -/
def namedA := namedComparisonHom MA laws adequate₀ adequate₁
  (fun _ => rfl) (fullSupport_edge A₀ (fun _ => rfl)) (fullSupport_face A₀ (fun _ => rfl))
  (fun _ => rfl) (fullSupport_edge A₁ (fun _ => rfl)) (fullSupport_face A₁ (fun _ => rfl)) label
/-- W3bの実生成比較の名付き三成分への移送。 -/
def namedB := namedComparisonHom MB laws adequate₀ adequate₁
  (fun _ => rfl) (fullSupport_edge B₀ (fun _ => rfl)) (fullSupport_face B₀ (fun _ => rfl))
  (fun _ => rfl) (fullSupport_edge B₁ (fun _ => rfl)) (fullSupport_face B₁ (fun _ => rfl)) label
/-- W3aの実次数0比較は一つの値を二chartへ複製する。 -/
theorem namedA_f0 (x : Fin 1 → ℚ) (c : Fin 2) : namedA.f0 x c = x 0 :=
  namedComparisonHom_f0 MA laws adequate₀ adequate₁ _ _ _ _ _ _ label x c
/-- W3bの実次数0比較は同名の三chartを選ぶ。 -/
theorem namedB_f0 (x : Fin 4 → ℚ) (c : Fin 3) : namedB.f0 x c = x (![0,1,2] c) :=
  namedComparisonHom_f0 MB laws adequate₀ adequate₁ _ _ _ _ _ _ label x c
/-- W3bの実次数1比較は粗辺01,02,12を順序通り選ぶ。 -/
theorem namedB_f1 (x : Fin 6 → ℚ) : namedB.f1 x = ![x 0,x 1,x 3] := by
  funext e
  fin_cases e
  · exact namedComparisonHom_f1_some MB laws adequate₀ adequate₁ _ _ _ _ _ _ label x 0 0 rfl
  · exact namedComparisonHom_f1_some MB laws adequate₀ adequate₁ _ _ _ _ _ _ label x 1 1 rfl
  · exact namedComparisonHom_f1_some MB laws adequate₀ adequate₁ _ _ _ _ _ _ label x 2 3 rfl
/-- W3bの実次数2比較は粗面012を選ぶ。 -/
theorem namedB_f2 (x : Fin 4 → ℚ) (f : Fin 1) : namedB.f2 x f = x 0 :=
  namedComparisonHom_f2_some MB laws adequate₀ adequate₁ _ _ _ _ _ _ label x f 0 rfl
/-- W3bの実次数0核比較は定数値をそのまま保つ。 -/
theorem namedB_H0_constants (x : LinearMap.ker (namedComplex B₀).d0) :
    triangleConstants (oldH0Map namedB x) = tetrahedronConstants x :=
  namedB_f0 x.val 0
/-- W3bの実次数0核比較は単射かつ全射である。 -/
theorem namedB_H0_bijective : Function.Bijective (oldH0Map namedB) := by
  apply (LinearConjugation.bijective_iff (oldH0Map namedB) (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
    tetrahedronConstants triangleConstants namedB_H0_constants).mpr
  exact Function.bijective_id
end AAT.AG.AtlasDefectComposition.WitnessThree
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessThree
