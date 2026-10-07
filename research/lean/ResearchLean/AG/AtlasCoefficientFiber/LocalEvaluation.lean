import ResearchLean.AG.AtlasCoefficientFiber.LocalNaturality
import ResearchLean.AG.AtlasCoefficientFiber.PushforwardEvaluation

/-!
# G-135 A：成分式による二射の評価と次数別単射性

## Implementation notes

実Kan counit評価を原始Φ・Γ・Λ成分評価へ同定する。
各成分の原始chart・mapped辺・持ち上げ面代表元からεの単射性を導く。
H¹単射性は退化部分複体と標準完全列への接続を要する別の義務である。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 実εのchart評価は、原始細chartが属するΦ成分での同じ係数評価。 -/
theorem evaluation0_phi (z : (pushforwardComplex M A).C0)
    (c : Nc.ChartInTargetSubset A) (v : PhiChart M A c) :
    evaluation0 M A z v.1 =
      phiCoefficientEquiv M A c (z c) (CategoryTheory.ConnectedComponents.mk (.inl v)) := by
  rcases v with ⟨v, hv⟩
  cases hv
  rw [evaluation0_apply, coefficientEvaluationAt_cellIso, phiCoefficientEquiv_apply,
    Functor.mapConnectedComponents_mk]
  rfl

/-- 実εのmapped辺評価は、原始mapped辺が属するΓ成分での同じ係数評価。 -/
theorem evaluation1_gamma (z : (pushforwardComplex M A).C1)
    (e : Nc.EdgeInTargetSubset A) (v : GammaVertex M A e) :
    evaluation1 M A z v.1 =
      gammaCoefficientEquiv M A e (z e) (CategoryTheory.ConnectedComponents.mk (.inl v)) := by
  rw [evaluation1_of_some M A z v.1 e.1 v.2, coefficientEvaluationAt_cellIso,
    gammaCoefficientEquiv_apply, Functor.mapConnectedComponents_mk]
  rfl

/-- 実εのmapped面評価は、原始持ち上げΛでの同じ係数評価。 -/
theorem evaluation2_lambda (z : (pushforwardComplex M A).C2)
    (F : Nc.FaceInTargetSubset A) (f : LambdaFace M A F) :
    evaluation2 M A z f.1 = lambdaCoefficientEquiv M A F (z F) f := by
  rw [evaluation2_of_some M A z f.1 F.1 f.2, coefficientEvaluationAt_cellIso,
    lambdaCoefficientEquiv_apply]
  rfl

/-- 実ηのchart成分は、全原始Φ成分上の同じ定数関数。 -/
theorem unit0_phi (z : (Nc.targetSubsetComplex A).C0) (c : Nc.ChartInTargetSubset A)
    (k : CategoryTheory.ConnectedComponents (PhiInc M A c)) :
    phiCoefficientEquiv M A c (unit0 M A z c) k = z c := by
  rw [unit0_apply, phiCoefficientEquiv_apply, coefficientConstant_eval]

/-- 実ηの辺成分は、全原始Γ成分上の同じ定数関数。 -/
theorem unit1_gamma (z : (Nc.targetSubsetComplex A).C1) (e : Nc.EdgeInTargetSubset A)
    (k : CategoryTheory.ConnectedComponents (GammaInc M A e)) :
    gammaCoefficientEquiv M A e (unit1 M A z e) k = z e := by
  rw [unit1_apply, gammaCoefficientEquiv_apply, coefficientConstant_eval]

/-- 実ηの面成分は、全原始Λ持ち上げ上の同じ定数関数。 -/
theorem unit2_lambda (z : (Nc.targetSubsetComplex A).C2) (F : Nc.FaceInTargetSubset A)
    (f : LambdaFace M A F) :
    lambdaCoefficientEquiv M A F (unit2 M A z F) f = z F := by
  rw [unit2_apply, lambdaCoefficientEquiv_apply, coefficientConstant_eval]

/-- ε次数0の単射性。全Φ成分のchart代表元を同じ細cochainで読む。 -/
theorem evaluation0_injective : Function.Injective (evaluation0 M A) := by
  intro z w hz
  funext c
  apply (phiCoefficientEquiv M A c).injective
  funext k
  obtain ⟨v, hv⟩ := phiComponent_chart_representative M A c k
  rw [← hv, ← evaluation0_phi, ← evaluation0_phi]
  exact congrFun hz v.1

/-- ε次数1の単射性。全Γ成分のmapped辺代表元を同じ細cochainで読む。 -/
theorem evaluation1_injective : Function.Injective (evaluation1 M A) := by
  intro z w hz
  funext e
  apply (gammaCoefficientEquiv M A e).injective
  funext k
  obtain ⟨v, hv⟩ := gammaComponent_vertex_representative M A e k
  rw [← hv, ← evaluation1_gamma, ← evaluation1_gamma]
  exact congrFun hz v.1

/-- ε次数2の単射性。全Λ持ち上げを同じ細cochainで読む。 -/
theorem evaluation2_injective : Function.Injective (evaluation2 M A) := by
  intro z w hz
  funext F
  apply (lambdaCoefficientEquiv M A F).injective
  funext f
  rw [← evaluation2_lambda, ← evaluation2_lambda]
  exact congrFun hz f.1

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation0_phi
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation1_gamma
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation2_lambda
#print axioms AAT.AG.AtlasCoefficientFiber.unit0_phi
#print axioms AAT.AG.AtlasCoefficientFiber.unit1_gamma
#print axioms AAT.AG.AtlasCoefficientFiber.unit2_lambda
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation0_injective
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation1_injective
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation2_injective
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
