import ResearchLean.AG.AtlasCoefficientFiber.PhiInterval
import ResearchLean.AG.FaceRelationSubdivision.WitnessOneDiagnostics

/-!
# W4：G134の原三角形比較のΦとliteral fiber

Implementation notes: rPlus/rMinusの同じ原Option表を選択し、唯一の退化辺cと
その二端点を読んでH¹零性を放電する。全Aを扱い、空Aも同じ構成に含む。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
variable (A : Set FaceRelationSubdivision.WitnessOne.qc.Target)

/-- 原rPlusで退化する辺はcだけである。 -/
theorem plus_vertical_name (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) (e : PhiEdge FaceRelationSubdivision.WitnessOne.rPlus A c) :
    e.1.1 = Sum.inr false := by
  have he := e.2.1
  rcases h : e.1.1 with a | b
  · rw [h, FaceRelationSubdivision.WitnessOne.rPlus_edge_old] at he
    cases he
  · cases b
    · rfl
    · rw [h, FaceRelationSubdivision.WitnessOne.rPlus_edge_e2] at he
      cases he

/-- 同じ原rMinusの退化辺もcだけである。 -/
theorem minus_vertical_name (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) (e : PhiEdge FaceRelationSubdivision.WitnessOne.rMinus A c) :
    e.1.1 = Sum.inr false := by
  have he := e.2.1
  rw [FaceRelationSubdivision.WitnessOne.rMinus_edge] at he
  rcases h : e.1.1 with a | b
  · rw [h, FaceRelationSubdivision.WitnessOne.rPlus_edge_old] at he
    cases he
  · cases b
    · rfl
    · rw [h, FaceRelationSubdivision.WitnessOne.rPlus_edge_e2] at he
      cases he

/-- 任意Aの原Φ辺は高々一つ。 -/
theorem plus_edge_subsingleton (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) :
    Subsingleton (PhiEdge FaceRelationSubdivision.WitnessOne.rPlus A c) :=
  ⟨fun e f => Subtype.ext (Subtype.ext ((plus_vertical_name A c e).trans
    (plus_vertical_name A c f).symm))⟩
/-- 面なしの場合も同じ元辺名から単一性を得る。 -/
theorem minus_edge_subsingleton (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) :
    Subsingleton (PhiEdge FaceRelationSubdivision.WitnessOne.rMinus A c) :=
  ⟨fun e f => Subtype.ext (Subtype.ext ((minus_vertical_name A c e).trans
    (minus_vertical_name A c f).symm))⟩

/-- 原cの右端はfresh、左端はoldであるため等しくない。 -/
theorem plus_endpoints_ne (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) (e : PhiEdge FaceRelationSubdivision.WitnessOne.rPlus A c) :
    phiEndpoint FaceRelationSubdivision.WitnessOne.rPlus A e true ≠ phiEndpoint FaceRelationSubdivision.WitnessOne.rPlus A e false := by
  intro hh
  have hv := congrArg (fun v => v.1.1) hh
  change FaceRelationSubdivision.WitnessOne.plus.nerve.edgeRight e.1.1 = FaceRelationSubdivision.WitnessOne.plus.nerve.edgeLeft e.1.1 at hv
  rw [plus_vertical_name A c e] at hv
  exact Sum.inr_ne_inl hv
/-- 同じ二端点は原minus表でも異なる。 -/
theorem minus_endpoints_ne (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) (e : PhiEdge FaceRelationSubdivision.WitnessOne.rMinus A c) :
    phiEndpoint FaceRelationSubdivision.WitnessOne.rMinus A e true ≠ phiEndpoint FaceRelationSubdivision.WitnessOne.rMinus A e false := by
  intro hh
  have hv := congrArg (fun v => v.1.1) hh
  change FaceRelationSubdivision.WitnessOne.minus.nerve.edgeRight e.1.1 = FaceRelationSubdivision.WitnessOne.minus.nerve.edgeLeft e.1.1 at hv
  rw [minus_vertical_name A c e] at hv
  exact Sum.inr_ne_inl hv

/-- 全Aのplus原Φで実H¹は零。 -/
theorem plus_phiH1_zero (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) :
    Subsingleton (phiComplex FaceRelationSubdivision.WitnessOne.rPlus A c).H1 := by
  letI := plus_edge_subsingleton A c
  exact phiH1_subsingleton_of_interval FaceRelationSubdivision.WitnessOne.rPlus A c (plus_endpoints_ne A c)
/-- 全Aのminus原Φで実H¹は零。 -/
theorem minus_phiH1_zero (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) :
    Subsingleton (phiComplex FaceRelationSubdivision.WitnessOne.rMinus A c).H1 := by
  letI := minus_edge_subsingleton A c
  exact phiH1_subsingleton_of_interval FaceRelationSubdivision.WitnessOne.rMinus A c (minus_endpoints_ne A c)

/-- 原κ*はplusの同じ全Φ H¹零から零射となる。 -/
theorem plus_kappaStar_zero : kappaStar FaceRelationSubdivision.WitnessOne.rPlus A = 0 := by
  letI (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) := plus_phiH1_zero A c
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl
/-- 原κ*はminusの同じ全Φ H¹零から零射となる。 -/
theorem minus_kappaStar_zero : kappaStar FaceRelationSubdivision.WitnessOne.rMinus A = 0 := by
  letI (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) := minus_phiH1_zero A c
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl
/-- literal原Rはplusで零空間。 -/
theorem plus_R_zero : Subsingleton (R FaceRelationSubdivision.WitnessOne.rPlus A) := by
  letI (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) := plus_phiH1_zero A c
  infer_instance
/-- literal原Rはminusで零空間。 -/
theorem minus_R_zero : Subsingleton (R FaceRelationSubdivision.WitnessOne.rMinus A) := by
  letI (c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A) := minus_phiH1_zero A c
  infer_instance
/-- 標準接続射から生成した同じplusのτは零。 -/
theorem plus_tau_zero : connectingTau FaceRelationSubdivision.WitnessOne.rPlus A = 0 := by
  letI := plus_R_zero A
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl
/-- 標準接続射から生成した同じminusのτは零。 -/
theorem minus_tau_zero : connectingTau FaceRelationSubdivision.WitnessOne.rMinus A = 0 := by
  letI := minus_R_zero A
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl

/-- 原chain上のκも、plusの同じΦ双対同定から零。 -/
theorem plus_kappa_zero : kappa FaceRelationSubdivision.WitnessOne.rPlus A = 0 :=
  kappa_zero_of_phiH1_zero _ A (plus_phiH1_zero A)
/-- 原chain上のκも、minusの同じΦ双対同定から零。 -/
theorem minus_kappa_zero : kappa FaceRelationSubdivision.WitnessOne.rMinus A = 0 :=
  kappa_zero_of_phiH1_zero _ A (minus_phiH1_zero A)

end AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.plus_vertical_name
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.minus_vertical_name
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.plus_edge_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.minus_edge_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.plus_endpoints_ne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.minus_endpoints_ne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.plus_phiH1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.minus_phiH1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.plus_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.minus_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.plus_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.minus_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.plus_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.minus_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.plus_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle.minus_kappa_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFourTriangle
