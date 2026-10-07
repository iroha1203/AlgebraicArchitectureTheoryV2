import ResearchLean.AG.AtlasCoefficientFiber.PushforwardCoefficient

/-!
# G-135 A：順像係数のセル複体

## Implementation notes

各粗セルにおける実順像係数の直積を取り、係数射の端点差・三辺和で微分を作る。
商chainの双対をPの定義にする案は、独立した順像から商双対への同定義務を消すため採らない。
一般の係数functorに対するAPIを先に証明し、実Mの右Kanへ適用する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision CategoryTheory TwoPhase
universe u
variable {Source : Type u} {q : Reading Source}
variable (N : TargetSupportedNerve q) (A : Set q.Target)
variable (G : Inc N A ⥤ ModuleCat.{u} ℚ)

/-- chart上の係数直積。 -/
abbrev CoefficientC0 := ∀ c : N.ChartInTargetSubset A, G.obj (.chart c)
/-- 辺上の係数直積。 -/
abbrev CoefficientC1 := ∀ e : N.EdgeInTargetSubset A, G.obj (.edge e)
/-- 面上の係数直積。 -/
abbrev CoefficientC2 := ∀ f : N.FaceInTargetSubset A, G.obj (.face f)

/-- 係数射による端点差分。 -/
def coefficientD0 : CoefficientC0 N A G →ₗ[ℚ] CoefficientC1 N A G where
  toFun z e := G.map (IncHom.chartEdge (N.targetSubsetEdgeRight A e) e true rfl)
      (z (N.targetSubsetEdgeRight A e)) -
    G.map (IncHom.chartEdge (N.targetSubsetEdgeLeft A e) e false rfl)
      (z (N.targetSubsetEdgeLeft A e))
  map_add' x y := by
    funext e
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' a x := by
    funext e
    simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

/-- 係数射による三辺の符号付き和。 -/
def coefficientD1 : CoefficientC1 N A G →ₗ[ℚ] CoefficientC2 N A G where
  toFun z f := G.map (IncHom.edgeFace (N.targetSubsetFaceEdge0 A f) f 0 rfl)
      (z (N.targetSubsetFaceEdge0 A f)) -
    G.map (IncHom.edgeFace (N.targetSubsetFaceEdge1 A f) f 1 rfl)
      (z (N.targetSubsetFaceEdge1 A f)) +
    G.map (IncHom.edgeFace (N.targetSubsetFaceEdge2 A f) f 2 rfl)
      (z (N.targetSubsetFaceEdge2 A f))
  map_add' x y := by
    funext f
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' a x := by
    funext f
    simp only [Pi.smul_apply, map_smul, smul_sub, smul_add, RingHom.id_apply]

/-- chart等号の輸送は依存したchart cochainの値の輸送に一致する。 -/
theorem coefficient_chart_transport (z : CoefficientC0 N A G)
    {c d : N.ChartInTargetSubset A} (he : c = d) :
    G.map (eqToHom (congrArg Inc.chart he)) (z c) = z d := by
  cases he
  simp

/-- 二経路を原始頂点位置へ正規化したincidence等号。 -/
theorem endpoint_edge_normal (f : N.FaceInTargetSubset A) (i : Fin 3) (s : Bool) :
    IncHom.chartEdge (edgeEndpoint N A (faceEdge N A f i) s) (faceEdge N A f i) s rfl ≫
      IncHom.edgeFace (faceEdge N A f i) f i rfl =
    eqToHom (congrArg Inc.chart (edgeEndpoint_faceEdge N A f i s)) ≫
      IncHom.chartFace (faceVertex N A f (endpointPosition i s)) f (endpointPosition i s) rfl := by
  apply incHomCode_injective
  rw [incHomCode_eqToHom_comp]
  rfl

/-- 係数の各二経路による評価は、同じ原始頂点の評価へ一致する。 -/
theorem coefficient_endpoint_edge_eval (z : CoefficientC0 N A G)
    (f : N.FaceInTargetSubset A) (i : Fin 3) (s : Bool) :
    G.map (IncHom.edgeFace (faceEdge N A f i) f i rfl)
      (G.map (IncHom.chartEdge (edgeEndpoint N A (faceEdge N A f i) s)
        (faceEdge N A f i) s rfl) (z (edgeEndpoint N A (faceEdge N A f i) s))) =
    G.map (IncHom.chartFace (faceVertex N A f (endpointPosition i s)) f
      (endpointPosition i s) rfl) (z (faceVertex N A f (endpointPosition i s))) := by
  have he := congrArg G.map (endpoint_edge_normal N A f i s)
  have hv := congrArg (fun g => g (z (edgeEndpoint N A (faceEdge N A f i) s))) he
  simp only [Functor.map_comp, ModuleCat.comp_apply] at hv
  have ht := coefficient_chart_transport N A G z (edgeEndpoint_faceEdge N A f i s)
  erw [ht] at hv
  exact hv

/-- 係数微分の二回合成は原始三角形の三頂点で相殺する。 -/
theorem coefficient_d1_comp_d0 (z : CoefficientC0 N A G) :
    coefficientD1 N A G (coefficientD0 N A G z) = 0 := by
  funext f
  simp only [coefficientD1, coefficientD0, LinearMap.coe_mk, AddHom.coe_mk,
    map_sub, Pi.zero_apply]
  erw [coefficient_endpoint_edge_eval N A G z f 0 true,
    coefficient_endpoint_edge_eval N A G z f 0 false,
    coefficient_endpoint_edge_eval N A G z f 1 true,
    coefficient_endpoint_edge_eval N A G z f 1 false,
    coefficient_endpoint_edge_eval N A G z f 2 true,
    coefficient_endpoint_edge_eval N A G z f 2 false]
  simp [endpointPosition]

/-- 粗セルの係数直積とincidence微分から作る有限三項複体。 -/
def coefficientComplex [∀ σ : Inc N A, FiniteDimensional ℚ (G.obj σ)] :
    ThreeCochainComplex ℚ where
  C0 := CoefficientC0 N A G
  C1 := CoefficientC1 N A G
  C2 := CoefficientC2 N A G
  d0 := coefficientD0 N A G
  d1 := coefficientD1 N A G
  d1_comp_d0 := coefficient_d1_comp_d0 N A G

/-- 係数複体の第一微分の定義所有者API。 -/
theorem coefficientComplex_d0 [∀ σ : Inc N A, FiniteDimensional ℚ (G.obj σ)] :
    (coefficientComplex N A G).d0 = coefficientD0 N A G := rfl

/-- 係数複体の第二微分の定義所有者API。 -/
theorem coefficientComplex_d1 [∀ σ : Inc N A, FiniteDimensional ℚ (G.obj σ)] :
    (coefficientComplex N A G).d1 = coefficientD1 N A G := rfl

/-- 係数複体の第一微分のセル評価。下流は端点差の定義を展開せず使う。 -/
theorem coefficientComplex_d0_apply [∀ σ : Inc N A, FiniteDimensional ℚ (G.obj σ)]
    (z : (coefficientComplex N A G).C0) (e : N.EdgeInTargetSubset A) :
    (coefficientComplex N A G).d0 z e =
      G.map (IncHom.chartEdge (N.targetSubsetEdgeRight A e) e true rfl)
        (z (N.targetSubsetEdgeRight A e)) -
      G.map (IncHom.chartEdge (N.targetSubsetEdgeLeft A e) e false rfl)
        (z (N.targetSubsetEdgeLeft A e)) := rfl

/-- 係数複体の第二微分のセル評価。下流は三辺和の定義を展開せず使う。 -/
theorem coefficientComplex_d1_apply [∀ σ : Inc N A, FiniteDimensional ℚ (G.obj σ)]
    (z : (coefficientComplex N A G).C1) (f : N.FaceInTargetSubset A) :
    (coefficientComplex N A G).d1 z f =
      G.map (IncHom.edgeFace (N.targetSubsetFaceEdge0 A f) f 0 rfl)
        (z (N.targetSubsetFaceEdge0 A f)) -
      G.map (IncHom.edgeFace (N.targetSubsetFaceEdge1 A f) f 1 rfl)
        (z (N.targetSubsetFaceEdge1 A f)) +
      G.map (IncHom.edgeFace (N.targetSubsetFaceEdge2 A f) f 2 rfl)
        (z (N.targetSubsetFaceEdge2 A f)) := rfl

variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}

/-- 原始Mの独立した右Kan順像から生成するP。商chainの双対を入力にしない。 -/
def pushforwardComplex (M : IncidenceSupportedComparison qc qf h Nc Nf)
    (A : Set qc.Target) : ThreeCochainComplex ℚ :=
  coefficientComplex Nc A (pushforwardCoefficients M A)

/-- 実順像複体Pの第一微分を同じ係数射の端点差として評価する公開API。 -/
theorem pushforwardComplex_d0_apply (M : IncidenceSupportedComparison qc qf h Nc Nf)
    (A : Set qc.Target) (z : (pushforwardComplex M A).C0) (e : Nc.EdgeInTargetSubset A) :
    (pushforwardComplex M A).d0 z e =
      (pushforwardCoefficients M A).map
        (IncHom.chartEdge (Nc.targetSubsetEdgeRight A e) e true rfl)
        (z (Nc.targetSubsetEdgeRight A e)) -
      (pushforwardCoefficients M A).map
        (IncHom.chartEdge (Nc.targetSubsetEdgeLeft A e) e false rfl)
        (z (Nc.targetSubsetEdgeLeft A e)) :=
  coefficientComplex_d0_apply Nc A (pushforwardCoefficients M A) z e

/-- 実順像複体Pの第二微分を同じ係数射の三辺和として評価する公開API。 -/
theorem pushforwardComplex_d1_apply (M : IncidenceSupportedComparison qc qf h Nc Nf)
    (A : Set qc.Target) (z : (pushforwardComplex M A).C1) (f : Nc.FaceInTargetSubset A) :
    (pushforwardComplex M A).d1 z f =
      (pushforwardCoefficients M A).map
        (IncHom.edgeFace (Nc.targetSubsetFaceEdge0 A f) f 0 rfl)
        (z (Nc.targetSubsetFaceEdge0 A f)) -
      (pushforwardCoefficients M A).map
        (IncHom.edgeFace (Nc.targetSubsetFaceEdge1 A f) f 1 rfl)
        (z (Nc.targetSubsetFaceEdge1 A f)) +
      (pushforwardCoefficients M A).map
        (IncHom.edgeFace (Nc.targetSubsetFaceEdge2 A f) f 2 rfl)
        (z (Nc.targetSubsetFaceEdge2 A f)) :=
  coefficientComplex_d1_apply Nc A (pushforwardCoefficients M A) z f

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.CoefficientC0
#print axioms AAT.AG.AtlasCoefficientFiber.CoefficientC1
#print axioms AAT.AG.AtlasCoefficientFiber.CoefficientC2
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientD0
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientD1
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_chart_transport
#print axioms AAT.AG.AtlasCoefficientFiber.endpoint_edge_normal
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_endpoint_edge_eval
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_d1_comp_d0
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientComplex
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientComplex_d0
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientComplex_d1
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardComplex
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientComplex_d0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientComplex_d1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardComplex_d0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardComplex_d1_apply
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
