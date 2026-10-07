import ResearchLean.AG.AtlasCoefficientFiber.CoefficientEvaluation
import ResearchLean.AG.AtlasDefectComposition.GeneratedComposition

/-!
# G-135 A：順像から細セルへの評価

## Implementation notes

chartとmapped辺/面では独立した右Kanのcounitを評価し、退化辺/面では零を置く。
粗セルの成分を元の有理値へ戻すことで、既存比較の全三次数生成式へ照合する。
実比較uをεの定義に用いる案は、二射の独立した構成を失うため採らない。
mixed面の適合と両微分の可換性は原始carrier射から証明する義務である。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- counitによるchart評価。原始chart像だけから作る次数0の線形写像。 -/
def evaluation0 : (pushforwardComplex M A).C0 →ₗ[ℚ]
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C0 :=
  LinearMap.pi fun c =>
    (coefficientEvaluationAt (Carrier.preimageFunctor M A) (.chart c) (Carrier.preimageFunctor_obj_chart M A c)).comp
      (LinearMap.proj (Carrier.chart M A _ (fun _ ht => ht) c))

/-- mapped辺のcounit評価と退化辺の零から生成する次数1の線形写像。 -/
def evaluation1 : (pushforwardComplex M A).C1 →ₗ[ℚ]
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1 :=
  LinearMap.pi fun e => match he : M.edgeMap e.1 with
    | none => 0
    | some a =>
      (coefficientEvaluationAt (Carrier.preimageFunctor M A) (.edge e)
        (Carrier.preimageFunctor_obj_edge_of_some M A e a he)).comp
        (LinearMap.proj (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he))

/-- mapped面のcounit評価と退化面の零から生成する次数2の線形写像。 -/
def evaluation2 : (pushforwardComplex M A).C2 →ₗ[ℚ]
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C2 :=
  LinearMap.pi fun f => match hf : M.faceMap f.1 with
    | none => 0
    | some a =>
      (coefficientEvaluationAt (Carrier.preimageFunctor M A) (.face f)
        (Carrier.preimageFunctor_obj_face_of_some M A f a hf)).comp
        (LinearMap.proj (M.targetSubsetFaceMap A _ (fun _ ht => ht) f a hf))

/-- chartでの評価の公開生成式。 -/
theorem evaluation0_apply (z : (pushforwardComplex M A).C0)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) :
    evaluation0 M A z c = coefficientEvaluationAt (Carrier.preimageFunctor M A) (.chart c)
      (Carrier.preimageFunctor_obj_chart M A c) (z (Carrier.chart M A _ (fun _ ht => ht) c)) := rfl

/-- 原始Option像がnoneの細辺での評価は零。 -/
theorem evaluation1_of_none (z : (pushforwardComplex M A).C1)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (he : M.edgeMap e.1 = none) : evaluation1 M A z e = 0 := by
  unfold evaluation1
  erw [LinearMap.pi_apply]
  split <;> simp_all

/-- mapped細辺での評価は同じcarrier辺におけるcounit値。 -/
theorem evaluation1_of_some (z : (pushforwardComplex M A).C1)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) :
    evaluation1 M A z e = coefficientEvaluationAt (Carrier.preimageFunctor M A) (.edge e)
      (Carrier.preimageFunctor_obj_edge_of_some M A e a he)
      (z (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he)) := by
  unfold evaluation1
  erw [LinearMap.pi_apply]
  split
  · rename_i hn
    cases he.symm.trans hn
  · rename_i b hb
    have hab : b = a := Option.some.inj (hb.symm.trans he)
    subst b
    rfl

/-- 原始Option像がnoneの細面での評価は零。 -/
theorem evaluation2_of_none (z : (pushforwardComplex M A).C2)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (hf : M.faceMap f.1 = none) : evaluation2 M A z f = 0 := by
  unfold evaluation2
  erw [LinearMap.pi_apply]
  split <;> simp_all

/-- mapped細面での評価は同じcarrier面におけるcounit値。 -/
theorem evaluation2_of_some (z : (pushforwardComplex M A).C2)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some a) :
    evaluation2 M A z f = coefficientEvaluationAt (Carrier.preimageFunctor M A) (.face f)
      (Carrier.preimageFunctor_obj_face_of_some M A f a hf)
      (z (M.targetSubsetFaceMap A _ (fun _ ht => ht) f a hf)) := by
  unfold evaluation2
  erw [LinearMap.pi_apply]
  split
  · rename_i hn
    cases hf.symm.trans hn
  · rename_i b hb
    have hab : b = a := Option.some.inj (hb.symm.trans hf)
    subst b
    rfl

/-- 独立に生成した二写像のchart合成は既存原始比較の生成式に一致する。 -/
theorem evaluation0_unit (z : (Nc.targetSubsetComplex A).C0) :
    evaluation0 M A (unit0 M A z) = M.targetSubsetPullback0 A _ (fun _ ht => ht) z := by
  funext c
  rw [evaluation0_apply, unit0_apply]
  erw [coefficientEvaluationAt_constant]
  rw [M.targetSubsetPullback0_apply]
  rfl

/-- 独立に生成した二写像の辺合成は既存原始比較の生成式に一致する。 -/
theorem evaluation1_unit (z : (Nc.targetSubsetComplex A).C1) :
    evaluation1 M A (unit1 M A z) = M.targetSubsetPullback1 A _ (fun _ ht => ht) z := by
  funext e
  cases he : M.edgeMap e.1 with
  | none =>
    rw [evaluation1_of_none M A _ e he, M.targetSubsetPullback1_apply,
      M.targetSubsetEdgeMapOption_eq_none A _ (fun _ ht => ht) e he]
    rfl
  | some a =>
    rw [evaluation1_of_some M A _ e a he, unit1_apply]
    erw [coefficientEvaluationAt_constant]
    rw [M.targetSubsetPullback1_apply,
      M.targetSubsetEdgeMapOption_eq_some A _ (fun _ ht => ht) e a he]
    rfl

/-- 独立に生成した二写像の面合成は既存原始比較の生成式に一致する。 -/
theorem evaluation2_unit (z : (Nc.targetSubsetComplex A).C2) :
    evaluation2 M A (unit2 M A z) = M.targetSubsetPullback2 A _ (fun _ ht => ht) z := by
  funext f
  cases hf : M.faceMap f.1 with
  | none =>
    rw [evaluation2_of_none M A _ f hf, M.targetSubsetPullback2_apply,
      M.targetSubsetFaceMapOption_eq_none A _ (fun _ ht => ht) f hf]
    rfl
  | some a =>
    rw [evaluation2_of_some M A _ f a hf, unit2_apply]
    erw [coefficientEvaluationAt_constant]
    rw [M.targetSubsetPullback2_apply,
      M.targetSubsetFaceMapOption_eq_some A _ (fun _ ht => ht) f a hf]
    rfl

/-- mapped辺の同じ端点位置での係数評価は細chartのcounit評価に一致する。 -/
theorem evaluation_endpoint_of_some (z : (pushforwardComplex M A).C0)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (s : Bool)
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) :
    coefficientEvaluationAt (Carrier.preimageFunctor M A) (.edge e)
        (Carrier.preimageFunctor_obj_edge_of_some M A e a he)
        ((pushforwardCoefficients M A).map
          (IncHom.chartEdge
            (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s)
            (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s rfl)
          (z (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s))) =
      evaluation0 M A z (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s) := by
  have hc : Carrier.chart M A _ (fun _ ht => ht)
      (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s) =
      edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s := by
    cases s
    · exact M.targetSubsetChartMap_edgeLeft A _ _ e a he
    · exact M.targetSubsetChartMap_edgeRight A _ _ e a he
  have hh := coefficientEvaluationAt_naturality (Carrier.preimageFunctor M A)
    (IncHom.chartEdge (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s) e s rfl)
    (Carrier.preimageFunctor_obj_chart M A _)
    (Carrier.preimageFunctor_obj_edge_of_some M A e a he)
    (IncHom.chartEdge (Carrier.chart M A _ (fun _ ht => ht)
      (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s))
      (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s hc)
    (Carrier.preimageFunctor_endpoint_of_some M A e s a he)
    (z (Carrier.chart M A _ (fun _ ht => ht)
      (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s)))
  erw [coefficient_endpoint_chart_eval Nc A (pushforwardCoefficients M A) z _ s _ hc] at hh
  exact hh.trans (evaluation0_apply M A z _).symm

/-- 退化辺の両端点評価は同じcarrier chartの係数評価へ一致する。 -/
theorem evaluation_endpoint_of_none (z : (pushforwardComplex M A).C0)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (s : Bool)
    (he : M.edgeMap e.1 = none) :
    coefficientEvaluationAt (Carrier.preimageFunctor M A) (.edge e)
        (Carrier.preimageFunctor_obj_edge_of_none M A e he)
        (z (Carrier.chart M A _ (fun _ ht => ht)
          (Nf.targetSubsetEdgeLeft (comparisonFactor qc qf h ⁻¹' A) e))) =
      evaluation0 M A z (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s) := by
  have hc : Carrier.chart M A _ (fun _ ht => ht)
      (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s) =
      Carrier.chart M A _ (fun _ ht => ht)
        (Nf.targetSubsetEdgeLeft (comparisonFactor qc qf h ⁻¹' A) e) := by
    cases s
    · rfl
    · exact (M.targetSubsetChartMap_edgeLeft_eq_right_of_none A _ _ e he).symm
  have hh := coefficientEvaluationAt_naturality (Carrier.preimageFunctor M A)
    (IncHom.chartEdge (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s) e s rfl)
    (Carrier.preimageFunctor_obj_chart M A _)
    (Carrier.preimageFunctor_obj_edge_of_none M A e he)
    (eqToHom (congrArg Inc.chart hc))
    (Carrier.preimageFunctor_endpoint_of_none M A e s he)
    (z (Carrier.chart M A _ (fun _ ht => ht)
      (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s)))
  erw [coefficient_chart_transport Nc A (pushforwardCoefficients M A) z hc] at hh
  exact hh.trans (evaluation0_apply M A z _).symm

/-- 原始mapped/退化分類とcounit自然性から評価の第一cochain条件を証明する。 -/
theorem evaluation_comm0 (z : (pushforwardComplex M A).C0) :
    evaluation1 M A ((pushforwardComplex M A).d0 z) =
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d0 (evaluation0 M A z) := by
  funext e
  cases he : M.edgeMap e.1 with
  | none =>
    rw [evaluation1_of_none M A _ e he, Nf.targetSubsetComplex_d0_apply]
    have hl := evaluation_endpoint_of_none M A z e false he
    have hr := evaluation_endpoint_of_none M A z e true he
    erw [← hr, ← hl]
    simp
  | some a =>
    rw [evaluation1_of_some M A _ e a he, pushforwardComplex_d0_apply, map_sub,
      Nf.targetSubsetComplex_d0_apply]
    erw [evaluation_endpoint_of_some M A z e true a he,
      evaluation_endpoint_of_some M A z e false a he]
    rfl

/-- mapped面の各辺評価は、右Kanの同じ粗辺面射に沿って可換である。 -/
theorem evaluation_face_edge_of_some (z : (pushforwardComplex M A).C1)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    coefficientEvaluationAt (Carrier.preimageFunctor M A) (.face f)
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)
        ((pushforwardCoefficients M A).map
          (IncHom.edgeFace
            (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
            (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl)
          (z (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i))) =
      evaluation1 M A z (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) := by
  have hh := coefficientEvaluationAt_naturality (Carrier.preimageFunctor M A)
    (IncHom.edgeFace (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) f i rfl)
    ((Carrier.preimageFunctor_obj_edge M A _).trans (Carrier.edge_of_face_some M A _ _ f F hf i))
    (Carrier.preimageFunctor_obj_face_of_some M A f F hf)
    (IncHom.edgeFace (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
      (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl)
    (Carrier.preimageFunctor_face_edgeHom_of_some M A f F hf i)
    (z (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i))
  exact hh.trans (evaluation1_of_some M A z _ _
    (Carrier.preimageFunctor_face_edgeMap_of_some M A f F hf i)).symm

/-- 左辺退化型のmapped二辺は同じ面carrierの係数を評価する。 -/
theorem evaluation_face_edge_of_mixed_left (z : (pushforwardComplex M A).C1)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e)
    (i : Fin 3) (hi : i ≠ 0)
    (he : M.edgeMap (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i).1 = some e) :
    coefficientEvaluationAt (Carrier.preimageFunctor M A) (.face f)
        ((Carrier.preimageFunctor_obj_face M A f).trans
          (Carrier.face_of_mixed_left M A _ _ f hf h0 e h1))
        (z (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge1 _ f) e h1)) =
      evaluation1 M A z (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) := by
  have ht : M.targetSubsetEdgeMap A _ (fun _ ht => ht)
      (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) e he =
        M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge1 _ f) e h1 := by
    apply Subtype.ext
    rfl
  have hh := coefficientEvaluationAt_naturality (Carrier.preimageFunctor M A)
    (IncHom.edgeFace (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) f i rfl)
    (Carrier.preimageFunctor_obj_edge_of_some M A _ e he)
    ((Carrier.preimageFunctor_obj_face M A f).trans
      (Carrier.face_of_mixed_left M A _ _ f hf h0 e h1))
    (eqToHom (congrArg Inc.edge ht))
    (Carrier.preimageFunctor_face_edgeHom_of_mixed_left M A f hf e h0 h1 i hi he)
    (z (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
      (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) e he))
  erw [coefficient_edge_transport Nc A (pushforwardCoefficients M A) z ht] at hh
  exact hh.trans (evaluation1_of_some M A z _ e he).symm

/-- 第三辺退化型のmapped二辺は同じ面carrierの係数を評価する。 -/
theorem evaluation_face_edge_of_mixed_right (z : (pushforwardComplex M A).C1)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some e)
    (i : Fin 3) (hi : i ≠ 2)
    (he : M.edgeMap (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i).1 = some e) :
    coefficientEvaluationAt (Carrier.preimageFunctor M A) (.face f)
        ((Carrier.preimageFunctor_obj_face M A f).trans
          (Carrier.face_of_mixed_right M A _ _ f hf e h0))
        (z (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge0 _ f) e h0)) =
      evaluation1 M A z (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) := by
  have ht : M.targetSubsetEdgeMap A _ (fun _ ht => ht)
      (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) e he =
        M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge0 _ f) e h0 := by
    apply Subtype.ext
    rfl
  have hh := coefficientEvaluationAt_naturality (Carrier.preimageFunctor M A)
    (IncHom.edgeFace (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) f i rfl)
    (Carrier.preimageFunctor_obj_edge_of_some M A _ e he)
    ((Carrier.preimageFunctor_obj_face M A f).trans
      (Carrier.face_of_mixed_right M A _ _ f hf e h0))
    (eqToHom (congrArg Inc.edge ht))
    (Carrier.preimageFunctor_face_edgeHom_of_mixed_right M A f hf e h0 i hi he)
    (z (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
      (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) e he))
  erw [coefficient_edge_transport Nc A (pushforwardCoefficients M A) z ht] at hh
  exact hh.trans (evaluation1_of_some M A z _ e he).symm

/-- 全退化型の符号付き相殺とcounit自然性から第二cochain条件を証明する。 -/
theorem evaluation_comm1 (z : (pushforwardComplex M A).C1) :
    evaluation2 M A ((pushforwardComplex M A).d1 z) =
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1 (evaluation1 M A z) := by
  funext f
  cases hf : M.faceMap f.1 with
  | some F =>
    rw [evaluation2_of_some M A _ f F hf, pushforwardComplex_d1_apply,
      map_add, map_sub, Nf.targetSubsetComplex_d1_apply]
    erw [evaluation_face_edge_of_some M A z f F hf 0,
      evaluation_face_edge_of_some M A z f F hf 1,
      evaluation_face_edge_of_some M A z f F hf 2]
    rfl
  | none =>
    rw [evaluation2_of_none M A _ f hf, Nf.targetSubsetComplex_d1_apply]
    rcases degenerate_face_cases M f.1 hf with hv | hl | hr
    · rcases hv with ⟨h0, h1, h2⟩
      erw [evaluation1_of_none M A z (Nf.targetSubsetFaceEdge0 _ f) h0,
        evaluation1_of_none M A z (Nf.targetSubsetFaceEdge1 _ f) h1,
        evaluation1_of_none M A z (Nf.targetSubsetFaceEdge2 _ f) h2]
      simp
    · rcases hl with ⟨e, h0, h1, h2⟩
      have he1 := evaluation_face_edge_of_mixed_left M A z f hf e h0 h1 1 (by decide) h1
      have he2 := evaluation_face_edge_of_mixed_left M A z f hf e h0 h1 2 (by decide) h2
      erw [evaluation1_of_none M A z _ h0, ← he1, ← he2]
      simp
    · rcases hr with ⟨e, h0, h1, h2⟩
      have he0 := evaluation_face_edge_of_mixed_right M A z f hf e h0 0 (by decide) h0
      have he1 := evaluation_face_edge_of_mixed_right M A z f hf e h0 1 (by decide) h1
      erw [evaluation1_of_none M A z (Nf.targetSubsetFaceEdge2 _ f) h2, ← he0, ← he1]
      simp

/-- 独立したcounit評価と全退化型の相殺から生成する実cochain射ε。 -/
def evaluationHom : ThreeCochainComplex.Hom (pushforwardComplex M A)
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)) where
  f0 := evaluation0 M A
  f1 := evaluation1 M A
  f2 := evaluation2 M A
  comm0 := evaluation_comm0 M A
  comm1 := evaluation_comm1 M A

/-- ε Homの次数0を読む定義所有者API。 -/
@[simp] theorem evaluationHom_f0 : (evaluationHom M A).f0 = evaluation0 M A := rfl

/-- ε Homの次数1を読む定義所有者API。 -/
@[simp] theorem evaluationHom_f1 : (evaluationHom M A).f1 = evaluation1 M A := rfl

/-- ε Homの次数2を読む定義所有者API。 -/
@[simp] theorem evaluationHom_f2 : (evaluationHom M A).f2 = evaluation2 M A := rfl

/-- A・設計§3：独立したKan unitとcounit評価の合成は実subset比較の全Homである。 -/
theorem evaluation_unitHom :
    AtlasDefectComposition.cochainComp (unitHom M A) (evaluationHom M A) =
      M.targetSubsetComparisonHom A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) := by
  apply AtlasDefectComposition.cochain_ext
  · ext z
    simpa only [AtlasDefectComposition.cochainComp_f0, unitHom_f0,
      evaluationHom_f0, IncidenceSupportedComparison.targetSubsetComparisonHom_f0] using
      evaluation0_unit M A z
  · ext z
    simpa only [AtlasDefectComposition.cochainComp_f1, unitHom_f1,
      evaluationHom_f1, IncidenceSupportedComparison.targetSubsetComparisonHom_f1] using
      evaluation1_unit M A z
  · ext z
    simpa only [AtlasDefectComposition.cochainComp_f2, unitHom_f2,
      evaluationHom_f2, IncidenceSupportedComparison.targetSubsetComparisonHom_f2] using
      evaluation2_unit M A z

/-- Aの実直接射uの因子化。preimage台の同じ既存Homへ全三次数等号を接続する。 -/
theorem aSubnerveComparisonHom_factorization :
    M.aSubnerveComparisonHom A =
      AtlasDefectComposition.cochainComp (unitHom M A) (evaluationHom M A) :=
  (evaluation_unitHom M A).symm

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation0
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation1
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation2
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation1_of_none
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation1_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation2_of_none
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation2_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation0_unit
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation1_unit
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation2_unit
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation_endpoint_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation_endpoint_of_none
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation_comm0
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation_face_edge_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation_face_edge_of_mixed_left
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation_face_edge_of_mixed_right
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationHom
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationHom_f0
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationHom_f1
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationHom_f2
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation_unitHom
#print axioms AAT.AG.AtlasCoefficientFiber.aSubnerveComparisonHom_factorization
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
