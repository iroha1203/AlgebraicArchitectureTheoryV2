import ResearchLean.AG.AtlasCoefficientFiber.FiberComma
import ResearchLean.AG.AtlasCoefficientFiber.ConnectedFiber

/-!
# G-135 A：chart commaと原始Φの接続

## Implementation notes

退化宣言と原始端点・面出現からΦを選び、同じchart carrierの全セルを尽くす。
mapped辺を端点の粗chart一致だけでΦに含める案は採らない。
mapped辺・面のcomma対象は指定端点・頂点へ、mixed面はcollapsed辺または反対頂点へ戻す。
これらの到達と共通原像の連結性から標準成分同型を構成する義務を持つ。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じchart carrierの全細セルは原始Φの三種類で尽くされる。A・設計§1–2。 -/
theorem phiCellObj_surjective_of_carrier (c : Nc.ChartInTargetSubset A)
    (j : Inc Nf (comparisonFactor qc qf h ⁻¹' A))
    (hj : (Carrier.preimageFunctor M A).obj j = .chart c) :
    ∃ x : PhiInc M A c, phiCellObj M A c x = j := by
  cases j with
  | chart v =>
    rw [Carrier.preimageFunctor_obj_chart] at hj
    exact ⟨.inl ⟨v, Inc.chart.inj hj⟩, rfl⟩
  | edge e =>
    cases he : M.edgeMap e.1 with
    | some a => rw [Carrier.preimageFunctor_obj_edge_of_some M A e a he] at hj; cases hj
    | none =>
      rw [Carrier.preimageFunctor_obj_edge_of_none M A e he] at hj
      exact ⟨.inr (.inl ⟨e, he, Inc.chart.inj hj⟩), rfl⟩
  | face f =>
    cases hf : M.faceMap f.1 with
    | some F => rw [Carrier.preimageFunctor_obj_face_of_some M A f F hf] at hj; cases hj
    | none =>
      rcases degenerate_face_cases M f.1 hf with hv | hl | hr
      · rw [Carrier.preimageFunctor_obj_face,
          Carrier.face_of_vertical M A _ _ f hf hv.1 hv.2.1] at hj
        exact ⟨.inr (.inr ⟨f, hf, hv.1, hv.2.1, hv.2.2, Inc.chart.inj hj⟩), rfl⟩
      · rcases hl with ⟨a, h0, h1, _⟩
        rw [Carrier.preimageFunctor_obj_face,
          Carrier.face_of_mixed_left M A _ _ f hf h0 a h1] at hj
        cases hj
      · rcases hr with ⟨a, h0, _, _⟩
        rw [Carrier.preimageFunctor_obj_face,
          Carrier.face_of_mixed_right M A _ _ f hf a h0] at hj
        cases hj

/-- mapped細辺の指定端点を、同じ粗端点の原始Φ chartとして生成する。 -/
def phiMappedEndpoint (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) (s : Bool) :
    PhiChart M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s) :=
  ⟨edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s,
    Carrier.preimageFunctor_edge_endpoint_of_some M A e a he s⟩

/-- mapped端点の細セル名を読む定義所有者API。 -/
@[simp] theorem phiMappedEndpoint_val (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) (s : Bool) :
    (phiMappedEndpoint M A e a he s).1 = edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s := rfl

/-- mapped細面の指定頂点を、同じ粗頂点の原始Φ chartとして生成する。 -/
def phiMappedVertex (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    PhiChart M A (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i) :=
  ⟨faceVertex Nf (comparisonFactor qc qf h ⁻¹' A) f i,
    Carrier.preimageFunctor_face_vertex_of_some M A f F hf i⟩

/-- mapped頂点の細セル名を読む定義所有者API。 -/
@[simp] theorem phiMappedVertex_val (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    (phiMappedVertex M A f F hf i).1 = faceVertex Nf (comparisonFactor qc qf h ⁻¹' A) f i := rfl

/-- 左辺退化mixed型のcollapsed辺を原始Φへ生成する。台所属は同じ面の端点等号から導出。 -/
def phiMixedLeftCollapsed (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some a) :
    PhiEdge M A (Nc.targetSubsetEdgeLeft A
      (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge1 _ f) a h1)) :=
  ⟨Nf.targetSubsetFaceEdge0 _ f, h0,
    (congrArg (Carrier.chart M A _ (fun _ ht => ht))
      (Nf.targetSubset_left_faceEdge0_eq_left_faceEdge1 _ f)).trans
      (M.targetSubsetChartMap_edgeLeft A _ _ (Nf.targetSubsetFaceEdge1 _ f) a h1)⟩

/-- 第三辺退化mixed型のcollapsed辺を原始Φへ生成する。原始右端点輸送を使用。 -/
def phiMixedRightCollapsed (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some a)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = none) :
    PhiEdge M A (Nc.targetSubsetEdgeRight A
      (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge0 _ f) a h0)) :=
  ⟨Nf.targetSubsetFaceEdge2 _ f, h2,
    (congrArg (Carrier.chart M A _ (fun _ ht => ht))
      (Nf.targetSubset_right_faceEdge0_eq_left_faceEdge2 _ f).symm).trans
      (M.targetSubsetChartMap_edgeRight A _ _ (Nf.targetSubsetFaceEdge0 _ f) a h0)⟩

/-- 左mixed型の原始collapsed辺名。定義所有者API。 -/
@[simp] theorem phiMixedLeftCollapsed_val (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some a) :
    (phiMixedLeftCollapsed M A f a h0 h1).1 = Nf.targetSubsetFaceEdge0 _ f := rfl

/-- 右mixed型の原始collapsed辺名。定義所有者API。 -/
@[simp] theorem phiMixedRightCollapsed_val (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some a)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = none) :
    (phiMixedRightCollapsed M A f a h0 h2).1 = Nf.targetSubsetFaceEdge2 _ f := rfl

/-- 同じ厳密chart carrierのcomma行先へ至るΦ原像は、Φ内で連結する。 -/
theorem phiComma_common_target_of_strict (c : Nc.ChartInTargetSubset A)
    (y : StructuredArrow (.chart c) (Carrier.preimageFunctor M A))
    (hy : (Carrier.preimageFunctor M A).obj y.right = .chart c)
    (x x' : PhiInc M A c)
    (f : (phiCommaFunctor M A c).obj x ⟶ y)
    (g : (phiCommaFunctor M A c).obj x' ⟶ y) : Zigzag x x' := by
  obtain ⟨z, hz⟩ := phiCellObj_surjective_of_carrier M A c y.right hy
  exact constantCarrierComma_common_target M A _ (phiCellObj M A c) (.chart c)
    (phiCellObj_carrier M A c) y z hz x x' f g

/-- mapped細辺上のchart comma incidenceは、指定端点の原始Φ chartから到達する。 -/
theorem phiComma_reachable_of_mapped_edge
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) (s : Bool)
    (y : StructuredArrow
      (Inc.chart (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s) : Inc Nc A)
      (Carrier.preimageFunctor M A))
    (hy : Inc.edge e = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        (Carrier.preimageFunctor_obj_edge_of_some M A e a he)) =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s rfl) :
    ∃ x : PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s),
      Nonempty ((phiCommaFunctor M A _).obj x ⟶ y) := by
  let v := phiMappedEndpoint M A e a he s
  refine ⟨.inl v, ⟨StructuredArrow.homMk
    (IncHom.chartEdge (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s) e s rfl ≫
      eqToHom hy) ?_⟩⟩
  rw [← cancel_mono (eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
    (Carrier.preimageFunctor_obj_edge_of_some M A e a he))), ht]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
  apply incHomCode_injective
  rw [phiCommaFunctor_obj_hom, incHomCode_eqToHom_comp, incHomCode_comp_eqToHom,
    Carrier.preimageFunctor_map_chartEdge_code_of_some M A _ e a he s rfl]
  rfl

/-- mapped細面上のchart comma incidenceは、指定頂点の原始Φ chartから到達する。 -/
theorem phiComma_reachable_of_mapped_face
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3)
    (y : StructuredArrow
      (Inc.chart (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i) : Inc Nc A)
      (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)) =
      IncHom.chartFace (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
        (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl) :
    ∃ x : PhiInc M A (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i),
      Nonempty ((phiCommaFunctor M A _).obj x ⟶ y) := by
  let v := phiMappedVertex M A f F hf i
  refine ⟨.inl v, ⟨StructuredArrow.homMk
    (IncHom.chartFace (faceVertex Nf (comparisonFactor qc qf h ⁻¹' A) f i) f i rfl ≫ eqToHom hy) ?_⟩⟩
  rw [← cancel_mono (eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
    (Carrier.preimageFunctor_obj_face_of_some M A f F hf))), ht]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
  apply incHomCode_injective
  rw [phiCommaFunctor_obj_hom, incHomCode_eqToHom_comp, incHomCode_comp_eqToHom,
    Carrier.preimageFunctor_map_chartFace_code_of_some M A _ f F hf i rfl]
  rfl

/-- 同じ細セルを持つchart comma対象への、原始Φからの恒等輸送射。 -/
theorem phiComma_arrow_of_same_cell (c : Nc.ChartInTargetSubset A) (x : PhiInc M A c)
    (y : StructuredArrow (.chart c) (Carrier.preimageFunctor M A))
    (hy : phiCellObj M A c x = y.right) :
    Nonempty ((phiCommaFunctor M A c).obj x ⟶ y) := by
  let a : ((phiCommaFunctor M A c).obj x).right ⟶ y.right := eqToHom hy
  have hc : (Carrier.preimageFunctor M A).obj y.right = .chart c :=
    (congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans (phiCellObj_carrier M A c x)
  refine ⟨StructuredArrow.homMk a ?_⟩
  rw [← cancel_mono (eqToHom hc)]
  exact (inc_endomorphism_eq_id (.chart c) _).trans (inc_endomorphism_eq_id (.chart c) _).symm

/-- 厳密chart carrierを持つcomma対象は原始Φ包含から到達できる。 -/
theorem phiComma_reachable_of_strict (c : Nc.ChartInTargetSubset A)
    (y : StructuredArrow (.chart c) (Carrier.preimageFunctor M A))
    (hy : (Carrier.preimageFunctor M A).obj y.right = .chart c) :
    ∃ x : PhiInc M A c, Nonempty ((phiCommaFunctor M A c).obj x ⟶ y) := by
  obtain ⟨x, hx⟩ := phiCellObj_surjective_of_carrier M A c y.right hy
  exact ⟨x, phiComma_arrow_of_same_cell M A c x y hx⟩

/-- mixed左型のchart comma対象は、collapsed辺または反対頂点の原始Φから到達する。 -/
theorem phiComma_reachable_of_mixed_left
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some a) (s : Bool)
    (y : StructuredArrow
      (Inc.chart (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s) : Inc Nc A) (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_left M A _ _ f hf h0 a h1))) =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge1 _ f) a h1) s rfl) :
    ∃ x : PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s), Nonempty ((phiCommaFunctor M A _).obj x ⟶ y) := by
  cases s
  · let v := phiMixedLeftCollapsed M A f a h0 h1
    refine ⟨.inr (.inl v), ⟨StructuredArrow.homMk
      (IncHom.edgeFace (Nf.targetSubsetFaceEdge0 _ f) f 0 rfl ≫ eqToHom hy) ?_⟩⟩
    rw [← cancel_mono (eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
      ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_left M A _ _ f hf h0 a h1)))), ht]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
    apply incHomCode_injective
    rw [phiCommaFunctor_obj_hom, incHomCode_eqToHom_comp, incHomCode_comp_eqToHom]
    erw [Carrier.preimageFunctor_map_edgeFace_code_of_mixed_left M A _ f hf a h0 h1 0 rfl]
    rfl
  · let v := phiMappedEndpoint M A (Nf.targetSubsetFaceEdge1 _ f) a h1 true
    refine ⟨.inl v, ⟨StructuredArrow.homMk
      (IncHom.chartFace (faceVertex Nf (comparisonFactor qc qf h ⁻¹' A) f 2) f 2 rfl ≫ eqToHom hy) ?_⟩⟩
    rw [← cancel_mono (eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
      ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_left M A _ _ f hf h0 a h1)))), ht]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
    apply incHomCode_injective
    rw [phiCommaFunctor_obj_hom, incHomCode_eqToHom_comp, incHomCode_comp_eqToHom,
      Carrier.preimageFunctor_map_chartFace_code_of_mixed_left M A _ f hf a h0 h1 2 rfl]
    rfl

/-- mixed右型のchart comma対象は、反対頂点またはcollapsed辺の原始Φから到達する。 -/
theorem phiComma_reachable_of_mixed_right
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some a) (s : Bool)
    (y : StructuredArrow
      (Inc.chart (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s) : Inc Nc A) (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_right M A _ _ f hf a h0))) =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge0 _ f) a h0) s rfl) :
    ∃ x : PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s), Nonempty ((phiCommaFunctor M A _).obj x ⟶ y) := by
  cases s
  · let v := phiMappedEndpoint M A (Nf.targetSubsetFaceEdge0 _ f) a h0 false
    refine ⟨.inl v, ⟨StructuredArrow.homMk
      (IncHom.chartFace (faceVertex Nf (comparisonFactor qc qf h ⁻¹' A) f 0) f 0 rfl ≫ eqToHom hy) ?_⟩⟩
    rw [← cancel_mono (eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
      ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_right M A _ _ f hf a h0)))), ht]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
    apply incHomCode_injective
    rw [phiCommaFunctor_obj_hom, incHomCode_eqToHom_comp, incHomCode_comp_eqToHom,
      Carrier.preimageFunctor_map_chartFace_code_of_mixed_right M A _ f hf a h0 0 rfl]
    rfl
  · let v := phiMixedRightCollapsed M A f a h0 (Carrier.face_none_edge0_some M _ f hf a h0).2
    refine ⟨.inr (.inl v), ⟨StructuredArrow.homMk
      (IncHom.edgeFace (Nf.targetSubsetFaceEdge2 _ f) f 2 rfl ≫ eqToHom hy) ?_⟩⟩
    rw [← cancel_mono (eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
      ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_right M A _ _ f hf a h0)))), ht]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
    apply incHomCode_injective
    rw [phiCommaFunctor_obj_hom, incHomCode_eqToHom_comp, incHomCode_comp_eqToHom]
    erw [Carrier.preimageFunctor_map_edgeFace_code_of_mixed_right M A _ f hf a h0 2 rfl]
    rfl

/-- chart carrierへのincidenceは同じ粗chartの恒等となり、厳密Φへ帰着する。 -/
theorem phiComma_reachable_of_chart_carrier (c a : Nc.ChartInTargetSubset A)
    (y : StructuredArrow (.chart c) (Carrier.preimageFunctor M A))
    (ha : (Carrier.preimageFunctor M A).obj y.right = .chart a) :
    ∃ x : PhiInc M A c, Nonempty ((phiCommaFunctor M A c).obj x ⟶ y) := by
  have he := incHom_chart_chart_target c a (y.hom ≫ eqToHom ha)
  exact phiComma_reachable_of_strict M A c y (ha.trans (congrArg Inc.chart he))

/-- 任意のchart comma対象へ、原始Φのセルから到達する。incidence位置は原始射から読む。 -/
theorem phiComma_reachable (c : Nc.ChartInTargetSubset A)
    (y : StructuredArrow (.chart c) (Carrier.preimageFunctor M A)) :
    ∃ x : PhiInc M A c, Nonempty ((phiCommaFunctor M A c).obj x ⟶ y) := by
  cases hy : y.right with
  | chart v =>
    exact phiComma_reachable_of_chart_carrier M A c _ y
      ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_chart M A v))
  | edge e =>
    cases he : M.edgeMap e.1 with
    | none =>
      exact phiComma_reachable_of_chart_carrier M A c _ y
        ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_edge_of_none M A e he))
    | some a =>
      let hp := (congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_edge_of_some M A e a he)
      let hh := y.hom ≫ eqToHom hp
      cases ht : hh with
      | chartEdge _ _ s hs =>
        subst c
        exact phiComma_reachable_of_mapped_edge M A e a he s y hy.symm ht
  | face f =>
    cases hf : M.faceMap f.1 with
    | some F =>
      let hp := (congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)
      let hh := y.hom ≫ eqToHom hp
      cases ht : hh with
      | chartFace _ _ i hi =>
        subst c
        exact phiComma_reachable_of_mapped_face M A f F hf i y hy.symm ht
    | none =>
      rcases degenerate_face_cases M f.1 hf with hv | hl | hr
      · exact phiComma_reachable_of_chart_carrier M A c _ y
          (((congrArg (Carrier.preimageFunctor M A).obj hy).trans
            (Carrier.preimageFunctor_obj_face M A f)).trans
            (Carrier.face_of_vertical M A _ _ f hf hv.1 hv.2.1))
      · rcases hl with ⟨a, h0, h1, _⟩
        let hp := ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_face M A f)).trans
          (Carrier.face_of_mixed_left M A _ _ f hf h0 a h1)
        let hh := y.hom ≫ eqToHom hp
        cases ht : hh with
        | chartEdge _ _ s hs =>
          subst c
          exact phiComma_reachable_of_mixed_left M A f hf a h0 h1 s y hy.symm ht
      · rcases hr with ⟨a, h0, _, _⟩
        let hp := ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_face M A f)).trans
          (Carrier.face_of_mixed_right M A _ _ f hf a h0)
        let hh := y.hom ≫ eqToHom hp
        cases ht : hh with
        | chartEdge _ _ s hs =>
          subst c
          exact phiComma_reachable_of_mixed_right M A f hf a h0 s y hy.symm ht

/-- mapped辺の同じ粗端点incidenceへのΦ原像は、指定した細端点だけである。 -/
theorem phiComma_source_of_mapped_edge
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) (s : Bool)
    (y : StructuredArrow
      (Inc.chart (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s) : Inc Nc A)
      (Carrier.preimageFunctor M A))
    (hy : Inc.edge e = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        (Carrier.preimageFunctor_obj_edge_of_some M A e a he)) =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s rfl)
    (x : PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s))
    (g : (phiCommaFunctor M A _).obj x ⟶ y) :
    phiCellObj M A _ x = Inc.chart (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s) := by
  rcases x with v | w
  · let gg : Inc.chart v.1 ⟶ Inc.edge e := g.right ≫ eqToHom hy.symm
    cases hg : gg with
    | chartEdge _ _ t hv =>
      have hw : ((phiCommaFunctor M A _).obj (.inl v)).hom ≫
          (Carrier.preimageFunctor M A).map gg ≫
            eqToHom (Carrier.preimageFunctor_obj_edge_of_some M A e a he) =
          IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s)
            (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s rfl := by
        calc
          _ = ((phiCommaFunctor M A _).obj (.inl v)).hom ≫
              (Carrier.preimageFunctor M A).map g.right ≫
                eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
                  (Carrier.preimageFunctor_obj_edge_of_some M A e a he)) := by
                    simp only [gg, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
          _ = _ := by rw [← Category.assoc, StructuredArrow.w, ht]
      rw [phiCommaFunctor_obj_hom] at hw
      have hc := congrArg incHomCode hw
      rw [incHomCode_eqToHom_comp, incHomCode_comp_eqToHom, hg,
        Carrier.preimageFunctor_map_chartEdge_code_of_some M A v.1 e a he t hv] at hc
      have hts : t = s := Sum.inl.inj (Sum.inr.inj hc)
      subst t
      exact congrArg Inc.chart hv
  · rcases w with v | f
    · let gg : Inc.edge v.1 ⟶ Inc.edge e := g.right ≫ eqToHom hy.symm
      have hve := incHom_edge_edge_target v.1 e gg
      have hn : M.edgeMap e.1 = none := by simpa only [hve] using v.2.1
      cases he.symm.trans hn
    · let gg : Inc.face f.1 ⟶ Inc.edge e := g.right ≫ eqToHom hy.symm
      cases gg

/-- mapped面の同じ粗頂点incidenceへのΦ原像は、指定した細頂点だけである。 -/
theorem phiComma_source_of_mapped_face
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3)
    (y : StructuredArrow
      (Inc.chart (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i) : Inc Nc A)
      (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)) =
      IncHom.chartFace (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
        (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl)
    (x : PhiInc M A (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i))
    (g : (phiCommaFunctor M A _).obj x ⟶ y) :
    phiCellObj M A _ x = Inc.chart (faceVertex Nf (comparisonFactor qc qf h ⁻¹' A) f i) := by
  rcases x with v | w
  · let gg : Inc.chart v.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
    cases hg : gg with
    | chartFace _ _ j hv =>
      have hw : ((phiCommaFunctor M A _).obj (.inl v)).hom ≫
          (Carrier.preimageFunctor M A).map gg ≫
            eqToHom (Carrier.preimageFunctor_obj_face_of_some M A f F hf) =
          IncHom.chartFace (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
            (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl := by
        calc
          _ = ((phiCommaFunctor M A _).obj (.inl v)).hom ≫
              (Carrier.preimageFunctor M A).map g.right ≫
                eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
                  (Carrier.preimageFunctor_obj_face_of_some M A f F hf)) := by
                    simp only [gg, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
          _ = _ := by rw [← Category.assoc, StructuredArrow.w, ht]
      rw [phiCommaFunctor_obj_hom] at hw
      have hc := congrArg incHomCode hw
      rw [incHomCode_eqToHom_comp, incHomCode_comp_eqToHom, hg,
        Carrier.preimageFunctor_map_chartFace_code_of_some M A v.1 f F hf j hv] at hc
      have hji : j = i := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj hc))
      subst j
      exact congrArg Inc.chart hv
  · rcases w with v | m
    · let gg : Inc.edge v.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
      cases gg with
      | edgeFace _ _ j hj =>
        have hs := Carrier.preimageFunctor_face_edgeMap_of_some M A f F hf j
        have hn : M.edgeMap (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f j).1 = none := by
          simpa only [hj] using v.2.1
        cases hs.symm.trans hn
    · let gg : Inc.face m.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
      have hmf := Inc.face.inj (incHom_target_of_face m.1 gg)
      have hn : M.faceMap f.1 = none := by simpa only [hmf] using m.2.1
      cases hf.symm.trans hn

/-- mapped edge の同じcomma行先への原像は、指定細chartとして連結する。 -/
theorem phiComma_common_target_of_mapped_edge
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) (s : Bool)
    (y : StructuredArrow
      (Inc.chart (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s) : Inc Nc A)
      (Carrier.preimageFunctor M A))
    (hy : Inc.edge e = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        (Carrier.preimageFunctor_obj_edge_of_some M A e a he)) =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s rfl)
    (x x' : PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) s))
    (g : (phiCommaFunctor M A _).obj x ⟶ y)
    (g' : (phiCommaFunctor M A _).obj x' ⟶ y) : Zigzag x x' := by
  have hx := phiComma_source_of_mapped_edge M A e a he s y hy ht x g
  have hx' := phiComma_source_of_mapped_edge M A e a he s y hy ht x' g'
  exact Zigzag.of_hom (eqToHom ((phiCellObj_injective M A _) (hx.trans hx'.symm)))

/-- mapped face の同じcomma行先への原像は、指定細chartとして連結する。 -/
theorem phiComma_common_target_of_mapped_face
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3)
    (y : StructuredArrow
      (Inc.chart (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i) : Inc Nc A)
      (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)) =
      IncHom.chartFace (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
        (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl)
    (x x' : PhiInc M A (faceVertex Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i))
    (g : (phiCommaFunctor M A _).obj x ⟶ y)
    (g' : (phiCommaFunctor M A _).obj x' ⟶ y) : Zigzag x x' := by
  have hx := phiComma_source_of_mapped_face M A f F hf i y hy ht x g
  have hx' := phiComma_source_of_mapped_face M A f F hf i y hy ht x' g'
  exact Zigzag.of_hom (eqToHom ((phiCellObj_injective M A _) (hx.trans hx'.symm)))

/-- 左mixed面への粗端点出現に対する、原始Φのcollapsed辺または反対頂点。 -/
def phiMixedLeftAnchor
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some a) :
    (s : Bool) → PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
      (Nf.targetSubsetFaceEdge1 _ f) a h1) s)
  | false => .inr (.inl (phiMixedLeftCollapsed M A f a h0 h1))
  | true => .inl (phiMappedEndpoint M A (Nf.targetSubsetFaceEdge1 _ f) a h1 true)

/-- 左mixed面の同じ粗端点出現へのΦ原像は、原始anchorへΦ内の射を持つ。 -/
theorem phiComma_arrow_to_mixed_left_anchor
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some a) (s : Bool)
    (y : StructuredArrow
      (Inc.chart (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s) : Inc Nc A) (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_left M A _ _ f hf h0 a h1))) =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge1 _ f) a h1) s rfl)
    (x : PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s))
    (g : (phiCommaFunctor M A _).obj x ⟶ y) :
    Nonempty (x ⟶ phiMixedLeftAnchor M A f a h0 h1 s) := by
  let hp := (Carrier.preimageFunctor_obj_face M A f).trans
    (Carrier.face_of_mixed_left M A _ _ f hf h0 a h1)
  have hw : ((phiCommaFunctor M A _).obj x).hom ≫
      (Carrier.preimageFunctor M A).map (g.right ≫ eqToHom hy.symm) ≫ eqToHom hp =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge1 _ f) a h1) s rfl := by
    calc
      _ = ((phiCommaFunctor M A _).obj x).hom ≫
          (Carrier.preimageFunctor M A).map g.right ≫
            eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans hp) := by
              simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
      _ = _ := by rw [← Category.assoc, StructuredArrow.w, ht]
  rw [phiCommaFunctor_obj_hom] at hw
  have hc := congrArg incHomCode hw
  rw [incHomCode_eqToHom_comp, incHomCode_comp_eqToHom] at hc
  rcases x with v | w
  · let gg : Inc.chart v.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
    change incHomCode ((Carrier.preimageFunctor M A).map gg) = _ at hc
    cases hg : gg with
    | chartFace _ _ j hv =>
      rw [hg, Carrier.preimageFunctor_map_chartFace_code_of_mixed_left M A v.1 f hf a h0 h1 j hv] at hc
      have hjs : (j == 2) = s := Sum.inl.inj (Sum.inr.inj hc)
      subst s
      fin_cases j
      · exact ⟨InducedCategory.homMk (IncHom.chartEdge v.1 (Nf.targetSubsetFaceEdge0 _ f) false hv)⟩
      · exact ⟨InducedCategory.homMk (IncHom.chartEdge v.1 (Nf.targetSubsetFaceEdge0 _ f) true hv)⟩
      · exact ⟨InducedCategory.homMk (eqToHom (congrArg Inc.chart hv))⟩
  · rcases w with v | m
    · let gg : Inc.edge v.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
      change incHomCode ((Carrier.preimageFunctor M A).map gg) = _ at hc
      cases hg : gg with
      | edgeFace _ _ j hv =>
        rw [hg, Carrier.preimageFunctor_map_edgeFace_code_of_mixed_left M A v.1 f hf a h0 h1 j hv] at hc
        fin_cases j
        · have hs : false = s := Sum.inl.inj (Sum.inr.inj hc)
          subst s
          exact ⟨InducedCategory.homMk (eqToHom (congrArg Inc.edge hv))⟩
        · cases hc
        · cases hc
    · let gg : Inc.face m.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
      have hmf := Inc.face.inj (incHom_target_of_face m.1 gg)
      have hn : M.edgeMap (Nf.nerve.faceEdge1 f.1) = none := by simpa only [hmf] using m.2.2.2.1
      cases h1.symm.trans hn

/-- 右mixed面への粗端点出現に対する、原始Φの反対頂点またはcollapsed辺。 -/
def phiMixedRightAnchor
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some a)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = none) :
    (s : Bool) → PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
      (Nf.targetSubsetFaceEdge0 _ f) a h0) s)
  | false => .inl (phiMappedEndpoint M A (Nf.targetSubsetFaceEdge0 _ f) a h0 false)
  | true => .inr (.inl (phiMixedRightCollapsed M A f a h0 h2))

/-- 右mixed面の同じ粗端点出現へのΦ原像は、原始anchorへΦ内の射を持つ。 -/
theorem phiComma_arrow_to_mixed_right_anchor
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some a) (s : Bool)
    (y : StructuredArrow
      (Inc.chart (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s) : Inc Nc A) (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_right M A _ _ f hf a h0))) =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge0 _ f) a h0) s rfl)
    (x : PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s))
    (g : (phiCommaFunctor M A _).obj x ⟶ y) :
    Nonempty (x ⟶ phiMixedRightAnchor M A f a h0 (Carrier.face_none_edge0_some M _ f hf a h0).2 s) := by
  let hp := (Carrier.preimageFunctor_obj_face M A f).trans
    (Carrier.face_of_mixed_right M A _ _ f hf a h0)
  have hw : ((phiCommaFunctor M A _).obj x).hom ≫
      (Carrier.preimageFunctor M A).map (g.right ≫ eqToHom hy.symm) ≫ eqToHom hp =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge0 _ f) a h0) s rfl := by
    calc
      _ = ((phiCommaFunctor M A _).obj x).hom ≫
          (Carrier.preimageFunctor M A).map g.right ≫
            eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans hp) := by
              simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
      _ = _ := by rw [← Category.assoc, StructuredArrow.w, ht]
  rw [phiCommaFunctor_obj_hom] at hw
  have hc := congrArg incHomCode hw
  rw [incHomCode_eqToHom_comp, incHomCode_comp_eqToHom] at hc
  rcases x with v | w
  · let gg : Inc.chart v.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
    change incHomCode ((Carrier.preimageFunctor M A).map gg) = _ at hc
    cases hg : gg with
    | chartFace _ _ j hv =>
      rw [hg, Carrier.preimageFunctor_map_chartFace_code_of_mixed_right M A v.1 f hf a h0 j hv] at hc
      have hjs : (j != 0) = s := Sum.inl.inj (Sum.inr.inj hc)
      subst s
      fin_cases j
      · exact ⟨InducedCategory.homMk (eqToHom (congrArg Inc.chart hv))⟩
      · exact ⟨InducedCategory.homMk (IncHom.chartEdge v.1 (Nf.targetSubsetFaceEdge2 _ f) false
          (hv.trans (edgeEndpoint_faceEdge Nf _ f 2 false).symm))⟩
      · exact ⟨InducedCategory.homMk (IncHom.chartEdge v.1 (Nf.targetSubsetFaceEdge2 _ f) true
          (hv.trans (edgeEndpoint_faceEdge Nf _ f 2 true).symm))⟩
  · rcases w with v | m
    · let gg : Inc.edge v.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
      change incHomCode ((Carrier.preimageFunctor M A).map gg) = _ at hc
      cases hg : gg with
      | edgeFace _ _ j hv =>
        rw [hg, Carrier.preimageFunctor_map_edgeFace_code_of_mixed_right M A v.1 f hf a h0 j hv] at hc
        fin_cases j
        · cases hc
        · cases hc
        · have hs : true = s := Sum.inl.inj (Sum.inr.inj hc)
          subst s
          exact ⟨InducedCategory.homMk (eqToHom (congrArg Inc.edge hv))⟩
    · let gg : Inc.face m.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
      have hmf := Inc.face.inj (incHom_target_of_face m.1 gg)
      have hn : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none := by simpa only [hmf] using m.2.2.1
      cases h0.symm.trans hn

/-- mixed left の同じcomma行先への原像は、原始anchorを介して連結する。 -/
theorem phiComma_common_target_of_mixed_left
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some a) (s : Bool)
    (y : StructuredArrow
      (Inc.chart (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s) : Inc Nc A) (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_left M A _ _ f hf h0 a h1))) =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge1 _ f) a h1) s rfl)
    (x x' : PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge1 _ f) a h1) s))
    (g : (phiCommaFunctor M A _).obj x ⟶ y)
    (g' : (phiCommaFunctor M A _).obj x' ⟶ y) : Zigzag x x' := by
  obtain ⟨gx⟩ := phiComma_arrow_to_mixed_left_anchor M A f hf a h0 h1 s y hy ht x g
  obtain ⟨gx'⟩ := phiComma_arrow_to_mixed_left_anchor M A f hf a h0 h1 s y hy ht x' g'
  exact (Zigzag.of_hom gx).trans (Zigzag.of_hom gx').symm

/-- mixed right の同じcomma行先への原像は、原始anchorを介して連結する。 -/
theorem phiComma_common_target_of_mixed_right
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some a) (s : Bool)
    (y : StructuredArrow
      (Inc.chart (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s) : Inc Nc A) (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        ((Carrier.preimageFunctor_obj_face M A f).trans (Carrier.face_of_mixed_right M A _ _ f hf a h0))) =
      IncHom.chartEdge (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s)
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge0 _ f) a h0) s rfl)
    (x x' : PhiInc M A (edgeEndpoint Nc A (M.targetSubsetEdgeMap A _ (fun _ ht => ht)
        (Nf.targetSubsetFaceEdge0 _ f) a h0) s))
    (g : (phiCommaFunctor M A _).obj x ⟶ y)
    (g' : (phiCommaFunctor M A _).obj x' ⟶ y) : Zigzag x x' := by
  obtain ⟨gx⟩ := phiComma_arrow_to_mixed_right_anchor M A f hf a h0 s y hy ht x g
  obtain ⟨gx'⟩ := phiComma_arrow_to_mixed_right_anchor M A f hf a h0 s y hy ht x' g'
  exact (Zigzag.of_hom gx).trans (Zigzag.of_hom gx').symm

/-- chart carrierへの共通原像は、同じ粗chartの厳密Φ内で連結する。 -/
theorem phiComma_common_target_of_chart_carrier (c a : Nc.ChartInTargetSubset A)
    (y : StructuredArrow (.chart c) (Carrier.preimageFunctor M A))
    (ha : (Carrier.preimageFunctor M A).obj y.right = .chart a)
    (x x' : PhiInc M A c)
    (g : (phiCommaFunctor M A c).obj x ⟶ y)
    (g' : (phiCommaFunctor M A c).obj x' ⟶ y) : Zigzag x x' := by
  have he := incHom_chart_chart_target c a (y.hom ≫ eqToHom ha)
  exact phiComma_common_target_of_strict M A c y (ha.trans (congrArg Inc.chart he)) x x' g g'

/-- 任意のchart comma共同行先の原像は、原始Φ内で連結する。成分単射性のproducer。 -/
theorem phiComma_common_target (c : Nc.ChartInTargetSubset A)
    (y : StructuredArrow (.chart c) (Carrier.preimageFunctor M A))
    (x x' : PhiInc M A c)
    (g : (phiCommaFunctor M A c).obj x ⟶ y)
    (g' : (phiCommaFunctor M A c).obj x' ⟶ y) : Zigzag x x' := by
  cases hy : y.right with
  | chart v =>
    exact phiComma_common_target_of_chart_carrier M A c _ y
      ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_chart M A v)) x x' g g'
  | edge e =>
    cases he : M.edgeMap e.1 with
    | none =>
      exact phiComma_common_target_of_chart_carrier M A c _ y
        ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_edge_of_none M A e he)) x x' g g'
    | some a =>
      let hp := (congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_edge_of_some M A e a he)
      let hh := y.hom ≫ eqToHom hp
      cases ht : hh with
      | chartEdge _ _ s hs =>
        subst c
        exact phiComma_common_target_of_mapped_edge M A e a he s y hy.symm ht x x' g g'
  | face f =>
    cases hf : M.faceMap f.1 with
    | some F =>
      let hp := (congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)
      let hh := y.hom ≫ eqToHom hp
      cases ht : hh with
      | chartFace _ _ i hi =>
        subst c
        exact phiComma_common_target_of_mapped_face M A f F hf i y hy.symm ht x x' g g'
    | none =>
      rcases degenerate_face_cases M f.1 hf with hv | hl | hr
      · exact phiComma_common_target_of_chart_carrier M A c _ y
          (((congrArg (Carrier.preimageFunctor M A).obj hy).trans
            (Carrier.preimageFunctor_obj_face M A f)).trans
            (Carrier.face_of_vertical M A _ _ f hf hv.1 hv.2.1)) x x' g g'
      · rcases hl with ⟨a, h0, h1, _⟩
        let hp := ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_face M A f)).trans
          (Carrier.face_of_mixed_left M A _ _ f hf h0 a h1)
        let hh := y.hom ≫ eqToHom hp
        cases ht : hh with
        | chartEdge _ _ s hs =>
          subst c
          exact phiComma_common_target_of_mixed_left M A f hf a h0 h1 s y hy.symm ht x x' g g'
      · rcases hr with ⟨a, h0, _, _⟩
        let hp := ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_face M A f)).trans
          (Carrier.face_of_mixed_right M A _ _ f hf a h0)
        let hh := y.hom ≫ eqToHom hp
        cases ht : hh with
        | chartEdge _ _ s hs =>
          subst c
          exact phiComma_common_target_of_mixed_right M A f hf a h0 s y hy.symm ht x x' g g'

/-- A・設計§2のΦとchart comma成分の全単射。全射・単射のproducerを原始Mから渡す。 -/
def phiComponentsEquiv (c : Nc.ChartInTargetSubset A) :
    CategoryTheory.ConnectedComponents (PhiInc M A c) ≃
      CategoryTheory.ConnectedComponents (StructuredArrow (.chart c) (Carrier.preimageFunctor M A)) :=
  componentEquivOfCommonTargets (phiCommaFunctor M A c)
    (phiComma_reachable M A c) (phiComma_common_target M A c)

/-- 原始Φからcommaへの成分同型の順向きは同じ包含関手の標準成分写像。 -/
@[simp] theorem phiComponentsEquiv_apply (c : Nc.ChartInTargetSubset A)
    (k : CategoryTheory.ConnectedComponents (PhiInc M A c)) :
    phiComponentsEquiv M A c k = (phiCommaFunctor M A c).mapConnectedComponents k := rfl

/-- A・設計§2のchart stalk成分式。独立した標準右Kan極限を原始Φ成分上の関数へ同定。 -/
def phiCoefficientEquiv (c : Nc.ChartInTargetSubset A) :
    (pushforwardCoefficients M A).obj (.chart c) ≃ₗ[ℚ]
      (CategoryTheory.ConnectedComponents (PhiInc M A c) → ℚ) :=
  ((coefficientCellIso (Carrier.preimageFunctor M A) (.chart c)).toLinearEquiv.trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : CategoryTheory.ConnectedComponents
      (StructuredArrow (.chart c) (Carrier.preimageFunctor M A)) => ULift.{u} ℚ)
      (phiComponentsEquiv M A c).symm)).trans
    (LinearEquiv.piCongrRight (fun _ => ULift.moduleEquiv))

/-- 原始Φ成分での同じ右Kan係数評価。定義所有者API。 -/
@[simp] theorem phiCoefficientEquiv_apply (c : Nc.ChartInTargetSubset A)
    (z : (pushforwardCoefficients M A).obj (.chart c))
    (k : CategoryTheory.ConnectedComponents (PhiInc M A c)) :
    phiCoefficientEquiv M A c z k =
      ((coefficientCellIso (Carrier.preimageFunctor M A) (.chart c)).hom z
        ((phiCommaFunctor M A c).mapConnectedComponents k)).down := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellObj_surjective_of_carrier
#print axioms AAT.AG.AtlasCoefficientFiber.phiMappedEndpoint
#print axioms AAT.AG.AtlasCoefficientFiber.phiMappedEndpoint_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiMappedVertex
#print axioms AAT.AG.AtlasCoefficientFiber.phiMappedVertex_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiMixedLeftCollapsed
#print axioms AAT.AG.AtlasCoefficientFiber.phiMixedRightCollapsed
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_common_target_of_strict
#print axioms AAT.AG.AtlasCoefficientFiber.phiMixedLeftCollapsed_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiMixedRightCollapsed_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_reachable_of_mapped_edge
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_reachable_of_mapped_face
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_arrow_of_same_cell
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_reachable_of_strict
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_reachable_of_mixed_left
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_reachable_of_mixed_right
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_reachable_of_chart_carrier
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_reachable
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_source_of_mapped_edge
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_source_of_mapped_face
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_common_target_of_mapped_edge
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_common_target_of_mapped_face
#print axioms AAT.AG.AtlasCoefficientFiber.phiMixedLeftAnchor
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_arrow_to_mixed_left_anchor
#print axioms AAT.AG.AtlasCoefficientFiber.phiMixedRightAnchor
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_arrow_to_mixed_right_anchor
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_common_target_of_mixed_left
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_common_target_of_mixed_right
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_common_target_of_chart_carrier
#print axioms AAT.AG.AtlasCoefficientFiber.phiComma_common_target
#print axioms AAT.AG.AtlasCoefficientFiber.phiComponentsEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.phiComponentsEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.phiCoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.phiCoefficientEquiv_apply
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
