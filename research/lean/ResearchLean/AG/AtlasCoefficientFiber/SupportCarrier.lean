import ResearchLean.AG.AtlasCoefficientFiber.SupportCells
import ResearchLean.AG.AtlasCoefficientFiber.ConstantLimit

/-!
# G-135 D：原carrierと台包含の全incidence正方形

## Implementation notes

Option像と元セル名から支持包含との可換性を生成する。対象だけの可換性では
十分でないので、全左右・三辺・三頂点射の位置を同じ原始表へ戻す。
別のcarrierを入力したり射を忘却したりする案は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 同じreading因子の逆像に誘導される台包含。 -/
def supportPreimageInclude : comparisonFactor qc qf h ⁻¹' A ⊆ comparisonFactor qc qf h ⁻¹' B :=
  fun _ hx => hab hx

/-- 逆像包含の成員値は元の粗台包含そのもの。 -/
theorem supportPreimageInclude_apply {t : qf.Target} (ht : comparisonFactor qc qf h t ∈ A) :
    supportPreimageInclude (h := h) hab ht = hab ht := rfl

/-- chartのcarrierは同じ名前付き支持包含と可換。 -/
theorem supportCarrier_chart (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) :
    (supportIncFunctor Nc hab).obj ((Carrier.preimageFunctor M A).obj (.chart c)) =
      (Carrier.preimageFunctor M B).obj
        ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj (.chart c)) := by
  rw [Carrier.preimageFunctor_obj_chart, supportIncFunctor_obj_chart,
    supportIncFunctor_obj_chart, Carrier.preimageFunctor_obj_chart]
  apply congrArg Inc.chart
  apply Subtype.ext
  rfl

/-- 辺のmapped/none両パターンで同じcarrier対象を保つ。 -/
theorem supportCarrier_edge (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) :
    (supportIncFunctor Nc hab).obj ((Carrier.preimageFunctor M A).obj (.edge e)) =
      (Carrier.preimageFunctor M B).obj
        ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj (.edge e)) := by
  rw [supportIncFunctor_obj_edge]
  cases he : M.edgeMap e.1 with
  | none =>
      rw [Carrier.preimageFunctor_obj_edge_of_none M A e he,
        Carrier.preimageFunctor_obj_edge_of_none M B _ he, supportIncFunctor_obj_chart]
      apply congrArg Inc.chart
      apply Subtype.ext
      rfl
  | some a =>
      rw [Carrier.preimageFunctor_obj_edge_of_some M A e a he,
        Carrier.preimageFunctor_obj_edge_of_some M B _ a he, supportIncFunctor_obj_edge]
      apply congrArg Inc.edge
      apply Subtype.ext
      rfl

/-- 面のmapped・混在二型・垂直型で同じcarrier対象を保つ。 -/
theorem supportCarrier_face (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) :
    (supportIncFunctor Nc hab).obj ((Carrier.preimageFunctor M A).obj (.face f)) =
      (Carrier.preimageFunctor M B).obj
        ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj (.face f)) := by
  rw [supportIncFunctor_obj_face]
  cases hf : M.faceMap f.1 with
  | some F =>
      rw [Carrier.preimageFunctor_obj_face_of_some M A f F hf,
        Carrier.preimageFunctor_obj_face_of_some M B _ F hf, supportIncFunctor_obj_face]
      apply congrArg Inc.face
      apply Subtype.ext
      rfl
  | none =>
      rw [Carrier.preimageFunctor_obj_face, Carrier.preimageFunctor_obj_face]
      cases h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) with
      | some e =>
          rw [Carrier.face_of_mixed_right M A _ _ f hf e h0,
            Carrier.face_of_mixed_right M B _ _ (supportCellInclude Nf.faceSupport (supportPreimageInclude (h := h) hab) f) hf e h0, supportIncFunctor_obj_edge]
          apply congrArg Inc.edge
          apply Subtype.ext
          rfl
      | none =>
          cases h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) with
          | some e =>
              rw [Carrier.face_of_mixed_left M A _ _ f hf h0 e h1,
                Carrier.face_of_mixed_left M B _ _ (supportCellInclude Nf.faceSupport (supportPreimageInclude (h := h) hab) f) hf h0 e h1, supportIncFunctor_obj_edge]
              apply congrArg Inc.edge
              apply Subtype.ext
              rfl
          | none =>
              rw [Carrier.face_of_vertical M A _ _ f hf h0 h1,
                Carrier.face_of_vertical M B _ _ (supportCellInclude Nf.faceSupport (supportPreimageInclude (h := h) hab) f) hf h0 h1, supportIncFunctor_obj_chart]
              apply congrArg Inc.chart
              apply Subtype.ext
              rfl

/-- 原carrierの支持包含正方形は全対象で可換。 -/
theorem supportCarrier_obj (x : Inc Nf (comparisonFactor qc qf h ⁻¹' A)) :
    (Carrier.preimageFunctor M A ⋙ supportIncFunctor Nc hab).obj x =
      (supportIncFunctor Nf (supportPreimageInclude (h := h) hab) ⋙ Carrier.preimageFunctor M B).obj x := by
  cases x with
  | chart c => exact supportCarrier_chart M hab c
  | edge e => exact supportCarrier_edge M hab e
  | face f => exact supportCarrier_face M hab f

/-- 原始端点射のcarrier位置は宣言上のOption辺像から決まる。 -/
def supportCarrierEndpointPosition (e : Nf.nerve.EdgeComponent) (s : Bool) :
    Unit ⊕ Bool ⊕ Fin 3 ⊕ Fin 3 :=
  match M.edgeMap e with
  | none => .inl ()
  | some _ => .inr (.inl s)

/-- 原始辺面射の位置は同じ面/辺Option表から決まる。 -/
def supportCarrierFaceEdgePosition (f : Nf.nerve.FaceComponent) (i : Fin 3) :
    Unit ⊕ Bool ⊕ Fin 3 ⊕ Fin 3 :=
  match M.faceMap f with
  | some _ => .inr (.inr (.inl i))
  | none =>
    match M.edgeMap (Nf.nerve.faceEdge0 f) with
    | some _ => if i = 2 then .inr (.inl true) else .inl ()
    | none =>
      match M.edgeMap (Nf.nerve.faceEdge1 f) with
      | some _ => if i = 0 then .inr (.inl false) else .inl ()
      | none => .inl ()

/-- 原始頂点面射の位置も同じ表と頂点位置だけで決まる。 -/
def supportCarrierFaceVertexPosition (f : Nf.nerve.FaceComponent) (i : Fin 3) :
    Unit ⊕ Bool ⊕ Fin 3 ⊕ Fin 3 :=
  match M.faceMap f with
  | some _ => .inr (.inr (.inr i))
  | none =>
    match M.edgeMap (Nf.nerve.faceEdge0 f) with
    | some _ => .inr (.inl (i != 0))
    | none =>
      match M.edgeMap (Nf.nerve.faceEdge1 f) with
      | some _ => .inr (.inl (i == 2))
      | none => .inl ()

/-- 任意台の実端点射は同じ原始位置を持つ。 -/
theorem supportCarrierEndpointPosition_eq (A : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (s : Bool)
    (hc : c = edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e s) :
    incHomCode ((Carrier.preimageFunctor M A).map (IncHom.chartEdge c e s hc)) =
      supportCarrierEndpointPosition M e.1 s := by
  cases he : M.edgeMap e.1 with
  | none =>
      rw [supportCarrierEndpointPosition, he]
      exact Carrier.preimageFunctor_map_chartEdge_code_of_none M A c e he s hc
  | some a =>
      rw [supportCarrierEndpointPosition, he]
      exact Carrier.preimageFunctor_map_chartEdge_code_of_some M A c e a he s hc

/-- 任意台の実辺面射は同じ全三辺の原始位置を持つ。 -/
theorem supportCarrierFaceEdgePosition_eq (A : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (i : Fin 3)
    (he : e = faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) :
    incHomCode ((Carrier.preimageFunctor M A).map (IncHom.edgeFace e f i he)) =
      supportCarrierFaceEdgePosition M f.1 i := by
  cases hf : M.faceMap f.1 with
  | some F =>
      rw [supportCarrierFaceEdgePosition, hf]
      exact Carrier.preimageFunctor_map_edgeFace_code_of_some M A e f F hf i he
  | none =>
      cases h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) with
      | some a =>
          rw [supportCarrierFaceEdgePosition, hf, h0]
          exact Carrier.preimageFunctor_map_edgeFace_code_of_mixed_right M A e f hf a h0 i he
      | none =>
          cases h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) with
          | some a =>
              rw [supportCarrierFaceEdgePosition, hf, h0, h1]
              exact Carrier.preimageFunctor_map_edgeFace_code_of_mixed_left M A e f hf a h0 h1 i he
          | none =>
              rw [supportCarrierFaceEdgePosition, hf, h0, h1]
              exact Carrier.preimageFunctor_map_edgeFace_code_of_vertical M A e f hf h0 h1 i he

/-- 任意台の実頂点面射は同じ全三頂点の原始位置を持つ。 -/
theorem supportCarrierFaceVertexPosition_eq (A : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (i : Fin 3)
    (hc : c = faceVertex Nf (comparisonFactor qc qf h ⁻¹' A) f i) :
    incHomCode ((Carrier.preimageFunctor M A).map (IncHom.chartFace c f i hc)) =
      supportCarrierFaceVertexPosition M f.1 i := by
  cases hf : M.faceMap f.1 with
  | some F =>
      rw [supportCarrierFaceVertexPosition, hf]
      exact Carrier.preimageFunctor_map_chartFace_code_of_some M A c f F hf i hc
  | none =>
      cases h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) with
      | some a =>
          rw [supportCarrierFaceVertexPosition, hf, h0]
          exact Carrier.preimageFunctor_map_chartFace_code_of_mixed_right M A c f hf a h0 i hc
      | none =>
          cases h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) with
          | some a =>
              rw [supportCarrierFaceVertexPosition, hf, h0, h1]
              exact Carrier.preimageFunctor_map_chartFace_code_of_mixed_left M A c f hf a h0 h1 i hc
          | none =>
              rw [supportCarrierFaceVertexPosition, hf, h0, h1]
              exact Carrier.preimageFunctor_map_chartFace_code_of_vertical M A c f hf h0 h1 i hc

/-- 原carrierの全射位置は同じ台包含を通しても変わらない。 -/
theorem supportCarrier_map_code {x y : Inc Nf (comparisonFactor qc qf h ⁻¹' A)} (f : x ⟶ y) :
    incHomCode ((Carrier.preimageFunctor M B).map
      ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).map f)) =
      incHomCode ((Carrier.preimageFunctor M A).map f) := by
  cases f with
  | id x =>
      change incHomCode ((Carrier.preimageFunctor M B).map (𝟙 _)) =
        incHomCode ((Carrier.preimageFunctor M A).map (𝟙 _))
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl
  | chartEdge c e s hc =>
      rw [supportIncFunctor_map_chartEdge, supportCarrierEndpointPosition_eq,
        supportCarrierEndpointPosition_eq]
      rfl
  | edgeFace e f i he =>
      rw [supportIncFunctor_map_edgeFace, supportCarrierFaceEdgePosition_eq,
        supportCarrierFaceEdgePosition_eq]
      rfl
  | chartFace c f i hc =>
      rw [supportIncFunctor_map_chartFace, supportCarrierFaceVertexPosition_eq,
        supportCarrierFaceVertexPosition_eq]
      rfl

/-- 同じ台包含のcarrier正方形は全対象と全射で自然同型をなす。 -/
def supportCarrierIso : Carrier.preimageFunctor M A ⋙ supportIncFunctor Nc hab ≅
    supportIncFunctor Nf (supportPreimageInclude (h := h) hab) ⋙ Carrier.preimageFunctor M B :=
  NatIso.ofComponents (fun x => eqToIso (supportCarrier_obj M hab x)) (by
    intro x y f
    apply incHomCode_injective
    simp only [CategoryTheory.Functor.comp_map, eqToIso.hom,
      incHomCode_comp_eqToHom, incHomCode_eqToHom_comp, supportIncFunctor_map_code]
    exact (supportCarrier_map_code M hab f).symm)

/-- 全射の自然性に使う同型成分は同じ対象等号の輸送だけ。 -/
theorem supportCarrierIso_hom_app (x : Inc Nf (comparisonFactor qc qf h ⁻¹' A)) :
    (supportCarrierIso M hab).hom.app x = eqToHom (supportCarrier_obj M hab x) := rfl

/-- 実comma圏の包含を同じ細セル包含とcarrier全正方形から生成する。 -/
def supportCommaFunctor (σ : Inc Nc A) :
    StructuredArrow σ (Carrier.preimageFunctor M A) ⥤
      StructuredArrow ((supportIncFunctor Nc hab).obj σ) (Carrier.preimageFunctor M B) :=
  StructuredArrow.map₂ (𝟙 ((supportIncFunctor Nc hab).obj σ)) (supportCarrierIso M hab).hom

/-- comma対象の細セル名は同じ支持包含。 -/
theorem supportCommaFunctor_obj_right (σ : Inc Nc A)
    (j : StructuredArrow σ (Carrier.preimageFunctor M A)) :
    ((supportCommaFunctor M hab σ).obj j).right =
      (supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj j.right := rfl

/-- comma対象の全incidence射も元の射とcarrier輸送から生成される。 -/
theorem supportCommaFunctor_obj_hom (σ : Inc Nc A)
    (j : StructuredArrow σ (Carrier.preimageFunctor M A)) :
    ((supportCommaFunctor M hab σ).obj j).hom =
      (supportIncFunctor Nc hab).map j.hom ≫ (supportCarrierIso M hab).hom.app j.right := by
  change 𝟙 _ ≫ _ ≫ _ = _
  rw [Category.id_comp]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportPreimageInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportPreimageInclude_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrier_chart
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrier_edge
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrier_face
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrier_obj
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrierEndpointPosition
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrierFaceEdgePosition
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrierFaceVertexPosition
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrierEndpointPosition_eq
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrierFaceEdgePosition_eq
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrierFaceVertexPosition_eq
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrier_map_code
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrierIso
#print axioms AAT.AG.AtlasCoefficientFiber.supportCarrierIso_hom_app
#print axioms AAT.AG.AtlasCoefficientFiber.supportCommaFunctor
#print axioms AAT.AG.AtlasCoefficientFiber.supportCommaFunctor_obj_right
#print axioms AAT.AG.AtlasCoefficientFiber.supportCommaFunctor_obj_hom
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
