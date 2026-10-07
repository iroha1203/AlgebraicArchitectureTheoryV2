import ResearchLean.AG.AtlasCoefficientFiber.FiberComma
import ResearchLean.AG.AtlasCoefficientFiber.ConnectedFiber

/-!
# G-135 A：辺commaの原始アンカー

## Implementation notes

粗辺からのincidenceを、mapped細辺、mixed細面、mapped細面の指定辺位置に分類する。
追加の成分certificateを入力にする案は採らず、同じcomma対象と原始Option像から選ぶ。
原始包含の到達と共通原像のzigzagから成分全単射を得る。
-/

noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)
/-- 粗辺をcarrierに持つ細セルは原始Γセルとして尽くされる。A・設計§1–2。 -/
theorem gammaCellObj_surjective_of_carrier (e : Nc.EdgeInTargetSubset A)
    (j : Inc Nf (comparisonFactor qc qf h ⁻¹' A))
    (hj : (Carrier.preimageFunctor M A).obj j = .edge e) :
    ∃ x : GammaInc M A e, gammaCellObj M A e x = j := by
  cases j with
  | chart v => rw [Carrier.preimageFunctor_obj_chart] at hj; cases hj
  | edge v =>
    have hv : M.edgeMap v.1 = some e.1 :=
      (Carrier.edge_eq_edge_iff M A _ (fun _ ht => ht) v e).mp
        ((Carrier.preimageFunctor_obj_edge M A v).symm.trans hj)
    exact ⟨.inl ⟨v, hv⟩, rfl⟩
  | face f =>
    cases hf : M.faceMap f.1 with
    | some F => rw [Carrier.preimageFunctor_obj_face_of_some M A f F hf] at hj; cases hj
    | none =>
      rcases degenerate_face_cases M f.1 hf with hv | hl | hr
      · rw [Carrier.preimageFunctor_obj_face,
          Carrier.face_of_vertical M A _ _ f hf hv.1 hv.2.1] at hj
        cases hj
      · rcases hl with ⟨a, h0, h1, h2⟩
        rw [Carrier.preimageFunctor_obj_face,
          Carrier.face_of_mixed_left M A _ _ f hf h0 a h1] at hj
        have ha := congrArg Subtype.val (Inc.edge.inj hj)
        exact ⟨.inr ⟨f, hf, Or.inl ⟨h0, h1.trans (congrArg some ha),
          h2.trans (congrArg some ha)⟩⟩, rfl⟩
      · rcases hr with ⟨a, h0, h1, h2⟩
        rw [Carrier.preimageFunctor_obj_face,
          Carrier.face_of_mixed_right M A _ _ f hf a h0] at hj
        have ha := congrArg Subtype.val (Inc.edge.inj hj)
        exact ⟨.inr ⟨f, hf, Or.inr ⟨h0.trans (congrArg some ha),
          h1.trans (congrArg some ha), h2⟩⟩, rfl⟩

/-- 厳密Γセルと同じ細セルを持つcomma対象への恒等輸送射。所属から可換性を導出する。 -/
theorem gammaComma_arrow_of_same_cell (e : Nc.EdgeInTargetSubset A) (x : GammaInc M A e)
    (y : StructuredArrow (.edge e) (Carrier.preimageFunctor M A))
    (hy : gammaCellObj M A e x = y.right) :
    Nonempty ((gammaCommaFunctor M A e).obj x ⟶ y) := by
  let a : ((gammaCommaFunctor M A e).obj x).right ⟶ y.right := eqToHom hy
  have hc : (Carrier.preimageFunctor M A).obj y.right = .edge e :=
    (congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans (gammaCellObj_carrier M A e x)
  refine ⟨StructuredArrow.homMk a ?_⟩
  rw [← cancel_mono (eqToHom hc)]
  exact (inc_endomorphism_eq_id (.edge e) _).trans (inc_endomorphism_eq_id (.edge e) _).symm

/-- 同じ粗辺を厳密carrierに持つcomma対象はΓ包含から到達できる。 -/
theorem gammaComma_reachable_of_strict (e : Nc.EdgeInTargetSubset A)
    (y : StructuredArrow (.edge e) (Carrier.preimageFunctor M A))
    (hy : (Carrier.preimageFunctor M A).obj y.right = .edge e) :
    ∃ x : GammaInc M A e, Nonempty ((gammaCommaFunctor M A e).obj x ⟶ y) := by
  obtain ⟨x, hx⟩ := gammaCellObj_surjective_of_carrier M A e y.right hy
  exact ⟨x, gammaComma_arrow_of_same_cell M A e x y hx⟩

/-- mapped細面の指定粗辺incidenceは、同じ細辺位置のΓ頂点から到達する。
所属と射の等号はcomma原始射の分類で得る方向仮定であり、結論fieldではない。 -/
theorem gammaComma_reachable_of_mapped_face
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3)
    (y : StructuredArrow
      (Inc.edge (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i) : Inc Nc A)
      (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)) =
      IncHom.edgeFace
        (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
        (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl) :
    ∃ x : GammaInc M A (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i),
      Nonempty ((gammaCommaFunctor M A _).obj x ⟶ y) := by
  let v : GammaVertex M A (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i) :=
    ⟨faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i,
      Carrier.preimageFunctor_face_edgeMap_of_some M A f F hf i⟩
  refine ⟨.inl v, ⟨StructuredArrow.homMk
    (IncHom.edgeFace (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) f i rfl ≫ eqToHom hy) ?_⟩⟩
  rw [← cancel_mono (eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
    (Carrier.preimageFunctor_obj_face_of_some M A f F hf))), ht]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
  rw [Carrier.preimageFunctor_face_edgeHom_of_some M A f F hf i]
  rw [gammaCommaFunctor_obj_hom]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- 辺carrierへのcomma incidenceは同じ粗辺の恒等に限られ、厳密Γから到達する。 -/
theorem gammaComma_reachable_of_edge_carrier (e a : Nc.EdgeInTargetSubset A)
    (y : StructuredArrow (.edge e) (Carrier.preimageFunctor M A))
    (ha : (Carrier.preimageFunctor M A).obj y.right = .edge a) :
    ∃ x : GammaInc M A e, Nonempty ((gammaCommaFunctor M A e).obj x ⟶ y) := by
  have he := incHom_edge_edge_target e a (y.hom ≫ eqToHom ha)
  exact gammaComma_reachable_of_strict M A e y (ha.trans (congrArg Inc.edge he))

/-- 任意の辺comma対象は原始Γセルから到達する。mapped面のincidence位置も保持。 -/
theorem gammaComma_reachable (e : Nc.EdgeInTargetSubset A)
    (y : StructuredArrow (.edge e) (Carrier.preimageFunctor M A)) :
    ∃ x : GammaInc M A e, Nonempty ((gammaCommaFunctor M A e).obj x ⟶ y) := by
  cases hy : y.right with
  | chart c =>
    have hh := y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
      (Carrier.preimageFunctor_obj_chart M A c))
    cases hh
  | edge v =>
    cases hv : M.edgeMap v.1 with
    | none =>
      have hh := y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_edge_of_none M A v hv))
      cases hh
    | some a =>
      exact gammaComma_reachable_of_edge_carrier M A e
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) v a hv) y
        ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_edge_of_some M A v a hv))
  | face f =>
    cases hf : M.faceMap f.1 with
    | some F =>
      let hp := (congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)
      let hh := y.hom ≫ eqToHom hp
      cases ht : hh with
      | edgeFace _ _ i hi =>
        subst e
        exact gammaComma_reachable_of_mapped_face M A f F hf i y hy.symm ht
    | none =>
      rcases degenerate_face_cases M f.1 hf with hv | hl | hr
      · have hh := y.hom ≫ eqToHom (((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_face M A f)).trans
          (Carrier.face_of_vertical M A _ _ f hf hv.1 hv.2.1))
        cases hh
      · rcases hl with ⟨a, h0, h1, _⟩
        exact gammaComma_reachable_of_edge_carrier M A e
          (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge1 _ f) a h1) y
          (((congrArg (Carrier.preimageFunctor M A).obj hy).trans
            (Carrier.preimageFunctor_obj_face M A f)).trans
            (Carrier.face_of_mixed_left M A _ _ f hf h0 a h1))
      · rcases hr with ⟨a, h0, _, _⟩
        exact gammaComma_reachable_of_edge_carrier M A e
          (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge0 _ f) a h0) y
          (((congrArg (Carrier.preimageFunctor M A).obj hy).trans
            (Carrier.preimageFunctor_obj_face M A f)).trans
            (Carrier.face_of_mixed_right M A _ _ f hf a h0))

/-- 関手像から各対象へ到達できれば、commaの連結成分への写像は全射となる一般API。 -/
theorem mapConnectedComponents_surjective_of_reachable {J K : Type u}
    [Category.{u} J] [Category.{u} K] (F : J ⥤ K)
    (hr : ∀ y : K, ∃ x : J, Nonempty (F.obj x ⟶ y)) :
    Function.Surjective F.mapConnectedComponents := by
  intro c
  induction c using Quotient.inductionOn with
  | h y =>
    obtain ⟨x, ⟨f⟩⟩ := hr y
    refine ⟨CategoryTheory.ConnectedComponents.mk x, ?_⟩
    rw [Functor.mapConnectedComponents_mk]
    exact Quotient.sound (Zigzag.of_hom f)

/-- 原始Γから辺comma成分への写像は全射。任意M・任意Aの到達producerで放電する。 -/
theorem gammaComma_components_surjective (e : Nc.EdgeInTargetSubset A) :
    Function.Surjective (gammaCommaFunctor M A e).mapConnectedComponents :=
  mapConnectedComponents_surjective_of_reachable (gammaCommaFunctor M A e)
    (gammaComma_reachable M A e)

/-- 厳密辺carrierの同じcomma対象へ至るΓ原像は、原始incidenceのzigzagで連結。
同じ細対象への逆輸送射を作り、fully faithful包含の原像射を使う。 -/
theorem gammaComma_common_target_of_strict (e : Nc.EdgeInTargetSubset A)
    (y : StructuredArrow (.edge e) (Carrier.preimageFunctor M A))
    (hy : (Carrier.preimageFunctor M A).obj y.right = .edge e)
    (x x' : GammaInc M A e)
    (f : (gammaCommaFunctor M A e).obj x ⟶ y)
    (g : (gammaCommaFunctor M A e).obj x' ⟶ y) : Zigzag x x' := by
  obtain ⟨z, hz⟩ := gammaCellObj_surjective_of_carrier M A e y.right hy
  let b : y ⟶ (gammaCommaFunctor M A e).obj z := StructuredArrow.homMk (eqToHom hz.symm) (by
    rw [← cancel_mono (eqToHom (gammaCellObj_carrier M A e z))]
    exact (inc_endomorphism_eq_id (.edge e) _).trans (inc_endomorphism_eq_id (.edge e) _).symm)
  exact (Zigzag.of_hom ((gammaCommaFullyFaithful M A e).preimage (f ≫ b))).trans
    (Zigzag.of_hom ((gammaCommaFullyFaithful M A e).preimage (g ≫ b))).symm

/-- mapped面の同じ粗辺incidenceへ至るΓ原像は、その細面の同じ辺出現に限られる。
原始面射のコード保存から位置を同定し、mixed面を始域とする場合はOption像で排除する。 -/
theorem gammaComma_source_of_mapped_face
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3)
    (y : StructuredArrow
      (Inc.edge (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i) : Inc Nc A)
      (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)) =
      IncHom.edgeFace
        (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
        (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl)
    (x : GammaInc M A (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i))
    (g : (gammaCommaFunctor M A _).obj x ⟶ y) :
    gammaCellObj M A _ x = Inc.edge (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f i) := by
  rcases x with v | m
  · let gg : Inc.edge v.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
    cases hg : gg with
    | edgeFace _ _ j hj =>
      have hw : ((gammaCommaFunctor M A _).obj (.inl v)).hom ≫
          (Carrier.preimageFunctor M A).map gg ≫
            eqToHom (Carrier.preimageFunctor_obj_face_of_some M A f F hf) =
          IncHom.edgeFace
            (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
            (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl := by
        calc
          _ = ((gammaCommaFunctor M A _).obj (.inl v)).hom ≫
              (Carrier.preimageFunctor M A).map g.right ≫
                eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
                  (Carrier.preimageFunctor_obj_face_of_some M A f F hf)) := by
                    simp only [gg, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
          _ = _ := by rw [← Category.assoc, StructuredArrow.w, ht]
      rw [gammaCommaFunctor_obj_hom] at hw
      have hc := congrArg incHomCode hw
      rw [incHomCode_eqToHom_comp, incHomCode_comp_eqToHom, hg,
        Carrier.preimageFunctor_map_edgeFace_code_of_some M A v.1 f F hf j hj] at hc
      have hjit : j = i := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj hc))
      subst j
      exact congrArg Inc.edge hj
  · let gg : Inc.face m.1 ⟶ Inc.face f := g.right ≫ eqToHom hy.symm
    have hmf := Inc.face.inj (incHom_target_of_face m.1 gg)
    have hn : M.faceMap f.1 = none := by simpa only [hmf] using m.2.1
    cases hf.symm.trans hn

/-- mapped面の同じ粗辺incidenceへ至るΓ原像は、同じ細辺位置として連結する。 -/
theorem gammaComma_common_target_of_mapped_face
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3)
    (y : StructuredArrow
      (Inc.edge (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i) : Inc Nc A)
      (Carrier.preimageFunctor M A))
    (hy : Inc.face f = y.right)
    (ht : y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).symm.trans
        (Carrier.preimageFunctor_obj_face_of_some M A f F hf)) =
      IncHom.edgeFace
        (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i)
        (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i rfl)
    (x x' : GammaInc M A (faceEdge Nc A (M.targetSubsetFaceMap A _ (fun _ ht => ht) f F hf) i))
    (g : (gammaCommaFunctor M A _).obj x ⟶ y)
    (g' : (gammaCommaFunctor M A _).obj x' ⟶ y) : Zigzag x x' := by
  have hx := gammaComma_source_of_mapped_face M A f F hf i y hy ht x g
  have hx' := gammaComma_source_of_mapped_face M A f F hf i y hy ht x' g'
  exact Zigzag.of_hom (eqToHom ((gammaCellObj_injective M A _) (hx.trans hx'.symm)))

/-- 任意の厳密粗辺carrierへの共通原像はΓ内で連結する。 -/
theorem gammaComma_common_target_of_edge_carrier (e a : Nc.EdgeInTargetSubset A)
    (y : StructuredArrow (.edge e) (Carrier.preimageFunctor M A))
    (ha : (Carrier.preimageFunctor M A).obj y.right = .edge a)
    (x x' : GammaInc M A e)
    (f : (gammaCommaFunctor M A e).obj x ⟶ y)
    (g : (gammaCommaFunctor M A e).obj x' ⟶ y) : Zigzag x x' := by
  have he := incHom_edge_edge_target e a (y.hom ≫ eqToHom ha)
  exact gammaComma_common_target_of_strict M A e y (ha.trans (congrArg Inc.edge he)) x x' f g

/-- 原始Γ包含の任意の共通comma行先への原像は連結。成分単射性のproducer。 -/
theorem gammaComma_common_target (e : Nc.EdgeInTargetSubset A)
    (y : StructuredArrow (.edge e) (Carrier.preimageFunctor M A))
    (x x' : GammaInc M A e)
    (f : (gammaCommaFunctor M A e).obj x ⟶ y)
    (g : (gammaCommaFunctor M A e).obj x' ⟶ y) : Zigzag x x' := by
  cases hy : y.right with
  | chart c =>
    have hh := y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
      (Carrier.preimageFunctor_obj_chart M A c))
    cases hh
  | edge v =>
    cases hv : M.edgeMap v.1 with
    | none =>
      have hh := y.hom ≫ eqToHom ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_edge_of_none M A v hv))
      cases hh
    | some a =>
      exact gammaComma_common_target_of_edge_carrier M A e
        (M.targetSubsetEdgeMap A _ (fun _ ht => ht) v a hv) y
        ((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_edge_of_some M A v a hv)) x x' f g
  | face ff =>
    cases hf : M.faceMap ff.1 with
    | some F =>
      let hp := (congrArg (Carrier.preimageFunctor M A).obj hy).trans
        (Carrier.preimageFunctor_obj_face_of_some M A ff F hf)
      let hh := y.hom ≫ eqToHom hp
      cases ht : hh with
      | edgeFace _ _ i hi =>
        subst e
        exact gammaComma_common_target_of_mapped_face M A ff F hf i y hy.symm ht x x' f g
    | none =>
      rcases degenerate_face_cases M ff.1 hf with hv | hl | hr
      · have hh := y.hom ≫ eqToHom (((congrArg (Carrier.preimageFunctor M A).obj hy).trans
          (Carrier.preimageFunctor_obj_face M A ff)).trans
          (Carrier.face_of_vertical M A _ _ ff hf hv.1 hv.2.1))
        cases hh
      · rcases hl with ⟨a, h0, h1, _⟩
        exact gammaComma_common_target_of_edge_carrier M A e
          (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge1 _ ff) a h1) y
          (((congrArg (Carrier.preimageFunctor M A).obj hy).trans
            (Carrier.preimageFunctor_obj_face M A ff)).trans
            (Carrier.face_of_mixed_left M A _ _ ff hf h0 a h1)) x x' f g
      · rcases hr with ⟨a, h0, _, _⟩
        exact gammaComma_common_target_of_edge_carrier M A e
          (M.targetSubsetEdgeMap A _ (fun _ ht => ht) (Nf.targetSubsetFaceEdge0 _ ff) a h0) y
          (((congrArg (Carrier.preimageFunctor M A).obj hy).trans
            (Carrier.preimageFunctor_obj_face M A ff)).trans
            (Carrier.face_of_mixed_right M A _ _ ff hf a h0)) x x' f g

/-- A・設計§2のΓと辺comma成分の全単射。全射・単射のproducerを原始Mから渡す。 -/
def gammaComponentsEquiv (e : Nc.EdgeInTargetSubset A) :
    CategoryTheory.ConnectedComponents (GammaInc M A e) ≃
      CategoryTheory.ConnectedComponents (StructuredArrow (.edge e) (Carrier.preimageFunctor M A)) :=
  componentEquivOfCommonTargets (gammaCommaFunctor M A e)
    (gammaComma_reachable M A e) (gammaComma_common_target M A e)

/-- 原始Γからcommaへの成分同型の順向きは同じ包含関手の標準成分写像。 -/
@[simp] theorem gammaComponentsEquiv_apply (e : Nc.EdgeInTargetSubset A)
    (c : CategoryTheory.ConnectedComponents (GammaInc M A e)) :
    gammaComponentsEquiv M A e c = (gammaCommaFunctor M A e).mapConnectedComponents c := rfl

/-- A・設計§2の辺stalk成分式。独立した標準右Kan極限を原始Γ成分上の関数へ同定。 -/
def gammaCoefficientEquiv (e : Nc.EdgeInTargetSubset A) :
    (pushforwardCoefficients M A).obj (.edge e) ≃ₗ[ℚ]
      (CategoryTheory.ConnectedComponents (GammaInc M A e) → ℚ) :=
  ((coefficientCellIso (Carrier.preimageFunctor M A) (.edge e)).toLinearEquiv.trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : CategoryTheory.ConnectedComponents
      (StructuredArrow (.edge e) (Carrier.preimageFunctor M A)) => ULift.{u} ℚ)
      (gammaComponentsEquiv M A e).symm)).trans
    (LinearEquiv.piCongrRight (fun _ => ULift.moduleEquiv))

/-- 原始Γ成分での同じ右Kan係数評価。定義所有者API。 -/
@[simp] theorem gammaCoefficientEquiv_apply (e : Nc.EdgeInTargetSubset A)
    (z : (pushforwardCoefficients M A).obj (.edge e))
    (c : CategoryTheory.ConnectedComponents (GammaInc M A e)) :
    gammaCoefficientEquiv M A e z c =
      ((coefficientCellIso (Carrier.preimageFunctor M A) (.edge e)).hom z
        ((gammaCommaFunctor M A e).mapConnectedComponents c)).down := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCellObj_surjective_of_carrier
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_arrow_of_same_cell
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_reachable_of_strict
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_reachable_of_mapped_face
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_reachable_of_edge_carrier
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_reachable
#print axioms AAT.AG.AtlasCoefficientFiber.mapConnectedComponents_surjective_of_reachable
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_components_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_common_target_of_strict
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_source_of_mapped_face
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_common_target_of_mapped_face
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_common_target_of_edge_carrier
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComma_common_target
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComponentsEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCoefficientEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComponentsEquiv_apply
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
