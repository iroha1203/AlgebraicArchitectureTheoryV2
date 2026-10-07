import ResearchLean.AG.AtlasCoefficientFiber.Carrier

/-!
# G-135 A：原始Mが生成するcarrier関手

## Implementation notes

Option像と原始退化分類から面incidenceの射を計算し、三角形関係を証明する。
関係を新しい入力fieldとして受け取る案は、原始Mからの生成義務を移すため採らない。
各退化型を場合分けし、混在面のmapped二辺は恒等射、垂直辺は指定端点射へ送る。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision CategoryTheory
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
/-- incidence位置表示の合成。非恒等合成は端点位置から頂点位置を計算する。 -/
def incidencePositionComp :
    (Unit ⊕ Bool ⊕ Fin 3 ⊕ Fin 3) → (Unit ⊕ Bool ⊕ Fin 3 ⊕ Fin 3) →
      Unit ⊕ Bool ⊕ Fin 3 ⊕ Fin 3
  | .inl _, b => b
  | a, .inl _ => a
  | .inr (.inl s), .inr (.inr (.inl i)) => .inr (.inr (.inr (endpointPosition i s)))
  | _, _ => .inl ()

/-- 合成可能なincidence射の位置表示は上の合成表に従う。 -/
theorem incHomCode_comp {q : Reading Source} {N : TargetSupportedNerve q}
    {A : Set q.Target} {x y z : Inc N A} (f : x ⟶ y) (g : y ⟶ z) :
    incHomCode (f ≫ g) = incidencePositionComp (incHomCode f) (incHomCode g) := by
  cases f <;> cases g <;> rfl

/-- 等号輸送は恒等位置を持つ。 -/
@[simp] theorem incHomCode_eqToHom {q : Reading Source} {N : TargetSupportedNerve q}
    {A : Set q.Target} {x y : Inc N A} (hxy : x = y) :
    incHomCode (eqToHom hxy) = .inl () := by
  cases hxy
  rfl

/-- 射の始点を等号輸送してもincidence位置は変わらない。 -/
@[simp] theorem incHomCode_eqToHom_comp {q : Reading Source} {N : TargetSupportedNerve q}
    {A : Set q.Target} {x y z : Inc N A} (hxy : x = y) (g : y ⟶ z) :
    incHomCode (eqToHom hxy ≫ g) = incHomCode g := by
  cases hxy
  cases g <;> rfl

namespace Carrier
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (Ac : Set qc.Target) (Af : Set qf.Target)
variable (hs : ∀ t, t ∈ Af → comparisonFactor qc qf h t ∈ Ac)

/-- mapped端点射の値を、carrier等号を含めて表示する。 -/
theorem endpointHom_of_some (e : Nf.EdgeInTargetSubset Af) (s : Bool)
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) :
    endpointHom M Ac Af hs e s ≫ eqToHom (edge_of_some M Ac Af hs e a he) =
      IncHom.chartEdge (chart M Ac Af hs (edgeEndpoint Nf Af e s))
        (M.targetSubsetEdgeMap Ac Af hs e a he) s (by
          cases s
          · exact M.targetSubsetChartMap_edgeLeft Ac Af hs e a he
          · exact M.targetSubsetChartMap_edgeRight Ac Af hs e a he) := by
  unfold endpointHom
  split
  · rename_i hn
    cases he.symm.trans hn
  · rename_i b hb
    have hab : b = a := Option.some.inj (hb.symm.trans he)
    subst b
    simp [Category.assoc]

/-- 退化端点射は同じchartへの等号輸送である。 -/
theorem endpointHom_of_none (e : Nf.EdgeInTargetSubset Af) (s : Bool)
    (he : M.edgeMap e.1 = none) :
    endpointHom M Ac Af hs e s ≫ eqToHom (edge_of_none M Ac Af hs e he) =
      eqToHom (by
        apply congrArg Inc.chart
        cases s
        · rfl
        · exact (M.targetSubsetChartMap_edgeLeft_eq_right_of_none Ac Af hs e he).symm) := by
  unfold endpointHom
  split
  · simp
  · rename_i a ha
    cases he.symm.trans ha

/-- mapped面の辺carrierは、粗面の同じ辺出現である。 -/
theorem edge_of_face_some (f : Nf.FaceInTargetSubset Af)
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    edge M Ac Af hs (faceEdge Nf Af f i) =
      Inc.edge (faceEdge Nc Ac (M.targetSubsetFaceMap Ac Af hs f F hf) i) := by
  fin_cases i
  · simpa [faceEdge] using
      (edge_of_some M Ac Af hs (Nf.targetSubsetFaceEdge0 Af f)
        (Nc.nerve.faceEdge0 F) (M.face_some_edge0 f.1 F hf)).trans
        (congrArg Inc.edge (M.targetSubsetEdgeMap_faceEdge0 Ac Af hs f F hf))
  · simpa [faceEdge] using
      (edge_of_some M Ac Af hs (Nf.targetSubsetFaceEdge1 Af f)
        (Nc.nerve.faceEdge1 F) (M.face_some_edge1 f.1 F hf)).trans
        (congrArg Inc.edge (M.targetSubsetEdgeMap_faceEdge1 Ac Af hs f F hf))
  · simpa [faceEdge] using
      (edge_of_some M Ac Af hs (Nf.targetSubsetFaceEdge2 Af f)
        (Nc.nerve.faceEdge2 F) (M.face_some_edge2 f.1 F hf)).trans
        (congrArg Inc.edge (M.targetSubsetEdgeMap_faceEdge2 Ac Af hs f F hf))

/-- mapped面への生成射は同じ粗辺出現への射である。 -/
def mappedFaceEdgeHom (f : Nf.FaceInTargetSubset Af)
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    edge M Ac Af hs (faceEdge Nf Af f i) ⟶ face M Ac Af hs f :=
  eqToHom (edge_of_face_some M Ac Af hs f F hf i) ≫
    IncHom.edgeFace _ _ i rfl ≫ eqToHom (face_of_some M Ac Af hs f F hf).symm

/-- mapped端点射は左右の出現コードを保つ。 -/
theorem endpointHom_code_some (e : Nf.EdgeInTargetSubset Af) (s : Bool)
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) :
    incHomCode (endpointHom M Ac Af hs e s) = .inr (.inl s) := by
  unfold endpointHom
  split
  · rename_i hn
    cases he.symm.trans hn
  · rw [incHomCode_comp, incHomCode_eqToHom]
    rfl

/-- 退化端点射は恒等位置を持つ。 -/
theorem endpointHom_code_none (e : Nf.EdgeInTargetSubset Af) (s : Bool)
    (he : M.edgeMap e.1 = none) :
    incHomCode (endpointHom M Ac Af hs e s) = .inl () := by
  unfold endpointHom
  split
  · simp
  · rename_i a ha
    cases he.symm.trans ha

/-- mapped面の辺射は三つの辺出現コードを保つ。 -/
theorem mappedFaceEdgeHom_code (f : Nf.FaceInTargetSubset Af)
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    incHomCode (mappedFaceEdgeHom M Ac Af hs f F hf i) = .inr (.inr (.inl i)) := by
  unfold mappedFaceEdgeHom
  rw [incHomCode_comp, incHomCode_comp, incHomCode_eqToHom, incHomCode_eqToHom]
  rfl

/-- mapped面の全辺における端点出現コード。 -/
theorem endpoint_face_some_code (f : Nf.FaceInTargetSubset Af)
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) (s : Bool) :
    incHomCode (endpointHom M Ac Af hs (faceEdge Nf Af f i) s) = .inr (.inl s) := by
  fin_cases i
  · exact endpointHom_code_some M Ac Af hs _ s _ (M.face_some_edge0 f.1 F hf)
  · exact endpointHom_code_some M Ac Af hs _ s _ (M.face_some_edge1 f.1 F hf)
  · exact endpointHom_code_some M Ac Af hs _ s _ (M.face_some_edge2 f.1 F hf)

/-- 第一辺がmappedの退化面では第二辺は同じ像、第三辺は垂直である。 -/
theorem face_none_edge0_some (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some e) :
    M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e ∧
      M.edgeMap (Nf.nerve.faceEdge2 f.1) = none := by
  rcases degenerate_face_cases M f.1 hf with hv | hl | hr
  · cases h0.symm.trans hv.1
  · obtain ⟨a, ha, _, _⟩ := hl
    cases h0.symm.trans ha
  · obtain ⟨a, ha, h1, h2⟩ := hr
    have he : a = e := Option.some.inj (ha.symm.trans h0)
    subst a
    exact ⟨h1, h2⟩

/-- 第一辺が垂直の退化面では第二・第三辺のOption像は等しい。 -/
theorem face_none_edge0_none (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none) :
    M.edgeMap (Nf.nerve.faceEdge1 f.1) = M.edgeMap (Nf.nerve.faceEdge2 f.1) := by
  rcases degenerate_face_cases M f.1 hf with hv | hl | hr
  · exact hv.2.1.trans hv.2.2.symm
  · obtain ⟨a, _, h1, h2⟩ := hl
    exact h1.trans h2.symm
  · obtain ⟨a, ha, _, _⟩ := hr
    cases h0.symm.trans ha

/-- 垂直面では全辺carrierが同じchart carrierへ一致する。 -/
theorem vertical_edge_eq_face (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = none)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = none) (i : Fin 3) :
    edge M Ac Af hs (faceEdge Nf Af f i) = face M Ac Af hs f := by
  rw [face_of_vertical M Ac Af hs f hf h0 h1]
  fin_cases i
  · exact edge_of_none M Ac Af hs _ h0
  · exact (edge_of_none M Ac Af hs _ h1).trans
      (congrArg Inc.chart (congrArg (chart M Ac Af hs)
        (Nf.targetSubset_left_faceEdge0_eq_left_faceEdge1 Af f).symm))
  · exact (edge_of_none M Ac Af hs _ h2).trans
      (congrArg Inc.chart ((congrArg (chart M Ac Af hs)
        (Nf.targetSubset_right_faceEdge0_eq_left_faceEdge2 Af f).symm).trans
        (M.targetSubsetChartMap_edgeLeft_eq_right_of_none Ac Af hs
          (Nf.targetSubsetFaceEdge0 Af f) h0).symm))

/-- 垂直面の各辺incidenceは等号輸送へ写る。 -/
def verticalFaceEdgeHom (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = none)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = none) (i : Fin 3) :
    edge M Ac Af hs (faceEdge Nf Af f i) ⟶ face M Ac Af hs f :=
  eqToHom (vertical_edge_eq_face M Ac Af hs f hf h0 h1 h2 i)

/-- 左辺退化型では、垂直辺を左端点射、mapped二辺を恒等射へ送る。 -/
def mixedLeftFaceEdgeHom (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = some e) :
    ∀ i, edge M Ac Af hs (faceEdge Nf Af f i) ⟶ face M Ac Af hs f
  | 0 => eqToHom (edge_of_none M Ac Af hs (Nf.targetSubsetFaceEdge0 Af f) h0) ≫
      IncHom.chartEdge _ (M.targetSubsetEdgeMap Ac Af hs (Nf.targetSubsetFaceEdge1 Af f) e h1)
        false ((congrArg (chart M Ac Af hs)
          (Nf.targetSubset_left_faceEdge0_eq_left_faceEdge1 Af f)).trans
          (M.targetSubsetChartMap_edgeLeft Ac Af hs (Nf.targetSubsetFaceEdge1 Af f) e h1)) ≫
      eqToHom (face_of_mixed_left M Ac Af hs f hf h0 e h1).symm
  | 1 => eqToHom ((edge_of_some M Ac Af hs (Nf.targetSubsetFaceEdge1 Af f) e h1).trans
      (face_of_mixed_left M Ac Af hs f hf h0 e h1).symm)
  | 2 => eqToHom ((edge_of_some M Ac Af hs (Nf.targetSubsetFaceEdge2 Af f) e h2).trans
      ((congrArg Inc.edge (by apply Subtype.ext; rfl)).trans
        (face_of_mixed_left M Ac Af hs f hf h0 e h1).symm))

/-- 第三辺退化型では、垂直辺を右端点射、mapped二辺を恒等射へ送る。 -/
def mixedRightFaceEdgeHom (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some e)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = none) :
    ∀ i, edge M Ac Af hs (faceEdge Nf Af f i) ⟶ face M Ac Af hs f
  | 0 => eqToHom ((edge_of_some M Ac Af hs (Nf.targetSubsetFaceEdge0 Af f) e h0).trans
      (face_of_mixed_right M Ac Af hs f hf e h0).symm)
  | 1 => eqToHom ((edge_of_some M Ac Af hs (Nf.targetSubsetFaceEdge1 Af f) e h1).trans
      ((congrArg Inc.edge (by apply Subtype.ext; rfl)).trans
        (face_of_mixed_right M Ac Af hs f hf e h0).symm))
  | 2 => eqToHom (edge_of_none M Ac Af hs (Nf.targetSubsetFaceEdge2 Af f) h2) ≫
      IncHom.chartEdge _ (M.targetSubsetEdgeMap Ac Af hs (Nf.targetSubsetFaceEdge0 Af f) e h0)
        true ((congrArg (chart M Ac Af hs)
          (Nf.targetSubset_right_faceEdge0_eq_left_faceEdge2 Af f).symm).trans
          (M.targetSubsetChartMap_edgeRight Ac Af hs (Nf.targetSubsetFaceEdge0 Af f) e h0)) ≫
      eqToHom (face_of_mixed_right M Ac Af hs f hf e h0).symm

/-- 垂直面射の位置コード。 -/
theorem verticalFaceEdgeHom_code (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = none)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = none) (i : Fin 3) :
    incHomCode (verticalFaceEdgeHom M Ac Af hs f hf h0 h1 h2 i) = .inl () :=
  incHomCode_eqToHom _

/-- 左辺退化型の面射位置は左端点、恒等、恒等である。 -/
theorem mixedLeftFaceEdgeHom_code (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = some e) (i : Fin 3) :
    incHomCode (mixedLeftFaceEdgeHom M Ac Af hs f hf e h0 h1 h2 i) =
      if i = 0 then .inr (.inl false) else .inl () := by
  fin_cases i
  · dsimp only [mixedLeftFaceEdgeHom]
    rw [incHomCode_comp, incHomCode_comp, incHomCode_eqToHom, incHomCode_eqToHom]
    rfl
  · simp [mixedLeftFaceEdgeHom]
  · simp [mixedLeftFaceEdgeHom]

/-- 第三辺退化型の面射位置は恒等、恒等、右端点である。 -/
theorem mixedRightFaceEdgeHom_code (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some e)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e)
    (h2 : M.edgeMap (Nf.nerve.faceEdge2 f.1) = none) (i : Fin 3) :
    incHomCode (mixedRightFaceEdgeHom M Ac Af hs f hf e h0 h1 h2 i) =
      if i = 2 then .inr (.inl true) else .inl () := by
  fin_cases i
  · simp [mixedRightFaceEdgeHom]
  · simp [mixedRightFaceEdgeHom]
  · dsimp only [mixedRightFaceEdgeHom]
    rw [incHomCode_comp, incHomCode_comp, incHomCode_eqToHom, incHomCode_eqToHom]
    rfl

/-- 全面incidence射を原始MのOption像と退化分類から生成する。 -/
def edgeHom (f : Nf.FaceInTargetSubset Af) (i : Fin 3) :
    edge M Ac Af hs (faceEdge Nf Af f i) ⟶ face M Ac Af hs f :=
  match hf : M.faceMap f.1 with
  | some F => mappedFaceEdgeHom M Ac Af hs f F hf i
  | none =>
    match h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) with
    | some e => mixedRightFaceEdgeHom M Ac Af hs f hf e h0
        (face_none_edge0_some M Af f hf e h0).1
        (face_none_edge0_some M Af f hf e h0).2 i
    | none =>
      match h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) with
      | some e => mixedLeftFaceEdgeHom M Ac Af hs f hf e h0 h1
          ((face_none_edge0_none M Af f hf h0).symm.trans h1) i
      | none => verticalFaceEdgeHom M Ac Af hs f hf h0 h1
          ((face_none_edge0_none M Af f hf h0).symm.trans h1) i

/-- 面carrierにおける三頂点の位置。混在型では隣接二頂点を同じ端点へ送る。 -/
def faceVertexHomPosition (f : Nf.FaceInTargetSubset Af) (i : Fin 3) :
    Unit ⊕ Bool ⊕ Fin 3 ⊕ Fin 3 :=
  match M.faceMap f.1 with
  | some _ => .inr (.inr (.inr i))
  | none =>
    match M.edgeMap (Nf.nerve.faceEdge0 f.1) with
    | some _ => .inr (.inl (i != 0))
    | none =>
      match M.edgeMap (Nf.nerve.faceEdge1 f.1) with
      | some _ => .inr (.inl (i == 2))
      | none => .inl ()

/-- 全六経路のcarrier位置は、その原始三角形頂点だけに依存する。 -/
theorem endpoint_edgeHom_code (f : Nf.FaceInTargetSubset Af) (i : Fin 3) (s : Bool) :
    incHomCode (endpointHom M Ac Af hs (faceEdge Nf Af f i) s ≫ edgeHom M Ac Af hs f i) =
      faceVertexHomPosition M Af f (endpointPosition i s) := by
  unfold edgeHom
  split
  · rename_i F hf
    rw [incHomCode_comp, endpoint_face_some_code M Ac Af hs f F hf,
      mappedFaceEdgeHom_code]
    simp only [faceVertexHomPosition, hf]
    rfl
  · rename_i hf
    split
    · rename_i e h0
      have hh := face_none_edge0_some M Af f hf e h0
      rw [incHomCode_comp, mixedRightFaceEdgeHom_code]
      fin_cases i <;> cases s
      all_goals first
        | erw [endpointHom_code_some M Ac Af hs (faceEdge Nf Af f 0) _ e h0]
        | erw [endpointHom_code_some M Ac Af hs (faceEdge Nf Af f 1) _ e hh.1]
        | erw [endpointHom_code_none M Ac Af hs (faceEdge Nf Af f 2) _ hh.2]
      all_goals simp [faceVertexHomPosition, hf, h0, endpointPosition, incidencePositionComp]
    · rename_i h0
      split
      · rename_i e h1
        have h2 := (face_none_edge0_none M Af f hf h0).symm.trans h1
        rw [incHomCode_comp, mixedLeftFaceEdgeHom_code]
        fin_cases i <;> cases s
        all_goals first
          | erw [endpointHom_code_none M Ac Af hs (faceEdge Nf Af f 0) _ h0]
          | erw [endpointHom_code_some M Ac Af hs (faceEdge Nf Af f 1) _ e h1]
          | erw [endpointHom_code_some M Ac Af hs (faceEdge Nf Af f 2) _ e h2]
        all_goals simp [faceVertexHomPosition, hf, h0, h1, endpointPosition, incidencePositionComp]
      · rename_i h1
        have h2 := (face_none_edge0_none M Af f hf h0).symm.trans h1
        rw [incHomCode_comp, verticalFaceEdgeHom_code]
        fin_cases i <;> cases s
        all_goals first
          | erw [endpointHom_code_none M Ac Af hs (faceEdge Nf Af f 0) _ h0]
          | erw [endpointHom_code_none M Ac Af hs (faceEdge Nf Af f 1) _ h1]
          | erw [endpointHom_code_none M Ac Af hs (faceEdge Nf Af f 2) _ h2]
        all_goals simp [faceVertexHomPosition, hf, h0, h1, incidencePositionComp]

/-- 原始Mから生成射と三関係を放電したincidence関手data。 -/
def incidenceData : IncidenceFunctorData Nf Af (Inc Nc Ac) where
  chartObj := fun c => .chart (chart M Ac Af hs c)
  edgeObj := edge M Ac Af hs
  faceObj := face M Ac Af hs
  endpointHom := endpointHom M Ac Af hs
  edgeHom := edgeHom M Ac Af hs
  triangle_zero f := by
    apply incHomCode_injective
    erw [incHomCode_eqToHom_comp, endpoint_edgeHom_code, endpoint_edgeHom_code]
    rfl
  triangle_one f := by
    apply incHomCode_injective
    erw [incHomCode_eqToHom_comp, endpoint_edgeHom_code, endpoint_edgeHom_code]
    rfl
  triangle_two f := by
    apply incHomCode_injective
    erw [incHomCode_eqToHom_comp, endpoint_edgeHom_code, endpoint_edgeHom_code]
    rfl

/-- 原始セルの比較Mだけから構成するcarrier関手。 -/
def functor : Inc Nf Af ⥤ Inc Nc Ac :=
  (incidenceData M Ac Af hs).functor

/-- carrier関手のchart値。 -/
@[simp] theorem functor_obj_chart (c : Nf.ChartInTargetSubset Af) :
    (functor M Ac Af hs).obj (.chart c) = .chart (chart M Ac Af hs c) := rfl

/-- carrier関手の辺値。 -/
@[simp] theorem functor_obj_edge (e : Nf.EdgeInTargetSubset Af) :
    (functor M Ac Af hs).obj (.edge e) = edge M Ac Af hs e := rfl

/-- carrier関手の面値。 -/
@[simp] theorem functor_obj_face (f : Nf.FaceInTargetSubset Af) :
    (functor M Ac Af hs).obj (.face f) = face M Ac Af hs f := rfl

/-- carrier関手の端点射は等号輸送を含む原始生成式である。 -/
theorem functor_map_chartEdge (c : Nf.ChartInTargetSubset Af)
    (e : Nf.EdgeInTargetSubset Af) (s : Bool) (he : c = edgeEndpoint Nf Af e s) :
    (functor M Ac Af hs).map (IncHom.chartEdge c e s he) =
      eqToHom (congrArg (fun c => Inc.chart (chart M Ac Af hs c)) he) ≫
        endpointHom M Ac Af hs e s := rfl

/-- carrier関手の辺面射は等号輸送を含む原始生成式である。 -/
theorem functor_map_edgeFace (e : Nf.EdgeInTargetSubset Af)
    (f : Nf.FaceInTargetSubset Af) (i : Fin 3) (he : e = faceEdge Nf Af f i) :
    (functor M Ac Af hs).map (IncHom.edgeFace e f i he) =
      eqToHom (congrArg (edge M Ac Af hs) he) ≫ edgeHom M Ac Af hs f i := rfl

/-- T0の台逆像に沿うcarrier。支持輸送を追加の入力にしない。 -/
def preimageFunctor (Ac : Set qc.Target) :
    Inc Nf (comparisonFactor qc qf h ⁻¹' Ac) ⥤ Inc Nc Ac :=
  functor M Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht)

end Carrier
end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.incidencePositionComp
#print axioms AAT.AG.AtlasCoefficientFiber.incHomCode_comp
#print axioms AAT.AG.AtlasCoefficientFiber.incHomCode_eqToHom
#print axioms AAT.AG.AtlasCoefficientFiber.incHomCode_eqToHom_comp
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.endpointHom_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.endpointHom_of_none
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.edge_of_face_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.mappedFaceEdgeHom
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.endpointHom_code_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.endpointHom_code_none
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.mappedFaceEdgeHom_code
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.endpoint_face_some_code
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.face_none_edge0_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.face_none_edge0_none
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.vertical_edge_eq_face
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.verticalFaceEdgeHom
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.mixedLeftFaceEdgeHom
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.mixedRightFaceEdgeHom
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.verticalFaceEdgeHom_code
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.mixedLeftFaceEdgeHom_code
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.mixedRightFaceEdgeHom_code
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.edgeHom
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.faceVertexHomPosition
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.endpoint_edgeHom_code
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.incidenceData
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.functor
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.functor_obj_chart
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.functor_obj_edge
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.functor_obj_face
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.functor_map_chartEdge
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.functor_map_edgeFace
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
