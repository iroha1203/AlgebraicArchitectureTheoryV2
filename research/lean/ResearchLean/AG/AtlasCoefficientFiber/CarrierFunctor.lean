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

/-- 射の終点を等号輸送してもincidence位置は変わらない。 -/
@[simp] theorem incHomCode_comp_eqToHom {q : Reading Source} {N : TargetSupportedNerve q}
    {A : Set q.Target} {x y z : Inc N A} (f : x ⟶ y) (hyz : y = z) :
    incHomCode (f ≫ eqToHom hyz) = incHomCode f := by
  cases hyz
  cases f <;> rfl

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

/-- 台逆像carrierのchart値。下流の評価射で対象定義を展開せず使う。 -/
@[simp] theorem preimageFunctor_obj_chart (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac)) :
    (preimageFunctor M Ac).obj (.chart c) =
      .chart (chart M Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht) c) := rfl

/-- 台逆像carrierの辺値。原始Option像による公開計算式へ接続する。 -/
@[simp] theorem preimageFunctor_obj_edge (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac)) :
    (preimageFunctor M Ac).obj (.edge e) =
      edge M Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht) e := rfl

/-- 台逆像carrierの面値。退化三分類の公開計算式へ接続する。 -/
@[simp] theorem preimageFunctor_obj_face (Ac : Set qc.Target)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac)) :
    (preimageFunctor M Ac).obj (.face f) =
      face M Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht) f := rfl

/-- 台逆像carrierの端点射は同じ原始生成射と等号輸送である。 -/
theorem preimageFunctor_map_chartEdge (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (s : Bool) (he : c = edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' Ac) e s) :
    (preimageFunctor M Ac).map (IncHom.chartEdge c e s he) =
      eqToHom (congrArg (fun c => Inc.chart
        (chart M Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht) c)) he) ≫
        endpointHom M Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht) e s := rfl

/-- 台逆像carrierの辺面射は同じ原始生成射と等号輸送である。 -/
theorem preimageFunctor_map_edgeFace (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (i : Fin 3) (he : e = faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    (preimageFunctor M Ac).map (IncHom.edgeFace e f i he) =
      eqToHom (congrArg (edge M Ac (comparisonFactor qc qf h ⁻¹' Ac)
        (fun _ ht => ht)) he) ≫
        edgeHom M Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht) f i := rfl

/-- mapped辺の台逆像carrierを、支持輸送された同じ粗辺へ同定する。 -/
theorem preimageFunctor_obj_edge_of_some (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) :
    (preimageFunctor M Ac).obj (.edge e) =
      .edge (M.targetSubsetEdgeMap Ac (comparisonFactor qc qf h ⁻¹' Ac)
        (fun _ ht => ht) e a he) :=
  (preimageFunctor_obj_edge M Ac e).trans (edge_of_some M Ac _ _ e a he)

/-- 退化辺の台逆像carrierは同じ原始左端点chartである。 -/
theorem preimageFunctor_obj_edge_of_none (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (he : M.edgeMap e.1 = none) :
    (preimageFunctor M Ac).obj (.edge e) =
      .chart (chart M Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht)
        (Nf.targetSubsetEdgeLeft (comparisonFactor qc qf h ⁻¹' Ac) e)) :=
  (preimageFunctor_obj_edge M Ac e).trans (edge_of_none M Ac _ _ e he)

/-- mapped面の台逆像carrierを、支持輸送された同じ粗面へ同定する。 -/
theorem preimageFunctor_obj_face_of_some (Ac : Set qc.Target)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (a : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some a) :
    (preimageFunctor M Ac).obj (.face f) =
      .face (M.targetSubsetFaceMap Ac (comparisonFactor qc qf h ⁻¹' Ac)
        (fun _ ht => ht) f a hf) :=
  (preimageFunctor_obj_face M Ac f).trans (face_of_some M Ac _ _ f a hf)

/-- mapped辺の端点carrier射の全等号。対象輸送を忘却せず評価自然性へ渡す。 -/
theorem preimageFunctor_endpoint_of_some (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac)) (s : Bool)
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) :
    (preimageFunctor M Ac).map
        (IncHom.chartEdge (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' Ac) e s) e s rfl) ≫
        eqToHom (preimageFunctor_obj_edge_of_some M Ac e a he) =
      eqToHom (preimageFunctor_obj_chart M Ac
        (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' Ac) e s)) ≫
      IncHom.chartEdge
        (chart M Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht)
          (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' Ac) e s))
        (M.targetSubsetEdgeMap Ac (comparisonFactor qc qf h ⁻¹' Ac) (fun _ ht => ht) e a he)
        s (by
          cases s
          · exact M.targetSubsetChartMap_edgeLeft Ac _ _ e a he
          · exact M.targetSubsetChartMap_edgeRight Ac _ _ e a he) := by
  erw [preimageFunctor_map_chartEdge]
  simp only [eqToHom_refl, Category.id_comp]
  exact endpointHom_of_some M Ac _ _ e s a he

/-- 退化辺の端点carrier射の全等号。左右は同じchartへの等号輸送になる。 -/
theorem preimageFunctor_endpoint_of_none (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac)) (s : Bool)
    (he : M.edgeMap e.1 = none) :
    (preimageFunctor M Ac).map
        (IncHom.chartEdge (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' Ac) e s) e s rfl) ≫
        eqToHom (preimageFunctor_obj_edge_of_none M Ac e he) =
      eqToHom (preimageFunctor_obj_chart M Ac
        (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' Ac) e s)) ≫
      eqToHom (by
        apply congrArg Inc.chart
        cases s
        · rfl
        · exact (M.targetSubsetChartMap_edgeLeft_eq_right_of_none Ac _ _ e he).symm) := by
  erw [preimageFunctor_map_chartEdge]
  simp only [eqToHom_refl, Category.id_comp]
  exact endpointHom_of_none M Ac _ _ e s he

/-- mapped面の各細辺は同じ粗面の辺出現へ写る。位置iを保持する原始式。 -/
theorem preimageFunctor_face_edgeMap_of_some (Ac : Set qc.Target)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    M.edgeMap (faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i).1 =
      some (faceEdge Nc Ac (M.targetSubsetFaceMap Ac _ (fun _ ht => ht) f F hf) i).1 := by
  fin_cases i
  · exact M.face_some_edge0 f.1 F hf
  · exact M.face_some_edge1 f.1 F hf
  · exact M.face_some_edge2 f.1 F hf

/-- mapped面の辺の支持輸送は、粗面の同じ辺出現へ一致する。 -/
theorem preimageFunctor_face_edge_of_some (Ac : Set qc.Target)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    M.targetSubsetEdgeMap Ac _ (fun _ ht => ht)
      (faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i)
      (faceEdge Nc Ac (M.targetSubsetFaceMap Ac _ (fun _ ht => ht) f F hf) i).1
      (preimageFunctor_face_edgeMap_of_some M Ac f F hf i) =
      faceEdge Nc Ac (M.targetSubsetFaceMap Ac _ (fun _ ht => ht) f F hf) i := by
  apply Subtype.ext
  rfl

/-- mapped面の辺面carrier射の全等号。原始位置と対象輸送を含む。 -/
theorem preimageFunctor_face_edgeHom_of_some (Ac : Set qc.Target)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    (preimageFunctor M Ac).map
        (IncHom.edgeFace (faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) f i rfl) ≫
        eqToHom (preimageFunctor_obj_face_of_some M Ac f F hf) =
      eqToHom ((preimageFunctor_obj_edge M Ac _).trans (edge_of_face_some M Ac _ _ f F hf i)) ≫
        IncHom.edgeFace
          (faceEdge Nc Ac (M.targetSubsetFaceMap Ac _ (fun _ ht => ht) f F hf) i)
          (M.targetSubsetFaceMap Ac _ (fun _ ht => ht) f F hf) i rfl := by
  erw [preimageFunctor_map_edgeFace]
  simp only [eqToHom_refl, Category.id_comp]
  unfold edgeHom
  split
  · rename_i G hG
    have hGF : G = F := Option.some.inj (hG.symm.trans hf)
    subst G
    simp [mappedFaceEdgeHom, Category.assoc]
    rfl
  · rename_i hn
    cases hf.symm.trans hn

/-- 左辺退化型の辺面射コードは、原始分類から左端点/恒等へ定まる。 -/
theorem edgeHom_code_of_mixed_left (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e) (i : Fin 3) :
    incHomCode (edgeHom M Ac Af hs f i) =
      if i = 0 then .inr (.inl false) else .inl () := by
  unfold edgeHom
  split
  · rename_i F hF
    cases hf.symm.trans hF
  · split
    · rename_i a ha
      cases h0.symm.trans ha
    · split
      · exact mixedLeftFaceEdgeHom_code M Ac Af hs f _ _ _ _ _ i
      · rename_i hn
        cases h1.symm.trans hn

/-- 第三辺退化型の辺面射コードは、原始分類から恒等/右端点へ定まる。 -/
theorem edgeHom_code_of_mixed_right (f : Nf.FaceInTargetSubset Af)
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some e) (i : Fin 3) :
    incHomCode (edgeHom M Ac Af hs f i) =
      if i = 2 then .inr (.inl true) else .inl () := by
  unfold edgeHom
  split
  · rename_i F hF
    cases hf.symm.trans hF
  · split
    · exact mixedRightFaceEdgeHom_code M Ac Af hs f _ _ _ _ _ i
    · rename_i hn
      cases h0.symm.trans hn

/-- 左辺退化型のmapped辺から面carrierへの全射等号。 -/
theorem preimageFunctor_face_edgeHom_of_mixed_left (Ac : Set qc.Target)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e)
    (i : Fin 3) (hi : i ≠ 0)
    (he : M.edgeMap (faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i).1 = some e) :
    (preimageFunctor M Ac).map
        (IncHom.edgeFace (faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) f i rfl) ≫
        eqToHom ((preimageFunctor_obj_face M Ac f).trans
          (face_of_mixed_left M Ac _ _ f hf h0 e h1)) =
      eqToHom (preimageFunctor_obj_edge_of_some M Ac _ e he) ≫
        eqToHom (congrArg Inc.edge (by apply Subtype.ext; rfl)) := by
  apply incHomCode_injective
  erw [preimageFunctor_map_edgeFace]
  simp only [eqToHom_refl, Category.id_comp]
  rw [incHomCode_comp, edgeHom_code_of_mixed_left M Ac _ _ f hf e h0 h1 i]
  simp [hi, incidencePositionComp]

/-- 第三辺退化型のmapped辺から面carrierへの全射等号。 -/
theorem preimageFunctor_face_edgeHom_of_mixed_right (Ac : Set qc.Target)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (hf : M.faceMap f.1 = none) (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some e)
    (i : Fin 3) (hi : i ≠ 2)
    (he : M.edgeMap (faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i).1 = some e) :
    (preimageFunctor M Ac).map
        (IncHom.edgeFace (faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) f i rfl) ≫
        eqToHom ((preimageFunctor_obj_face M Ac f).trans
          (face_of_mixed_right M Ac _ _ f hf e h0)) =
      eqToHom (preimageFunctor_obj_edge_of_some M Ac _ e he) ≫
        eqToHom (congrArg Inc.edge (by apply Subtype.ext; rfl)) := by
  apply incHomCode_injective
  erw [preimageFunctor_map_edgeFace]
  simp only [eqToHom_refl, Category.id_comp]
  rw [incHomCode_comp, edgeHom_code_of_mixed_right M Ac _ _ f hf e h0 i]
  simp [hi, incidencePositionComp]

/-- mapped細面への任意の辺incidenceは、同じ粗辺出現コードを持つ。 -/
theorem preimageFunctor_map_edgeFace_code_of_some (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F)
    (i : Fin 3) (he : e = faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.edgeFace e f i he)) = .inr (.inr (.inl i)) := by
  rw [preimageFunctor_map_edgeFace, incHomCode_eqToHom_comp]
  unfold edgeHom
  split
  · rename_i G hG
    have hGF : G = F := Option.some.inj (hG.symm.trans hf)
    subst G
    simp only [mappedFaceEdgeHom, incHomCode_eqToHom_comp, incHomCode_comp_eqToHom]
    rfl
  · rename_i hn
    cases hf.symm.trans hn

/-- 台逆像carrierのchart面射は、生成dataの同じ頂点値である。 -/
theorem preimageFunctor_map_chartFace (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (i : Fin 3) (hc : c = faceVertex Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    (preimageFunctor M Ac).map (IncHom.chartFace c f i hc) =
      eqToHom (congrArg (fun c => Inc.chart (chart M Ac _ (fun _ ht => ht) c)) hc) ≫
        (incidenceData M Ac _ (fun _ ht => ht)).vertexHom f i := rfl

/-- 原始全退化型を含むchart面射の位置コード。選択は原始face/edge Option像で生成。 -/
theorem preimageFunctor_map_chartFace_code (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (i : Fin 3) (hc : c = faceVertex Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.chartFace c f i hc)) =
      faceVertexHomPosition M _ f i := by
  rw [preimageFunctor_map_chartFace, incHomCode_eqToHom_comp]
  fin_cases i
  · erw [IncidenceFunctorData.vertexHom_zero]
    erw [endpoint_edgeHom_code]
    rfl
  · erw [IncidenceFunctorData.vertexHom_one]
    erw [endpoint_edgeHom_code]
    rfl
  · erw [IncidenceFunctorData.vertexHom_two]
    erw [endpoint_edgeHom_code]
    rfl

/-- mapped面のchart射は同じ粗頂点位置のコードを持つ。 -/
theorem preimageFunctor_map_chartFace_code_of_some (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F)
    (i : Fin 3) (hc : c = faceVertex Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.chartFace c f i hc)) = .inr (.inr (.inr i)) := by
  rw [preimageFunctor_map_chartFace_code]
  simp only [faceVertexHomPosition, hf]

/-- mapped細面の頂点像は同じ粗頂点。原始端点と三辺の輸送から所属を導出。 -/
theorem preimageFunctor_face_vertex_of_some (Ac : Set qc.Target)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    chart M Ac _ (fun _ ht => ht) (faceVertex Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) =
      faceVertex Nc Ac (M.targetSubsetFaceMap Ac _ (fun _ ht => ht) f F hf) i := by
  fin_cases i
  · exact (M.targetSubsetChartMap_edgeLeft Ac _ _ (Nf.targetSubsetFaceEdge0 _ f)
      (Nc.nerve.faceEdge0 F) (M.face_some_edge0 f.1 F hf)).trans
      (congrArg (Nc.targetSubsetEdgeLeft Ac) (M.targetSubsetEdgeMap_faceEdge0 Ac _ _ f F hf))
  · exact (M.targetSubsetChartMap_edgeRight Ac _ _ (Nf.targetSubsetFaceEdge0 _ f)
      (Nc.nerve.faceEdge0 F) (M.face_some_edge0 f.1 F hf)).trans
      (congrArg (Nc.targetSubsetEdgeRight Ac) (M.targetSubsetEdgeMap_faceEdge0 Ac _ _ f F hf))
  · exact (M.targetSubsetChartMap_edgeRight Ac _ _ (Nf.targetSubsetFaceEdge1 _ f)
      (Nc.nerve.faceEdge1 F) (M.face_some_edge1 f.1 F hf)).trans
      (congrArg (Nc.targetSubsetEdgeRight Ac) (M.targetSubsetEdgeMap_faceEdge1 Ac _ _ f F hf))

/-- mapped面の頂点射は同じ粗chart面射へ全輸送を含めて可換。 -/
theorem preimageFunctor_face_vertexHom_of_some (Ac : Set qc.Target)
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (F : Nc.nerve.FaceComponent) (hf : M.faceMap f.1 = some F) (i : Fin 3) :
    (preimageFunctor M Ac).map (IncHom.chartFace
        (faceVertex Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) f i rfl) ≫
        eqToHom (preimageFunctor_obj_face_of_some M Ac f F hf) =
      eqToHom ((preimageFunctor_obj_chart M Ac _).trans
        (congrArg Inc.chart (preimageFunctor_face_vertex_of_some M Ac f F hf i))) ≫
        IncHom.chartFace
          (faceVertex Nc Ac (M.targetSubsetFaceMap Ac _ (fun _ ht => ht) f F hf) i)
          (M.targetSubsetFaceMap Ac _ (fun _ ht => ht) f F hf) i rfl := by
  apply incHomCode_injective
  rw [incHomCode_comp_eqToHom, preimageFunctor_map_chartFace_code_of_some M Ac _ f F hf i rfl,
    incHomCode_eqToHom_comp]
  rfl

/-- mapped細辺の端点像は同じ粗端点。原始左右端点APIから生成する所属。 -/
theorem preimageFunctor_edge_endpoint_of_some (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a) (s : Bool) :
    chart M Ac _ (fun _ ht => ht) (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' Ac) e s) =
      edgeEndpoint Nc Ac (M.targetSubsetEdgeMap Ac _ (fun _ ht => ht) e a he) s := by
  cases s
  · exact M.targetSubsetChartMap_edgeLeft Ac _ _ e a he
  · exact M.targetSubsetChartMap_edgeRight Ac _ _ e a he

/-- mapped細辺へのchart射は同じ左右出現コードを持つ。Φの端点対応のAPI。 -/
theorem preimageFunctor_map_chartEdge_code_of_some (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (a : Nc.nerve.EdgeComponent) (he : M.edgeMap e.1 = some a)
    (s : Bool) (hc : c = edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' Ac) e s) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.chartEdge c e s hc)) = .inr (.inl s) := by
  rw [preimageFunctor_map_chartEdge, incHomCode_eqToHom_comp]
  exact endpointHom_code_some M Ac _ _ e s a he

/-- mixed左型の辺面射コードを、同じ原始edgeFace出現へ接続する。 -/
theorem preimageFunctor_map_edgeFace_code_of_mixed_left (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some a) (i : Fin 3)
    (he : e = faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.edgeFace e f i he)) =
      if i = 0 then .inr (.inl false) else .inl () := by
  rw [preimageFunctor_map_edgeFace, incHomCode_eqToHom_comp]
  exact edgeHom_code_of_mixed_left M Ac _ _ f hf a h0 h1 i

/-- mixed右型の辺面射コードを、同じ原始edgeFace出現へ接続する。 -/
theorem preimageFunctor_map_edgeFace_code_of_mixed_right (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some a) (i : Fin 3)
    (he : e = faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.edgeFace e f i he)) =
      if i = 2 then .inr (.inl true) else .inl () := by
  rw [preimageFunctor_map_edgeFace, incHomCode_eqToHom_comp]
  exact edgeHom_code_of_mixed_right M Ac _ _ f hf a h0 i

/-- mixed左型の頂点位置は、collapsed側では左、反対頂点では右となる。 -/
theorem preimageFunctor_map_chartFace_code_of_mixed_left (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some a) (i : Fin 3)
    (hc : c = faceVertex Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.chartFace c f i hc)) = .inr (.inl (i == 2)) := by
  rw [preimageFunctor_map_chartFace_code]
  simp only [faceVertexHomPosition, hf, h0, h1]

/-- mixed右型の頂点位置は、反対頂点では左、collapsed側では右となる。 -/
theorem preimageFunctor_map_chartFace_code_of_mixed_right (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (hf : M.faceMap f.1 = none) (a : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some a) (i : Fin 3)
    (hc : c = faceVertex Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.chartFace c f i hc)) = .inr (.inl (i != 0)) := by
  rw [preimageFunctor_map_chartFace_code]
  simp only [faceVertexHomPosition, hf, h0]

/-- 退化辺の任意の端点射は恒等位置へ写る。台包含自然性の所有API。 -/
theorem preimageFunctor_map_chartEdge_code_of_none (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (he : M.edgeMap e.1 = none) (s : Bool)
    (hc : c = edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' Ac) e s) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.chartEdge c e s hc)) = .inl () := by
  rw [preimageFunctor_map_chartEdge, incHomCode_eqToHom_comp]
  exact endpointHom_code_none M Ac _ _ e s he

/-- 垂直面の任意の辺面射は同じ恒等位置へ写る。 -/
theorem preimageFunctor_map_edgeFace_code_of_vertical (Ac : Set qc.Target)
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (hf : M.faceMap f.1 = none)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = none) (i : Fin 3)
    (he : e = faceEdge Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.edgeFace e f i he)) = .inl () := by
  rw [preimageFunctor_map_edgeFace, incHomCode_eqToHom_comp]
  unfold edgeHom
  split
  · rename_i F hF
    cases hf.symm.trans hF
  · split
    · rename_i a ha
      cases h0.symm.trans ha
    · split
      · rename_i a ha
        cases h1.symm.trans ha
      · exact verticalFaceEdgeHom_code M Ac _ _ f _ _ _ _ i

/-- 垂直面の任意の頂点射も同じ恒等位置へ写る。 -/
theorem preimageFunctor_map_chartFace_code_of_vertical (Ac : Set qc.Target)
    (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' Ac))
    (hf : M.faceMap f.1 = none)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = none) (i : Fin 3)
    (hc : c = faceVertex Nf (comparisonFactor qc qf h ⁻¹' Ac) f i) :
    incHomCode ((preimageFunctor M Ac).map (IncHom.chartFace c f i hc)) = .inl () := by
  rw [preimageFunctor_map_chartFace_code]
  simp only [faceVertexHomPosition, hf, h0, h1]

end Carrier
end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.incidencePositionComp
#print axioms AAT.AG.AtlasCoefficientFiber.incHomCode_comp
#print axioms AAT.AG.AtlasCoefficientFiber.incHomCode_eqToHom
#print axioms AAT.AG.AtlasCoefficientFiber.incHomCode_eqToHom_comp
#print axioms AAT.AG.AtlasCoefficientFiber.incHomCode_comp_eqToHom
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
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_obj_chart
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_obj_edge
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_obj_face
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_chartEdge
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_edgeFace
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_obj_edge_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_obj_edge_of_none
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_obj_face_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_endpoint_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_endpoint_of_none
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_face_edgeMap_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_face_edge_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_face_edgeHom_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.edgeHom_code_of_mixed_left
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.edgeHom_code_of_mixed_right
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_face_edgeHom_of_mixed_left
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_face_edgeHom_of_mixed_right
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_edgeFace_code_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_chartFace
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_chartFace_code
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_chartFace_code_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_face_vertex_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_face_vertexHom_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_edge_endpoint_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_chartEdge_code_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_edgeFace_code_of_mixed_left
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_edgeFace_code_of_mixed_right
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_chartFace_code_of_mixed_left
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_chartFace_code_of_mixed_right
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_chartEdge_code_of_none
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_edgeFace_code_of_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.preimageFunctor_map_chartFace_code_of_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.edge.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.mixedLeftFaceEdgeHom.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.mixedRightFaceEdgeHom.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
