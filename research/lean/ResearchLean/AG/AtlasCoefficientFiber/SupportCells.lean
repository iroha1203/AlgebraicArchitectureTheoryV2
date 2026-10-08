import ResearchLean.AG.AtlasCoefficientFiber.CarrierFunctor
import ResearchLean.AG.FaceRelationSubdivision.SubsetRestriction

/-!
# G-135 D：台包含が生成する同じセルとincidenceの包含

## Implementation notes

包含は元のセル名と出現位置を保持する。左右端点・三辺・三頂点の
同じ原始計算から圏の関手を作り、台包含を別の関手入力へ移さない。
セル集合の半順序に交換する案はloopや重複辺の出現を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {q : Reading Source}

/-- 台包含による同じ名前付き支持セルの包含。 -/
def supportCellInclude {T I : Type u} (s : I → Set T) {A B : Set T}
    (hab : A ⊆ B) (i : Selected s A) : Selected s B :=
  ⟨i.1, by obtain ⟨t, ht, ha⟩ := i.2; exact ⟨t, ht, hab ha⟩⟩

/-- 原セル名は包含で変わらない。 -/
@[simp] theorem supportCellInclude_val {T I : Type u} (s : I → Set T) {A B : Set T}
    (hab : A ⊆ B) (i : Selected s A) : (supportCellInclude s hab i).1 = i.1 := rfl

/-- 同じ台のセル包含は恒等。 -/
@[simp] theorem supportCellInclude_refl {T I : Type u} (s : I → Set T)
    (A : Set T) (i : Selected s A) : supportCellInclude s (Set.Subset.refl A) i = i := rfl

/-- 包含の合成も同じセル名を保つ。 -/
@[simp] theorem supportCellInclude_comp {T I : Type u} (s : I → Set T) {A B C : Set T}
    (hab : A ⊆ B) (hbc : B ⊆ C) (i : Selected s A) :
    supportCellInclude s hbc (supportCellInclude s hab i) = supportCellInclude s (hab.trans hbc) i := rfl

/-- 同じ原支持cochain制限の値は、所有セル包含での評価である。 -/
theorem supportSelectedRestrict_apply {T I : Type u} (s : I → Set T) {A B : Set T}
    (hab : A ⊆ B) (z : Selected s B → ℚ) (i : Selected s A) :
    selectedRestrict s hab z i = z (supportCellInclude s hab i) := by
  rw [selectedRestrict_apply]
  rfl

variable (N : TargetSupportedNerve q) {A B : Set q.Target} (hab : A ⊆ B)

/-- 左右出現の端点計算は同じセル包含と可換。 -/
theorem supportCellInclude_endpoint (e : N.EdgeInTargetSubset A) (s : Bool) :
    supportCellInclude N.chartSupport hab (edgeEndpoint N A e s) =
      edgeEndpoint N B (supportCellInclude N.edgeSupport hab e) s := by
  cases s <;> apply Subtype.ext <;> rfl

/-- 全三辺の出現は台包含でもその位置を保つ。 -/
theorem supportCellInclude_faceEdge (f : N.FaceInTargetSubset A) (i : Fin 3) :
    supportCellInclude N.edgeSupport hab (faceEdge N A f i) =
      faceEdge N B (supportCellInclude N.faceSupport hab f) i := by
  fin_cases i <;> apply Subtype.ext <;> rfl

/-- 全三頂点の出現も台包含と可換。 -/
theorem supportCellInclude_faceVertex (f : N.FaceInTargetSubset A) (i : Fin 3) :
    supportCellInclude N.chartSupport hab (faceVertex N A f i) =
      faceVertex N B (supportCellInclude N.faceSupport hab f) i := by
  fin_cases i <;> apply Subtype.ext <;> rfl

/-- 三次数を保つ原incidence対象の包含。 -/
def supportIncObj : Inc N A → Inc N B
  | .chart c => .chart (supportCellInclude N.chartSupport hab c)
  | .edge e => .edge (supportCellInclude N.edgeSupport hab e)
  | .face f => .face (supportCellInclude N.faceSupport hab f)

/-- 全射の包含は同じ左右・辺・頂点出現の射。 -/
def supportIncMap {x y : Inc N A} : IncHom N A x y →
    IncHom N B (supportIncObj N hab x) (supportIncObj N hab y)
  | .id _ => .id _
  | .chartEdge c e s hc => .chartEdge _ _ s
      ((congrArg (supportCellInclude N.chartSupport hab) hc).trans
        (supportCellInclude_endpoint N hab e s))
  | .edgeFace e f i he => .edgeFace _ _ i
      ((congrArg (supportCellInclude N.edgeSupport hab) he).trans
        (supportCellInclude_faceEdge N hab f i))
  | .chartFace c f i hc => .chartFace _ _ i
      ((congrArg (supportCellInclude N.chartSupport hab) hc).trans
        (supportCellInclude_faceVertex N hab f i))

/-- 全原射の位置表示は包含で変わらない。 -/
theorem supportIncMap_code {x y : Inc N A} (f : IncHom N A x y) :
    incHomCode (supportIncMap N hab f) = incHomCode f := by
  cases f <;> rfl

/-- 台包含から生成する出現を保つincidence関手。 -/
def supportIncFunctor : Inc N A ⥤ Inc N B where
  obj := supportIncObj N hab
  map := supportIncMap N hab
  map_id _ := rfl
  map_comp f g := by
    apply incHomCode_injective
    rw [supportIncMap_code, incHomCode_comp, incHomCode_comp,
      supportIncMap_code, supportIncMap_code]

/-- 関手対象は同じ三次数セルの包含。 -/
@[simp] theorem supportIncFunctor_obj (x : Inc N A) :
    (supportIncFunctor N hab).obj x = supportIncObj N hab x := rfl

/-- chart対象は同じ支持chartの包含。 -/
@[simp] theorem supportIncFunctor_obj_chart (c : N.ChartInTargetSubset A) :
    (supportIncFunctor N hab).obj (.chart c) = .chart (supportCellInclude N.chartSupport hab c) := rfl

/-- 辺対象は同じ支持辺の包含。 -/
@[simp] theorem supportIncFunctor_obj_edge (e : N.EdgeInTargetSubset A) :
    (supportIncFunctor N hab).obj (.edge e) = .edge (supportCellInclude N.edgeSupport hab e) := rfl

/-- 面対象は同じ支持面の包含。 -/
@[simp] theorem supportIncFunctor_obj_face (f : N.FaceInTargetSubset A) :
    (supportIncFunctor N hab).obj (.face f) = .face (supportCellInclude N.faceSupport hab f) := rfl

/-- 左右端点射は同じ左右位置の実射に写る。 -/
theorem supportIncFunctor_map_chartEdge (c : N.ChartInTargetSubset A)
    (e : N.EdgeInTargetSubset A) (s : Bool) (hc : c = edgeEndpoint N A e s) :
    (supportIncFunctor N hab).map (IncHom.chartEdge c e s hc) =
      IncHom.chartEdge (supportCellInclude N.chartSupport hab c)
        (supportCellInclude N.edgeSupport hab e) s
        ((congrArg (supportCellInclude N.chartSupport hab) hc).trans
          (supportCellInclude_endpoint N hab e s)) := rfl

/-- 三辺射は全辺位置を保った実射。 -/
theorem supportIncFunctor_map_edgeFace (e : N.EdgeInTargetSubset A)
    (f : N.FaceInTargetSubset A) (i : Fin 3) (he : e = faceEdge N A f i) :
    (supportIncFunctor N hab).map (IncHom.edgeFace e f i he) =
      IncHom.edgeFace (supportCellInclude N.edgeSupport hab e)
        (supportCellInclude N.faceSupport hab f) i
        ((congrArg (supportCellInclude N.edgeSupport hab) he).trans
          (supportCellInclude_faceEdge N hab f i)) := rfl

/-- 三頂点射は全頂点位置を保った実射。 -/
theorem supportIncFunctor_map_chartFace (c : N.ChartInTargetSubset A)
    (f : N.FaceInTargetSubset A) (i : Fin 3) (hc : c = faceVertex N A f i) :
    (supportIncFunctor N hab).map (IncHom.chartFace c f i hc) =
      IncHom.chartFace (supportCellInclude N.chartSupport hab c)
        (supportCellInclude N.faceSupport hab f) i
        ((congrArg (supportCellInclude N.chartSupport hab) hc).trans
          (supportCellInclude_faceVertex N hab f i)) := rfl

/-- 関手の全射は元incidence射の位置を保つ。 -/
theorem supportIncFunctor_map_code {x y : Inc N A} (f : x ⟶ y) :
    incHomCode ((supportIncFunctor N hab).map f) = incHomCode f := supportIncMap_code N hab f

/-- 台包含の恒等則は全対象・全射の関手等号。 -/
theorem supportIncFunctor_refl (A : Set q.Target) :
    supportIncFunctor N (Set.Subset.refl A) = 𝟭 (Inc N A) := by
  fapply CategoryTheory.Functor.ext
  · intro x
    cases x <;> rfl
  · intro x y f
    cases f <;> try rfl
    cases x <;> rfl

/-- 台包含の合成則も、出現位置と輸送を含む全関手等号。 -/
theorem supportIncFunctor_comp {C : Set q.Target} (hbc : B ⊆ C) :
    supportIncFunctor N (hab.trans hbc) = supportIncFunctor N hab ⋙ supportIncFunctor N hbc := by
  fapply CategoryTheory.Functor.ext
  · intro x
    cases x <;> rfl
  · intro x y f
    cases f <;> try rfl
    cases x <;> rfl

/-- 原自由chain包含の基底は同じ支持セル包含。 -/
theorem supportChainInclude_single {T I : Type u} (s : I → Set T) {A B : Set T}
    (hab : A ⊆ B) (i : Selected s A) (r : ℚ) :
    selectedInclude s hab (Finsupp.single i r) = Finsupp.single (supportCellInclude s hab i) r := by
  rw [selectedInclude_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

/-- 元の細/粗第一chain微分は原支持包含と可換。 -/
theorem supportChainInclude_boundary1 :
    (selectedInclude N.chartSupport hab).comp (chainD1 N A) =
      (chainD1 N B).comp (selectedInclude N.edgeSupport hab) := by
  have hn := (TargetSupportedNerve.rawD1 N).selected_include_natural hab
  rw [TargetSupportedNerve.selected_rawD1, TargetSupportedNerve.selected_rawD1] at hn
  exact hn

/-- 元の第二chain微分も全三辺の重複を保持して可換。 -/
theorem supportChainInclude_boundary2 :
    (selectedInclude N.edgeSupport hab).comp (chainD2 N A) =
      (chainD2 N B).comp (selectedInclude N.faceSupport hab) := by
  have hn := (TargetSupportedNerve.rawD2 N).selected_include_natural hab
  rw [TargetSupportedNerve.selected_rawD2, TargetSupportedNerve.selected_rawD2] at hn
  exact hn

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportCellInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportCellInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportCellInclude_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportCellInclude_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportSelectedRestrict_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportCellInclude_endpoint
#print axioms AAT.AG.AtlasCoefficientFiber.supportCellInclude_faceEdge
#print axioms AAT.AG.AtlasCoefficientFiber.supportCellInclude_faceVertex
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncObj
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncMap
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncMap_code
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_obj
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_obj_chart
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_obj_edge
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_obj_face
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_map_chartEdge
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_map_edgeFace
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_map_chartFace
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_map_code
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportChainInclude_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportChainInclude_boundary1
#print axioms AAT.AG.AtlasCoefficientFiber.supportChainInclude_boundary2
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
