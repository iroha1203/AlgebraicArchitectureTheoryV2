import ResearchLean.AG.FaceRelationSubdivision.SubsetComparison
import Mathlib.CategoryTheory.Category.Basic
import Formal.Util.AssertStandardAxioms

/-!
# G-135 A：出現を保持する有限incidence圏

## Implementation notes

辺の左右と面の三辺を別の射として保持する。頂点から面への二経路は
三角形の頂点位置へ正規化する。セル包含の半順序はloopや重複辺の出現を
同一視するため用いない。対象・射は既存の支持subsetのセルから生成する。
-/

noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance CategoryTheory
universe u
variable {Source : Type u} {q : Reading Source}

/-- 選択辺の左・右の出現に対応する頂点。 -/
def edgeEndpoint (N : TargetSupportedNerve q) (A : Set q.Target)
    (e : N.EdgeInTargetSubset A) (s : Bool) : N.ChartInTargetSubset A :=
  if s then N.targetSubsetEdgeRight A e else N.targetSubsetEdgeLeft A e

/-- 選択面の三辺の出現。 -/
def faceEdge (N : TargetSupportedNerve q) (A : Set q.Target)
    (f : N.FaceInTargetSubset A) : Fin 3 → N.EdgeInTargetSubset A :=
  ![N.targetSubsetFaceEdge0 A f, N.targetSubsetFaceEdge1 A f, N.targetSubsetFaceEdge2 A f]

/-- 三角形の頂点位置。 -/
def faceVertex (N : TargetSupportedNerve q) (A : Set q.Target)
    (f : N.FaceInTargetSubset A) : Fin 3 → N.ChartInTargetSubset A :=
  ![N.targetSubsetEdgeLeft A (N.targetSubsetFaceEdge0 A f),
    N.targetSubsetEdgeRight A (N.targetSubsetFaceEdge0 A f),
    N.targetSubsetEdgeRight A (N.targetSubsetFaceEdge1 A f)]

/-- 辺出現と端点出現から三角形の頂点位置を計算する。 -/
def endpointPosition (i : Fin 3) (s : Bool) : Fin 3 :=
  if s then (if i = 0 then 1 else 2) else (if i = 2 then 1 else 0)

/-- 端点・面incidenceの二経路は原始三角形の同じ頂点へ至る。 -/
theorem edgeEndpoint_faceEdge (N : TargetSupportedNerve q) (A : Set q.Target)
    (f : N.FaceInTargetSubset A) (i : Fin 3) (s : Bool) :
    edgeEndpoint N A (faceEdge N A f i) s = faceVertex N A f (endpointPosition i s) := by
  fin_cases i <;> cases s <;>
    simp [edgeEndpoint, faceEdge, faceVertex, endpointPosition,
      N.targetSubset_left_faceEdge0_eq_left_faceEdge1,
      N.targetSubset_right_faceEdge0_eq_left_faceEdge2,
      N.targetSubset_right_faceEdge1_eq_right_faceEdge2]

/-- 支持subsetの名前付き三次数セル。 -/
inductive Inc (N : TargetSupportedNerve q) (A : Set q.Target) where
  | chart : N.ChartInTargetSubset A → Inc N A
  | edge : N.EdgeInTargetSubset A → Inc N A
  | face : N.FaceInTargetSubset A → Inc N A

/-- 恒等射と、端点・辺・頂点位置のincidence。位置は重複セルでも保持する。 -/
inductive IncHom (N : TargetSupportedNerve q) (A : Set q.Target) : Inc N A → Inc N A → Type u where
  | id (x) : IncHom N A x x
  | chartEdge (c e) (s : Bool) (h : c = edgeEndpoint N A e s) :
      IncHom N A (.chart c) (.edge e)
  | edgeFace (e f) (i : Fin 3) (h : e = faceEdge N A f i) :
      IncHom N A (.edge e) (.face f)
  | chartFace (c f) (i : Fin 3) (h : c = faceVertex N A f i) :
      IncHom N A (.chart c) (.face f)

/-- incidence射の合成。非恒等射の合成は三角形の頂点位置へ正規化する。 -/
def incComp {N : TargetSupportedNerve q} {A : Set q.Target} {x y z : Inc N A} :
    IncHom N A x y → IncHom N A y z → IncHom N A x z
  | .id _, g => g
  | f, .id _ => f
  | .chartEdge c e s h, .edgeFace _ f i he =>
      .chartFace c f (endpointPosition i s) (h.trans (by rw [he, edgeEndpoint_faceEdge]))

/-- 原始incidenceの正規化は結合的である。 -/
theorem incComp_assoc {N : TargetSupportedNerve q} {A : Set q.Target}
    {w x y z : Inc N A} (f : IncHom N A w x) (g : IncHom N A x y)
    (h : IncHom N A y z) : incComp (incComp f g) h = incComp f (incComp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

/-- 支持セルのincidenceはmathlibの圏である。 -/
instance incCategory (N : TargetSupportedNerve q) (A : Set q.Target) : Category (Inc N A) where
  Hom := IncHom N A
  id := IncHom.id
  comp := incComp
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc := incComp_assoc

/-- incidence生成射への値と、三角形の二経路の関係。関手構成のAPI。 -/
structure IncidenceFunctorData (N : TargetSupportedNerve q) (A : Set q.Target)
    (D : Type u) [Category D] where
  chartObj : N.ChartInTargetSubset A → D
  edgeObj : N.EdgeInTargetSubset A → D
  faceObj : N.FaceInTargetSubset A → D
  endpointHom : ∀ e s, chartObj (edgeEndpoint N A e s) ⟶ edgeObj e
  edgeHom : ∀ f i, edgeObj (faceEdge N A f i) ⟶ faceObj f
  triangle_zero : ∀ f,
    endpointHom (faceEdge N A f 0) false ≫ edgeHom f 0 =
      eqToHom (congrArg chartObj (N.targetSubset_left_faceEdge0_eq_left_faceEdge1 A f)) ≫
        endpointHom (faceEdge N A f 1) false ≫ edgeHom f 1
  triangle_one : ∀ f,
    endpointHom (faceEdge N A f 0) true ≫ edgeHom f 0 =
      eqToHom (congrArg chartObj (N.targetSubset_right_faceEdge0_eq_left_faceEdge2 A f)) ≫
        endpointHom (faceEdge N A f 2) false ≫ edgeHom f 2
  triangle_two : ∀ f,
    endpointHom (faceEdge N A f 1) true ≫ edgeHom f 1 =
      eqToHom (congrArg chartObj (N.targetSubset_right_faceEdge1_eq_right_faceEdge2 A f)) ≫
        endpointHom (faceEdge N A f 2) true ≫ edgeHom f 2

namespace IncidenceFunctorData
variable {N : TargetSupportedNerve q} {A : Set q.Target} {D : Type u} [Category D]

/-- 三つの頂点位置の関手値。二経路の片側を用いた正規形。 -/
def vertexHom (T : IncidenceFunctorData N A D) (f : N.FaceInTargetSubset A) :
    ∀ i, T.chartObj (faceVertex N A f i) ⟶ T.faceObj f
  | 0 => T.endpointHom (faceEdge N A f 0) false ≫ T.edgeHom f 0
  | 1 => T.endpointHom (faceEdge N A f 0) true ≫ T.edgeHom f 0
  | 2 => T.endpointHom (faceEdge N A f 1) true ≫ T.edgeHom f 1

/-- 任意の端点出現からの合成は、三角形関係により同じ頂点の値になる。 -/
theorem endpoint_edge (T : IncidenceFunctorData N A D) (f : N.FaceInTargetSubset A)
    (i : Fin 3) (s : Bool) :
    T.endpointHom (faceEdge N A f i) s ≫ T.edgeHom f i =
      eqToHom (congrArg T.chartObj (edgeEndpoint_faceEdge N A f i s)) ≫
        T.vertexHom f (endpointPosition i s) := by
  fin_cases i <;> cases s
  · simp [vertexHom, endpointPosition, faceVertex, faceEdge, edgeEndpoint]
  · simp [vertexHom, endpointPosition, faceVertex, faceEdge, edgeEndpoint]
  · simpa [vertexHom, endpointPosition, faceVertex, faceEdge, edgeEndpoint] using
      (eqToHom_comp_iff _ _ _).mp (T.triangle_zero f).symm
  · simp [vertexHom, endpointPosition, faceVertex, faceEdge, edgeEndpoint]
  · simpa [vertexHom, endpointPosition, faceVertex, faceEdge, edgeEndpoint] using
      (eqToHom_comp_iff _ _ _).mp (T.triangle_one f).symm
  · simpa [vertexHom, endpointPosition, faceVertex, faceEdge, edgeEndpoint] using
      (eqToHom_comp_iff _ _ _).mp (T.triangle_two f).symm

/-- incidence dataの対象値。 -/
def obj (T : IncidenceFunctorData N A D) : Inc N A → D
  | .chart c => T.chartObj c
  | .edge e => T.edgeObj e
  | .face f => T.faceObj f

/-- 全incidence射の値。位置の正規化と等号による輸送を含む。 -/
def map (T : IncidenceFunctorData N A D) {x y : Inc N A} :
    IncHom N A x y → (T.obj x ⟶ T.obj y)
  | .id _ => 𝟙 _
  | .chartEdge _ e s h => eqToHom (congrArg T.chartObj h) ≫ T.endpointHom e s
  | .edgeFace _ f i h => eqToHom (congrArg T.edgeObj h) ≫ T.edgeHom f i
  | .chartFace _ f i h => eqToHom (congrArg T.chartObj h) ≫ T.vertexHom f i

/-- 生成射と三角形関係から、全incidence圏の関手を構成する。 -/
def functor (T : IncidenceFunctorData N A D) : Inc N A ⥤ D where
  obj := T.obj
  map := T.map
  map_id x := rfl
  map_comp f g := by
    change T.map (incComp f g) = T.map f ≫ T.map g
    cases f <;> cases g <;> simp only [incComp, map, Category.id_comp, Category.comp_id]
    rename_i c e s hc f i he
    subst e
    subst c
    simp only [eqToHom_refl, Category.id_comp]
    exact (T.endpoint_edge f i s).symm
end IncidenceFunctorData

/-- incidence対象の有限表示。同じ型のセルを次数で区別する。 -/
def incCode (N : TargetSupportedNerve q) (A : Set q.Target) :
    Inc N A → N.ChartInTargetSubset A ⊕ N.EdgeInTargetSubset A ⊕ N.FaceInTargetSubset A
  | .chart c => .inl c
  | .edge e => .inr (.inl e)
  | .face f => .inr (.inr f)

/-- 対象の表示はセル名を失わない。 -/
theorem incCode_injective (N : TargetSupportedNerve q) (A : Set q.Target) :
    Function.Injective (incCode N A) := by
  intro x y h
  cases x <;> cases y <;> simp [incCode] at h <;> cases h <;> rfl

/-- incidence対象の有限性は支持セルの有限性から導く。 -/
instance incFinite (N : TargetSupportedNerve q) (A : Set q.Target) : Finite (Inc N A) :=
  Finite.of_injective (incCode N A) (incCode_injective N A)

/-- 射の有限表示。端点・三辺・三頂点の位置を別々に保つ。 -/
def incHomCode {N : TargetSupportedNerve q} {A : Set q.Target} {x y : Inc N A} :
    IncHom N A x y → Unit ⊕ Bool ⊕ Fin 3 ⊕ Fin 3
  | .id _ => .inl ()
  | .chartEdge _ _ s _ => .inr (.inl s)
  | .edgeFace _ _ i _ => .inr (.inr (.inl i))
  | .chartFace _ _ i _ => .inr (.inr (.inr i))

/-- 射の表示は、セル名を固定した全incidence出現を反映する。 -/
theorem incHomCode_injective {N : TargetSupportedNerve q} {A : Set q.Target}
    {x y : Inc N A} : Function.Injective (@incHomCode _ _ N A x y) := by
  intro f g h
  cases f <;> cases g <;> simp [incHomCode] at h <;> cases h <;> rfl

/-- incidence射の有限性を位置表示から導く。 -/
instance incHomFinite {N : TargetSupportedNerve q} {A : Set q.Target} (x y : Inc N A) :
    Finite (x ⟶ y) := Finite.of_injective incHomCode incHomCode_injective

/-- 左辺端点から面へ至る二経路の同定。 -/
theorem face_vertex_zero_relation (N : TargetSupportedNerve q) (A : Set q.Target)
    (f : N.FaceInTargetSubset A) :
    incComp (.chartEdge _ _ false rfl) (.edgeFace _ f 0 rfl) =
      incComp (.chartEdge _ _ false
        (N.targetSubset_left_faceEdge0_eq_left_faceEdge1 A f)) (.edgeFace _ f 1 rfl) := rfl

/-- 第一辺右端点と第三辺左端点から面へ至る二経路の同定。 -/
theorem face_vertex_one_relation (N : TargetSupportedNerve q) (A : Set q.Target)
    (f : N.FaceInTargetSubset A) :
    incComp (.chartEdge _ _ true rfl) (.edgeFace _ f 0 rfl) =
      incComp (.chartEdge _ _ false
        (N.targetSubset_right_faceEdge0_eq_left_faceEdge2 A f)) (.edgeFace _ f 2 rfl) := rfl

/-- 第二辺と第三辺の右端点から面へ至る二経路の同定。 -/
theorem face_vertex_two_relation (N : TargetSupportedNerve q) (A : Set q.Target)
    (f : N.FaceInTargetSubset A) :
    incComp (.chartEdge _ _ true rfl) (.edgeFace _ f 1 rfl) =
      incComp (.chartEdge _ _ true
        (N.targetSubset_right_faceEdge1_eq_right_faceEdge2 A f)) (.edgeFace _ f 2 rfl) := rfl

/-- loopの左・右incidenceは同じセル名でも異なる射である。 -/
theorem chartEdge_left_ne_right {N : TargetSupportedNerve q} {A : Set q.Target}
    (c : N.ChartInTargetSubset A) (e : N.EdgeInTargetSubset A)
    (hl : c = edgeEndpoint N A e false) (hr : c = edgeEndpoint N A e true) :
    IncHom.chartEdge c e false hl ≠ IncHom.chartEdge c e true hr := by
  intro h
  cases h

/-- 面で同じ辺が現れても、異なる辺位置のincidenceは異なる射である。 -/
theorem edgeFace_ne_of_position_ne {N : TargetSupportedNerve q} {A : Set q.Target}
    (e : N.EdgeInTargetSubset A) (f : N.FaceInTargetSubset A) (i j : Fin 3)
    (hi : e = faceEdge N A f i) (hj : e = faceEdge N A f j) (hij : i ≠ j) :
    IncHom.edgeFace e f i hi ≠ IncHom.edgeFace e f j hj := by
  intro h
  cases h
  exact hij rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.edgeEndpoint
#print axioms AAT.AG.AtlasCoefficientFiber.faceEdge
#print axioms AAT.AG.AtlasCoefficientFiber.faceVertex
#print axioms AAT.AG.AtlasCoefficientFiber.endpointPosition
#print axioms AAT.AG.AtlasCoefficientFiber.edgeEndpoint_faceEdge
#print axioms AAT.AG.AtlasCoefficientFiber.Inc
#print axioms AAT.AG.AtlasCoefficientFiber.IncHom
#print axioms AAT.AG.AtlasCoefficientFiber.incComp
#print axioms AAT.AG.AtlasCoefficientFiber.incComp_assoc
#print axioms AAT.AG.AtlasCoefficientFiber.incCategory
#print axioms AAT.AG.AtlasCoefficientFiber.IncidenceFunctorData
#print axioms AAT.AG.AtlasCoefficientFiber.IncidenceFunctorData.vertexHom
#print axioms AAT.AG.AtlasCoefficientFiber.IncidenceFunctorData.endpoint_edge
#print axioms AAT.AG.AtlasCoefficientFiber.IncidenceFunctorData.obj
#print axioms AAT.AG.AtlasCoefficientFiber.IncidenceFunctorData.map
#print axioms AAT.AG.AtlasCoefficientFiber.IncidenceFunctorData.functor
#print axioms AAT.AG.AtlasCoefficientFiber.incCode
#print axioms AAT.AG.AtlasCoefficientFiber.incCode_injective
#print axioms AAT.AG.AtlasCoefficientFiber.incFinite
#print axioms AAT.AG.AtlasCoefficientFiber.incHomCode
#print axioms AAT.AG.AtlasCoefficientFiber.incHomCode_injective
#print axioms AAT.AG.AtlasCoefficientFiber.incHomFinite
#print axioms AAT.AG.AtlasCoefficientFiber.face_vertex_zero_relation
#print axioms AAT.AG.AtlasCoefficientFiber.face_vertex_one_relation
#print axioms AAT.AG.AtlasCoefficientFiber.face_vertex_two_relation
#print axioms AAT.AG.AtlasCoefficientFiber.chartEdge_left_ne_right
#print axioms AAT.AG.AtlasCoefficientFiber.edgeFace_ne_of_position_ne
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
