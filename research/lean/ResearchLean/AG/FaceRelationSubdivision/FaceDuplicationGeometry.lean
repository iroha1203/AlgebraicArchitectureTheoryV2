import ResearchLean.AG.FaceRelationSubdivision.TriangleGeometry
import ResearchLean.AG.AtlasDefectComposition.ComparisonLaws
import Formal.Util.AssertStandardAxioms

/-!
# 原始面の複製

G-134 Eの任意の面を、同じ三辺・K1台を持つfresh面として追加する。

## Implementation notes

面の直和タグでfreshnessを保証し、chartとedgeの型・台を保つ。
比較と旧面へのsectionを原始incidenceから生成する。三項の相同型は入力に置かない。
面座標の期待次元を指定する行列表は採らず、任意supported nerveの面を使う。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution Cohomology ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}

namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent)

/-- 面のfold。fresh面を指定した旧面へ送る。 -/
def fold : N.nerve.FaceComponent ⊕ PUnit.{u+1} → N.nerve.FaceComponent :=
  Sum.elim id (fun _ => F)

/-- 頂点と辺を保ち、指定面と同じincidenceの別名面を加える。 -/
def nerve : CoverNerve.{u} where
  Chart := N.nerve.Chart
  EdgeComponent := N.nerve.EdgeComponent
  FaceComponent := N.nerve.FaceComponent ⊕ PUnit.{u+1}
  edgeLeft := N.nerve.edgeLeft
  edgeRight := N.nerve.edgeRight
  faceEdge0 := N.nerve.faceEdge0 ∘ fold N F
  faceEdge1 := N.nerve.faceEdge1 ∘ fold N F
  faceEdge2 := N.nerve.faceEdge2 ∘ fold N F
  edgeOverlapComponent := N.nerve.edgeOverlapComponent
  faceTripleOverlapComponent := N.nerve.faceTripleOverlapComponent ∘ fold N F
  edgeOverlapComponent_holds := N.nerve.edgeOverlapComponent_holds
  faceTripleOverlapComponent_holds := fun _ => N.nerve.faceTripleOverlapComponent_holds _

/-- 原始chart台を保ち、複製面の台をK1から生成する。 -/
def supported : TargetSupportedNerve q where
  nerve := nerve N F
  chartFintype := N.chartFintype
  edgeFintype := N.edgeFintype
  faceFintype := by change Fintype (N.nerve.FaceComponent ⊕ PUnit.{u+1}); infer_instance
  chartSupport := N.chartSupport
  chartSupport_nonempty := N.chartSupport_nonempty
  faceEdge0_left := fun f => N.faceEdge0_left (fold N F f)
  faceEdge0_right := fun f => N.faceEdge0_right (fold N F f)
  faceEdge1_right := fun f => N.faceEdge1_right (fold N F f)

/-- chart台は元の台そのもの。 -/
@[simp] theorem chartSupport_eq (v : N.nerve.Chart) :
    (supported N F).chartSupport v = N.chartSupport v := rfl
/-- K1辺台は元の台そのもの。 -/
@[simp] theorem edgeSupport_eq (e : N.nerve.EdgeComponent) :
    (supported N F).edgeSupport e = N.edgeSupport e := rfl
/-- 元の辺の始点をそのまま保つ。 -/
@[simp] theorem edgeLeft_eq (e : N.nerve.EdgeComponent) :
    (supported N F).nerve.edgeLeft e = N.nerve.edgeLeft e := rfl
/-- 元の辺の終点をそのまま保つ。 -/
@[simp] theorem edgeRight_eq (e : N.nerve.EdgeComponent) :
    (supported N F).nerve.edgeRight e = N.nerve.edgeRight e := rfl
/-- 各面のK1台はfoldで読んだ旧面の台。 -/
@[simp] theorem faceSupport_fold (f : (supported N F).nerve.FaceComponent) :
    (supported N F).faceSupport f = N.faceSupport (fold N F f) := rfl
/-- 旧面の支持は保持される。 -/
@[simp] theorem faceSupport_old (f : N.nerve.FaceComponent) :
    (supported N F).faceSupport (.inl f) = N.faceSupport f := rfl
/-- fresh面の支持は指定面と等しい。 -/
@[simp] theorem faceSupport_new :
    (supported N F).faceSupport (.inr PUnit.unit) = N.faceSupport F := rfl

/-- 原始表からの旧hereditary比較。複製面のfoldと旧セル恒等を持つ。 -/
def collapse : TargetSupportedNerveMorphism q q (Reading.coarserThan_refl q) N (supported N F) where
  chartMap := id
  edgeMap := some
  faceMap := some ∘ fold N F
  edge_some_left := by intro e a h; cases Option.some.inj h; rfl
  edge_some_right := by intro e a h; cases Option.some.inj h; rfl
  edge_none_fiber := by intro e h; cases h
  face_some_edge0 := by intro f a h; cases Option.some.inj h; rfl
  face_some_edge1 := by intro f a h; cases Option.some.inj h; rfl
  face_some_edge2 := by intro f a h; cases Option.some.inj h; rfl
  face_none_edge0 := by intro f h; cases h
  face_none_edge1 := by intro f h; cases h
  face_none_edge2 := by intro f h; cases h
  chartSupport_compatible := by intro v t ht; rw [TriangleAddition.self_factor]; exact ht

/-- 旧面を保持する原始section。頂点・辺は同じ恒等である。 -/
def sectionMap : TargetSupportedNerveMorphism q q (Reading.coarserThan_refl q) (supported N F) N where
  chartMap := id
  edgeMap := some
  faceMap := fun f => some (.inl f)
  edge_some_left := by intro e a h; cases Option.some.inj h; rfl
  edge_some_right := by intro e a h; cases Option.some.inj h; rfl
  edge_none_fiber := by intro e h; cases h
  face_some_edge0 := by intro f a h; cases Option.some.inj h; rfl
  face_some_edge1 := by intro f a h; cases Option.some.inj h; rfl
  face_some_edge2 := by intro f a h; cases Option.some.inj h; rfl
  face_none_edge0 := by intro f h; cases h
  face_none_edge1 := by intro f h; cases h
  face_none_edge2 := by intro f h; cases h
  chartSupport_compatible := by intro v t ht; rw [TriangleAddition.self_factor]; exact ht

/-- foldの旧面評価。 -/
@[simp] theorem fold_old (f : N.nerve.FaceComponent) : fold N F (.inl f) = f := rfl
/-- foldのfresh面評価。 -/
@[simp] theorem fold_new : fold N F (.inr PUnit.unit) = F := rfl
/-- 複製面の第0辺はfold先の同じ原始辺。 -/
@[simp] theorem faceEdge0_fold (f : (supported N F).nerve.FaceComponent) :
    (supported N F).nerve.faceEdge0 f = N.nerve.faceEdge0 (fold N F f) := rfl
/-- 複製面の第1辺はfold先の同じ原始辺。 -/
@[simp] theorem faceEdge1_fold (f : (supported N F).nerve.FaceComponent) :
    (supported N F).nerve.faceEdge1 f = N.nerve.faceEdge1 (fold N F f) := rfl
/-- 複製面の第2辺はfold先の同じ原始辺。 -/
@[simp] theorem faceEdge2_fold (f : (supported N F).nerve.FaceComponent) :
    (supported N F).nerve.faceEdge2 f = N.nerve.faceEdge2 (fold N F f) := rfl
/-- 原始比較のchart評価。 -/
@[simp] theorem collapse_chart (v : N.nerve.Chart) : (collapse N F).chartMap v = v := rfl
/-- 原始比較のedge評価。 -/
@[simp] theorem collapse_edge (e : N.nerve.EdgeComponent) : (collapse N F).edgeMap e = some e := rfl
/-- 原始比較のface評価。 -/
@[simp] theorem collapse_face (f : (supported N F).nerve.FaceComponent) :
    (collapse N F).faceMap f = some (fold N F f) := rfl
/-- 原始sectionのchart評価。 -/
@[simp] theorem section_chart (v : N.nerve.Chart) : (sectionMap N F).chartMap v = v := rfl
/-- 原始sectionのedge評価。 -/
@[simp] theorem section_edge (e : N.nerve.EdgeComponent) : (sectionMap N F).edgeMap e = some e := rfl
/-- 原始sectionのface評価。 -/
@[simp] theorem section_face (f : N.nerve.FaceComponent) :
    (sectionMap N F).faceMap f = some (.inl f) := rfl

end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
