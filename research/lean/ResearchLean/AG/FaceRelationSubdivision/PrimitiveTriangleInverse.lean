import ResearchLean.AG.FaceRelationSubdivision.PrimitiveCellDeletion
import ResearchLean.AG.FaceRelationSubdivision.TriangleContraction
import ResearchLean.AG.FaceRelationSubdivision.EdgeSubdivision
import Formal.Util.AssertStandardAxioms

/-!
# 全接続を検査する三角形逆縮約

## Implementation notes

入力は元nerveの局所セル名、端点・三辺・台等号と、削除名への全接続条件だけ。
旧nerveや既成表示同型をfieldへ入れる案を避け、保持セルの部分型から旧入力を作る。
新しい辺が既存面に入っていないことは、全位置を量化する条件から導出する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution Cohomology ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}

/-- 設計§4の三角形逆操作を原始セル表から認識する条件。 -/
structure TriangleInversePattern (N : TargetSupportedNerve q) where
  vertex : N.nerve.Chart
  baseEdge : N.nerve.EdgeComponent
  connector : N.nerve.EdgeComponent
  second : N.nerve.EdgeComponent
  face : N.nerve.FaceComponent
  base_ne_connector : baseEdge ≠ connector
  base_ne_second : baseEdge ≠ second
  connector_ne_second : connector ≠ second
  connector_left : N.nerve.edgeLeft connector = N.nerve.edgeLeft baseEdge
  connector_right : N.nerve.edgeRight connector = vertex
  second_left : N.nerve.edgeLeft second = vertex
  second_right : N.nerve.edgeRight second = N.nerve.edgeRight baseEdge
  face0 : N.nerve.faceEdge0 face = connector
  face1 : N.nerve.faceEdge1 face = baseEdge
  face2 : N.nerve.faceEdge2 face = second
  vertex_support : N.chartSupport vertex = N.chartSupport (N.nerve.edgeLeft baseEdge)
  vertex_connections : ∀ a, N.nerve.edgeLeft a = vertex ∨ N.nerve.edgeRight a = vertex →
    a = connector ∨ a = second
  face_connections : ∀ F i, EdgeSubdivision.faceSlot N F i = connector ∨
    EdgeSubdivision.faceSlot N F i = second → F = face

namespace TriangleInversePattern
variable {N : TargetSupportedNerve.{u, u} q} (P : TriangleInversePattern N)

/-- 削除頂点以外の全chart名。 -/
abbrev OldChart := {v : N.nerve.Chart // v ≠ P.vertex}
/-- 指定二辺以外の全edge名。 -/
abbrev OldEdge := {a : N.nerve.EdgeComponent // a ≠ P.connector ∧ a ≠ P.second}
/-- 指定追加面以外の全face名。 -/
abbrev OldFace := {F : N.nerve.FaceComponent // F ≠ P.face}

/-- 全接続条件から、保持辺の左端点は削除頂点ではない。 -/
theorem retained_left (a : P.OldEdge) : N.nerve.edgeLeft a.1 ≠ P.vertex := by
  intro h
  rcases P.vertex_connections a.1 (Or.inl h) with hc | hs
  · exact a.2.1 hc
  · exact a.2.2 hs
/-- 全接続条件から、保持辺の右端点も削除頂点ではない。 -/
theorem retained_right (a : P.OldEdge) : N.nerve.edgeRight a.1 ≠ P.vertex := by
  intro h
  rcases P.vertex_connections a.1 (Or.inr h) with hc | hs
  · exact a.2.1 hc
  · exact a.2.2 hs
/-- 保持面の全三位置に削除辺が現れない。 -/
theorem retained_slot (F : P.OldFace) (i : Fin 3) :
    EdgeSubdivision.faceSlot N F.1 i ≠ P.connector ∧
      EdgeSubdivision.faceSlot N F.1 i ≠ P.second := by
  constructor
  · intro h; exact F.2 (P.face_connections F.1 i (Or.inl h))
  · intro h; exact F.2 (P.face_connections F.1 i (Or.inr h))

/-- 旧辺の左端点を全接続条件から構成する。 -/
def oldLeft (a : P.OldEdge) : P.OldChart := ⟨N.nerve.edgeLeft a.1, P.retained_left a⟩
/-- 旧辺の右端点を全接続条件から構成する。 -/
def oldRight (a : P.OldEdge) : P.OldChart := ⟨N.nerve.edgeRight a.1, P.retained_right a⟩
/-- 保持面の各位置を同じ名前の保持辺へ制限する。 -/
def oldSlot (F : P.OldFace) (i : Fin 3) : P.OldEdge :=
  ⟨EdgeSubdivision.faceSlot N F.1 i, P.retained_slot F i⟩

/-- 削除セルへの全接続検査から復元する旧nerve。 -/
def restoredNerve : CoverNerve.{u} where
  Chart := P.OldChart
  EdgeComponent := P.OldEdge
  FaceComponent := P.OldFace
  edgeLeft := P.oldLeft
  edgeRight := P.oldRight
  faceEdge0 := fun F => P.oldSlot F 0
  faceEdge1 := fun F => P.oldSlot F 1
  faceEdge2 := fun F => P.oldSlot F 2
  edgeOverlapComponent := fun a => N.nerve.edgeOverlapComponent a.1
  faceTripleOverlapComponent := fun F => N.nerve.faceTripleOverlapComponent F.1
  edgeOverlapComponent_holds := fun a => N.nerve.edgeOverlapComponent_holds a.1
  faceTripleOverlapComponent_holds := fun F => N.nerve.faceTripleOverlapComponent_holds F.1

/-- 保持chart台を変えずに復元する有限supported nerve。 -/
def restored : TargetSupportedNerve q := by
  classical
  exact {
    nerve := P.restoredNerve
    chartFintype := by change Fintype P.OldChart; infer_instance
    edgeFintype := by change Fintype P.OldEdge; infer_instance
    faceFintype := by change Fintype P.OldFace; infer_instance
    chartSupport := fun v => N.chartSupport v.1
    chartSupport_nonempty := fun v => N.chartSupport_nonempty v.1
    faceEdge0_left := by intro F; apply Subtype.ext; exact N.faceEdge0_left F.1
    faceEdge0_right := by intro F; apply Subtype.ext; exact N.faceEdge0_right F.1
    faceEdge1_right := by intro F; apply Subtype.ext; exact N.faceEdge1_right F.1 }

/-- 復元する元の辺はfresh二辺とは異なり保持される。 -/
def restoredBase : P.restored.nerve.EdgeComponent :=
  ⟨P.baseEdge, P.base_ne_connector, P.base_ne_second⟩
/-- 指定元辺と全接続条件は削除頂点の始点freshnessも強制する。 -/
theorem vertex_ne_left : P.vertex ≠ N.nerve.edgeLeft P.baseEdge :=
  Ne.symm (P.retained_left P.restoredBase)
/-- 同じ条件から終点freshnessを導く。loopの始終点の一致は許す。 -/
theorem vertex_ne_right : P.vertex ≠ N.nerve.edgeRight P.baseEdge :=
  Ne.symm (P.retained_right P.restoredBase)
/-- 復元chart台は同じ原始chart台。 -/
@[simp] theorem restored_chartSupport (v : P.OldChart) :
    P.restored.chartSupport v = N.chartSupport v.1 := rfl
/-- 復元旧辺のK1台は保持される。 -/
@[simp] theorem restored_edgeSupport (a : P.OldEdge) :
    P.restored.edgeSupport a = N.edgeSupport a.1 := rfl
/-- 復元旧面のK1台は保持される。 -/
@[simp] theorem restored_faceSupport (F : P.OldFace) :
    P.restored.faceSupport F = N.faceSupport F.1 := rfl

/-- 復元旧入力の三角形追加を元の全セル名・incidence・台へ戻す原始表示同型。 -/
def presentation : CellPresentationEquiv q q (Reading.coarserThan_refl q) N
    (TriangleAddition.supported P.restored P.restoredBase) where
  chartEquiv := deleteOneEquiv P.vertex
  edgeEquiv := deleteTwoEquiv P.connector P.second P.connector_ne_second
  faceEquiv := deleteOneEquiv P.face
  edge_left := by
    rintro (a | b)
    · rfl
    · cases b
      · exact P.connector_left.symm
      · exact P.second_left.symm
  edge_right := by
    rintro (a | b)
    · rfl
    · cases b
      · exact P.connector_right.symm
      · exact P.second_right.symm
  face_edge0 := by
    rintro (F | x)
    · rfl
    · exact P.face0.symm
  face_edge1 := by
    rintro (F | x)
    · rfl
    · exact P.face1.symm
  face_edge2 := by
    rintro (F | x)
    · rfl
    · exact P.face2.symm
  chartSupport_eq := by
    rintro (v | x)
    · ext t
      change t ∈ N.chartSupport v.1 ↔ comparisonFactor q q (Reading.coarserThan_refl q) t ∈ N.chartSupport v.1
      rw [TriangleAddition.self_factor]
    · ext t
      change t ∈ N.chartSupport (N.nerve.edgeLeft P.baseEdge) ↔
        comparisonFactor q q (Reading.coarserThan_refl q) t ∈ N.chartSupport P.vertex
      rw [TriangleAddition.self_factor, P.vertex_support]

/-- 復元表示で旧辺名を保持する。 -/
@[simp] theorem presentation_old_edge (a : P.OldEdge) :
    P.presentation.edgeEquiv (.inl a) = a.1 := rfl
/-- 指定connectorの原始名への復元。 -/
@[simp] theorem presentation_connector : P.presentation.edgeEquiv (.inr false) = P.connector := rfl
/-- 指定secondの原始名への復元。 -/
@[simp] theorem presentation_second : P.presentation.edgeEquiv (.inr true) = P.second := rfl
/-- 指定面の原始名への復元。 -/
@[simp] theorem presentation_face : P.presentation.faceEquiv (.inr PUnit.unit) = P.face := rfl

/-- 正の三角形追加の出力には全接続条件を含む原始逆patternがある。 -/
def ofAddition (M : TargetSupportedNerve q) (e : M.nerve.EdgeComponent) :
    TriangleInversePattern (TriangleAddition.supported M e) where
  vertex := .inr PUnit.unit
  baseEdge := .inl e
  connector := .inr false
  second := .inr true
  face := .inr PUnit.unit
  base_ne_connector := by simp
  base_ne_second := by simp
  connector_ne_second := by intro h; cases Sum.inr.inj h
  connector_left := rfl
  connector_right := rfl
  second_left := rfl
  second_right := rfl
  face0 := rfl
  face1 := rfl
  face2 := rfl
  vertex_support := rfl
  vertex_connections := by
    rintro (a | b) h
    · cases h with
      | inl h => cases h
      | inr h => cases h
    · cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
  face_connections := by
    rintro (F | x) i h
    · rcases h with hc | hs
      · have : ∃ a, EdgeSubdivision.faceSlot (TriangleAddition.supported M e) (.inl F) i = .inl a := by
          fin_cases i <;> exact ⟨_, rfl⟩
        obtain ⟨a, ha⟩ := this
        rw [ha] at hc; cases hc
      · have : ∃ a, EdgeSubdivision.faceSlot (TriangleAddition.supported M e) (.inl F) i = .inl a := by
          fin_cases i <;> exact ⟨_, rfl⟩
        obtain ⟨a, ha⟩ := this
        rw [ha] at hs; cases hs
    · cases x; rfl

/-- 第三の辺が指定fresh頂点へ接続する原始dataは、同じ局所セル指定の逆patternを持たない。 -/
theorem no_pattern_with_extra_edge (vp : N.nerve.Chart) (c s a : N.nerve.EdgeComponent)
    (ha : N.nerve.edgeLeft a = vp ∨ N.nerve.edgeRight a = vp) (hac : a ≠ c) (has : a ≠ s) :
    ¬ ∃ P : TriangleInversePattern N, P.vertex = vp ∧ P.connector = c ∧ P.second = s := by
  rintro ⟨P, hv, hc, hs⟩
  rcases P.vertex_connections a (by simpa [hv] using ha) with h | h
  · exact hac (h.trans hc)
  · exact has (h.trans hs)

/-- 最初のconnectorへさらに三角形を加えると、最初のfresh頂点への第三辺が生じ、
最初の局所名を指定した逆縮約は全接続検査で拒否される。 -/
theorem double_addition_rejects_first_pattern (M : TargetSupportedNerve q)
    (e : M.nerve.EdgeComponent) :
    ¬ ∃ P : TriangleInversePattern
      (TriangleAddition.supported (TriangleAddition.supported M e) (.inr false)),
      P.vertex = .inl (.inr PUnit.unit) ∧ P.connector = .inl (.inr false) ∧
        P.second = .inl (.inr true) :=
  no_pattern_with_extra_edge _ _ _ (.inr true) (Or.inr rfl) (by simp) (by simp)

end TriangleInversePattern
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
