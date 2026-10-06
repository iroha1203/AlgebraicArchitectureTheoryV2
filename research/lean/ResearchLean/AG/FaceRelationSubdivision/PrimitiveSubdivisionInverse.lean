import ResearchLean.AG.FaceRelationSubdivision.PrimitiveCellDeletion
import ResearchLean.AG.FaceRelationSubdivision.EdgeContraction
import Formal.Util.AssertStandardAxioms

/-!
# 出現位置と全接続から辺分割を逆縮約する原始条件

## Implementation notes

原始の対角辺名と追加面名、中心面の指定位置を使い、対角辺の全出現をiffで検査する。
出現型の有限性は原始対角辺の単射と既存有限辺名から導出する。面ごと・辺名ごとに
位置をまとめる案は三重出現の符号を失うため採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution Cohomology ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}

/-- 設計§4の辺分割逆操作の全接続検査。収縮や旧入力は入力に含めない。 -/
structure SubdivisionInversePattern (N : TargetSupportedNerve.{u, u} q) where
  vertex : N.nerve.Chart
  left : N.nerve.Chart
  right : N.nerve.Chart
  connector : N.nerve.EdgeComponent
  second : N.nerve.EdgeComponent
  Occurrence : Type u
  diagonal : Occurrence → N.nerve.EdgeComponent
  triangle : Occurrence → N.nerve.FaceComponent
  position : Occurrence → N.nerve.FaceComponent × Fin 3
  left_ne_vertex : left ≠ vertex
  right_ne_vertex : right ≠ vertex
  connector_ne_second : connector ≠ second
  connector_ne_diagonal : ∀ o, connector ≠ diagonal o
  second_ne_diagonal : ∀ o, second ≠ diagonal o
  diagonal_injective : Function.Injective diagonal
  connector_left : N.nerve.edgeLeft connector = left
  connector_right : N.nerve.edgeRight connector = vertex
  second_left : N.nerve.edgeLeft second = vertex
  second_right : N.nerve.edgeRight second = right
  diagonal_left : ∀ o, N.nerve.edgeLeft (diagonal o) = left
  diagonal_right : ∀ o, N.nerve.edgeRight (diagonal o) = right
  triangle0 : ∀ o, N.nerve.faceEdge0 (triangle o) = connector
  triangle1 : ∀ o, N.nerve.faceEdge1 (triangle o) = diagonal o
  triangle2 : ∀ o, N.nerve.faceEdge2 (triangle o) = second
  vertex_support : N.chartSupport vertex = N.chartSupport left
  center_not_triangle : ∀ o a, (position o).1 ≠ triangle a
  vertex_connections : ∀ a, N.nerve.edgeLeft a = vertex ∨ N.nerve.edgeRight a = vertex →
    a = connector ∨ a = second
  face_connections : ∀ F i, EdgeSubdivision.faceSlot N F i = connector ∨
    EdgeSubdivision.faceSlot N F i = second → ∃ o, F = triangle o
  diagonal_connections : ∀ F i o, EdgeSubdivision.faceSlot N F i = diagonal o ↔
    (F = triangle o ∧ i = 1) ∨ (F = (position o).1 ∧ i = (position o).2)

namespace SubdivisionInversePattern
variable {N : TargetSupportedNerve.{u, u} q} (P : SubdivisionInversePattern N)

/-- 原始対角辺単射から出現型の有限性を導く。 -/
instance occurrenceFintype : Fintype P.Occurrence := Fintype.ofInjective P.diagonal P.diagonal_injective

/-- 追加面名も対角辺単射と第1slotから別名である。 -/
theorem triangle_injective : Function.Injective P.triangle := by
  intro o a h
  apply P.diagonal_injective
  rw [← P.triangle1 o, ← P.triangle1 a, h]

/-- 各出現の中心面・位置に、同じ原始対角辺がある。 -/
theorem position_slot (o : P.Occurrence) :
    EdgeSubdivision.faceSlot N (P.position o).1 (P.position o).2 = P.diagonal o :=
  (P.diagonal_connections _ _ o).mpr (Or.inr ⟨rfl, rfl⟩)

/-- 二つの別名対角辺が同じ中心位置へ入ることはない。 -/
theorem position_injective : Function.Injective P.position := by
  intro o a h
  apply P.diagonal_injective
  rw [← P.position_slot o, ← P.position_slot a, h]

/-- 削除する全辺名の原始有限族。false=c、true=b、各出現がその対角辺。 -/
def removedEdge : Bool ⊕ P.Occurrence → N.nerve.EdgeComponent
  | .inl false => P.connector
  | .inl true => P.second
  | .inr o => P.diagonal o

/-- freshnessから、削除辺族の全タグは別名である。 -/
theorem removedEdge_injective : Function.Injective P.removedEdge := by
  rintro (b | o) (c | a) h
  · cases b <;> cases c
    · rfl
    · exact False.elim (P.connector_ne_second h)
    · exact False.elim (P.connector_ne_second h.symm)
    · rfl
  · cases b
    · exact False.elim (P.connector_ne_diagonal a h)
    · exact False.elim (P.second_ne_diagonal a h)
  · cases c
    · exact False.elim (P.connector_ne_diagonal o h.symm)
    · exact False.elim (P.second_ne_diagonal o h.symm)
  · exact congrArg Sum.inr (P.diagonal_injective h)

/-- 削除頂点以外の旧chart名。 -/
abbrev OldChart := {v : N.nerve.Chart // v ≠ P.vertex}
/-- 全削除辺族の外側の保持辺名。 -/
abbrev RetainedEdge := {a : N.nerve.EdgeComponent // ∀ j, a ≠ P.removedEdge j}
/-- 追加三角面をすべて除いた旧面名。 -/
abbrev OldFace := {F : N.nerve.FaceComponent // ∀ o, F ≠ P.triangle o}
/-- 保持辺と復元する共通辺の名前。 -/
abbrev OldEdge := P.RetainedEdge ⊕ PUnit.{u+1}

/-- 保持辺はconnectorではない。 -/
theorem retained_ne_connector (a : P.RetainedEdge) : a.1 ≠ P.connector := a.2 (.inl false)
/-- 保持辺はsecondでもない。 -/
theorem retained_ne_second (a : P.RetainedEdge) : a.1 ≠ P.second := a.2 (.inl true)
/-- 保持辺の左端点が削除頂点になる接続は全接続検査で除かれる。 -/
theorem retained_left (a : P.RetainedEdge) : N.nerve.edgeLeft a.1 ≠ P.vertex := by
  intro h
  rcases P.vertex_connections a.1 (Or.inl h) with h | h
  · exact P.retained_ne_connector a h
  · exact P.retained_ne_second a h
/-- 保持辺の右端点も削除頂点ではない。 -/
theorem retained_right (a : P.RetainedEdge) : N.nerve.edgeRight a.1 ≠ P.vertex := by
  intro h
  rcases P.vertex_connections a.1 (Or.inr h) with h | h
  · exact P.retained_ne_connector a h
  · exact P.retained_ne_second a h
/-- 保持面のどのslotにもconnectorは現れない。 -/
theorem oldSlot_ne_connector (F : P.OldFace) (i : Fin 3) :
    EdgeSubdivision.faceSlot N F.1 i ≠ P.connector := by
  intro h
  obtain ⟨o, ho⟩ := P.face_connections F.1 i (Or.inl h)
  exact F.2 o ho
/-- 保持面のどのslotにもsecondは現れない。 -/
theorem oldSlot_ne_second (F : P.OldFace) (i : Fin 3) :
    EdgeSubdivision.faceSlot N F.1 i ≠ P.second := by
  intro h
  obtain ⟨o, ho⟩ := P.face_connections F.1 i (Or.inr h)
  exact F.2 o ho

/-- 復元共通辺の始点。 -/
def oldLeftVertex : P.OldChart := ⟨P.left, P.left_ne_vertex⟩
/-- 復元共通辺の終点。loopの場合も同じ名前を許す。 -/
def oldRightVertex : P.OldChart := ⟨P.right, P.right_ne_vertex⟩
/-- 復元旧辺の左端点。保持辺は元端点、共通辺は指定始点。 -/
def oldLeft : P.OldEdge → P.OldChart
  | .inl a => ⟨N.nerve.edgeLeft a.1, P.retained_left a⟩
  | .inr _ => P.oldLeftVertex
/-- 復元旧辺の右端点。 -/
def oldRight : P.OldEdge → P.OldChart
  | .inl a => ⟨N.nerve.edgeRight a.1, P.retained_right a⟩
  | .inr _ => P.oldRightVertex

/-- 対角辺を共通辺へ戻し、それ以外を元の保持名へ戻す全slot式。 -/
def oldSlot (F : P.OldFace) (i : Fin 3) : P.OldEdge := by
  classical
  exact if h : ∃ o, EdgeSubdivision.faceSlot N F.1 i = P.diagonal o then .inr PUnit.unit
    else .inl ⟨EdgeSubdivision.faceSlot N F.1 i, by
      rintro (b | o)
      · cases b
        · exact P.oldSlot_ne_connector F i
        · exact P.oldSlot_ne_second F i
      · exact fun he => h ⟨o, he⟩⟩

/-- 対角辺のslotは復元共通辺へ写る。 -/
theorem oldSlot_of_diagonal (F : P.OldFace) (i : Fin 3) (o : P.Occurrence)
    (h : EdgeSubdivision.faceSlot N F.1 i = P.diagonal o) : P.oldSlot F i = .inr PUnit.unit := by
  classical
  simp [oldSlot, show ∃ a, EdgeSubdivision.faceSlot N F.1 i = P.diagonal a from ⟨o, h⟩]

/-- 復元slotが共通辺であることは、元slotが指定対角辺族に属することと同値。 -/
theorem oldSlot_eq_common_iff (F : P.OldFace) (i : Fin 3) :
    P.oldSlot F i = .inr PUnit.unit ↔ ∃ o, EdgeSubdivision.faceSlot N F.1 i = P.diagonal o := by
  classical
  dsimp [oldSlot]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- 対角辺がないslotの保持辺名の値。 -/
theorem oldSlot_of_no_diagonal (F : P.OldFace) (i : Fin 3)
    (h : ¬ ∃ o, EdgeSubdivision.faceSlot N F.1 i = P.diagonal o) :
    ∃ a : P.RetainedEdge, P.oldSlot F i = .inl a ∧ a.1 = EdgeSubdivision.faceSlot N F.1 i := by
  classical
  dsimp [oldSlot]
  rw [dif_neg h]
  exact ⟨_, rfl, rfl⟩

/-- 復元slotの左端点は、元slotの同じchart名。 -/
theorem oldSlot_left (F : P.OldFace) (i : Fin 3) :
    (P.oldLeft (P.oldSlot F i)).1 = N.nerve.edgeLeft (EdgeSubdivision.faceSlot N F.1 i) := by
  classical
  dsimp [oldSlot]
  split_ifs with h
  · obtain ⟨o, ho⟩ := h
    change P.left = _
    rw [ho, P.diagonal_left]
  · rfl
/-- 復元slotの右端点も元slotの同じchart名。 -/
theorem oldSlot_right (F : P.OldFace) (i : Fin 3) :
    (P.oldRight (P.oldSlot F i)).1 = N.nerve.edgeRight (EdgeSubdivision.faceSlot N F.1 i) := by
  classical
  dsimp [oldSlot]
  split_ifs with h
  · obtain ⟨o, ho⟩ := h
    change P.right = _
    rw [ho, P.diagonal_right]
  · rfl

/-- 共通辺を戻し、保持面の各対角slotを戻した旧nerve。 -/
def restoredNerve : CoverNerve.{u} where
  Chart := P.OldChart
  EdgeComponent := P.OldEdge
  FaceComponent := P.OldFace
  edgeLeft := P.oldLeft
  edgeRight := P.oldRight
  faceEdge0 := fun F => P.oldSlot F 0
  faceEdge1 := fun F => P.oldSlot F 1
  faceEdge2 := fun F => P.oldSlot F 2
  edgeOverlapComponent := fun a => match a with
    | .inl a => N.nerve.edgeOverlapComponent a.1
    | .inr _ => True
  faceTripleOverlapComponent := fun F => N.nerve.faceTripleOverlapComponent F.1
  edgeOverlapComponent_holds := by rintro (a | x); exact N.nerve.edgeOverlapComponent_holds a.1; trivial
  faceTripleOverlapComponent_holds := fun F => N.nerve.faceTripleOverlapComponent_holds F.1

/-- 元chart台を保持し、復元共通辺のK1台を生成する旧入力。 -/
def restored : TargetSupportedNerve q := by
  classical
  exact {
    nerve := P.restoredNerve
    chartFintype := by change Fintype P.OldChart; infer_instance
    edgeFintype := by change Fintype P.OldEdge; infer_instance
    faceFintype := by change Fintype P.OldFace; infer_instance
    chartSupport := fun v => N.chartSupport v.1
    chartSupport_nonempty := fun v => N.chartSupport_nonempty v.1
    faceEdge0_left := by
      intro F; apply Subtype.ext
      simpa only [restoredNerve, P.oldSlot_left, EdgeSubdivision.faceSlot_zero, EdgeSubdivision.faceSlot_one] using N.faceEdge0_left F.1
    faceEdge0_right := by
      intro F; apply Subtype.ext
      simpa only [restoredNerve, P.oldSlot_right, P.oldSlot_left, EdgeSubdivision.faceSlot_zero, EdgeSubdivision.faceSlot_two] using N.faceEdge0_right F.1
    faceEdge1_right := by
      intro F; apply Subtype.ext
      simpa only [restoredNerve, P.oldSlot_right, EdgeSubdivision.faceSlot_one, EdgeSubdivision.faceSlot_two] using N.faceEdge1_right F.1 }

/-- 復元する共通辺の指定名。 -/
def commonEdge : P.restored.nerve.EdgeComponent := .inr PUnit.unit
/-- 保持chart台は同じ原始台。 -/
@[simp] theorem restored_chartSupport (v : P.OldChart) : P.restored.chartSupport v = N.chartSupport v.1 := rfl
/-- 共通辺の台を、指定始終点の交差から作る。空でもよい。 -/
@[simp] theorem restored_commonSupport :
    P.restored.edgeSupport P.commonEdge = N.chartSupport P.left ∩ N.chartSupport P.right := rfl

/-- 復元面の三位置は、同じ原始oldSlot式。 -/
theorem restored_faceSlot (F : P.OldFace) (i : Fin 3) :
    EdgeSubdivision.faceSlot P.restored F i = P.oldSlot F i := by
  fin_cases i <;> rfl

/-- 中心面の指定位置の保持名を全接続入力から構成する。 -/
def positionFace (o : P.Occurrence) : P.OldFace :=
  ⟨(P.position o).1, P.center_not_triangle o⟩

/-- 指定各出現から、復元共通辺の面内出現を構成する。 -/
def toOccurrence (o : P.Occurrence) : EdgeSubdivision.Occurrence P.restored P.commonEdge :=
  ⟨(P.positionFace o, (P.position o).2), by
    rw [P.restored_faceSlot]
    exact P.oldSlot_of_diagonal _ _ o (P.position_slot o)⟩

/-- 復元共通辺の全出現について、原始対角辺の名前を回収する。 -/
def ofOccurrence (p : EdgeSubdivision.Occurrence P.restored P.commonEdge) : P.Occurrence :=
  Classical.choose ((P.oldSlot_eq_common_iff p.1.1 p.1.2).mp
    ((P.restored_faceSlot p.1.1 p.1.2).symm.trans p.2))

/-- 回収した対角名は元の中心slotの同じ辺である。 -/
theorem ofOccurrence_slot (p : EdgeSubdivision.Occurrence P.restored P.commonEdge) :
    EdgeSubdivision.faceSlot N p.1.1.1 p.1.2 = P.diagonal (P.ofOccurrence p) :=
  Classical.choose_spec ((P.oldSlot_eq_common_iff p.1.1 p.1.2).mp
    ((P.restored_faceSlot p.1.1 p.1.2).symm.trans p.2))

/-- 元の指定出現を回収すると同じ対角辺名へ戻る。 -/
@[simp] theorem ofOccurrence_toOccurrence (o : P.Occurrence) :
    P.ofOccurrence (P.toOccurrence o) = o := by
  apply P.diagonal_injective
  exact (P.ofOccurrence_slot (P.toOccurrence o)).symm.trans (P.position_slot o)

/-- 復元出現を指定位置へ戻すと、面名とFin3位置の両成分で恒等となる。 -/
@[simp] theorem toOccurrence_ofOccurrence (p : EdgeSubdivision.Occurrence P.restored P.commonEdge) :
    P.toOccurrence (P.ofOccurrence p) = p := by
  have h := (P.diagonal_connections _ _ (P.ofOccurrence p)).mp (P.ofOccurrence_slot p)
  rcases h with h | h
  · exact False.elim (p.1.1.2 (P.ofOccurrence p) h.1)
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact h.1.symm
    · exact h.2.symm

/-- 全出現の両逆。三重出現も面名・位置の組を保持する。 -/
def occurrenceEquiv : EdgeSubdivision.Occurrence P.restored P.commonEdge ≃ P.Occurrence where
  toFun := P.ofOccurrence
  invFun := P.toOccurrence
  left_inv := P.toOccurrence_ofOccurrence
  right_inv := P.ofOccurrence_toOccurrence

/-- 出現全単射の順方向の計算式。 -/
@[simp] theorem occurrenceEquiv_apply (p) : P.occurrenceEquiv p = P.ofOccurrence p := rfl
/-- 出現全単射の逆方向は指定中心位置。 -/
@[simp] theorem occurrenceEquiv_symm_apply (o) : P.occurrenceEquiv.symm o = P.toOccurrence o := rfl

end SubdivisionInversePattern
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
