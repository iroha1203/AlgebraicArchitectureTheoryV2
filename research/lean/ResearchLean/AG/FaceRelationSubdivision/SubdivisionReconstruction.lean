import ResearchLean.AG.FaceRelationSubdivision.PrimitiveSubdivisionInverse
import ResearchLean.AG.FaceRelationSubdivision.PresentationInverse
import Formal.Util.AssertStandardAxioms

/-!
# 原始辺分割逆patternを正操作で復元する

## Implementation notes

共通辺以外の復元辺と元の保持辺、面内出現と指定対角名を両逆で同定する。
それらを削除名の全単射と合成して全セル名を戻し、全incidence・chart台を検証する。
元入力への表示同型を先に供給する案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}
namespace SubdivisionInversePattern
variable {N : TargetSupportedNerve.{u, u} q} (P : SubdivisionInversePattern N)

/-- 復元共通辺を除く旧辺は、元入力の保持辺と両逆で一致する。 -/
def retainedEquiv : EdgeSubdivision.RetainedEdge P.restored P.commonEdge ≃ P.RetainedEdge where
  toFun := fun a => match h : a.1 with
    | .inl b => b
    | .inr x => False.elim (a.2 (by cases x; exact h))
  invFun := fun a => ⟨.inl a, by intro h; cases h⟩
  left_inv := by
    rintro ⟨a, ha⟩
    cases a with
    | inl a => rfl
    | inr x => cases x; exact False.elim (ha rfl)
  right_inv := fun _ => rfl

/-- 保持旧辺名への両逆の逆方向。 -/
@[simp] theorem retainedEquiv_symm_apply (a : P.RetainedEdge) :
    (P.retainedEquiv.symm a).1 = .inl a := rfl

/-- 保持辺の原始値が指定名なら、順方向の復元全単射もその名前を返す。 -/
theorem retainedEquiv_apply_of_val_eq
    (a : EdgeSubdivision.RetainedEdge P.restored P.commonEdge) (b : P.RetainedEdge)
    (h : a.1 = .inl b) : P.retainedEquiv a = b := by
  apply P.retainedEquiv.symm.injective
  apply Subtype.ext
  simpa only [Equiv.symm_apply_apply, P.retainedEquiv_symm_apply] using h

/-- 正分割後の全辺名を、保持・二辺・各対角名へ戻す両逆。 -/
def recoveredEdgeEquiv : (EdgeSubdivision.supported P.restored P.commonEdge).nerve.EdgeComponent ≃
    N.nerve.EdgeComponent :=
  (Equiv.sumCongr P.retainedEquiv (Equiv.sumCongr (Equiv.refl Bool) P.occurrenceEquiv)).trans
    (deleteFamilyEquiv P.removedEdge P.removedEdge_injective)

/-- 正分割後の全面名を、保持面・各追加三角名へ戻す両逆。 -/
def recoveredFaceEquiv : (EdgeSubdivision.supported P.restored P.commonEdge).nerve.FaceComponent ≃
    N.nerve.FaceComponent :=
  (Equiv.sumCongr (Equiv.refl P.OldFace) P.occurrenceEquiv).trans
    (deleteFamilyEquiv P.triangle P.triangle_injective)

/-- 保持辺の原始名への復元。 -/
@[simp] theorem recoveredEdge_old (a : EdgeSubdivision.RetainedEdge P.restored P.commonEdge) :
    P.recoveredEdgeEquiv (.inl a) = (P.retainedEquiv a).1 := rfl
/-- connectorの原始名への復元。 -/
@[simp] theorem recoveredEdge_connector :
    P.recoveredEdgeEquiv (.inr (.inl false)) = P.connector := rfl
/-- secondの原始名への復元。 -/
@[simp] theorem recoveredEdge_second :
    P.recoveredEdgeEquiv (.inr (.inl true)) = P.second := rfl
/-- 各面内出現の対角名への復元。 -/
@[simp] theorem recoveredEdge_diagonal (o : EdgeSubdivision.Occurrence P.restored P.commonEdge) :
    P.recoveredEdgeEquiv (.inr (.inr o)) = P.diagonal (P.ofOccurrence o) := rfl
/-- 保持面名は同じ名前で復元。 -/
@[simp] theorem recoveredFace_old (F : P.OldFace) : P.recoveredFaceEquiv (.inl F) = F.1 := rfl
/-- 各追加面も同じ出現名で復元。 -/
@[simp] theorem recoveredFace_triangle (o : EdgeSubdivision.Occurrence P.restored P.commonEdge) :
    P.recoveredFaceEquiv (.inr o) = P.triangle (P.ofOccurrence o) := rfl

/-- 中心面の全slotを元の同じ辺へ戻す。出現位置を落とさない。 -/
theorem recovered_centerEdge (F : P.OldFace) (i : Fin 3) :
    P.recoveredEdgeEquiv (EdgeSubdivision.centerEdge P.restored P.commonEdge F i) =
      EdgeSubdivision.faceSlot N F.1 i := by
  classical
  by_cases h : ∃ o, EdgeSubdivision.faceSlot N F.1 i = P.diagonal o
  · obtain ⟨o, ho⟩ := h
    have hs : EdgeSubdivision.faceSlot P.restored F i = P.commonEdge :=
      (P.restored_faceSlot F i).trans (P.oldSlot_of_diagonal F i o ho)
    rw [EdgeSubdivision.centerEdge_of_eq _ _ _ _ hs, P.recoveredEdge_diagonal]
    exact (P.ofOccurrence_slot ⟨(F, i), hs⟩).symm
  · obtain ⟨a, ha, hv⟩ := P.oldSlot_of_no_diagonal F i h
    have hs : EdgeSubdivision.faceSlot P.restored F i ≠ P.commonEdge := by
      rw [P.restored_faceSlot, ha]
      intro h'; cases h'
    rw [EdgeSubdivision.centerEdge_of_ne _ _ _ _ hs, P.recoveredEdge_old]
    change (P.retainedEquiv ⟨EdgeSubdivision.faceSlot P.restored F i, hs⟩).1 = _
    have he : EdgeSubdivision.faceSlot P.restored F i = .inl a :=
      (P.restored_faceSlot F i).trans ha
    rw [P.retainedEquiv_apply_of_val_eq _ a he]
    exact hv

/-- 保持辺の復元左端点は元の同じchart名。 -/
theorem retained_left_val (a : EdgeSubdivision.RetainedEdge P.restored P.commonEdge) :
    (P.restored.nerve.edgeLeft a.1).1 = N.nerve.edgeLeft (P.retainedEquiv a).1 := by
  rcases a with ⟨a, ha⟩
  cases a with
  | inl a => rfl
  | inr x => cases x; exact False.elim (ha rfl)
/-- 保持辺の復元右端点も同じchart名。 -/
theorem retained_right_val (a : EdgeSubdivision.RetainedEdge P.restored P.commonEdge) :
    (P.restored.nerve.edgeRight a.1).1 = N.nerve.edgeRight (P.retainedEquiv a).1 := by
  rcases a with ⟨a, ha⟩
  cases a with
  | inl a => rfl
  | inr x => cases x; exact False.elim (ha rfl)

/-- 原始逆patternから復元して正分割した入力は、元の全セル・台表示へ戻る。 -/
def presentation : CellPresentationEquiv q q (Reading.coarserThan_refl q) N
    (EdgeSubdivision.supported P.restored P.commonEdge) where
  chartEquiv := deleteOneEquiv P.vertex
  edgeEquiv := P.recoveredEdgeEquiv
  faceEquiv := P.recoveredFaceEquiv
  edge_left := by
    rintro (a | (b | o))
    · exact P.retained_left_val a
    · cases b
      · exact P.connector_left.symm
      · exact P.second_left.symm
    · exact (P.diagonal_left _).symm
  edge_right := by
    rintro (a | (b | o))
    · exact P.retained_right_val a
    · cases b
      · exact P.connector_right.symm
      · exact P.second_right.symm
    · exact (P.diagonal_right _).symm
  face_edge0 := by
    rintro (F | o)
    · exact P.recovered_centerEdge F 0
    · exact (P.triangle0 _).symm
  face_edge1 := by
    rintro (F | o)
    · exact P.recovered_centerEdge F 1
    · exact (P.triangle1 _).symm
  face_edge2 := by
    rintro (F | o)
    · exact P.recovered_centerEdge F 2
    · exact (P.triangle2 _).symm
  chartSupport_eq := by
    rintro (v | x)
    · ext t
      change t ∈ N.chartSupport v.1 ↔ comparisonFactor q q (Reading.coarserThan_refl q) t ∈ N.chartSupport v.1
      rw [TriangleAddition.self_factor]
    · ext t
      change t ∈ N.chartSupport P.left ↔ comparisonFactor q q (Reading.coarserThan_refl q) t ∈ N.chartSupport P.vertex
      rw [TriangleAddition.self_factor, P.vertex_support]

end SubdivisionInversePattern
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
