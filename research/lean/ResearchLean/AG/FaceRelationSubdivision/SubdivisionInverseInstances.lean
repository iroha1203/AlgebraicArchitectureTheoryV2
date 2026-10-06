import ResearchLean.AG.FaceRelationSubdivision.SubdivisionReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# 正操作の全出現patternと追加接続による拒否

## Implementation notes

任意の旧nerveと辺から、面名とFin 3位置を保持した原始逆patternを生成する。
loop・同じ面の繰返し出現・出現なしを除外する仮定を加えない。
中心slotの公開評価APIで、対角辺の全出現の両方向を検証する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution Cohomology ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}
namespace SubdivisionInversePattern

/-- 中心slotと指定対角名の等号は、指定された面名・位置そのものの等号。 -/
theorem centerEdge_eq_diagonal_iff (M : TargetSupportedNerve.{u,u} q)
    (e : M.nerve.EdgeComponent) (F : M.nerve.FaceComponent) (i : Fin 3)
    (o : EdgeSubdivision.Occurrence M e) :
    EdgeSubdivision.centerEdge M e F i = .inr (.inr o) ↔ (F,i) = o.1 := by
  classical
  by_cases h : EdgeSubdivision.faceSlot M F i = e
  · rw [EdgeSubdivision.centerEdge_of_eq M e F i h]
    constructor
    · intro he
      exact congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj he))
    · intro he
      exact congrArg (fun a => Sum.inr (Sum.inr a)) (Subtype.ext he)
  · rw [EdgeSubdivision.centerEdge_of_ne M e F i h]
    constructor
    · intro he; cases he
    · intro he
      exact False.elim (h ((congrArg (fun p => EdgeSubdivision.faceSlot M p.1 p.2) he).trans o.2))

/-- 中心面の全slotを同じ公開centerEdgeとして読む。 -/
theorem center_slot (M : TargetSupportedNerve.{u,u} q) (e : M.nerve.EdgeComponent)
    (F : M.nerve.FaceComponent) (i : Fin 3) :
    EdgeSubdivision.faceSlot (EdgeSubdivision.supported M e) (.inl F) i =
      EdgeSubdivision.centerEdge M e F i := by
  fin_cases i <;> rfl

/-- 中心slotはconnectorにもsecondにもならない。 -/
theorem center_not_connector_second (M : TargetSupportedNerve.{u,u} q)
    (e : M.nerve.EdgeComponent) (F : M.nerve.FaceComponent) (i : Fin 3) :
    EdgeSubdivision.centerEdge M e F i ≠ .inr (.inl false) ∧
    EdgeSubdivision.centerEdge M e F i ≠ .inr (.inl true) := by
  classical
  by_cases h : EdgeSubdivision.faceSlot M F i = e
  · rw [EdgeSubdivision.centerEdge_of_eq M e F i h]
    constructor <;> intro he <;> cases Sum.inr.inj he
  · rw [EdgeSubdivision.centerEdge_of_ne M e F i h]
    constructor <;> intro he <;> cases he

/-- 任意の正の面付き辺分割から、全接続を検査する原始逆patternを生成する。 -/
def ofSubdivision (M : TargetSupportedNerve.{u,u} q) (e : M.nerve.EdgeComponent) :
    SubdivisionInversePattern (EdgeSubdivision.supported M e) where
  vertex := .inr PUnit.unit
  left := .inl (M.nerve.edgeLeft e)
  right := .inl (M.nerve.edgeRight e)
  connector := .inr (.inl false)
  second := .inr (.inl true)
  Occurrence := EdgeSubdivision.Occurrence M e
  diagonal := fun o => .inr (.inr o)
  triangle := Sum.inr
  position := fun o => (.inl o.1.1, o.1.2)
  left_ne_vertex := by simp
  right_ne_vertex := by simp
  connector_ne_second := by intro h; cases Sum.inl.inj (Sum.inr.inj h)
  connector_ne_diagonal := by intro o h; cases Sum.inr.inj h
  second_ne_diagonal := by intro o h; cases Sum.inr.inj h
  diagonal_injective := by intro a b h; exact Sum.inr.inj (Sum.inr.inj h)
  connector_left := rfl
  connector_right := rfl
  second_left := rfl
  second_right := rfl
  diagonal_left := by intro o; rfl
  diagonal_right := by intro o; rfl
  triangle0 := by intro o; rfl
  triangle1 := by intro o; rfl
  triangle2 := by intro o; rfl
  vertex_support := rfl
  center_not_triangle := by intro o a h; cases h
  vertex_connections := by
    rintro (a | (b | o)) h
    · rcases h with h | h <;> cases h
    · cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases h with h | h <;> cases h
  face_connections := by
    rintro (F | o) i h
    · rw [center_slot] at h
      rcases h with h | h
      · exact False.elim ((center_not_connector_second M e F i).1 h)
      · exact False.elim ((center_not_connector_second M e F i).2 h)
    · exact ⟨o,rfl⟩
  diagonal_connections := by
    rintro (F | a) i o
    · rw [center_slot, centerEdge_eq_diagonal_iff]
      constructor
      · intro h
        exact Or.inr ⟨congrArg Sum.inl (congrArg Prod.fst h), congrArg Prod.snd h⟩
      · rintro (⟨h,_⟩ | ⟨hF,hi⟩)
        · cases h
        · exact Prod.ext (Sum.inl.inj hF) hi
    · fin_cases i
      · constructor
        · intro h; cases Sum.inr.inj h
        · rintro (⟨_,h⟩ | ⟨h,_⟩) <;> cases h
      · change Sum.inr (Sum.inr a) = Sum.inr (Sum.inr o) ↔
          (Sum.inr a = Sum.inr o ∧ (1 : Fin 3) = 1) ∨
          (Sum.inr a = Sum.inl o.1.1 ∧ (1 : Fin 3) = o.1.2)
        constructor
        · intro h; exact Or.inl ⟨congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h)),rfl⟩
        · rintro (⟨h,_⟩ | ⟨h,_⟩)
          · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Sum.inr.inj h)
          · cases h
      · constructor
        · intro h; cases Sum.inr.inj h
        · rintro (⟨_,h⟩ | ⟨h,_⟩) <;> cases h

/-- 第三辺がfresh頂点へ接続すると、指定局所名の逆patternは存在しない。 -/
theorem no_pattern_with_extra_edge {N : TargetSupportedNerve.{u,u} q}
    (vp : N.nerve.Chart) (c b a : N.nerve.EdgeComponent)
    (ha : N.nerve.edgeLeft a = vp ∨ N.nerve.edgeRight a = vp) (hac : a ≠ c) (hab : a ≠ b) :
    ¬ ∃ P : SubdivisionInversePattern N, P.vertex = vp ∧ P.connector = c ∧ P.second = b := by
  rintro ⟨P,hv,hc,hb⟩
  rcases P.vertex_connections a (by simpa [hv] using ha) with h | h
  · exact hac (h.trans hc)
  · exact hab (h.trans hb)

/-- 分割connectorへ三角形をさらに加える実操作は、最初の局所逆patternを拒否する。 -/
theorem addition_rejects_subdivision_pattern (M : TargetSupportedNerve.{u,u} q)
    (e : M.nerve.EdgeComponent) :
    ¬ ∃ P : SubdivisionInversePattern
      (TriangleAddition.supported (EdgeSubdivision.supported M e) (.inr (.inl false))),
      P.vertex = .inl (.inr PUnit.unit) ∧ P.connector = .inl (.inr (.inl false)) ∧
        P.second = .inl (.inr (.inl true)) :=
  no_pattern_with_extra_edge _ _ _ (.inr true) (Or.inr rfl) (by simp) (by simp)

end SubdivisionInversePattern
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
