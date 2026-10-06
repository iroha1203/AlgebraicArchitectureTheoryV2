import ResearchLean.AG.FaceRelationSubdivision.IncidenceBasis
import ResearchLean.AG.FaceRelationSubdivision.RawSupportedChain
import Formal.Util.AssertStandardAxioms

/-!
# 面の各出現を保持する辺分割の原始幾何

## Implementation notes

対象辺を除くセル名はsubtypeで保持し、追加辺c/b、対角辺、追加三角面を直和タグで作る。
出現は面名とFin3の位置の組であり、loopの同じ辺が三回現れる場合も別名である。
出現を辺名だけで索引する案は符号の異なる繰返しを潰すため採らない。
診断・逆写像・homotopyを入力に含めず、原始セル表とK1台から構成する。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution Cohomology ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}
namespace EdgeSubdivision
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)

/-- 三角面の三つの符号位置を独立に読む原始slot。 -/
def faceSlot (F : N.nerve.FaceComponent) (i : Fin 3) : N.nerve.EdgeComponent :=
  if i = 0 then N.nerve.faceEdge0 F else if i = 1 then N.nerve.faceEdge1 F else N.nerve.faceEdge2 F

/-- 第0位置の評価。 -/
@[simp] theorem faceSlot_zero (F : N.nerve.FaceComponent) : faceSlot N F 0 = N.nerve.faceEdge0 F := by
  simp [faceSlot]
/-- 第1位置の評価。 -/
@[simp] theorem faceSlot_one (F : N.nerve.FaceComponent) : faceSlot N F 1 = N.nerve.faceEdge1 F := by
  simp [faceSlot]
/-- 第2位置の評価。 -/
@[simp] theorem faceSlot_two (F : N.nerve.FaceComponent) : faceSlot N F 2 = N.nerve.faceEdge2 F := by
  simp [faceSlot]

/-- 旧辺の各出現。面名と位置を保持する。 -/
abbrev Occurrence := {p : N.nerve.FaceComponent × Fin 3 // faceSlot N p.1 p.2 = e}
/-- 分割対象以外の旧辺名。 -/
abbrev RetainedEdge := {a : N.nerve.EdgeComponent // a ≠ e}

/-- 有限な旧面とFin3位置の積のsubtypeとして、別名の全出現を有限に列挙する。 -/
instance occurrenceFintype : Fintype (Occurrence N e) := by classical infer_instance
/-- 有限な旧辺のsubtypeから、分割対象以外の保持辺の有限性を継承する。 -/
instance retainedEdgeFintype : Fintype (RetainedEdge N e) := by classical infer_instance

/-- 新辺名。false=c、true=b、各Occurrenceが別名の対角辺。 -/
abbrev Edge := RetainedEdge N e ⊕ (Bool ⊕ Occurrence N e)
/-- 新面名。旧面ごとの中心面と出現ごとの追加三角面。 -/
abbrev Face := N.nerve.FaceComponent ⊕ Occurrence N e

/-- 中心面の各旧slotを、非対象辺または当該出現の対角辺へ置換する。 -/
def centerEdge (F : N.nerve.FaceComponent) (i : Fin 3) : Edge N e := by
  classical
  exact if h : faceSlot N F i = e then .inr (.inr ⟨(F, i), h⟩)
    else .inl ⟨faceSlot N F i, h⟩

/-- 全出現を別々に再三角形化する名前付きnerve。 -/
def nerve : CoverNerve.{u} where
  Chart := N.nerve.Chart ⊕ PUnit.{u+1}
  EdgeComponent := Edge N e
  FaceComponent := Face N e
  edgeLeft := fun a => match a with
    | .inl a => .inl (N.nerve.edgeLeft a.1)
    | .inr (.inl false) => .inl (N.nerve.edgeLeft e)
    | .inr (.inl true) => .inr PUnit.unit
    | .inr (.inr _) => .inl (N.nerve.edgeLeft e)
  edgeRight := fun a => match a with
    | .inl a => .inl (N.nerve.edgeRight a.1)
    | .inr (.inl false) => .inr PUnit.unit
    | .inr (.inl true) => .inl (N.nerve.edgeRight e)
    | .inr (.inr _) => .inl (N.nerve.edgeRight e)
  faceEdge0 := fun F => match F with
    | .inl F => centerEdge N e F 0
    | .inr _ => .inr (.inl false)
  faceEdge1 := fun F => match F with
    | .inl F => centerEdge N e F 1
    | .inr o => .inr (.inr o)
  faceEdge2 := fun F => match F with
    | .inl F => centerEdge N e F 2
    | .inr _ => .inr (.inl true)
  edgeOverlapComponent := fun a => match a with
    | .inl a => N.nerve.edgeOverlapComponent a.1
    | .inr _ => True
  faceTripleOverlapComponent := fun F => match F with
    | .inl F => N.nerve.faceTripleOverlapComponent F
    | .inr _ => True
  edgeOverlapComponent_holds := by
    rintro (a | b)
    · exact N.nerve.edgeOverlapComponent_holds a.1
    · trivial
  faceTripleOverlapComponent_holds := by
    rintro (F | o)
    · exact N.nerve.faceTripleOverlapComponent_holds F
    · trivial

/-- 中心slotの左端点は元のslotの左端点。 -/
@[simp] theorem centerEdge_left (F : N.nerve.FaceComponent) (i : Fin 3) :
    (nerve N e).edgeLeft (centerEdge N e F i) = .inl (N.nerve.edgeLeft (faceSlot N F i)) := by
  classical
  dsimp [centerEdge]
  split_ifs with h
  · change Sum.inl (N.nerve.edgeLeft e) = _
    rw [h]
  · rfl

/-- 中心slotの右端点は元のslotの右端点。 -/
@[simp] theorem centerEdge_right (F : N.nerve.FaceComponent) (i : Fin 3) :
    (nerve N e).edgeRight (centerEdge N e F i) = .inl (N.nerve.edgeRight (faceSlot N F i)) := by
  classical
  dsimp [centerEdge]
  split_ifs with h
  · change Sum.inl (N.nerve.edgeRight e) = _
    rw [h]
  · rfl

/-- 旧chart台を保ち、新頂点の台を元辺の始点と同じにする。 -/
def supported : TargetSupportedNerve q := by
  classical
  exact {
    nerve := nerve N e
    chartFintype := by change Fintype (N.nerve.Chart ⊕ PUnit.{u+1}); infer_instance
    edgeFintype := by change Fintype (Edge N e); infer_instance
    faceFintype := by change Fintype (Face N e); infer_instance
    chartSupport := fun v => match v with
      | .inl v => N.chartSupport v
      | .inr _ => N.chartSupport (N.nerve.edgeLeft e)
    chartSupport_nonempty := by
      rintro (v | x)
      · exact N.chartSupport_nonempty v
      · exact N.chartSupport_nonempty (N.nerve.edgeLeft e)
    faceEdge0_left := by
      rintro (F | o)
      · change (nerve N e).edgeLeft (centerEdge N e F 0) = (nerve N e).edgeLeft (centerEdge N e F 1)
        simpa only [centerEdge_left, faceSlot_zero, faceSlot_one] using congrArg Sum.inl (N.faceEdge0_left F)
      · rfl
    faceEdge0_right := by
      rintro (F | o)
      · change (nerve N e).edgeRight (centerEdge N e F 0) = (nerve N e).edgeLeft (centerEdge N e F 2)
        simpa only [centerEdge_right, centerEdge_left, faceSlot_zero, faceSlot_two] using
          congrArg Sum.inl (N.faceEdge0_right F)
      · rfl
    faceEdge1_right := by
      rintro (F | o)
      · change (nerve N e).edgeRight (centerEdge N e F 1) = (nerve N e).edgeRight (centerEdge N e F 2)
        simpa only [centerEdge_right, faceSlot_one, faceSlot_two] using congrArg Sum.inl (N.faceEdge1_right F)
      · rfl }

/-- 旧chart台の評価。 -/
@[simp] theorem chartSupport_old (v : N.nerve.Chart) :
    (supported N e).chartSupport (.inl v) = N.chartSupport v := rfl
/-- 新chart台の評価。 -/
@[simp] theorem chartSupport_new : (supported N e).chartSupport (.inr PUnit.unit) =
    N.chartSupport (N.nerve.edgeLeft e) := rfl

/-- 保持した辺のK1台は同じ旧辺の台。 -/
@[simp] theorem edgeSupport_old (a : RetainedEdge N e) :
    (supported N e).edgeSupport (.inl a) = N.edgeSupport a.1 := rfl
/-- cの台は始点chart台。 -/
@[simp] theorem edgeSupport_c : (supported N e).edgeSupport (.inr (.inl false)) =
    N.chartSupport (N.nerve.edgeLeft e) := by
  ext t
  rw [(supported N e).mem_edgeSupport_iff]
  change (t ∈ N.chartSupport (N.nerve.edgeLeft e) ∧ t ∈ N.chartSupport (N.nerve.edgeLeft e)) ↔ _
  exact and_self_iff
/-- bの台は元辺の台。 -/
@[simp] theorem edgeSupport_b : (supported N e).edgeSupport (.inr (.inl true)) = N.edgeSupport e := rfl
/-- 各対角辺の台は元辺の台。出現名は別々に保持する。 -/
@[simp] theorem edgeSupport_diagonal (o : Occurrence N e) :
    (supported N e).edgeSupport (.inr (.inr o)) = N.edgeSupport e := rfl

/-- 各中心slotの台は対応する旧slotの台。 -/
theorem edgeSupport_center (F : N.nerve.FaceComponent) (i : Fin 3) :
    (supported N e).edgeSupport (centerEdge N e F i) = N.edgeSupport (faceSlot N F i) := by
  ext t
  rw [(supported N e).mem_edgeSupport_iff, N.mem_edgeSupport_iff]
  change (t ∈ (supported N e).chartSupport ((nerve N e).edgeLeft (centerEdge N e F i)) ∧
    t ∈ (supported N e).chartSupport ((nerve N e).edgeRight (centerEdge N e F i))) ↔ _
  rw [centerEdge_left, centerEdge_right, chartSupport_old, chartSupport_old]

/-- 中心面の台は元の面の台。 -/
@[simp] theorem faceSupport_center (F : N.nerve.FaceComponent) :
    (supported N e).faceSupport (.inl F) = N.faceSupport F := by
  ext t
  rw [(supported N e).mem_faceSupport_iff, N.mem_faceSupport_iff]
  change (t ∈ (supported N e).edgeSupport (centerEdge N e F 0) ∧
    t ∈ (supported N e).edgeSupport (centerEdge N e F 1) ∧
    t ∈ (supported N e).edgeSupport (centerEdge N e F 2)) ↔ _
  rw [edgeSupport_center, edgeSupport_center, edgeSupport_center,
    faceSlot_zero, faceSlot_one, faceSlot_two]

/-- 出現ごとの追加三角面の台は元辺の台。 -/
@[simp] theorem faceSupport_triangle (o : Occurrence N e) :
    (supported N e).faceSupport (.inr o) = N.edgeSupport e := by
  ext t
  rw [(supported N e).mem_faceSupport_iff]
  change (t ∈ (supported N e).edgeSupport (.inr (.inl false)) ∧
    t ∈ (supported N e).edgeSupport (.inr (.inr o)) ∧
    t ∈ (supported N e).edgeSupport (.inr (.inl true))) ↔ _
  rw [edgeSupport_c, edgeSupport_diagonal, edgeSupport_b, N.mem_edgeSupport_iff]
  exact ⟨fun h => h.2.1, fun h => ⟨h.1, h, h⟩⟩


/-- 原始収縮のchart表。 -/
def chartImage (v : (supported N e).nerve.Chart) : N.nerve.Chart := match v with
  | .inl v => v
  | .inr _ => N.nerve.edgeLeft e

/-- 原始収縮のedge表。cのみ零でありbと全対角辺はeへ写る。 -/
def edgeImage (a : Edge N e) : Option N.nerve.EdgeComponent := match a with
  | .inl a => some a.1
  | .inr (.inl false) => none
  | .inr (.inl true) => some e
  | .inr (.inr _) => some e

/-- 原始収縮のface表。中心面は旧面へ写り追加三角面は零。 -/
def faceImage (F : Face N e) : Option N.nerve.FaceComponent := match F with
  | .inl F => some F
  | .inr _ => none

/-- 中心slotの像は元のslotそのもの。 -/
@[simp] theorem edgeImage_center (F : N.nerve.FaceComponent) (i : Fin 3) :
    edgeImage N e (centerEdge N e F i) = some (faceSlot N F i) := by
  classical
  dsimp [centerEdge]
  split_ifs with h
  · change some e = some (faceSlot N F i)
    rw [h]
  · rfl

/-- 面付き辺分割のprimitive mixed比較。全fieldを原始セル表から構成する。 -/
def collapse : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) N (supported N e) where
  chartMap := chartImage N e
  edgeMap := edgeImage N e
  faceMap := faceImage N e
  edge_some_left := by
    rintro (a | b) j hj
    · cases Option.some.inj hj; rfl
    · rcases b with b | o
      · cases b
        · cases hj
        · cases Option.some.inj hj; rfl
      · cases Option.some.inj hj; rfl
  edge_some_right := by
    rintro (a | b) j hj
    · cases Option.some.inj hj; rfl
    · rcases b with b | o
      · cases b
        · cases hj
        · cases Option.some.inj hj; rfl
      · cases Option.some.inj hj; rfl
  edge_none_fiber := by
    rintro (a | b) hj
    · cases hj
    · rcases b with b | o
      · cases b
        · rfl
        · cases hj
      · cases hj
  face_some_edge0 := by
    rintro (F | o) G hG
    · cases Option.some.inj hG
      change edgeImage N e (centerEdge N e F 0) = some (N.nerve.faceEdge0 F)
      rw [edgeImage_center, faceSlot_zero]
    · cases hG
  face_some_edge1 := by
    rintro (F | o) G hG
    · cases Option.some.inj hG
      change edgeImage N e (centerEdge N e F 1) = some (N.nerve.faceEdge1 F)
      rw [edgeImage_center, faceSlot_one]
    · cases hG
  face_some_edge2 := by
    rintro (F | o) G hG
    · cases Option.some.inj hG
      change edgeImage N e (centerEdge N e F 2) = some (N.nerve.faceEdge2 F)
      rw [edgeImage_center, faceSlot_two]
    · cases hG
  face_none_incidence := by
    rintro (F | o) hF
    · cases hF
    · change optionCell (none : Option N.nerve.EdgeComponent) - optionCell (some e) + optionCell (some e) = 0
      simp
  chartSupport_compatible := by
    intro v t ht
    rw [AtlasDefectComposition.comparisonFactor_self]
    cases v <;> exact ht

/-- 同じ旧辺の各出現の対角辺名は位置も含めて相異なる。 -/
theorem diagonal_injective : Function.Injective
    (fun o : Occurrence N e => (Sum.inr (Sum.inr o) : Edge N e)) := by
  intro a b h
  exact Sum.inr.inj (Sum.inr.inj h)

/-- 同じ旧辺の各出現の三角面名も相異なる。 -/
theorem triangle_injective : Function.Injective
    (fun o : Occurrence N e => (Sum.inr o : Face N e)) := Sum.inr_injective

/-- 対象辺は旧保持辺の名前として残らない。 -/
theorem retired_edge_absent (a : RetainedEdge N e) : a.1 ≠ e := a.2

/-- 新辺のLeft端点のセル表評価。 -/
@[simp] theorem edgeLeft_old (a : RetainedEdge N e) : (supported N e).nerve.edgeLeft (.inl a) = Sum.inl (N.nerve.edgeLeft a.1) := rfl

/-- 新辺のRight端点のセル表評価。 -/
@[simp] theorem edgeRight_old (a : RetainedEdge N e) : (supported N e).nerve.edgeRight (.inl a) = Sum.inl (N.nerve.edgeRight a.1) := rfl

/-- 新辺のLeft端点のセル表評価。 -/
@[simp] theorem edgeLeft_c : (supported N e).nerve.edgeLeft (.inr (.inl false)) = Sum.inl (N.nerve.edgeLeft e) := rfl

/-- 新辺のRight端点のセル表評価。 -/
@[simp] theorem edgeRight_c : (supported N e).nerve.edgeRight (.inr (.inl false)) = Sum.inr PUnit.unit := rfl

/-- 新辺のLeft端点のセル表評価。 -/
@[simp] theorem edgeLeft_b : (supported N e).nerve.edgeLeft (.inr (.inl true)) = Sum.inr PUnit.unit := rfl

/-- 新辺のRight端点のセル表評価。 -/
@[simp] theorem edgeRight_b : (supported N e).nerve.edgeRight (.inr (.inl true)) = Sum.inl (N.nerve.edgeRight e) := rfl

/-- 新辺のLeft端点のセル表評価。 -/
@[simp] theorem edgeLeft_diagonal (o : Occurrence N e) : (supported N e).nerve.edgeLeft (.inr (.inr o)) = Sum.inl (N.nerve.edgeLeft e) := rfl

/-- 新辺のRight端点のセル表評価。 -/
@[simp] theorem edgeRight_diagonal (o : Occurrence N e) : (supported N e).nerve.edgeRight (.inr (.inr o)) = Sum.inl (N.nerve.edgeRight e) := rfl

/-- 中心面の第0slotのセル表評価。 -/
@[simp] theorem faceEdge0_center (F : N.nerve.FaceComponent) : (supported N e).nerve.faceEdge0 (.inl F) = centerEdge N e F 0 := rfl

/-- 追加面の第0slotのセル表評価。 -/
@[simp] theorem faceEdge0_triangle (o : Occurrence N e) : (supported N e).nerve.faceEdge0 (.inr o) = .inr (.inl false) := rfl

/-- 中心面の第1slotのセル表評価。 -/
@[simp] theorem faceEdge1_center (F : N.nerve.FaceComponent) : (supported N e).nerve.faceEdge1 (.inl F) = centerEdge N e F 1 := rfl

/-- 追加面の第1slotのセル表評価。 -/
@[simp] theorem faceEdge1_triangle (o : Occurrence N e) : (supported N e).nerve.faceEdge1 (.inr o) = .inr (.inr o) := rfl

/-- 中心面の第2slotのセル表評価。 -/
@[simp] theorem faceEdge2_center (F : N.nerve.FaceComponent) : (supported N e).nerve.faceEdge2 (.inl F) = centerEdge N e F 2 := rfl

/-- 追加面の第2slotのセル表評価。 -/
@[simp] theorem faceEdge2_triangle (o : Occurrence N e) : (supported N e).nerve.faceEdge2 (.inr o) = .inr (.inl true) := rfl

/-- 原始chart収縮のセル表評価。 -/
@[simp] theorem chartImage_old (v : N.nerve.Chart) : chartImage N e (.inl v) = v := rfl

/-- 原始chart収縮のセル表評価。 -/
@[simp] theorem chartImage_new  : chartImage N e (.inr PUnit.unit) = N.nerve.edgeLeft e := rfl

/-- 原始edge収縮のセル表評価。 -/
@[simp] theorem edgeImage_old (a : RetainedEdge N e) : edgeImage N e (.inl a) = some a.1 := rfl

/-- 原始edge収縮のセル表評価。 -/
@[simp] theorem edgeImage_c  : edgeImage N e (.inr (.inl false)) = none := rfl

/-- 原始edge収縮のセル表評価。 -/
@[simp] theorem edgeImage_b  : edgeImage N e (.inr (.inl true)) = some e := rfl

/-- 原始edge収縮のセル表評価。 -/
@[simp] theorem edgeImage_diagonal (o : Occurrence N e) : edgeImage N e (.inr (.inr o)) = some e := rfl

/-- 原始face収縮のセル表評価。 -/
@[simp] theorem faceImage_center (F : N.nerve.FaceComponent) : faceImage N e (.inl F) = some F := rfl

/-- 原始face収縮のセル表評価。 -/
@[simp] theorem faceImage_triangle (o : Occurrence N e) : faceImage N e (.inr o) = none := rfl
/-- 対象辺の出現位置の中心辺はその対角辺である。 -/
theorem centerEdge_of_eq (F : N.nerve.FaceComponent) (i : Fin 3) (h : faceSlot N F i = e) :
    centerEdge N e F i = .inr (.inr ⟨(F,i),h⟩) := by
  classical
  simp [centerEdge, h]
/-- 対象以外の位置は元の保持辺である。 -/
theorem centerEdge_of_ne (F : N.nerve.FaceComponent) (i : Fin 3) (h : faceSlot N F i ≠ e) :
    centerEdge N e F i = .inl ⟨faceSlot N F i,h⟩ := by
  classical
  simp [centerEdge, h]

end EdgeSubdivision
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
