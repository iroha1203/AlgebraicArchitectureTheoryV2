import ResearchLean.AG.FaceRelationSubdivision.IncidenceComparison
import Formal.Util.AssertStandardAxioms

/-!
# 原始辺からの三角形追加

G-134 B§2のセル名・台・incidenceを原始constructorで生成する。

## Implementation notes

各次数の直和タグでfreshnessを保証する。旧面のincidenceと台を保持し、
新しい面は辺の像の相殺によって退化する。写像や保存結論を入力に含めない。
旧セル型の要素を流用する表現はfreshnessを別仮定にするため採らず、
既存の名前を保持したまま衝突を型で排除できる直和タグを用いる。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution Cohomology ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}

namespace TriangleAddition
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)

/-- 元の辺を保持し、新頂点・二辺・一面を追加した名前付きnerve。 -/
def nerve : CoverNerve.{u} where
  Chart := N.nerve.Chart ⊕ PUnit.{u+1}
  EdgeComponent := N.nerve.EdgeComponent ⊕ Bool
  FaceComponent := N.nerve.FaceComponent ⊕ PUnit.{u+1}
  edgeLeft := fun x => match x with
    | .inl a => .inl (N.nerve.edgeLeft a)
    | .inr false => .inl (N.nerve.edgeLeft e)
    | .inr true => .inr PUnit.unit
  edgeRight := fun x => match x with
    | .inl a => .inl (N.nerve.edgeRight a)
    | .inr false => .inr PUnit.unit
    | .inr true => .inl (N.nerve.edgeRight e)
  faceEdge0 := fun x => match x with
    | .inl f => .inl (N.nerve.faceEdge0 f)
    | .inr _ => .inr false
  faceEdge1 := fun x => match x with
    | .inl f => .inl (N.nerve.faceEdge1 f)
    | .inr _ => .inl e
  faceEdge2 := fun x => match x with
    | .inl f => .inl (N.nerve.faceEdge2 f)
    | .inr _ => .inr true
  edgeOverlapComponent := fun x => match x with
    | .inl a => N.nerve.edgeOverlapComponent a
    | .inr _ => True
  faceTripleOverlapComponent := fun x => match x with
    | .inl f => N.nerve.faceTripleOverlapComponent f
    | .inr _ => True
  edgeOverlapComponent_holds := by
    rintro (a | b)
    · exact N.nerve.edgeOverlapComponent_holds a
    · trivial
  faceTripleOverlapComponent_holds := by
    rintro (f | x)
    · exact N.nerve.faceTripleOverlapComponent_holds f
    · trivial

/-- chart台は旧chartで同じ、新頂点では元辺の始点と同じ。 -/
def supported : TargetSupportedNerve q where
  nerve := nerve N e
  chartFintype := by change Fintype (N.nerve.Chart ⊕ PUnit.{u+1}); infer_instance
  edgeFintype := by change Fintype (N.nerve.EdgeComponent ⊕ Bool); infer_instance
  faceFintype := by change Fintype (N.nerve.FaceComponent ⊕ PUnit.{u+1}); infer_instance
  chartSupport := fun x => match x with
    | .inl v => N.chartSupport v
    | .inr _ => N.chartSupport (N.nerve.edgeLeft e)
  chartSupport_nonempty := by
    rintro (v | x)
    · exact N.chartSupport_nonempty v
    · exact N.chartSupport_nonempty (N.nerve.edgeLeft e)
  faceEdge0_left := by
    rintro (f | x)
    · exact congrArg Sum.inl (N.faceEdge0_left f)
    · rfl
  faceEdge0_right := by
    rintro (f | x)
    · exact congrArg Sum.inl (N.faceEdge0_right f)
    · rfl
  faceEdge1_right := by
    rintro (f | x)
    · exact congrArg Sum.inl (N.faceEdge1_right f)
    · rfl

/-- 旧chart台の保持。 -/
@[simp] theorem chartSupport_old (v : N.nerve.Chart) :
    (supported N e).chartSupport (.inl v) = N.chartSupport v := rfl

/-- fresh頂点の台等号。 -/
@[simp] theorem chartSupport_new :
    (supported N e).chartSupport (.inr PUnit.unit) =
      N.chartSupport (N.nerve.edgeLeft e) := rfl

/-- 追加辺cのK1台は新頂点・始点の台と一致する。 -/
@[simp] theorem edgeSupport_c :
    (supported N e).edgeSupport (.inr false) = N.chartSupport (N.nerve.edgeLeft e) := by
  ext t
  rw [(supported N e).mem_edgeSupport_iff]
  change (t ∈ N.chartSupport (N.nerve.edgeLeft e) ∧
    t ∈ N.chartSupport (N.nerve.edgeLeft e)) ↔ _
  exact and_self_iff

/-- 追加辺e2のK1台は元辺の台と一致する。 -/
@[simp] theorem edgeSupport_e2 :
    (supported N e).edgeSupport (.inr true) = N.edgeSupport e := rfl

/-- 旧辺のK1台は保持される。 -/
@[simp] theorem edgeSupport_old (a : N.nerve.EdgeComponent) :
    (supported N e).edgeSupport (.inl a) = N.edgeSupport a := rfl

/-- 追加面fのK1台は元辺の台と一致する。 -/
@[simp] theorem faceSupport_new :
    (supported N e).faceSupport (.inr PUnit.unit) = N.edgeSupport e := by
  ext t
  rw [(supported N e).mem_faceSupport_iff]
  change (t ∈ (supported N e).edgeSupport (.inr false) ∧
    t ∈ (supported N e).edgeSupport (.inl e) ∧
    t ∈ (supported N e).edgeSupport (.inr true)) ↔ _
  rw [edgeSupport_c, edgeSupport_old, edgeSupport_e2, N.mem_edgeSupport_iff]
  exact ⟨fun h => h.2.1, fun h => ⟨h.1, h, h⟩⟩

/-- 旧面のK1台は保持される。 -/
@[simp] theorem faceSupport_old (f : N.nerve.FaceComponent) :
    (supported N e).faceSupport (.inl f) = N.faceSupport f := rfl

/-- 同じreadingの因子の点ごとの式。全射から得る。 -/
theorem self_factor (t : q.Target) : comparisonFactor q q (Reading.coarserThan_refl q) t = t := by
  obtain ⟨s, rfl⟩ := q.surjective t
  exact comparisonFactor_commutes q q (Reading.coarserThan_refl q) s

/-- 三角形追加の原始収縮。新面の相殺は0-e+e。 -/
def collapse : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) N (supported N e) where
  chartMap := fun x => match x with
    | .inl v => v
    | .inr _ => N.nerve.edgeLeft e
  edgeMap := fun x => match x with
    | .inl a => some a
    | .inr false => none
    | .inr true => some e
  faceMap := fun x => match x with
    | .inl f => some f
    | .inr _ => none
  edge_some_left := by
    rintro (a | b) c h
    · cases Option.some.inj h; rfl
    · cases b
      · cases h
      · cases Option.some.inj h; rfl
  edge_some_right := by
    rintro (a | b) c h
    · cases Option.some.inj h; rfl
    · cases b
      · cases h
      · cases Option.some.inj h; rfl
  edge_none_fiber := by
    rintro (a | b) h
    · cases h
    · cases b
      · rfl
      · cases h
  face_some_edge0 := by
    rintro (f | x) g h
    · cases Option.some.inj h; rfl
    · cases h
  face_some_edge1 := by
    rintro (f | x) g h
    · cases Option.some.inj h; rfl
    · cases h
  face_some_edge2 := by
    rintro (f | x) g h
    · cases Option.some.inj h; rfl
    · cases h
  face_none_incidence := by
    rintro (f | x) h
    · cases h
    · change optionCell (none : Option N.nerve.EdgeComponent) - optionCell (some e) + optionCell (some e) = 0
      simp
  chartSupport_compatible := by
    intro v t ht
    rw [self_factor]
    cases v <;> exact ht

/-- 原始収縮には非零辺像を持つ退化面が実際にある。 -/
theorem collapse_mixed_degenerate :
    (collapse N e).faceMap (.inr PUnit.unit) = none ∧
      (collapse N e).edgeMap (.inr false) = none ∧
      (collapse N e).edgeMap (.inr true) = some e ∧
      (collapse N e).edgeMap (.inl e) = some e := ⟨rfl, rfl, rfl, rfl⟩

/-- 同じ原始セル写像は旧hereditary条件を満たさない。 -/
theorem collapse_not_hereditary :
    ¬ ∃ M : TargetSupportedNerveMorphism q q (Reading.coarserThan_refl q) N (supported N e),
      M.edgeMap = (collapse N e).edgeMap ∧ M.faceMap = (collapse N e).faceMap := by
  rintro ⟨M, he, hf⟩
  have hm := M.face_none_edge1 (.inr PUnit.unit) (by rw [hf]; rfl)
  rw [he] at hm
  cases hm


/-! ## 原始セル表の公開評価API -/
/-- 原始constructorのedgeLeft_old評価。 -/
@[simp] theorem edgeLeft_old (a : N.nerve.EdgeComponent) :
    (supported N e).nerve.edgeLeft (.inl a) = .inl (N.nerve.edgeLeft a) := rfl

/-- 原始constructorのedgeRight_old評価。 -/
@[simp] theorem edgeRight_old (a : N.nerve.EdgeComponent) :
    (supported N e).nerve.edgeRight (.inl a) = .inl (N.nerve.edgeRight a) := rfl

/-- 原始constructorのedgeLeft_c評価。 -/
@[simp] theorem edgeLeft_c  :
    (supported N e).nerve.edgeLeft (.inr false) = .inl (N.nerve.edgeLeft e) := rfl

/-- 原始constructorのedgeRight_c評価。 -/
@[simp] theorem edgeRight_c  :
    (supported N e).nerve.edgeRight (.inr false) = .inr PUnit.unit := rfl

/-- 原始constructorのedgeLeft_e2評価。 -/
@[simp] theorem edgeLeft_e2  :
    (supported N e).nerve.edgeLeft (.inr true) = .inr PUnit.unit := rfl

/-- 原始constructorのedgeRight_e2評価。 -/
@[simp] theorem edgeRight_e2  :
    (supported N e).nerve.edgeRight (.inr true) = .inl (N.nerve.edgeRight e) := rfl

/-- 原始constructorのfaceEdge0_old評価。 -/
@[simp] theorem faceEdge0_old (f : N.nerve.FaceComponent) :
    (supported N e).nerve.faceEdge0 (.inl f) = .inl (N.nerve.faceEdge0 f) := rfl

/-- 原始constructorのfaceEdge1_old評価。 -/
@[simp] theorem faceEdge1_old (f : N.nerve.FaceComponent) :
    (supported N e).nerve.faceEdge1 (.inl f) = .inl (N.nerve.faceEdge1 f) := rfl

/-- 原始constructorのfaceEdge2_old評価。 -/
@[simp] theorem faceEdge2_old (f : N.nerve.FaceComponent) :
    (supported N e).nerve.faceEdge2 (.inl f) = .inl (N.nerve.faceEdge2 f) := rfl

/-- 原始constructorのfaceEdge0_new評価。 -/
@[simp] theorem faceEdge0_new  :
    (supported N e).nerve.faceEdge0 (.inr PUnit.unit) = .inr false := rfl

/-- 原始constructorのfaceEdge1_new評価。 -/
@[simp] theorem faceEdge1_new  :
    (supported N e).nerve.faceEdge1 (.inr PUnit.unit) = .inl e := rfl

/-- 原始constructorのfaceEdge2_new評価。 -/
@[simp] theorem faceEdge2_new  :
    (supported N e).nerve.faceEdge2 (.inr PUnit.unit) = .inr true := rfl

/-- 原始constructorのcollapse_chart_old評価。 -/
@[simp] theorem collapse_chart_old (v : N.nerve.Chart) :
    (collapse N e).chartMap (.inl v) = v := rfl

/-- 原始constructorのcollapse_chart_new評価。 -/
@[simp] theorem collapse_chart_new  :
    (collapse N e).chartMap (.inr PUnit.unit) = N.nerve.edgeLeft e := rfl

/-- 原始constructorのcollapse_edge_old評価。 -/
@[simp] theorem collapse_edge_old (a : N.nerve.EdgeComponent) :
    (collapse N e).edgeMap (.inl a) = some a := rfl

/-- 原始constructorのcollapse_edge_c評価。 -/
@[simp] theorem collapse_edge_c  :
    (collapse N e).edgeMap (.inr false) = none := rfl

/-- 原始constructorのcollapse_edge_e2評価。 -/
@[simp] theorem collapse_edge_e2  :
    (collapse N e).edgeMap (.inr true) = some e := rfl

/-- 原始constructorのcollapse_face_old評価。 -/
@[simp] theorem collapse_face_old (f : N.nerve.FaceComponent) :
    (collapse N e).faceMap (.inl f) = some f := rfl

/-- 原始constructorのcollapse_face_new評価。 -/
@[simp] theorem collapse_face_new  :
    (collapse N e).faceMap (.inr PUnit.unit) = none := rfl


end TriangleAddition
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
