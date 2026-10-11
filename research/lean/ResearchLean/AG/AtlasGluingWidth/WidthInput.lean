import ResearchLean.AG.AtlasGluingWidth.LawDefect
import Mathlib.Data.ZMod.Basic
import Formal.Util.AssertStandardAxioms

/-! # 全幅証人の原始セル表

固定設計のZMod n上の交互閉路とa₀だけを除いたpathを構成する。
台・incidence・readingから選択式を導く。期待rankや診断を入力に含めない。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance Cohomology FaceRelationSubdivision
variable (n : ℕ) [NeZero n]

/-- 指定有限概念集合。 -/
abbrev Concept := ZMod n
/-- 指定Source。同じ概念の二つの発生点を持つ。 -/
abbrev Source := Concept n × Bool
/-- 粗readingは概念への射影。 -/
abbrev coarseReading : Reading (Source n) where
  Target := Concept n
  read := Prod.fst
  surjective c := ⟨(c, false), rfl⟩
/-- 細readingは同じSourceの恒等。 -/
abbrev fineReading : Reading (Source n) where
  Target := Source n
  read := id
  surjective := Function.surjective_id
omit [NeZero n] in
/-- 指定reading順序。 -/
theorem coarser : (coarseReading n).CoarserThan (fineReading n) :=
  fun _ _ h => congrArg Prod.fst h
omit [NeZero n] in
/-- 生成因子は指定射影そのもの。 -/
theorem factor : comparisonFactor (coarseReading n) (fineReading n) (coarser n) =
    Prod.fst := by
  symm
  exact comparisonFactor_unique (coarseReading n) (fineReading n) (coarser n)
    Prod.fst (fun _ => rfl)

/-- falseは閉路、trueはa₀だけを除く。辺の名前はaᵢ=(i,false),bᵢ=(i,true)。 -/
abbrev Edge (cut : Bool) := {e : Concept n × Bool // cut = true → e ≠ (0, false)}
/-- 同じchart名vᵢ=(i,false),wᵢ=(i,true)。 -/
abbrev Chart := Concept n × Bool
/-- 指定有向辺の左端。 -/
def left (e : Concept n × Bool) : Chart n :=
  if e.2 then (e.1, true) else (e.1, false)
/-- 指定有向辺の右端。 -/
def right (e : Concept n × Bool) : Chart n :=
  if e.2 then (e.1 + 1, false) else (e.1, true)
/-- 粗nerveは一点、辺・面なし。 -/
abbrev coarseNerve : CoverNerve where
  Chart := Unit
  EdgeComponent := Empty
  FaceComponent := Empty
  edgeLeft := Empty.elim
  edgeRight := Empty.elim
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := Empty.elim
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds := fun e => e.elim
  faceTripleOverlapComponent_holds := fun f => f.elim
/-- 細nerveは指定交互閉路、cutの場合a₀を除いたpath。 -/
abbrev fineNerve (cut : Bool) : CoverNerve where
  Chart := Chart n
  EdgeComponent := Edge n cut
  FaceComponent := Empty
  edgeLeft e := left n e.1
  edgeRight e := right n e.1
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds := fun f => f.elim
/-- 指定chart台。vはsingleton、wは隣接二概念、Bool座標は全て。 -/
def support (v : Chart n) : Set (Source n) :=
  {s | s.1 = v.1 ∨ (v.2 = true ∧ s.1 = v.1 + 1)}
/-- 粗支持nerveの台は全概念集合。 -/
abbrev coarse : TargetSupportedNerve (coarseReading n) where
  nerve := coarseNerve
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨0, Set.mem_univ _⟩
  faceEdge0_left := fun f => f.elim
  faceEdge0_right := fun f => f.elim
  faceEdge1_right := fun f => f.elim
/-- 細支持nerveは指定台と空面から構成する。 -/
abbrev fine (cut : Bool) : TargetSupportedNerve (fineReading n) where
  nerve := fineNerve n cut
  chartSupport := support n
  chartSupport_nonempty v := ⟨(v.1, false), Or.inl rfl⟩
  faceEdge0_left := fun f => f.elim
  faceEdge0_right := fun f => f.elim
  faceEdge1_right := fun f => f.elim
/-- 旧hereditary条件を満たす指定比較。 -/
def hereditary (cut : Bool) : TargetSupportedNerveMorphism
    (coarseReading n) (fineReading n) (coarser n) (coarse n) (fine n cut) where
  chartMap _ := ()
  edgeMap _ := none
  faceMap := Empty.elim
  edge_some_left := by intros _ e; exact e.elim
  edge_some_right := by intros _ e; exact e.elim
  edge_none_fiber := by intros; rfl
  face_some_edge0 := fun f => f.elim
  face_some_edge1 := fun f => f.elim
  face_some_edge2 := fun f => f.elim
  face_none_edge0 := fun f => f.elim
  face_none_edge1 := fun f => f.elim
  face_none_edge2 := fun f => f.elim
  chartSupport_compatible _ _ _ := Set.mem_univ _
/-- G-134の原始incidence比較への同じ埋め込み。 -/
def comparison (cut : Bool) := IncidenceSupportedComparison.ofHereditary (hereditary n cut)
/-- 細選択は指定X×Bool。 -/
def region (X : Set (Concept n)) : Set (Source n) := Prod.fst ⁻¹' X
omit [NeZero n] in
/-- 因子から生成される逆像と指定細選択の一致。 -/
theorem factor_region (X : Set (Concept n)) :
    comparisonFactor (coarseReading n) (fineReading n) (coarser n) ⁻¹' X = region n X := by
  rw [factor]; rfl
/-- chartの選択式は原始台から出る。 -/
theorem chart_selected (cut : Bool) (X : Set (Concept n)) (v : Chart n) :
    (CellSelection.region (fine n cut) (region n X)).chart v ↔
      v.1 ∈ X ∨ (v.2 = true ∧ v.1 + 1 ∈ X) := by
  constructor
  · rintro ⟨s, h | ⟨hb, h⟩, hx⟩
    · exact Or.inl (h ▸ hx)
    · exact Or.inr ⟨hb, h ▸ hx⟩
  · rintro (hx | ⟨hb, hx⟩)
    · exact ⟨(v.1, false), Or.inl rfl, hx⟩
    · exact ⟨(v.1 + 1, false), Or.inr ⟨hb, rfl⟩, hx⟩
/-- K1辺台は端点交差から指定singletonになる。n=2でも成立。 -/
theorem edge_support (cut : Bool) (e : Edge n cut) (s : Source n) :
    s ∈ (fine n cut).edgeSupport e ↔
      s.1 = if e.1.2 then e.1.1 + 1 else e.1.1 := by
  rcases e with ⟨⟨i, b⟩, he⟩
  cases b <;> simp [TargetSupportedNerve.edgeSupport, left, right, support] <;> tauto
/-- 全細辺の選択式。plusでは型自身がa₀を除く。 -/
theorem edge_selected (cut : Bool) (X : Set (Concept n)) (e : Edge n cut) :
    (CellSelection.region (fine n cut) (region n X)).edge e ↔
      (if e.1.2 then e.1.1 + 1 else e.1.1) ∈ X := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact (edge_support n cut e s).mp hs ▸ hx
  · intro hx
    exact ⟨((if e.1.2 then e.1.1 + 1 else e.1.1), false),
      (edge_support n cut e _).mpr rfl, hx⟩

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
