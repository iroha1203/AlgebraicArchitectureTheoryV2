import ResearchLean.AG.FaceRelationSubdivision.ReadingPullback
import ResearchLean.AG.FaceRelationSubdivision.TriangleGeometry
import ResearchLean.AG.AtlasDefectComposition.FullSupportIncidence
import Mathlib.Data.Fin.VecNotation
import Formal.Util.AssertStandardAxioms
/-!
# W1 の原始 paired セル表

## Implementation notes

Source は Bool×Bool、粗 reading は第一射影、細 reading は恒等。
細側は同じ reading 逆像表に三角形を追加し、minus では面型だけを空にする。
行列・rank・同型を入力する方式を採らず、表と台から生成する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessOne
open CanonicalResolution ResolutionInvariance Cohomology TwoPhase AtlasDefectComposition
/-- 指定二座標 Source。 -/
abbrev Source := Bool × Bool
/-- 第一射影 reading。 -/
abbrev qc : Reading Source where
  Target := Bool
  read := Prod.fst
  surjective a := ⟨(a,false),rfl⟩
/-- 恒等 reading。 -/
abbrev qf : Reading Source where
  Target := Source
  read := id
  surjective := Function.surjective_id
/-- 一つの第一射影 Law。 -/
def laws : FiniteLawFamily Source where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Bool
  valueDecidableEq _ := inferInstance
  eval _ := Prod.fst
/-- 粗 adequacy の原始証明。 -/
theorem coarseAdequate : laws.Adequate qc := fun _ => ⟨id,fun _ => rfl⟩
/-- 細 adequacy の原始証明。 -/
theorem fineAdequate : laws.Adequate qf := fun _ => ⟨Prod.fst,fun _ => rfl⟩
/-- 第一射影は粗細順序を与える。 -/
theorem coarser : qc.CoarserThan qf := fun _ _ h => congrArg Prod.fst h
/-- 第二座標を失うので逆順序はない。 -/
theorem not_reverse : ¬ qf.CoarserThan qc := by
  intro h
  have hx := h (x := (false,false)) (y := (false,true)) rfl
  exact Bool.false_ne_true (congrArg Prod.snd hx)
/-- 全射から得る実因子の第一射影式。 -/
@[simp] theorem factor_apply (t : Source) : comparisonFactor qc qf coarser t = t.1 :=
  comparisonFactor_commutes qc qf coarser t
/-- 同じ Law は非定数である。 -/
theorem law_nonconstant : laws.eval () (false,false) ≠ laws.eval () (true,false) := Bool.false_ne_true
/-- 原始 Source 発生ラベル。 -/
def label (a : Bool) : LawValueLabel laws := LawValueLabel.ofSource laws () (a,false)
/-- 二ラベルの分離。 -/
theorem labels_distinct : label false ≠ label true := by
  intro h
  exact Bool.false_ne_true (congrArg (fun l : LawValueLabel laws => l.value) h)
/-- 全発生ラベルの二値表示。 -/
def labelEquiv : LawValueLabel laws ≃ Bool where
  toFun l := l.value
  invFun := label
  left_inv l := by cases l with | mk l v h => cases l; apply LawValueLabel.ext <;> rfl
  right_inv _ := rfl
/-- ラベル逆表示の公開式。 -/
@[simp] theorem labelEquiv_symm (a : Bool) : labelEquiv.symm a = label a := rfl
/-- ラベル順表示の公開式。 -/
@[simp] theorem labelEquiv_label (a : Bool) : labelEquiv (label a) = a := rfl
/-- v,w、辺 e1,k、面なしの原始表。 -/
abbrev nerve : CoverNerve where
  Chart := Fin 2
  EdgeComponent := Fin 2
  FaceComponent := Empty
  edgeLeft _ := 0
  edgeRight := ![1,0]
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds := fun f => nomatch f
/-- 全 chart 台から粗入力を生成する。 -/
abbrev N : TargetSupportedNerve qc where
  nerve := nerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false,Set.mem_univ _⟩
  faceEdge0_left := fun f => nomatch f
  faceEdge0_right := fun f => nomatch f
  faceEdge1_right := fun f => nomatch f
/-- 同じセル表の細 reading 逆像。 -/
abbrev pulled := readingPullback N coarser
/-- e1 を三角形にする面あり入力。 -/
abbrev plus := TriangleAddition.supported pulled (0 : Fin 2)
/-- plus の面だけを空にする原始 nerve。 -/
abbrev minusNerve : CoverNerve where
  Chart := plus.nerve.Chart
  EdgeComponent := plus.nerve.EdgeComponent
  FaceComponent := Empty
  edgeLeft := plus.nerve.edgeLeft
  edgeRight := plus.nerve.edgeRight
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := plus.nerve.edgeOverlapComponent
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds := plus.nerve.edgeOverlapComponent_holds
  faceTripleOverlapComponent_holds := fun f => nomatch f
/-- 面 f だけを除いた paired 入力。 -/
abbrev minus : TargetSupportedNerve qf where
  nerve := minusNerve
  chartFintype := plus.chartFintype
  edgeFintype := plus.edgeFintype
  faceFintype := inferInstance
  chartSupport := plus.chartSupport
  chartSupport_nonempty := plus.chartSupport_nonempty
  faceEdge0_left := fun f => nomatch f
  faceEdge0_right := fun f => nomatch f
  faceEdge1_right := fun f => nomatch f
/-- paired 入力の台・端点を厳密に共有する。 -/
theorem paired_table : minus.chartSupport = plus.chartSupport ∧
    minus.nerve.edgeLeft = plus.nerve.edgeLeft ∧ minus.nerve.edgeRight = plus.nerve.edgeRight := ⟨rfl,rfl,rfl⟩
/-- 粗 chart 全台。 -/
theorem chart_full (v : N.nerve.Chart) : N.chartSupport v = Set.univ := rfl
/-- plus chart 全台は逆像から生成する。 -/
theorem plus_chart_full (v : plus.nerve.Chart) : plus.chartSupport v = Set.univ := by
  cases v with
  | inl v => rw [TriangleAddition.chartSupport_old,readingPullback_chartSupport]; rfl
  | inr v => cases v; rw [TriangleAddition.chartSupport_new,readingPullback_chartSupport]; rfl
/-- minus の同じ全台。 -/
theorem minus_chart_full (v : minus.nerve.Chart) : minus.chartSupport v = Set.univ := plus_chart_full v
/-- 粗 K1 辺台。 -/
theorem edge_full : ∀ x, N.edgeSupport x = Set.univ := fullSupport_edge N chart_full
/-- 粗 K1 面台。 -/
theorem face_full : ∀ x, N.faceSupport x = Set.univ := fullSupport_face N chart_full
/-- plus K1 辺台。 -/
theorem plus_edge_full : ∀ x, plus.edgeSupport x = Set.univ := fullSupport_edge plus plus_chart_full
/-- plus K1 面台。 -/
theorem plus_face_full : ∀ x, plus.faceSupport x = Set.univ := fullSupport_face plus plus_chart_full
/-- minus K1 辺台。 -/
theorem minus_edge_full : ∀ x, minus.edgeSupport x = Set.univ := fullSupport_edge minus minus_chart_full
/-- minus K1 面台。 -/
theorem minus_face_full : ∀ x, minus.faceSupport x = Set.univ := fullSupport_face minus minus_chart_full
/-- 粗微分の端点評価。 -/
@[simp] theorem d0_apply (c : Fin 2 → ℚ) (e : Fin 2) :
    (namedComplex N).d0 c e = c (![1,0] e) - c 0 := rfl
/-- plus の旧辺微分。 -/
@[simp] theorem plus_d0_old (c : plus.nerve.Chart → ℚ) (e : Fin 2) :
    (namedComplex plus).d0 c (.inl e) = c (.inl ((![1,0] e : Fin 2))) - c (.inl (0 : Fin 2)) := by
  rw [namedComplex_d0_apply,TriangleAddition.edgeLeft_old,TriangleAddition.edgeRight_old]; rfl
/-- plus の c 微分。 -/
@[simp] theorem plus_d0_c (c : plus.nerve.Chart → ℚ) :
    (namedComplex plus).d0 c (.inr false) = c (.inr PUnit.unit) - c (.inl (0 : Fin 2)) := by
  rw [namedComplex_d0_apply,TriangleAddition.edgeLeft_c,TriangleAddition.edgeRight_c]; rfl
/-- plus の e2 微分。 -/
@[simp] theorem plus_d0_e2 (c : plus.nerve.Chart → ℚ) :
    (namedComplex plus).d0 c (.inr true) = c (.inl (1 : Fin 2)) - c (.inr PUnit.unit) := by
  rw [namedComplex_d0_apply,TriangleAddition.edgeLeft_e2,TriangleAddition.edgeRight_e2]; rfl
/-- plus の f 微分は指定三辺の符号和。 -/
@[simp] theorem plus_d1_apply (z : plus.nerve.EdgeComponent → ℚ) (f : plus.nerve.FaceComponent) :
    (namedComplex plus).d1 z f = z (.inr false) - z (.inl (0 : Fin 2)) + z (.inr true) := by
  cases f with
  | inl f => exact Empty.elim f
  | inr f => cases f; rw [namedComplex_d1_apply,TriangleAddition.faceEdge0_new,
      TriangleAddition.faceEdge1_new,TriangleAddition.faceEdge2_new]
/-- minus と plus の次数0微分は同じ。 -/
@[simp] theorem minus_d0_eq : (namedComplex minus).d0 = (namedComplex plus).d0 := rfl
/-- minus の旧辺微分を同じ原始端点で読む。 -/
@[simp] theorem minus_d0_old (c : minus.nerve.Chart → ℚ) (e : Fin 2) :
    (namedComplex minus).d0 c (.inl e)=c (.inl (![1,0] e : Fin 2))-c (.inl (0 : Fin 2)) := rfl
/-- minus の c 微分を同じ原始端点で読む。 -/
@[simp] theorem minus_d0_c (c : minus.nerve.Chart → ℚ) :
    (namedComplex minus).d0 c (.inr false)=c (.inr PUnit.unit)-c (.inl (0 : Fin 2)) := rfl
/-- minus の e2 微分を同じ原始端点で読む。 -/
@[simp] theorem minus_d0_e2 (c : minus.nerve.Chart → ℚ) :
    (namedComplex minus).d0 c (.inr true)=c (.inl (1 : Fin 2))-c (.inr PUnit.unit) := rfl
/-- k は変更部分の v に接続する。 -/
theorem loop_attached : N.nerve.edgeLeft 1 = N.nerve.edgeRight 1 ∧
    plus.nerve.edgeLeft (.inl (1 : Fin 2)) = plus.nerve.edgeLeft (.inr false) := ⟨rfl,rfl⟩
/-- 全頂点を v から e1 または c で結ぶ具体道。 -/
theorem every_vertex_connected (v : plus.nerve.Chart) : v = .inl (0 : Fin 2) ∨
    ∃ e : plus.nerve.EdgeComponent, plus.nerve.edgeLeft e = .inl (0 : Fin 2) ∧ plus.nerve.edgeRight e = v := by
  cases v with
  | inl v => fin_cases v; exact Or.inl rfl; exact Or.inr ⟨.inl (0 : Fin 2),rfl,rfl⟩
  | inr v => cases v; exact Or.inr ⟨.inr false,rfl,rfl⟩
end AAT.AG.FaceRelationSubdivision.WitnessOne
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessOne
