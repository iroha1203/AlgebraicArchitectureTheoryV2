import ResearchLean.AG.SafeCoarseningOrder.SimpleEdgeHomology
import ResearchLean.AG.SafeCoarseningOrder.PrimitiveExamples
import ResearchLean.AG.SafeCoarseningOrder.IteratedQuotient
import Mathlib.Tactic.FinCases

/-!
# G-137 の実安全性の成立例と不成立例

同じSafeの定義にW0と全台の有向三角形を通す。三角形の全関係商は実H¹の余核を持つ。
非零類は指定一辺cochainのperiodで検証し、H¹次元の比較だけで判定しない。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase

/-- W0の原始辺は指定の一辺だけである。 -/
theorem w0_edges_subsingleton : Subsingleton w0.Edge := by
  constructor
  rintro ⟨⟨v,w⟩,hv,hw⟩ ⟨⟨v',w'⟩,hv',hw'⟩
  apply Subtype.ext
  exact Prod.ext (hv.trans hv'.symm) (hw.trans hw'.symm)

/-- W0の全粗化は全Aの同じ実H¹比較を保存する。 -/
theorem w0_safe (R : Coarsening Unit Bool) : w0.Safe R := by
  letI := w0_edges_subsingleton
  exact safe_of_single_edge w0 R

namespace Triangle

/-- 有向三角形。S=T=Unit、全台、0→1→2→0、空面。 -/
def input : PrimitiveInput Unit Unit (Fin 3) where
  read := id
  read_surjective := Function.surjective_id
  edge v w := w = v+1
  edge_ne v w h := by subst w; fin_cases v <;> decide
  support _ := Set.univ
  support_nonempty _ := Set.univ_nonempty

/-- 三角形の全支持複体。元K1選択から作る。 -/
abbrev fullComplex := input.supported.targetSubsetComplex (Set.univ : Set Unit)

/-- 全台で選択された元chart。 -/
def fullChart (v : Fin 3) : input.supported.ChartInTargetSubset (Set.univ : Set Unit) :=
  ⟨v, (), True.intro, True.intro⟩

/-- 全台で選択された元有向辺。 -/
def fullEdge (v : Fin 3) : input.supported.EdgeInTargetSubset (Set.univ : Set Unit) :=
  ⟨⟨(v,v+1),rfl⟩, (), ⟨True.intro,True.intro⟩, True.intro⟩

/-- 指定一巡periodは三つの元辺の和。 -/
def period : fullComplex.C1 →ₗ[ℚ] ℚ where
  toFun z := z (fullEdge 0) + z (fullEdge 1) + z (fullEdge 2)
  map_add' x y := by
    change (x (fullEdge 0)+y (fullEdge 0)) + (x (fullEdge 1)+y (fullEdge 1)) +
      (x (fullEdge 2)+y (fullEdge 2)) = _
    ring
  map_smul' a x := by
    change a*x (fullEdge 0) + a*x (fullEdge 1) + a*x (fullEdge 2) =
      a*(x (fullEdge 0)+x (fullEdge 1)+x (fullEdge 2))
    ring

/-- 原始d0の一巡和はtelescopingで零。 -/
theorem period_boundary (x : fullComplex.C0) : period (fullComplex.d0 x) = 0 := by
  change (x (fullChart 1)-x (fullChart 0)) +
    (x (fullChart 2)-x (fullChart 1)) + (x (fullChart 0)-x (fullChart 2)) = 0
  ring

/-- 面が空なので、指定全辺cochainは同じ実cocycleに入る。 -/
def cycle (z : fullComplex.C1) : LinearMap.ker fullComplex.d1 :=
  ⟨z, by funext f; exact f.1.elim⟩

/-- 指定cochainを既存の実H¹商に入れる。 -/
def classOf (z : fullComplex.C1) : fullComplex.H1 :=
  (LinearMap.range fullComplex.boundaryToCycles).mkQ (cycle z)

/-- 同じperiodは原始d0で零なので、実H¹商上の汎関数を生成する。 -/
def periodH1 : fullComplex.H1 →ₗ[ℚ] ℚ :=
  (LinearMap.range fullComplex.boundaryToCycles).liftQ
    (period.comp (LinearMap.ker fullComplex.d1).subtype) (by
      rintro z ⟨x,rfl⟩
      change period (fullComplex.d0 x) = 0
      exact period_boundary x)

/-- 原始代表元から商へのperiod評価を同定。 -/
@[simp] theorem periodH1_classOf (z : fullComplex.C1) : periodH1 (classOf z) = period z := rfl

/-- 0→1だけが1で、残りは0という原始cochain。 -/
def spike : fullComplex.C1 := fun e => if e.1.1.1 = 0 then 1 else 0

/-- 指定元cochainのperiodは1。 -/
theorem period_spike : period spike = 1 := by decide +kernel

/-- 指定period1の同じ実H¹類は非零。 -/
theorem spike_class_nonzero : classOf spike ≠ 0 := by
  intro hz
  have hm : cycle spike ∈ LinearMap.range fullComplex.boundaryToCycles :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨x,hx⟩ := hm
  have he : fullComplex.d0 x = spike := congrArg Subtype.val hx
  have hp := congrArg period he
  rw [period_boundary,period_spike] at hp
  exact zero_ne_one hp

end Triangle

/-- 全関係chart商は全原始辺を内部化するため、商辺型は空。 -/
theorem top_edges_empty {S T V : Type} (M : PrimitiveInput S T V) :
    IsEmpty (M.QuotientEdge (⊤ : Coarsening T V)) := by
  constructor
  intro e
  apply e.2.1
  exact Quotient.inductionOn₂ e.1.1 e.1.2 (fun _ _ => Quotient.sound True.intro)

/-- 全関係商の全A実H¹は零。 -/
theorem top_h1_subsingleton {S T V : Type} [Fintype V] (M : PrimitiveInput S T V)
    (A : Set (Quotient (⊤ : Setoid T))) :
    Subsingleton ((M.quotientSupported (⊤ : Coarsening T V)).targetSubsetComplex A).H1 := by
  letI := top_edges_empty M
  letI : IsEmpty (M.quotientSupported (⊤ : Coarsening T V)).nerve.EdgeComponent :=
    inferInstanceAs (IsEmpty (M.QuotientEdge (⊤ : Coarsening T V)))
  letI : Subsingleton ((M.quotientSupported (⊤ : Coarsening T V)).targetSubsetComplex A).C1 :=
    inferInstanceAs (Subsingleton
      ((M.quotientSupported (⊤ : Coarsening T V)).EdgeInTargetSubset A → ℚ))
  infer_instance

/-- 三角形の全関係商比較は非零fine類に全射でなく、同じSafeを満たさない。 -/
theorem triangle_top_not_safe : ¬ Triangle.input.Safe (⊤ : Coarsening Unit (Fin 3)) := by
  intro hs
  letI := top_h1_subsingleton Triangle.input Set.univ
  obtain ⟨x,hx⟩ := (hs Set.univ).2 (Triangle.classOf Triangle.spike)
  have he : x = 0 := Subsingleton.elim _ _
  rw [he, map_zero] at hx
  exact Triangle.spike_class_nonzero hx.symm

/-- 同じ有限集合と台で辺だけを空にしたT0表。原始同型条件の不成立例に使う。 -/
def triangleEdgeless : PrimitiveInput Unit Unit (Fin 3) :=
  { Triangle.input with edge := fun _ _ => False, edge_ne := fun _ _ h => h.elim }

/-- 原始有向辺を保存する同型は三角形を同じ台の辺なし表へ送れない。 -/
theorem triangle_not_iso_edgeless : ¬ Nonempty (PrimitiveIso Triangle.input triangleEdgeless) := by
  rintro ⟨a⟩
  exact (a.edge_iff 0 1).mp rfl

/-- 三角形の恒等商では原始同型条件を入力から構成できる。 -/
theorem triangle_bot_iso : Nonempty (PrimitiveIso Triangle.input
    (Triangle.input.quotientInput (⊥ : Coarsening Unit (Fin 3)))) :=
  ⟨Triangle.input.botIso⟩

end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
