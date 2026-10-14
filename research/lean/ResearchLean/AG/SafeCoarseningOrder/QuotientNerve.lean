import ResearchLean.AG.SafeCoarseningOrder.PrimitiveInput
import ResearchLean.AG.FaceRelationSubdivision.IncidenceComparison

/-!
# G-137 の全商 nerve と原始比較

T0 の任意の同値関係対から、chart 台の合併の像、K1 交差、内部辺の縮約、
有向平行辺の併合を同じ式で生成する。既存の hereditary 比較に接続する。

## Implementation notes

商の名前は `Quotient` を用いる。辺の生成証拠は Prop であり多重辺を作らない。
商の K1 台は商 chart 台から再計算し、元辺台の像との一致を要求しない。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance Cohomology FaceRelationSubdivision
variable {S T V : Type}
namespace PrimitiveInput
variable (M : PrimitiveInput S T V) (R : Coarsening T V)

/-- 商 target への全射 reading。 -/
def quotientReading : Reading S where
  Target := Quotient R.1
  read s := Quotient.mk R.1 (M.read s)
  surjective := by
    intro x
    induction x using Quotient.inductionOn with
    | _ t =>
      obtain ⟨s, rfl⟩ := M.read_surjective t
      exact ⟨s, rfl⟩

/-- 商 chart fiber の台の合併の像。 -/
def quotientSupport (b : Quotient R.2) : Set (Quotient R.1) :=
  {x | ∃ v t, Quotient.mk R.2 v = b ∧ t ∈ M.support v ∧ Quotient.mk R.1 t = x}

/-- quotientSupport の生成条件を公開する。 -/
@[simp] theorem mem_quotientSupport (b : Quotient R.2) (x : Quotient R.1) :
    x ∈ M.quotientSupport R b ↔
      ∃ v t, Quotient.mk R.2 v = b ∧ t ∈ M.support v ∧ Quotient.mk R.1 t = x :=
  Iff.rfl

/-- 原始台からの商台所属。 -/
theorem quotientSupport_mk (v : V) {t : T} (ht : t ∈ M.support v) :
    Quotient.mk R.1 t ∈ M.quotientSupport R (Quotient.mk R.2 v) :=
  ⟨v, t, rfl, ht, rfl⟩

/-- 全商 chart 台の非空性。原始台から生成する。 -/
theorem quotientSupport_nonempty (b : Quotient R.2) :
    (M.quotientSupport R b).Nonempty := by
  induction b using Quotient.inductionOn with
  | _ v =>
    obtain ⟨t, ht⟩ := M.support_nonempty v
    exact ⟨Quotient.mk R.1 t, M.quotientSupport_mk R v ht⟩

/-- 異なる商 chart 間に残る有向辺関係。逆向きは別順序対。 -/
def quotientEdge (b c : Quotient R.2) : Prop :=
  b ≠ c ∧ ∃ v w, M.edge v w ∧ Quotient.mk R.2 v = b ∧ Quotient.mk R.2 w = c

/-- quotientEdge の全生成条件。 -/
@[simp] theorem quotientEdge_iff (b c : Quotient R.2) :
    M.quotientEdge R b c ↔ b ≠ c ∧
      ∃ v w, M.edge v w ∧ Quotient.mk R.2 v = b ∧ Quotient.mk R.2 w = c := Iff.rfl

/-- 商の有向辺セル。存在証拠の違いは同一セル。 -/
abbrev QuotientEdge := {e : Quotient R.2 × Quotient R.2 // M.quotientEdge R e.1 e.2}

/-- 商 nerve のセルと incidence は原始表だけから生成する。 -/
def quotientNerve : CoverNerve where
  Chart := Quotient R.2
  EdgeComponent := M.QuotientEdge R
  FaceComponent := Empty
  edgeLeft e := e.1.1
  edgeRight e := e.1.2
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds f := f.elim

variable [Fintype V]

/-- 全粗化を既存 TargetSupportedNerve に接続する。 -/
def quotientSupported : TargetSupportedNerve (M.quotientReading R) where
  nerve := M.quotientNerve R
  chartFintype := by classical change Fintype (Quotient R.2); infer_instance
  edgeFintype := by classical change Fintype (M.QuotientEdge R); infer_instance
  faceFintype := by change Fintype Empty; infer_instance
  chartSupport := M.quotientSupport R
  chartSupport_nonempty := M.quotientSupport_nonempty R
  faceEdge0_left f := f.elim
  faceEdge0_right f := f.elim
  faceEdge1_right f := f.elim

/-- 商 K1 辺台は商 chart 台の交差である。 -/
@[simp] theorem mem_quotient_edgeSupport (e : M.QuotientEdge R) (x : Quotient R.1) :
    x ∈ (M.quotientSupported R).edgeSupport e ↔
      x ∈ M.quotientSupport R e.1.1 ∧ x ∈ M.quotientSupport R e.1.2 := Iff.rfl

omit [Fintype V] in
/-- 商 reading が fine reading に対して粗いことを生成する。 -/
theorem quotient_coarser : (M.quotientReading R).CoarserThan M.reading := by
  intro x y h
  exact congrArg (Quotient.mk R.1) h

omit [Fintype V] in
/-- 既存の canonical factor は原始 target 商写像に等しい。 -/
theorem quotient_factor :
    comparisonFactor (M.quotientReading R) M.reading (M.quotient_coarser R) =
      Quotient.mk R.1 := by
  symm
  apply comparisonFactor_unique (M.quotientReading R) M.reading (M.quotient_coarser R)
  intro s
  rfl

/-- 原始辺の部分像。chart fiber 内では none、それ以外では有向商辺。 -/
def quotientEdgeMap (e : M.Edge) : Option (M.QuotientEdge R) := by
  classical
  exact if h : Quotient.mk R.2 e.1.1 = Quotient.mk R.2 e.1.2 then none else
    some ⟨(Quotient.mk R.2 e.1.1, Quotient.mk R.2 e.1.2),
      h, e.1.1, e.1.2, e.2, rfl, rfl⟩

omit [Fintype V] in
/-- 内部辺縮約の必要十分条件。 -/
@[simp] theorem quotientEdgeMap_eq_none (e : M.Edge) :
    M.quotientEdgeMap R e = none ↔ R.2 e.1.1 e.1.2 := by
  classical
  simp [quotientEdgeMap, Quotient.eq]

omit [Fintype V] in
/-- 残存辺の両端評価。 -/
theorem quotientEdgeMap_some_endpoints (e : M.Edge) (f : M.QuotientEdge R)
    (h : M.quotientEdgeMap R e = some f) :
    Quotient.mk R.2 e.1.1 = f.1.1 ∧ Quotient.mk R.2 e.1.2 = f.1.2 := by
  classical
  unfold quotientEdgeMap at h
  split_ifs at h with he
  cases Option.some.inj h
  exact ⟨rfl, rfl⟩

omit [Fintype V] in
/-- 残存辺は両端で一意に定まる。同方向平行辺併合の公開規則。 -/
theorem quotientEdgeMap_eq_some (e : M.Edge) (f : M.QuotientEdge R) :
    M.quotientEdgeMap R e = some f ↔
      Quotient.mk R.2 e.1.1 = f.1.1 ∧ Quotient.mk R.2 e.1.2 = f.1.2 := by
  classical
  constructor
  · exact M.quotientEdgeMap_some_endpoints R e f
  · rintro ⟨hl, hr⟩
    have hn : Quotient.mk R.2 e.1.1 ≠ Quotient.mk R.2 e.1.2 := by
      rw [hl, hr]
      exact f.2.1
    simp only [quotientEdgeMap, dif_neg hn]
    congr 1
    apply Subtype.ext
    exact Prod.ext hl hr

/-- 全Rの原始比較。比較条件を全て原始表から放電する。 -/
def quotientMorphism : TargetSupportedNerveMorphism
    (M.quotientReading R) M.reading (M.quotient_coarser R)
    (M.quotientSupported R) M.supported where
  chartMap := Quotient.mk R.2
  edgeMap := M.quotientEdgeMap R
  faceMap := Empty.elim
  edge_some_left e f h := (M.quotientEdgeMap_some_endpoints R e f h).1
  edge_some_right e f h := (M.quotientEdgeMap_some_endpoints R e f h).2
  edge_none_fiber e h := Quotient.sound ((M.quotientEdgeMap_eq_none R e).mp h)
  face_some_edge0 f := f.elim
  face_some_edge1 f := f.elim
  face_some_edge2 f := f.elim
  face_none_edge0 f := f.elim
  face_none_edge1 f := f.elim
  face_none_edge2 f := f.elim
  chartSupport_compatible v t ht := by
    rw [M.quotient_factor R]
    exact M.quotientSupport_mk R v ht

/-- 同じ原始比較をG-134の incidence supported comparison に埋め込む。 -/
def quotientComparison := IncidenceSupportedComparison.ofHereditary (M.quotientMorphism R)

end PrimitiveInput
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
