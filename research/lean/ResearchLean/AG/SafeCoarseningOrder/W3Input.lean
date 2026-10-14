import ResearchLean.AG.SafeCoarseningOrder.QuotientNerve
import ResearchLean.AG.AtlasGluingWidth.WidthInput

/-! # W3 の指定原始入力と元商写像

G-136のn=2の元セル・台・readingを保持し、T0有向単純表と指定商を構成する。

## Implementation notes

元G136辺名から順序対を生成し、左端による全単射を証明する。商名は元mkと可換なEquivで同定し、同次元nerveで置換しない。
-/
set_option maxHeartbeats 1200000
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W3
open CanonicalResolution ResolutionInvariance TwoPhase AtlasGluingWidth AtlasDefectComposition

/-- W3指定Source/Target。各ZMod2概念にBool二発生点を保持する。 -/
abbrev Point := Width.Source 2
/-- W3の旧chart名vᵢ/wᵢを保持する型。 -/
abbrev Chart := Width.Chart 2
/-- 旧辺名はその左端chart名そのものなので、端点対の符号化は単射。 -/
@[simp] theorem old_left (v : Chart) : Width.left 2 v = v := by
  rcases v with ⟨i,b⟩; cases b <;> rfl
/-- W3原始表。falseは全閉路、trueはa₀だけを除く。 -/
def input (cut : Bool) : PrimitiveInput Point Point Chart where
  read := id
  read_surjective := Function.surjective_id
  edge v w := (cut = true → v ≠ (0,false)) ∧ w = Width.right 2 v
  edge_ne v w h := by
    rcases h with ⟨_,rfl⟩
    rcases v with ⟨i,b⟩
    cases b <;> simp [Width.right]
  support := Width.support 2
  support_nonempty v := ⟨(v.1,false),Or.inl rfl⟩
/-- 指定有向辺表の公開特徴づけ。plusではa₀だけを除く。 -/
@[simp] theorem input_edge_iff (cut : Bool) (v w : Chart) :
    (input cut).edge v w ↔ (cut = true → v ≠ (0,false)) ∧ w = Width.right 2 v := Iff.rfl
/-- 新原始chart台は指定旧fine台と同じ元集合。 -/
@[simp] theorem input_support (cut : Bool) (v : Chart) :
    (input cut).support v = (Width.fine 2 cut).chartSupport v := rfl
/-- 旧辺名と新有向端点対の全単射。左端が元辺名なので重複セルを生まない。 -/
def edgeEquiv (cut : Bool) : Width.Edge 2 cut ≃ (input cut).Edge where
  toFun e := ⟨(e.1,Width.right 2 e.1),e.2,rfl⟩
  invFun e := ⟨e.1.1,e.2.1⟩
  left_inv e := rfl
  right_inv e := by
    apply Subtype.ext
    exact Prod.ext rfl e.2.2.symm
/-- 元辺の左端を旧chartの同じ名前で保持する。 -/
@[simp] theorem edgeEquiv_left (cut : Bool) (e : Width.Edge 2 cut) :
    (edgeEquiv cut e).1.1 = Width.left 2 e.1 := (old_left e.1).symm
/-- 元辺の右端も旧incidenceそのものである。 -/
@[simp] theorem edgeEquiv_right (cut : Bool) (e : Width.Edge 2 cut) :
    (edgeEquiv cut e).1.2 = Width.right 2 e.1 := rfl
/-- E W3指定R。targetはfstの核、chartは全関係。 -/
def coarsening : Coarsening Point Chart := (Setoid.ker Prod.fst,⊤)
/-- 指定target関係の基本特徴づけ。元fst核そのもの。 -/
theorem coarsening_target_iff (p q : Point) : coarsening.1 p q ↔ p.1 = q.1 := Iff.rfl
/-- 指定chart関係の基本API。全元chart対を同じ商へ縮約する。 -/
theorem coarsening_chart_rel (v w : Chart) : coarsening.2 v w := True.intro
/-- 指定商targetとZMod2の全単射。元fstの全射性から生成する。 -/
def targetEquiv : Quotient coarsening.1 ≃ Width.Concept 2 :=
  (Setoid.quotientKerEquivOfSurjective (f := Prod.fst) (fun i => ⟨(i,false),rfl⟩))
/-- 元target商写像は同定後に指定fst射影と可換。 -/
@[simp] theorem targetEquiv_mk (p : Point) : targetEquiv (Quotient.mk coarsening.1 p) = p.1 := rfl
/-- 指定商chartをUnitへ同定する。元全関係の商を使う。 -/
def chartEquiv : Quotient coarsening.2 ≃ Unit where
  toFun _ := ()
  invFun _ := Quotient.mk coarsening.2 (0,false)
  left_inv c := Quotient.inductionOn c (fun v => by apply Quotient.sound; exact True.intro)
  right_inv c := by cases c; rfl
/-- 元点を含むvᵢ台から指定商chartの全target台を生成する。 -/
theorem quotient_support_all (cut : Bool) (c : Quotient coarsening.2)
    (t : Quotient coarsening.1) : t ∈ (input cut).quotientSupport coarsening c := by
  induction t using Quotient.inductionOn with
  | _ p =>
    rw [PrimitiveInput.mem_quotientSupport]
    refine ⟨(p.1,false),p,?_,Or.inl rfl,rfl⟩
    apply chartEquiv.injective
    exact Subsingleton.elim _ _
/-- 全関係chart商は一点であることの公開API。 -/
theorem quotient_chart_eq (c d : Quotient coarsening.2) : c = d :=
  chartEquiv.injective (Subsingleton.elim _ _)
/-- 全内部辺は縮約され、指定商の有向辺は空。 -/
theorem quotient_no_edge (cut : Bool) (c d : Quotient coarsening.2) :
    ¬ (input cut).quotientEdge coarsening c d :=
  fun h => h.1 (quotient_chart_eq c d)
/-- 元ZMod2領域を同じ商targetへ逆像で読む。 -/
def region (X : Set (Width.Concept 2)) : Set (Quotient coarsening.1) := targetEquiv ⁻¹' X
/-- region所属は同じ商target全単射の逆像であることの基本API。 -/
theorem mem_region (X : Set (Width.Concept 2)) (t : Quotient coarsening.1) :
    t ∈ region X ↔ targetEquiv t ∈ X := Iff.rfl
/-- 新canonical因子の逆像は旧Width.regionと同じ元点集合。 -/
theorem factor_region (cut : Bool) (X : Set (Width.Concept 2)) :
    comparisonFactor ((input cut).quotientReading coarsening) (input cut).reading
      ((input cut).quotient_coarser coarsening) ⁻¹' region X = Width.region 2 X := by
  rw [PrimitiveInput.quotient_factor]
  rfl

end AAT.AG.SafeCoarseningOrder.W3
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
