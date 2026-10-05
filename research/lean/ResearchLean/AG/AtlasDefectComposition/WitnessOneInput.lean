import ResearchLean.AG.AtlasDefectComposition.ComparisonComposition
import ResearchLean.AG.ResolutionInvariance.LawValueBlockDecomposition
import Mathlib.Data.Fin.VecNotation
import Formal.Util.AssertStandardAxioms

/-!
# W1 の共通原始入力

G-133 W1 の八点Source、真の三reading、非定数Law、支持セル表、部分比較を構成する。
比較行列とコホモロジーは入力に持たず、既存生成APIへの入力幾何を与える。

## Implementation notes

セル名は指定表の順にFinで表す。全chart台は全target。辺・面の台は既存K1交差で生成する。
面はW1の指定通り空であり、一般Aの量化は変更しない。
-/

noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open CanonicalResolution ResolutionInvariance Cohomology

/-- W1 の八点Source。座標は (a,(b,c))。 -/
abbrev Source := Bool × Bool × Bool

/-- W1 の第一座標を読む粗reading。 -/
abbrev q₀ : Reading Source where
  Target := Bool
  read s := s.1
  surjective a := ⟨(a, false, false), rfl⟩

/-- W1 の第一・第二座標を読む中間reading。 -/
abbrev q₁ : Reading Source where
  Target := Bool × Bool
  read s := (s.1, s.2.1)
  surjective ab := ⟨(ab.1, ab.2, false), by cases ab; rfl⟩

/-- W1 の全Sourceを読む細reading。 -/
abbrev q₂ : Reading Source where
  Target := Source
  read := id
  surjective := Function.surjective_id

/-- W1 の最初のreading順序。 -/
theorem coarser₀₁ : q₀.CoarserThan q₁ := by
  intro x y h
  change (x.1, x.2.1) = (y.1, y.2.1) at h
  change x.1 = y.1
  exact congrArg (fun p : Bool × Bool => p.1) h

/-- W1 の二番目のreading順序。 -/
theorem coarser₁₂ : q₁.CoarserThan q₂ := by
  intro x y h
  exact congrArg q₁.read h

/-- W1 の最初の真の細分化をSourceで示す。 -/
theorem not_coarser₁₀ : ¬ q₁.CoarserThan q₀ := by
  intro h
  have heq := h (x := (false, false, false)) (y := (false, true, false)) rfl
  exact Bool.false_ne_true (congrArg Prod.snd heq)

/-- W1 の二番目の真の細分化をSourceで示す。 -/
theorem not_coarser₂₁ : ¬ q₂.CoarserThan q₁ := by
  intro h
  have heq := h (x := (false, false, false)) (y := (false, false, true)) rfl
  exact Bool.false_ne_true (congrArg (fun s : Source => s.2.2) heq)

/-- W1 の唯一のLawは第一座標。 -/
def laws : FiniteLawFamily Source where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Bool
  valueDecidableEq _ := inferInstance
  eval _ s := s.1

/-- W1 の粗readingのadequacyは評価から構成する。 -/
theorem adequate₀ : laws.Adequate q₀ := fun _ => ⟨id, fun _ => rfl⟩

/-- W1 の中間readingのadequacyを一般因子化から生成する。 -/
theorem adequate₁ : laws.Adequate q₁ := adequate_of_coarser laws coarser₀₁ adequate₀

/-- W1 の細readingのadequacyを一般因子化から生成する。 -/
theorem adequate₂ : laws.Adequate q₂ := adequate_of_coarser laws coarser₁₂ adequate₁

/-- W1 のLawが非定数である同じSource上の証人。 -/
theorem law_nonconstant : ∃ l s t, laws.eval l s ≠ laws.eval l t :=
  ⟨(), (false, false, false), (true, false, false), by decide⟩

/-- W1 の第一因子は第一座標射影。 -/
theorem factor₀₁ : comparisonFactor q₀ q₁ coarser₀₁ = Prod.fst := by
  symm
  exact comparisonFactor_unique q₀ q₁ coarser₀₁ Prod.fst (fun _ => rfl)

/-- W1 の第二因子は第一・第二座標射影。 -/
theorem factor₁₂ : comparisonFactor q₁ q₂ coarser₁₂ = q₁.read := by
  symm
  exact comparisonFactor_unique q₁ q₂ coarser₁₂ q₁.read (fun _ => rfl)

/-- W1 の粗・細三角形。辺順は01,02,12。 -/
abbrev triangle : CoverNerve where
  Chart := Fin 3
  EdgeComponent := Fin 3
  FaceComponent := Empty
  edgeLeft := ![0, 0, 1]
  edgeRight := ![1, 2, 2]
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds := fun f => f.elim

/-- W1 の中間段。辺順は01,02,12,03,04,34。 -/
abbrev twoTriangles : CoverNerve where
  Chart := Fin 5
  EdgeComponent := Fin 6
  FaceComponent := Empty
  edgeLeft := ![0, 0, 1, 0, 0, 3]
  edgeRight := ![1, 2, 2, 3, 4, 4]
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds := fun f => f.elim

/-- W1 の段階0の支持nerve。全chart台は全target。 -/
abbrev N₀ : TargetSupportedNerve q₀ where
  nerve := triangle
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false, Set.mem_univ _⟩
  faceEdge0_left := fun f => f.elim
  faceEdge0_right := fun f => f.elim
  faceEdge1_right := fun f => f.elim

/-- W1 の段階1の支持nerve。全chart台は全target。 -/
abbrev N₁ : TargetSupportedNerve q₁ where
  nerve := twoTriangles
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(false, false), Set.mem_univ _⟩
  faceEdge0_left := fun f => f.elim
  faceEdge0_right := fun f => f.elim
  faceEdge1_right := fun f => f.elim

/-- W1 の段階2の支持nerve。全chart台は全target。 -/
abbrev N₂ : TargetSupportedNerve q₂ where
  nerve := triangle
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(false, false, false), Set.mem_univ _⟩
  faceEdge0_left := fun f => f.elim
  faceEdge0_right := fun f => f.elim
  faceEdge1_right := fun f => f.elim

/-- W1 の指定セル表による原始比較M₀₁。全fieldを表から放電する。 -/
def M₀₁ : TargetSupportedNerveMorphism q₀ q₁ coarser₀₁ N₀ N₁ where
  chartMap := ![0, 1, 2, 0, 0]
  edgeMap := ![some 0, some 1, some 2, none, none, none]
  faceMap := Empty.elim
  edge_some_left := by
    intro e c h
    fin_cases e <;> simp at h <;> subst c <;> rfl
  edge_some_right := by
    intro e c h
    fin_cases e <;> simp at h <;> subst c <;> rfl
  edge_none_fiber := by
    intro e h
    fin_cases e <;> simp at h <;> rfl
  face_some_edge0 := fun f => f.elim
  face_some_edge1 := fun f => f.elim
  face_some_edge2 := fun f => f.elim
  face_none_edge0 := fun f => f.elim
  face_none_edge1 := fun f => f.elim
  face_none_edge2 := fun f => f.elim
  chartSupport_compatible _ _ _ := Set.mem_univ _

/-- W1 の指定セル表による原始比較M₁₂。全fieldを表から放電する。 -/
def M₁₂ : TargetSupportedNerveMorphism q₁ q₂ coarser₁₂ N₁ N₂ where
  chartMap := ![0, 1, 2]
  edgeMap := ![some 0, some 1, some 2]
  faceMap := Empty.elim
  edge_some_left := by
    intro e c h
    fin_cases e <;> simp at h <;> subst c <;> rfl
  edge_some_right := by
    intro e c h
    fin_cases e <;> simp at h <;> subst c <;> rfl
  edge_none_fiber := by
    intro e h
    fin_cases e <;> simp at h
  face_some_edge0 := fun f => f.elim
  face_some_edge1 := fun f => f.elim
  face_some_edge2 := fun f => f.elim
  face_none_edge0 := fun f => f.elim
  face_none_edge1 := fun f => f.elim
  face_none_edge2 := fun f => f.elim
  chartSupport_compatible _ _ _ := Set.mem_univ _

/-- W1 の直接セル比較は原始二射の合成から作る。 -/
abbrev M₀₂ := comparisonComp M₀₁ M₁₂

/-- W1 の直接比較は全chart名を保持する。readingは同一視しない。 -/
theorem direct_chart (c : Fin 3) : M₀₂.chartMap c = c := by
  fin_cases c <;> rfl

/-- W1 の直接比較は全edge名を保持する。 -/
theorem direct_edge (e : Fin 3) : M₀₂.edgeMap e = some e := by
  fin_cases e <;> rfl

/-- W1 の二つの実ラベルをSourceから構成する。 -/
def label (a : Bool) : LawValueLabel laws := LawValueLabel.ofSource laws () (a, false, false)

/-- W1 の二つのラベルが異なることの値による証明。 -/
theorem labels_distinct : label false ≠ label true := by
  intro h
  have hv := congrArg (fun l : LawValueLabel laws => l.value) h
  exact Bool.false_ne_true hv

/-- W1 の全発生ラベルは指定した二ラベルで尽くされる。 -/
theorem labels_exhaust (l : LawValueLabel laws) : ∃ a : Bool, l = label a := by
  cases l with
  | mk law value generated =>
    cases law
    exact ⟨value, by apply LawValueLabel.ext <;> rfl⟩

end AAT.AG.AtlasDefectComposition.WitnessOne

#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
