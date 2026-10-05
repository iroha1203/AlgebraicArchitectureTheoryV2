import ResearchLean.AG.AtlasDefectComposition.ComparisonComposition
import ResearchLean.AG.ResolutionInvariance.LawValueBlockDecomposition
import Mathlib.Data.Fin.VecNotation
import Formal.Util.AssertStandardAxioms
/-! # W3の二つの原始セル比較

指定した同一Bool Source、粗一点reading、細恒等reading、定数Lawから、
孤立chart比較と四面体表面から充填三角形への比較を構成する。
微分・homology・rankは入力fieldに持たない。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessThree
open CanonicalResolution ResolutionInvariance Cohomology
/-- W3の共通二点Source。 -/
abbrev Source := Bool
/-- W3の粗readingは一点を読む。 -/
abbrev q₀ : Reading Source where
  Target := Unit
  read _ := ()
  surjective x := by cases x; exact ⟨false,rfl⟩
/-- W3の細readingは元のSourceを読む。 -/
abbrev q₁ : Reading Source where
  Target := Bool
  read := id
  surjective := Function.surjective_id
/-- W3のreadingの粗細順序を原始評価から放電する。 -/
theorem coarser : q₀.CoarserThan q₁ := by
  intro x y h
  rfl
/-- W3のreadingの真の細分化は二つのSourceで証明する。 -/
theorem not_coarser : ¬ q₁.CoarserThan q₀ := by
  intro h
  exact Bool.false_ne_true (h (x:=false) (y:=true) rfl)
/-- W3の唯一の定数Law。 -/
def laws : FiniteLawFamily Source where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Unit
  valueDecidableEq _ := inferInstance
  eval _ _ := ()
/-- W3の粗readingのadequacyは定数評価から構成する。 -/
theorem adequate₀ : laws.Adequate q₀ := fun _ => ⟨fun _ => (),fun _ => rfl⟩
/-- W3の細readingのadequacyは因子化から構成する。 -/
theorem adequate₁ : laws.Adequate q₁ := adequate_of_coarser laws coarser adequate₀
/-- W3の唯一の発生ラベルは実Sourceから得る。 -/
def label : LawValueLabel laws := LawValueLabel.ofSource laws () false
/-- W3の発生ラベルは実際に一つだけである。 -/
theorem label_unique (l : LawValueLabel laws) : l = label := by
  cases l with
  | mk l v h => cases l; cases v; apply LawValueLabel.ext <;> rfl

/-- W3aの孤立chart nerve。 -/
abbrev isolated (n : ℕ) : CoverNerve where
  Chart := Fin n
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
/-- W3aの粗一chart支持入力。 -/
abbrev A₀ : TargetSupportedNerve q₀ where
  nerve := isolated 1
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(),Set.mem_univ _⟩
  faceEdge0_left := fun f => f.elim
  faceEdge0_right := fun f => f.elim
  faceEdge1_right := fun f => f.elim
/-- W3aの細二chart支持入力。 -/
abbrev A₁ : TargetSupportedNerve q₁ where
  nerve := isolated 2
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false,Set.mem_univ _⟩
  faceEdge0_left := fun f => f.elim
  faceEdge0_right := fun f => f.elim
  faceEdge1_right := fun f => f.elim
/-- W3aの原始比較。二chartを粗唯一chartへ送る。 -/
def MA : TargetSupportedNerveMorphism q₀ q₁ coarser A₀ A₁ where
  chartMap _ := 0
  edgeMap := Empty.elim
  faceMap := Empty.elim
  edge_some_left := fun e => e.elim
  edge_some_right := fun e => e.elim
  edge_none_fiber := fun e => e.elim
  face_some_edge0 := fun f => f.elim
  face_some_edge1 := fun f => f.elim
  face_some_edge2 := fun f => f.elim
  face_none_edge0 := fun f => f.elim
  face_none_edge1 := fun f => f.elim
  face_none_edge2 := fun f => f.elim
  chartSupport_compatible _ _ _ := Set.mem_univ _
/-- W3bの四面体表面。辺順01,02,03,12,13,23、面順012,013,023,123。 -/
abbrev tetrahedron : CoverNerve where
  Chart := Fin 4
  EdgeComponent := Fin 6
  FaceComponent := Fin 4
  edgeLeft := ![0,0,0,1,1,2]
  edgeRight := ![1,2,3,2,3,3]
  faceEdge0 := ![0,0,1,3]
  faceEdge1 := ![1,2,2,4]
  faceEdge2 := ![3,4,5,5]
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial
/-- W3bの充填三角形。辺順01,02,12、面012。 -/
abbrev filledTriangle : CoverNerve where
  Chart := Fin 3
  EdgeComponent := Fin 3
  FaceComponent := Fin 1
  edgeLeft := ![0,0,1]
  edgeRight := ![1,2,2]
  faceEdge0 _ := 0
  faceEdge1 _ := 1
  faceEdge2 _ := 2
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial
/-- W3bの粗四面体支持入力。全incidenceを原始表から証明する。 -/
abbrev B₀ : TargetSupportedNerve q₀ where
  nerve := tetrahedron
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(),Set.mem_univ _⟩
  faceEdge0_left := by intro f; fin_cases f <;> rfl
  faceEdge0_right := by intro f; fin_cases f <;> rfl
  faceEdge1_right := by intro f; fin_cases f <;> rfl
/-- W3bの細充填三角形支持入力。 -/
abbrev B₁ : TargetSupportedNerve q₁ where
  nerve := filledTriangle
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false,Set.mem_univ _⟩
  faceEdge0_left := by intro f; fin_cases f <;> rfl
  faceEdge0_right := by intro f; fin_cases f <;> rfl
  faceEdge1_right := by intro f; fin_cases f <;> rfl
/-- W3bの原始比較。全細セルを同名の粗セルへ送る。 -/
def MB : TargetSupportedNerveMorphism q₀ q₁ coarser B₀ B₁ where
  chartMap := ![0,1,2]
  edgeMap := ![some 0,some 1,some 3]
  faceMap _ := some 0
  edge_some_left := by intro e c h; fin_cases e <;> simp at h <;> subst c <;> rfl
  edge_some_right := by intro e c h; fin_cases e <;> simp at h <;> subst c <;> rfl
  edge_none_fiber := by intro e h; fin_cases e <;> simp at h
  face_some_edge0 := by intro f c h; simp at h; subst c; rfl
  face_some_edge1 := by intro f c h; simp at h; subst c; rfl
  face_some_edge2 := by intro f c h; simp at h; subst c; rfl
  face_none_edge0 := by intro f h; simp at h
  face_none_edge1 := by intro f h; simp at h
  face_none_edge2 := by intro f h; simp at h
  chartSupport_compatible _ _ _ := Set.mem_univ _

end AAT.AG.AtlasDefectComposition.WitnessThree
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessThree
