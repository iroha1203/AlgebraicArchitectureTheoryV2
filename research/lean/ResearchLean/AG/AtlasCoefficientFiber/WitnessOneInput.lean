import ResearchLean.AG.AtlasCoefficientFiber.WitnessCommon
import Mathlib.Data.Fin.VecNotation

/-!
# G-135 W1：指定されたloop削除と重複の原始入力

## Implementation notes

セル名e,hとe₀,e₁,hをFinの順で保持する。両側のchart台は指定target全体。
期待する核や余核を入力にせず、同じSource、Law、Optionから比較を生成する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessOne
open CanonicalResolution ResolutionInvariance Cohomology FaceRelationSubdivision WitnessCommon

/-- 一chart、指定個数のloop、面なしの原始表。 -/
abbrev loopNerve (n : ℕ) : CoverNerve where
  Chart := Fin 1
  EdgeComponent := Fin n
  FaceComponent := Fin 0
  edgeLeft _ := 0
  edgeRight _ := 0
  faceEdge0 := Fin.elim0
  faceEdge1 := Fin.elim0
  faceEdge2 := Fin.elim0
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial

/-- 粗loop e,hの全台入力。 -/
abbrev Nc : TargetSupportedNerve qc where
  nerve := loopNerve 2
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false, Set.mem_univ _⟩
  faceEdge0_left := by intro f; exact Fin.elim0 f
  faceEdge0_right := by intro f; exact Fin.elim0 f
  faceEdge1_right := by intro f; exact Fin.elim0 f

/-- hだけを残す細全台入力。 -/
abbrev Na : TargetSupportedNerve qf where
  nerve := loopNerve 1
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(false,false), Set.mem_univ _⟩
  faceEdge0_left := by intro f; exact Fin.elim0 f
  faceEdge0_right := by intro f; exact Fin.elim0 f
  faceEdge1_right := by intro f; exact Fin.elim0 f

/-- e₀,e₁,hを別名で保持する細全台入力。 -/
abbrev Nb : TargetSupportedNerve qf where
  nerve := loopNerve 3
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(false,false), Set.mem_univ _⟩
  faceEdge0_left := by intro f; exact Fin.elim0 f
  faceEdge0_right := by intro f; exact Fin.elim0 f
  faceEdge1_right := by intro f; exact Fin.elim0 f

/-- W1a原始Optionはhだけをhへ送る。 -/
def Ma : IncidenceSupportedComparison qc qf coarser Nc Na where
  chartMap _ := 0
  edgeMap _ := some 1
  faceMap := Fin.elim0
  edge_some_left := by intros; rfl
  edge_some_right := by intros; rfl
  edge_none_fiber := by intro e h; cases h
  face_some_edge0 := by intro f; exact Fin.elim0 f
  face_some_edge1 := by intro f; exact Fin.elim0 f
  face_some_edge2 := by intro f; exact Fin.elim0 f
  face_none_incidence := by intro f; exact Fin.elim0 f
  chartSupport_compatible _ _ _ := Set.mem_univ _

/-- W1b原始Optionはe₀,e₁をe、hをhへ送る。 -/
def Mb : IncidenceSupportedComparison qc qf coarser Nc Nb where
  chartMap _ := 0
  edgeMap := ![some 0,some 0,some 1]
  faceMap := Fin.elim0
  edge_some_left := by intros; rfl
  edge_some_right := by intros; rfl
  edge_none_fiber := by intro e h; fin_cases e <;> simp at h
  face_some_edge0 := by intro f; exact Fin.elim0 f
  face_some_edge1 := by intro f; exact Fin.elim0 f
  face_some_edge2 := by intro f; exact Fin.elim0 f
  face_none_incidence := by intro f; exact Fin.elim0 f
  chartSupport_compatible _ _ _ := Set.mem_univ _

/-- W1a全辺mappedは指定表の結論。 -/
theorem Ma_all_mapped (e) : Ma.edgeMap e ≠ none := by simp [Ma]
/-- W1b全辺mappedは指定表の結論。 -/
theorem Mb_all_mapped (e) : Mb.edgeMap e ≠ none := by fin_cases e <;> simp [Mb]
/-- W1a指定面なしから全面mapped条件が成立する。 -/
theorem Ma_faces_mapped (f) : Ma.faceMap f ≠ none := Fin.elim0 f
/-- W1b指定面なしから全面mapped条件が成立する。 -/
theorem Mb_faces_mapped (f) : Mb.faceMap f ≠ none := Fin.elim0 f

end AAT.AG.AtlasCoefficientFiber.WitnessOne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.loopNerve
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.Nc
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.Na
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.Nb
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.Ma
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.Mb
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.Ma_all_mapped
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.Mb_all_mapped
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.Ma_faces_mapped
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.Mb_faces_mapped
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessOne
