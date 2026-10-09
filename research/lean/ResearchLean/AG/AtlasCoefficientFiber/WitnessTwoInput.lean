import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneInput
import ResearchLean.AG.AtlasCoefficientFiber.DegenerateCells

/-!
# G-135 W2：pure閉路の原始表

## Implementation notes

共通Source/readings/Lawを保持し、hとkの原Optionを別名で指定する。
原Option表と既存loop nerveから生成し、期待欠損を入力に持つcertificateは使わない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessTwo
open CanonicalResolution ResolutionInvariance Cohomology FaceRelationSubdivision WitnessCommon

/-- 粗一頂点、一loop h、面なし、全台K1。 -/
abbrev Nc : TargetSupportedNerve qc where
  nerve := WitnessOne.loopNerve 1
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false, Set.mem_univ _⟩
  faceEdge0_left := by intro f; exact Fin.elim0 f
  faceEdge0_right := by intro f; exact Fin.elim0 f
  faceEdge1_right := by intro f; exact Fin.elim0 f

/-- 細一頂点、h,k二loop、面なし、同じ全台。 -/
abbrev Nf : TargetSupportedNerve qf where
  nerve := WitnessOne.loopNerve 2
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(false,false), Set.mem_univ _⟩
  faceEdge0_left := by intro f; exact Fin.elim0 f
  faceEdge0_right := by intro f; exact Fin.elim0 f
  faceEdge1_right := by intro f; exact Fin.elim0 f

/-- hはh、kはnone。期待保存値を供給しない原始比較。 -/
def M : IncidenceSupportedComparison qc qf coarser Nc Nf where
  chartMap _ := 0
  edgeMap := ![some 0,none]
  faceMap := Fin.elim0
  edge_some_left := by intros; rfl
  edge_some_right := by intros; rfl
  edge_none_fiber := by intros; rfl
  face_some_edge0 := by intro f; exact Fin.elim0 f
  face_some_edge1 := by intro f; exact Fin.elim0 f
  face_some_edge2 := by intro f; exact Fin.elim0 f
  face_none_incidence := by intro f; exact Fin.elim0 f
  chartSupport_compatible _ _ _ := Set.mem_univ _

/-- 面なしから元混在面の型は空、任意A。 -/
theorem mixed_empty (A : Set Bool) : IsEmpty (MixedFace M A) :=
  ⟨fun f => Fin.elim0 f.1.1⟩

end AAT.AG.AtlasCoefficientFiber.WitnessTwo
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.Nc
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.Nf
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.M
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.mixed_empty
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessTwo
