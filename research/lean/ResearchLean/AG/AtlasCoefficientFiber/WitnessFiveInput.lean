import ResearchLean.AG.AtlasCoefficientFiber.WitnessCommon
import Mathlib.Data.Fin.VecNotation

/-!
# G-135 W5：同じ辺が二度現れる混在面の原始表

## Implementation notes

粗辺e,hと細辺e,h,kをFinの順序で名付ける。原m=(k,e,e)はUnitの面であり、
位置1と2を別のincidenceとして保持する。全chart台から辺・面の台を生成する。
κ同型や期待rankを表のfieldにする案は構成義務を残すため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CanonicalResolution ResolutionInvariance Cohomology FaceRelationSubdivision WitnessCommon

/-- 一chart・二つの別名loop・面なしの指定粗表。 -/
abbrev coarseNerve : CoverNerve where
  Chart := Unit
  EdgeComponent := Fin 2
  FaceComponent := Empty
  edgeLeft _ := ()
  edgeRight _ := ()
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial
/-- 三loopと指定m=(k,e,e)。同辺eの二位置を保持する。 -/
abbrev fineNerve : CoverNerve where
  Chart := Unit
  EdgeComponent := Fin 3
  FaceComponent := Unit
  edgeLeft _ := ()
  edgeRight _ := ()
  faceEdge0 _ := 2
  faceEdge1 _ := 0
  faceEdge2 _ := 0
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial
/-- 原全chart台を持つ粗reading入力。 -/
abbrev Nc : TargetSupportedNerve qc where
  nerve := coarseNerve
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false, Set.mem_univ _⟩
  faceEdge0_left f := Empty.elim f
  faceEdge0_right f := Empty.elim f
  faceEdge1_right f := Empty.elim f
/-- 同原全chart台を持つ細reading入力。 -/
abbrev Nf : TargetSupportedNerve qf where
  nerve := fineNerve
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(false,false), Set.mem_univ _⟩
  faceEdge0_left _ := rfl
  faceEdge0_right _ := rfl
  faceEdge1_right _ := rfl
/-- 指定Option像とk−e+eの原零和から生成する部分セル比較。 -/
def M : IncidenceSupportedComparison qc qf coarser Nc Nf where
  chartMap := id
  edgeMap := ![some 0,some 1,none]
  faceMap _ := none
  edge_some_left := by intro e c h; rfl
  edge_some_right := by intro e c h; rfl
  edge_none_fiber := by intro e h; rfl
  face_some_edge0 := by intro f c h; cases h
  face_some_edge1 := by intro f c h; cases h
  face_some_edge2 := by intro f c h; cases h
  face_none_incidence := by intro f h; simp
  chartSupport_compatible _ _ _ := Set.mem_univ _

/-- 原chart像は同じ唯一chart。 -/
@[simp] theorem chartMap_apply (c : Unit) : M.chartMap c = c := rfl
/-- 同名eの原像。 -/
@[simp] theorem edgeMap_e : M.edgeMap 0 = some 0 := rfl
/-- 同名hの原像。 -/
@[simp] theorem edgeMap_h : M.edgeMap 1 = some 1 := rfl
/-- 原kはnone辺。 -/
@[simp] theorem edgeMap_k : M.edgeMap 2 = none := rfl
/-- 原表から唯一のnone辺を同定するowner API。 -/
theorem edgeMap_none_iff (e : Fin 3) : M.edgeMap e = none ↔ e = 2 := by
  fin_cases e <;> simp [M]
/-- 原mapped辺の全像を同名e/hへ同定するowner API。 -/
theorem edgeMap_some_iff (e : Fin 3) (c : Fin 2) :
    M.edgeMap e = some c ↔ e = Fin.castLE (by decide) c := by
  fin_cases e <;> fin_cases c <;> simp [M]
/-- 元mの像はnone。 -/
@[simp] theorem faceMap_apply (f : Unit) : M.faceMap f = none := rfl
/-- 同じ唯一chartが各原細辺の両端点である。 -/
@[simp] theorem fine_edgeLeft (e : Fin 3) : Nf.nerve.edgeLeft e = () := rfl
/-- 原細辺の右端点評価。 -/
@[simp] theorem fine_edgeRight (e : Fin 3) : Nf.nerve.edgeRight e = () := rfl
/-- 指定mの位置0はk。 -/
@[simp] theorem fine_faceEdge0 (f : Unit) : Nf.nerve.faceEdge0 f = 2 := rfl
/-- 指定mの位置1はe。 -/
@[simp] theorem fine_faceEdge1 (f : Unit) : Nf.nerve.faceEdge1 f = 0 := rfl
/-- 指定mの位置2も同じe、位置そのものは保持する。 -/
@[simp] theorem fine_faceEdge2 (f : Unit) : Nf.nerve.faceEdge2 f = 0 := rfl

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseNerve
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineNerve
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.Nc
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.Nf
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.M
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.chartMap_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.edgeMap_e
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.edgeMap_h
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.edgeMap_k
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.edgeMap_none_iff
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.edgeMap_some_iff
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.faceMap_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_edgeLeft
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_edgeRight
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_faceEdge0
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_faceEdge1
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_faceEdge2
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
