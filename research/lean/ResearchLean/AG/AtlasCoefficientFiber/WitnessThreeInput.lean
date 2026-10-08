import ResearchLean.AG.AtlasCoefficientFiber.WitnessCommon
import Mathlib.Data.Fin.VecNotation

/-!
# G-135 W3の指定原始セル表

## Implementation notes

粗辺はa,b,c,h、細辺はa₀,a₁,b,c,h,k、細面はf₀,f₁,mの順にFinで表す。
全chart台は指定target全体であり、辺・面の台は既存K1から生成する。
同じincidenceを持つ二面を一面へまとめる案は指定された面名を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CanonicalResolution ResolutionInvariance Cohomology FaceRelationSubdivision WitnessCommon

/-- 粗側の二つの別名三角面と保存用loop h。 -/
abbrev coarseNerve : CoverNerve where
  Chart := Fin 3
  EdgeComponent := Fin 4
  FaceComponent := Fin 2
  edgeLeft := ![0,0,1,0]
  edgeRight := ![1,2,2,0]
  faceEdge0 _ := 0
  faceEdge1 _ := 1
  faceEdge2 _ := 2
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial
/-- 細側の指定二面と混在面m=(k,a₁,a₀)。 -/
abbrev fineNerve : CoverNerve where
  Chart := Fin 3
  EdgeComponent := Fin 6
  FaceComponent := Fin 3
  edgeLeft := ![0,0,0,1,0,0]
  edgeRight := ![1,1,2,2,0,0]
  faceEdge0 := ![0,1,5]
  faceEdge1 := ![2,2,1]
  faceEdge2 := ![3,3,0]
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial
/-- 全chart台を持つ指定粗入力。 -/
abbrev Nc : TargetSupportedNerve qc where
  nerve := coarseNerve
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false, Set.mem_univ _⟩
  faceEdge0_left _ := rfl
  faceEdge0_right _ := rfl
  faceEdge1_right _ := rfl
/-- 全chart台を持つ指定細入力。 -/
abbrev Nf : TargetSupportedNerve qf where
  nerve := fineNerve
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(false,false), Set.mem_univ _⟩
  faceEdge0_left := by intro f; fin_cases f <;> rfl
  faceEdge0_right := by intro f; fin_cases f <;> rfl
  faceEdge1_right := by intro f; fin_cases f <;> rfl
/-- 全セルの指定像と原始零和から生成する比較。 -/
def M : IncidenceSupportedComparison qc qf coarser Nc Nf where
  chartMap := id
  edgeMap := ![some 0,some 0,some 1,some 2,some 3,none]
  faceMap := ![some 0,some 1,none]
  edge_some_left := by
    intro e c h
    fin_cases e <;> simp at h <;> subst c <;> rfl
  edge_some_right := by
    intro e c h
    fin_cases e <;> simp at h <;> subst c <;> rfl
  edge_none_fiber := by
    intro e h
    fin_cases e <;> simp at h
    rfl
  face_some_edge0 := by
    intro f c h
    fin_cases f <;> simp at h <;> subst c <;> rfl
  face_some_edge1 := by
    intro f c h
    fin_cases f <;> simp at h <;> subst c <;> rfl
  face_some_edge2 := by
    intro f c h
    fin_cases f <;> simp at h <;> subst c <;> rfl
  face_none_incidence := by
    intro f h
    fin_cases f <;> simp at h
    simp
  chartSupport_compatible _ _ _ := Set.mem_univ _

/-- 指定paired入力はmだけを除き、全頂点・辺・二面を保つ。 -/
abbrev pairedNerve : CoverNerve where
  Chart := Fin 3
  EdgeComponent := Fin 6
  FaceComponent := Fin 2
  edgeLeft := ![0,0,0,1,0,0]
  edgeRight := ![1,1,2,2,0,0]
  faceEdge0 := ![0,1]
  faceEdge1 _ := 2
  faceEdge2 _ := 3
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial
/-- mだけを除いた同じ全支持細入力。 -/
abbrev pairedNf : TargetSupportedNerve qf where
  nerve := pairedNerve
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(false,false), Set.mem_univ _⟩
  faceEdge0_left := by intro f; fin_cases f <;> rfl
  faceEdge0_right := by intro f; fin_cases f <;> rfl
  faceEdge1_right := by intro f; fin_cases f <;> rfl
/-- mだけを除いた原始比較。既存辺像・頂点像を全て保持する。 -/
def pairedM : IncidenceSupportedComparison qc qf coarser Nc pairedNf where
  chartMap := M.chartMap
  edgeMap := M.edgeMap
  faceMap f := some f
  edge_some_left := M.edge_some_left
  edge_some_right := M.edge_some_right
  edge_none_fiber := M.edge_none_fiber
  face_some_edge0 := by
    intro f c h
    simp only [Option.some.injEq] at h
    subst c
    fin_cases f <;> rfl
  face_some_edge1 := by intro f c h; cases h; rfl
  face_some_edge2 := by intro f c h; cases h; rfl
  face_none_incidence := by intro f h; cases h
  chartSupport_compatible _ _ _ := Set.mem_univ _

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseNerve
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fineNerve
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.Nc
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.Nf
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.M
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedNerve
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedNf
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedM
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
