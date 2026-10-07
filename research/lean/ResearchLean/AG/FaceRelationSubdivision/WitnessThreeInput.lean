import ResearchLean.AG.FaceRelationSubdivision.ConnectedFaceWitnessInput
import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationLaw
import ResearchLean.AG.AtlasDefectComposition.NamedComparison
import Formal.Util.AssertStandardAxioms

/-!
# W3の固定入力と実三項生成

## Implementation notes

全台の同じ連結面表をEの原始face複製へ渡す。
名付き複体は実Law生成後の全三成分同定として使い、期待H¹/H²をfieldに置かない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessThree
open CanonicalResolution ResolutionInvariance Cohomology TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label labelEquiv)

/-- W3の指定全台入力。辺順e,a,b,k、頂点順v,w,u。 -/
abbrev N : TargetSupportedNerve q := ConnectedFaceWitness.supported (fun _ => Set.univ)
  (fun _ => ⟨false,Set.mem_univ _⟩)
/-- 同じF=()の原始複製。 -/
abbrev fine : TargetSupportedNerve q := FaceDuplication.supported N ()
/-- W3の指定fresh面→F比較を新クラスで生成する。 -/
abbrev comparison := FaceDuplication.comparison N ()
/-- W3の全旧chart台。 -/
theorem chart_full (v : N.nerve.Chart) : N.chartSupport v = Set.univ := rfl
/-- 同じK1からの全旧辺台。 -/
theorem edge_full : ∀ e, N.edgeSupport e = Set.univ := fullSupport_edge N chart_full
/-- 同じK1からの全旧面台。 -/
theorem face_full : ∀ f, N.faceSupport f = Set.univ := fullSupport_face N chart_full
/-- 複製後も全chart台を保持する。 -/
theorem fine_chart_full (v : fine.nerve.Chart) : fine.chartSupport v = Set.univ := rfl
/-- 複製後のK1辺台。 -/
theorem fine_edge_full : ∀ e, fine.edgeSupport e = Set.univ := fullSupport_edge fine fine_chart_full
/-- 複製後のK1面台。 -/
theorem fine_face_full : ∀ f, fine.faceSupport f = Set.univ := fullSupport_face fine fine_chart_full
/-- 各ラベルの旧実生成複体と名付き原始三項複体の全三成分同定。 -/
def blockEquiv (l : LawValueLabel laws) := fullBlockNamedEquivalence N laws adequate chart_full edge_full face_full l
/-- 各ラベルの細実生成複体と名付き原始三項複体の全三成分同定。 -/
def fineBlockEquiv (l : LawValueLabel laws) := fullBlockNamedEquivalence fine laws adequate fine_chart_full fine_edge_full fine_face_full l
/-- 旧名付き実微分は指定端点差分である。 -/
@[simp] theorem d0_apply (c : Fin 3 → ℚ) (e : Fin 4) :
    (namedComplex N).d0 c e = c (![1,2,2,0] e) - c (![0,0,1,0] e) := by
  rw [namedComplex_d0_apply, ConnectedFaceWitness.edgeLeft, ConnectedFaceWitness.edgeRight]
/-- 旧名付き実面微分はe−a+b。 -/
@[simp] theorem d1_apply (z : Fin 4 → ℚ) (f : Unit) :
    (namedComplex N).d1 z f = z 0 - z 1 + z 2 := by
  rw [namedComplex_d1_apply, ConnectedFaceWitness.faceEdge0, ConnectedFaceWitness.faceEdge1,
    ConnectedFaceWitness.faceEdge2]
/-- 細名付き次数0微分は同じ端点差分。 -/
@[simp] theorem fine_d0_apply (c : Fin 3 → ℚ) (e : Fin 4) :
    (namedComplex fine).d0 c e = c (![1,2,2,0] e) - c (![0,0,1,0] e) := by
  rw [namedComplex_d0_apply, FaceDuplication.edgeLeft_eq, FaceDuplication.edgeRight_eq,
    ConnectedFaceWitness.edgeLeft, ConnectedFaceWitness.edgeRight]
/-- 細名付き微分は旧面・fresh面の両方で同じe−a+b。 -/
@[simp] theorem fine_d1_apply (z : Fin 4 → ℚ) (f : fine.nerve.FaceComponent) :
    (namedComplex fine).d1 z f = z 0 - z 1 + z 2 := by
  rw [namedComplex_d1_apply, FaceDuplication.faceEdge0_fold, FaceDuplication.faceEdge1_fold,
    FaceDuplication.faceEdge2_fold, ConnectedFaceWitness.faceEdge0, ConnectedFaceWitness.faceEdge1,
    ConnectedFaceWitness.faceEdge2]
/-- 名付き射は独立実生成block比較の移送として作る。 -/
def namedHom (l : LawValueLabel laws) := namedComparisonHom (FaceDuplication.collapse N ()) laws
  adequate adequate chart_full edge_full face_full fine_chart_full fine_edge_full fine_face_full l
/-- 同じ実生成block射との全三成分正方形。 -/
theorem named_square (l : LawValueLabel laws) :
    cochainComp (FaceDuplication.blockHom N () laws adequate l) (fineBlockEquiv l).toHom =
    cochainComp (blockEquiv l).toHom (namedHom l) := by
  rw [FaceDuplication.blockHom_eq_hereditary]
  exact namedComparisonHom_square _ _ _ _ _ _ _ _ _ _ _
/-- 同じ名付き比較の次数1は各辺上で恒等。 -/
@[simp] theorem named_f1 (l : LawValueLabel laws) (z : Fin 4 → ℚ) (e : Fin 4) :
    (namedHom l).f1 z e = z e :=
  namedComparisonHom_f1_some (FaceDuplication.collapse N ()) laws adequate adequate chart_full edge_full face_full fine_chart_full fine_edge_full fine_face_full l z e e (FaceDuplication.collapse_edge N () e)
/-- 同じ名付き比較の次数2はFから両面へ同じ値を読む。 -/
@[simp] theorem named_f2 (l : LawValueLabel laws) (z : Unit → ℚ) (f : fine.nerve.FaceComponent) :
    (namedHom l).f2 z f = z () := by
  exact namedComparisonHom_f2_some _ _ _ _ _ _ _ _ _ _ _ z f () (by
    rw [FaceDuplication.collapse_face])

end AAT.AG.FaceRelationSubdivision.WitnessThree
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessThree
