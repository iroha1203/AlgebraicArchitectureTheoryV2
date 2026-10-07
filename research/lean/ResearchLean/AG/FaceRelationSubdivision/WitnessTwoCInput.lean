import ResearchLean.AG.FaceRelationSubdivision.ConnectedFaceWitnessInput
import ResearchLean.AG.FaceRelationSubdivision.ElementaryDiagnostics
import ResearchLean.AG.AtlasDefectComposition.ZeroH1
import Formal.Util.AssertStandardAxioms

/-!
# W2c の空辺台の分割

## Implementation notes

二点の互いに素な chart 台から空の辺台を K1 で導出する。
分割を同じ一般 constructor に適用し、alpha の頂点辺対と beta の恒等を読む。
空辺台を入力条件で排除する方式は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessTwoC
open CanonicalResolution ResolutionInvariance Cohomology TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label)
/-- v=false,w=true の原始辺と空の面型。 -/
abbrev nerve : CoverNerve where
  Chart := Bool
  EdgeComponent := Unit
  FaceComponent := Empty
  edgeLeft _ := false
  edgeRight _ := true
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds := fun f => nomatch f
/-- 各点だけを含む非空 chart 台から原始入力を生成する。 -/
abbrev N : TargetSupportedNerve q where
  nerve := nerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport v := {v}
  chartSupport_nonempty v := ⟨v,rfl⟩
  faceEdge0_left := fun f => nomatch f
  faceEdge0_right := fun f => nomatch f
  faceEdge1_right := fun f => nomatch f
/-- 空辺台にも同じ原始分割を適用する。 -/
abbrev fine := EdgeSubdivision.supported N ()
/-- 同じ mixed 原始 collapse。 -/
abbrev comparison := EdgeSubdivision.collapse N ()
/-- 原始 chart 台は指定の singleton。 -/
@[simp] theorem chart_support (v : Bool) : N.chartSupport v={v} := rfl
/-- 原始 K1 の辺台は空。 -/
@[simp] theorem edge_empty : N.edgeSupport ()=∅ := by
  ext t
  rw [N.mem_edgeSupport_iff]
  change (t=false ∧ t=true) ↔ False
  constructor
  · rintro ⟨h0,h1⟩
    exact Bool.false_ne_true (h0.symm.trans h1)
  · exact False.elim
/-- fresh chart の台は alpha。 -/
@[simp] theorem fresh_support : fine.chartSupport (.inr PUnit.unit)={false} :=
  EdgeSubdivision.chartSupport_new N ()
/-- c の台は alpha。 -/
@[simp] theorem c_support : fine.edgeSupport (.inr (.inl false))={false} :=
  EdgeSubdivision.edgeSupport_c N ()
/-- b の台は空。 -/
@[simp] theorem b_empty : fine.edgeSupport (.inr (.inl true))=∅ := by
  rw [EdgeSubdivision.edgeSupport_b,edge_empty]
/-- 原始面が空なので全出現も空。 -/
instance occurrenceIsEmpty : IsEmpty (EdgeSubdivision.Occurrence N ()) :=
  ⟨fun o => nomatch o.val.1⟩
/-- 分割対象以外の旧辺はない。 -/
instance retainedIsEmpty : IsEmpty (EdgeSubdivision.RetainedEdge N ()) :=
  ⟨fun e => e.property (Subsingleton.elim _ _)⟩
/-- alpha は fresh 頂点と c をともに選択する。 -/
theorem alpha_pair_selected : false∈fine.chartSupport (.inr PUnit.unit) ∧
    false∈fine.edgeSupport (.inr (.inl false)) := by
  rw [fresh_support,c_support]
  exact ⟨rfl,rfl⟩
/-- beta は fresh 頂点と c を選択しない。 -/
theorem beta_pair_absent : true∉fine.chartSupport (.inr PUnit.unit) ∧
    true∉fine.edgeSupport (.inr (.inl false)) := by
  rw [fresh_support,c_support]
  exact ⟨Ne.symm Bool.false_ne_true,Ne.symm Bool.false_ne_true⟩
/-- b は両ラベルで座標を生成しない。 -/
theorem b_absent (a : Bool) : a∉fine.edgeSupport (.inr (.inl true)) := by
  rw [b_empty]
  exact id
/-- alpha の fresh 頂点は同じ c で補正される。 -/
theorem homotopy_vertex : (EdgeSubdivision.h0 N ()).basisImage (.inr PUnit.unit)=
    Finsupp.single (.inr (.inl false)) 1 := EdgeSubdivision.h0_new_basis N ()
/-- beta の旧頂点の収縮像は恒等。 -/
theorem beta_identity : comparison.chartMap (.inl true)=true ∧
    (EdgeSubdivision.s0 N ()).basisImage true=Finsupp.single (.inl true) 1 ∧
    (EdgeSubdivision.h0 N ()).basisImage (.inl true)=0 :=
  ⟨rfl,EdgeSubdivision.s0_basis N () true,EdgeSubdivision.h0_old_basis N () true⟩
/-- 同じ任意 A の一般原始収縮を空辺台に適用した出力。 -/
def contraction (A : Set Bool) := EdgeSubdivision.chainContraction N () A
/-- 同じ実 Law 射は原始比較の生成 Hom。 -/
theorem law_comparison : EdgeSubdivision.lawR N () laws adequate=
    comparison.generatedComparisonHom laws adequate adequate := EdgeSubdivision.lawR_eq_generated N () laws adequate
/-- 空旧辺台から各ラベルの実辺座標は存在しない。 -/
def edgeBlockIsEmpty (l : LawValueLabel laws) : IsEmpty (N.EdgeBlockCoordinate laws adequate l) :=
  ⟨fun x => by obtain ⟨t,ht,_⟩ := x.val.generated; rw [edge_empty] at ht; exact ht⟩
/-- 同じ原始旧 H¹ は各ラベルで零。 -/
theorem old_h1_zero (l : LawValueLabel laws) : Subsingleton (N.lawValueBlockComplex laws adequate l).H1 := by
  letI := edgeBlockIsEmpty l
  letI : Subsingleton (N.lawValueBlockComplex laws adequate l).C1 :=
    (inferInstance : Subsingleton (N.EdgeBlockCoordinate laws adequate l → ℚ))
  exact h1_subsingleton_of_C1 _
/-- 同じ独立生成比較の標準同値から fine H¹ も零。 -/
theorem fine_h1_zero (l : LawValueLabel laws) : Subsingleton (fine.lawValueBlockComplex laws adequate l).H1 := by
  letI := old_h1_zero l
  exact (EdgeSubdivision.blockOldH1Iso N () laws adequate l).toLinearEquiv.symm.toEquiv.subsingleton

end AAT.AG.FaceRelationSubdivision.WitnessTwoC
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessTwoC
