import ResearchLean.AG.FaceRelationSubdivision.ConnectedFaceWitnessInput
import ResearchLean.AG.FaceRelationSubdivision.ElementaryDiagnostics
import Formal.Util.AssertStandardAxioms

/-!
# W2b の一面内三重出現

## Implementation notes

一頂点・二 loop・同じ辺の三つの位置を原始表から生成する。
Occurrence の Fin3 位置を別名として保持し、一般分割の section の符号を評価する。
三つの位置を辺名の集合にまとめる方式は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessTwoB
open CanonicalResolution ResolutionInvariance Cohomology TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label labelEquiv)

/-- 二 loop e=false,k=true と三重面の原始 nerve。 -/
abbrev nerve : CoverNerve where
  Chart := Unit
  EdgeComponent := Bool
  FaceComponent := Unit
  edgeLeft _ := ()
  edgeRight _ := ()
  faceEdge0 _ := false
  faceEdge1 _ := false
  faceEdge2 _ := false
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial
/-- 全 chart 台から同じ K1 と微分を生成する入力。 -/
abbrev N : TargetSupportedNerve q where
  nerve := nerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false,Set.mem_univ _⟩
  faceEdge0_left _ := rfl
  faceEdge0_right _ := rfl
  faceEdge1_right _ := rfl
/-- e の全三出現を再三角形化した同じ細入力。 -/
abbrev fine := EdgeSubdivision.supported N false
/-- 同じ原始 mixed collapse。 -/
abbrev comparison := EdgeSubdivision.collapse N false
/-- 原始旧 chart 台は全体。 -/
@[simp] theorem chart_full (v : N.nerve.Chart) : N.chartSupport v=Set.univ := rfl
/-- 同じ fine chart 台も全体。 -/
@[simp] theorem fine_chart_full (v : fine.nerve.Chart) : fine.chartSupport v=Set.univ := by
  cases v with
  | inl v => exact EdgeSubdivision.chartSupport_old N false v
  | inr v => exact EdgeSubdivision.chartSupport_new N false
/-- 原始三位置はどれも e を指す。 -/
@[simp] theorem slot_target (i : Fin 3) : EdgeSubdivision.faceSlot N () i=false := by
  fin_cases i
  · exact EdgeSubdivision.faceSlot_zero N ()
  · exact EdgeSubdivision.faceSlot_one N ()
  · exact EdgeSubdivision.faceSlot_two N ()
/-- 三重出現の位置から得る別名。 -/
def occurrence (i : Fin 3) : EdgeSubdivision.Occurrence N false := ⟨((),i),slot_target i⟩
/-- 全出現は Fin3 の三位置で尽くされ、位置は潰れない。 -/
def occurrenceEquiv : EdgeSubdivision.Occurrence N false ≃ Fin 3 where
  toFun o := o.val.2
  invFun := occurrence
  left_inv o := by apply Subtype.ext; apply Prod.ext; exact Subsingleton.elim _ _; rfl
  right_inv _ := rfl
/-- 異なる位置は異なる原始出現名を持つ。 -/
theorem occurrence_injective : Function.Injective occurrence := fun _ _ h => congrArg (fun o => o.val.2) h
/-- 位置ごとの対角辺名。 -/
def diagonal (i : Fin 3) : fine.nerve.EdgeComponent := .inr (.inr (occurrence i))
/-- 位置ごとの追加面名。 -/
def triangle (i : Fin 3) : fine.nerve.FaceComponent := .inr (occurrence i)
/-- 三つの対角辺は別名である。 -/
theorem diagonal_injective : Function.Injective diagonal := by
  intro i j h
  exact occurrence_injective (Sum.inr.inj (Sum.inr.inj h))
/-- 三つの追加面も別名である。 -/
theorem triangle_injective : Function.Injective triangle := by
  intro i j h
  exact occurrence_injective (Sum.inr.inj h)
/-- 同じ旧面の原始境界は三出現の符号 1−1+1 により e。 -/
theorem old_boundary : (TargetSupportedNerve.rawD2 N).basisImage ()=Finsupp.single false 1 := by
  rw [TargetSupportedNerve.rawD2_basis]
  change Finsupp.single false 1-Finsupp.single false 1+Finsupp.single false 1=_
  abel
/-- 指定 section は中心面+t0−t1+t2 である。 -/
theorem section_face : (EdgeSubdivision.s2 N false).basisImage ()=
    Finsupp.single (.inl ()) 1+Finsupp.single (triangle 0) 1-
      Finsupp.single (triangle 1) 1+Finsupp.single (triangle 2) 1 := by
  rw [EdgeSubdivision.s2_basis]
  simp only [EdgeSubdivision.slotSection_basis,slot_target,↓reduceDIte]
  rfl
/-- fresh 頂点の指定補正は c。 -/
theorem homotopy_vertex : (EdgeSubdivision.h0 N false).basisImage (.inr PUnit.unit)=
    Finsupp.single (.inr (.inl false)) 1 := EdgeSubdivision.h0_new_basis N false
/-- 各対角辺は自分の別名追加面の負で補正する。 -/
theorem homotopy_diagonal (i : Fin 3) : (EdgeSubdivision.h1 N false).basisImage (diagonal i)=
    -Finsupp.single (triangle i) 1 := EdgeSubdivision.h1_diagonal_basis N false (occurrence i)
/-- 同じ二 loop の原始次数0微分は零。 -/
@[simp] theorem d0_apply (z : (namedComplex N).C0) (e : Bool) : (namedComplex N).d0 z e=0 := by
  rw [namedComplex_d0_apply]
  exact sub_self _
/-- 三重出現の実次数1微分は e 値を読む。 -/
@[simp] theorem d1_apply (z : (namedComplex N).C1) (f : Unit) : (namedComplex N).d1 z f=z false := by
  rw [namedComplex_d1_apply]
  change z false-z false+z false=_
  ring
/-- 同じ loop k は分割する e と同じ唯一の頂点に接続する。 -/
theorem loop_attached : N.nerve.edgeLeft true=N.nerve.edgeLeft false ∧
    N.nerve.edgeRight true=N.nerve.edgeRight false := ⟨rfl,rfl⟩

end AAT.AG.FaceRelationSubdivision.WitnessTwoB
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessTwoB
