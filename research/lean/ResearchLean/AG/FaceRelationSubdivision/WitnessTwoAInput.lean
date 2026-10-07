import ResearchLean.AG.FaceRelationSubdivision.ConnectedFaceWitnessInput
import ResearchLean.AG.FaceRelationSubdivision.ElementaryDiagnostics
import ResearchLean.AG.FaceRelationSubdivision.PointSubsetNamed
import Formal.Util.AssertStandardAxioms

/-!
# W2a の面付き分割と片側の支持

## Implementation notes

連結原始表 v,w,u/e,a,b,k/F を共有し、w の台だけを alpha にする。
K1 の交差から全支持値を得て、同じ一般分割の一出現を評価する。
beta 成分を全台へ替えて収縮を示す方式は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessTwoA
open CanonicalResolution ResolutionInvariance Cohomology TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label)
/-- 指定 chart 台 v,u 全体 / w alpha。 -/
def support : Fin 3 → Set Bool := ![Set.univ,{false},Set.univ]
/-- 原始 chart 台はすべて非空。 -/
theorem support_nonempty (v : Fin 3) : (support v).Nonempty := by
  fin_cases v <;> simp [support]
/-- 指定 chart 台から同じ連結面入力を生成する。 -/
abbrev N := ConnectedFaceWitness.supported support support_nonempty
/-- e の一出現を再三角形化する同じ細入力。 -/
abbrev fine := EdgeSubdivision.supported N (0 : Fin 4)
/-- 同じ原始 mixed collapse。 -/
abbrev comparison := EdgeSubdivision.collapse N (0 : Fin 4)
/-- 原始 chart 台の公開式。 -/
@[simp] theorem chart_support (v : Fin 3) : N.chartSupport v=support v := rfl
/-- 原始 K1 の四辺台。 -/
@[simp] theorem edge_support (e : Fin 4) : N.edgeSupport e=![{false},Set.univ,{false},Set.univ] e := by
  ext a
  rw [N.mem_edgeSupport_iff]
  rw [ConnectedFaceWitness.edgeLeft,ConnectedFaceWitness.edgeRight]
  simp only [chart_support]
  fin_cases e <;> simp [support]
/-- 原始面の K1 台は alpha。 -/
@[simp] theorem face_support (f : Unit) : N.faceSupport f={false} := by
  ext a
  rw [N.mem_faceSupport_iff]
  rw [ConnectedFaceWitness.faceEdge0,ConnectedFaceWitness.faceEdge1,ConnectedFaceWitness.faceEdge2]
  simp only [edge_support]
  simp
/-- alpha は全原始 chart に属する。 -/
theorem alpha_common (v : Fin 3) : false∈N.chartSupport v := by
  rw [chart_support]
  fin_cases v <;> simp [support]
/-- alpha は fine の全 chart にも属する。 -/
theorem fine_alpha_common (v : fine.nerve.Chart) : false∈fine.chartSupport v := by
  cases v with
  | inl v => rw [EdgeSubdivision.chartSupport_old]; exact alpha_common v
  | inr v => rw [EdgeSubdivision.chartSupport_new]; exact alpha_common _
/-- e の唯一の原始出現は F の第0位置。 -/
def occurrence : EdgeSubdivision.Occurrence N (0 : Fin 4) := ⟨((),0),EdgeSubdivision.faceSlot_zero N ()⟩
/-- 全出現が指定位置で尽くされることの証明。 -/
theorem occurrence_unique (o : EdgeSubdivision.Occurrence N (0 : Fin 4)) : o=occurrence := by
  rcases o with ⟨⟨f,i⟩,hi⟩
  cases f
  fin_cases i
  · rfl
  · have h : (1 : Fin 4)=0 := (EdgeSubdivision.faceSlot_one N ()).symm.trans hi
    exact False.elim ((by decide : (1 : Fin 4)≠0) h)
  · have h : (2 : Fin 4)=0 := (EdgeSubdivision.faceSlot_two N ()).symm.trans hi
    exact False.elim ((by decide : (2 : Fin 4)≠0) h)
/-- 別名の対角辺 d。 -/
def diagonal : fine.nerve.EdgeComponent := .inr (.inr occurrence)
/-- 一出現の追加面 t。 -/
def triangle : fine.nerve.FaceComponent := .inr occurrence
/-- fresh chart 台は全体。 -/
@[simp] theorem fresh_full : fine.chartSupport (.inr PUnit.unit)=Set.univ := EdgeSubdivision.chartSupport_new N (0 : Fin 4)
/-- c の台は全体。 -/
@[simp] theorem c_full : fine.edgeSupport (.inr (.inl false))=Set.univ := EdgeSubdivision.edgeSupport_c N (0 : Fin 4)
/-- 後半 b' の台は alpha。 -/
@[simp] theorem b_support : fine.edgeSupport (.inr (.inl true))={false} := by
  rw [EdgeSubdivision.edgeSupport_b,edge_support]
  rfl
/-- 対角辺の台は alpha。 -/
@[simp] theorem diagonal_support : fine.edgeSupport diagonal={false} := by
  exact (EdgeSubdivision.edgeSupport_diagonal N (0 : Fin 4) occurrence).trans (edge_support 0)
/-- 追加面 t の台は alpha。 -/
@[simp] theorem triangle_support : fine.faceSupport triangle={false} :=
  (EdgeSubdivision.faceSupport_triangle N (0 : Fin 4) occurrence).trans (edge_support 0)
/-- 中心面の台も alpha。 -/
@[simp] theorem center_support : fine.faceSupport (.inl ())={false} :=
  (EdgeSubdivision.faceSupport_center N (0 : Fin 4) ()).trans (face_support ())
/-- beta は原始 w,e,b,F を選ばない。 -/
theorem beta_old_absent : true∉N.chartSupport (1 : Fin 3) ∧ true∉N.edgeSupport (0 : Fin 4) ∧
    true∉N.edgeSupport (2 : Fin 4) ∧ true∉N.faceSupport () := by
  simp only [edge_support,face_support]
  simp [support]
/-- beta は d,b',t,中心面を選ばない。 -/
theorem beta_new_absent : true∉fine.edgeSupport diagonal ∧ true∉fine.edgeSupport (.inr (.inl true)) ∧
    true∉fine.faceSupport triangle ∧ true∉fine.faceSupport (.inl ()) := by
  rw [diagonal_support,b_support,triangle_support,center_support]
  exact ⟨Ne.symm Bool.false_ne_true,Ne.symm Bool.false_ne_true,Ne.symm Bool.false_ne_true,Ne.symm Bool.false_ne_true⟩
/-- beta は fresh 頂点と c をともに選ぶ。 -/
theorem beta_pair_selected : true∈fine.chartSupport (.inr PUnit.unit) ∧
    true∈fine.edgeSupport (.inr (.inl false)) := by
  rw [fresh_full,c_full]
  exact ⟨Set.mem_univ _,Set.mem_univ _⟩
/-- 指定 section は中心面+t。 -/
theorem section_face : (EdgeSubdivision.s2 N (0 : Fin 4)).basisImage ()=
    Finsupp.single (.inl ()) 1+Finsupp.single triangle 1 := by
  rw [EdgeSubdivision.s2_basis]
  simp only [EdgeSubdivision.slotSection_basis,EdgeSubdivision.faceSlot_zero,
    EdgeSubdivision.faceSlot_one,EdgeSubdivision.faceSlot_two]
  simp only [dif_neg (by decide : (1 : Fin 4)≠0),
    dif_neg (by decide : (2 : Fin 4)≠0),sub_zero,add_zero]
  rfl
/-- fresh 頂点の同じ補正は c。 -/
theorem homotopy_vertex : (EdgeSubdivision.h0 N (0 : Fin 4)).basisImage (.inr PUnit.unit)=
    Finsupp.single (.inr (.inl false)) 1 := EdgeSubdivision.h0_new_basis N (0 : Fin 4)
/-- 同じ対角辺の補正は −t。 -/
theorem homotopy_diagonal : (EdgeSubdivision.h1 N (0 : Fin 4)).basisImage diagonal=
    -Finsupp.single triangle 1 := EdgeSubdivision.h1_diagonal_basis N (0 : Fin 4) occurrence
/-- 変更部分と同じ原始連結成分に loop k がある。 -/
theorem loop_attached : N.nerve.edgeLeft (3 : Fin 4)=N.nerve.edgeRight (3 : Fin 4) ∧
    N.nerve.edgeLeft (3 : Fin 4)=N.nerve.edgeLeft (0 : Fin 4) ∧
    N.nerve.edgeLeft (3 : Fin 4)=N.nerve.edgeLeft (1 : Fin 4) :=
  ConnectedFaceWitness.loop_attached support support_nonempty
end AAT.AG.FaceRelationSubdivision.WitnessTwoA
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessTwoA
